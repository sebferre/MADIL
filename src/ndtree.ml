(* n-dim trees, all paths must have the same lengths, which is the number of dimensions *)
(* inspired by ndarrays but without the same-size constraint per axis *)

open Madil_common

type 'a tree =
  | Scalar of 'a (* ndim = 0 *)
  | Vector1 of 'a array (* ndim = 1, memory optim of Vector to avoid many boxing with Scalar *)
  | Vector of 'a tree array (* ndim = 1 + ndim of subtrees *)

type 'a t =
  { ndim : int;
    tree: 'a tree }

exception Wrong_ndim
  
let scalar (x : 'a) : 'a t =
  { ndim = 0;
    tree = Scalar x} [@@inline]

let pack1 (xs : 'a array) : 'a t =
  { ndim = 1;
    tree = Vector1 xs }
  
let pack (ts : 'a t array) : 'a t =
  (* pack a list of n-trees into a (n+1)-tree *)
  if Array.length ts = 0 then
    failwith "Ndtree.pack: empty list";
  let ndim0 = ts.(0).ndim in
  if Array.exists (fun t1 -> t1.ndim <> ndim0) ts then
    failwith "Ndtree.pack: inconsistent ndims";
  if ndim0 = 0
  then
    { ndim = 1;
      tree = Vector1
               (Array.map
                  (fun t ->
                    match t.tree with
                    | Scalar x -> x
                    | _ -> assert false)
                  ts) }
  else
    { ndim = ndim0 + 1;
      tree = Vector
               (Array.map
                  (fun t -> t.tree)
                  ts) }

let pack_tree (trees : 'a tree array) : 'a tree =
  assert (Array.length trees > 0);
  match trees.(0) with
  | Scalar _ -> Vector1 (Array.map (function Scalar x -> x | _ -> assert false) trees)
  | _ -> Vector trees
  
let unscalar (t : 'a t) : ('a,exn) Result.t =
  match t.tree with
  | Scalar x -> Result.Ok x
  | Vector1 _ -> Result.Error Wrong_ndim
  | Vector _ -> Result.Error Wrong_ndim

let unpack (t : 'a t) : ('a t array, exn) Result.t =
  (* unpack a (n+1)-tree into a list of n-trees *)
  match t.tree with
  | Scalar _ -> Result.Error Wrong_ndim
  | Vector1 v -> Result.Ok (Array.map scalar v)
  | Vector v ->
     let ndim = t.ndim - 1 in
     Result.Ok (Array.map (fun tree -> {ndim; tree}) v)
     
let index (t : 'a t) (is : int option list) : 'a t option =
  let rec aux_ndim ndim is =
    match is with
    | [] -> ndim
    | (Some _)::is1 -> aux_ndim (ndim-1) is1 (* axis elimination *)
    | None::is1 -> 1 + aux_ndim (ndim-1) is1 in
  let rec aux_tree tree is =
    match tree, is with
    | _, [] -> tree
    | Scalar _, _ -> failwith "Ndtree.index: invalid index, too many dims"
    | Vector1 v, (Some i)::_ ->
       if i >= 0 && i < Array.length v
       then Scalar v.(i)
       else raise Not_found
    | Vector1 v, None::_ -> tree
    | Vector v, (Some i)::is1 ->
       if i >= 0 && i < Array.length v
       then aux_tree v.(i) is1
       else raise Not_found
    | Vector v, None::is1 ->
       pack_tree (Array.map (fun tree1 -> aux_tree tree1 is1) v)
  in
  try
    let ndim = aux_ndim t.ndim is in
    let tree = aux_tree t.tree is in
    Some { ndim; tree }
  with Not_found -> None

let fold ~(scalar: 'a -> 'b) ~(vector: 'b array -> 'b) (t : 'a t) : 'b =
  let rec aux = function
    | Scalar x -> scalar x
    | Vector1 vx -> vector (Array.map scalar vx)
    | Vector v -> vector (Array.map aux v)
  in
  aux t.tree
                  
let foldi ~(scalar: int list -> 'a -> 'b) ~(vector: int list -> 'b array -> 'b) (t : 'a t) : 'b =
  let rec aux rev_is = function
    | Scalar x -> scalar (List.rev rev_is) x
    | Vector1 vx -> vector (List.rev rev_is)
                      (Array.mapi (fun i x -> scalar (List.rev (i::rev_is)) x) vx)
    | Vector v -> vector (List.rev rev_is)
                    (Array.mapi (fun i tree1 -> aux (i::rev_is) tree1) v)
  in
  aux [] t.tree

let map (f : 'a -> 'b) (t : 'a t) : 'b t =
  let rec aux = function
    | Scalar x -> Scalar (f x)
    | Vector1 v -> Vector1 (Array.map f v)
    | Vector v -> Vector (Array.map aux v)
  in
  { t with tree = aux t.tree }

let mapi (f : int list -> 'a -> 'b) (t : 'a t) : 'b t =
  let rec aux rev_is = function
    | Scalar x ->
       let is = List.rev rev_is in
       Scalar (f is x)
    | Vector1 vx -> Vector1 (Array.mapi (fun i x -> f (List.rev rev_is) x) vx)
    | Vector v -> Vector (Array.mapi (fun i tree1 -> aux (i::rev_is) tree1) v)
  in
  { t with tree = aux [] t.tree }

let map_result (f : 'a -> 'b result) (t : 'a t) : 'b t result =
  let rec aux = function
    | Scalar x ->
       let| y = f x in
       Result.Ok (Scalar y)
    | Vector1 vx ->
       let| vy = array_map_result f vx in
       Result.Ok (Vector1 vy)
    | Vector v ->
       let| v' = array_map_result aux v in
       Result.Ok (Vector v')
  in
  let| tree' = aux t.tree in
  Result.Ok { t with tree = tree' }

let bind (f : 'a -> 'b t) (t : 'a t) : 'b t =
  let ndim_incr = ref 0 in
  let rec aux = function
    | Scalar x ->
       let t = f x in
       ndim_incr := t.ndim; (* should be constant for all calls to f *)
       t.tree
    | Vector1 v -> pack_tree (Array.map (fun x -> (f x).tree) v)
    | Vector v -> pack_tree (Array.map aux v)
  in
  let tree = aux t.tree in
  { ndim = t.ndim + !ndim_incr; tree }

let for_all (f : 'a -> bool) (t : 'a t) : bool =
  let rec aux = function
    | Scalar x -> f x
    | Vector1 vx -> Array.for_all f vx
    | Vector v -> Array.for_all aux v
  in
  aux t.tree

module Operators =
  struct
    let ( let< ) t f = map f t
    let ( let<* ) t f = bind f t
  end
