(* n-dim trees, all paths must have the same lengths, which is the number of dimensions *)
(* inspired by ndarrays but without the same-size constraint per axis *)

open Madil_common

type 'a tree =
  | Scalar of 'a option (* ndim = 0 *)
  | Vector1 of 'a option array (* ndim = 1, memory optim of Vector to avoid many boxing with Scalar *)
  | Vector of 'a tree array (* ndim = 1 + ndim of subtrees *)

type 'a t =
  { ndim : int;
    tree: 'a tree }

exception Wrong_ndim
exception Undefined (* None *)

let ndim (t : 'a t) : int = t.ndim [@@inline]
        
let scalar (x_opt : 'a option) : 'a t =
  { ndim = 0;
    tree = Scalar x_opt} [@@inline]

let pack1 (x_opts : 'a option array) : 'a t =
  { ndim = 1;
    tree = Vector1 x_opts }
  
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
                    | Scalar x_opt -> x_opt
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
  | Scalar _ ->
     Vector1
       (Array.map
          (function
           | Scalar x_opt -> x_opt
           | _ -> assert false)
          trees)
  | _ -> Vector trees
  
let unscalar (t : 'a t) : 'a result =
  match t.tree with
  | Scalar (Some x) -> Result.Ok x
  | Scalar None -> Result.Error Undefined
  | Vector1 _ -> Result.Error Wrong_ndim
  | Vector _ -> Result.Error Wrong_ndim

let choose (t : 'a t) : 'a option =
  (* return any defined scalar, if any *)
  let rec aux = function
    | Scalar x_opt -> x_opt
    | Vector1 vx -> Option.join (Array.find_opt (fun x_opt -> x_opt <> None) vx)
    | Vector v -> Option.join (Array.find_opt (fun x_opt -> x_opt <> None) (Array.map aux v))
  in
  aux t.tree
              
let unpack (t : 'a t) : 'a t array result =
  (* unpack a (n+1)-tree into a list of n-trees *)
  match t.tree with
  | Scalar _ -> Result.Error Wrong_ndim
  | Vector1 v -> Result.Ok (Array.map scalar v)
  | Vector v ->
     let ndim = t.ndim - 1 in
     Result.Ok (Array.map (fun tree -> {ndim; tree}) v)

let lookup (t : 'a t) (is : int list) : 'a option =
  let rec aux tree is =
    match tree, is with
    | Scalar x_opt, _ -> x_opt
    | Vector1 vx, i::_ ->
       let n = Array.length vx in
       vx.(i mod n)
    | Vector v, i::is1 ->
       let n = Array.length v in
       if i >= 0 && i < n
       then aux v.(i) is1
       else None
    | _ -> failwith "Ndtree.lookup: invalid index, lower ndim than the ndtree"
  in
  aux t.tree is
     
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

let fold ~(scalar: 'a option -> 'b) ~(vector: 'b array -> 'b) (t : 'a t) : 'b =
  let rec aux = function
    | Scalar x_opt -> scalar x_opt
    | Vector1 vx -> vector (Array.map scalar vx)
    | Vector v -> vector (Array.map aux v)
  in
  aux t.tree
                  
let foldi ~(scalar: int list -> 'a option -> 'b) ~(vector: int list -> 'b array -> 'b) (t : 'a t) : 'b =
  let rec aux rev_is = function
    | Scalar x_opt -> scalar (List.rev rev_is) x_opt
    | Vector1 vx -> vector (List.rev rev_is)
                      (Array.mapi (fun i x_opt -> scalar (List.rev (i::rev_is)) x_opt) vx)
    | Vector v -> vector (List.rev rev_is)
                    (Array.mapi (fun i tree1 -> aux (i::rev_is) tree1) v)
  in
  aux [] t.tree

let map (f : 'a -> 'b) (t : 'a t) : 'b t =
  let rec aux = function
    | Scalar x_opt -> Scalar (Option.map f x_opt)
    | Vector1 vx -> Vector1 (Array.map (Option.map f) vx)
    | Vector v -> Vector (Array.map aux v)
  in
  { t with tree = aux t.tree }

let map_filter (f : 'a -> 'b option) (t : 'a t) : 'b t =
  let rec aux = function
    | Scalar x_opt -> Scalar (Option.bind x_opt f)
    | Vector1 vx -> Vector1 (Array.map (fun x_opt -> Option.bind x_opt f) vx)
    | Vector v -> Vector (Array.map aux v)
  in
  { t with tree = aux t.tree }

let mapi (f : int list -> 'a -> 'b) (t : 'a t) : 'b t =
  let rec aux rev_is = function
    | Scalar x_opt ->
       let is = List.rev rev_is in
       Scalar (Option.map (f is) x_opt)
    | Vector1 vx -> Vector1 (Array.mapi (fun i x_opt -> Option.map (f (List.rev (i::rev_is))) x_opt) vx)
    | Vector v -> Vector (Array.mapi (fun i tree1 -> aux (i::rev_is) tree1) v)
  in
  { t with tree = aux [] t.tree }

let map_result (f : 'a -> 'b result) (t : 'a t) : 'b t result =
  let rec aux = function
    | Scalar None ->
       Result.Ok (Scalar None)
    | Scalar (Some x) ->
       let| y = f x in
       Result.Ok (Scalar (Some y))
    | Vector1 vx ->
       let| vy =
         array_map_result
           (function
            | None -> Result.Ok None
            | Some x -> let| y = f x in Result.Ok (Some y))
           vx in
       Result.Ok (Vector1 vy)
    | Vector v ->
       let| v' = array_map_result aux v in
       Result.Ok (Vector v')
  in
  let| tree' = aux t.tree in
  Result.Ok { t with tree = tree' }

let bind (f : 'a option -> 'b t) (t : 'a t) : 'b t =
  let ndim_incr = ref 0 in
  let rec aux = function
    | Scalar x_opt ->
       let t = f x_opt in
       ndim_incr := t.ndim; (* should be constant for all calls to f *)
       t.tree
    | Vector1 vx -> pack_tree (Array.map (fun x_opt -> (f x_opt).tree) vx)
    | Vector v -> pack_tree (Array.map aux v)
  in
  let tree = aux t.tree in
  { ndim = t.ndim + !ndim_incr; tree }

let for_all (f : 'a option -> bool) (t : 'a t) : bool =
  let rec aux = function
    | Scalar x_opt -> f x_opt
    | Vector1 vx -> Array.for_all f vx
    | Vector v -> Array.for_all aux v
  in
  aux t.tree

let for_all_defined (f : 'a -> bool) (t : 'a t) : bool =
  let rec aux = function
    | Scalar (Some x) -> f x
    | Scalar None -> true
    | Vector1 vx -> Array.for_all (function Some x -> f x | None -> true) vx
    | Vector v -> Array.for_all aux v
  in
  aux t.tree

  
module Operators =
  struct
    let ( let< ) t f = map f t
    let ( let<?) t f = map_filter f t
    let ( let<* ) t f = bind f t
  end
