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

let xp ~(xp_elt : 'a html_xp) : 'a t html_xp =
  let rec aux ~html print = function
    | Scalar x_opt -> aux_elt_opt ~html print x_opt
    | Vector1 vx ->
       xp_array ~delims:("<",">") ~sep:" ; "
         aux_elt_opt
         ~html print vx
    | Vector v ->
       xp_array ~delims:("<",">") ~sep:" ; "
         aux
         ~html print v
  and aux_elt_opt ~html print = function
    | None -> print#string "-"
    | Some x -> xp_elt ~html print x
  in
  fun ~html print t ->
  aux ~html print t.tree

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
       if i >= 0 && i < n
       then vx.(i)
       else None
    | Vector v, i::is1 ->
       let n = Array.length v in
       if i >= 0 && i < n
       then aux v.(i) is1
       else None
    | _ -> failwith "Ndtree.lookup: invalid index, lower ndim than the ndtree"
  in
  aux t.tree is
     
let index (t : 'a t) (is : int option list) : 'a t option =
  (* None = full slice :, Some i = index i, negative indices supported *)
  let rec aux_ndim ndim is =
    match is with
    | [] -> ndim
    | (Some _)::is1 -> aux_ndim (max 0 (ndim-1)) is1 (* axis elimination *)
    | None::is1 -> 1 + aux_ndim (max 0 (ndim-1)) is1 in
  let rec aux_tree tree is =
    match tree, is with
    | _, [] -> tree
    | Scalar _, _ -> tree (* some form of broadcasting *)
    | Vector1 v, (Some i)::_ ->
       let n = Array.length v in
       if i >= 0 && i < n then Scalar v.(i)
       else if i < 0 && i >= -n then Scalar v.(n+i) 
       else raise Not_found
    | Vector1 v, None::_ -> tree
    | Vector v, (Some i)::is1 ->
       let n = Array.length v in
       if i >= 0 && i < n then aux_tree v.(i) is1
       else if i < 0 && i > -n then aux_tree v.(n+i) is1
       else raise Not_found
    | Vector v, None::is1 ->
       pack_tree (Array.map (fun tree1 -> aux_tree tree1 is1) v)
  in
  try
    let ndim = aux_ndim t.ndim is in
    let tree = aux_tree t.tree is in
    Some { ndim; tree }
  with Not_found -> None

let head_opt (t : 'a t) : 'a t option = (* t[0] *)
  match t.tree with
  | Scalar _ -> None
  | Vector1 vx ->
     if vx <> [||]
     then Some {ndim = 0; tree = Scalar vx.(0)}
     else None
  | Vector v ->
     if v <> [||]
     then Some {ndim = t.ndim - 1; tree = v.(0)}
     else None

let replace_head (t : 'a t) (t0 : 'a t) : 'a t = (* t[0] <- t0, not in place *)
  if t0.ndim <> t.ndim - 1 then raise Wrong_ndim;
  match t.tree, t0.tree with
  | Vector1 vx, Scalar x_opt ->
     if vx = [||] then failwith "Ndtree.replace_head: empty vector, no head";
     let vx' = Array.copy vx in
     vx'.(0) <- x_opt;
     {ndim = 1; tree = Vector1 vx'}
  | Vector v, tree0 ->
     if v = [||] then failwith "Ndtree.replace_head: empty vector, no head";
     let v' = Array.copy v in
     v'.(0) <- tree0;
     {ndim = t.ndim; tree = Vector v'}
  | _ -> assert false
  
let tail_opt  (t : 'a t) : 'a t option = (* t[1:] *)
  match t.tree with
  | Scalar _ -> None
  | Vector1 vx ->
     let n = Array.length vx in
     if n > 0
     then Some {ndim = 1; tree = Vector1 (Array.sub vx 1 (n-1))}
     else None
  | Vector v ->
     let n = Array.length v in
     if n > 0
     then Some {ndim = t.ndim; tree = Vector (Array.sub v 1 (n-1))}
     else None

                  
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
            | Some x ->
               let| y = f x in
               Result.Ok (Some y))
           vx in
       Result.Ok (Vector1 vy)
    | Vector v ->
       let| v' =
         array_map_result
           (fun tree1 ->
             aux tree1)
           v in
       Result.Ok (Vector v')
  in
  let| tree' = aux t.tree in
  Result.Ok { t with tree = tree' }

let mapi_result (f : int list -> 'a -> 'b result) (t : 'a t) : 'b t result =
  let rec aux rev_is = function
    | Scalar None ->
       Result.Ok (Scalar None)
    | Scalar (Some x) ->
       let is = List.rev rev_is in
       let| y = f is x in
       Result.Ok (Scalar (Some y))
    | Vector1 vx ->
       let| vy =
         array_mapi_result
           (fun i -> function
            | None -> Result.Ok None
            | Some x ->
               let is = List.rev (i::rev_is) in
               let| y = f is x in
               Result.Ok (Some y))
           vx in
       Result.Ok (Vector1 vy)
    | Vector v ->
       let| v' =
         array_mapi_result
           (fun i tree1 ->
             aux (i::rev_is) tree1)
           v in
       Result.Ok (Vector v')
  in
  let| tree' = aux [] t.tree in
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

let all_same_size_or_one (ts : 'a t array) : int option =
  Array.fold_left
    (fun size_opt t ->
      match size_opt with
      | None -> None
      | Some size ->
         match t.tree with
         | Scalar _ -> Some size
         | Vector1 vx ->
            let n = Array.length vx in
            if size = 1 || n = 1 || size = n
            then Some (max size n)
            else None
         | Vector v ->
            let n = Array.length v in
            if size = 1 || n = 1 || size = n
            then Some (max size n)
            else None)
    (Some 1) ts

exception Invalid_broadcast

let broadcastable (ts : 'a t array) : bool =
  (* when broadcast_result is well-defined *)
  let rec aux ts =
    if Array.for_all (fun t -> t.ndim = 0) ts (* all scalars *)
    then true
    else
      match all_same_size_or_one ts with
      | Some size -> (* broadcastable: all ndtrees have equal size or size=1 on first axis *)
         Common.fold_for
           (fun i ok ->
             ok 
             && (let ts_i = (* [t1[i], ..., tk[i] *)
                   Array.map
                     (fun t ->
                       match t.tree with
                       | Scalar x_opt -> t
                       | Vector1 vx ->
                          let n = Array.length vx in
                          {ndim = 0; tree = Scalar vx.(i mod n)}
                       | Vector v ->
                          let n = Array.length v in
                          {ndim = t.ndim-1; tree = v.(i mod n)})
                     ts in
                 aux ts_i))
           0 (size-1)
           true
      | None -> false
  in
  match ts with
  | [||] -> true
  | [|t1|] -> true
  | _ -> aux ts (* the real broadcasting case *)
        
let broadcast_result (f : 'a array -> 'b result) (ts : 'a t array) : 'b t result =
  (* function application by broadcasting through an array of ndtrees *)
  (* when the function application fails, the whole broadcast fails *)
  let rec aux ts =
    if Array.for_all (fun t -> t.ndim = 0) ts (* all scalars *)
    then
      let| xs = array_map_result unscalar ts in (* get scalars, if all defined *)
      let| y = f xs in (* apply the function *)
      Result.Ok (scalar (Some y)) (* TODO: consider converting app failure into None *)
    else
      match all_same_size_or_one ts with
      | Some size -> (* broadcastable: all ndtrees have equal size or size=1 on first axis *)
         let| ts_y: 'b t array =
           array_map_result
             (fun i ->
               let ts_i = (* [t1[i], ..., tk[i] *)
                 Array.map
                   (fun t ->
                     match t.tree with
                     | Scalar x_opt -> t
                     | Vector1 vx ->
                        let n = Array.length vx in
                        {ndim = 0; tree = Scalar vx.(i mod n)}
                     | Vector v ->
                        let n = Array.length v in
                        {ndim = t.ndim-1; tree = v.(i mod n)})
                   ts in
               aux ts_i)
             (Array.init size (fun i -> i)) in
         Result.Ok (pack ts_y)
      | None ->
         Result.Error Invalid_broadcast
  in
  match ts with
  | [||] ->
     let| y = f [||] in
     Result.Ok (scalar (Some y))
  | [|t1|] ->
     map_result (fun x1 -> f [|x1|]) t1
  | _ -> aux ts (* the real broadcasting case *)

module Operators =
  struct
    let ( let< ) t f = map f t
    let ( let<?) t f = map_filter f t
    let ( let<* ) t f = bind f t
  end
