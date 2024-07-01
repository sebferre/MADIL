(* n-dim sequences, all paths must have the same length, which is the number of dimensions *)
(* inspired by ndarrays, but without the same-size constraint per axis *)
(* some values are projections on some indices: incomplete values *)

open Madil_common

type 'a seq = [`Seq of int (* item depth *) * int option * 'a list] (* when Some i, then list contains only item at index i *)

exception Incomplete (* incomplete sequence, only item at some position *)

let xp_seq xp_item : 'a seq html_xp =
  fun ~html print ->
  function
  | `Seq (_, pos_opt, items) ->
     let s_pos =
       match pos_opt with
       | None -> ""
       | Some pos -> "... " ^ string_of_int pos ^ ":" in
     xp_list ~delims:("〈" ^ s_pos, "〉") xp_item ~html print items

type 'a t = [> 'a seq] as 'a

exception Invalid_depth (* undefined depth in structure *)

let rec depth : 'a t -> int = function
  | `Seq (d, _, l) ->
     assert (List.for_all (fun x -> depth x = d) l);
     1 + d
(* REM     (match l with
      | [] -> 1 (* TODO: invalid, add information somehow *)
      | x::_ -> 1 + depth x) *)
  | _ -> 0

let seq (d : int) (items : 'a list) : 'a t =
  assert (List.for_all (fun item -> depth item = d) items);
  `Seq (d, None, items)

let as_seq (x : 'a t) : (int * 'a list) option = (* item depth and items *)
  match x with
  | `Seq (d,None,l) -> Some (d,l)
  | `Seq (d,Some _,_) -> raise Incomplete
  | _ -> None

let fold_left (f : 'b -> 'a -> 'b) (init : 'b) (x : 'a t) : 'b =
  let rec aux acc = function
    | `Seq (_, _, l) -> List.fold_left aux acc l
    | x -> f acc x
  in
  aux init x

let rec map ?(depth = -1) (delta_depth : int) (f : 'a -> 'b) (x : 'a t) : 'b t =
  (* delta_depth = depth(b) - depth(a) *)
  if depth = 0
  then f x
  else
    match x with
    | `Seq (d,i_opt,l) -> `Seq (d + delta_depth, i_opt, List.map (map ~depth:(depth-1) delta_depth f) l)
    | _ -> f x

let rec map_result ?(depth = -1) (delta_depth : int) (f : 'a -> 'b result) (x : 'a t) : 'b t result =
  if depth = 0
  then f x
  else
    match x with
    | `Seq (d,i_opt,l) ->
       let| ly = list_map_result (map_result ~depth:(depth-1) delta_depth f) l in
       Result.Ok (`Seq (d + delta_depth, i_opt, ly))
    | _ -> f x

let rec map2 ?(depth = -1) (delta_depth : int) (f : 'a -> 'b -> 'c) (x1 : 'a t) (x2 : 'b t) : 'c t =
  (* delta_depth = depth(c) - depth(a) *)
  if depth = 0
  then f x1 x2
  else
    match x1, x2 with
    | `Seq (d1,i1_opt,l1), `Seq (d2,i2_opt,l2) ->
       if i1_opt = i2_opt && List.length l1 = List.length l2
       then `Seq (d1 + delta_depth, i1_opt, List.map2 (map2 ~depth:(depth-1) delta_depth f) l1 l2)
       else invalid_arg "Utilities.XSeq.map2: inconsistent structure"
    | _ -> f x1 x2

let rec map2_result ?(depth = -1) (delta_depth : int) (f : 'a -> 'b -> 'c result) (x1 : 'a t) (x2 : 'b t) : 'c t result =
  if depth = 0
  then f x1 x2
  else
    match x1, x2 with
    | `Seq (d1,i1_opt,l1), `Seq (d2,i2_opt,l2) ->
       if i1_opt = i2_opt && List.length l1 = List.length l2
       then
         let l = List.combine l1 l2 in
         let| ly =
           list_map_result
             (fun (x1,x2) ->
               map2_result ~depth:(depth-1) delta_depth f x1 x2)
             l in
         Result.Ok (`Seq (d1 + delta_depth, i1_opt, ly))
       else invalid_arg "Utilities.XSeq.map2: inconsistent structure"
    | _ -> f x1 x2

let rec map3 ?(depth = -1) (delta_depth : int) (f : 'a -> 'b -> 'c -> 'd) (x1 : 'a t) (x2 : 'b t) (x3 : 'c t) : 'd t =
  if depth = 0
  then f x1 x2 x3
  else
    match x1, x2, x3 with
    | `Seq (d1,i1_opt,l1), `Seq (d2,i2_opt,l2), `Seq (d3,i3_opt,l3) ->
       let n = List.length l1 in
       if i2_opt = i1_opt && i3_opt = i1_opt
          && List.length l2 = n && List.length l3 = n
       then `Seq (d1 + delta_depth, i1_opt, list_map3 (map3 ~depth:(depth-1) delta_depth f) l1 l2 l3)
       else invalid_arg "Utilities.XSeq.map3: inconsistent structure"
    | _ -> f x1 x2 x3

let rec match_myseq (delta_depth : int) (f : 'a -> 'b -> ('c * 'd) Myseq.t) (x1 : 'a t) (x2 : 'b t) : ('c t * 'd t) Myseq.t =
  (* delta_depth = depth(c or d) - dpeth(b) *)
  match x1, x2 with
  | `Seq (_,i1_opt,l1), `Seq (d2,None,l2) ->
     assert (i1_opt = None);
     if List.length l1 = List.length l2
     then
       let d = d2 + delta_depth in
       let* ly = Myseq.product_fair (List.map2 (match_myseq delta_depth f) l1 l2) in
       let ly1, ly2 = List.split ly in
       Myseq.return (`Seq (d, None, ly1), `Seq (d, None, ly2))
     else Myseq.empty
  | `Seq (_,i1_opt,l1), `Seq (d2,Some i2,[z2]) ->
     assert (i1_opt = None);
     if i2 >= 0 && i2 < List.length l1
     then
       let d = d2 + delta_depth in
       let z1 = List.nth l1 i2 in
       let* y1, y2 = match_myseq delta_depth f z1 z2 in
       Myseq.return (`Seq (d, Some i2, [y1]), `Seq (d, Some i2, [y2]))
     else Myseq.empty
  | _, `Seq (d2,None,l2) -> (* broadcast x1 *)
     let d = d2 + delta_depth in
     let* ly = Myseq.product_fair (List.map (match_myseq delta_depth f x1) l2) in
     let ly1, ly2 = List.split ly in
     Myseq.return (`Seq (d, None, ly1), `Seq (d, None, ly2))
  | _, `Seq (d2, Some i2, [z2]) -> (* broadcast x1 *)
     let d = d2 + delta_depth in
     let* y1, y2 = match_myseq delta_depth f x1 z2 in
     Myseq.return (`Seq (d, Some i2, [y1]), `Seq (d, Some i2, [y2]))
  | `Seq _, _ | _, `Seq _ -> Myseq.empty
  | _ -> f x1 x2

let rec for_all ?(depth = -1) (f : 'a -> bool) (x : 'a t) : bool =
  if depth = 0
  then f x
  else
    match x with
    | `Seq (d,i_opt,l) -> List.for_all (for_all ~depth:(depth-1) f) l
    | _ -> f x

let rec bind ?(depth = -1) (x : 'a t) (delta_depth : int) (f : 'a -> 'b t) : 'b t =
  if depth = 0
  then f x
  else
    match x with
    | `Seq (d,i_opt,l) -> `Seq (d + delta_depth, i_opt, List.map (fun x -> bind ~depth:(depth-1) x delta_depth f) l)
    | _ -> f x

let rec bind_option ?(depth = -1) (rev_path : int list) (x : 'a t) (delta_depth : int) (f : int list -> 'a -> 'b t option) : 'b option =
  if depth = 0
  then f rev_path x
  else
    match x with
    | `Seq (d,pos_opt,lx) ->
       let@ ly =
         match pos_opt, lx with
         | None, _ ->
            list_mapi_option
              (fun pos x -> bind_option ~depth:(depth-1) (pos::rev_path) x delta_depth f)
              lx
         | Some pos, [x1] ->
            let@ y1 = bind_option ~depth:(depth-1) (pos::rev_path) x1 delta_depth f in
            Some [y1]
         | _ -> assert false in
       Some (`Seq (d + delta_depth, pos_opt, ly))
    | _ -> f rev_path x

let rec bind_result ?(depth = -1) (rev_path : int list) (x : 'a t) (delta_depth : int) (f : int list -> 'a -> 'b t result) : 'b result =
  if depth = 0
  then f rev_path x
  else
    match x with
    | `Seq (d,pos_opt,lx) ->
       let| ly =
         match pos_opt, lx with
         | None, _ ->
            list_mapi_result
              (fun pos x -> bind_result ~depth:(depth-1) (pos::rev_path) x delta_depth f)
              lx
         | Some pos, [x1] ->
            let| y1 = bind_result ~depth:(depth-1) (pos::rev_path) x1 delta_depth f in
            Result.Ok [y1]
         | _ -> assert false in
       Result.Ok (`Seq (d + delta_depth, pos_opt, ly))
    | _ -> f rev_path x

let rec bind_myseq ?(depth = -1) (rev_path : int list) (x : 'a t) (delta_depth : int) (f : int list -> 'a -> 'b t Myseq.t) : 'b t Myseq.t =
  if depth = 0
  then f rev_path x
  else
    match x with
    | `Seq (d,pos_opt,lx) ->
       let* ly =
         match pos_opt, lx with
         | None, _ ->
            Myseq.product_fair
              (List.mapi
                 (fun pos x -> bind_myseq ~depth:(depth-1) (pos::rev_path) x delta_depth f)
                 lx)
         | Some pos, [x1] ->
            let* y1 = bind_myseq ~depth:(depth-1) (pos::rev_path) x1 delta_depth f in
            Myseq.return [y1]
         | _ -> assert false in
       Myseq.return (`Seq (d + delta_depth, pos_opt, ly))
    | _ -> f rev_path x

let nest_path (rev_path : int list) (x : 'a t) : int list * 'a t = (* returns List.rev rev_path, and x at the end of path *)
  let rec aux rev_path d x path =
    match rev_path with
    | [] -> path, x
    | pos::rev_path1 ->
       aux rev_path1 (d+1) (`Seq (d, Some pos, [x])) (pos::path)
  in
  let d = depth x in
  aux rev_path d x []

let rec unnest_path (path : int list) (x : 'a t) : 'a t =
  match path, x with
  | [], _ -> x
  | pos::path1, `Seq (_, Some pos', [x1]) when pos = pos' ->
     unnest_path path1 x1
  | _ -> invalid_arg "Utilities.XSeq.unnest_path: inconsistent path"


let is_complete ~depth (x : 'a t) : bool =
  for_all ~depth
    (function
     | `Seq (_,pos_opt,_) -> pos_opt = None
     | _ -> raise Invalid_depth)
    x

let seq_of_seq (f : 'a list -> 'b list) (items : 'a t) : 'b t =
  (* a and b should have same depth *)
  match items with
  | `Seq (d,None,l) -> `Seq (d, None, f l)
  | `Seq _ -> raise Incomplete
  | _ -> raise Invalid_depth

let item_of_seq (f : 'a list -> 'b) (items : 'a t) : 'b =
  match items with
  | `Seq (d,None,l) -> f l
  | `Seq _ -> raise Incomplete
  | _ -> raise Invalid_depth

let item_of_seq2 (f : 'a list -> 'b list -> 'c) (items1 : 'a t) (items2 : 'b t) : 'c =
  match items1, items2 with
  | `Seq (d1,None,l1), `Seq (d2,None,l2) -> f l1 l2
  | `Seq _, _ | _, `Seq _ -> raise Incomplete
  | _ -> raise Invalid_depth

let item_of_item_seq (f : 'a -> 'b list -> 'c) (x1 : 'a) (x2 : 'b t) : 'c =
  match x2 with
  | `Seq (d2,None,l2) -> f x1 l2
  | `Seq _ -> raise Incomplete
  | _ -> raise Invalid_depth

let seq_of_item_seq (f : 'a -> 'b list -> 'c list) (x1 : 'a) (x2 : 'b t) : 'c t =
  (* b and c should have the same depth *)
  match x2 with
  | `Seq (d2,None,l2) -> `Seq (d2, None, f x1 l2)
  | `Seq _ -> raise Incomplete
  | _ -> raise Invalid_depth

let seq_of_item (f : 'a -> 'b list) (x : 'a) : 'b t =
  (* b should have depth 0 *)
  `Seq (0, None, f x)

let head ~(depth : int) (x : 'a t) : 'a option =
  bind_option ~depth [] x (-1)
    (fun rev_path -> function
      | `Seq (d,i_opt,l) ->
         (match i_opt, l with
          | None, x0::_ -> Some x0
          | Some 0, [x0] -> Some x0
          | _ -> None)
      | _ -> raise Invalid_depth)

let tail ~(depth : int) (x : 'a t) : 'a t option =
  bind_option ~depth [] x 0
    (fun rev_path -> function
      | `Seq (d,i_opt,l) ->
         (match i_opt, l with
          | None, x0::l1 -> Some (`Seq (d,None,l1))
          | _ -> None)
      | _ -> raise Invalid_depth)

let cons ~(depth : int) (hd : 'a t) (tl : 'a t) : 'a t =
  map2 ~depth (+1)
    (fun x0 x1 ->
      match x1 with
      | `Seq (d1,None,l1) -> `Seq (d1, None, x0::l1)
      | `Seq (_,Some _,_) -> raise Incomplete
      | _ -> raise Invalid_depth)
    hd tl

let index ~(depth : int) (i : int) (x : 'a t) : 'a option =
  bind_option ~depth [] x (-1)
    (fun rev_path -> function
      | `Seq (d,None,l) ->
         let n = List.length l in
         if i >= 0 && i < n then Some (List.nth l i)
         else if i < 0 && i >= -n then Some (List.nth l (n+i))
         else None
      | `Seq (d,Some pos,[x1]) ->
         if pos = i then Some x1
         else None
      | _ -> raise Invalid_depth)

let _ = (* UNIT TEST *)
  let x = `Seq (0, None, [`Int 1; `Int 2; `Int 3]) in
  let y1 = map 0 (function `Int n -> `String (string_of_int n) | _ -> assert false) x in
  assert (y1 = `Seq (0, None, [`String "1"; `String "2"; `String "3"]));
  let y2 = bind x (+1) (function `Int n -> `Seq (0, None, List.init n (fun i -> `Int i)) | _ -> assert false) in
  assert (y2 = `Seq (1, None, [`Seq (0, None, [`Int 0]);
                               `Seq (0, None, [`Int 0; `Int 1]);
                               `Seq (0, None, [`Int 0;`Int 1;`Int 2])]));
  ()
