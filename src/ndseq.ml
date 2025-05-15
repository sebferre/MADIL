(* n-dim sequences, all paths must have the same length, which is the number of dimensions *)
(* inspired by ndarrays, but without the same-size constraint per axis *)
(* some values are projections on some indices: incomplete values *)

open Madil_common

type 'a seq = [`Seq of int (* item depth *) * 'a list]

let xp_seq xp_item : 'a seq html_xp =
  fun ~html print ->
  function
  | `Seq (_, items) ->
     xp_list ~delims:("〈", "〉") xp_item ~html print items

type 'a t = [> 'a seq] as 'a

exception Invalid_depth (* undefined depth in structure *)

let rec depth : 'a t -> int = function
  | `Seq (d, l) ->
     assert (d >= 0);
     assert (List.for_all (fun x -> depth x = d) l);
     1 + d
  | _ -> 0
let ndim = depth

let seq (d : int) (items : 'a list) : 'a t =
  assert (d >= 0);
  assert (List.for_all (fun item -> depth item = d) items);
  `Seq (d, items)

let as_seq (x : 'a t) : (int * 'a list) option = (* item depth and items *)
  match x with
  | `Seq (d,l) -> Some (d,l)
  | _ -> None

let choose (x : 'a t) : 'a option =
  let rec aux = function
    | `Seq (d,l) -> List.find_map aux l
    | x -> Some x
  in
  aux x

let fold_left (f : 'b -> 'a -> 'b) (init : 'b) (x : 'a t) : 'b =
  let rec aux acc = function
    | `Seq (_, l) -> List.fold_left aux acc l
    | x -> f acc x
  in
  aux init x

let fold_left2 (f : 'c -> 'a -> 'b -> 'c) (init : 'c) (x : 'a t) (y : 'b t) : 'c =
  let rec aux acc x y =
    match x, y with
    | `Seq (_, lx), `Seq (_, ly) -> List.fold_left2 aux acc lx ly
    | x, y -> f acc x y
  in
  aux init x y

let foldi_left (f : 'b -> int list (* revpath *) -> 'a -> 'b) (init : 'b) (x : 'a t) : 'b =
  let rec aux acc revpath = function
    | `Seq (_, l) ->
       list_foldi_left
         (fun acc i x -> aux acc (i::revpath) x)
         acc l
    | x -> f acc revpath x
  in
  aux init [] x

let rec map ?(depth = -1) (delta_depth : int) (f : 'a -> 'b) (x : 'a t) : 'b t =
  (* delta_depth = depth(b) - depth(a) *)
  if depth = 0
  then f x
  else
    match x with
    | `Seq (d,l) ->
       let ly = List.map (map ~depth:(depth-1) delta_depth f) l in
       let dy = d + delta_depth in
       assert (dy >= 0);
       `Seq (dy, ly)
    | _ -> f x

let const (c : 'b) (x : 'a t) : 'b t =
  map 0 (fun _ -> c) x

let rec map_option ?(depth = -1) (delta_depth : int) (f : 'a -> 'b option) (x : 'a t) : 'b t option =
  if depth = 0
  then f x
  else
    match x with
    | `Seq (d,l) ->
       let@ ly = list_mapi_option (fun i -> map_option ~depth:(depth-1) delta_depth f) l in
       let dy = d + delta_depth in
       assert (dy >= 0);
       Some (`Seq (dy, ly))
    | _ -> f x

let rec map_result ?(depth = -1) (delta_depth : int) (f : 'a -> 'b result) (x : 'a t) : 'b t result =
  if depth = 0
  then f x
  else
    match x with
    | `Seq (d,l) ->
       let| ly = list_map_result (map_result ~depth:(depth-1) delta_depth f) l in
       let dy = d + delta_depth in
       assert (dy >= 0);
       Result.Ok (`Seq (dy, ly))
    | _ -> f x

let rec map_myseq ?(depth = -1) (delta_depth : int) (f : 'a -> 'b Myseq.t) (x : 'a t) : 'b t Myseq.t =
  if depth = 0
  then f x
  else
    match x with
    | `Seq (d,l) ->
       let* ly =
         Myseq.product_fair
           (List.map (map_myseq ~depth:(depth-1) delta_depth f) l) in
       let dy = d + delta_depth in
       assert (dy >= 0);
       Myseq.return (`Seq (dy, ly))
    | _ -> f x

let rec map2 ?(depth = -1) (delta_depth : int) (f : 'a -> 'b -> 'c) (x1 : 'a t) (x2 : 'b t) : 'c t =
  (* delta_depth = depth(c) - depth(a) *)
  if depth = 0
  then f x1 x2
  else
    match x1, x2 with
    | `Seq (d1,l1), `Seq (d2,l2) ->
       if List.length l1 = List.length l2
       then
         let dy = d1 + delta_depth in
         assert (dy >= 0);
         `Seq (dy, List.map2 (map2 ~depth:(depth-1) delta_depth f) l1 l2)
       else invalid_arg "Ndseq.map2: inconsistent lengths"
    | _ -> f x1 x2

let combine2 ?(depth = -1) x1 x2 =
  map2 ~depth 0 (fun x1 x2 -> `X2 (x1,x2)) x1 x2

let rec map2_result ?(depth = -1) (delta_depth : int) (f : 'a -> 'b -> 'c result) (x1 : 'a t) (x2 : 'b t) : 'c t result =
  if depth = 0
  then f x1 x2
  else
    match x1, x2 with
    | `Seq (d1,l1), `Seq (d2,l2) ->
       if List.length l1 = List.length l2
       then
         let l = List.combine l1 l2 in
         let| ly =
           list_map_result
             (fun (x1,x2) ->
               map2_result ~depth:(depth-1) delta_depth f x1 x2)
             l in
         let dy = d1 + delta_depth in
         assert (dy >= 0);
         Result.Ok (`Seq (dy, ly))
       else invalid_arg "Utilities.XSeq.map2: inconsistent structure"
    | _ -> f x1 x2

let mapn_n ?(name = "?") ~(depth : int) (res_depth : int array) (f : int list -> 'a t array -> 'b t array) (args : 'a t array) : 'b t array =
  (* res_depth is relative to depth: result ndim = depth + res_depth, not relative to arg ndim *)
  assert (args <> [||]);
  let m = Array.length res_depth in
  let res_nil = Array.make m [] in
  let rec aux rev_path depth args =
    if depth = 0
    then
      let res = f rev_path args in
      let () =
        if not (Array.length res = m) then
          invalid_arg ("Ndseq.mapn_n: inconsistent nb of results @ " ^ name) in
      res
    else
      let args_l : 'a list array =
        Array.map
          (function
           | `Seq (_,li) -> li
           | _ -> assert false)
          args in
      let rec aux2 pos args_l =
        if Array.for_all (fun l -> l = []) args_l then
          res_nil
        else if Array.exists (fun l -> l = []) args_l then
          invalid_arg ("Ndseq.mapn_n: inconsistent lengths @ " ^ name)
        else
          let args_hd = Array.map List.hd args_l in
          let args_tl = Array.map List.tl args_l in
          let res_hd = aux (pos::rev_path) (depth-1) args_hd in
          let res_tl = aux2 (pos+1) args_tl in
          let res = Array.map2 (fun hd tl -> hd::tl) res_hd res_tl in
          res
      in
      let res_l = aux2 0 args_l in
      let res =
        Array.mapi
          (fun i l ->
            let d = depth - 1 + res_depth.(i) in
            assert (d >= 0);
            `Seq (d, l))
          res_l in
      res
  in
  aux [] depth args

let mapi_tup ?name ~depth res_depth (f : int list -> 'a -> 'b) (args : 'a) : 'b =
  (* BEWARE: make sure to use 'tup1' to build singleton tuples !!! *)
  (* checking parameters *)
  let repr_res_depth = Obj.repr res_depth in
  let repr_args = Obj.repr args in
  assert (Obj.is_block repr_args && Obj.tag repr_args = 0); (* args is a tuple *)
  let n = Obj.size repr_args in
  let res_depth, m =
    if Obj.is_int repr_res_depth
    then (Obj.magic [|res_depth|] : int array), 1
    else (
      assert (Obj.is_block repr_res_depth && Obj.tag repr_res_depth = 0);
      let m = Obj.size repr_res_depth in
      for i = 0 to m-1 do assert (Obj.is_int (Obj.field repr_res_depth i)) done; (* res_depth is made of ints *)
      (Obj.magic res_depth : int array), m
    ) in
  let (res : 'bx t array) =
    mapn_n ?name ~depth
      res_depth
      (fun (rev_path : int list) (args : 'ax array) ->
        let args = if n = 1 then (Obj.magic args.(0) : 'a) else (Obj.magic args : 'a) in (* singleton handling *)
        let res = f rev_path args in
        (* checking result *)
        if m = 1
        then (Obj.magic [|res|] : 'bx array)
        else
          let repr_res = Obj.repr res in
          assert (Obj.is_block repr_res && Obj.tag repr_res = 0);
          if not (Obj.size repr_res = m) then failwith "Ndseq.map*_tup: inconsistent number of results";
          (Obj.magic res : 'bx array)) (* from tuple *)
      (Obj.magic args : 'ax t array) in
  if m = 1 then (Obj.magic res.(0) : 'b) else (Obj.magic res : 'b) (* singleton handling *)

let map_tup ?name ~depth res_depth (f : 'a -> 'b) (args : 'a) : 'b =
  mapi_tup ?name ~depth res_depth (fun rev_path -> f) args [@@inline]


let mapn_n_myseq ?(name = "?") ~(depth : int) (res_depth : int array) (f : int list -> 'a array -> 'b array Myseq.t) (args : 'a t array) : 'b t array Myseq.t =
  assert (args <> [||]);
  let m = Array.length res_depth in
  let rec aux rev_path depth args =
    if depth = 0
    then
      let* res = f rev_path args in
      let () =
        if not (Array.length res = m) then
          invalid_arg ("Ndseq.mapn_n_myseq: inconsistent nb of results @ " ^ name) in
      Myseq.return res
    else
      let args_l : 'a list array =
        Array.map
          (function
           | `Seq (_,li) -> li
           | _ -> assert false)
          args in
      let rec aux2 pos args_l : 'b t array Myseq.t list =
        if Array.for_all (fun l -> l = []) args_l then
          []
        else if Array.exists (fun l -> l = []) args_l then
          invalid_arg ("Ndseq.mapn_n_myseq: inconsistent lengths @ " ^ name)
        else
          let args_hd = Array.map List.hd args_l in
          let args_tl = Array.map List.tl args_l in
          let res_s_hd = aux (pos::rev_path) (depth-1) args_hd in
          let res_s_tl = aux2 (pos+1) args_tl in
          res_s_hd::res_s_tl
      in
      let res_s_l = aux2 0 args_l in
      let* res_l : 'b t array list = Myseq.product_fair res_s_l in
      let res : 'b t array =
        Array.init m
          (fun j ->
            let l =
              List.map
                (fun res ->
                  res.(j))
                res_l in
            let d = depth - 1 + res_depth.(j) in
            assert (d >= 0);
            `Seq (d, l)) in
      Myseq.return res
  in
  aux [] depth args

let mapi_tup_myseq ?name ~depth res_depth (f : int list -> 'a -> 'b Myseq.t) (args : 'a) : 'b Myseq.t =
  (* BEWARE: make sure to use 'tup1' to build singleton tuples !!! *)
  (* checking parameters *)
  let repr_res_depth = Obj.repr res_depth in
  let repr_args = Obj.repr args in
  assert (Obj.is_block repr_args && Obj.tag repr_args = 0); (* args is a tuple *)
  let n = Obj.size repr_args in
  let res_depth, m =
    if Obj.is_int repr_res_depth
    then (Obj.magic [|res_depth|] : int array), 1
    else (
      assert (Obj.is_block repr_res_depth && Obj.tag repr_res_depth = 0);
      let m = Obj.size repr_res_depth in
      for i = 0 to m-1 do assert (Obj.is_int (Obj.field repr_res_depth i)) done; (* res_depth is made of ints *)
      (Obj.magic res_depth : int array), m
    ) in
  let* (res : 'bx t array) =
    mapn_n_myseq ?name ~depth
      (Obj.magic res_depth : int array) (* from int tuple *)
      (fun (rev_path : int list) (args : 'ax array) ->
        let args = if n = 1 then (Obj.magic args.(0) : 'a) else (Obj.magic args : 'a) in (* singleton handling *)
        let* res = f rev_path args in
        (* checking result *)
        if m = 1
        then Myseq.return (Obj.magic [|res|] : 'bx array)
        else
          let repr_res = Obj.repr res in
          assert (Obj.is_block repr_res && Obj.tag repr_res = 0);
          if not (Obj.size repr_res = m) then failwith "Ndseq.map*_tup_myseq: inconsistent number of results";
          Myseq.return (Obj.magic res : 'bx array)) (* from tuple *)
      (Obj.magic args : 'ax t array) in
  let res = if m = 1 then (Obj.magic res.(0) : 'b) else (Obj.magic res : 'b) in
  Myseq.return res

let map_tup_myseq ?name ~depth res_depth (f : 'a -> 'b Myseq.t) (args : 'a) : 'b Myseq.t =
  mapi_tup_myseq ?name ~depth res_depth (fun rev_path -> f) args [@@inline]

let test1_map_tup_myseq ~depth x1 x2 x3 : ('b1 * 'b2) Myseq.t =
  map_tup_myseq ~name:"test1" ~depth (0,0)
    (function
     | (`A a1,`A a2,`A a3) -> Myseq.return (`A (a1+a2), `A (a1-a2))
     | _ -> assert false)
    (x1,x2,x3)
let test2_map_tup_myseq ~depth (x : 'a) : 'b Myseq.t =
  map_tup_myseq ~name:"test2" ~depth (tup1 0)
    (function
     | `A a -> Myseq.return (tup1 (`A (2*a)))
     | _ -> assert false)
    (tup1 x)


let rec match_myseq (delta_depth : int) (f : 'a -> 'b -> 'c Myseq.t) (x1 : 'a t) (x2 : 'b t) : 'c t Myseq.t =
  (* delta_depth = depth(c or d) - dpeth(b) *)
  match x1, x2 with
  | `Seq (_,[]), `Seq (d2,l2) ->
     if l2 = []
     then
       let d = d2 + delta_depth in
       Myseq.return (`Seq (d, []))
     else Myseq.empty
  | `Seq (_,l1), `Seq (d2,l2) ->
     let n1 = List.length l1 in
     let n2 = List.length l2 in
     let n1, l1 =
       if n1 >= n2
       then n1, l1
       else (* assuming periodic sequence from l1 *)
         let k = (n2 - 1) / n1 + 1 in
         n1 * k, List.concat (List.init k (fun _ -> l1)) in
     let l1 = if n1 = n2 then l1 else Common.sub_list l1 0 n2 in
     let d = d2 + delta_depth in
     assert (d >= 0);
     let* ly = Myseq.product_fair (List.map2 (match_myseq delta_depth f) l1 l2) in
     Myseq.return (`Seq (d, ly))
  | _, `Seq (d2,l2) -> (* broadcast x1 *)
     let d = d2 + delta_depth in
     assert (d >= 0);
     let* ly = Myseq.product_fair (List.map (match_myseq delta_depth f x1) l2) in
     Myseq.return (`Seq (d, ly))
  | `Seq _, _ -> Myseq.empty
  | _ -> f x1 x2

let rec matches (delta_depth : int) (f : 'a -> 'b -> bool) (x1 : 'a t) (x2 : 'b t) : bool =
  (* delta_depth = depth(c or d) - dpeth(b) *)
  match x1, x2 with
  | `Seq (_,[]), `Seq (d2,l2) -> l2 = []
  | `Seq (_,l1), `Seq (d2,l2) ->
     let n1 = List.length l1 in
     let n2 = List.length l2 in
     let n1, l1 =
       if n1 >= n2
       then n1, l1
       else (* assuming periodic sequence from l1 *)
         let k = (n2 - 1) / n1 + 1 in
         n1 * k, List.concat (List.init k (fun _ -> l1)) in
     let l1 = if n1 = n2 then l1 else Common.sub_list l1 0 n2 in
     let d = d2 + delta_depth in
     assert (d >= 0);
     List.for_all2 (matches delta_depth f) l1 l2
  | _, `Seq (d2,l2) -> (* broadcast x1 *)
     let d = d2 + delta_depth in
     assert (d >= 0);
     List.for_all (matches delta_depth f x1) l2
  | `Seq _, _ -> false
  | _ -> f x1 x2

let rec for_all ?(depth = -1) (f : 'a -> bool) (x : 'a t) : bool =
  if depth = 0
  then f x
  else
    match x with
    | `Seq (d,l) -> List.for_all (for_all ~depth:(depth-1) f) l
    | _ -> f x

(* DEPR let nest_path (rev_path : int list) (x : 'a t) : int list * 'a t = (* returns List.rev rev_path, and x at the end of path *)
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
  | pos::path1, `Seq (_, Some pos', [x1]) ->
     if pos = pos'
     then unnest_path path1 x1
     else invalid_arg "Ndseq.unnest_path: inconsistent position"
  | _ -> invalid_arg "Ndseq.unnest_path: inconsistent path"

let parseur_item (p : 'a t -> 'data Myseq.t) (rev_path : int list) (input_item : 'a) : 'value Myseq.t =
  let path, input = nest_path rev_path input_item in
  let* data = p input in
  let v_item = unnest_path path (Data.value data) in
  Myseq.return v_item

let parseur_item2 (p : 'a t -> 'b t -> 'data Myseq.t) (rev_path : int list) (v_item : 'a) (r_item : 'b) : 'value Myseq.t =
  let path, v = nest_path rev_path v_item in
  let _path, r = nest_path rev_path r_item in
  let* data = p v r in
  let v_item = unnest_path path (Data.value data) in
  Myseq.return v_item

let is_complete ~depth (x : 'a t) : bool =
  for_all ~depth
    (function
     | `Seq (_,_) -> pos_opt = None
     | _ -> raise Invalid_depth)
    x *)

let seq_of_seq (f : 'a list -> 'b list) (items : 'a t) : 'b t =
  (* a and b should have same depth *)
  match items with
  | `Seq (d,l) -> `Seq (d, f l)
  | _ -> raise Invalid_depth

let item_of_seq (f : 'a list -> 'b) (items : 'a t) : 'b =
  match items with
  | `Seq (d,l) -> f l
  | _ -> raise Invalid_depth

let item_of_seq2 (f : 'a list -> 'b list -> 'c) (items1 : 'a t) (items2 : 'b t) : 'c =
  match items1, items2 with
  | `Seq (d1,l1), `Seq (d2,l2) -> f l1 l2
  | _ -> raise Invalid_depth

let item_of_item_seq (f : 'a -> 'b list -> 'c) (x1 : 'a) (x2 : 'b t) : 'c =
  match x2 with
  | `Seq (d2,l2) -> f x1 l2
  | _ -> raise Invalid_depth

let seq_of_item_seq (f : 'a -> 'b list -> 'c list) (x1 : 'a) (x2 : 'b t) : 'c t =
  (* b and c should have the same depth *)
  match x2 with
  | `Seq (d2,l2) -> `Seq (d2, f x1 l2)
  | _ -> raise Invalid_depth

let seq_of_seq2 (f : 'a list -> 'b list -> 'c list) (x1 : 'a t) (x2 : 'b t) : 'c t =
  (* a, b, c should have the same depth *)
  match x1, x2 with
  | `Seq (d1,l1), `Seq (d2,l2) ->
     assert (d1 = d2);
     `Seq (d1, f l1 l2)
  | _ -> raise Invalid_depth

let seq_of_item (f : 'a -> 'b list) (x : 'a) : 'b t =
  (* b should have depth 0 *)
  `Seq (0, f x)

let head ~(depth : int) (x : 'a t) : 'a option =
  map_option ~depth (-1)
    (function
     | `Seq (d,l) ->
        (match l with
         | x0::_ -> Some x0
         | _ -> None)
     | _ -> raise Invalid_depth)
    x

let tail ~(depth : int) (x : 'a t) : 'a t option =
  map_option ~depth 0
    (function
     | `Seq (d,l) ->
        (match l with
         | x0::l1 -> Some (`Seq (d,l1))
         | _ -> None)
     | _ -> raise Invalid_depth)
    x

let head_tail ~(depth : int) (x : 'a t) : ('a * 'a t) Myseq.t =
  let ndim = ndim x in
  map_tup_myseq ~depth (ndim - depth - 1, ndim - depth)
    (function
     | `Seq (d,l) ->
        assert (d = ndim - depth - 1);
        (match l with
         | x0::l1 -> Myseq.return (x0, `Seq (d,l1))
         | _ -> Myseq.empty)
     | _ -> raise Invalid_depth)
    (tup1 x)

let cons ~(depth : int) (hd : 'a t) (tl : 'a t) : 'a t =
  map2 ~depth (+1)
    (fun x0 x1 ->
      match x1 with
      | `Seq (d1,l1) -> `Seq (d1, x0::l1)
      | _ -> raise Invalid_depth)
    hd tl

let index ~(depth : int) (i : int) (x : 'a t) : 'a option =
  map_option ~depth (-1)
    (function
     | `Seq (d,l) ->
        let n = List.length l in
        if i >= 0 && i < n then Some (List.nth l i)
        else if i < 0 && i >= -n then Some (List.nth l (n+i))
        else None
     | _ -> raise Invalid_depth)
    x

let index_list (x : 'a t) (is : int option list) : 'a t option =
  let rec aux delta_depth is x =
    match is, x with
    | [], _ -> Some x
    | (Some i)::is1, `Seq (d,l) ->
       let@ x1 =
         let n = List.length l in
         if i >= 0 && i < n then Some (List.nth l i)
         else if i < 0 && i >= -n then Some (List.nth l (n+i))
         else None in
       aux (delta_depth+1) is1 x1
    | None::is1, `Seq (d,l) ->
       let@ l' = list_mapi_option (fun _ x1 -> aux delta_depth is1 x1) l in
       let d' = d + delta_depth in
       assert (d' >= 0);
       Some (`Seq (d', l'))
    | _ -> invalid_arg "Ndseq.index: is is too long"
  in
  let delta_depth =
    List.fold_left
      (fun res -> function
        | None -> res
        | Some _ -> res - 1)
      0 is in
  aux delta_depth is x

let transpose (x : 'a t) : 'a t option =
  match x with
  | `Seq (d0,l0) ->
     (match l0 with
      | [] -> Some x (* empty ndseq *)
      | `Seq (d1,l1) :: r0 ->
         let n1 = List.length l1 in
         let@ l01 =
           list_mapi_option
             (fun _ -> function
               | `Seq (_,l1') ->
                  if List.length l1' = n1
                  then Some l1
                  else None (* not a proper matrix *)
               | _ -> None)
             l0 in
         let l10 = list_list_transpose l01 in
         let l1 = List.map (fun l0 -> `Seq (d1, l0)) l10 in
         Some (`Seq (d0, l1))
      | _ -> None)
  | _ -> None

let flatten_by_rows ?(snake = false) (x : 'a t) : 'a t option =
  match x with
  | `Seq (d0,l0) ->
     (match l0 with
      | [] -> Some x (* empty ndseq *)
      | `Seq (d1,l1) :: _ ->
         let@ ll1 =
           list_mapi_option
             (fun j -> function
               | `Seq (_, l1') ->
                  if snake && j mod 2 <> 0
                  then Some (List.rev l1')
                  else Some l1'
               | _ -> None)
             l0 in
         let l01 = List.concat ll1 in
         Some (`Seq (d1, l01))
      | _ -> None)
  | _ -> None

let flatten_by_cols ?(snake = false) (x : 'a t) : 'a t option =
  let@ x' = transpose x in
  flatten_by_rows ~snake x'

(* broadcasting of scalar functions *)

exception Invalid_broadcast

let all_same_size_or_one (xs : 'a t array) : int option =
  Array.fold_left
    (fun size_opt x ->
      match size_opt with
      | None -> None
      | Some size ->
         match x with
         | `Seq (d,l) ->
            let n = List.length l in
            if n = 0 then None
            else if size = 1 || n = 1 || size = n then Some (max size n)
            else None
         | _ -> Some size)
    (Some 1) xs

let broadcastable (xs : 'a t array) : bool =
  (* when broadcast_result is well-defined *)
  let rec aux xs =
    if Array.for_all (fun x -> depth x = 0) xs (* all scalars *)
    then true
    else
      match all_same_size_or_one xs with
      | Some size ->
         assert (size > 0);
         Common.fold_for
           (fun i ok ->
             ok
             && (let xs_i = (* [t1[i], ..., tk[i] *)
                   Array.map
                     (function
                      | `Seq (d,l) ->
                         let n = List.length l in
                         List.nth l (i mod n)
                      | x -> x)
                     xs in
                 aux xs_i))
           0 (size-1)
           true
      | None -> false
  in
  match xs with
  | [||] -> true
  | [|x1|] -> true
  | _ -> aux xs

let broadcast_result (f : 'a array -> 'b result) (xs : 'a t array) : 'b t result =
  (* function application by broadcasting through an array of ndseqs *)
  (* when the function application fails, the whole broadcast fails *)
  let rec aux d xs =
    if d = 0 (* Array.for_all (fun x -> depth x = 0) ts *) (* all scalars *)
    then f xs (* apply the scalar function *)
    else
      match all_same_size_or_one xs with
      | Some size -> (* broadcastable: all ndseqs have equal size or size=1 on first axis *)
         assert (size > 0);
         let| xs_y: 'b t list =
           list_mapi_result
             (fun i () ->
               let xs_i = (* [x1[i], ..., xk[i] *)
                 Array.map
                   (function
                    | `Seq (d,l) ->
                       let n = List.length l in
                       List.nth l (i mod n)
                    | x -> x)
                   xs in
               aux (d-1) xs_i)
             (List.init size (fun _ -> ())) in
         Result.Ok (`Seq (d-1, xs_y))
      | None ->
         Result.Error Invalid_broadcast
  in
  match xs with
  | [||] -> f [||]
  | [|x1|] -> map_result 0 (fun x1 -> f [|x1|]) x1
  | _ ->
     let d =
       Array.fold_left
         (fun res x -> max res (depth x))
         0 xs in
     aux d xs (* the real broadcasting case *)

let index_list_broadcast (x : 'a t) (is : int list) (depth_result : int) : 'a t option =
  let rec aux is x =
    match is, x with
    | [], _ -> aux2 x
    | i::is1, `Seq (d,l) ->
       if d < depth_result
       then None (* index too deep *)
       else
         let@ x1 =
           let n = List.length l in
           if i >= 0 && i < n then Some (List.nth l i)
           else if i < 0 && i >= -n then Some (List.nth l (n+i))
           else None in
         aux is1 x1
    | i::is1, _ -> aux is1 x (* broadcast *)
  and aux2 x =
    match x with
    | `Seq (d,l) ->
       if d + 1 = depth_result then
         Some x
       else if d >= depth_result then
         match l with
         | [x1] -> aux2 x1 (* broadcast *)
         | _ -> None (* ambiguity *)
       else None
    | _ ->
       if depth_result = 0
       then Some x
       else None
  in
  aux is x


let _ = (* UNIT TEST *)
  let x = `Seq (0, [`Int 1; `Int 2; `Int 3]) in
  let y1 = map 0 (function `Int n -> `String (string_of_int n) | _ -> assert false) x in
  assert (y1 = `Seq (0, [`String "1"; `String "2"; `String "3"]));
  let y2 = map (+1) (function `Int n -> `Seq (0, List.init n (fun i -> `Int i)) | _ -> assert false) x in
  assert (y2 = `Seq (1, [`Seq (0, [`Int 0]);
                         `Seq (0, [`Int 0; `Int 1]);
                         `Seq (0, [`Int 0;`Int 1;`Int 2])]));
  ()
