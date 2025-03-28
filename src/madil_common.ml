
exception TODO

module TEST = (* for profiling visually, used for the JS version *)
  struct
    let prof name f =
      print_endline (name ^ "...");
      let res = f () in
      print_endline ("DONE " ^ name);
      res
  end

(* tuples *)

type 'a double = 'a * 'a
type 'a triple = 'a * 'a * 'a

let tup1 (x : 'a) = (Obj.magic [|x|] : 'a)

(* list *)

let rec list_take k = function
  | [] -> []
  | x::r ->
     if k <= 0
     then []
     else x :: list_take (k-1) r

let list_foldi_left (f : 'b -> int -> 'a -> 'b) (init : 'b) (l : 'a list) : 'b =
  let rec aux acc i l =
    match l with
    | [] -> acc
    | x::r -> aux (f acc i x) (i+1) r
  in
  aux init 0 l

let rec list_remove x l =
  match l with
  | [] -> []
  | y::xs ->
     if y = x
     then xs
     else y::list_remove x xs
               
let rec list_update (f : 'a -> 'a) (i : int) : 'a list -> 'a list = function
  | [] -> raise Not_found
  | x::l ->
     if i = 0
     then f x :: l
     else x :: list_update f (i-1) l

let rec list_replace_assoc (k : 'a) (v : 'b) (l : ('a * 'b) list) : ('a * 'b) list =
  match l with
  | [] -> []
  | (x,y)::xs ->
     if x = k
     then (k,v)::xs
     else (x,y)::list_replace_assoc k v xs

let rec list_partition_map (f : 'a -> ('b,'c) Result.t) (selected : 'a list) (others : 'c list) : 'b list * 'c list =
  match selected with
  | [] -> [], others
  | x::r ->
     let r1, r2 = list_partition_map f r others in
     ( match f x with
     | Result.Ok y -> y::r1, r2
     | Result.Error z -> r1, z::r2 )

let rec list_map3 (f : 'a -> 'b -> 'c -> 'd) (l1 : 'a list) (l2 : 'b list) (l3 : 'c list) : 'd list =
  match l1, l2, l3 with
  | [], [], [] -> []
  | x1::r1, x2::r2, x3::r3 -> f x1 x2 x3 :: list_map3 f r1 r2 r3
  | _ -> invalid_arg "Madil_common.list_map3: inconsistent lengths"

let list_list_map (f : 'a -> 'b) (reads : 'a list list) : 'b list list  =
  List.map
    (fun l ->
      List.map f l)
    reads

let list_mapi_monad (type a b bm blm) (return : b list -> blm) (bind : bm -> (b -> blm) -> blm) (bind_list : blm -> (b list -> blm) -> blm) (f : int -> a -> bm) (l : a list) : blm =
  let rec aux i = function
    | [] -> return []
    | x::xs ->
       bind (f i x)
         (fun y ->
           bind_list (aux (i+1) xs)
             (fun ys ->
               return (y::ys)))
  in
  aux 0 l
let list_mapi_option =
  fun f l -> list_mapi_monad Option.some Option.bind Option.bind f l
let list_mapi_result =
  fun f l -> list_mapi_monad Result.ok Result.bind Result.bind f l
let list_mapi_myseq =
  fun f l -> list_mapi_monad Myseq.return Myseq.bind Myseq.bind f l


let rec list_list_transpose (ll : 'a list list) : 'a list list =
  if List.for_all (fun l -> l <> []) ll
  then
    let l_hd_tl =
      List.map
        (function
         | [] -> assert false
         | x::r -> x, r)
        ll in
    let l_hd, l_tl = List.split l_hd_tl in
    l_hd :: list_list_transpose l_tl
  else List.map (fun _ -> []) ll

(* array *)

let array_float_sum : float array -> float = Array.fold_left (+.) 0.

let array_reverse (ar : 'a array) : 'a array =
  let n = Array.length ar in
  Array.init n (fun i -> ar.(n-i-1))

let array_rotate (ar : 'a array) (shift : int) : 'a array =
  let n = Array.length ar in
  Array.init n (fun i -> ar.((i + n * (abs shift) - shift) mod n)) (* + n*shift to ensure positive value before applying modulo *)

(* option *)

let ( let@ ) = Option.bind

(* result *)
        
type 'a result = ('a,exn) Result.t
let ( let| ) res f = Result.bind res f [@@inline]

let catch (r : 'a result) (h : exn -> 'a result) : 'a result =
  match r with
  | Result.Ok _ -> r
  | Result.Error exn -> h exn
                   
let rec list_map_result (f : 'a -> ('b,'c) Result.t) (lx : 'a list) : ('b list, 'c) Result.t =
  match lx with
  | [] -> Result.Ok []
  | x::lx1 ->
     let| y = f x in
     let| ly1 = list_map_result f lx1 in
     Result.Ok (y::ly1)

let array_map_result (f : 'a -> 'b result) (xs : 'a array) : 'b array result =
  try
    Result.Ok
      (Array.map
         (fun x ->
           match f x with
           | Result.Ok y -> y
           | Result.Error exn -> raise exn)
         xs)
  with exn ->
    Result.Error exn

let array_mapi_result (f : int -> 'a -> 'b result) (xs : 'a array) : 'b array result =
  try
    Result.Ok
      (Array.mapi
         (fun i x ->
           match f i x with
           | Result.Ok y -> y
           | Result.Error exn -> raise exn)
         xs)
  with exn ->
    Result.Error exn

let result_list_bind_some (lx_res : ('a list,'c) Result.t) (f : 'a -> ('b list,'c) Result.t) : ('b list, 'c) Result.t =
  let rec aux = function
  | [] -> invalid_arg "Model2.bind_map_ok: empty list"
  | [x] -> f x
  | x::lx1 ->
     let open Result in
     match f x, aux lx1 with
     | Ok ly0, Ok ly1 -> Ok (List.append ly0 ly1)
     | Ok ly0, Error _ -> Ok ly0
     | Error _, Ok ly1 -> Ok ly1
     | Error e1, Error _ -> Error e1
  in
  let| lx = lx_res in
  aux lx
let ( let+|+ ) = result_list_bind_some


(* seq *)

module Seq = Stdlib.Seq (* the standard one, not Myseq *)

let ( let* ) seq f = seq |> Myseq.flat_map f [@@inline]
let ( let*? ) seq f = seq |> Myseq.filter_map f [@@inline]
let ( let*! ) seq f = seq |> Myseq.map f [@@inline]
let myseq_cons_if cond x seq =
  if cond
  then Myseq.cons x seq
  else seq
let myseq_concat_if cond seq1 seq2 =
  if cond
  then Myseq.concat [seq1; seq2]
  else seq2

let myseq_bind_sample_fair ~(size1 : int) ~(size2 : int) (s : 'a Myseq.t) (f : 'a -> 'b Myseq.t) : bool (* s is not empty? *) * 'a list * 'b list =
(* sample size1 ['a] from [s] for which there is some ['b], and sample size2 such ['b] per ['a], hence returns at most size1 x size2 ['b] *)
  let rec aux quota1 ok1 rev_acc1 rev_acc12 s =
    if quota1 <= 0
    then ok1, rev_acc1, rev_acc12
    else
      match s () with
      | Myseq.Nil -> ok1, rev_acc1, rev_acc12
      | Myseq.Cons (x,next) ->
         let s2 = f x in
         let ok2, rev_acc12 = aux2 size2 false rev_acc12 x s2 in
         if ok2
         then aux (quota1 - 1) true (x::rev_acc1) rev_acc12 next
         else aux quota1 true rev_acc1 rev_acc12 next
  and aux2 quota2 ok2 rev_acc12 x s2 =
    if quota2 <= 0
    then ok2, rev_acc12
    else
      match s2 () with
      | Myseq.Nil -> ok2, rev_acc12
      | Myseq.Cons (y,next2) -> aux2 (quota2 - 1) true (y::rev_acc12) x next2
  in
  let ok1, rev_acc1, rev_acc12 = aux size1 false [] [] s in
  ok1, List.rev rev_acc1, List.rev rev_acc12

let myseq_find_map_k (k : int) (f : 'a -> 'b option) (s : 'a Myseq.t) : 'b list =
  let rec aux i s acc =
    if i >= k then acc
    else
      match Myseq.find_map f s with
      | Some (y,next) -> aux (i+1) next (y::acc)
      | None -> acc
  in
  List.rev (aux 0 s [])
  
(* xprint *)

type 'a html_xp = html:bool -> 'a Xprint.xp

let pp (xp : 'a html_xp) (x : 'a) : unit =
  Xprint.to_stdout (xp ~html:false) x

let pp_endline xp x =
  pp xp x;
  print_newline ()

let to_string (xp : 'a html_xp) (x : 'a) : string =
  Xprint.to_string (xp ~html:false) x
  
let xp_newline : unit html_xp =
  fun ~html print () ->
  if html
  then print#string "<br/>"
  else print#string "\n"

let xp_brackets : (unit -> unit) html_xp =
  fun ~html print p ->
  if html then print#string "<div class=\"model-brackets\">" else print#string "(";
  p ();
  if html then print#string "</div>" else print#string ")"

let xp_brackets_prio ~prio_ctx ~prio : (unit -> unit) html_xp =
  fun ~html print p ->
  if prio <= prio_ctx
  then p ()
  else xp_brackets ~html print p

let xp_tuple1 ?(delims = "(",")") (xp1 : 'a1 html_xp) : 'a1 html_xp =
  fun ~html print x1 ->
  let left, right = delims in
  print#string left;
  xp1 ~html print x1;
  print#string right

let xp_tuple2 ?(delims = "(",")") ?(sep = ", ") (xp1 : 'a1 html_xp) (xp2 : 'a2 html_xp) : ('a1 * 'a2) html_xp =
  fun ~html print (x1,x2) ->
  let left, right = delims in
  print#string left;
  xp1 ~html print x1;
  print#string sep;
  xp2 ~html print x2;
  print#string right

let xp_tuple3 ?(delims = "(",")") ?(sep = ", ") (xp1 : 'a1 html_xp) (xp2 : 'a2 html_xp) (xp3 : 'a3 html_xp) : ('a1 * 'a2 * 'a3) html_xp =
  fun ~html print (x1,x2,x3) ->
  let left, right = delims in
  print#string left;
  xp1 ~html print x1;
  print#string sep;
  xp2 ~html print x2;
  print#string sep;
  xp3 ~html print x3;
  print#string right

let xp_tuple ?(delims = "(",")") ?(sep = ", ") (xps : unit html_xp array) : unit html_xp =
  fun ~html print () ->
  let left, right = delims in
  print#string left;
  Array.iteri
    (fun i xpi ->
      if i > 0 then print#string sep;
      xpi ~html print ())
    xps;
  print#string right

let xp_array ?(delims = "[","]") ?(sep = ", ") (xp : 'a html_xp) : 'a array html_xp =
  fun ~html print xs ->
  let left, right = delims in
  print#string left;
  Array.iteri
    (fun i xi ->
      if i > 0 then print#string sep;
      xp ~html print xi)
    xs;
  print#string right

let xp_list ?(delims = "[","]") ?(sep = ", ") (xp : 'a html_xp) : 'a list html_xp =
  fun ~html print xs ->
  let left, right = delims in
  print#string left;
  List.iteri
    (fun i xi ->
      if i > 0 then print#string sep;
      xp ~html print xi)
    xs;
  print#string right
  
let xp_html_elt (tag : string) ?(classe : string = "") : (unit -> unit) html_xp =
  fun ~html print p ->
  if html then
    if classe = ""
    then print#string ("<" ^ tag ^ ">")
    else print#string ("<" ^ tag ^ " class=\"" ^ String.escaped classe ^ "\">");
  p ();
  if html then print#string ("</" ^ tag ^ ">")

(* combinatorics *)

let sum_conv ?(min_arg = 0) (lf : (int -> float) list) (n : int) : float =
  (* distributes [n] over functions in [lf], multiply results, sums over all distribs *)
  (* assuming [f n] = 0. for n < min_arg, i.e. size of elements at least min_arg *)
  (* TODO: memoize recursive calls? *)
  let rec aux k lf n =
    match lf with
    | [] -> if n = 0 then 1. else 0.
    | [f1] -> f1 n
    | f1::lf2 ->
       Common.fold_for
         (fun n1 res ->
           let card1 = f1 n1 in
           if card1 > 0.
           then res +. card1 *. aux (k - 1) lf2 (n - n1)
           else res)
         min_arg (n - (k - 1) * min_arg) 0.
  in
  let k = List.length lf in
  aux k lf n

let distribute (n : int) (lf : (int -> 'a Myseq.t) array) : 'a array Myseq.t =
  (* distributes [n] over functions in [lf] *)
  let rec aux k lf n =
    match lf with
    | [] ->
       if n = 0
       then Myseq.return []
       else Myseq.empty
    | [f1] ->
       let* x1 = f1 n in
       Myseq.return [x1]
    | f1::lf' ->
       let* n1 = Myseq.range 1 (n-k+1) in (* leave at least cost 1 for each other elt *)
       let n' = n - n1 in
       let seq_x1 = f1 n1 in
       let seq_lx' = aux (k-1) lf' n' in
       let* x1 = seq_x1 in
       let* lx' = seq_lx' in
       Myseq.return (x1::lx')
  in
  let k = Array.length lf in
  if n < k then Myseq.empty
  else
    let* lx = aux k (Array.to_list lf) n in
    Myseq.return (Array.of_list lx)

(* mdl *)
                   
type dl = Mdl.bits

let dl0 = 0.

let dl_round dl = Float.round (dl *. 1e9) /. 1e9

let dl_compare (dl1 : float) (dl2 : float) =
  if dl1 < dl2 then -1
  else if dl1 = dl2 then 0
  else 1 [@@inline]
