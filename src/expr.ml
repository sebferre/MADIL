
open Madil_common
open Data
open Path

type ('dconstr,'func) expr =
  | Ref of 'dconstr path
  | Apply of 'func * ('dconstr,'func) expr array


let xp_expr
      (print_field : ('dconstr * int) Xprint.xp)
      (print_func : 'func Xprint.xp)
    : ('dconstr,'func) expr Xprint.xp =
  let rec aux print e =
    match e with
    | Ref p -> xp_path print_field print p
    | Apply (f,args) ->
       print_func print f;
       Xprint.bracket ("(",")")
         (Xprint.sep_array ", " aux)
         print args
  in
  fun print e ->
  Xprint.bracket ("{","}") aux
    print e


let eval
      ~(eval_func : 'func -> 'value array -> 'value result)
      (lookup : 'dconstr path -> 'value result)
      (e : ('dconstr,'func) expr) : 'value result =
  let rec aux e =
    match e with
    | Ref p -> lookup p
    | Apply (f,args) ->
       let| lv = list_map_result aux (Array.to_list args) in
       eval_func f (Array.of_list lv)
  in
  aux e

  
(* expression sets : idea taken from FlashMeta *)
    
type ('dconstr,'func) exprset = ('dconstr,'func) expritem list
and ('dconstr,'func) expritem =
  | SRef of 'dconstr path
  | SApply of 'func * ('dconstr,'func) exprset array

let rec exprset_to_seq (es : ('dconstr,'func) exprset) : ('dconstr,'func) expr Myseq.t =
  let* item = Myseq.from_list es in
  expritem_to_seq item
and expritem_to_seq : ('dconstr,'func) expritem -> ('dconstr,'func) expr Myseq.t =
  function
  | SRef p -> Myseq.return (Ref p)
  | SApply (f,es_args) ->
     let seq_args = Array.map exprset_to_seq es_args in
     let* l_args = Myseq.product (Array.to_list seq_args) in (* TODO: extend Myseq for arrays *)
     let args = Array.of_list l_args in
     Myseq.return (Apply (f,args))
     
let rec exprset_inter (es1 : ('dconstr,'func) exprset) (es2 : ('dconstr,'func) exprset) : ('dconstr,'func) exprset =
  List.fold_left
    (fun res item1 ->
      List.fold_left
        (fun res item2 ->
          match expritem_inter item1 item2 with
          | None -> res
          | Some item -> item::res)
        res es2)
    [] es1
and expritem_inter (item1 : ('dconstr,'func) expritem) (item2 : ('dconstr,'func) expritem) : ('dconstr,'func) expritem option =
  match item1, item2 with
  | SRef p1, SRef p2 when p1 = p2 -> Some (SRef p1)
  | SApply (f1,es_args1), SApply (f2,es_args2) when f1 = f2 ->
     let es_args = Array.map2 exprset_inter es_args1 es_args2 in
     if Array.exists (fun es -> es = []) es_args
     then None
     else Some (SApply (f1, es_args))
(*  | `Arg, `Arg -> Some (`Arg)
  | `Fun e1, `Fun e2 ->
     (match exprset_inter e1 e2 with
      | [] -> None
      | e -> Some (`Fun e)) *)
  | _ -> None

let rec exprset_inter_list (esl1 : ('dconstr,'func) exprset list) (esl2 : ('dconstr,'func) exprset list) : ('dconstr,'func) exprset list =
  List.fold_left
    (fun res es1 ->
      List.fold_left
        (fun res es2 ->
          match exprset_inter es1 es2 with
          | [] -> res
          | es -> es::res)
        res esl2)
    [] esl1
