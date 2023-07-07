
open Madil_common
open Data
open Path

type ('dconstr,'func) expr =
  | Ref of 'dconstr path
  | Apply of 'func * ('dconstr,'func) expr array
  | Arg (* implicit unique argument of functions *)
  | Fun of ('dconstr,'func) expr (* support for unary functions, to be used as arg of higher-order functions *)

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
    | Arg -> print#string "_"
    | Fun e1 -> print#string "fun { "; aux print e1; print#string " }"
  in
  fun print e ->
  Xprint.bracket ("{","}") aux
    print e


let eval
      ~(eval_func : 'func -> 'value array -> 'value result)
      ~(eval_arg : unit -> 'value result) (* the value should be the identity function *)
      (lookup : 'dconstr path -> 'value result)
      (e : ('dconstr,'func) expr) : 'value result =
  let rec aux e =
    match e with
    | Ref p -> lookup p
    | Apply (f,args) ->
       let| lv = list_map_result aux (Array.to_list args) in
       eval_func f (Array.of_list lv)
    | Arg -> eval_arg ()
    | Fun e1 -> aux e1
  in
  aux e

  
(* expression sets : idea taken from FlashMeta *)
    
type ('dconstr,'func) exprset = ('dconstr,'func) expritem list
and ('dconstr,'func) expritem =
  | SRef of 'dconstr path
  | SApply of 'func * ('dconstr,'func) exprset array
  | SArg
  | SFun of ('dconstr,'func) exprset

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
  | SArg -> Myseq.return Arg
  | SFun es1 ->
     let* e1 = exprset_to_seq es1 in
     Myseq.return (Fun e1)

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
  | SArg, SArg -> Some SArg
  | SFun es1, SFun es2 ->
     (match exprset_inter es1 es2 with
      | [] -> None
      | es -> Some (SFun es))
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


(* indexes : idea inspired from FlashMeta *)

module Index =
  struct
    type ('value,'dconstr,'func) t = ('value, ('dconstr,'func) exprset) Mymap.t

    let empty = Mymap.empty
                
    let bind (v : 'value) (item : ('dconstr,'func) expritem) (index : ('value,'dconstr,'func) t) : ('value,'dconstr,'func) t =
      Mymap.update v
        (function
         | None -> Some [item]
         | Some exprs -> Some (item :: exprs))
        index

    let bind_set (v : 'value) (es : ('dconstr,'func) exprset) (index : ('value,'dconstr,'func) t) : ('value,'dconstr,'func) t =
      Mymap.update v
        (function
         | None -> Some es
         | Some exprs -> Some (List.rev_append es exprs))
        index

    let find_opt = Mymap.find_opt

    let fold = Mymap.fold
                
    let lookup (v : 'value) (index : ('value,'dconstr,'func) t) : ('dconstr,'func) exprset =
      match find_opt v index with
      | None -> []
      | Some exprs -> exprs
  end
           
let index_add_bindings index (bindings : ('dconstr path * 'value) list) : ('value,'dconstr,'func) Index.t =
  List.fold_left
    (fun res (p,v) -> Index.bind v (SRef p) res)
    index bindings

let index_apply_functions
      index (max_arity : int) (get_functions : 'value array -> ('func * 'value) list)
    : ('value,'dconstr,'func) Index.t =
  let rec aux k lv_k les_k args_k es_args_k res =
    let res =
      get_functions args_k
      |> List.fold_left
           (fun res (f,v) ->
             Index.bind v (SApply (f, es_args_k)) res)
           res in
    if k >= max_arity
    then res
    else
      Index.fold
        (fun v es res ->
          let lv = v::lv_k in
          let les = es::les_k in
          let args = Array.of_list lv in
          let es_args = Array.of_list les in
          aux (k+1) lv les args es_args res)
        index res
  in
  aux 0 [] [] [||] [||] index
