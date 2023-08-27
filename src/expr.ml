
open Madil_common
open Data
open Kind 

type ('var,'func) expr =
  | Ref of 'var
  | Apply of 'func * ('var,'func) expr array
  | Arg (* implicit unique argument of functions *)
  | Fun of ('var,'func) expr (* support for unary functions, to be used as arg of higher-order functions *)

type 'var binding_vars = 'var Bintree.t
let binding_vars0 = Bintree.empty

type ('var,'value) bindings = ('var, 'value) Mymap.t
let bindings0 = Mymap.empty

let xp_expr
      ~(xp_var : 'var html_xp)
      ~(xp_func : 'func html_xp)
    : ('var,'func) expr html_xp =
  let rec aux ~html print e =
    match e with
    | Ref x -> xp_var ~html print x
    | Apply (f,args) ->
       xp_func ~html print f;
       Xprint.bracket ("(",")")
         (Xprint.sep_array ", " (aux ~html))
         print args
    | Arg -> print#string "_"
    | Fun e1 -> print#string "fun { "; aux ~html print e1; print#string " }"
  in
  fun ~html print e ->
  Xprint.bracket ("{","}") (aux ~html)
    print e

(* expression evaluation *)

let eval
      ~(eval_unbound_var : 'var -> 'value result) (* ex: return some null value, or fail *)
      ~(eval_func : 'func -> 'value array -> 'value result)
      ~(eval_arg : unit -> 'value result) (* the value should be the identity function *)
      (e : ('var,'func) expr) (bindings : ('var,'value) bindings)
    : 'value result =
  let rec aux e =
    match e with
    | Ref x ->
       (match Mymap.find_opt x bindings with
        | Some v -> Result.Ok v
        | None -> eval_unbound_var x)
    | Apply (f,args) ->
       let| lv = list_map_result aux (Array.to_list args) in
       eval_func f (Array.of_list lv)
    | Arg -> eval_arg ()
    | Fun e1 -> aux e1
  in
  aux e

  
(* expression sets : idea taken from FlashMeta *)
    
type ('var,'func) exprset = ('var,'func) expritem list
and ('var,'func) expritem =
  | SRef of 'var
  | SApply of 'func * ('var,'func) exprset array
  | SArg
  | SFun of ('var,'func) exprset

let rec exprset_to_seq (es : ('var,'func) exprset) : ('var,'func) expr Myseq.t =
  let* item = Myseq.from_list es in
  expritem_to_seq item
and expritem_to_seq : ('var,'func) expritem -> ('var,'func) expr Myseq.t =
  function
  | SRef x -> Myseq.return (Ref x)
  | SApply (f,es_args) ->
     let seq_args = Array.map exprset_to_seq es_args in
     let* l_args = Myseq.product (Array.to_list seq_args) in (* TODO: extend Myseq for arrays *)
     let args = Array.of_list l_args in
     Myseq.return (Apply (f,args))
  | SArg -> Myseq.return Arg
  | SFun es1 ->
     let* e1 = exprset_to_seq es1 in
     Myseq.return (Fun e1)

let rec exprset_inter (es1 : ('var,'func) exprset) (es2 : ('var,'func) exprset) : ('var,'func) exprset =
  List.fold_left
    (fun res item1 ->
      List.fold_left
        (fun res item2 ->
          match expritem_inter item1 item2 with
          | None -> res
          | Some item -> item::res)
        res es2)
    [] es1
and expritem_inter (item1 : ('var,'func) expritem) (item2 : ('var,'func) expritem) : ('var,'func) expritem option =
  match item1, item2 with
  | SRef x1, SRef x2 when x1 = x2 -> Some (SRef x1)
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

let rec exprset_inter_list (esl1 : ('var,'func) exprset list) (esl2 : ('var,'func) exprset list) : ('var,'func) exprset list =
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
    type ('value,'var,'func) t = ('value, ('var,'func) exprset) Mymap.t

    let empty = Mymap.empty
                
    let bind (v : 'value) (item : ('var,'func) expritem) (index : ('value,'var,'func) t) : ('value,'var,'func) t =
      Mymap.update v
        (function
         | None -> Some [item]
         | Some exprs -> Some (item :: exprs))
        index

    let bind_set (v : 'value) (es : ('var,'func) exprset) (index : ('value,'var,'func) t) : ('value,'var,'func) t =
      Mymap.update v
        (function
         | None -> Some es
         | Some exprs -> Some (List.rev_append es exprs))
        index

    let find_opt = Mymap.find_opt

    let fold = Mymap.fold
                
    let lookup (v : 'value) (index : ('value,'var,'func) t) : ('var,'func) exprset =
      match find_opt v index with
      | None -> []
      | Some exprs -> exprs
  end
           
let index_add_bindings index (bindings : ('var,'value) bindings) : ('value,'var,'func) Index.t =
  Mymap.fold
    (fun x v res -> Index.bind v (SRef x) res)
    bindings index

let index_apply_functions
      ~(eval_func : 'func -> 'value array -> 'value result)
      index (max_arity : int) (get_functions : 'value array -> 'func list)
    : ('value,'var,'func) Index.t =
  let rec aux k lv_k les_k args_k es_args_k res =
    let res =
      get_functions args_k
      |> List.fold_left
           (fun res f ->
             match eval_func f args_k with
             | Result.Ok v -> Index.bind v (SApply (f, es_args_k)) res
             | Result.Error _ -> res)
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


(* expr encoding *)

let size_expr_ast (* for DL computing *)
    : ('var,'func) expr -> int =
  let rec aux = function
    | Ref x -> 1
    | Apply (f,args) -> Array.fold_left (fun res arg -> res + aux arg) 1 args
    | Arg -> 1
    | Fun e1 -> 1 + aux e1
  in
  aux

let nb_expr_ast (* for DL computing *)
      ~(funcs : 't kind -> ('func * 't kind array) list)
    : 't kind -> int -> float =
  let tab : ('t kind * int, float) Hashtbl.t = Hashtbl.create 1013 in
  let rec aux (k : 't kind) (size : int) : float =
    match Hashtbl.find_opt tab (k,size) with
    | Some nb -> nb
    | None ->
       let nb =
         List.fold_left
           (fun nb (f,k_args) ->
             if k_args = [||] (* leaf node *)
             then if size = 1 then nb +. 1. else nb
             else
               if size >= 1
               then nb +. sum_conv (Array.to_list (Array.map aux k_args)) (size-1)
               else nb)
           0. (funcs k) in
       Hashtbl.add tab (k,size) nb;
       nb
  in
  aux
  
let dl_expr_params
      ~(dl_func_params : 'func -> dl)
      ~(dl_var : 'var -> dl)
    : ('var,'func) expr -> dl =
  let rec aux = function
    | Ref x -> dl_var x
    | Apply (f,args) ->
       let dl_args_params =
         Array.map aux args
         |> Array.fold_left (+.) 0. in
       dl_func_params f +. dl_args_params
    | Arg -> 0.
    | Fun e1 -> aux e1
  in
  aux
