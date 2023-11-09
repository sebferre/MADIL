
open Madil_common
open Data

type ('typ,'value,'var,'func) expr =
  | Const of 'typ * 'value
  | Ref of 'typ * 'var
  | Apply of 'typ * 'func * ('typ,'value,'var,'func) expr array
  | Arg of 'typ (* implicit unique argument of functions *)
  | Fun of 'typ (* arg type *) * ('typ,'value,'var,'func) expr (* support for unary functions, to be used as arg of higher-order functions *)
(* TODO: add indexing construct for ndtree values ? with exprs for the ndtree and the indexes ? *)

let typ : ('typ,'value,'var,'func) expr -> 'typ = function
  | Const (t,v) -> t
  | Ref (t,x) -> t
  | Apply (t,f,args) -> t
  | Arg t -> t
  | Fun (t,e) -> raise TODO (* functional type: t -> typ(e) *)
         
type 'var binding_vars = 'var Bintree.t
let binding_vars0 = Bintree.empty

type ('var,'typ,'value) bindings = ('var, 'typ * 'value Ndtree.t) Mymap.t
let bindings0 = Mymap.empty

let xp_expr
      ~(xp_value : 'value html_xp)
      ~(xp_var : 'var html_xp)
      ~(xp_func : 'func html_xp)
    : ('typ,'value,'var,'func) expr html_xp =
  let rec aux ~html print e =
    match e with
    | Const (t,v) -> xp_value ~html print v
    | Ref (t,x) -> xp_var ~html print x
    | Apply (t,f,args) ->
       xp_func ~html print f;
       if args <> [||] then
         Xprint.bracket ("(",")")
           (Xprint.sep_array ", " (aux ~html))
           print args
    | Arg t -> print#string "_"
    | Fun (t,e1) -> print#string "fun { "; aux ~html print e1; print#string " }"
  in
  fun ~html print e ->
  Xprint.bracket ("{","}") (aux ~html)
    print e

let xp_bindings
      ~(xp_var : 'var html_xp)
      ~(xp_typ : 'typ html_xp)
      ~(xp_value : 'value html_xp)
    : ('var,'typ,'value) bindings html_xp =
  fun ~html print bindings ->
  print#string "BINDINGS";
  xp_newline ~html print ();
  Mymap.iter
    (fun x (t,v_tree) ->
      xp_var ~html print x;
      print#string " : ";
      xp_typ ~html print t;
      print#string " = ";
      Ndtree.xp ~xp_elt:xp_value ~html print v_tree;
      xp_newline ~html print ())
    bindings
  
(* expression evaluation *)

let eval
      ~(eval_unbound_var : 'var -> 'value Ndtree.t result) (* ex: return some null value, or fail *)
      ~(eval_func : 'func -> 'value Ndtree.t array -> 'value Ndtree.t result)
      ~(eval_arg : unit -> 'value Ndtree.t result) (* the value should be the identity function *)
      (e : ('typ,'value,'var,'func) expr) (bindings : ('var,'typ,'value) bindings)
    : 'value Ndtree.t result =
  let rec aux e =
    match e with
    | Const (t,v) ->
       Result.Ok (Ndtree.scalar (Some v))
    | Ref (t,x) ->
       (match Mymap.find_opt x bindings with
        | Some (t,v) -> Result.Ok v
        | None -> eval_unbound_var x)
    | Apply (t,f,args) ->
       let| lv = list_map_result aux (Array.to_list args) in
       eval_func f (Array.of_list lv)
    | Arg t -> eval_arg ()
    | Fun (t,e1) -> aux e1
  in
  aux e

  
(* expression sets : idea taken from FlashMeta *)

module type EXPRSET =
  sig
    type ('typ,'value,'var,'func) t
    val xp : xp_value:'value html_xp -> xp_var:'var html_xp -> xp_func:'func html_xp -> ('typ,'value,'var,'func) t html_xp
    val to_seq : ('typ,'value,'var,'func) t -> ('typ,'value,'var,'func) expr Myseq.t
    val mem : ('typ,'value,'var,'func) expr -> ('typ,'value,'var,'func) t -> bool
    val empty : 'typ -> ('typ,'value,'var,'func) t
    val value : 'typ -> 'value -> ('typ,'value,'var,'func) t
    val add_const : 'value -> ('typ,'value,'var,'func) t -> ('typ,'value,'var,'func) t
    val add_ref : 'var -> ('typ,'value,'var,'func) t -> ('typ,'value,'var,'func) t
    val add_apply : 'func -> ('typ,'value,'var,'func) t array -> ('typ,'value,'var,'func) t -> ('typ,'value,'var,'func) t
  end

(* DEPRECATED
module Exprset_old : EXPRSET =
  struct
  
type ('typ,'value,'var,'func) t = ('typ,'value,'var,'func) item list
and ('typ,'value,'var,'func) item =
  | SConst of 'value
  | SRef of 'var
  | SApply of 'func * ('typ,'value,'var,'func) t array
  | SArg
  | SFun of ('typ,'value,'var,'func) t

let xp ~xp_value ~xp_var ~xp_func ~html print es = raise TODO
          
let rec to_seq (es : ('typ,'value,'var,'func) t) : ('typ,'value,'var,'func) expr Myseq.t =
  let* item = Myseq.from_list es in
  item_to_seq item
and item_to_seq : ('typ,'value,'var,'func) item -> ('typ,'value,'var,'func) expr Myseq.t =
  function
  | SConst v -> Myseq.return (Const v)
  | SRef x -> Myseq.return (Ref x)
  | SApply (f,es_args) ->
     let seq_args = Array.map to_seq es_args in
     let* l_args = Myseq.product (Array.to_list seq_args) in (* TODO: extend Myseq for arrays *)
     let args = Array.of_list l_args in
     Myseq.return (Apply (f,args))
  | SArg -> Myseq.return Arg
  | SFun es1 ->
     let* e1 = to_seq es1 in
     Myseq.return (Fun e1)

let rec mem (e : ('typ,'value,'var,'func) expr) (es : ('typ,'value,'var,'func) t) : bool =
  List.exists (item_mem e) es
and item_mem e item =
  match e, item with
  | Const v, SConst w -> v=w 
  | Ref x, SRef y -> x=y
  | Apply (f,args), SApply (g,es_args) ->
     f = g
     && Array.length args = Array.length es_args
     && Array.for_all2 mem args es_args
  | Arg, SArg -> true
  | Fun e, SFun es -> mem e es
  | _ -> false

let empty : ('typ,'value,'var,'func) t = []
       
let add_const (v : 'value) (es : ('typ,'value,'var,'func) t) : ('typ,'value,'var,'func) t =
  SConst v :: es

let add_ref (x : 'var) (es : ('typ,'value,'var,'func) t) : ('typ,'value,'var,'func) t =
  SRef x :: es

let add_apply (f : 'func) (es_args : ('typ,'value,'var,'func) t array) (es : ('typ,'value,'var,'func) t) : ('typ,'value,'var,'func) t =
  SApply (f,es_args) :: es

let union (es1 : ('typ,'value,'var,'func) t) (es2 : ('typ,'value,'var,'func) t) : ('typ,'value,'var,'func) t =
  List.rev_append es1 es2
  
let rec inter (es1 : ('typ,'value,'var,'func) t) (es2 : ('typ,'value,'var,'func) t) : ('typ,'value,'var,'func) t =
  List.fold_left
    (fun res item1 ->
      List.fold_left
        (fun res item2 ->
          match item_inter item1 item2 with
          | None -> res
          | Some item -> item::res)
        res es2)
    [] es1
and item_inter (item1 : ('typ,'value,'var,'func) item) (item2 : ('typ,'value,'var,'func) item) : ('typ,'value,'var,'func) item option =
  match item1, item2 with
  | SConst v1, SConst v2 when v1 = v2 -> Some (SConst v1)
  | SRef x1, SRef x2 when x1 = x2 -> Some (SRef x1)
  | SApply (f1,es_args1), SApply (f2,es_args2) when f1 = f2 ->
     let es_args = Array.map2 inter es_args1 es_args2 in
     if Array.exists (fun es -> es = []) es_args
     then None
     else Some (SApply (f1, es_args))
  | SArg, SArg -> Some SArg
  | SFun es1, SFun es2 ->
     (match inter es1 es2 with
      | [] -> None
      | es -> Some (SFun es))
  | _ -> None

  end
 *)
  
module Exprset_new : EXPRSET =
  struct
    type ('typ,'value,'var,'func) t =
      { typ : 'typ;
        consts : 'value Bintree.t;
        refs : 'var Bintree.t;
        applies : ('func, ('typ,'value,'var,'func) t array Bintree.t) Mymap.t;
        args : bool;
        funs : ('typ,'value,'var,'func) t option }
      
    let rec to_seq es : ('typ,'value,'var,'func) expr Myseq.t =
      let t = es.typ in
      Myseq.concat
        [ (let* v = Myseq.from_bintree es.consts in
           Myseq.return (Const (t,v)));

          (let* x = Myseq.from_bintree es.refs in
           Myseq.return (Ref (t,x)));

          (if es.args then Myseq.return (Arg t)
           else Myseq.empty);
          
          (Myseq.interleave
             (List.map
                (fun (f, es_args_set) ->
                  let* es_args = Myseq.from_bintree es_args_set in
                  let seq_args = Array.map to_seq es_args in
                  let* l_args = Myseq.product_fair (Array.to_list seq_args) in (* TODO: extend Myseq for arrays *)
                  let args = Array.of_list l_args in
                  Myseq.return (Apply (t,f,args)))
                (Mymap.bindings es.applies)));
          
          (* let* es1 = Myseq.from_option es.funs in
           let* e = to_seq es1 in
           Myseq.return (Fun (t_arg,e) *) (* needs to decompose t as (t_arg -> es1.typ) *) 
        ]

    let xp
          ~(xp_value : 'value html_xp)
          ~(xp_var : 'var html_xp)
          ~(xp_func : 'func html_xp)
        : ('typ,'value,'var,'func) t html_xp =
      let rec aux ~html print es =
        print#string "[";
        Bintree.iter
          (fun v ->
            xp_value ~html print v;
            print#string "  ")
          es.consts;
        Bintree.iter
          (fun x ->
            xp_var ~html print x;
            print#string "  ")
          es.refs;
        Mymap.iter
          (fun f es_args_set ->
            xp_func ~html print f;
            Bintree.iter
              (fun es_args ->
                if es_args <> [||] then
                  xp_array ~delims:("(",")")
                    aux
                    ~html print es_args)
              es_args_set;
            print#string "  ")
          es.applies;
        print#string "]"
      in
      aux

    let rec mem e es =
      (* assuming compatible type *)
      match e with
      | Const (t,v) -> Bintree.mem v es.consts
      | Ref (t,x) -> Bintree.mem x es.refs
      | Apply (t,f,args) ->
         (match Mymap.find_opt f es.applies with
          | None -> false
          | Some es_args_set ->
             Bintree.exists
               (fun es_args ->
                 Array.length args = Array.length es_args
                 && Array.for_all2 mem args es_args)
               es_args_set)
      | Arg t -> es.args
      | Fun (t,e) ->
         (match es.funs with
          | None -> false
          | Some es1 -> mem e es1)

    let empty t =
      { typ = t;
        consts = Bintree.empty;
        refs = Bintree.empty;
        applies = Mymap.empty;
        args = false;
        funs = None }

    let add_const v es =
      { es with
        consts = Bintree.add v es.consts }

    let value t v = add_const v (empty t) [@@inline]

    let add_ref x es =
      { es with
        refs = Bintree.add x es.refs }

    let add_apply f es_args es =
      { es with
        applies =
          Mymap.update f
            (function
             | None -> Some (Bintree.singleton es_args)
             | Some es_args_set -> Some (Bintree.add es_args es_args_set))
            es.applies }

    let rec union es1 es2 =
      assert (es1.typ = es2.typ);
      { typ = es1.typ;
        consts = Bintree.union es1.consts es2.consts;
        refs = Bintree.union es1.refs es2.refs;
        applies =
          Mymap.merge
            (fun f es_args_set1_opt es_args_set2_opt ->
              match es_args_set1_opt, es_args_set2_opt with
              | None, None -> assert false
              | Some s1, None -> Some s1
              | None, Some s2 -> Some s2
              | Some s1, Some s2 -> Some (Bintree.union s1 s2))
            es1.applies es2.applies;
        args = es1.args || es2.args;
        funs =
          (match es1.funs, es2.funs with
           | None, None -> None
           | None, Some es2 -> Some es2
           | Some es1, None -> Some es1
           | Some es1, Some es2 -> Some (union es1 es2)) } 
                  
    let rec inter es1 es2 =
      assert (es1.typ = es2.typ);
      { typ = es1.typ;
        consts = Bintree.inter es1.consts es2.consts;
        refs = Bintree.inter es1.refs es2.refs;
        applies =
          Mymap.merge
            (fun f es_args_set1_opt es_args_set2_opt ->
              match es_args_set1_opt, es_args_set2_opt with
              | None, None -> assert false
              | Some s1, None -> None
              | None, Some s2 -> None
              | Some s1, Some s2 -> Some (Bintree.inter s1 s2))
            es1.applies es2.applies;
        args = es1.args && es2.args;
        funs =
          (match es1.funs, es2.funs with
           | None, None -> None
           | None, Some es2 -> None
           | Some es1, None -> None
           | Some es1, Some es2 -> Some (inter es1 es2)) } 
  end

module Exprset = Exprset_new
  
(* indexes : idea inspired from FlashMeta *)

module Index =
  struct
    type ('typ,'value,'var,'func) t = ('typ * 'value Ndtree.t, ('typ,'value,'var,'func) Exprset.t) Mymap.t

    let xp
          ~(xp_typ : 'typ html_xp)
          ~(xp_value : 'value html_xp)
          ~(xp_var : 'var html_xp)
          ~(xp_func : 'func html_xp)
        : ('typ,'value,'var,'func) t html_xp =
      let xp_exprset = Exprset.xp ~xp_value ~xp_var ~xp_func in
      fun ~html print index ->
      print#string "INDEX";
      xp_newline ~html print ();
      Mymap.iter
        (fun (t,v_tree) es ->
          xp_typ ~html print t;
          print#string " ";
          Ndtree.xp ~xp_elt:xp_value ~html print v_tree;
          print#string " = ";
          xp_exprset ~html print es;
          xp_newline ~html print ())
        index

    let empty = Mymap.empty
                
    let bind_ref (tv : 'typ * 'value Ndtree.t) (x : 'var) (index : ('typ,'value,'var,'func) t) : ('typ,'value,'var,'func) t =
      Mymap.update tv
        (function
         | None -> Some (Exprset.add_ref x (Exprset.empty (fst tv)))
         | Some es -> Some (Exprset.add_ref x es))
        index
      
    let bind_apply (tv : 'typ * 'value Ndtree.t) (f : 'func) (es_args : ('typ,'value,'var,'func) Exprset.t array) (index : ('typ,'value,'var,'func) t) : ('typ,'value,'var,'func) t = (* QUICK *)
      Mymap.update tv
        (function
         | None -> Some (Exprset.add_apply f es_args (Exprset.empty (fst tv)))
         | Some es -> Some (Exprset.add_apply f es_args es))
        index
      
    let find_opt = Mymap.find_opt

    let fold = Mymap.fold

    let iter = Mymap.iter
                
    let lookup (tv : 'typ * 'value Ndtree.t) (index : ('typ,'value,'var,'func) t) : ('typ,'value,'var,'func) Exprset.t =
      match find_opt tv index with
      | None -> Exprset.empty (fst tv)
      | Some exprs -> exprs
  end
           
let index_add_bindings index (bindings : ('var,'typ,'value) bindings) : ('typ,'value,'var,'func) Index.t =
  Mymap.fold
    (fun x tv res -> Index.bind_ref tv x res)
    bindings index

type ('typ,'value) args_spec =
  [ `Default
  | `Custom of [`Pos of int | `Val of 'typ * 'value] array ]
  
let index_apply_functions
      ~(eval_func : 'func -> 'value Ndtree.t array -> 'value Ndtree.t result)
      index
      (max_arity : int)
      (get_functions : 'typ array * 'value Ndtree.t array -> ('typ * 'func * ('typ,'value) args_spec) list)
    : ('typ,'value,'var,'func) Index.t = (* COSTLY in itself, apart from get_functions, eval, and bind_apply *)
  let args_k =
    Array.init (max_arity+1) (* for each arity k in 0..max_arity *)
      (fun k -> (* three undefined arrays for types, values, and exprsets *)
        Array.make k (Obj.magic () : 'typ),
        Array.make k (Obj.magic () : 'value Ndtree.t),
        Array.make k (Obj.magic () : ('typ,'value,'var,'func) Exprset.t)) in
  let rec aux k res =
    let res = (* generating and applying functions for arity k *)
      let t_args_k, v_args_k, es_args_k = args_k.(k) in
      let es_args_k = Array.copy es_args_k in (* because it is inserted into the index *)
      get_functions (t_args_k, v_args_k)
      |> List.fold_left
           (fun res (t,f,args_spec) ->
             let v_args, es_args =
               match args_spec with
               | `Default -> v_args_k, es_args_k
               | `Custom ar ->
                  let v_args =
                    Array.map
                      (function
                       | `Pos i ->
                          if not (i>=0 && i < k) then failwith "Expr.index_apply_functions: invalid position in args_spec";
                          v_args_k.(i)
                       | `Val (t,v) -> Ndtree.scalar (Some v))
                      ar in
                  let es_args =
                    Array.map
                      (function
                       | `Pos i -> es_args_k.(i)
                       | `Val (t,v) -> Exprset.value t v)
                      ar in
                  v_args, es_args in
             match eval_func f v_args with
             | Result.Ok v -> Index.bind_apply (t,v) f es_args res
             | Result.Error _ -> res)
           res in
    if k >= max_arity
    then res
    else
      Index.fold
        (fun (t,v) es res ->
          for l = k+1 to max_arity do (* comleting the arrays at position k *)
            let ts, vs, ess = args_k.(l) in
            ts.(k) <- t;
            vs.(k) <- v;
            ess.(k) <- es
          done;
          aux (k+1) res)
        index res
  in
  aux 0 index


(* expr encoding *)

let size_expr_ast (* for DL computing *)
    : ('typ,'value,'var,'func) expr -> int =
  let rec aux = function
    | Const (t,v) -> 1
    | Ref (t,x) -> 1
    | Apply (t,f,args) -> Array.fold_left (fun res arg -> res + aux arg) 1 args
    | Arg t -> 1
    | Fun (t,e1) -> 1 + aux e1
  in
  aux

let nb_expr_ast (* for DL computing *)
      ~(funcs : 'typ -> ('func * 'typ array) list)
    : ('typ -> int -> float) * (unit -> unit) =
  let tab : ('typ * int, float) Hashtbl.t = Hashtbl.create 1013 in
  let reset () = Hashtbl.clear tab in
  let rec aux (k : 'typ) (size : int) : float =
    match Hashtbl.find_opt tab (k,size) with
    | Some nb -> nb
    | None -> (* QUICK *)
       let nb = (* counting Const and Ref *)
         if size = 1
         then 2. (* Const or Ref *)
         else 0. in
       let nb = (* counting Apply-s *)
         List.fold_left
           (fun nb (f,k_args) ->
             if k_args = [||] (* leaf node *)
             then if size = 1 then nb +. 1. else nb
             else
               if size >= 1
               then nb +. sum_conv (Array.to_list (Array.map aux k_args)) (size-1)
               else nb)
           nb (funcs k) in
       (* not yet counting Arg and Fun-s *)
       Hashtbl.add tab (k,size) nb;
       nb
  in
  aux, reset
  
let dl_expr_params
      ~(dl_value : 'typ -> 'value -> dl)
      ~(dl_var : 'typ -> 'var -> dl)
      ~(dl_func_params : 'typ -> 'func -> dl)
    : ('typ,'value,'var,'func) expr -> dl =
  let rec aux = function
    | Const (t,v) -> dl_value t v
    | Ref (t,x) -> dl_var t x
    | Apply (t,f,args) ->
       let dl_args_params =
         Array.map aux args
         |> Array.fold_left (+.) 0. in
       dl_func_params t f +. dl_args_params
    | Arg t -> 0.
    | Fun (t,e1) -> aux e1
  in
  aux
