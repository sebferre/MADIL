
open Madil_common
open Data

type ('typ,'value,'var,'func) expr =
  | Const of 'typ * 'value
  | Ref of 'typ * 'var
  | Apply of 'typ * 'func * ('typ,'value,'var,'func) expr array
  | Arg of 'typ (* implicit unique argument of functions *)
  | Fun of 'typ (* arg type *) * ('typ,'value,'var,'func) expr (* support for unary functions, to be used as arg of higher-order functions *)

let typ : ('typ,'value,'var,'func) expr -> 'typ = function
  | Const (t,v) -> t
  | Ref (t,x) -> t
  | Apply (t,f,args) -> t
  | Arg t -> t
  | Fun (t,e) -> raise TODO (* functional type: t -> typ(e) *)
         
type ('var,'typ) binding_vars = ('var, 'typ) Mymap.t
let binding_vars0 = Mymap.empty

type ('var,'typ,'value) bindings = ('var, 'typ * 'value) Mymap.t
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
    (fun x (t,v) ->
      xp_var ~html print x;
      print#string " : ";
      xp_typ ~html print t;
      print#string " = ";
      xp_value ~html print v;
      xp_newline ~html print ())
    bindings

let size_expr_ast (* used for DL computing, check consistency *)
    : ('typ,'value,'var,'func) expr -> int =
  let rec aux = function
    | Const (t,v) -> 1
    | Ref (t,x) -> 1
    | Apply (t,f,args) ->
       Array.fold_left
         (fun res arg ->
           match arg with
           | Const _ -> res (* const arg considered as function param *)
           | _ -> res + aux arg)
         1 args
    | Arg t -> 1
    | Fun (t,e1) -> 1 + aux e1
  in
  aux


(* expression evaluation *)

let eval
      ~(eval_unbound_var : 'var -> 'value result) (* ex: return some null value, or fail *)
      ~(eval_func : 'func -> 'value array -> 'value result)
      ~(eval_arg : unit -> 'value result) (* the value should be the identity function *)
      (e : ('typ,'value,'var,'func) expr) (bindings : ('var,'typ,'value) bindings)
    : 'value result =
  let rec aux e =
    match e with
    | Const (t,v) -> Result.Ok v
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
    val to_seq : max_expr_size:int -> ('typ,'value,'var,'func) t -> ('typ,'value,'var,'func) expr Myseq.t
    val mem : ('typ,'value,'var,'func) expr -> ('typ,'value,'var,'func) t -> bool
    val empty : 'typ -> ('typ,'value,'var,'func) t
    val value : 'typ -> 'value -> ('typ,'value,'var,'func) t
    val add_const : 'value -> ('typ,'value,'var,'func) t -> ('typ,'value,'var,'func) t
    val add_ref : 'var -> ('typ,'value,'var,'func) t -> ('typ,'value,'var,'func) t
    val add_apply : 'func -> ('typ,'value,'var,'func) t array -> ('typ,'value,'var,'func) t -> ('typ,'value,'var,'func) t
    val union : ('typ,'value,'var,'func) t -> ('typ,'value,'var,'func) t -> ('typ,'value,'var,'func) t
  end

(* DEPRECATED
module Exprset_old : EXPRSET =
  struct
  
type ('typ,'value,'var,'func) t =
  { typ : 'typ;
    items : ('typ,'value,'var,'func) item list }
and ('typ,'value,'var,'func) item =
  | SConst of 'value
  | SRef of 'var
  | SApply of 'func * ('typ,'value,'var,'func) t array
  | SArg
  | SFun of ('typ,'value,'var,'func) t

let xp ~xp_value ~xp_var ~xp_func ~html print es = raise TODO
          
let rec to_seq (es : ('typ,'value,'var,'func) t) : ('typ,'value,'var,'func) expr Myseq.t =
  let* item = Myseq.from_list es.items in
  item_to_seq es.typ item
and item_to_seq t : ('typ,'value,'var,'func) item -> ('typ,'value,'var,'func) expr Myseq.t =
  function
  | SConst v -> Myseq.return (Const (t,v))
  | SRef x -> Myseq.return (Ref (t,x))
  | SApply (f,es_args) ->
     let seq_args = Array.map to_seq es_args in
     let* l_args = Myseq.product (Array.to_list seq_args) in (* TODO: extend Myseq for arrays *)
     let args = Array.of_list l_args in
     Myseq.return (Apply (t,f,args))
  | SArg -> Myseq.return (Arg t)
  | SFun es1 ->
     let* e1 = to_seq es1 in
     Myseq.return (Fun (t,e1))

let rec mem (e : ('typ,'value,'var,'func) expr) (es : ('typ,'value,'var,'func) t) : bool =
  List.exists (item_mem e) es.items
and item_mem e item =
  match e, item with
  | Const (t,v), SConst w -> v=w 
  | Ref (t,x), SRef y -> x=y
  | Apply (t,f,args), SApply (g,es_args) ->
     f = g
     && Array.length args = Array.length es_args
     && Array.for_all2 mem args es_args
  | Arg t, SArg -> true
  | Fun (t,e), SFun es -> mem e es
  | _ -> false

let empty t : ('typ,'value,'var,'func) t = { typ = t; items = [] }
       
let add_const (v : 'value) (es : ('typ,'value,'var,'func) t) : ('typ,'value,'var,'func) t =
  { es with items = SConst v :: es.items }

let value t v = add_const v (empty t) [@@inline]
  
let add_ref (x : 'var) (es : ('typ,'value,'var,'func) t) : ('typ,'value,'var,'func) t =
  { es with items = SRef x :: es.items }

let add_apply (f : 'func) (es_args : ('typ,'value,'var,'func) t array) (es : ('typ,'value,'var,'func) t) : ('typ,'value,'var,'func) t =
  { es with items = SApply (f,es_args) :: es.items }

(*  
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
 *)
  
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
      
    let rec to_seq ~(max_expr_size : int) es : ('typ,'value,'var,'func) expr Myseq.t =
      if max_expr_size <= 0 then Myseq.empty
      else
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
                  let k = Array.length es_args in
                  let seq_args = Array.map (to_seq ~max_expr_size:(max_expr_size - k)) es_args in
                  let* l_args = Myseq.product_fair (Array.to_list seq_args) in (* TODO: extend Myseq for arrays *)
                  let args = Array.of_list l_args in
                  Myseq.return (Apply (t,f,args)))
                (Mymap.bindings es.applies)));
          
          (* let* es1 = Myseq.from_option es.funs in
           let* e = to_seq es1 in
           Myseq.return (Fun (t_arg,e) *) (* needs to decompose t as (t_arg -> es1.typ) *) 
        ]
      |> Myseq.filter (fun e -> size_expr_ast e <= max_expr_size)

    let rec to_seq_for_size es n =
      assert (n >= 0);
      if n = 0 then
        Myseq.empty (* no expression has size 0 *)
      else if n = 1 then
        let t = es.typ in
        Myseq.concat
          [ (let* v = Myseq.from_bintree es.consts in
             Myseq.return (Const (t,v)));
            
            (let* x = Myseq.from_bintree es.refs in
             Myseq.return (Ref (t,x)));
            
            (if es.args then Myseq.return (Arg t)
             else Myseq.empty) ]
      else (* n > 1 *)
        let t = es.typ in
        Myseq.interleave
          (List.map
             (fun (f, es_args_set) ->
               let* es_args = Myseq.from_bintree es_args_set in
               let* args = distribute (n-1) (Array.map to_seq_for_size es_args) in (* cost 1 for the function *)
               Myseq.return (Apply (t,f,args)))
             (Mymap.bindings es.applies))
    
    let to_seq ~(max_expr_size : int) (es : ('typ,'value,'var,'func) t) : ('typ,'value,'var,'func) expr Myseq.t =
      (* enumerate expressions in increasing ast size *)
      let* n = Myseq.range 1 max_expr_size in
      to_seq_for_size es n

    let xp
          ~(xp_value : 'value html_xp)
          ~(xp_var : 'var html_xp)
          ~(xp_func : 'func html_xp)
        : ('typ,'value,'var,'func) t html_xp =
      let rec aux ~html print es =
        print#string "{";
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
        print#string "}"
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

    let rec union es1 es2 = (* not used, not tested *)
      Common.prof "Expr.Exprset.union" (fun () ->
      assert (es1.typ = es2.typ);
      { typ = es1.typ;
        consts = Bintree.union es1.consts es2.consts;
        refs = Bintree.union es1.refs es2.refs;
        applies =
          Mymap.merge
            (fun f es_args_s1_opt es_args_s2_opt ->
              match es_args_s1_opt, es_args_s2_opt with
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
           | Some es1, Some es2 -> Some (union es1 es2)) })
                  
    let rec inter es1 es2 = (* not used, not tested *)
      assert (es1.typ = es2.typ);
      { typ = es1.typ;
        consts = Bintree.inter es1.consts es2.consts;
        refs = Bintree.inter es1.refs es2.refs;
        applies =
          Mymap.merge
            (fun f es_args_s1_opt es_args_s2_opt ->
              match es_args_s1_opt, es_args_s2_opt with
              | None, None -> assert false
              | Some s1, None -> None
              | None, Some s2 -> None
              | Some s1, Some s2 ->
                 let s = Bintree.inter s1 s2 in
                 if Bintree.is_empty s
                 then None
                 else Some s)
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

(* TENTATIVE for efficiency - FAIL
  module ExprsetBySize =
  struct
    type ('typ,'value,'var,'func) t = ('typ,'value,'var,'func) Exprset.t Intmap.t

    let get typ size ess =
      try Intmap.get size ess
      with Not_found -> Exprset.empty typ [@@inline]

    let rec to_seq (ess : _ t) : ('typ,'value,'var,'func) expr Myseq.t =
      let* size, es = Intmap.to_seq ess in (* assuming increasing size *)
      Exprset.to_seq es

    let xp
          ~(xp_value : 'value html_xp)
          ~(xp_var : 'var html_xp)
          ~(xp_func : 'func html_xp)
        : ('typ,'value,'var,'func) t html_xp =
      fun ~html print ess ->
      Intmap.iter
        (fun size es ->
          print#int size;
          print#string ":";
          Exprset.xp ~xp_value ~xp_var ~xp_func ~html print es;
          print#string ", ")
        ess

    let empty : _ t = Intmap.empty
    
    let add_const typ v ess =
      Intmap.set 1 (Exprset.add_const v (get typ 1 ess)) ess

    let value typ v = add_const typ v empty [@@inline]

    let add_ref typ x ess =
      Intmap.set 1 (Exprset.add_ref x (get typ 1 ess)) ess

    let add_apply ~maxsize typ f (ess_args : _ t array) (ess : _ t) : _ t =
      let rec aux ess i maxni n es_args =
        (* current [ess] at arg index [i] with maxsize [maxni], cumulated size so far [n], cumulated arg expresets [es_args] *)
        if maxni < 1 then ess
        else if i < 0 then
          let es_n = get typ n ess in
          let es_args = Array.of_list es_args in
          Intmap.set n (Exprset.add_apply f es_args es_n) ess
        else
          Intmap.fold
            (fun ess n_i es_i ->
              if n_i <= maxni
              then aux ess (i-1) (maxni - n_i + 1) (n + n_i) (es_i::es_args)                
              else ess)
            ess ess_args.(i)
      in
      let k = Array.length ess_args in
      aux ess (k-1) (maxsize - 1 - k + 1) 1 [] (* at least size 1 for each arg *)
        
  end*)

(* func args specs *)

type ('typ,'value,'func) args_spec =
  [ `Default
  | `Custom of ('typ,'value,'func) arg_spec array ]
and ('typ,'value,'func) arg_spec =
  [ `Pos of int
  | `Val of 'typ * 'value
  | `Apply of 'typ * 'func * ('typ,'value,'func) arg_spec array ]

let rec eval_arg_spec ~eval_func k v_args_k es_args_k =
  (* arity, arg values, arg exprsets *)
  function
  | `Pos i ->
     if i>=0 && i < k
     then Result.Ok (v_args_k.(i), es_args_k.(i))
     else failwith "Expr.index_apply_functions: invalid position in args_spec"
  | `Val (t,v) ->
     Result.Ok (v, Exprset.value t v)
  | `Apply (t,f,arg_spec_ar) ->
     let| v_ar, es_ar = eval_arg_spec_ar ~eval_func k v_args_k es_args_k arg_spec_ar in
     let| v = eval_func f v_ar in
     let es = Exprset.add_apply f es_ar (Exprset.empty t) in
     Result.Ok (v,es)
and eval_arg_spec_ar ~eval_func k v_args_k es_args_k arg_spec_ar =
  let| ar = array_map_result (eval_arg_spec ~eval_func k v_args_k es_args_k) arg_spec_ar in
  Result.Ok (Array.split ar)


(* indexes : idea inspired from FlashMeta *)

class virtual ['typ,'value,'var,'func] index =
  object
    method virtual xp : xp_typ:'typ html_xp ->
                        xp_value:'value html_xp ->
                        xp_var:'var html_xp ->
                        xp_func:'func html_xp ->
                        ?on_typ:('typ -> bool) ->
                        unit html_xp
    method virtual lookup : 'typ * 'value -> ('typ,'value,'var,'func) Exprset.t    
  end

class ['typ,'value,'var,'func] index_bind =
  object
    inherit ['typ,'value,'var,'func] index
    
    val mutable index : ('typ * 'value, ('typ,'value,'var,'func) Exprset.t) Mymap.t = Mymap.empty
    (* Hashtbl less efficient and unsafe (iter + updates) *)

    method bind_ref tv x =
      index <-
        Mymap.update tv
          (function
           | None -> Some (Exprset.add_ref x (Exprset.empty (fst tv)))
           | Some es -> Some (Exprset.add_ref x es))
          index
      
    method bind_apply tv f es_args = (* QUICK *)
      index <-
        Mymap.update tv
          (function
           | None -> Some (Exprset.add_apply f es_args (Exprset.empty (fst tv)))
           | Some es -> Some (Exprset.add_apply f es_args es))
          index
      
    method xp ~xp_typ ~xp_value ~xp_var ~xp_func =
      let xp_exprset = Exprset.xp ~xp_value ~xp_var ~xp_func in
      fun ?(on_typ : 'typ -> bool = fun _ -> true)
          ~html print () ->
      print#string "INDEX";
      xp_newline ~html print ();
      Mymap.iter
        (fun (t,v) es ->
          if on_typ t then (
            xp_typ ~html print t;
            print#string " ";
            xp_value ~html print v;
            print#string " = ";
            xp_exprset ~html print es;
            xp_newline ~html print ()
        ))
        index

    method lookup tv = (* QUICK *)
      match Mymap.find_opt tv index with
      | None -> Exprset.empty (fst tv)
      | Some exprs -> exprs

    method fold : 'acc. ('tv -> 'es -> 'acc -> 'acc) -> 'acc -> 'acc =
      fun f acc ->
      Mymap.fold f index acc

    method iter (f : 'tv -> 'es -> unit) = Mymap.iter f index

  end

let index_add_bindings index (bindings : ('var,'typ,'value) bindings) : unit =
  Mymap.iter
    (fun x tv -> index#bind_ref tv x)
    bindings

let index_apply_functions_1
      ~(eval_func : 'func -> 'value array -> 'value result)
      index
      (get_functions : 'typ -> 'value -> ('typ * 'func * ('typ,'value,'func) args_spec) list)
    : unit = (* COSTLY in itself, apart from get_functions, eval, and bind_apply *)
  index#iter
    (fun (t1,v1) es1 ->
      get_functions t1 v1
      |> List.iter
           (fun (t,f,args_spec) ->
             let vfes_res =
               let| v_args, es_args =
                 match args_spec with
                 | `Default -> Result.Ok ([|v1|], [|es1|])
                 | `Custom ar -> eval_arg_spec_ar ~eval_func 1 [|v1|] [|es1|] ar in
               let| v = eval_func f v_args in
               Result.Ok (v, f, es_args) in (* v is the result of applying f to es_args *)
             match vfes_res with
             | Result.Ok (v,f,es_args) -> index#bind_apply (t,v) f es_args
             | Result.Error _ -> ())
    )

let index_apply_functions_2
      ~(eval_func : 'func -> 'value array -> 'value result)
      index
      (filter_1 : 'typ * 'value -> bool)
      (get_functions : 'typ -> 'value -> 'typ -> 'value -> ('typ * 'func * ('typ,'value,'func) args_spec) list)
    : unit = (* COSTLY in itself, apart from get_functions, eval, and bind_apply *)
  index#iter
    (fun (t1,v1 as tv1) es1 ->
      if filter_1 tv1
      then
        index#iter
          (fun (t2,v2) es2 ->
            get_functions t1 v1 t2 v2
            |> List.iter
                 (fun (t,f,args_spec) ->
                   let vfes_res =
                     let| v_args, es_args =
                       match args_spec with
                       | `Default -> Result.Ok ([|v1;v2|], [|es1;es2|])
                       | `Custom ar -> eval_arg_spec_ar ~eval_func 2 [|v1;v2|] [|es1;es2|] ar in
                     let| v = eval_func f v_args in
                     Result.Ok (v, f, es_args) in (* v is the result of applying f to es_args *)
                   match vfes_res with
                   | Result.Ok (v,f,es_args) -> index#bind_apply (t,v) f es_args
                   | Result.Error _ -> ())
          )
      else ())

let index_apply_functions
      ~(eval_func : 'func -> 'value array -> 'value result)
      index
      (max_arity : int)
      (get_functions : 'typ array * 'value array -> ('typ * 'func * ('typ,'value,'func) args_spec) list)
    : unit = (* COSTLY in itself, apart from get_functions, eval, and bind_apply *)
  let args_k =
    Array.init (max_arity+1) (* for each arity k in 0..max_arity *)
      (fun k -> (* three undefined arrays for types, values, and exprsets *)
        Array.make k (Obj.magic () : 'typ),
        Array.make k (Obj.magic () : 'value),
        Array.make k (Obj.magic () : ('typ,'value,'var,'func) Exprset.t)) in
  let rec aux k =
    let () = (* generating and applying functions for arity k *)
      let t_args_k, v_args_k, es_args_k = args_k.(k) in
      let es_args_k = Array.copy es_args_k in (* because it is inserted into the index *)
      get_functions (t_args_k, v_args_k)
      |> List.iter
           (fun (t,f,args_spec) ->
             let vfes_res =
               let| v_args, es_args =
                 match args_spec with
                 | `Default -> Result.Ok (v_args_k, es_args_k)
                 | `Custom ar -> eval_arg_spec_ar ~eval_func k v_args_k es_args_k ar in
               let| v = eval_func f v_args in
               Result.Ok (v, f, es_args) in (* v is the result of applying f to es_args *)
             match vfes_res with
             | Result.Ok (v,f,es_args) -> index#bind_apply (t,v) f es_args
             | Result.Error _ -> ())
    in
    if k >= max_arity
    then ()
    else
      index#iter
        (fun (t,v) es ->
          for l = k+1 to max_arity do (* completing the arrays at position k *)
            let ts, vs, ess = args_k.(l) in
            ts.(k) <- t;
            vs.(k) <- v;
            ess.(k) <- es
          done;
          aux (k+1))
  in
  aux 0


class ['typ,'value,'var,'func] index_union =
  object
    inherit ['typ,'value,'var,'func] index

    val mutable indexes : ('typ,'value,'var,'func) index list = []

    method add_index (index : ('typ,'value,'var,'func) index) : unit =
      indexes <- index::indexes

    method xp ~xp_typ ~xp_value ~xp_var ~xp_func
             ?on_typ ~html print () =
      List.iteri
        (fun i index ->
          print#string "INDEX "; print#int i; xp_newline ~html print ();
          index#xp ~xp_typ ~xp_value ~xp_var ~xp_func ?on_typ ~html print ())
        indexes

    method lookup tv =
      List.fold_left
        (fun res index -> Exprset.union res (index#lookup tv))
        (Exprset.empty (fst tv)) indexes

  end


(* expr encoding *)

let nb_expr_ast (* for DL computing *)
      ~(funcs : 'asd_typ -> (string * 'asd_typ array) list)
    : ('asd_typ -> int -> float) * (unit -> unit) =
  let tab : ('typ * int, float) Hashtbl.t = Hashtbl.create 1013 in
  let reset () = Hashtbl.clear tab in
  let rec aux (k : 'asd_typ) (size : int) : float =
    match Hashtbl.find_opt tab (k,size) with
    | Some nb -> nb
    | None -> (* QUICK *)
       (* Const args considered as function params, must be taken into account by 'func' *)
       let nb = (* counting Ref *)
         if size = 1 then 1. (* Ref *)
         else 0. in
       let nb = (* counting Apply-s *)
         List.fold_left
           (fun nb (label_f,k_args) ->
             let len = Array.length k_args in
             if len = 0 (* leaf node *)
             then if size = 1 then nb +. 1. else nb
             else
               if size >= 1 + len
               then nb +. sum_conv ~min_arg:1 (Array.to_list (Array.map aux k_args)) (size-1)
               else nb)
           nb (funcs k) in
       (* not yet counting Arg and Fun-s *)
       Hashtbl.add tab (k,size) nb;
       nb in
  let main k size =
    if size = 1
    then 2. (* Const and Ref *)
    else aux k size (* Apply expression, assuming no 0-ary func *)
  in
  main, reset

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
