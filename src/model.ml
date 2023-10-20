
open Madil_common
open Ndtree.Operators
open Data

type ('var,'func) cond_model =
  | Undet of float (* undetermined condition, probability for left choice *)
  | True (* always true condition - only in evaluated model *)
  | False (* always false condition - only in evaluated model *)
  | BoolExpr of ('var,'func) Expr.expr (* computed condition - not in evaluated model *)
 
type ('typ,'var,'constr,'func) model =
  | Def of 'var * ('typ,'var,'constr,'func) model (* a var is an id for the value at this sub-model - not in evaluated model *)
  | Pat of 'typ * 'constr * ('typ,'var,'constr,'func) model array (* constr type may be different from data constr *)
  | Fail (* like an empty alternative - only in evaluated model *)
  | Alt of 'var (* condition var *) * ('var,'func) cond_model * ('typ,'var,'constr,'func) model * ('typ,'var,'constr,'func) model
  | Loop of ('typ,'var,'constr,'func) model
  | Seq of int * 'typ (* elt type *) * ('typ,'var,'constr,'func) model array
  | Expr of 'typ * ('var,'func) Expr.expr (* not in evaluated model *)

type 'constr path =
  | This
  | Field of 'constr * int * 'constr path (* Pat field *)
  | Branch of bool * 'constr path (* Alt branch *)
  | Item of int * 'constr path (* Seq item *)

type 'constr ctx = 'constr path -> 'constr path
let ctx0 : _ ctx = (fun p -> p)

let make_def (x : 'var) (m1 : ('typ,'var,'constr,'func) model) : ('typ,'var,'constr,'func) model =
  Def (x,m1)
let make_pat (t : 't) (c : 'constr) (args : ('typ,'var,'constr,'func) model array) : ('typ,'var,'constr,'func) model =
  Pat (t,c,args)
let make_alt (xc : 'var) (cond : ('var,'func) cond_model) (m1 : ('typ,'var,'constr,'func) model) (m2 : ('typ,'var,'constr,'func) model) : ('typ,'var,'constr,'func) model =
  Alt (xc,cond,m1,m2)
let make_loop (m1 : ('typ,'var,'constr,'func) model) : ('typ,'var,'constr,'func) model =
  Loop m1

let rec typ : ('typ,'var,'constr,'func) model -> 'typ = function
  | Def (x,m1) -> typ m1
  | Pat (t,c,args) -> t
  | Fail -> assert false
  | Alt (xc,c,m1,m2) -> typ m1
  | Loop m1 -> typ m1
  | Seq (n,t1,lm1) -> t1
  | Expr (t,e) -> t
  
(* printing *)
  
let xp_model
      ~(xp_var : 'var html_xp)
      ~(xp_pat : 'constr -> unit html_xp array -> unit html_xp)
      ~(xp_func : 'func html_xp)
    : ('typ,'var,'constr,'func) model html_xp =
  let rec aux ~prio_ctx ~html print m =
    match m with
    | Def (x,m1) ->
       if html then print#string "<span class=\"model-def\">";
       xp_var ~html print x; print#string ":"; aux ~prio_ctx ~html print m1;
       if html then print#string "</span>"
    | Pat (_t,c,args) ->
       let xp_args =
         Array.map
           (fun arg -> (fun ~html print () -> aux ~prio_ctx:0 ~html print arg))
           args in
       xp_pat c xp_args ~html print ()

    | Fail -> assert false
    | Alt (xc, Undet prob, m1, m2) -> (* m1 | m2 *)
       xp_brackets_prio ~prio_ctx ~prio:2 ~html print
         (fun () ->
           if html then print#string "<div class=\"model-alt\">";
           xp_var ~html print xc; print#string ": ";
           aux_prob ~html print prob;
           print#string "? ";
           aux ~html ~prio_ctx:2 print m1;
           print#string (if html then " <span class=\"model-meta-operator\">|</span> " else " | ");
           aux ~html ~prio_ctx:2 print m2;
           if html then print#string "</div>")
    | Alt (xc,c,m1,m2) -> (* if c then m1 else m2 *)
       xp_brackets_prio ~prio_ctx ~prio:2 ~html print
         (fun () ->
           if html then print#string "<div class=\"model-alt\">";
           print#string (if html then "<span class=\"model-meta-operator\">if</span> " else "if ");
           xp_var ~html print xc; print#string ": ";
           aux_cond ~html print c;
           print#string (if html then " <span class=\"model-meta-operator\">then</span> " else " then ");
           aux ~html ~prio_ctx:2 print m1;
           print#string (if html then " <span class=\"model-meta-operator\">else</span> " else " else ");
           aux ~html ~prio_ctx:2 print m2;
           if html then print#string "</div>")

    | Loop m1 ->
       xp_tuple1 ~delims:("〈", " ...〉") (aux ~prio_ctx:2) ~html print m1
    | Seq (n,_t1,lm1) ->
       xp_array ~delims:("〈","〉") (aux ~prio_ctx:2) ~html print lm1
    | Expr (_t,e) ->
       if html then print#string "<span class=\"model-expr\">";
       Expr.xp_expr ~xp_var ~xp_func ~html print e;
       if html then print#string "</span>"
  and aux_cond ~html print = function
    | Undet prob ->
       aux_prob ~html print prob
    | True -> assert false
    | False -> assert false
    | BoolExpr e ->
       if html then print#string "<span class=\"model-expr\">";
       Expr.xp_expr ~xp_var ~xp_func ~html print e;
       if html then print#string "</span>"
  and aux_prob ~html print prob =
    let p1 = int_of_float (prob *. 10.) in
    let p2 = 10 - p1 in
    print#int p1; print#string "-"; print#int p2
  in
  aux ~prio_ctx:2

let xp_pat_default
      ~(xp_constr : 'constr html_xp)

      (c : 'constr) (xp_args : unit html_xp array) : unit html_xp =
  fun ~html print () ->
  xp_constr ~html print c;
  if xp_args <> [||] then (
    print#string "[";
    Array.iteri
      (fun i xp_argi ->
        if i > 0 then print#string ", ";
        xp_argi ~html print ())
      xp_args;
    print#string "]"
  )

let xp_path
      ~(xp_field : ('constr * int) html_xp)
    : 'constr path html_xp =
  let rec aux ~html print p =
    match p with
    | This -> ()
    | Field (c,i,p1) ->
       print#string ".";
       xp_field ~html print (c,i);
       aux ~html print p1
    | Branch (b,p1) ->
       print#string (if b then "#true" else "#false");
       aux ~html print p1
    | Item (i,p1) ->
       print#string "["; print#int i; print#string "]";
       aux ~html print p1
  in
  aux

(* ASD *)

class virtual ['typ,'constr,'func] asd =
  object (self)
    method virtual is_default_constr : 'constr -> bool
    method virtual default_and_other_pats : 'typ -> 'constr option * ('constr * ('typ * int) array) list (* the int is the ndim of the field *)
    method virtual funcs : 'typ -> ('func * 'typ array) list (* None when expressions not allowed for this type *)
    method virtual expr_opt : 'typ -> 'typ option
    method virtual alt_opt : 'typ -> bool
  end
        
(* model evaluation *)

let binding_vars
      (m0 : ('typ,'var,'constr,'func) model)
    : 'var Expr.binding_vars =
  let rec aux m acc =
    match m with
    | Def (x,m1) ->
       let acc = aux m1 acc in
       Bintree.add x acc
    | Pat (t,c,args) ->
       Array.fold_right aux args acc
    | Fail -> assert false
    | Alt (xc,cond,m1,m2) ->
       let acc = aux m1 acc in
       let acc = aux m2 acc in
       Bintree.add xc acc
    | Loop m1 -> aux m1 acc
    | Seq (n,t1,lm1) ->
       Array.fold_right aux lm1 acc
    | Expr (t,e) -> acc
  in
  aux m0 Bintree.empty

  
let get_bindings  (* QUICK *)
      ~(typ_bool : 'typ)
      ~(value_of_bool : bool -> 'value)
      (m0 : ('typ,'var,'constr,'func) model as 'model)
      (d0 : ('value,'dconstr) data as 'data)
    : ('var,'typ,'value) Expr.bindings =
  let rec aux m (d_tree : 'data Ndtree.t) acc =
    match m with
    | Def (x,m1) ->
       let acc = aux m1 d_tree acc in
       let t1 = typ m1 in
       let v_tree =
         let< d = d_tree in
         Data.value d in
       Mymap.add x (t1,v_tree) acc
    | Pat (t,c,args) ->
       let n = Array.length args in
       let ref_acc = ref acc in (* missing Array.fold_right2 *)
       for i = 0 to n - 1 do
         let di_tree =
           let< d = d_tree in
           match d with
           | D (_v, DPat (dc, dargs)) ->
              assert (Array.length dargs = n);
              dargs.(i)
           | _ -> assert false in
         ref_acc := aux args.(i) di_tree !ref_acc
       done;
       !ref_acc
    | Fail -> assert false (* because Fail only occurs in evaluated models *)
    | Alt (xc,c,m1,m2) ->
       let d1_tree =
         let<? d = d_tree in
         match d with
         | D (_v, DAlt (_prob,b,d12)) -> if b then Some d12 else None
         | _ -> assert false in
       let acc = aux m1 d1_tree acc in
       let d2_tree =
         let<? d = d_tree in
         match d with
         | D (_v, DAlt (_prob,b,d12)) -> if b then None else Some d12
         | _ -> assert false in
       let acc = aux m2 d2_tree acc in
       let vc_tree =
         let< d = d_tree in
         match d with
         | D (_v, DAlt (_prob,b,d12)) -> value_of_bool b
         | _ -> assert false in
       Mymap.add xc (typ_bool, vc_tree) acc
    | Loop m1 ->
       let d1_tree =
         let<* d = d_tree in
         match d with
         | Some (D (_v, DSeq (dn,_,ds1))) ->
            Ndtree.pack1 (Array.map (fun d1 -> Some d1) ds1)
         | None ->
            Ndtree.pack1 [|None|]
         | _ -> assert false in
       aux m1 d1_tree acc
    | Seq (n,t1,ms1) ->
       let ref_acc = ref acc in (* missing Array.fold_right2 *)
       for i = 0 to n - 1 do
         let di_tree =
           let< d = d_tree in
           match d with
           | D (_v, DSeq (dn, _, ds1)) ->
              assert (dn = n);
              ds1.(i)
           | _ -> assert false in
         ref_acc := aux ms1.(i) di_tree !ref_acc
       done;
       !ref_acc
    | Expr _ -> acc
  in
  aux m0 (Ndtree.scalar (Some d0)) Expr.bindings0

exception EmptyAlt
  
let eval (* from model to evaluated model: resolving expr, ignoring def *)
      ~asd
      ~(eval_expr : ('var,'func) Expr.expr -> ('var,'typ,'value) Expr.bindings -> 'value Ndtree.t result)
      ~(model_of_value : 'typ -> 'value -> ('typ,'var,'constr,'func) model result)
      ~(bool_of_value : 'value -> bool result)
      (m : ('typ,'var,'constr,'func) model)
      (bindings : ('var,'typ,'value) Expr.bindings)
    : ('typ,'var,'constr,'func) model result =
  (* INV: eval must ensure that the resulting model has data that is compatible with the given model, so that encoding is well-defined. E.g. no Alt simplification when condition evaluates to True/False. *)
  let rec aux m = (* QUICK *)
    match m with
    | Def (x,m1) -> aux m1
    | Pat (t,c,args) ->
       let| l_args' =
         list_map_result
           (fun argi -> aux argi)
           (Array.to_list args) in
       let args' = Array.of_list l_args' in
       Result.Ok (Pat (t,c,args'))
    | Fail -> assert false
    | Alt (xc,c,m1,m2) ->
       let| c' = aux_cond c in
       let m1' = match aux m1 with Result.Ok m1' -> m1' | Result.Error _ -> Fail in
       let m2' = match aux m2 with Result.Ok m2' -> m2' | Result.Error _ -> Fail in
       (match c', m1', m2' with
        | Undet _, Fail, Fail
          | True, Fail, _
          | False, _, Fail -> Result.Error EmptyAlt
        | _ -> Result.Ok (Alt (xc,c',m1',m2')))
    | Loop m1 ->
       let| m1' = aux m1 in
       Result.Ok (Loop m1')
    | Seq (n,t1,ms1) ->
       let| ms1' = array_map_result aux ms1 in
       Result.Ok (Seq (n,t1,ms1'))
    | Expr (t,e) ->
       let| v_tree = eval_expr e bindings in
       let| v = Ndtree.unscalar v_tree in
       model_of_value t v
  and aux_cond = function
    | Undet prob -> Result.Ok (Undet prob)
    | True | False -> assert false
    | BoolExpr e ->
       let| v_tree = eval_expr e bindings in
       let| v = Ndtree.unscalar v_tree in
       let| b = bool_of_value v in
       Result.Ok (if b then True else False)
  in
  aux m
  
(* model-based generation *)

type ('info,'value,'dconstr) generator = 'info -> ('value,'dconstr) data Myseq.t

let generator (* on evaluated models: no expr, no def *)
      ~(generator_pat: 'typ -> 'constr -> (('info,'value,'dconstr) generator as 'gen) array -> 'gen)
      ~(dseq_value : ('value,'dconstr) data array -> 'value)
    : ('typ,'var,'constr,'func) model -> 'gen =
  let rec gen = function
    | Def (x,m1) -> assert false
    | Pat (t,c,args) ->
       let gen_args = Array.map gen args in
       generator_pat t c gen_args
    | Fail ->
       (fun info -> Myseq.empty)
    | Alt (xc,c,m1,m2) ->
       let gen_b_d1 prob =
         let gen_m1 = gen m1 in
         (fun info ->
           let* d1 = gen_m1 info in
           Myseq.return (prob, true, d1)) in
       let gen_b_d2 prob =
         let gen_m2 = gen m2 in
         (fun info ->
           let* d2 = gen_m2 info in
           Myseq.return (prob, false, d2)) in
       let gen_b_d12 =
         match c with
         | Undet prob ->
            if prob >= 0.5 (* TODO: weight interleave according to prob *)
            then (fun info ->
              Myseq.interleave [gen_b_d1 prob info;
                                gen_b_d2 (1. -. prob) info])
            else (fun info ->
              Myseq.interleave [gen_b_d2 (1. -. prob) info;
                                gen_b_d1 prob info])
         | True -> gen_b_d1 1.
         | False -> gen_b_d2 1.
         | BoolExpr _ -> assert false in
       (fun info ->
         let* prob, b, d12 = gen_b_d12 info in
         let v = value d12 in
         Myseq.return (D (v, DAlt (prob, b, d12))))
    | Loop m1 ->
       let gen_m1 = gen m1 in
       (fun info ->
         let* d1 = gen_m1 info in (* generating a single item *)
         let ds1 = [|d1|] in
         let v = dseq_value ds1 in
         Myseq.return (D (v, DSeq (1, Range.make_open 0, ds1))))
    | Seq (n,t1,ms1) ->
       let gen_ms1 = Array.to_list (Array.map gen ms1) in
       (fun info ->
         let* ld1 = Myseq.product_fair (List.map (fun gen_mi -> gen_mi info) gen_ms1) in
         let ds1 = Array.of_list ld1 in
         let v = dseq_value ds1 in
         Myseq.return (D (v, DSeq (n, Range.make_exact n, ds1))))
    | Expr (t,e) -> assert false
  in
  gen
                                        
(* model-based parsing *)

type ('input,'value,'dconstr) parseur = 'input -> (('value,'dconstr) data * 'input) Myseq.t

let parseur (* on evaluated models: no expr, no def *)
      ~(parseur_pat : 'typ -> 'constr -> 'parse array -> 'parse)
      ~(dseq_value : ('value,'dconstr) data array -> 'value)
    : ('typ,'var,'constr,'func) model -> (('input,'value,'dconstr) parseur as 'parse) =
  let rec parse = function
    | Def (x,m1) -> assert false
    | Pat (t,c,args) ->
       let parse_args = Array.map parse args in
       parseur_pat t c parse_args
    | Fail ->
       (fun input -> Myseq.empty)
    | Alt (xc,c,m1,m2) -> (* if-then-else *)
       let seq1 prob =
         let parse_m1 = parse m1 in
         (fun input ->
           let* d1, input = parse_m1 input in
           Myseq.return (D (value d1, DAlt (prob,true,d1)), input)) in
       let seq2 prob =
         let parse_m2 = parse m2 in
         (fun input ->
           let* d2, input = parse_m2 input in
           Myseq.return (D (value d2, DAlt (prob,false,d2)), input)) in
       (match c with
        | Undet prob ->
           if prob >= 0.5 (* TODO: weight interleave according to prob *)
           then (fun input ->
             Myseq.interleave [seq1 prob input;
                               seq2 (1. -. prob) input])
           else (fun input ->
             Myseq.interleave [seq2 (1. -. prob) input;
                               seq1 prob input])
        | True -> seq1 1.
        | False -> seq2 1.
        | BoolExpr _ -> assert false)
    | Loop m1 ->
       let parse_m1 = parse m1 in
       let seq_parse_m1 = Myseq.const parse_m1 in
       (fun input ->
         let* ld1, input = Myseq.star_dependent_fair seq_parse_m1 input in
         let ds1 = Array.of_list ld1 in
         let n = Array.length ds1 in
         let v = dseq_value ds1 in
         Myseq.return (D (v, DSeq (n, Range.make_open 0, ds1)), input))
    | Seq (n,t1,ms1) ->
       let parse_lm1 = Array.to_list (Array.map parse ms1) in
       (fun input ->
         let* ld1, input = Myseq.product_dependent_fair parse_lm1 input in
         let ds1 = Array.of_list ld1 in
         let v = dseq_value ds1 in
         Myseq.return (D (v, (DSeq (n, Range.make_exact n, ds1))), input))
    | Expr (t,e) -> assert false
  in
  parse

(* model-based encoding of data *)

let dl_data
      ~(encoding_dpat : 'dconstr -> 'encoding array -> 'encoding)
      ~(encoding_alt : dl (* DL of branch choice *) -> 'encoding -> 'encoding (* with added DL choice *))
      ~(encoding_seq : dl (* DL of seq length *) -> 'encoding array -> 'encoding)
      ~(dl_of_encoding : 'encoding -> dl)
    : (('value,'dconstr) data as 'data) -> dl = (* QUICK *)
  let rec aux (D (v, dm)) =
    match dm with
    | DPat (dc, dargs) ->
       let encs = Array.map aux dargs in
       encoding_dpat dc encs
    | DAlt (prob,b,d12) ->
       let dl_choice = Mdl.Code.usage prob in
       let enc12 = aux d12 in
       encoding_alt dl_choice enc12
    | DSeq (dn,range,ds1) ->
       let dl_length = Range.dl dn range in
       let encs = Array.map aux ds1 in
       encoding_seq dl_length encs
  in
  fun d ->
  let enc = aux d in
  dl_of_encoding enc

let dl_parse_rank (rank : int) : dl =
  (* penalty DL for parse rank, starting at 0 *)
  Mdl.Code.universal_int_star rank -. 1.
  
(* model encoding *)

let size_alt = 3
let size_loop = 2
let size_seq = 2
  
let size_model_ast (* for DL computing, QUICK *)
      ~(asd : ('typ,'constr,'func) asd)
    (m : ('typ,'var,'constr,'func) model) : int =
  let rec aux = function
    | Def (x,m1) -> aux m1 (* definitions are ignore in DL, assumed determined by model AST *)
    | Pat (t,c,args) ->
       Array.fold_left
         (fun res arg -> res + aux arg)
         (if asd#is_default_constr c && args = [||] then 0 else 1)
         args
    | Fail -> assert false
    | Alt (xc,c,m1,m2) -> size_alt + aux_cond c + aux m1 + aux m2
    | Loop m1 -> size_loop + aux m1
    | Seq (n,t1,ms1) -> Array.fold_left (fun res m1 -> res + aux m1) 1 ms1
    | Expr (t,e) -> Expr.size_expr_ast e
  and aux_cond = function
    | Undet _ -> 0
    | True | False -> assert false
    | BoolExpr e -> Expr.size_expr_ast e
  in
  aux m

let nb_model_ast (* for DL computing, must be consistent with size_model_ast *)
      ~(typ_bool : 'typ)
      ~(asd : ('typ,'constr,'func) asd)
      ~(nb_expr_ast : 'typ -> int -> float) =
  let tab : ('typ * int, float) Hashtbl.t = Hashtbl.create 1013 in
  let reset () = Hashtbl.clear tab in
  let rec aux (t : 'typ) (size : int) : float (* float to handle large numbers *) =
    match Hashtbl.find_opt tab (t,size) with
    | Some nb -> nb
    | None -> (* QUICK *)
       let nb = (* counting possible expressions *)
         match asd#expr_opt t with
         | None -> 0.
         | Some t1 -> nb_expr_ast t1 size in
       let nb = (* counting possible alternatives *)
         if size >= size_alt && asd#alt_opt t
         then nb +. sum_conv [aux_cond; aux t; aux t] (size - size_alt)
                             (* split between condition, left model, right model *)
         else nb in
       let nb = (* counting Pat (c,args) *)
         let default_constr_opt, other_constr_args = asd#default_and_other_pats t in
         let nb =
           if size = 0 && default_constr_opt <> None
           then nb +. 1.
           else nb in
         List.fold_left
           (fun nb (c,t_ndim_args) ->
             if t_ndim_args = [||] (* leaf node *)
             then if size = 1 then nb +. 1. else nb
             else
               if size >= 1
               then nb +. sum_conv (Array.to_list (Array.map aux_seq t_ndim_args)) (size-1)
               else nb)
           nb other_constr_args in
       Hashtbl.add tab (t,size) nb;
       nb
  and aux_cond (size : int) : float =
    if size = 0
    then 1. (* Undet *)
    else nb_expr_ast typ_bool size (* BoolExpr *)
  and aux_seq (t,ndim : 'typ * int) (size : int) : float =
    assert (ndim >= 0);
    if ndim = 0
    then aux t size
    else
      let nb = 0. in
      let nb = (* counting possible loops *)
        if size >= size_loop
        then nb +. aux_seq (t,ndim-1) (size - size_loop)
        else nb in
      let nb = (* counting possible Seqs *)
        if size >= size_seq
        then
          Common.fold_for
            (fun n nb ->
              nb +. sum_conv (List.init n (fun _ -> aux_seq (t,ndim-1))) (size - size_seq - n)) (* cost 1 for each item to avoid pb with zero-cost models *)
            0 (max 4 (size - size_seq)) (* bounding to 4 to avoid explosion *)
            nb
        else nb in
      nb
  in
  aux, reset

let dl_model_params
      ~(dl_constr_params : 'typ -> 'constr -> dl)
      ~(dl_func_params : 'func -> dl)
      ~(dl_var : 'var -> dl)
    : ('typ,'var,'constr,'func) model -> dl =
  let dl_expr_params =
    Expr.dl_expr_params ~dl_func_params ~dl_var in
  let rec aux = function
    | Def (x,m1) -> aux m1 (* variable names do not matter, only variable choice in expr matters *)
    | Pat (t,c,args) ->
       let dl_args_params =
         Array.map aux args
         |> Array.fold_left (+.) 0. in
       dl_constr_params t c +. dl_args_params
    | Fail -> assert false
    | Alt (xc,c,m1,m2) ->
       aux_cond c +. aux m1 +. aux m2
    | Loop m1 -> aux m1
    | Seq (n,t1,ms1) ->
       Mdl.Code.universal_int_star n
       +. (Array.map aux ms1
           |> Array.fold_left (+.) 0.)
    | Expr (t,e) -> dl_expr_params e
  and aux_cond = function
    | Undet prob -> Mdl.Code.uniform 10 (* bounding float precision, TODO: use better distrib *)
    | True | False -> assert false
    | BoolExpr e -> dl_expr_params e
  in
  aux

let dl
      ~(size_model_ast : ('typ,'var,'constr,'func) model -> int)
      ~(nb_model_ast : 'typ -> int -> float)
      ~(dl_model_params : dl_var:('var -> dl) -> ('typ,'var,'constr,'func) model -> dl)
      ~(dl_var : nb_env_vars:int -> 'var -> dl) =
  fun
    ~(nb_env_vars : int)
    (m : ('typ,'var,'constr,'func) model) -> (* QUICK *)
  let size = size_model_ast m in
  let t = typ m in    
  let nb = nb_model_ast t size in
  assert (nb > 0.); (* as [m] has this size, the nb of AST of this size must not be zero *)
  Mdl.Code.universal_int_star size (* encoding model AST size *)
  +. Mdl.log2 nb (* encoding choice of model AST for that size *)
  +. dl_model_params
       ~dl_var:(dl_var ~nb_env_vars)
       m
       
(* reading *)

type ('typ,'value,'dconstr,'var,'func) read =
  { env : ('value,'dconstr) data;
    bindings : ('var,'typ,'value) Expr.bindings;
    lazy_index : ('typ,'value,'var,'func) Expr.Index.t Lazy.t;
    data : ('value,'dconstr) data;
    dl : dl }

(* let limit_dl ~(max_parse_dl_factor : float) (f_dl : 'a -> dl) (l : 'a list) : 'a list = (* QUICK *)
  match l with
  | [] -> []
  | x0::_ ->
     let dl0 = f_dl x0 in
     let min_dl = max_parse_dl_factor *. dl0 in
     List.filter (fun x -> f_dl x <= min_dl) l *)

exception Parse_failure

type ('input,'typ,'value,'dconstr,'var) eval_parse_bests = ('var,'typ,'value) Expr.bindings -> 'input -> (('value,'dconstr) data * dl) list result
        
let eval_parse_bests
      ~(max_nb_parse : int)
      ~(eval : ('typ,'var,'constr,'func) model -> ('var,'typ,'value) Expr.bindings -> ('typ,'var,'constr,'func) model result)
      ~(parseur : ('typ,'var,'constr,'func) model -> ('input,'value,'dconstr) parseur)
      ~(dl_data : ('value,'dconstr) data -> dl)

      (m0 : ('typ,'var,'constr,'func) model)
    : ('input,'typ,'value,'dconstr,'var) eval_parse_bests =
  fun bindings input ->
  Common.prof "Model.eval_parse_bests" (fun () ->
  let| m = eval m0 bindings in (* resolving expressions *)
  let parses =
    let* data, _ = parseur m input in
    let dl = (* QUICK *)
      dl_round (dl_data data) in
      (* rounding before sorting to absorb float error accumulation *)
    Myseq.return (data, dl) in
  let l_parses =
    Common.prof "Model.sorted_parseur/first_parses" (fun () ->
        parses
        |> Myseq.slice ~offset:0 ~limit:max_nb_parse
        |> Myseq.to_list) in
  if l_parses = []
  then Result.Error Parse_failure
  else
    let best_parses =
      l_parses (* QUICK *)
      |> List.stable_sort (fun (_,dl1) (_,dl2) -> dl_compare dl1 dl2) in
    Result.Ok best_parses)
  (* TODO: take into account max_parse_dl_factor? *)

let read
      ~(input_of_value : 'value -> 'input)
      ~(eval : ('typ,'var,'constr,'func) model -> ('var,'typ,'value) Expr.bindings -> ('typ,'var,'constr,'func) model result)
      ~(eval_parse_bests : ('typ,'var,'constr,'func) model -> ('input,'typ,'value,'dconstr,'var) eval_parse_bests)

      ~(dl_assuming_contents_known : bool)
      ~(env : ('value,'dconstr) data)
      ~(bindings : ('var,'typ,'value) Expr.bindings)
      ~(lazy_index : ('typ,'value,'var,'func) Expr.Index.t Lazy.t)
      (m0 : ('typ,'var,'constr,'func) model)
      (v : 'value)
    : ('typ,'value,'dconstr,'var,'func) read Myseq.t =
  Myseq.prof "Model.read" (
  let input = input_of_value v in
  let* best_parses = Myseq.from_result (eval_parse_bests m0 bindings input) in
  let* rank, (data, dl) = Myseq.with_position (Myseq.from_list best_parses) in
  let dl_rank = dl_parse_rank rank in
  let dl =
    if dl_assuming_contents_known
    then dl_rank
    else dl +. dl_rank in (* to penalize later parses, in case of equivalent parses *)
  Myseq.return { env; bindings; lazy_index; data; dl })


(* writing *)

exception Generate_failure
  
let write
      ~(eval : ('typ,'var,'constr,'func) model -> ('var,'typ,'value) Expr.bindings -> ('typ,'var,'constr,'func) model result)
      ~(generator : ('typ,'var,'constr,'func) model -> ('info,'value,'dconstr) generator)
      ~(dl_data : ('value,'dconstr) data -> dl)
      
      ~(bindings : ('var,'typ,'value) Expr.bindings)
      (m0 : ('typ,'var,'constr,'func) model)
      (info : 'info)
    : (('value,'dconstr) data * dl) Myseq.t =
  Myseq.prof "Model.write" (
  let* m = Myseq.from_result (eval m0 bindings) in
  let* data = generator m info in
  let dl = dl_data data in (* encoding of what is not specified by the evaluated model *)
  Myseq.return (data, dl))

  
(* paths and model refinement *)

let reverse_path (p : 'constr path) : 'constr path =
  let rec aux = function
    | This -> (fun rp -> rp)
    | Field (c,i,p1) ->
       let ctx1 = aux p1 in
       (fun rp -> ctx1 (Field (c,i,rp)))
    | Branch (b,p1) ->
       let ctx1 = aux p1 in
       (fun rp -> ctx1 (Branch (b,rp)))
    | Item (i,p1) ->
       let ctx1 = aux p1 in
       (fun rp -> ctx1 (Item (i,rp)))
  in
  let ctx = aux p in
  ctx This       
  
let refine (* replace submodel of [m] at [p] by [r] *) 
    : 'constr path -> ('typ,'var,'constr,'func) model -> ('typ,'var,'constr,'func) model -> ('typ,'var,'constr,'func) model =
  let rec aux p r m =
    match p, m with
    | _, Def (x,m1) ->
       let new_m1 = aux p r m1 in
       Def (x,new_m1)
    | This, _ -> r
    | Field (c,i,p1), Pat (t,c',args) when c = c' && i < Array.length args ->
       let new_args = Array.copy args in
       new_args.(i) <- aux p1 r args.(i);
       Pat (t, c, new_args)
    | Branch (true,p1), Alt (xc,c,m1,m2) ->
       let new_m1 = aux p1 r m1 in
       Alt (xc,c,new_m1,m2)
    | Branch (false,p1), Alt (xc,c,m1,m2) ->
       let new_m2 = aux p1 r m2 in
       Alt (xc,c,m1,new_m2)
    | _, Loop m1 ->
       let new_m1 = aux p r m1 in
       Loop new_m1
    | Item (i,p1), Seq (n,t1,ms1) when i >= 0 && i < n ->
       let new_ms1 = Array.copy ms1 in
       new_ms1.(i) <- aux p1 r ms1.(i);
       Seq (n,t1,new_ms1)
    | _ -> assert false
  in
  aux
