
open Madil_common
open Ndtree.Operators
open Data

type ('typ,'value,'var,'func) cond_model =
  | Undet of float (* undetermined condition, probability for left choice *)
  | True (* always true condition - only in evaluated model *)
  | False (* always false condition - only in evaluated model *)
  | BoolExpr of ('typ,'value,'var,'func) Expr.expr (* computed condition - not in evaluated model *)
 
type ('typ,'value,'var,'constr,'func) model =
  | Def of 'var * ('typ,'value,'var,'constr,'func) model (* a var is an id for the value at this sub-model - not in evaluated model *)
  | Pat of 'typ * 'constr * ('typ,'value,'var,'constr,'func) model array (* constr type may be different from data constr *)
  | Fail (* like an empty alternative - only in evaluated model *)
  | Alt of 'var (* condition var *) * ('typ,'value,'var,'func) cond_model * ('typ,'value,'var,'constr,'func) model * ('typ,'value,'var,'constr,'func) model
  | Loop of ('typ,'value,'var,'constr,'func) model
  | Nil of 'typ
  | Cons of ('typ,'value,'var,'constr,'func) model * ('typ,'value,'var,'constr,'func) model
  | Expr of 'typ * ('typ,'value,'var,'func) Expr.expr (* not in evaluated model *)
  | Value of 'typ * 'value Ndtree.t (* only in evaluated model *)

type ('var,'constr) path = ('var,'constr) path_step list
and ('var,'constr) path_step =
  | Field of 'constr * int (* Pat field *)
  | Branch of bool (* Alt branch *)
  | Head (* Cons head *)
  | Tail (* Cons tail *)
  | Alias of 'var * ('var,'constr) path (* named path, reverse path *)

let p0 : ('var,'constr) path = [] (* the empty path = This *)
let ctx0 : ('var,'constr) path = [] (* a context is a reverse path *)

let make_def (x : 'var) (m1 : ('typ,'value,'var,'constr,'func) model) : ('typ,'value,'var,'constr,'func) model =
  Def (x,m1)
let make_pat (t : 't) (c : 'constr) (args : ('typ,'value,'var,'constr,'func) model array) : ('typ,'value,'var,'constr,'func) model =
  Pat (t,c,args)
let make_alt (xc : 'var) (cond : ('typ,'value,'var,'func) cond_model) (m1 : ('typ,'value,'var,'constr,'func) model) (m2 : ('typ,'value,'var,'constr,'func) model) : ('typ,'value,'var,'constr,'func) model =
  Alt (xc,cond,m1,m2)
let make_loop (m1 : ('typ,'value,'var,'constr,'func) model) : ('typ,'value,'var,'constr,'func) model =
  Loop m1
let make_nil t = Nil t
let make_cons m0 m1 = Cons (m0,m1)
let make_expr t e = Expr (t,e)

let undef : ('typ,'value,'var,'constr,'func) model -> ('typ,'value,'var,'constr,'func) model =
  function
  | Def (_,m) -> m
  | m -> m
                    
let rec typ : ('typ,'value,'var,'constr,'func) model -> 'typ = function
  | Def (x,m1) -> typ m1
  | Pat (t,c,args) -> t
  | Fail -> assert false
  | Alt (xc,c,m1,m2) -> typ m1
  | Loop m1 -> typ m1
  | Nil t -> t
  | Cons (m0,m1) -> typ m0
  | Expr (t,e) -> t
  | Value _ -> assert false

let rec seq_length : ('typ,'value,'var,'constr,'func) model -> Range.t = function
  | Def (x,m1) -> seq_length m1
  | Pat (t,c,args) ->
     if args = [||]
     then Range.make_open 0
     else
       Array.to_list args
       |> List.map seq_length
       |> Range.inter_list
  | Fail -> Range.make_open 0
  | Alt (xc,c,m1,m2) ->
     Range.union (seq_length m1) (seq_length m2)
  | Loop m1 -> seq_length m1
  | Nil _ -> Range.make_exact 0
  | Cons (m0,m1) ->
     Range.add (Range.make_exact 1) (seq_length m1)
  | Expr _ -> Range.make_open 0
  | Value (t,v_tree) ->
     (match Ndtree.length v_tree with
      | Some n -> Range.make_exact n
      | None -> Range.make_open 0)
             
(* printing *)
  
let xp_model
      ~(xp_value : 'value html_xp)
      ~(xp_var : 'var html_xp)
      ~(xp_pat : 'constr -> unit html_xp array -> unit html_xp)
      ~(xp_func : 'func html_xp)
    : ('typ,'value,'var,'constr,'func) model html_xp =
  let rec aux ~prio_ctx ~html print m =
    match m with
    | Def (x,m1) ->
       xp_html_elt "span" ~classe:"model-def" ~html print
         (fun () ->
           xp_var ~html print x; print#string ":";
           aux ~prio_ctx ~html print m1)
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
           xp_html_elt "div" ~classe:"model-alt" ~html print
             (fun () ->
               xp_var ~html print xc; print#string ": ";
               aux_prob ~html print prob;
               print#string "? ";
               aux ~html ~prio_ctx:2 print m1;
               print#string " ";
               xp_html_elt "span" ~classe:"model-meta-operator" ~html print
                 (fun () -> print#string "|");
               print#string " ";
               aux ~html ~prio_ctx:2 print m2))
    | Alt (xc,c,m1,m2) -> (* if c then m1 else m2 *)
       xp_brackets_prio ~prio_ctx ~prio:2 ~html print
         (fun () ->
           xp_html_elt "div" ~classe:"model-alt" ~html print
             (fun () ->
               xp_html_elt "span" ~classe:"model-meta-operator" ~html print
                 (fun () -> print#string "if");
               print#string " ";
               xp_var ~html print xc; print#string ": ";
               aux_cond ~html print c;
               print#string " ";
               xp_html_elt "span" ~classe:"model-meta-operator" ~html print
                 (fun () -> print#string "then");
               print#string " ";
               aux ~html ~prio_ctx:2 print m1;
               print#string " ";
               xp_html_elt "span" ~classe:"model-meta-operator" ~html print
                 (fun () -> print#string "else");
               print#string " ";
               aux ~html ~prio_ctx:2 print m2))
      
    | Loop m1 ->
       xp_html_elt "div" ~classe:"model-block" ~html print
         (fun () -> aux ~prio_ctx:2 ~html print m1)
    (* xp_tuple1 ~delims:("〈", " ...〉") (aux ~prio_ctx:2) ~html print m1 *)
    | Nil t ->
       xp_html_elt "span" ~classe:"model-meta-operator" ~html print
         (fun () -> print#string "end")
    | Cons (m0,m1) ->
       xp_brackets_prio ~prio_ctx ~prio:1 ~html print
         (fun () ->
           xp_html_elt "div" ~classe:"model-seq" ~html print
             (fun () ->
               aux ~html ~prio_ctx:0 print m0;
               xp_html_elt "span" ~classe:"model-meta-operator" ~html print
                 (fun () -> print#string "; ");
               aux ~html ~prio_ctx:1 print m1))
    | Expr (_, Expr.Const (_,v)) ->
       xp_value ~html print v
    | Expr (_t,e) ->
       xp_html_elt "span" ~classe:"model-expr" ~html print
         (fun () ->
           Expr.xp_expr ~xp_value ~xp_var ~xp_func ~html print e)
    | Value _ -> assert false
  and aux_cond ~html print = function
    | Undet prob ->
       aux_prob ~html print prob
    | True -> assert false
    | False -> assert false
    | BoolExpr e ->
       xp_html_elt "span" ~classe:"model-expr" ~html print
         (fun () -> Expr.xp_expr ~xp_value ~xp_var ~xp_func ~html print e)
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
      ~(xp_var : 'var html_xp)
      ~(xp_field : ('constr * int) html_xp)
    : ('var,'constr) path html_xp =
  let rec aux ~html print p =
    match p with
    | [] -> ()
    | Tail::p1 ->
       aux_tail ~html print 1 p1
    | step::p1 ->
       aux_step ~html print step;
       aux ~html print p1
  and aux_step ~html print step =
    match step with
    | Field (c,i) ->
       print#string ".";
       xp_field ~html print (c,i)
    | Branch b ->
       print#string (if b then "#true" else "#false")
    | Head ->
       xp_index ~html print 0
    | Tail -> assert false
    | Alias (x,_p) ->
       print#string " ";
       xp_var ~html print x
  and aux_tail ~html print i = function
    | Head::p1 ->
       xp_index ~html print i;
       aux ~html print p1
    | Tail::p1 ->
       aux_tail ~html print (i+1) p1
    | p1 ->
       xp_slice ~html print i;
       aux ~html print p1
  and xp_index ~html print i =
    print#string "["; print#int i; print#string "]"
  and xp_slice ~html print i =
    print#string "["; print#int i; print#string ":]"
  in
  aux

(* ASD *)

class virtual ['typ,'constr,'func] asd =
  object (self)
    method virtual is_default_constr : 'constr -> bool
    method virtual default_and_other_pats : 'typ -> 'constr option * ('constr * ('typ * int) array) list (* the int is the ndim of the field *)
    method virtual funcs : 'typ -> ('func * 'typ array) list (* None when expressions not allowed for this type *)
    method virtual expr_opt : 'typ -> ('typ * bool) option (* bool for Const-ok? *)
    method virtual alt_opt : 'typ -> bool
  end

(* model evaluation *)

let binding_vars
      (m0 : ('typ,'value,'var,'constr,'func) model)
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
    | Nil t -> acc
    | Cons (m0,m1) ->
       let acc = aux m0 acc in
       let acc = aux m1 acc in
       acc
    | Expr (t,e) -> acc
    | Value _ -> assert false
  in
  aux m0 Bintree.empty

  
let get_bindings  (* QUICK *)
      ~(typ_bool : 'typ)
      ~(value_of_bool : bool -> 'value)
      (m0 : ('typ,'value,'var,'constr,'func) model as 'model)
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
    | Nil t ->
       acc
    | Cons (m0,m1) ->
       let d0_tree =
         match Ndtree.head_opt d_tree with
         | Some d0_tree -> d0_tree
         | None -> assert false in (* pb in parsing *)
       let acc = aux m0 d0_tree acc in
       let d1_tree =
         match Ndtree.tail_opt d_tree with
         | Some d1_tree -> d1_tree
         | None -> assert false in
       let acc = aux m1 d1_tree acc in
       acc
    | Expr _ -> acc
    | Value _ -> assert false
  in
  aux m0 (Ndtree.scalar (Some d0)) Expr.bindings0

exception EmptyAlt
  
let eval (* from model to evaluated model: resolving expr, ignoring def *)
      ~asd
      ~(eval_expr : ('typ,'value,'var,'func) Expr.expr -> ('var,'typ,'value) Expr.bindings -> 'value Ndtree.t result)
      ~(bool_of_value : 'value -> bool result)
      (m : ('typ,'value,'var,'constr,'func) model)
      (bindings : ('var,'typ,'value) Expr.bindings)
    : ('typ,'value,'var,'constr,'func) model result =
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
    | Nil t ->
       Result.Ok (Nil t)
    | Cons (m0,m1) ->
       let| m0' = aux m0 in
       let| m1' = aux m1 in
       Result.Ok (Cons (m0',m1'))
    | Expr (t,e) ->
       let| v_tree = eval_expr e bindings in
       Result.Ok (Value (t,v_tree))
    | Value _ -> assert false
  and aux_cond = function
    | Undet prob -> Result.Ok (Undet prob)
    | True | False -> assert false
    | BoolExpr e ->
       let| v_tree = eval_expr e bindings in
       let| v = Ndtree.unscalar v_tree in (* handle ndtrees like for Expr, with a BoolValue *)
       let| b = bool_of_value v in
       Result.Ok (if b then True else False)
  in
  aux m
  
(* model-based generation *)

type ('info,'value,'dconstr) generator = 'info -> ('value,'dconstr) data Myseq.t

let generator (* on evaluated models: no expr, no def *)
      ~(generator_pat: 'typ -> 'constr -> (('info,'value,'dconstr) generator as 'gen) array -> 'gen)
      ~(value_of_seq : 'value array -> 'value)
    : ('typ,'value,'var,'constr,'func) model -> 'gen =
  let rec gen rev_is = function
    | Def (x,m1) -> assert false
    | Pat (t,c,args) ->
       let gen_args = Array.map (gen rev_is) args in
       generator_pat t c gen_args
    | Fail ->
       (fun info -> Myseq.empty)
    | Alt (xc,c,m1,m2) ->
       let gen_b_d1 prob =
         let gen_m1 = gen rev_is m1 in
         (fun info ->
           let* d1 = gen_m1 info in
           Myseq.return (prob, true, d1)) in
       let gen_b_d2 prob =
         let gen_m2 = gen rev_is m2 in
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
       let seq_len_m1 = seq_length m1 in
       let gen_nil = Myseq.return [] in
       let rec gen_seq_m1 i info =
         if i < Range.lower seq_len_m1 then
           gen_cons i info
         else if i < (match Range.upper seq_len_m1 with
                      | None -> 9
                      | Some b -> min 9 b) then
           Myseq.if_not_empty_else (gen_cons i info) gen_nil
         else
           gen_nil
       and gen_cons i info =
         let* di = gen (i::rev_is) m1 info in
         let* ld = gen_seq_m1 (i+1) info in
         Myseq.return (di::ld) in
       (* let gen_m1 i = gen (i::rev_is) m1 in
       let rec seq_gen_m1 i info =
         if i < 9 (* TODO: find a better way *)
         then Myseq.if_not_empty_else
                (let* di = gen_m1 i info in
                 let* ld = seq_gen_m1 (i+1) info in
                 Myseq.return (di::ld))
                (Myseq.return [])
         else Myseq.return [] in *)
       (fun info ->
         let* ld1 = gen_seq_m1 0 info in
         let ds1 = Array.of_list ld1 in
         let n = Array.length ds1 in
         let v = value_of_seq (Array.map Data.value ds1) in
         assert (Range.mem n seq_len_m1);
         Myseq.return (D (v, DSeq (n, seq_len_m1, ds1))))
    | Nil t ->
       (fun info ->
         Myseq.empty)
    | Cons (m0,m1) ->
       let is = List.rev rev_is in
       let gen_m = (* choosing model according to first index *)
         match is with
         | 0::is0 -> gen (List.rev is0) m0
         | i::is1 -> gen (List.rev ((i-1)::is1)) m1
         | [] -> (fun info -> Myseq.empty) in
       (fun info ->
         gen_m info)
    | Expr (t,e) -> assert false
    | Value (t,v_tree) ->
       let is = List.rev rev_is in
       (match Ndtree.lookup v_tree is with
        | Some v -> (fun info -> Myseq.return (D (v, DExpr)))
        | None -> (fun info -> Myseq.empty))
  in
  gen []
                                        
(* model-based parsing *)

type ('input,'value,'dconstr) parseur = 'input -> (('value,'dconstr) data * 'input) Myseq.t

let parseur (* on evaluated models: no expr, no def *)
      ~(parseur_value : 'value -> 'parse)
      ~(parseur_pat : 'typ -> 'constr -> 'parse array -> 'parse)
      ~(value_of_seq : 'value array -> 'value)
    : ('typ,'value,'var,'constr,'func) model -> ?is:(int list) -> (('input,'value,'dconstr) parseur as 'parse) =
  let rec parse rev_is m input =
    match m with
    | Def (x,m1) -> assert false
    | Pat (t,c,args) ->
       let parse_args = Array.map (parse rev_is) args in
       parseur_pat t c parse_args input
    | Fail -> Myseq.empty
    | Alt (xc,c,m1,m2) -> (* if-then-else *)
       let seq1 prob =
         let* d1, input = parse rev_is m1 input in
         Myseq.return (D (value d1, DAlt (prob,true,d1)), input) in
       let seq2 prob =
         let* d2, input = parse rev_is m2 input in
         Myseq.return (D (value d2, DAlt (prob,false,d2)), input) in
       (match c with
        | Undet prob ->
           if prob >= 0.5 (* TODO: weight interleave according to prob *)
           then Myseq.interleave [seq1 prob; seq2 (1. -. prob)]
           else Myseq.interleave [seq2 (1. -. prob); seq1 prob]
        | True -> seq1 1.
        | False -> seq2 1.
        | BoolExpr _ -> assert false)
    | Loop m1 ->
       let seq_len_m1 = seq_length m1 in
       let seq_parse_m1 =
         let* i = Myseq.counter 0 in
         Myseq.return (parse (i::rev_is) m1) in
       let* ld1, input = Myseq.star_dependent_fair seq_parse_m1 input in
       let ds1 = Array.of_list ld1 in
       let n = Array.length ds1 in
       let v = value_of_seq (Array.map Data.value ds1) in
       if Range.mem n seq_len_m1
       then Myseq.return (D (v, DSeq (n, seq_len_m1, ds1)), input)
       else Myseq.empty (* could not parse the expected number of elements *)
    | Nil t -> Myseq.empty
    | Cons (m0,m1) ->
       let is = List.rev rev_is in
       (match is with (* choosing model according to first index *)
       | 0::is0 -> parse (List.rev is0) m0 input
       | i::is1 -> parse (List.rev ((i-1)::is1)) m1 input
       | [] -> Myseq.empty)
    | Expr (t,e) -> assert false
    | Value (t,v_tree) ->
       let is = List.rev rev_is in
       assert (List.length is >= Ndtree.ndim v_tree);
       (match Ndtree.lookup v_tree is with
       | Some v -> parseur_value v input
       | None -> Myseq.empty)
  in
  fun m ?(is = []) input ->
  parse (List.rev is) m input

(* model-based encoding of data *)

let dl_data
      ~(encoding_dpat : 'dconstr -> 'encoding array -> 'encoding)
      ~(encoding_alt : dl (* DL of branch choice *) -> 'encoding -> 'encoding (* with added DL choice *))
      ~(encoding_seq : dl (* DL of seq length *) -> 'encoding array -> 'encoding)
      ~(encoding_expr_value : 'value -> 'encoding) (* DL = 0 *)
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
    | DExpr -> encoding_expr_value v
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
let size_nil = 1
let size_cons = 1
let size_seq = 2
  
let size_model_ast (* for DL computing, QUICK *)
      ~(asd : ('typ,'constr,'func) asd)
    (m : ('typ,'value,'var,'constr,'func) model) : int =
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
    | Nil t -> size_nil
    | Cons (m0,m1) -> size_cons + aux m0 + aux m1
    | Expr (t,e) -> Expr.size_expr_ast e
    | Value _ -> assert false
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
  let tab : ('typ * int, float) Hashtbl.t = Hashtbl.create 1013 in (* TODO: make it a function of ndim as well *)
  let reset () = Hashtbl.clear tab in
  let rec aux (t : 'typ) (size : int) : float (* float to handle large numbers *) =
    match Hashtbl.find_opt tab (t,size) with
    | Some nb -> nb
    | None -> (* QUICK *)
       let nb = 0. in
       let nb = (* counting possible expressions *)
         match asd#expr_opt t with
         | None -> nb
         | Some (t1, _const_ok) -> nb +. nb_expr_ast t1 size in
       let nb = (* counting possible alternatives *)
         if size >= size_alt && asd#alt_opt t
         then nb +. sum_conv [aux_cond; aux t; aux t] (size - size_alt)
                             (* split between condition, left model, right model *)
         else nb in
       let nb = (* counting possible Nil *)
         if size = size_nil
         then nb +. 1.
         else nb in
       let nb = (* counting possible Cons *)
         if size >= size_cons
         then nb +. sum_conv [aux t; aux t] (size - size_cons)
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
    else (* counting possible loops *)
      if size >= size_loop
      then aux_seq (t,ndim-1) (size - size_loop)
      else 0.
  in
  aux, reset

let dl_model_params
      ~(dl_value : 'typ -> 'value -> dl)
      ~(dl_var : 'typ -> 'var -> dl)
      ~(dl_constr_params : 'typ -> 'constr -> dl)
      ~(dl_func_params : 'typ -> 'func -> dl)
    : ('typ,'value,'var,'constr,'func) model -> dl =
  let dl_expr_params =
    Expr.dl_expr_params ~dl_value ~dl_var ~dl_func_params in
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
    | Nil t -> 0.
    | Cons (m0,m1) -> aux m0 +. aux m1
    | Expr (t,e) -> dl_expr_params e
    | Value _ -> assert false
  and aux_cond = function
    | Undet prob -> Mdl.Code.uniform 10 (* bounding float precision, TODO: use better distrib *)
    | True | False -> assert false
    | BoolExpr e -> dl_expr_params e
  in
  aux

let dl
      ~(size_model_ast : ('typ,'value,'var,'constr,'func) model -> int)
      ~(nb_model_ast : 'typ -> int -> float)
      ~(dl_model_params : dl_var:('typ -> 'var -> dl) -> ('typ,'value,'var,'constr,'func) model -> dl)
      ~(dl_var : nb_env_vars:int -> 'typ -> 'var -> dl) =
  fun
    ~(nb_env_vars : int)
    (m : ('typ,'value,'var,'constr,'func) model) -> (* QUICK *)
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
    mutable lazy_index : ('typ,'value,'var,'func) Expr.Index.t option; (* not using Lazy.t because breaks comparisons and hash *)
    data : ('value,'dconstr) data;
    dl : dl }

let force_index
      ~(make_index : ('var,'typ,'value) Expr.bindings -> ('typ,'value,'var,'func) Expr.Index.t)
      (read : ('typ,'value,'dconstr,'var,'func) read)
    : ('typ,'value,'var,'func) Expr.Index.t =
  match read.lazy_index with
  | Some index -> index
  | None ->
     let index = Common.prof "Model.make_index" (fun () ->
                     make_index read.bindings) in
     read.lazy_index <- Some index;
     index [@@inline]
  
(* let limit_dl ~(max_parse_dl_factor : float) (f_dl : 'a -> dl) (l : 'a list) : 'a list = (* QUICK *)
  match l with
  | [] -> []
  | x0::_ ->
     let dl0 = f_dl x0 in
     let min_dl = max_parse_dl_factor *. dl0 in
     List.filter (fun x -> f_dl x <= min_dl) l *)

exception Parse_failure

type ('input,'value,'dconstr) parse_bests = 'input -> (('value,'dconstr) data * dl) list result
        
let parse_bests
      ~(max_nb_parse : int)
      ~(parseur : ('typ,'value,'var,'constr,'func) model -> ?is:(int list) -> ('input,'value,'dconstr) parseur)
      ~(dl_data : ('value,'dconstr) data -> dl)

      (m : ('typ,'value,'var,'constr,'func) model)
      ?(is = [])
    : ('input,'value,'dconstr) parse_bests =
  fun input ->
  Common.prof "Model.parse_bests" (fun () ->
  let parses =
    let* data, _ = parseur m ~is input in
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
      ~(input_of_value : 'typ -> 'value -> 'input)
      ~(eval : ('typ,'value,'var,'constr,'func) model -> ('var,'typ,'value) Expr.bindings -> ('typ,'value,'var,'constr,'func) model result)
      ~(parse_bests : ('typ,'value,'var,'constr,'func) model -> ?is:(int list) -> ('input,'value,'dconstr) parse_bests)

      ~(dl_assuming_contents_known : bool)
      ~(env : ('value,'dconstr) data)
      ~(bindings : ('var,'typ,'value) Expr.bindings)
      (m0 : ('typ,'value,'var,'constr,'func) model)
      (v : 'value)
    : ('typ,'value,'dconstr,'var,'func) read Myseq.t =
  Myseq.prof "Model.read" (
  let t = typ m0 in
  let input = input_of_value t v in
  let* m = Myseq.from_result (eval m0 bindings) in    
  let* best_parses = Myseq.from_result (parse_bests m input) in
  let* rank, (data, dl) = Myseq.with_position (Myseq.from_list best_parses) in
  let dl_rank = dl_parse_rank rank in
  let dl =
    if dl_assuming_contents_known
    then dl_rank
    else dl +. dl_rank in (* to penalize later parses, in case of equivalent parses *)
  Myseq.return { env; bindings; lazy_index=None; data; dl })


(* writing *)

exception Generate_failure
  
let write
      ~(eval : ('typ,'value,'var,'constr,'func) model -> ('var,'typ,'value) Expr.bindings -> ('typ,'value,'var,'constr,'func) model result)
      ~(generator : ('typ,'value,'var,'constr,'func) model -> ('info,'value,'dconstr) generator)
      ~(dl_data : ('value,'dconstr) data -> dl)
      
      ~(bindings : ('var,'typ,'value) Expr.bindings)
      (m0 : ('typ,'value,'var,'constr,'func) model)
      (info : 'info)
    : (('value,'dconstr) data * dl) Myseq.t =
  Myseq.prof "Model.write" (
  let* m = Myseq.from_result (eval m0 bindings) in
  let* data = generator m info in
  let dl = dl_data data in (* encoding of what is not specified by the evaluated model *)
  Myseq.return (data, dl))

  
(* paths and model refinement *)
  
let refine (* replace submodel of [m] at [p] by [r] *) 
    : ('var,'constr) path -> ('typ,'value,'var,'constr,'func) model -> ('typ,'value,'var,'constr,'func) model -> ('typ,'value,'var,'constr,'func) model =
  let rec aux p r m =
    match p, m with
    | _, Def (x,m1) ->
       let new_m1 = aux p r m1 in
       Def (x,new_m1) 
    | Alias (x,p0) :: p1, _ ->
       aux (List.rev_append p0 p1) r m
    | [], _ -> r
    | Field (c,i) :: p1, Pat (t,c',args) when c = c' && i < Array.length args ->
       let new_args = Array.copy args in
       new_args.(i) <- aux p1 r args.(i);
       Pat (t, c, new_args)
    | Branch true :: p1, Alt (xc,c,m1,m2) ->
       let new_m1 = aux p1 r m1 in
       Alt (xc,c,new_m1,m2)
    | Branch false :: p1, Alt (xc,c,m1,m2) ->
       let new_m2 = aux p1 r m2 in
       Alt (xc,c,m1,new_m2)
    | _, Loop m1 ->
       let new_m1 = aux p r m1 in
       Loop new_m1
    | Head :: p1, Cons (m0,m1) ->
       let new_m0 = aux p1 r m0 in
       Cons (new_m0,m1)
    | Tail :: p1, Cons (m0,m1) ->
       let new_m1 = aux p1 r m1 in
       Cons (m0,new_m1)
    | _ -> assert false
  in
  aux
