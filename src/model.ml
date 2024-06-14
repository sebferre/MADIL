
open Madil_common
open Ndtree.Operators
open Data

type ('typ,'value,'var,'func) cond_model =
  | Undet of float (* undetermined condition, probability for left choice *)
  | BoolExpr of ('typ,'value,'var,'func) Expr.expr (* computed condition - not in evaluated model *)
 
type ('typ,'value,'var,'constr,'func) model =
  | Def of 'var * ('typ,'value,'var,'constr,'func) model (* a var is an id for the value at this sub-model *)
  | Any of 'typ
  | Pat of 'typ * 'constr * ('typ,'value,'var,'constr,'func) model array (* constr type may be different from data constr *)
  | Alt of 'var (* condition var *) * ('typ,'value,'var,'func) cond_model * ('typ,'value,'var,'constr,'func) model * ('typ,'value,'var,'constr,'func) model
  | Loop of 'var * ('typ,'value,'var,'constr,'func) model
  | Nil of 'typ
  | Cons of 'var * ('typ,'value,'var,'constr,'func) model * ('typ,'value,'var,'constr,'func) model
  | Expr of 'typ * ('typ,'value,'var,'func) Expr.expr
  | Derived of 'typ (* derived value, in general from sibling pattern args, like an implicit expression *)

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
let make_any (t : 't) : ('typ,'value,'var,'constr,'func) model =
  Any t
let make_pat (t : 't) (c : 'constr) (args : ('typ,'value,'var,'constr,'func) model array) : ('typ,'value,'var,'constr,'func) model =
  Pat (t,c,args)
let make_alt (xc : 'var) (cond : ('typ,'value,'var,'func) cond_model) (m1 : ('typ,'value,'var,'constr,'func) model) (m2 : ('typ,'value,'var,'constr,'func) model) : ('typ,'value,'var,'constr,'func) model =
  Alt (xc,cond,m1,m2)
let make_loop (xl : 'var) (m1 : ('typ,'value,'var,'constr,'func) model) : ('typ,'value,'var,'constr,'func) model =
  Loop (xl,m1)
let make_nil t = Nil (t)
let make_cons xl m0 m1 = Cons (xl,m0,m1)
let make_expr t e = Expr (t,e)
let make_expr_const t v = Expr (t, Expr.Const (t, v))
let make_derived t = Derived t

let undef : ('typ,'value,'var,'constr,'func) model -> ('typ,'value,'var,'constr,'func) model =
  function
  | Def (_,m) -> m
  | m -> m
                    
let rec typ : ('typ,'value,'var,'constr,'func) model -> 'typ = function
  | Def (x,m1) -> typ m1
  | Any t -> t
  | Pat (t,c,args) -> t
  | Alt (xc,c,m1,m2) -> typ m1
  | Loop (xl,m1) -> typ m1
  | Nil t -> t
  | Cons (xl,m0,m1) -> typ m0
  | Expr (t,e) -> t
  | Derived t -> t

(* deprecated *)
(*let rec seq_length rev_xis (xl : 'var) : ('typ,'value,'var,'constr,'func) model -> Range.t = function
  | Def (x,m1) -> seq_length rev_xis xl m1
  | Pat (t,c,args) ->
     if args = [||]
     then Range.make_open 0 (* broadcasting scalar *)
     else
       Array.to_list args
       |> List.map (seq_length rev_xis xl)
       |> Range.inter_list
  | Fail -> Range.make_open 0
  | Alt (xc,c,m1,m2) ->
     Range.union (seq_length rev_xis xl m1) (seq_length rev_xis xl m2)
  | Loop (xl1,m1) -> seq_length rev_xis xl m1
  | Nil _ -> Range.make_exact 0
  | Cons (xl1,m0,m1) ->
     if xl1 = xl
     then Range.add
            (Range.make_exact 1)
            (seq_length rev_xis xl m1)
     else Range.union
            (let rev_xis0 = List.remove_assoc xl1 rev_xis in 
              seq_length rev_xis0 xl m0)
            (let rev_xis1 =
               match List.assoc_opt xl1 rev_xis with
               | Some i -> list_replace_assoc xl1 (i - 1) rev_xis
               | None -> rev_xis in 
             seq_length rev_xis1 xl m1)
  | Expr _ -> Range.make_open 0
  | Value (t,v_tree) ->
     let idx = List.rev_map (fun (x,i) -> Some i) rev_xis in
     (match Ndtree.index v_tree idx with
      | Some v1_tree ->
         (match Ndtree.length v1_tree with
          | Some n -> Range.make_exact n
          | None -> Range.make_open 0) (* broadcasting scalar *)
      | None -> Range.make_open 0) (* dummy, should be the empty range *)
  | Derived t -> Range.make_open 0*)

let rec is_index_invariant : ('typ,'value,'var,'constr,'func) model -> bool = function
  | Def (x,m1) -> is_index_invariant m1
  | Any t -> true
  | Pat (t,c,args) -> Array.for_all is_index_invariant args
  | Alt (xc,c,m1,m2) -> is_index_invariant m1 && is_index_invariant m2
  | Loop (xl,m1) -> is_index_invariant m1
  | Nil _ -> false
  | Cons _ -> false
  | Expr _ -> false (* in case it evaluates to a non-scalar ndtree *)
  | Derived _ -> false (* in case it evaluates to a non-scalar ndtree *)
    
(* printing *)
  
let xp_model
      ~(xp_value : 'value html_xp)
      ~(xp_var : 'var html_xp)
      ~(xp_any : 'typ -> unit html_xp)
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
    | Any t ->
       xp_html_elt "span" ~classe:"model-any" ~html print
         (fun () ->
           xp_any t ~html print ())
    | Pat (_t,c,args) ->
       let xp_args =
         Array.map
           (fun arg -> (fun ~html print () -> aux ~prio_ctx:0 ~html print arg))
           args in
       xp_pat c xp_args ~html print ()

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
      
    | Loop (xl,m1) ->
       print#string "for "; xp_var ~html print xl; print#string ":";
       xp_html_elt "div" ~classe:"model-block" ~html print
         (fun () -> aux ~prio_ctx:2 ~html print m1)
    (* xp_tuple1 ~delims:("〈", " ...〉") (aux ~prio_ctx:2) ~html print m1 *)
    | Nil t ->
       xp_html_elt "span" ~classe:"model-meta-operator" ~html print
         (fun () -> print#string " end")
    | Cons (xl,m0,m1) ->
       xp_brackets_prio ~prio_ctx ~prio:1 ~html print
         (fun () ->
           xp_html_elt "div" ~classe:"model-seq" ~html print
             (fun () ->
               xp_var ~html print xl;
               xp_html_elt "span" ~classe:"model-meta-operator" ~html print
                 (fun () -> print#string " first: ");
               aux ~html ~prio_ctx:0 print m0;
               xp_html_elt "span" ~classe:"model-meta-operator" ~html print
                 (fun () -> print#string "; rest: ");
               aux ~html ~prio_ctx:1 print m1))
    | Expr (_, Expr.Const (_,v)) ->
       xp_value ~html print v
    | Expr (_t,e) ->
       xp_html_elt "span" ~classe:"model-expr" ~html print
         (fun () ->
           Expr.xp_expr ~xp_value ~xp_var ~xp_func ~html print e)
    | Derived _t ->
       print#string " (derived)"
  and aux_cond ~html print = function
    | Undet prob ->
       aux_prob ~html print prob
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
    method virtual default_and_other_pats : 'typ -> 'constr option * ('constr * ('typ * int) array) list (* omit derived arguments; the int is the ndim of the field *)
    method virtual funcs : 'typ -> ('func * 'typ array) list (* None when expressions not allowed for this type *)
    method virtual expr_opt : 'typ -> bool * 'typ list (* OK to produce constant values, and list of compatible types  *)
    method virtual alt_opt : 'typ -> bool
  end

(* model evaluation *)

let binding_vars
      ~(typ_bool : 'typ)
      (m0 : ('typ,'value,'var,'constr,'func) model)
    : ('var, 'typ) Expr.binding_vars =
  let rec aux m acc =
    match m with
    | Def (x,m1) ->
       let t = typ m1 in
       let acc = aux m1 acc in
       Mymap.add x t acc
    | Any t -> acc
    | Pat (t,c,args) ->
       Array.fold_right aux args acc
    | Alt (xc,cond,m1,m2) ->
       let acc = aux m1 acc in
       let acc = aux m2 acc in
       Mymap.add xc typ_bool acc
    | Loop (xl,m1) -> aux m1 acc (* xl is a local var *)
    | Nil (t) -> acc
    | Cons (xl,m0,m1) ->
       let acc = aux m0 acc in
       let acc = aux m1 acc in
       acc
    | Expr (t,e) -> acc
    | Derived t -> acc
  in
  aux m0 Mymap.empty
  
let get_bindings  (* QUICK *)
      ~(typ_bool : 'typ)
      ~(value_of_bool : bool -> 'value)
      (m0 : ('typ,'value,'var,'constr,'func) model as 'model)
      (d0 : ('value,'constr) data as 'data)
    : ('var,'typ,'value) Expr.bindings =
  let rec aux rev_xls m (d_tree : 'data Ndtree.t) acc =
    match m with
    | Def (x,m1) ->
       let acc = aux rev_xls m1 d_tree acc in
       let t1 = typ m1 in
       let v_tree =
         let< d = d_tree in
         Data.value d in
       Mymap.add x (t1,v_tree) acc
    | Any t -> acc
    | Pat (t,c,args) ->
       let n = Array.length args in
       let ref_acc = ref acc in (* missing Array.fold_right2 *)
       for i = 0 to n - 1 do
         let di_tree =
           let< d = d_tree in
           match d with
           | DPat (_v, dc, dargs) ->
              assert (Array.length dargs = n);
              dargs.(i)
           | _ -> assert false in
         ref_acc := aux rev_xls args.(i) di_tree !ref_acc
       done;
       !ref_acc
    | Alt (xc,c,m1,m2) ->
       let d1_tree =
         let<? d = d_tree in
         match d with
         | DAlt (_prob,b,d12) -> if b then Some d12 else None
         | _ -> assert false in
       let acc = aux rev_xls m1 d1_tree acc in
       let d2_tree =
         let<? d = d_tree in
         match d with
         | DAlt (_prob,b,d12) -> if b then None else Some d12
         | _ -> assert false in
       let acc = aux rev_xls m2 d2_tree acc in
       let vc_tree =
         let< d = d_tree in
         match d with
         | DAlt (_prob,b,d12) -> value_of_bool b
         | _ -> assert false in
       Mymap.add xc (typ_bool, vc_tree) acc
    | Loop (xl,m1) ->
       let d1_tree =
         let<* d = d_tree in
         match d with
         | Some (DSeq (_v, ds1)) ->
            Ndtree.pack1 (Array.map (fun d1 -> Some d1) ds1)
         | None ->
            Ndtree.pack1 [|None|]
         | _ -> assert false in
       aux (xl::rev_xls) m1 d1_tree acc
    | Nil (t) ->
       acc
    | Cons (xl,m0,m1) ->
       let indices, slices =
         List.split
           (List.rev_map
              (fun yl ->
                if yl = xl
                then Some 0, (1,None)
                else None, (0,None))
              rev_xls) in
       (match Ndtree.index d_tree indices, Ndtree.slice d_tree slices with
        | Some d0_tree, Some d1_tree ->
           let acc = aux (list_remove xl rev_xls) m0 d0_tree acc in
           let acc = aux rev_xls m1 d1_tree acc in
           acc
        | _ -> acc) (* for cases where sequences end before this Cons pattern *)
    | Expr _ -> acc
    | Derived _ -> acc
  in
  aux [] m0 (Ndtree.scalar (Some d0)) Expr.bindings0


(* model-based generation *)

type ('info,'var,'typ,'value,'constr) generator = 'info -> (('value,'constr) data * 'info) Myseq.t

let generator (* on evaluated models: no expr, no def *)
      ~(eval_expr : ('typ,'value,'var,'func) Expr.expr -> ('var,'typ,'value) Expr.bindings -> 'value Ndtree.t result)
      ~(bool_of_value : 'value -> bool result)
      ~(generator_value : 'value -> 'gen)
      ~(generator_any : 'typ -> 'gen)
      ~(generator_pat : 'typ -> 'constr -> (('info,'var,'typ,'value,'constr) generator as 'gen) array -> 'gen)
      ~(generator_end : depth:int -> 'info -> 'info Myseq.t)
      ~(value_of_seq : 'value array -> 'value)
    : ?xis:(('var * int) list) -> ('typ,'value,'var,'constr,'func) model -> ('var,'typ,'value) Expr.bindings -> 'gen =
  fun ?(xis = []) m bindings info ->
  let rec gen rev_xis m info =
    match m with
    | Def (x,m1) ->
       gen rev_xis m1 info
    | Any t ->
       generator_any t info
    | Pat (t,c,args) ->
       let gen_args = Array.map (gen rev_xis) args in
       generator_pat t c gen_args info
    | Alt (xc,c,m1,m2) ->
       let gen_b_d1 prob =
         let* d1, info = gen rev_xis m1 info in
         let d = DAlt (prob,true,d1) in
         Myseq.return (d, info) in
       let gen_b_d2 prob =
         let* d2, info = gen rev_xis m2 info in
         let d = DAlt (prob,false,d2) in
         Myseq.return (d, info) in
       (match c with
        | Undet prob ->
           if prob >= 0.5 (* TODO: weight interleave according to prob *)
           then Myseq.interleave [gen_b_d1 prob;
                                  gen_b_d2 (1. -. prob)]
           else Myseq.interleave [gen_b_d2 (1. -. prob);
                                  gen_b_d1 prob]
        | BoolExpr e ->
           let* b =
             Myseq.from_result
               (let| v_tree = eval_expr e bindings in
                let| v = Ndtree.unscalar v_tree in
                bool_of_value v) in
           if b
           then gen_b_d1 1.
           else gen_b_d2 1.)
    | Loop (xl,m1) ->
       let depth = 1 + List.length rev_xis in
       let seq_gen_m1 =
         let* i = Myseq.counter 0 in
         Myseq.return (gen ((xl,i)::rev_xis) m1) in
       let* ld1, info = Myseq.star_dependent_max (* _fair : BUGGY *) seq_gen_m1 info in
       let* info = generator_end ~depth info in (* checking valid end *)
       (* Myseq.star_dependent_max prevents stop anywhere *)
       let ds1 = Array.of_list ld1 in
       let v = value_of_seq (Array.map Data.value ds1) in
       let d = DSeq (v, ds1) in
       Myseq.return (d, info)
    | Nil (t) -> Myseq.empty
    | Cons (xl,m0,m1) ->
       (* choosing model according to first index *)
       (match List.assoc_opt xl rev_xis with
        | None -> Myseq.empty
        | Some 0 -> gen (List.remove_assoc xl rev_xis) m0 info
        | Some i -> gen (list_replace_assoc xl (i-1) rev_xis) m1 info)
    | Expr (t,e) ->
       let* v_tree = Myseq.from_result (eval_expr e bindings) in
       let is = List.rev_map snd rev_xis in
       if List.length is >= Ndtree.ndim v_tree
       then
         match Ndtree.lookup v_tree is with
         | Some v -> generator_value v info (* Myseq.return (DExpr v, info) *)
         | None -> Myseq.empty
       else Myseq.empty (* TODO: accepting vtrees ? *)
    | Derived t ->
       failwith "Derived arguments must not be generated but computed" (* must be computed, not generated *)
  in
  gen (List.rev xis) m info
     
(* model-based parsing *)

type ('input,'var,'typ,'value,'constr) parseur = 'input -> (('value,'constr) data * 'input) Myseq.t

let parseur (* on evaluated models: no expr, no def *)
      ~(eval_expr : ('typ,'value,'var,'func) Expr.expr -> ('var,'typ,'value) Expr.bindings -> 'value Ndtree.t result)
      ~(bool_of_value : 'value -> bool result)
      ~(parseur_value : 'value -> 'parse)
      ~(parseur_any : 'typ -> 'parse)
      ~(parseur_pat : 'typ -> 'constr -> 'parse array -> 'parse)
      ~(parseur_end : depth:int -> 'input -> 'input Myseq.t)
      ~(value_of_seq : 'value array -> 'value)
    : ?xis:(('var * int) list) -> ('typ,'value,'var,'constr,'func) model -> ('var,'typ,'value) Expr.bindings -> (('input,'var,'typ,'value,'constr) parseur as 'parse) =
  fun ?(xis = []) m bindings input ->
  let rec parse rev_xis m input =
    match m with
    | Def (x,m1) ->
       parse rev_xis m1 input
    | Any t ->
       parseur_any t input
    | Pat (t,c,args) ->
       let parse_args = Array.map (parse rev_xis) args in
       parseur_pat t c parse_args input
    | Alt (xc,c,m1,m2) -> (* if-then-else *)
       let seq1 prob =
         let* d1, input = parse rev_xis m1 input in
         let d = DAlt (prob,true,d1) in
         Myseq.return (d, input) in
       let seq2 prob =
         let* d2, input = parse rev_xis m2 input in
         let d = DAlt (prob,false,d2) in
         Myseq.return (d, input) in
       (match c with
        | Undet prob ->
           if prob >= 0.5 (* TODO: weight interleave according to prob *)
           then Myseq.interleave [seq1 prob; seq2 (1. -. prob)]
           else Myseq.interleave [seq2 (1. -. prob); seq1 prob]
        | BoolExpr e ->
           let* b =
             Myseq.from_result
               (let| v_tree = eval_expr e bindings in
                let| v = Ndtree.unscalar v_tree in
                bool_of_value v) in
           if b
           then seq1 1.
           else seq2 1.)                
    | Loop (xl,m1) ->
       let depth = 1 + List.length rev_xis in
       let seq_parse_m1 =
         let* i = Myseq.counter 0 in
         Myseq.return (parse ((xl,i)::rev_xis) m1) in
       let* ld1, input = Myseq.star_dependent_max (* _fair : BUGGY *) seq_parse_m1 input in
       let* input = parseur_end ~depth input in (* checking valid end *)
       (* Myseq.star_dependent_max prevents stop anywhere *)
       let ds1 = Array.of_list ld1 in
       let v = value_of_seq (Array.map Data.value ds1) in
       let d = DSeq (v, ds1) in
       Myseq.return (d, input)
    | Nil (t) -> Myseq.empty
    | Cons (xl,m0,m1) ->
       (match List.assoc_opt xl rev_xis with
        | None -> Myseq.empty
        | Some 0 -> parse (List.remove_assoc xl rev_xis) m0 input
        | Some i -> parse (list_replace_assoc xl (i-1) rev_xis) m1 input)
    | Expr (t,e) ->
       let* v_tree = Myseq.from_result (eval_expr e bindings) in
       let is = List.rev_map snd rev_xis in
       if List.length is >= Ndtree.ndim v_tree
       then
         match Ndtree.lookup v_tree is with
         | Some v -> parseur_value v input
         | None -> Myseq.empty
       else Myseq.empty (* TODO: accepting vtrees ? *)
    | Derived t ->
       failwith "Derived arguments must not be parsed but computed" 
  in
  parse (List.rev xis) m input

(* model-based encoding of data *)

let dl_data
      ~(encoding_dany : 'value -> 'encoding)
      ~(encoding_dpat : 'constr -> 'encoding array -> 'encoding)
      ~(encoding_alt : dl (* DL of branch choice *) -> 'encoding -> 'encoding (* with added DL choice *))
      ~(encoding_seq : 'encoding array -> 'encoding)
      ~(encoding_expr_value : 'value -> 'encoding) (* DL = 0 *)
      ~(dl_of_encoding : 'encoding -> dl)
    : (('value,'constr) data as 'data) -> dl = (* QUICK *)
  let rec aux = function
    | DAny (_, v_r) -> encoding_dany v_r
    | DPat (_, dc, dargs) ->
       let encs = Array.map aux dargs in
       encoding_dpat dc encs
    | DAlt (prob,b,d12) ->
       let dl_choice = Mdl.Code.usage prob in
       let enc12 = aux d12 in
       encoding_alt dl_choice enc12
    | DSeq (_, ds1) ->
       let encs = Array.map aux ds1 in
       encoding_seq encs
    | DExpr v -> encoding_expr_value v
  in
  fun d ->
  let enc = aux d in
  dl_of_encoding enc

let dl_parse_rank (rank : int) : dl =
  (* penalty DL for parse rank, starting at 0 *)
  Mdl.Code.universal_int_star rank -. 1.
  
(* model encoding *)

let size_any = 1
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
    | Any t -> size_any
    | Pat (t,c,args) ->
       Array.fold_left
         (fun res arg -> res + aux arg)
         (if asd#is_default_constr c && args = [||] then 0 else 1)
         args
    | Alt (xc,c,m1,m2) -> size_alt + aux_cond c + aux m1 + aux m2
    | Loop (xl,m1) -> size_loop + aux m1
    | Nil t -> size_nil
    | Cons (xl,m0,m1) -> size_cons + aux m0 + aux m1
    | Expr (t,e) -> Expr.size_expr_ast e
    | Derived t -> 0 (* implicit, no information there *)
  and aux_cond = function
    | Undet _ -> 0
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
         let const_ok, ts1 = asd#expr_opt t in
         List.fold_left (* not sure this is best to sum over all ts1 if they share a lot *)
           (fun nb t1 -> nb +. nb_expr_ast t1 size)
           nb ts1 in
       let nb = (* counting possible Any *)
         if size = size_any
         then nb +. 1.
         else nb in
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
    : ndim:int -> ('typ,'value,'var,'constr,'func) model -> dl =
  let dl_expr_params =
    Expr.dl_expr_params ~dl_value ~dl_var ~dl_func_params in
  let rec aux ndim = function
    | Def (x,m1) -> aux ndim m1 (* variable names do not matter, only variable choice in expr matters *)
    | Any t -> 0.
    | Pat (t,c,args) ->
       let dl_args_params =
         Array.map (aux ndim) args
         |> Array.fold_left (+.) 0. in
       dl_constr_params t c +. dl_args_params
    | Alt (xc,c,m1,m2) ->
       aux_cond c +. aux ndim m1 +. aux ndim m2
    | Loop (xl,m1) -> aux (ndim+1) m1 (* rlen encoded by parent pattern *)
    | Nil t -> 0.
    | Cons (xl,m0,m1) ->
       assert (ndim > 0);
       Mdl.Code.uniform ndim (* choice of loop var *)
       +. aux (ndim-1) m0
       +. aux ndim m1
    | Expr (t,e) -> dl_expr_params e
    | Derived t -> 0.
  and aux_cond = function
    | Undet prob -> Mdl.Code.uniform 10 (* bounding float precision, TODO: use better distrib *)
    | BoolExpr e -> dl_expr_params e
  in
  fun ~ndim m ->
  aux ndim m

let dl
      ~(size_model_ast : ('typ,'value,'var,'constr,'func) model -> int)
      ~(nb_model_ast : 'typ -> int -> float)
      ~(dl_model_params : dl_var:('typ -> 'var -> dl) -> ndim:int -> (('typ,'value,'var,'constr,'func) model as 'model) -> dl)
      ~(dl_var : nb_env_vars:int -> 'typ -> 'var -> dl)
      ~(xp_model : 'model html_xp)
      ~(xp_typ : 'typ html_xp) =
  fun
    ~(nb_env_vars : int)
    ?(ndim = 0) (* to be customized for sub-models *)
    (m : 'model) -> (* QUICK *)
  let size = size_model_ast m in
  let t = typ m in    
  let nb = nb_model_ast t size in
  if not (nb > 0.) then ( (* as [m] has this size, the nb of AST of this size must not be zero *)
    Printf.printf "Failed assertion in Model.dl: size=%d\ttyp=" size;
    pp xp_typ t;
    print_string "\tmodel="; pp_endline xp_model m;
    assert false);
  Mdl.Code.universal_int_star size (* encoding model AST size *)
  +. Mdl.log2 nb (* encoding choice of model AST for that size *)
  +. dl_model_params
       ~dl_var:(dl_var ~nb_env_vars)
       ~ndim
       m
       
(* reading *)

type ('typ,'value,'constr,'var,'func) read =
  { env : ('value,'constr) data;
    bindings : ('var,'typ,'value) Expr.bindings;
    mutable lazy_index : ('typ,'value,'var,'func) Expr.Index.t option; (* not using Lazy.t because breaks comparisons and hash *)
    data : ('value,'constr) data;
    dl_rank : dl;
    dl : dl } (* including rank *)

let force_index
      ~(make_index : ('var,'typ,'value) Expr.bindings -> ('typ,'value,'var,'func) Expr.Index.t)
      (read : ('typ,'value,'constr,'var,'func) read)
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

type ('input,'var,'typ,'value,'constr) parse_bests = ('var,'typ,'value) Expr.bindings -> 'input -> (('value,'constr) data * dl) list result
        
let parse_bests
      ~(max_nb_parse : int)
      ~(parseur : ?xis:(('var * int) list) -> ('typ,'value,'var,'constr,'func) model -> ('var,'typ,'value) Expr.bindings -> ('input,'var,'typ,'value,'constr) parseur)
      ~(dl_data : ('value,'constr) data -> dl)

      ?(xis = [])
      (m : ('typ,'value,'var,'constr,'func) model)
    : ('input,'var,'typ,'value,'constr) parse_bests =
  fun bindings input ->
  Common.prof "Model.parse_bests" (fun () ->
  let parses =
    let* data, _ = parseur m ~xis bindings input in
    let dl = (* QUICK *)
      dl_round (dl_data data) in
      (* rounding before sorting to absorb float error accumulation *)
    Myseq.return (data, dl) in
  let l_parses =
    Common.prof "Model.sorted_parseur/first_parses" (fun () ->
        parses
        |> Myseq.slice ~offset:0 ~limit:max_nb_parse
        |> Myseq.to_list) in
  (*        |> Myseq.to_list_timeout ~timeout:1) in *) (* TODO: find a way to bound search for parses, can explode, but 1s is too much and too rigid *)
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
      ~(parse_bests : ?xis:(('var * int) list) -> ('typ,'value,'var,'constr,'func) model -> ('input,'var,'typ,'value,'constr) parse_bests)

      ~(env : ('value,'constr) data)
      ~(bindings : ('var,'typ,'value) Expr.bindings)
      (m : ('typ,'value,'var,'constr,'func) model)
      (v : 'value)
    : ('typ,'value,'constr,'var,'func) read Myseq.t =
  Myseq.prof "Model.read" (
  let t = typ m in
  let input = input_of_value t v in
  let* best_parses = Myseq.from_result (parse_bests m bindings input) in
  let* rank, (data, dl) = Myseq.with_position (Myseq.from_list best_parses) in
  let dl_rank = dl_parse_rank rank in
  let dl = dl +. dl_rank in (* to penalize later parses, in case of equivalent parses *)
  Myseq.return { env; bindings; lazy_index=None; data; dl_rank; dl })


(* writing *)

exception Generate_failure
  
let write
      ~(generator : ('typ,'value,'var,'constr,'func) model -> ('var,'typ,'value) Expr.bindings -> ('info,'var,'typ,'value,'constr) generator)
      ~(dl_data : ('value,'constr) data -> dl)
      
      ~(bindings : ('var,'typ,'value) Expr.bindings)
      (m : ('typ,'value,'var,'constr,'func) model)
      (info : 'info)
    : (('value,'constr) data * dl) Myseq.t =
  Myseq.prof "Model.write" (
  let* data, _ = generator m bindings info in
  let dl = dl_data data in (* encoding of what is not specified by the evaluated model *)
  Myseq.return (data, dl))

  
(* paths and model refinement *)
  
let refine (* replace submodel of [m] at [p] by [r] *) 
    : ('var,'constr) path -> ('typ,'value,'var,'constr,'func) model -> ('typ,'value,'var,'constr,'func) model -> ('typ,'value,'var,'constr,'func) model =
  let rec aux p r m =
    match p, m with
    | Alias (x,p0) :: p1, _ ->
       aux (List.rev_append p0 p1) r m
    | _, Def (x,m1) ->
       let new_m1 = aux p r m1 in
       Def (x,new_m1)
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
    | _, Loop (xl,m1) ->
       let new_m1 = aux p r m1 in
       Loop (xl,new_m1)
    | Head :: p1, Cons (xl,m0,m1) ->
       let new_m0 = aux p1 r m0 in
       Cons (xl,new_m0,m1)
    | Tail :: p1, Cons (xl,m0,m1) ->
       let new_m1 = aux p1 r m1 in
       Cons (xl,m0,new_m1)
    | [], _ -> r
    | _ -> assert false
  in
  aux
