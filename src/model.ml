
open Madil_common
open Kind
open Data

type ('var,'func) cond_model =
  | Undet of float (* undetermined condition, probability for left choice *)
  | True (* always true condition - only in evaluated model *)
  | False (* always false condition - only in evaluated model *)
  | BoolExpr of ('var,'func) Expr.expr (* computed condition - not in evaluated model *)
 
type ('t,'var,'constr,'func) model =
  | Def of 'var * ('t,'var,'constr,'func) model (* a var is an id for the value at this sub-model - not in evaluated model *)
  | Pat of 't * 'constr * ('t,'var,'constr,'func) model array (* constr type may be different from data constr *)
  | Fail (* like an empty alternative - only in evaluated model *)
  | Alt of 'var (* condition var *) * ('var,'func) cond_model * ('t,'var,'constr,'func) model * ('t,'var,'constr,'func) model
  | Seq of int * 't kind (* elt kind *) * ('t,'var,'constr,'func) model list
  | Cst of ('t,'var,'constr,'func) model
  | Expr of 't kind * ('var,'func) Expr.expr (* not in evaluated model *)

type 'constr path =
  | This
  | Field of 'constr * int * 'constr path
  | Branch of bool * 'constr path
  | Item of int * 'constr path

type 'constr ctx = 'constr path -> 'constr path
let ctx0 : _ ctx = (fun p -> p)

let make_def (x : 'var) (m1 : ('t,'var,'constr,'func) model) : ('t,'var,'constr,'func) model =
  Def (x,m1)
let make_pat (t : 't) (c : 'constr) (args : ('t,'var,'constr,'func) model array) : ('t,'var,'constr,'func) model =
  Pat (t,c,args)

let rec kind : ('t,'var,'constr,'func) model -> 't kind = function
  | Def (x,m1) -> kind m1
  | Pat (t,c,args) -> KPat t
  | Fail -> assert false
  | Alt (xc,c,m1,m2) -> kind m1
  | Seq (n,k1,lm1) -> KSeq k1
  | Cst m1 -> KSeq (kind m1)
  | Expr (k,e) -> k
  
(* printing *)
  
let xp_model
      ~(xp_var : 'var html_xp)
      ~(xp_pat : 'constr -> unit html_xp array -> unit html_xp)
      ~(xp_func : 'func html_xp)
    : ('t,'var,'constr,'func) model html_xp =
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

    | Seq (n,_k1,lm1) ->
       Xprint.bracket ("〈" ^ string_of_int n ^ ": ", "〉")
         (Xprint.sep_list ", " (aux ~prio_ctx:2 ~html))
         print lm1
    | Cst m1 ->
       Xprint.bracket ("〈", " = 〉") (aux ~prio_ctx:2 ~html)
         print m1
    | Expr (_k,e) ->
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

class virtual ['t,'constr,'func] asd =
  object (self)
    method virtual is_default_constr : 'constr -> bool
    method virtual default_and_other_pats : 't -> 'constr option * ('constr * 't kind array) list
    method virtual funcs : 't kind -> ('func * 't kind array) list (* None when expressions not allowed for this kind *)
    method virtual expr_opt : 't kind -> 't kind option
    method virtual alt_opt : 't kind -> bool
  end
        
(* model evaluation *)

let binding_vars
      (m0 : ('t,'var,'constr,'func) model)
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
    | Seq (n,k1,lm1) ->
       List.fold_right aux lm1 acc
    | Cst m1 -> raise TODO
    | Expr (k,e) -> acc
  in
  aux m0 Bintree.empty

  
let get_bindings  (* QUICK *)
      ~(value_of_bool : bool -> 'value)
      (m0 : ('t,'var,'constr,'func) model)
      (d0 : ('value,'dconstr) data)
    : ('var,'value) Expr.bindings =
  let rec aux m d acc =
    match m, d with
    | Def (x,m1), D (v,_) ->
       let acc = aux m1 d acc in
       Mymap.add x v acc
    | Pat (t,c,args), D (_v, DPat (dc, dargs)) ->
       let n = Array.length args in
       assert (Array.length dargs = n);
       let ref_acc = ref acc in (* missing Array.fold_right2 *)
       for i = 0 to n - 1 do
         let acc = aux args.(i) dargs.(i) !ref_acc in
         ref_acc := acc
       done;
       !ref_acc
    | Fail, _ -> assert false (* because Fail only occurs in evaluated models *)
    | Alt (xc,c,m1,m2), D (_v, DAlt (_prob,b,d12)) ->
       let acc = aux (if b then m1 else m2) d12 acc in
       Mymap.add xc (value_of_bool b) acc
    | Seq (n,k1,lm1), D (_v, DSeq (dn,ld1)) ->
       assert (n = dn);
       List.fold_right2 aux lm1 ld1 acc
    | Cst _, _ -> raise TODO
    | Expr _, _ -> acc
    | _ -> assert false
  in
  aux m0 d0 Expr.bindings0

exception EmptyAlt
  
let eval (* from model to evaluated model: resolving expr, ignoring def *)
      ~asd
      ~(eval_expr : ('var,'func) Expr.expr -> ('var,'value) Expr.bindings -> 'value result)
      ~(model_of_value : 't kind -> 'value -> ('t,'var,'constr,'func) model result)
      ~(bool_of_value : 'value -> bool result)
      (m : ('t,'var,'constr,'func) model)
      (bindings : ('var,'value) Expr.bindings)
    : ('t,'var,'constr,'func) model result =
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
    | Seq (n,k1,lm1) ->
       let| lm1' = list_map_result aux lm1 in
       Result.Ok (Seq (n,k1,lm1'))
    | Cst m1 -> raise TODO
    | Expr (k,e) ->
       let| v = eval_expr e bindings in
       model_of_value k v
  and aux_cond = function
    | Undet prob -> Result.Ok (Undet prob)
    | True | False -> assert false
    | BoolExpr e ->
       let| v = eval_expr e bindings in
       let| b = bool_of_value v in
       Result.Ok (if b then True else False)
  in
  aux m
  
(* model-based generation *)

type ('info,'value,'dconstr) generator = 'info -> ('value,'dconstr) data Myseq.t

let generator (* on evaluated models: no expr, no def *)
      ~(generator_pat: 'constr -> (('info,'value,'dconstr) generator as 'gen) array -> 'gen)
      ~(dseq_value : ('value,'dconstr) data list -> 'value)
    : ('t,'var,'constr,'func) model -> 'gen =
  let rec gen = function
    | Def (x,m1) -> assert false
    | Pat (t,c,args) ->
       let gen_args = Array.map gen args in
       generator_pat c gen_args
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
    | Seq (n,k1,lm1) ->
       let gen_lm1 = List.map gen lm1 in
       (fun info ->
         let* ld = Myseq.product_fair (List.map (fun gen_mi -> gen_mi info) gen_lm1) in
         let v = dseq_value ld in
         Myseq.return (D (v, DSeq (n, ld))))
    | Cst m1 -> raise TODO
    | Expr (k,e) -> assert false
  in
  gen
                                        
(* model-based parsing *)

type ('input,'value,'dconstr) parseur = 'input -> (('value,'dconstr) data * 'input) Myseq.t

let parseur (* on evaluated models: no expr, no def *)
      ~(parseur_pat : 'constr -> 'parse array -> 'parse)
      ~(dseq_value : ('value,'dconstr) data list -> 'value)
    : ('t,'var,'constr,'func) model -> (('input,'value,'dconstr) parseur as 'parse) =
  let rec parse = function
    | Def (x,m1) -> assert false
    | Pat (t,c,args) ->
       let parse_args = Array.map parse args in
       parseur_pat c parse_args
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
    | Seq (n,k1,lm1) ->
       let parse_lm1 = List.map parse lm1 in
       (fun input ->
         let* ld, input = Myseq.product_dependent_fair parse_lm1 input in
         let v = dseq_value ld in
         Myseq.return (D (v, (DSeq (n, ld))), input))
    | Cst m1 -> raise TODO
    | Expr (k,e) -> assert false
  in
  parse

(* model-based encoding of data *)

let dl_data
      ~(encoding_dpat : 'dconstr -> 'encoding array -> 'encoding)
      ~(encoding_alt : dl (* DL of branch choice *) -> 'encoding -> 'encoding (* with added DL choice *))
      ~(encoding_seq : 'encoding list -> 'encoding)
      ~(dl_of_encoding : 'encoding -> dl)
    : (('value,'dconstr) data as 'data) -> dl =
  let rec aux (D (v, dm)) =
    match dm with
    | DPat (dc, dargs) ->
       let encs = Array.map aux dargs in
       encoding_dpat dc encs
    | DAlt (prob,b,d12) ->
       let dl_choice = Mdl.Code.usage prob in
       let enc12 = aux d12 in
       encoding_alt dl_choice enc12
    | DSeq (dn,ld1) ->
       let encs = List.map aux ld1 in
       encoding_seq encs
  in
  fun d -> Common.prof "Model.dl_data" (fun () ->
  let enc = aux d in
  dl_of_encoding enc)

let dl_parse_rank (rank : int) : dl =
  (* penalty DL for parse rank, starting at 0 *)
  Mdl.Code.universal_int_star rank -. 1.
  
(* model encoding *)

let size_alt = 3
  
let size_model_ast (* for DL computing, QUICK *)
      ~(asd : ('t,'constr,'func) asd)
    (m : ('t,'var,'constr,'func) model) : int =
  let rec aux = function
    | Def (x,m1) -> aux m1 (* definitions are ignore in DL, assumed determined by model AST *)
    | Pat (t,c,args) ->
       Array.fold_left
         (fun res arg -> res + aux arg)
         (if asd#is_default_constr c && args = [||] then 0 else 1)
         args
    | Fail -> assert false
    | Alt (xc,c,m1,m2) -> size_alt + aux_cond c + aux m1 + aux m2
    | Seq (n,k1,lm1) -> List.fold_left (fun res m1 -> res + aux m1) 1 lm1
    | Cst m1 -> 1 + aux m1
    | Expr (k,e) -> Expr.size_expr_ast e
  and aux_cond = function
    | Undet _ -> 0
    | True | False -> assert false
    | BoolExpr e -> Expr.size_expr_ast e
  in
  aux m

let nb_model_ast (* for DL computing, must be consistent with size_model_ast *)
      ~(asd : ('t,'constr,'func) asd)
      ~(nb_expr_ast : 't kind -> int -> float) =
  let tab : ('t kind * int, float) Hashtbl.t = Hashtbl.create 1013 in
  let reset () = Hashtbl.clear tab in
  let rec aux (k : 't kind) (size : int) : float (* float to handle large numbers *) =
    match Hashtbl.find_opt tab (k,size) with
    | Some nb -> nb
    | None -> (* QUICK *)
       let nb = (* counting possible expressions *)
         match asd#expr_opt k with
         | None -> 0.
         | Some k1 -> nb_expr_ast k1 size in
       let nb = (* counting possible alternatives *)
         if size >= size_alt && asd#alt_opt k
         then nb +. sum_conv [aux_cond; aux k; aux k] (size - size_alt)
                             (* split between condition, left model, right model *)
         else nb in
       let nb =
         match k with
         | KBool -> nb (* no Boolean model construct *)
         | KPat t -> (* counting Pat (c,args) *)
            let default_constr_opt, other_constr_args = asd#default_and_other_pats t in
            let nb =
              if size = 0 && default_constr_opt <> None
              then nb +. 1.
              else nb in
            List.fold_left
              (fun nb (c,k_args) ->
                if k_args = [||] (* leaf node *)
                then if size = 1 then nb +. 1. else nb
                else
                  if size >= 1
                  then nb +. sum_conv (Array.to_list (Array.map aux k_args)) (size-1)
                  else nb)
              nb other_constr_args
         | KSeq k1 -> (* counting Seq (n,lm1) *)
            let aux_k1 = aux k1 in
            let size1 = size-1 in
            Common.fold_for
              (fun n nb ->
                nb +. sum_conv (List.init n (fun _ -> aux_k1)) size1)
              1 (max 9 size1)
              nb in
       Hashtbl.add tab (k,size) nb;
       nb
  and aux_cond (size : int) : float =
    if size = 0
    then 1. (* Undet *)
    else nb_expr_ast KBool size (* BoolExpr *)
  in
  aux, reset

let dl_model_params
      ~(dl_constr_params : 'constr -> dl)
      ~(dl_func_params : 'func -> dl)
      ~(dl_var : 'var -> dl)
    : ('t,'var,'constr,'func) model -> dl =
  let dl_expr_params =
    Expr.dl_expr_params ~dl_func_params ~dl_var in
  let rec aux = function
    | Def (x,m1) -> aux m1 (* variable names do not matter, only variable choice in expr matters *)
    | Pat (t,c,args) ->
       let dl_args_params =
         Array.map aux args
         |> Array.fold_left (+.) 0. in
       dl_constr_params c +. dl_args_params
    | Fail -> assert false
    | Alt (xc,c,m1,m2) ->
       aux_cond c +. aux m1 +. aux m2
    | Seq (n,k1,lm1) ->
       List.map aux lm1
       |> List.fold_left (+.) 0.
    | Cst m1 -> raise TODO
    | Expr (k,e) -> dl_expr_params e
  and aux_cond = function
    | Undet prob -> Mdl.Code.uniform 10 (* bounding float precision, TODO: use better distrib *)
    | True | False -> assert false
    | BoolExpr e -> dl_expr_params e
  in
  aux

let dl
      ~(size_model_ast : ('t,'var,'constr,'func) model -> int)
      ~(nb_model_ast : 't kind -> int -> float)
      ~(dl_model_params : dl_var:('var -> dl) -> ('t,'var,'constr,'func) model -> dl)
      ~(dl_var : nb_env_vars:int -> 'var -> dl) =
  fun
    ~(nb_env_vars : int)
    (m : ('t,'var,'constr,'func) model) -> (* QUICK *)
  let size = size_model_ast m in
  let k = kind m in    
  let nb = nb_model_ast k size in
  assert (nb > 0.); (* as [m] has this size, the nb of AST of this size must not be zero *)
  Mdl.Code.universal_int_star size (* encoding model AST size *)
  +. Mdl.log2 nb (* encoding choice of model AST for that size *)
  +. dl_model_params
       ~dl_var:(dl_var ~nb_env_vars)
       m
       
(* reading *)

type ('value,'dconstr,'var,'func) read =
  { env : ('value,'dconstr) data;
    bindings : ('var,'value) Expr.bindings;
    lazy_index : ('value,'var,'func) Expr.Index.t Lazy.t;
    data : ('value,'dconstr) data;
    dl : dl }

let limit_dl ~(max_parse_dl_factor : float) (f_dl : 'a -> dl) (l : 'a list) : 'a list = (* QUICK *)
  match l with
  | [] -> []
  | x0::_ ->
     let dl0 = f_dl x0 in
     let min_dl = max_parse_dl_factor *. dl0 in
     List.filter (fun x -> f_dl x <= min_dl) l

exception Parse_failure

type ('input,'value,'dconstr,'var) eval_parse_bests = ('var,'value) Expr.bindings -> 'input -> (('value,'dconstr) data * dl) list result
        
let eval_parse_bests
      ~(max_nb_parse : int)
      ~(eval : ('t,'var,'constr,'func) model -> ('var,'value) Expr.bindings -> ('t,'var,'constr,'func) model result)
      ~(parseur : ('t,'var,'constr,'func) model -> ('input,'value,'dconstr) parseur)
      ~(dl_data : ('value,'dconstr) data -> dl)

      (m0 : ('t,'var,'constr,'func) model)
    : ('input,'value,'dconstr,'var) eval_parse_bests =
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


let read
      ~(max_parse_dl_factor : float)
      ~(max_nb_reads : int)
      ~(input_of_value : 'value -> 'input)
      ~(eval : ('t,'var,'constr,'func) model -> ('var,'value) Expr.bindings -> ('t,'var,'constr,'func) model result)
      ~(eval_parse_bests : ('t,'var,'constr,'func) model -> ('input,'value,'dconstr,'var) eval_parse_bests)

      ~(dl_assuming_contents_known : bool)
      ~(env : ('value,'dconstr) data)
      ~(bindings : ('var,'value) Expr.bindings)
      ~(lazy_index : ('value,'var,'func) Expr.Index.t Lazy.t)
      (m0 : ('t,'var,'constr,'func) model)
      (v : 'value)
    : ('value,'dconstr,'var,'func) read list result =
  Common.prof "Model.read" (fun () ->
  let input = input_of_value v in
  let| best_parses = eval_parse_bests m0 bindings input in
  let reads =
    best_parses
    |> (fun l -> Common.sub_list l 0 max_nb_reads)
    |> limit_dl ~max_parse_dl_factor (fun (_,dl) -> dl)
    |> List.mapi (fun rank (data,dl) ->
           let dl_rank = dl_parse_rank rank in
           let dl =
             if dl_assuming_contents_known
             then dl_rank
             else dl +. dl_rank in (* to penalize later parses, in case of equivalent parses *)
           { env;
             bindings;
             lazy_index;
             data;
             dl }) in
  Result.Ok reads)


(* writing *)

exception Generate_failure
  
let write
      ~(max_nb_writes : int)
      ~(eval : ('t,'var,'constr,'func) model -> ('var,'value) Expr.bindings -> ('t,'var,'constr,'func) model result)
      ~(generator : ('t,'var,'constr,'func) model -> ('info,'value,'dconstr) generator)
      
      ~(bindings : ('var,'value) Expr.bindings)
      (m0 : ('t,'var,'constr,'func) model)
      (info : 'info)
    : ('value,'dconstr) data list result =
  Common.prof "Model.write" (fun () ->
  let| m = eval m0 bindings in
  let ld, _ = Myseq.take max_nb_writes (generator m info) in
  if ld = []
  then Result.Error Generate_failure
  else Result.Ok ld)

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
    : 'constr path -> ('t,'var,'constr,'func) model -> ('t,'var,'constr,'func) model -> ('t,'var,'constr,'func) model =
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
    | Item (i,p1), Seq (n,k1,lm1) when i < n ->
       let new_lm1 = list_update (fun mi -> aux p1 r mi) i lm1 in
       Seq (n,k1,new_lm1)
    | _ -> assert false
  in
  aux
