
open Madil_common
open Kind
open Data

type ('var,'func) cond_model =
  | Undet of float (* undetermined condition, probability for left choice *)
  | True (* always true condition *)
  | False (* always false condition *)
  | BoolExpr of ('var,'func) Expr.expr (* computed condition *)
 
type ('var,'constr,'func) model =
  | Def of 'var * ('var,'constr,'func) model (* a var is an id for the value at this sub-model *)
  | Pat of 'constr * ('var,'constr,'func) model array (* constr type may be different from data constr *)
  | Fail (* like an empty alternative *)
  | Alt of 'var (* condition var *) * ('var,'func) cond_model * ('var,'constr,'func) model * ('var,'constr,'func) model
  | Seq of int * ('var,'constr,'func) model list
  | Cst of ('var,'constr,'func) model
  | Expr of ('var,'func) Expr.expr

type 'constr path =
  | This
  | Field of 'constr * int * 'constr path
  | Branch of bool * 'constr path
  | Item of int * 'constr path

type 'constr ctx = 'constr path -> 'constr path
let ctx0 : _ ctx = (fun p -> p)

let make_def (x : 'var) (m1 : ('var,'constr,'func) model) : ('var,'constr,'func) model =
  Def (x,m1)
let make_pat (c : 'constr) (args : ('var,'constr,'func) model array) : ('var,'constr,'func) model =
  Pat (c,args)

let xp_model
      ~(xp_var : 'var html_xp)
      ~(xp_pat : 'constr -> unit html_xp array -> unit html_xp)
      ~(xp_func : 'func html_xp)
    : ('var,'constr,'func) model html_xp =
  let rec aux ~prio_ctx ~html print m =
    match m with
    | Def (x,m1) ->
       if html then print#string "<span class=\"model-def\">";
       xp_var ~html print x; print#string ":"; aux ~prio_ctx ~html print m1;
       if html then print#string "</span>"
    | Pat (c,args) ->
       let xp_args =
         Array.map
           (fun arg -> (fun ~html print () -> aux ~prio_ctx:0 ~html print arg))
           args in
       xp_pat c xp_args ~html print ()

    | Fail -> print#string "fail"
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

    | Seq (n,lm1) ->
       Xprint.bracket ("〈" ^ string_of_int n ^ ": ", "〉")
         (Xprint.sep_list ", " (aux ~prio_ctx:2 ~html))
         print lm1
    | Cst m1 ->
       Xprint.bracket ("〈", " = 〉") (aux ~prio_ctx:2 ~html)
         print m1
    | Expr e ->
       if html then print#string "<span class=\"model-expr\">";
       Expr.xp_expr ~xp_var ~xp_func ~html print e;
       if html then print#string "</span>"
  and aux_cond ~html print = function
    | Undet prob ->
       aux_prob ~html print prob
    | True ->
       print#string "true"
    | False ->
       print#string "false"
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
    method virtual constr_args : 't -> 'constr -> 't kind array
    method virtual default_and_other_pats : 't -> 'constr option * ('constr * 't kind array) list
    method virtual funcs : 't kind -> ('func * 't kind array) list (* None when expressions not allowed for this kind *)
    method virtual expr_opt : 't kind -> 't kind option
    method virtual alt_opt : 't kind -> bool
  end

(*
let make_asd
      ~(all_constrs : ('t (* for each type *)
                      * 'constr option (* is there a default constr? *)
                      * ('constr * 't kind array) list (* other constrs and their arg kind *)
                     ) list)
      ~(all_funcs : ('t kind (* for each kind *)
                     * 't kind option (* can it be an expr? *)
                     * ('func * 't kind array) list (* funcs resulting in this kind, and their arg kind *)
                    ) list) : ('t,'constr,'func) asd =
  let map_constr =
    List.fold_left
      (fun m (t, default_constr_opt, other_constr_args) ->
        Mymap.add t (default_constr_opt, other_constr_args) m)
      Mymap.empty all_constrs in
  let map_expr, map_funcs =
    List.fold_left
      (fun (me,mf) (k, expr_opt, l_f_args) ->
        (match expr_opt with None -> me | Some k1 -> Mymap.add k k1 me),
        Mymap.add k l_f_args mf)
      (Mymap.empty, Mymap.empty) all_funcs in
  object
    method default_and_other_pats t =
      match Mymap.find_opt t map_constr with
      | Some default_others -> default_others
      | None -> None, []
    method constr_args t c =
      match Mymap.find_opt t map_constr with
      | Some (default,others) ->
         if default = Some c then [||]
         else
           (match List.assoc_opt c others with
            | Some args -> args
            | None -> failwith "Model.asd#constr_args: unexpected constr for type")
      | None -> failwith "Model.asd#constr_args: unexpected type"
    method expr_opt k =
      Mymap.find_opt k map_expr
    method funcs k =
      match Mymap.find_opt k map_funcs with
      | Some funcs -> funcs
      | None -> []
  end
 *)
        
(* model evaluation *)

let binding_vars
      (m0 : ('var,'constr,'func) model)
    : 'var Expr.binding_vars =
  let rec aux m acc =
    match m with
    | Def (x,m1) ->
       let acc = aux m1 acc in
       Bintree.add x acc
    | Pat (c,args) ->
       Array.fold_right aux args acc
    | Fail -> acc
    | Alt (xc,cond,m1,m2) ->
       let acc = aux m1 acc in
       let acc = aux m2 acc in
       Bintree.add xc acc
    | Seq (n,lm1) ->
       List.fold_right aux lm1 acc
    | Cst m1 -> raise TODO
    | Expr e -> acc
  in
  aux m0 Bintree.empty

  
let get_bindings  (* QUICK *)
      ~(value_of_bool : bool -> 'value)
      (m0 : ('var,'constr,'func) model)
      (d0 : ('value,'dconstr) data)
    : ('var,'value) Expr.bindings =
  let rec aux m d acc =
    match m, d with
    | Def (x,m1), D (v, _) ->
       Mymap.add x v acc
    | Pat (c,args), D (_v, DPat (dc, dargs)) ->
       let n = Array.length args in
       assert (Array.length dargs = n);
       let ref_acc = ref acc in (* missing Array.fold_right2 *)
       for i = 0 to n - 1 do
         let acc = aux args.(i) dargs.(i) !ref_acc in
         ref_acc := acc
       done;
       !ref_acc
    | Fail, _ -> assert false (* because parsing and generation must have failed here *)
    | Alt (xc,c,m1,m2), D (_v, DAlt (b,d12)) ->
       let acc = aux (if b then m1 else m2) d12 acc in
       Mymap.add xc (value_of_bool b) acc
    | Seq (n,lm), D (_v, DSeq (dn,ld)) ->
       assert (n = dn);
       List.fold_right2 aux lm ld acc
    | Cst _, _ -> raise TODO
    | Expr _, _ -> acc (* expressions only in task output but TODO in general expression values should be accessible *)
    | _ -> assert false
  in
  aux m0 d0 Expr.bindings0

let eval (* QUICK *)
      ~asd
      ~eval_unbound_var ~eval_func ~eval_arg (* TODO: replace par eval_expr ? *)
      ~(model_of_value : 't kind -> 'value -> ('var,'constr,'func) model result)
      ~(bool_of_value : 'value -> bool result)
      (k : 't kind)
      (m : ('var,'constr,'func) model)
      (bindings : ('var,'value) Expr.bindings)
    : ('var,'constr,'func) model result =
  (* INV: eval must ensure that the resulting model has data that is compatible with the given model, so that encoding is well-defined. E.g. no Alt simplification when condition evaluates to True/False. *)
  let eval_expr = Expr.eval ~eval_unbound_var ~eval_func ~eval_arg in
  let rec aux k m =
    match k, m with
    | _, Def (x,m1) ->
       let| m1' = aux k m1 in
       Result.Ok (Def (x,m1'))
    | KVal t, Pat (c,args) ->
       let k_args = asd#constr_args t c in
       let| l_args' =
         list_map_result
           (fun (ki,argi) -> aux ki argi)
           (Array.to_list
              (Array.mapi
                 (fun i argi ->
                   let ki = try k_args.(i) with _ -> assert false in
                   ki, argi)
                 args)) in
       let args' = Array.of_list l_args' in
       Result.Ok (Pat (c,args'))
    | _, Fail ->
       Result.Ok Fail
    | _, Alt (xc,c,m1,m2) ->
       let| c' = aux_cond c in
       let m1' = match aux k m1 with Result.Ok m1' -> m1' | Result.Error _ -> Fail in
       let m2' = match aux k m2 with Result.Ok m2' -> m2' | Result.Error _ -> Fail in
       Result.Ok (Alt (xc,c',m1',m2'))
    | KSeq k1, Seq (n,lm1) ->
       let| lm1' = list_map_result (aux k1) lm1 in
       Result.Ok (Seq (n,lm1'))
    | _, Cst m1 -> raise TODO
    | _, Expr e ->
       let| v = eval_expr e bindings in
       model_of_value k v
    | _ -> assert false
  and aux_cond = function
    | Undet prob -> Result.Ok (Undet prob)
    | True -> Result.Ok True
    | False -> Result.Ok False
    | BoolExpr e ->
       let| v = eval_expr e bindings in
       let| b = bool_of_value v in
       if b
       then Result.Ok True
       else Result.Ok False
  in
  aux k m
  
(* model-based generation *)

type ('info,'value,'dconstr) generator = 'info -> ('value,'dconstr) data

let generator
      ~(generator_pat: 'constr -> (('info,'value,'dconstr) generator as 'gen) array -> 'gen)
      ~(dseq_value : ('value,'dconstr) data list -> 'value)
    : ('var,'constr,'func) model -> 'gen =
  let rec gen = function
    | Def (x,m1) ->
       gen m1
    | Pat (c,args) ->
       let gen_args = Array.map gen args in
       generator_pat c gen_args
    | Fail ->
       (fun info -> raise Not_found)
    | Alt (xc,c,m1,m2) -> (* TODO: make stochastic *)
       let b, m12 =
         match c with
         | Undet prob ->
            (match m1, m2 with
             | Fail, Fail -> true, Fail
             | Fail, _ -> false, m2
             | _, Fail -> true, m1
             | _ -> if prob >= 0.5 then true, m1 else false, m2)
         | True -> true, m1
         | False -> false, m2
         | BoolExpr _ -> assert false in
       let gen_m12 = gen m12 in
       (fun info ->
         let d12 = gen_m12 info in
         let v = value d12 in
         D (v, DAlt (b, d12)))
    | Seq (n,lm1) ->
       let gen_lm1 = List.map gen lm1 in
       (fun info ->
         let ld = List.map (fun gen_mi -> gen_mi info) gen_lm1 in
         let v = dseq_value ld in
         D (v, DSeq (n, ld)))
    | Cst m1 -> raise TODO
    | Expr e -> assert false
  in
  gen
                                        
(* model-based parsing *)

type ('input,'value,'dconstr) parseur = 'input -> (('value,'dconstr) data * 'input) Myseq.t

let parseur
      ~(parseur_pat : 'constr -> 'parse array -> 'parse)
      ~(dseq_value : ('value,'dconstr) data list -> 'value)
    : ('var,'constr,'func) model -> (('input,'value,'dconstr) parseur as 'parse) =
  let rec parse = function
    | Def (x,m1) ->
       parse m1
    | Pat (c,args) ->
       let parse_args = Array.map parse args in
       parseur_pat c parse_args
    | Fail ->
       (fun input -> Myseq.empty)
    | Alt (xc,c,m1,m2) -> (* if-then-else *)
       let parse_m1 = parse m1 in
       let parse_m2 = parse m2 in
       (fun input ->
         let seq1 =
           let* d1, input = parse_m1 input in
           Myseq.return (D (value d1, DAlt (true,d1)), input) in
         let seq2 =
           let* d2, input = parse_m2 input in
           Myseq.return (D (value d2, DAlt (false,d2)), input) in
         match c with
         | Undet prob ->
            if Myseq.is_empty seq1
            then seq2
            else seq1 (* for exclusive alternatives, anticipating condition *)
         | True -> seq1
         | False -> seq2
         | BoolExpr _ -> (fun () -> assert false))
    | Seq (n,lm1) ->
       let parse_lm1 = List.map parse lm1 in
       (fun input ->
         let* ld, input = Myseq.product_dependent_fair parse_lm1 input in
         let v = dseq_value ld in
         Myseq.return (D (v, (DSeq (n, ld))), input))
    | Cst m1 -> raise TODO
    | Expr e -> assert false
  in
  parse

(* model-based encoding of data *)

let encode_data
      ~(xp_model : 'model html_xp)
      ~(xp_data : 'data html_xp)
      ~(encoding_pat : 'constr -> 'dconstr -> 'encoding array -> 'encoding)
      ~(encoding_expr : 'value -> 'encoding)
      ~(encoding_alt : dl (* DL of branch choice *) -> 'encoding -> 'encoding (* with added DL choice *))
      ~(encoding_seq : 'encoding list -> 'encoding)
      ~(dl_of_encoding : 'encoding -> dl)
      (m : ('var,'constr,'func) model as 'model) (d : ('value,'dconstr) data as 'data) : dl =
  let rec aux m d =
    match m, d with
    | Def (x,m1), _ ->
       aux m1 d
    | Pat (c,args), D (_, DPat (dc, dargs)) ->
       let encs = Array.map2 aux args dargs in
       encoding_pat c dc encs
    | Fail, _ -> assert false
    | Alt (xc,c,m1,m2), D (_, DAlt (b,d12)) -> (* choice determined by model *)
       let dl_choice =
         match c with
         | Undet prob -> Mdl.Code.usage (if b then prob else 1. -. prob)
         | True | False | BoolExpr _ -> 0. in
       let enc12 = aux (if b then m1 else m2) d12 in
       encoding_alt dl_choice enc12
    | Seq (n,lm1), D (_, DSeq (dn,ld1)) ->
       assert (n = dn);
       let encs = List.map2 aux lm1 ld1 in
       (* no need to encode 'dn', equal 'n' in model *)
       encoding_seq encs
    | Cst m1, _ -> raise TODO
    | Expr e, D (v, _) ->
       encoding_expr v
    | _ ->
       print_endline "ERROR in encode_data: (model, data)";
       pp xp_model m; print_newline ();
       pp xp_data d; print_newline ();
       assert false
  in
  Common.prof "Model.encode_data" (fun () ->
  let enc = aux m d in
  dl_of_encoding enc)

let dl_parse_rank (rank : int) : dl =
  (* penalty DL for parse rank, starting at 0 *)
  Mdl.Code.universal_int_star rank -. 1.
  
(* model encoding *)

let size_model_ast (* for DL computing, QUICK *)
      ~(asd : ('t,'constr,'func) asd)
    (m : ('var,'constr,'func) model) : int =
  let rec aux = function
    | Def (x,m1) -> aux m1 (* definitions are ignore in DL, assumed determined by model AST *)
    | Pat (c,args) ->
       Array.fold_left
         (fun res arg -> res + aux arg)
         (if asd#is_default_constr c && args = [||] then 0 else 1)
         args
    | Fail -> 1
    | Alt (xc,c,m1,m2) -> 2 + aux_cond c + aux m1 + aux m2
    | Seq (n,lm1) -> List.fold_left (fun res m1 -> res + aux m1) 1 lm1
    | Cst m1 -> 1 + aux m1
    | Expr e -> Expr.size_expr_ast e
  and aux_cond = function
    | Undet _ -> 0
    | True | False -> assert false
    | BoolExpr e -> Expr.size_expr_ast e
  in
  aux m

let nb_model_ast (* for DL computing, must be consistent with size_model_ast *)
      ~(asd : ('t,'constr,'func) asd) =
  let tab : ('t kind * int, float) Hashtbl.t = Hashtbl.create 1013 in
  let rec aux (k : 't kind) (size : int) : float =
    match Hashtbl.find_opt tab (k,size) with
    | Some nb -> nb
    | None ->
       let nb = (* counting possible expressions *)
         match asd#expr_opt k with
         | None -> 0.
         | Some k1 -> Expr.nb_expr_ast ~funcs:asd#funcs k1 size in
       let nb = (* counting possible alternatives *)
         if size >= 2 && asd#alt_opt k
         then nb +. sum_conv [aux_cond; aux k; aux k] (size-2)
                             (* split between condition, left model, right model *)
         else nb in
       match k with
       | KBool -> nb (* no Boolean model construct *)
       | KVal t -> (* counting Pat (c,args) *)
          let default_constr_opt, other_constr_args = asd#default_and_other_pats t in
          let nb =
            if size = 0 && default_constr_opt <> None
            then nb +. 1.
            else nb in
          let nb =
            List.fold_left
              (fun nb (c,k_args) ->
                if k_args = [||] (* leaf node *)
                then if size = 1 then nb +. 1. else nb
                else
                  if size >= 1
                  then nb +. sum_conv (Array.to_list (Array.map aux k_args)) (size-1)
                  else nb)
              nb other_constr_args in
          Hashtbl.add tab (k,size) nb;
          nb
       | KSeq k1 -> (* counting Seq (n,lm1) *)
          let aux_k1 = aux k1 in
          let size1 = size-1 in
          Common.fold_for
            (fun n nb ->
              nb +. sum_conv (List.init n (fun _ -> aux_k1)) size1)
            1 (max 9 size1)
            nb
  and aux_cond (size : int) : float =
    if size = 0
    then 1. (* Undet *)
    else Expr.nb_expr_ast ~funcs:asd#funcs KBool size (* BoolExpr *)
  in
  fun (k : 't kind) (size : int) (* AST size *) -> (* float to handle large numbers *)
  Common.prof "Model.nb_model_ast" (fun () ->
  aux k size)

let dl_model_params
      ~(dl_constr_params : 'constr -> dl)
      ~(dl_func_params : 'func -> dl)
      ~(dl_var : 'var -> dl)
    : ('var,'constr,'func) model -> dl =
  let dl_expr_params =
    Expr.dl_expr_params ~dl_func_params ~dl_var in
  let rec aux = function
    | Def (x,m1) -> aux m1 (* variable names do not matter, only variable choice in expr matters *)
    | Pat (c,args) ->
       let dl_args_params =
         Array.map aux args
         |> Array.fold_left (+.) 0. in
       dl_constr_params c +. dl_args_params
    | Fail -> 0.
    | Alt (xc,c,m1,m2) ->
       aux_cond c +. aux m1 +. aux m2
    | Seq (n,lm1) ->
       List.map aux lm1
       |> List.fold_left (+.) 0.
    | Cst m1 -> raise TODO
    | Expr e -> dl_expr_params e
  and aux_cond = function
    | Undet prob -> Mdl.Code.uniform 10 (* bounding float precision, TODO: use better distrib *)
    | True | False -> 0.
    | BoolExpr e -> dl_expr_params e
  in
  aux

let dl
      ~(asd : ('t,'constr,'func) asd)
      ~(dl_constr_params : 'constr -> dl)
      ~(dl_func_params : 'func -> dl)
      ~(dl_var : nb_env_vars:int -> 'var -> dl) =
  let size_model_ast = size_model_ast ~asd in
  let nb_model_ast = nb_model_ast ~asd in
  let dl_model_params = dl_model_params ~dl_constr_params ~dl_func_params in
  fun
    ~(nb_env_vars : int)
    (k : 't kind) (m : ('var,'constr,'func) model) ->
  Common.prof "Model.dl" (fun () ->
  let size = size_model_ast m in
  let nb = nb_model_ast k size in
  Mdl.Code.universal_int_star size (* encoding model AST size *)
  +. Mdl.log2 nb (* encoding choice of model AST for that size *)
  +. dl_model_params
       ~dl_var:(dl_var ~nb_env_vars)
       m)

       
(* reading *)

type ('value,'dconstr,'var,'func) read =
  { env : ('value,'dconstr) data;
    bindings : ('var,'value) Expr.bindings;
    index : ('value,'var,'func) Expr.Index.t;
    data : ('value,'dconstr) data;
    dl : dl }

let limit_dl ~(max_parse_dl_factor : float) (f_dl : 'a -> dl) (l : 'a list) : 'a list =
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
      ~(eval : 't kind -> ('var,'constr,'func) model -> ('var,'value) Expr.bindings -> ('var,'constr,'func) model result)
      ~(parseur : ('var,'constr,'func) model -> ('input,'value,'dconstr) parseur)
      ~(dl_data : ('var,'constr,'func) model -> ('value,'dconstr) data -> dl)

      (k : 't kind)
      (m0 : ('var,'constr,'func) model)
    : ('input,'value,'dconstr,'var) eval_parse_bests =
  let dl_data_m0 = dl_data m0 in
  fun bindings input ->
  Common.prof "Model.eval_parse_bests" (fun () ->
  let| m = eval k m0 bindings in (* resolving expressions *)
  let parses =
    let* data, _ = parseur m input in
    let dl = (* QUICK *)
      dl_round (dl_data_m0 data) in
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
      ~(eval : 't kind -> ('var,'constr,'func) model -> ('var,'value) Expr.bindings -> ('var,'constr,'func) model result)
      ~(eval_parse_bests : 't kind -> ('var,'constr,'func) model -> ('input,'value,'dconstr,'var) eval_parse_bests)
      ~(make_index : ('var,'value) Expr.bindings -> ('value,'var,'func) Expr.Index.t)

      ~(dl_assuming_contents_known : bool)
      ~(env : ('value,'dconstr) data)
      ~(bindings : ('var,'value) Expr.bindings)
      (k : 't kind)
      (m0 : ('var,'constr,'func) model)
      (v : 'value)
    : ('value,'dconstr,'var,'func) read list result =
  Common.prof "Model.read" (fun () ->
  let input = input_of_value v in
  let| best_parses = eval_parse_bests k m0 bindings input in
  let index = lazy (make_index bindings) in
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
             index=Lazy.force index;
             data;
             dl }) in
  Result.Ok reads)


(* writing *)

exception Generate_failure
  
let write
      ~(eval : 't kind -> ('var,'constr,'func) model -> ('var,'value) Expr.bindings -> ('var,'constr,'func) model result)
      ~(generator : ('var,'constr,'func) model -> ('info,'value,'dconstr) generator)
      
      ~(bindings : ('var,'value) Expr.bindings)
      (k : 't kind)
      (m0 : ('var,'constr,'func) model)
      (info : 'info)
    : (('value,'dconstr) data * 'value) result =
  Common.prof "Model.write" (fun () ->
  let| m = eval k m0 bindings in
  let| d =
    try Result.Ok (generator m info)
    with Not_found -> Result.Error Generate_failure in
  let v = value d in
  Result.Ok (d, v))


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
  
let path_kind
      ~(asd : ('t,'constr,'func) asd)
    : 't kind -> 'constr path -> 't kind =
  let rec aux k p =
    match k, p with
    | _, This -> k
    | KVal t, Field (c,i,p1) ->
       let kind_args = asd#constr_args t c in
       let k1 = try kind_args.(i) with _ -> assert false in
       aux k1 p1
    | _, Branch (b,p1) -> aux k p1
    | KSeq k1, Item (i,p1) -> aux k1 p1
    | _ -> assert false
  in
  aux
  
let refine (* replace submodel of [m] at [p] by [r] *) 
    : 'constr path -> ('var,'constr,'func) model -> ('var,'constr,'func) model -> ('var,'constr,'func) model =
  let rec aux p r m =
    match p, m with
    | _, Def (x,m1) ->
       let new_m1 = aux p r m1 in
       Def (x,new_m1)
    | This, _ -> r
    | Field (c,i,p1), Pat (c',args) when c = c' && i < Array.length args ->
       let new_args = Array.copy args in
       new_args.(i) <- aux p1 r args.(i);
       Pat (c, new_args)
    | Branch (true,p1), Alt (xc,c,m1,m2) ->
       let new_m1 = aux p1 r m1 in
       Alt (xc,c,new_m1,m2)
    | Branch (false,p1), Alt (xc,c,m1,m2) ->
       let new_m2 = aux p1 r m2 in
       Alt (xc,c,m1,new_m2)
    | Item (i,p1), Seq (n,lm1) when i < n ->
       let new_lm1 = list_update (fun mi -> aux p1 r mi) i lm1 in
       Seq (n,new_lm1)
    | _ -> assert false
  in
  aux
