
open Madil_common
open Data

type ('typ,'value,'var,'func) cond_model =
  | Undet of float (* undetermined condition, probability for left choice *)
  | BoolExpr of ('typ,'value,'var,'func) Expr.expr (* computed condition - not in evaluated model *)
 
type ('typ,'value,'var,'constr,'func) model =
  | Def of 'var * ('typ,'value,'var,'constr,'func) model (* a var is an id for the value at this sub-model *)
  | Any of 'typ
  | Pat of 'typ * 'constr * ('typ,'value,'var,'func) Expr.expr array * ('typ,'value,'var,'constr,'func) model array (* constr type may be different from data constr *)
  | Alt of 'var (* condition var *) * ('typ,'value,'var,'func) cond_model * ('typ,'value,'var,'constr,'func) model * ('typ,'value,'var,'constr,'func) model
  | Expr of ('typ,'value,'var,'func) Expr.expr
  | Derived of 'typ (* derived value, in general from sibling pattern args, like an implicit expression *)

type ('var,'constr) path = ('var,'constr) path_step list
and ('var,'constr) path_step =
  | Field of 'constr * int (* Pat field *)
  | Branch of bool (* Alt branch *)
  | Alias of 'var * ('var,'constr) path (* named path, reverse path *)

let p0 : ('var,'constr) path = [] (* the empty path = This *)
let ctx0 : ('var,'constr) path = [] (* a context is a reverse path *)

let make_def (x : 'var) (m1 : ('typ,'value,'var,'constr,'func) model) : ('typ,'value,'var,'constr,'func) model =
  Def (x,m1) [@@inline]
let make_any (t : 't) : ('typ,'value,'var,'constr,'func) model =
  Any t [@@inline]
let make_pat (t : 't) (c : 'constr) ?(src = [||]) (args : ('typ,'value,'var,'constr,'func) model array) : ('typ,'value,'var,'constr,'func) model =
  Pat (t,c,src,args) [@@inline]
let make_alt (xc : 'var) (cond : ('typ,'value,'var,'func) cond_model) (m1 : ('typ,'value,'var,'constr,'func) model) (m2 : ('typ,'value,'var,'constr,'func) model) : ('typ,'value,'var,'constr,'func) model =
  Alt (xc,cond,m1,m2) [@@inline]
let make_expr e = Expr e [@@inline]
let make_expr_const t v = Expr (Expr.Const (t, v)) [@@inline]
let make_derived t = Derived t [@@inline]

let undef : ('typ,'value,'var,'constr,'func) model -> ('typ,'value,'var,'constr,'func) model =
  function
  | Def (_,m) -> m
  | m -> m
                    
let rec typ : ('typ,'value,'var,'constr,'func) model -> 'typ = function
  | Def (x,m1) -> typ m1
  | Any t -> t
  | Pat (t,c,src,args) -> t
  | Alt (xc,c,m1,m2) -> typ m1
  | Expr e -> Expr.typ e
  | Derived t -> t

let rec fold (f : 'a -> 'model -> 'a) (acc : 'a) (m : 'model) : 'a =
  let acc = f acc m in 
  match m with
  | Def (x,m1) -> fold f acc m1
  | Any t -> acc
  | Pat (t,c,src,args) -> Array.fold_left (fold f) acc args
  | Alt (xc,c,m1,m2) ->
     let acc = fold f acc m1 in
     let acc = fold f acc m2 in
     acc
  | Expr e -> acc
  | Derived t -> acc

(* printing *)
  
let xp_model
      ~(xp_value : 'value html_xp)
      ~(xp_var : 'var html_xp)
      ~(xp_any : 'typ -> unit html_xp)
      ~(xp_pat : 'constr -> unit html_xp array -> unit html_xp array -> unit html_xp)
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
    | Pat (_t,c,src,args) ->
       let xp_src =
         Array.map
           (fun e -> (fun ~html print () ->
              Expr.xp_expr ~xp_value ~xp_var ~xp_func ~html print e))
           src in
       let xp_args =
         Array.map
           (fun arg -> (fun ~html print () -> aux ~prio_ctx:0 ~html print arg))
           args in
       xp_pat c xp_src xp_args ~html print ()

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
      
    | Expr (Expr.Const (_,v)) ->
       xp_value ~html print v
    | Expr e ->
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
    | Alias (x,_p) ->
       print#string " ";
       xp_var ~html print x
  in
  aux

(* ASD *)

class virtual ['typ,'asd_typ,'constr,'func] asd =
  object (self)
    method virtual abstract : 'typ -> 'asd_typ
    method virtual pats : 'asd_typ -> ('constr * 'asd_typ array * 'asd_typ array) list (* omit derived arguments *)
    method virtual funcs : 'asd_typ -> ('func * 'asd_typ array) list (* omit constant args (relative to make_index), repeat functions for different const-related modes *)
    
    method virtual expr_opt : 'typ -> bool (* allow expressions on this type? *)
    method virtual alt_opt : 'typ -> bool (* allow alternatives on this type? *)
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
    | Pat (t,c,src,args) ->
       Array.fold_right aux args acc
    | Alt (xc,cond,m1,m2) ->
       let acc = aux m1 acc in
       let acc = aux m2 acc in
       Mymap.add xc typ_bool acc
    | Expr e -> acc
    | Derived t -> acc
  in
  aux m0 Mymap.empty
  
let get_bindings  (* QUICK *)
      ~(typ_bool : 'typ)
      ~(value_of_bool : bool -> 'value)
      (m0 : ('typ,'value,'var,'constr,'func) model as 'model)
      (d0 : ('value,'constr) data as 'data)
    : ('var,'typ,'value) Expr.bindings =
  let rec aux m (d : 'data) acc =
    match m, d with
    | Def (x,m1), _ ->
       let acc = aux m1 d acc in
       let t1 = typ m1 in
       let v = Data.value d in
       Mymap.add x (t1,v) acc
    | Any t, _ -> acc
    | Pat (t,c,src,args), DPat (_v, _c, _src, dargs) ->
       let n = Array.length args in
       assert (Array.length dargs = n);
       let ref_acc = ref acc in (* missing Array.fold_right2 *)
       for i = 0 to n - 1 do
         ref_acc := aux args.(i) dargs.(i) !ref_acc
       done;
       !ref_acc
    | Alt (xc,c,m1,m2), DAlt (_prob,b,d12) ->
       let acc =
         if b
         then aux m1 d12 acc
         else aux m2 d12 acc in
       Mymap.add xc (typ_bool, value_of_bool b) acc
    | Expr _, _ -> acc
    | Derived _, _ -> acc
    | _ -> assert false
  in
  aux m0 d0 Expr.bindings0


(* model-based generation *)

type ('info,'var,'typ,'value,'constr) generator = 'info -> ('value,'constr) data Myseq.t

let generator (* on evaluated models: no expr, no def *)
      ~(eval_expr : ('typ,'value,'var,'func) Expr.expr -> ('var,'typ,'value) Expr.bindings -> 'value result)
      ~(bool_of_value : 'value -> bool result)
      ~(generator_value : 'value -> 'gen)
      ~(generator_any : 'typ -> 'gen)
      ~(generator_pat : 'typ -> 'constr -> 'value array -> (('info,'var,'typ,'value,'constr) generator as 'gen) array -> 'gen)
    : ('typ,'value,'var,'constr,'func) model -> ('var,'typ,'value) Expr.bindings -> 'gen =
  fun m bindings info ->
  let rec gen m info =
    match m with
    | Def (x,m1) ->
       gen m1 info
    | Any t ->
       generator_any t info
    | Pat (t,c,src,args) ->
       let* vsrc = Myseq.from_result (array_map_result (fun e -> eval_expr e bindings) src) in
       let gen_args = Array.map gen args in
       generator_pat t c vsrc gen_args info
    | Alt (xc,c,m1,m2) ->
       let gen_b_d1 prob =
         let* d1 = gen m1 info in
         let d = DAlt (prob,true,d1) in
         Myseq.return d in
       let gen_b_d2 prob =
         let* d2 = gen m2 info in
         let d = DAlt (prob,false,d2) in
         Myseq.return d in
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
               (let| v = eval_expr e bindings in
                bool_of_value v) in
           if b
           then gen_b_d1 1.
           else gen_b_d2 1.)
    | Expr e ->
       let* v = Myseq.from_result (eval_expr e bindings) in
       generator_value v info
    | Derived t ->
       failwith "Derived arguments must not be generated but computed" (* must be computed, not generated *)
  in
  gen m info

(* model-based parsing *)

type ('input,'var,'typ,'value,'constr) parseur = 'input -> ('value,'constr) data Myseq.t

let parseur (* on evaluated models: no expr, no def *)
      ~(eval_expr : ('typ,'value,'var,'func) Expr.expr -> ('var,'typ,'value) Expr.bindings -> 'value result)
      ~(bool_of_value : 'value -> bool result)
      ~(parseur_value : 'value -> 'parse)
      ~(parseur_any : 'typ -> 'parse)
      ~(parseur_pat : 'typ -> 'constr -> 'value array -> 'parse array -> 'parse)
    : ('typ,'value,'var,'constr,'func) model -> ('var,'typ,'value) Expr.bindings -> (('input,'var,'typ,'value,'constr) parseur as 'parse) =
  fun m bindings input ->
  let rec parse m input =
    match m with
    | Def (x,m1) ->
       parse m1 input
    | Any t ->
       parseur_any t input
    | Pat (t,c,src,args) ->
       let* vsrc =  Myseq.from_result (array_map_result (fun e -> eval_expr e bindings) src) in
       let parse_args = Array.map parse args in
       parseur_pat t c vsrc parse_args input
    | Alt (xc,c,m1,m2) -> (* if-then-else *)
       let seq1 prob =
         let* d1 = parse m1 input in
         let d = DAlt (prob,true,d1) in
         Myseq.return d in
       let seq2 prob =
         let* d2 = parse m2 input in
         let d = DAlt (prob,false,d2) in
         Myseq.return d in
       (match c with
        | Undet prob ->
           if prob >= 0.5 (* TODO: weight interleave according to prob *)
           then Myseq.interleave [seq1 prob; seq2 (1. -. prob)]
           else Myseq.interleave [seq2 (1. -. prob); seq1 prob]
        | BoolExpr e ->
           let* b =
             Myseq.from_result
               (let| v = eval_expr e bindings in
                bool_of_value v) in
           if b
           then seq1 1.
           else seq2 1.)                
    | Expr e ->
       let* v = Myseq.from_result (eval_expr e bindings) in
       parseur_value v input
    | Derived t ->
       failwith "Derived arguments must not be parsed but computed" 
  in
  parse m input

(* model-based encoding of data *)

let dl_data
      ~(encoding_dany : 'value -> 'encoding)
      ~(encoding_dpat : 'constr -> 'value array -> 'encoding array -> 'encoding)
      ~(encoding_alt : dl (* DL of branch choice *) -> 'encoding -> 'encoding (* with added DL choice *))
      ~(encoding_expr_value : 'value -> 'encoding) (* DL = 0 *)
      ~(dl_of_encoding : 'encoding -> dl)
    : (('value,'constr) data as 'data) -> dl = (* QUICK *)
  let rec aux = function
    | DAny (_, v_r) -> encoding_dany v_r
    | DPat (_, c, vsrc, dargs) ->
       let encs = Array.map aux dargs in
       encoding_dpat c vsrc encs
    | DAlt (prob,b,d12) ->
       let dl_choice = Mdl.Code.usage prob in
       let enc12 = aux d12 in
       encoding_alt dl_choice enc12
    | DExpr v -> encoding_expr_value v
  in
  fun d ->
  let enc = aux d in
  dl_of_encoding enc

let dl_parse_rank (rank : int) : dl =
  (* penalty DL for parse rank, starting at 0 *)
  float rank (* exponential decay of probability *)
  (* Mdl.Code.universal_int_star rank -. 1. *)
  
(* model encoding *)

let size_any = 1
let size_alt = 1
  
let size_model_ast (* for DL computing, QUICK *)
      ~(asd : ('typ,'asd_typ,'constr,'func) asd)
    (m : ('typ,'value,'var,'constr,'func) model) : int =
  let rec aux = function
    | Def (x,m1) -> aux m1 (* definitions are ignore in DL, assumed determined by model AST *)
    | Any t -> size_any
    | Pat (t,c,src,args) ->
       let size = 1 in (* pattern *)
       let size = (* src exprs *)
         Array.fold_left
           (fun res e -> res + Expr.size_expr_ast e)
           size src in
       let size = (* arg models *)
         Array.fold_left
           (fun res arg -> res + aux arg)
           size args in
       size
    | Alt (xc,c,m1,m2) -> size_alt + aux_cond c + aux m1 + aux m2
    | Expr e -> Expr.size_expr_ast e
    | Derived t -> 0 (* implicit, no information there *)
  and aux_cond = function
    | Undet _ -> 1
    | BoolExpr e -> Expr.size_expr_ast e
  in
  aux m

let nb_model_ast (* for DL computing, must be consistent with size_model_ast *)
      ~(typ_bool : 'typ)
      ~(asd : ('typ,'asd_typ,'constr,'func) asd)
      ~(nb_expr_ast : 'asd_typ -> int -> float) =
  let tab : ('asd_typ * int, float) Hashtbl.t = Hashtbl.create 1013 in
  let reset () = Hashtbl.clear tab in
  let rec aux (t : 'typ) (size : int) : float (* float to handle large numbers *) =
    let k = asd#abstract t in
    match Hashtbl.find_opt tab (k,size) with
    | Some nb -> nb
    | None -> (* QUICK *)
       let nb = 0. in
       let nb = (* counting possible expressions *)
         if asd#expr_opt t
         then nb +. nb_expr_ast k size
         else nb in
       let nb = (* counting possible Any *)
         if size = size_any
         then nb +. 1.
         else nb in
       let nb = (* counting possible alternatives *)
         if size >= size_alt + 3 && asd#alt_opt t
         then nb +. sum_conv ~min_arg:1 [aux_cond; aux k; aux k] (size - size_alt)
                             (* split between condition, left model, right model *)
         else nb in
       let nb = (* counting Pat (c,args) *)
         let constr_args = asd#pats k in
         List.fold_left
           (fun nb (c,k_src,k_args) ->
             let len_src = Array.length k_src in
             let len_args = Array.length k_args in
             let len = len_src + len_args in
             if len = 0 (* leaf node *)
             then if size = 1 then nb +. 1. else nb
             else
               if size >= 1 + len
               then nb +. sum_conv ~min_arg:1
                            (Array.to_list
                               (Array.append
                                  (Array.map nb_expr_ast k_src)
                                  (Array.map aux k_args)))
                            (size-1)
               else nb)
           nb constr_args in
       Hashtbl.add tab (k,size) nb;
       nb
  and aux_cond (size : int) : float =
    let nb = nb_expr_ast (asd#abstract typ_bool) size in (* BoolExpr *)
    if size = 1
    then nb +. 1.
    else nb
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
    | Any t -> 0.
    | Pat (t,c,src,args) ->
       let dl_src_params =
         Array.map dl_expr_params src
         |> Array.fold_left (+.) 0. in
       let dl_args_params =
         Array.map aux args
         |> Array.fold_left (+.) 0. in
       dl_constr_params t c +. dl_src_params +. dl_args_params
    | Alt (xc,c,m1,m2) ->
       aux_cond c +. aux m1 +. aux m2
    | Expr e -> dl_expr_params e
    | Derived t -> 0.
  and aux_cond = function
    | Undet prob -> Mdl.Code.uniform 10 (* bounding float precision, TODO: use better distrib *)
    | BoolExpr e -> dl_expr_params e
  in
  fun m ->
  aux m

let dl
      ~(size_model_ast : ('typ,'value,'var,'constr,'func) model -> int)
      ~(nb_model_ast : 'typ -> int -> float)
      ~(dl_model_params : dl_var:('typ -> 'var -> dl) -> (('typ,'value,'var,'constr,'func) model as 'model) -> dl)
      ~(dl_var : nb_env_vars:int -> 'typ -> 'var -> dl)
      ~(xp_model : 'model html_xp)
      ~(xp_typ : 'typ html_xp) =
  fun
    ~(nb_env_vars : int)
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
       m
       
(* reading *)

type ('typ,'value,'constr,'var,'func) read =
  { bindings : ('var,'typ,'value) Expr.bindings;
    mutable lazy_index : ('typ,'value,'var,'func) Expr.index option; (* not using Lazy.t because breaks comparisons and hash *)
    data : ('value,'constr) data;
    dl_rank : dl;
    dl : dl } (* including rank *)

let force_index
      ~(make_index : ('var,'typ,'value) Expr.bindings -> ('typ,'value,'var,'func) Expr.index)
      (read : ('typ,'value,'constr,'var,'func) read)
    : ('typ,'value,'var,'func) Expr.index =
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
      ~(parseur : ('typ,'value,'var,'constr,'func) model -> ('var,'typ,'value) Expr.bindings -> ('input,'var,'typ,'value,'constr) parseur)
      ~(dl_data : ('value,'constr) data -> dl)

      (m : ('typ,'value,'var,'constr,'func) model)
    : ('input,'var,'typ,'value,'constr) parse_bests =
  fun bindings input ->
  Common.prof "Model.parse_bests" (fun () ->
  let parses =
    let* data = parseur m bindings input in
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
      ~(parse_bests : ('typ,'value,'var,'constr,'func) model -> ('input,'var,'typ,'value,'constr) parse_bests)

      ~(bindings : ('var,'typ,'value) Expr.bindings)
      (m : ('typ,'value,'var,'constr,'func) model)
      (v : 'value)
    : ('typ,'value,'constr,'var,'func) read Myseq.t =
  Myseq.prof "Model.read" (
  let t = typ m in
  let input = input_of_value t v in
  let* best_parses = Myseq.from_result (parse_bests m bindings input) in
  let* rank, (data, dl) = Myseq.with_position (Myseq.from_list best_parses) in
  let dl_rank = dl_parse_rank rank in (* to penalize later parses, in case of equivalent parses, only for prediction *)
  Myseq.return { bindings; lazy_index=None; data; dl_rank; dl })

let does_parse_value
      ~(input_of_value : 'typ -> 'value -> 'input)
      ~(parseur : ('typ,'value,'var,'constr,'func) model -> ('var,'typ,'value) Expr.bindings -> ('input,'var,'typ,'value,'constr) parseur)

      (m : ('typ,'value,'var,'constr,'func) model)
      (bindings : ('var,'typ,'value) Expr.bindings)
      (value : 'value)
    : bool =
  Common.prof "Model.does_parse" (fun () ->
  let t = typ m in
  let input = input_of_value t value in
  not (Myseq.is_empty (parseur m bindings input)))

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
  let* data = generator m bindings info in
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
    | Field (c,i) :: p1, Pat (t,c',src,args) when c = c' && i < Array.length args ->
       let new_args = Array.copy args in
       new_args.(i) <- aux p1 r args.(i);
       Pat (t, c, src, new_args)
    | Branch true :: p1, Alt (xc,c,m1,m2) ->
       let new_m1 = aux p1 r m1 in
       Alt (xc,c,new_m1,m2)
    | Branch false :: p1, Alt (xc,c,m1,m2) ->
       let new_m2 = aux p1 r m2 in
       Alt (xc,c,m1,new_m2)
    | [], _ -> r
    | _ -> assert false
  in
  aux
