
open Madil_common
open Data
open Path
open Kind

type 'constr ctx = 'constr path -> 'constr path
let ctx0 : _ ctx = (fun p -> p)

type ('constr,'func) model =
  | Pat of 'constr * ('constr,'func) model array (* constr type may be different from data constr *)
  | Seq of int * ('constr,'func) model list
  | Cst of ('constr,'func) model
  | Expr of ('constr,'func) Expr.expr

let make_pat (c : 'constr) (args : ('constr,'func) model array) : ('constr,'func) model =
  Pat (c,args)
          
let xp_model
      (xp_constr : 'constr Xprint.xp)
      (xp_field : ('constr * int) Xprint.xp)
      (xp_func : 'func Xprint.xp)
    : ('constr,'func) model Xprint.xp =
  let rec aux print m =
    match m with
    | Pat (c,args) ->
       xp_constr print c;
       Xprint.bracket ("[","]")
         (Xprint.sep_array ", " aux)
         print args
    | Seq (n,lm1) ->
       Xprint.bracket ("<" ^ string_of_int n ^ ": ", ">")
         (Xprint.sep_list ", " aux)
         print lm1
    | Cst m1 ->
       Xprint.bracket ("<", " = >") aux
         print m1
    | Expr e -> Expr.xp_expr xp_field xp_func print e
  in
  aux


(* model evaluation *)

let binding_paths
      ~(visible_path : 'constr path -> bool) (* is this path accessible to the output model? *)
      (m : ('constr,'func) model)
    : 'constr binding_paths =
  let rec aux ctx m =
    let p = ctx This in
    let s =
      if visible_path p
      then Bintree.singleton p
      else Bintree.empty in
    match m with
    | Pat (c,args) ->
       let s_args =
         Array.mapi
           (fun i argi ->
             let ctxi = (fun pi -> ctx (Field (c,i,pi))) in
             aux ctxi argi)
           args in
       Array.fold_left Bintree.union s s_args
    | Expr e -> s
    | Seq (n,lm1) ->
       let i, s =
         List.fold_left
           (fun (i,s) mi ->
             let cxti = (fun pi -> ctx (Item (i,pi))) in
             i+1, Bintree.union s (aux cxti mi))
           (0,s) lm1 in
       assert (i = n);
       s
    | Cst m1 -> raise TODO
  in
  aux ctx0 m

  
let get_bindings
      ~(constr_value_opt : 'constr path -> 'value -> 'dconstr -> 'value option) (* binding values at some path given value and data constr there *)
      ~(seq_value_opt : 'constr path -> 'value list -> 'value option)
      (m : ('constr,'func) model)
      (d : ('value,'dconstr) data)
    : ('value,'constr) bindings =
  let rec aux ctx m d acc =
    match m, d with
    | Pat (c,args), DVal (v, DPat (dc, dargs)) ->
       let n = Array.length args in
       assert (Array.length dargs = n);
       let p = ctx This in
       let v_opt = constr_value_opt p v dc in
       let ref_acc = ref acc in
       Option.iter
         (fun v -> ref_acc := Mymap.add p v !ref_acc)
         v_opt;
       for i = 0 to n - 1 do
         let vi_opt, acc = aux (fun pi -> ctx (Field (c,i,pi))) args.(i) dargs.(i) !ref_acc in
         ref_acc := acc
       done;
       v_opt, !ref_acc
    | Expr _, _ -> None, acc (* expressions only in task output but TODO in general expression values should be accessible *)
    | Seq (n,lm), DSeq (dn,ld) ->
       assert (n = dn);
       let _, lv_opt, acc =
         List.fold_right2
           (fun mi di (i,lv_opt,acc) ->
             let ctx_i = (fun pi -> ctx (Item (i,pi))) in
             let v_opt, acc = aux ctx_i mi di acc in
             match v_opt, lv_opt with
             | Some v, Some lv -> i-1, Some (v::lv), acc
             | _ -> i-1, None, acc)
           lm ld (n-1, Some [], acc) in
       (match lv_opt with
        | Some lv ->
           let p = ctx This in
           seq_value_opt p lv, acc
        | None -> None, acc)
    | Cst _, _ -> raise TODO
    | _ -> assert false
  in
  let v_opt, acc = aux ctx0 m d bindings0 in
  acc

let eval
      ~asd
      ~eval_unbound_path ~eval_func ~eval_arg
      ~(model_of_value : 't kind -> 'value -> ('constr,'func) model result)
      (k : 't kind)
      (m : ('constr,'func) model)
      (bindings : ('value,'constr) bindings)
    : ('constr,'func) model result =
  let eval_expr = Expr.eval ~eval_unbound_path ~eval_func ~eval_arg in
  let rec aux k m =
    match k, m with
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
    | _, Expr e ->
       let| v = eval_expr e bindings in
       model_of_value k v
    | KSeq k1, Seq (n,lm1) ->
       let| lm1' = list_map_result (aux k1) lm1 in
       Result.Ok (Seq (n,lm1'))
    | _, Cst m1 -> raise TODO
    | _ -> assert false
  in
  aux k m
  
(* model-based generation *)

type ('info,'value,'dconstr) generator = 'info -> ('value,'dconstr) data

let generator
      ~(generator_pat: 'constr -> 'gen array -> 'gen)
    : ('constr,'func) model -> (('info,'value,'dconstr) generator as 'gen) =
  let rec gen = function
    | Pat (c,args) ->
       let gen_args = Array.map gen args in
       generator_pat c gen_args
    | Expr e -> assert false
    | Seq (n,lm1) ->
       let gen_lm1 = List.map gen lm1 in
       (fun x ->
         let ld = List.map (fun gen_mi -> gen_mi x) gen_lm1 in
         DSeq (n, ld))
    | Cst m1 -> raise TODO
  in
  gen
  
                                        
(* model-based parsing *)

type ('input,'value,'dconstr) parseur = 'input -> (('value,'dconstr) data * 'input) Myseq.t

let parseur
      ~(parseur_pat : 'constr -> 'parse array -> 'parse)
    : ('constr,'func) model -> (('input,'value,'dconstr) parseur as 'parse) =
  let rec parse = function
    | Pat (c,args) ->
       let parse_args = Array.map parse args in
       parseur_pat c parse_args
    | Expr e -> assert false
    | Seq (n,lm1) ->
       let parse_lm1 = List.map parse lm1 in
       (fun x ->
         let* ld, x = Myseq.product_dependent_fair parse_lm1 x in
         Myseq.return (DSeq (n, ld), x))
    | Cst m1 -> raise TODO
  in
  parse

(* model-based encoding of data *)

type ('info,'value,'dconstr) encoder = 'info -> ('value,'dconstr) data -> dl * 'info

let encoder
      ~(encoder_pat : 'constr -> 'enc array -> 'enc)
  : ('constr,'func) model -> (('info,'value,'dconstr) encoder as 'enc) =
  let rec enc = function
    | Pat (c,args) ->
       let enc_args = Array.map enc args in
       encoder_pat c enc_args
    | Expr e ->
       (fun x d -> 0., x)
    | Seq (n,lm1) ->
       let enc_lm1 = List.map enc lm1 in
       (fun x -> function
         | DSeq (dn, ld) when dn = n ->
            List.fold_left2
              (fun (dl,x) enc_mi di ->
                let dli, x = enc_mi x di in
                dl +. dli, x)
              (0., x) (* no need to encode 'dn', equal 'n' in model *)
              enc_lm1 ld
         | _ -> assert false)
    | Cst m1 -> raise TODO
  in
  enc

let dl_parse_rank (rank : int) : dl =
  (* penalty DL for parse rank, starting at 0 *)
  Mdl.Code.universal_int_star rank -. 1.
  
(* ASD *)

class virtual ['t,'constr,'func] asd =
  object (self)
    method virtual default_and_other_pats : 't -> 'constr option * ('constr * 't kind array) list
    method constr_args : 't -> 'constr -> 't kind array =
      fun t c ->
      let def_opt, others = self#default_and_other_pats t in
      if def_opt = Some c then [||]
      else
        match List.assoc_opt c others with
        | Some args -> args
        | None -> failwith "Model.asd#constr_args: unexpected constr"
    method virtual expr_opt : 't kind -> 't kind option
    method virtual funcs : 't kind -> ('func * 't kind array) list (* None when expressions not allowed for this kind *)
  end

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
  
(* model encoding *)

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
    | KSeq k1, Item (i,p1) -> aux k1 p1
    | _ -> assert false
  in
  aux
  
let size_model_ast (* for DL computing *)
    : ('constr,'func) model -> int =
  let rec aux = function
    | Pat (c,args) -> Array.fold_left (fun res arg -> res + aux arg) 1 args
    | Expr e -> Expr.size_expr_ast e
    | Seq (n,lm1) -> List.fold_left (fun res m1 -> res + aux m1) 1 lm1
    | Cst m1 -> 1 + aux m1
  in
  aux

let nb_model_ast (* for DL computing *)
      ~(asd : ('t,'constr,'func) asd)
    : 't kind -> int (* AST size *) -> float = (* float to handle large numbers *)
  let tab : ('t kind * int, float) Hashtbl.t = Hashtbl.create 1013 in
  let rec aux (k : 't kind) (size : int) : float =
    match Hashtbl.find_opt tab (k,size) with
    | Some nb -> nb
    | None ->
       let nb = (* counting possible expressions *)
         match asd#expr_opt k with
         | None -> 0.
         | Some k1 -> Expr.nb_expr_ast ~funcs:asd#funcs k1 size in
       match k with
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
  in
  aux

let dl_model_params
      ~(dl_constr_params : 'constr -> dl)
      ~(dl_func_params : 'func -> dl)
      ~(dl_path : 'constr path -> dl)
    : ('constr,'func) model -> dl =
  let dl_expr_params =
    Expr.dl_expr_params ~dl_func_params ~dl_path in
  let rec aux = function
    | Pat (c,args) ->
       let dl_args_params =
         Array.map aux args
         |> Array.fold_left (+.) 0. in
       dl_constr_params c +. dl_args_params
    | Expr e -> dl_expr_params e
    | Seq (n,lm1) ->
       List.map aux lm1
       |> List.fold_left (+.) 0.
    | Cst m1 -> raise TODO
  in
  aux

let dl
      ~(asd : ('t,'constr,'func) asd)
      ~(dl_constr_params : 'constr -> dl)
      ~(dl_func_params : 'func -> dl)
      ~(dl_path : nb_env_paths:int -> 'constr path -> dl)

      ~(nb_env_paths : int)
      (k : 't kind) (m : ('constr,'func) model) : dl =
  let size = size_model_ast m in
  let nb = nb_model_ast ~asd k size in
  Mdl.Code.universal_int_star size (* encoding model AST size *)
  +. Mdl.log2 nb (* encoding choice of model AST for that size *)
  +. dl_model_params
       ~dl_constr_params
       ~dl_func_params
       ~dl_path:(dl_path ~nb_env_paths)
       m

       
(* reading *)

type ('value,'dconstr,'constr,'func) read =
  { env : ('value,'dconstr) data;
    bindings : ('value,'constr) bindings;
    index : ('value,'constr,'func) Expr.Index.t;
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

type ('input,'value,'dconstr) parseur_bests = 'input -> (('value,'dconstr) data * dl) list result
        
let parseur_bests
      ~(max_nb_parse : int)
      ~(parseur : ('constr,'func) model -> ('input,'value,'dconstr) parseur)
      ~(dl_data : ('constr,'func) model -> ('value,'dconstr) data -> dl)

      (m : ('constr,'func) model)
    : ('input,'value,'dconstr) parseur_bests =
  let parse = parseur m in
  let dl_data_m = dl_data m in
  fun x ->
  Common.prof "Model.sorted_parseur" (fun () ->
  let parses =
    let* data, _ = parse x in
    let dl = (* QUICK *)
      dl_round (dl_data_m data) in
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
      ~(eval : 't kind -> ('constr,'func) model -> ('value,'constr) bindings -> ('constr,'func) model result)
      ~(parseur_bests : ('constr,'func) model -> ('input,'value,'dconstr) parseur_bests)
      ~(make_index : ('value,'constr) bindings -> ('value,'constr,'func) Expr.Index.t)

      ?(dl_assuming_contents_known = false)
      ~(env : ('value,'dconstr) data)
      ~(bindings : ('value,'constr) bindings)
      (k : 't kind)
      (m0 : ('constr,'func) model)
      (x : 'input)
    : ('value,'dconstr,'constr,'func) read list result =
  Common.prof "Model.read" (fun () ->
  let| m = eval k m0 bindings in (* reducing expressions *)
  let| best_parses = parseur_bests m x in
  let index = lazy (make_index bindings) in
  let reads =
    best_parses
    |> (fun l ->
      Common.sub_list l 0
        (if dl_assuming_contents_known
         then 1 (* TODO: relax because fragile, see task 5, relaxing digit 5 *)
         else max_nb_reads))
         (* in pruning mode, only best read as we simulate prediction *)
         (* TODO: should be handled by DLs *)
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

let write
      ~(eval : 't kind -> ('constr,'func) model -> ('value,'constr) bindings -> ('constr,'func) model result)
      ~(generator : ('constr,'func) model -> ('info,'value,'dconstr) generator)
      
      ~(bindings : ('value,'constr) bindings)
      (k : 't kind)
      (m0 : ('constr,'func) model)
      (info : 'info)
    : ('value,'dconstr) data result =
  Common.prof "Model.write" (fun () ->
  let| m = eval k m0 bindings in
  let d = generator m info in
  Result.Ok d)


(* model refinement *)

let refine (* replace submodel of [m] at [p] by [r] *) 
    : 'constr path -> ('constr,'func) model -> ('constr,'func) model -> ('constr,'func) model =
  let rec aux p r m =
    match p, m with
    | This, _ -> r
    | Field (c,i,p1), Pat (c',args) when c = c' && i < Array.length args ->
       let new_args = Array.copy args in
       new_args.(i) <- aux p1 r args.(i);
       Pat (c, new_args)
    | Item (i,p1), Seq (n,lm1) when i < n ->
       let new_lm1 = list_update (fun mi -> aux p1 r mi) i lm1 in
       Seq (n,new_lm1)
    | _ -> assert false
  in
  aux
