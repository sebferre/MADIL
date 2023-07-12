
open Madil_common
open Data
open Path

type 'dconstr ctx = 'dconstr path -> 'dconstr path
let ctx0 : _ ctx = (fun p -> p)

type ('constr,'func) model =
  | Pat of 'constr * ('constr,'func) model array (* constr type may be different from data constr *)
  | Seq of int * ('constr,'func) model list
  | Cst of ('constr,'func) model
  | Expr of ('constr path,'func) Expr.expr

let xp_model
      (print_constr : 'constr Xprint.xp)
      (print_field : ('dconstr * int) Xprint.xp)
      (print_func : 'func Xprint.xp)
    : ('constr,'func) model Xprint.xp =
  let rec aux print m =
    match m with
    | Pat (c,args) ->
       print_constr print c;
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
    | Expr e -> Expr.xp_expr print_field print_func print e
  in
  fun print m ->
  aux print m


(* model evaluation *)

let get_bindings
      ~(constr_value_opt : 'dconstr path -> 'value -> 'dconstr -> 'value option) (* binding values at some path given value and data constr there *)
      ~(seq_value_opt : 'dconstr path -> 'value list -> 'value option)
      (m : ('constr,'func) model) (d : ('value,'dconstr) data) : ('value,'dconstr) bindings =
  let rec aux ctx m d acc =
    match m, d with
    | Pat (c,args), DVal (v, DPat (dc, dargs)) ->
       let n = Array.length args in
       assert (Array.length dargs = n);
       let p = ctx This in
       let v_opt = constr_value_opt p v dc in
       let ref_acc = ref acc in
       Option.iter
         (fun v -> ref_acc := (p,v) :: !ref_acc)
         v_opt;
       for i = 0 to n - 1 do
         let vi_opt, acc = aux (fun pi -> ctx (Field (dc,i,pi))) args.(i) dargs.(i) !ref_acc in
         ref_acc := acc
       done;
       v_opt, !ref_acc
    | Expr _, _ -> None, acc (* expressions only in task output *)
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
  let v_opt, acc = aux ctx0 m d [] in
  acc

let eval
      ~eval_unbound_path ~eval_func ~eval_arg
      ~(model_of_value : 'value -> ('constr,'func) model result)
      (m : ('constr,'func) model) (bindings : ('value,'dconstr) bindings)
    : ('constr,'func) model result =
  let eval_expr = Expr.eval ~eval_unbound_path ~eval_func ~eval_arg in
  let rec aux = function
    | Pat (c,args) ->
       let| l_args' = list_map_result aux (Array.to_list args) in
       let args' = Array.of_list l_args' in
       Result.Ok (Pat (c,args'))
    | Expr e ->
       let| v = eval_expr e bindings in
       model_of_value v
    | Seq (n,lm1) ->
       let| lm1' = list_map_result aux lm1 in
       Result.Ok (Seq (n,lm1'))
    | Cst m1 -> raise TODO
  in
  aux m
  
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

  (* TODO: model encoding *)

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
