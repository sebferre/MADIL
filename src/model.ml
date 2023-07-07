
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


let compile
      ~(x_constr : 'a -> 'constr -> 'a) (* input preparation for constr *)
      ~(x_field : 'a -> 'constr -> int -> 'a) (* dispatch pattern input to each field *)
      ~(y_constr : 'a -> 'constr -> 'b array -> 'b) (* pattern output from input, and argument outputs *)
      ~(x_first : 'a -> 'a) (* initial input for sequence *)
      ~(x_next : 'a -> 'b -> 'a) (* next input in sequence, from previous item input and output *)
      ~(y_seq : 'a -> 'b list -> 'a -> 'b) (* sequence output from input, item outputs, and remainder input *)
      (m : ('constr,'func) model) : 'a -> 'b =
  let rec aux : ('constr,'field) model -> ('a -> 'b) = function
    | Pat (c,args) ->
       let g_args = Array.map aux args in
       (fun x ->
         let x = x_constr x c in
         let y_args = Array.mapi (fun i g_arg -> g_arg (x_field x c i)) g_args in
         y_constr x c y_args)
    | Expr e -> assert false
    | Seq (n,lm1) ->
       let g_lm1 = List.map aux lm1 in
       (fun x ->
         let x1 = x_first x in
         let xN, rev_ly =
           List.fold_left
             (fun (xi, rev_ly) gi ->
               let yi = gi xi in
               x_next xi yi, yi::rev_ly)
             (x1,[]) g_lm1 in
         y_seq x (List.rev rev_ly) xN)
    | Cst m1 -> raise TODO
(*       let g_m1 = aux m1 in
       (fun x ->
         let x1 = x_first x in
 *)       
  in
  aux m

let generator (* naive *)
      ~(output_constr : 'constr -> ('value,'dconstr) data array -> ('value,'dconstr) data)
    : ('constr,'func) model -> (unit -> ('value, 'constr) data) =
  compile
    ~x_constr:(fun () c -> ())
    ~x_field:(fun () c i -> ())
    ~y_constr:(fun () c args -> output_constr c args)
    ~x_first:(fun () -> ())
    ~x_next:(fun () _ -> ())
    ~y_seq:(fun () ld () -> DSeq (List.length ld, ld))

let parseur
      ~(input_constr : 'input -> 'constr -> 'input)
      ~(input_field : 'input -> 'constr -> int -> 'input)
      ~(output_constr : 'input -> 'constr -> ('value,'dconstr) data array -> ('value,'dconstr) data Myseq.t)
      ~(input_first : 'input -> 'input)
      ~(input_next : 'input -> ('value,'dconstr) data Myseq.t -> 'input)
      ~(output_seq : 'input -> int -> ('value,'dconstr) data list -> 'input -> ('value,'dconstr) data Myseq.t)
    : ('constr,'func) model -> ('input -> ('value,'dconstr) data Myseq.t) =
  compile
    ~x_constr:input_constr
    ~x_field:input_field
    ~y_constr:(fun input c seq_args ->
      let* l_args = Myseq.product_fair (Array.to_list seq_args) in
      let args = Array.of_list l_args in
      output_constr input c args)
    ~x_first:input_first
    ~x_next:input_next
    ~y_seq:(fun input seq_ld input_last ->
      let n = List.length seq_ld in
      let* ld = Myseq.product_fair seq_ld in
      output_seq input n ld input_last)
