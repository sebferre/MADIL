
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
      ~(x_constr : 'a -> 'constr -> 'a Myseq.t) (* input preparation for constr *)
      ~(x_field : 'a -> 'constr -> int -> 'a) (* dispatch pattern input to each field *)
      ~(y_constr : 'a -> 'constr -> 'b array -> 'b Myseq.t) (* pattern output from input, and argument outputs *)
      ~(x_first : 'a -> 'a Myseq.t) (* initial input for sequence *)
      ~(x_next : 'a -> 'b -> 'a Myseq.t) (* next input in sequence, from previous item input and output *)
      ~(y_seq : 'a -> 'b list -> 'a -> 'b Myseq.t) (* sequence output from input, item outputs, and remainder input *)
      (m : ('constr,'func) model) : 'a -> 'b Myseq.t=
  let rec aux : ('constr,'field) model -> ('a -> 'b Myseq.t) = function
    | Pat (c,args) ->
       let g_args = Array.map aux args in
       (fun x ->
         let* x = x_constr x c in
         let seq_args = Array.mapi (fun i g_arg -> g_arg (x_field x c i)) g_args in
         let* l_args = Myseq.product_fair (Array.to_list seq_args) in
         let args = Array.of_list l_args in
         y_constr x c args)
    | Expr e -> assert false
    | Seq (n,lm1) ->
       let g_lm1 =
         List.map
           (fun mi ->
             let gi = aux mi in
             (fun xi ->
               let* yi = gi xi in
               let* x_next = x_next xi yi in
               Myseq.return (yi,x_next)))
           lm1 in
       (*let g_lm1 = List.map aux lm1 in*)
       (fun x ->
         let* x1 = x_first x in
         let* ly, xN = Myseq.product_dependent_fair g_lm1 x1 in
(*         let xN, rev_ly =
           List.fold_left
             (fun (xi, rev_ly) gi ->
               let yi = gi xi in
               x_next xi yi, yi::rev_ly)
             (x1,[]) g_lm1 in
         let ly = List.rev rev_ly in *)
         y_seq x ly xN)
    | Cst m1 -> raise TODO
(*       let g_m1 = aux m1 in
       (fun x ->
         let x1 = x_first x in
 *)       
  in
  aux m

type ('value,'dconstr) generator = unit -> ('value,'dconstr) data Myseq.t
  
let generator (* naive *)
      ~(output_constr : 'constr -> ('value,'dconstr) data array -> ('value,'dconstr) data)
    : ('constr,'func) model -> ('value, 'dconstr) generator =
  compile
    ~x_constr:(fun () c -> Myseq.return ())
    ~x_field:(fun () c i -> ())
    ~y_constr:(fun () c args -> Myseq.return (output_constr c args))
    ~x_first:(fun () -> Myseq.return ())
    ~x_next:(fun () _ -> Myseq.return ())
    ~y_seq:(fun () ld () -> Myseq.return (DSeq (List.length ld, ld)))


type ('input,'value,'dconstr) parseur = 'input -> ('value,'dconstr) data Myseq.t
  
let parseur
      ~(input_constr : 'input -> 'constr -> 'input Myseq.t)
      ~(input_field : 'input -> 'constr -> int -> 'input)
      ~(output_constr : 'input -> 'constr -> ('value,'dconstr) data array -> ('value,'dconstr) data Myseq.t)
      ~(input_first : 'input -> 'input Myseq.t)
      ~(input_next : 'input -> ('value,'dconstr) data -> 'input Myseq.t)
      ~(output_seq : 'input -> ('value,'dconstr) data list -> 'input -> ('value,'dconstr) data Myseq.t)
    : ('constr,'func) model -> ('input,'value,'dconstr) parseur =
  compile
    ~x_constr:input_constr
    ~x_field:input_field
    ~y_constr:output_constr
    ~x_first:input_first
    ~x_next:input_next
    ~y_seq:output_seq


type ('value,'dconstr) encoder = ('value,'dconstr) data -> dl

let encoder
      ~(dl_constr : 'constr -> 'dconstr -> dl)
    : ('constr,'func) model -> ('value,'dconstr) encoder =
  let aux : ('constr,'func) model -> (('value,'dconstr) data * ('value,'dconstr) data list -> dl Myseq.t) =
    compile
      ~x_constr:(fun (d,_) c -> Myseq.return (d,[]))
      ~x_field:(fun (d,_) c i ->
        match d with
        | DVal (v, DPat (dc, args)) -> (args.(i), [])
        | _ -> failwith "Model.encoder: unexpected data w.r.t. model")
      ~y_constr:(fun (d,_) c dl_args ->
        match d with
        | DVal (v, DPat (dc, args)) ->
           let dl_dc = dl_constr c dc in
           let dl = Array.fold_left (fun res dl_arg -> res +. dl_arg) dl_dc dl_args in
           Myseq.return dl
        | _ -> assert false)
      ~x_first:(fun (d,_) ->
        match d with
        | DSeq (_, d0::ld1) -> Myseq.return (d0,ld1)
        | _ -> assert false)
      ~x_next:(fun (di,ldi) _ ->
        match ldi with
        | [] -> Myseq.return (di,[]) (* should have some Null instead of di *)
        | d0::ld1 -> Myseq.return (d0,ld1))
      ~y_seq:(fun (d,_) dl_items (_,ldi_last) ->
        assert (ldi_last = []);
        (* no need to encode nb of items, rigid sequence model *)
        let dl = List.fold_left (fun res dl_item -> res +. dl_item) 0. dl_items in
        Myseq.return dl)
  in
  fun m ->
  let g = aux m in
  fun d ->
  match Myseq.hd_opt (g (d,[])) with
  | Some dl -> dl
  | None -> assert false
