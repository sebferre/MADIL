
open Madil_common

type ('value,'constr) data = (* data according to model, must be self-contained for encoding *)
  D of 'value * ('value,'constr) data_model
and ('value,'constr) data_model =
  | DAny of 'value (* a form of value often coming with some range constraint for DL computing *)
  | DPat of 'constr * ('value,'constr) data array
  | DAlt of float (* prob *) * bool * ('value,'constr) data (* the bool indicates which branch was chosen *)
  | DSeq of ('value,'constr) data array
  | DExpr (* computed value *)

(* TODO: consider adding DNil as nil data, for use as nil env *)

let value (d : ('value,'constr) data) : 'value =
  match d with
  | D (v, _) -> v

let make_dany (value : 'value) (value_range : 'value) : ('value,'constr) data =
  D (value, DAny value_range)
let make_dpat (value : 'value) (c : 'constr) (args : ('value,'constr) data array) : ('value,'constr) data =
  D (value, DPat (c, args))
let make_dseq (value : 'value) (ds : ('value,'constr) data array) : ('value,'constr) data =
  D (value, DSeq ds)
let make_dexpr (value : 'value) : ('value,'constr) data =
  D (value, DExpr)
          
let xp_data
      ~(xp_value : 'value html_xp)
      ~(xp_pat : 'constr -> unit html_xp array -> unit html_xp)
    : ('value,'constr) data html_xp =
  let rec aux ~prio_ctx ~html print d =
    match d with
    | D (_v, DAny v_r) ->
       xp_html_elt "span" ~classe:"data-any" ~html print
         (fun () ->
           xp_value ~html print v_r)
    | D (_v, DPat (c,args)) ->
       let xp_args =
         Array.map
           (fun arg -> (fun ~html print () -> aux ~prio_ctx:0 ~html print arg))
           args in
       xp_pat c xp_args ~html print ()
    | D (_v, DAlt (_prob,_b,d12)) ->
       xp_brackets_prio ~prio_ctx ~prio:2 ~html print
         (fun () ->
           xp_html_elt "div" ~classe:"data-alt" ~html print
             (fun () ->
               aux ~prio_ctx:2 ~html print d12))
    | D (_v, DSeq items) ->
       xp_array ~delims:("〈#" ^ string_of_int (Array.length items) ^ ": ", "〉")
         (aux ~prio_ctx:2)
         ~html print items
    | D (v, DExpr) ->
       xp_html_elt "span" ~classe:"data-expr" ~html print
         (fun () ->
           xp_tuple1 ~delims:("{","}") xp_value ~html print v)
  in
  aux ~prio_ctx:2
  
let xp_dpat_default
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
