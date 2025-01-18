
open Madil_common

type ('value,'distrib,'constr) data = (* data according to model, must be self-contained for encoding *)
  | DAny of 'value * 'distrib (* bare value, and an enriched form of value often coming with some range constraint for DL computing *)
  | DPat of 'value * 'constr * 'value array * ('value,'distrib,'constr) data array
  | DAlt of float (* prob *) * bool * ('value,'distrib,'constr) data (* the bool indicates which branch was chosen *)
  | DExpr of 'value (* computed value *)

(* TODO: consider adding DNil as nil data, for use as nil env *)

let rec value (d : ('value,'distrib,'constr) data) : 'value =
  match d with
  | DAny (v,_) -> v
  | DPat (v,_,_,_) -> v
  | DAlt (prob,b,d) -> value d
  | DExpr v -> v (* TODO: consider including the expression *)

let make_dany (value : 'value) (distrib : 'distrib) : ('value,'distrib,'constr) data =
  DAny (value, distrib) [@@inline]
let make_dpat (value : 'value) (c : 'constr) ?(src : 'value array = [||]) (args : ('value,'distrib,'constr) data array) : ('value,'distrib,'constr) data =
  DPat (value, c, src, args) [@@inline]
let make_dexpr (value : 'value) : ('value,'distrib,'constr) data =
  DExpr value [@@inline]
 
let xp_data
      ~(xp_value : 'value html_xp)
      ~(xp_distrib : 'distrib html_xp)
      ~(xp_pat : 'constr -> unit html_xp array -> unit html_xp array -> unit html_xp)
    : ('value,'distrib,'constr) data html_xp =
  let rec aux ~prio_ctx ~html print d =
    match d with
    | DAny (v,r) ->
       xp_html_elt "span" ~classe:"data-any" ~html print
         (fun () ->
           xp_value ~html print v;
           print#string " ~ ";
           xp_distrib ~html print r)
    | DPat (v,c,src,args) ->
       let xp_src =
         Array.map
           (fun v -> (fun ~html print () -> xp_value ~html print v))
           src in
       let xp_args =
         Array.map
           (fun arg -> (fun ~html print () -> aux ~prio_ctx:0 ~html print arg))
           args in
       xp_pat c xp_src xp_args ~html print ()
    | DAlt (_prob,b,d12) ->
       xp_brackets_prio ~prio_ctx ~prio:2 ~html print
         (fun () ->
           xp_html_elt "div" ~classe:"data-alt" ~html print
             (fun () ->
               print#string (if b then "T " else "F ");
               aux ~prio_ctx:2 ~html print d12))
    | DExpr v ->
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
