
open Madil_common

type ('value,'dconstr) data = (* data according to model, must be self-contained for encoding *)
  D of 'value * ('value,'dconstr) data_model
and ('value,'dconstr) data_model =
  | DPat of 'dconstr * ('value,'dconstr) data array
  | DAlt of float (* prob *) * bool * ('value,'dconstr) data (* the bool indicates which branch was chosen *)
  | DSeq of int * Range.t * ('value,'dconstr) data array (* inv: <int> = Array.length <data array> *)

(* TODO: consider adding DNil as nil data, for use as nil env *)

let value (d : ('value,'dconstr) data) : 'value =
  match d with
  | D (v, _) -> v

let make_dpat (value : 'value) (dc : 'dconstr) (args : ('value,'dconstr) data array) : ('value,'dconstr) data =
  D (value, DPat (dc, args))
let make_dseq (value : 'value) (range : Range.t) (ds : ('value,'dconstr) data array) : ('value,'dconstr) data =
  let n = Array.length ds in
  D (value, DSeq (n,range,ds))
          
let xp_data
      ~(xp_dpat : 'dconstr -> unit html_xp array -> unit html_xp)
    : ('value,'dconstr) data html_xp =
  let rec aux ~prio_ctx ~html print d =
    match d with
    | D (_v, DPat (dc,args)) ->
       let xp_args =
         Array.map
           (fun arg -> (fun ~html print () -> aux ~prio_ctx:0 ~html print arg))
           args in
       xp_dpat dc xp_args ~html print ()
    | D (_v, DAlt (_prob,_b,d12)) ->
       xp_brackets_prio ~prio_ctx ~prio:2 ~html print
         (fun () ->
           if html then print#string "<div class=\"data-alt\">";
           aux ~prio_ctx:2 ~html print d12;
           if html then print#string "</div>")
    | D (_v, DSeq (n,_range,items)) ->
       xp_array ~delims:("〈" ^ string_of_int n ^ ": ", "〉")
         (aux ~prio_ctx:2)
         ~html print items
  in
  aux ~prio_ctx:2
  
let xp_dpat_default
      ~(xp_dconstr : 'dconstr html_xp)
      
      (dc : 'dconstr) (xp_args : unit html_xp array) : unit html_xp =
  fun ~html print () ->
  xp_dconstr ~html print dc;
  if xp_args <> [||] then (
    print#string "[";
    Array.iteri
      (fun i xp_argi ->
        if i > 0 then print#string ", ";
        xp_argi ~html print ())
      xp_args;
    print#string "]"
  )
