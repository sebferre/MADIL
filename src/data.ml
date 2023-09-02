
open Madil_common

type ('value,'dconstr) data =
  D of 'value * ('value,'dconstr) data_model
and ('value,'dconstr) data_model =
  | DNone
  | DPat of 'dconstr * ('value,'dconstr) data array
  | DSeq of int * ('value,'dconstr) data list (* inv: <int> = List.length <data list> *)

(* TODO: consider adding DNil as nil data, for use as nil env *)

let value (d : ('value,'dconstr) data) : 'value =
  match d with
  | D (v, _) -> v

let make_dval (value : 'value) : ('value,'dconstr) data =
  D (value, DNone)
let make_dpat (value : 'value) (dc : 'dconstr) (args : ('value,'dconstr) data array) : ('value,'dconstr) data =
  D (value, DPat (dc, args))
          
let xp_data
      ~(xp_value : 'value html_xp)
      ~(xp_dpat : 'dconstr -> unit html_xp array -> unit html_xp)
    : ('value,'dconstr) data html_xp =
  let rec aux ~html print d =
    match d with
    | D (v, DNone) -> xp_value ~html print v
    | D (_v, DPat (dc,args)) ->
       let xp_args =
         Array.map
           (fun arg -> (fun ~html print () -> aux ~html print arg))
           args in
       xp_dpat dc xp_args ~html print ()
    | D (_v, DSeq (n,items)) ->
       Xprint.bracket ("〈" ^ string_of_int n ^ ": ", "〉")
         (Xprint.sep_list ", " (aux ~html))
         print items
  in
  aux
  
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
