
open Madil_common

type ('value,'dconstr) data =
  | DVal of 'value * ('value,'dconstr) pattern
  | DSeq of int * ('value,'dconstr) data list (* inv: <int> = List.length <data list> *)
and ('value,'dconstr) pattern =
  | DNone
  | DPat of 'dconstr * ('value,'dconstr) data array

(* TODO: consider adding DNil as nil data, for use as nil env *)

let make_dval (v : 'value) (dc : 'dconstr) (args : ('value,'dconstr) data array) : ('value,'dconstr) data =
  DVal (v, DPat (dc, args))
          
let xp_data
      ~(xp_value : 'value html_xp)
      ~(xp_dpat : 'dconstr -> unit html_xp array -> unit html_xp)
    : ('value,'dconstr) data html_xp =
  let rec aux ~html print d =
    match d with
    | DVal (v, DNone) -> xp_value ~html print v
    | DVal (v, DPat (dc,args)) ->
       let xp_args =
         Array.map
           (fun arg -> (fun ~html print () -> aux ~html print arg))
           args in
       xp_dpat dc xp_args ~html print ()
    | DSeq (n,items) ->
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
