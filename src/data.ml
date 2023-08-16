
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
      ~(xp_dconstr : 'dconstr html_xp)
    : ('value,'dconstr) data html_xp =
  let rec aux ~html print d =
    match d with
    | DVal (v, DNone) -> xp_value ~html print v
    | DVal (v, DPat (dc,args)) ->
       xp_dconstr ~html print dc;
       if args <> [||] then
         Xprint.bracket ("[", "]")
           (Xprint.sep_array ", " (aux ~html))
           print args
    | DSeq (n,items) ->
       Xprint.bracket ("〈" ^ string_of_int n ^ ": ", "〉")
         (Xprint.sep_list ", " (aux ~html))
         print items
  in
  aux
