
open Madil_common

type ('value,'dconstr) data =
  | DVal of 'value * ('value,'dconstr) pattern
  | DSeq of int * ('value,'dconstr) data list (* inv: <int> = List.length <data list> *)
and ('value,'dconstr) pattern =
  | DNone
  | DPat of 'dconstr * ('value,'dconstr) data array

let make_dval (v : 'value) (dc : 'dconstr) (args : ('value,'dconstr) data array) : ('value,'dconstr) data =
  DVal (v, DPat (dc, args))
          
let xp_data
      (* TODO: html option *)
      (xp_value : 'value Xprint.xp)
      (xp_dconstr : 'dconstr Xprint.xp)
    : ('value,'dconstr) data Xprint.xp =
  let rec aux print d =
    match d with
    | DVal (v, DNone) -> xp_value print v
    | DVal (v, DPat (dc,args)) ->
       xp_dconstr print dc;
       Xprint.bracket ("[", "]")
         (Xprint.sep_array ", " aux)
         print args
    | DSeq (n,items) ->
       Xprint.bracket ("<" ^ string_of_int n ^ ": ", ">")
         (Xprint.sep_list ", " aux)
         print items
  in
  fun print d ->
  aux print d

