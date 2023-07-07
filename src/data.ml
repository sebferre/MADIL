
open Madil_common

type constr = string
   
type ('value,'dconstr) data =
  | DVal of 'value * ('value,'dconstr) pattern
  | DSeq of int * ('value,'dconstr) data list (* inv: <int> = List.length <data list> *)
and ('value,'dconstr) pattern =
  | DNone
  | DPat of 'dconstr * ('value,'dconstr) data array

let xp_data
      (* TODO: html option *)
      (print_value : 'value Xprint.xp)
      (print_dconstr : 'dconstr Xprint.xp)
    : ('value,'dconstr) data Xprint.xp =
  let rec aux print d =
    match d with
    | DVal (v, DNone) -> print_value print v
    | DVal (v, DPat (dc,args)) ->
       print_dconstr print dc;
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

