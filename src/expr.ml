
open Madil_common
open Data
open Path

type ('dconstr,'func) expr =
  | Ref of 'dconstr path
  | Apply of 'func * ('dconstr,'func) expr array


let xp_expr
      (print_field : ('dconstr * int) Xprint.xp)
      (print_func : 'func Xprint.xp)
    : ('dconstr,'func) expr Xprint.xp =
  let rec aux print e =
    match e with
    | Ref p -> xp_path print_field print p
    | Apply (f,args) ->
       print_func print f;
       Xprint.bracket ("(",")")
         (Xprint.sep_array ", " aux)
         print args
  in
  fun print e ->
  Xprint.bracket ("{","}") aux
    print e
