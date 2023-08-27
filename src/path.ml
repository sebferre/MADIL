
open Madil_common
   
type 'constr path =
  | This
  | Field of 'constr * int * 'constr path
  | Item of int * 'constr path

let xp_path
      ~(xp_field : ('constr * int) html_xp)
    : 'constr path html_xp =
  let rec aux ~html print p =
    match p with
    | This -> ()
    | Field (c,i,p1) ->
       print#string ".";
       xp_field ~html print (c,i);
       aux ~html print p1
    | Item (i,p1) ->
       print#string "["; print#int i; print#string "]";
       aux ~html print p1
  in
  aux
