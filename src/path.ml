
open Madil_common
open Data
   
type 'dconstr path =
  | This
  | Field of 'dconstr * int * 'dconstr path

let xp_path
      (print_field : ('dconstr * int) Xprint.xp)
    : 'dconstr path Xprint.xp =
  let rec aux print p =
    match p with
    | This -> ()
    | Field (dc,i,p1) ->
       print#string ".";
       print_field print (dc,i)
  in
  fun print p ->
  print#string "^";
  aux print p

exception Invalid_field of string
  
let rec find (p : 'dconstr path) (d : ('value,'dconstr) data) : ('value,'dconstr) data result =
  match p with
  | This -> Result.Ok d
  | Field (dc,i,p1) ->
     ( match d with
     | DVal (v, DNone) -> Result.Error (Invalid_field "No pattern for value")
     | DVal (v, DPat (dc',args)) ->
        if dc' = dc && i >= 0 && i < Array.length args
        then find p1 args.(i)
        else Result.Error (Invalid_field "unexpected field")
     | DSeq (n, items) ->
        let| parts = list_map_result (find p1) items in
        Result.Ok (DSeq (n, parts)) )
