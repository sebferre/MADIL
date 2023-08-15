
open Madil_common
open Data
open Kind
   
type 'constr path =
  | This
  | Field of 'constr * int * 'constr path
  | Item of int * 'constr path

type 'constr binding_paths = 'constr path Bintree.t
let binding_paths0 = Bintree.empty

type ('value,'constr) bindings = ('constr path, 'value) Mymap.t
let bindings0 = Mymap.empty

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
  fun ~html print p ->
  print#string "^";
  aux ~html print p

(*
exception Invalid_field of string
exception Invalid_item of int
  
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
  | Item (i,p1) ->
     ( match d with
       | DVal _ -> Result.Error (Invalid_item i)
       | DSeq (n, items) ->
          if i >=0 && i < n
          then find p1 (try List.nth items i with _ -> assert false)
          else Result.Error (Invalid_item i))
 *)

