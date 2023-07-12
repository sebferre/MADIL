
open Madil_common
open Data
open Kind
   
type 'constr path =
  | This
  | Field of 'constr * int * 'constr path
  | Item of int * 'constr path

type ('value,'constr) bindings = ('constr path * 'value) list
let bindings0 = []

let xp_path
      (xp_field : ('constr * int) Xprint.xp)
    : 'constr path Xprint.xp =
  let rec aux print p =
    match p with
    | This -> ()
    | Field (c,i,p1) ->
       print#string ".";
       xp_field print (c,i);
       aux print p1
    | Item (i,p1) ->
       print#string "["; print#int i; print#string "]";
       aux print p1
  in
  fun print p ->
  print#string "^";
  aux print p

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
  
let kind
      ~(t_field : 't -> 'constr -> int -> 't)
    : 't kind -> 'constr path -> 't kind =
  let rec aux k p =
    match k, p with
    | _, This -> k
    | KVal t, Field (c,i,p1) ->
       let t1 = t_field t c i in
       let k1 = KVal t1 in
       aux k1 p1
    | KSeq k1, Item (i,p1) -> aux k1 p1
    | _ -> assert false
  in
  aux
