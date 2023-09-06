
open Madil_common

type 't kind =
  | KBool
  | KVal of 't
  | KSeq of 't kind

type 't signature = { res : 't kind; args : 't kind array }

let xp_kind
      ~(xp_type : 't html_xp)
    : 't kind html_xp =
  let rec aux ~html print = function
    | KBool -> print#string "bool"
    | KVal t -> xp_type ~html print t
    | KSeq k1 -> aux ~html print k1; print#string "+"
  in
  aux

let xp_signature
      ~(xp_type : 't html_xp)
    : 't signature html_xp =
  fun ~html print {res; args} ->
  xp_kind ~xp_type ~html print res;
  Xprint.bracket ("(", ")")
    (Xprint.sep_array ", " (xp_kind ~xp_type ~html))
    print args

