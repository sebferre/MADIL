
open Madil_common

type 't kind =
  | KVal of 't
  | KSeq of 't kind

type 't signature = { res : 't kind; args : 't kind array }

let xp_kind
      (xp_type : 't Xprint.xp)
    : 't kind Xprint.xp =
  let rec aux print = function
    | KVal t -> xp_type print t
    | KSeq k1 -> aux print k1; print#string "+"
  in
  aux

let xp_signature
      (xp_type : 't Xprint.xp)
    : 't signature Xprint.xp =
  let xp_k = xp_kind xp_type in
  fun print {res; args} ->
  xp_k print res;
  Xprint.bracket ("(", ")")
    (Xprint.sep_array ", " xp_k)
    print args

