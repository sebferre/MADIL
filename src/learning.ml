
open Madil_common

(* computing model refinements from parsing data *)
   
let map_reads (f : 'a -> 'b) (reads : 'a list list) : 'b list list  =
  List.map
    (fun example_reads ->
      List.map f example_reads)
    reads

let partition_map_reads (f : 'a -> ('b,'c) Result.t) (selected_reads : 'a list list) (other_reads : 'c list list) : 'b list list * 'c list list =
  (* returns: 1) the result of applying [f] on [selected_reads] when [f] is defined, 
     and 2) the complement part of [selected_reads] to [others] *)
  list_partition_map
    (fun example_reads ->
      let defined_example_reads, example_reads_env =
        list_partition_map f example_reads [] in
      if defined_example_reads = []
      then Result.Error example_reads_env
      else Result.Ok defined_example_reads)
    selected_reads
    other_reads

type ('value,'dconstr,'constr,'func) best_read =
  { matching : bool; (* matching flag *)
    read : ('value,'dconstr,'constr,'func) Model.read; (* the selected best read *)
    new_data : ('value,'dconstr) Data.data } (* the new data *)

let best_reads_stats (best_reads : ('value,'dconstr,'constr,'func) best_read list) : int * int = (* support, total *)
  List.fold_left
    (fun (supp,nb) best_read ->
      if best_read.matching
      then supp+1, nb+1
      else supp, nb+1)
    (0,0) best_reads

let inter_union_reads
      (get_rs : ('value,'dconstr,'constr,'func) Model.read -> (('constr,'func) Model.model * ('value,'dconstr) Data.data) list)
      (reads : ('value,'dconstr,'constr,'func) Model.read list list)
    : (('constr,'func) Model.model, ('value,'dconstr,'constr,'func) best_read list) Mymap.t =
  (* given a function extracting refinements (submodels) from each read,
     return a set of such refinements, each mapped to the dl-shortest reads supporting it, along with new data *)
  let process_example reads =
    assert (reads <> []);
    let read0 = List.hd reads in
    let alt_read = {matching = false; read = read0; new_data = read0.Model.data} in
    let refs =
      List.fold_left
        (fun refs read ->
          let refs_read = get_rs read in
          List.fold_left (* union(refs, refs_read) *)
            (fun refs (r,data') ->
              if Mymap.mem r refs
              then refs
              else Mymap.add r {matching = true; read; new_data = data'} refs)
            refs refs_read)
        Mymap.empty reads in
    alt_read, refs
  in
  match List.rev reads with (* rev to have best_reads in right order at the end *)
  | [] -> assert false
  | example0_reads :: other_reads ->
     let alt_read0, refs0 = process_example example0_reads in
     let alt_reads = [alt_read0] in
     let refs = refs0 |> Mymap.map (fun best_read -> [best_read]) in
     let alt_reads, refs =
       List.fold_left
         (fun (alt_reads,refs) exampleI_reads ->
           let alt_readI, refsI = process_example exampleI_reads in
           let refs =
             Mymap.merge (* intersection(refs, refsI) *)
               (fun r best_reads_opt best_readI_opt ->
                 match best_reads_opt, best_readI_opt with
                 | Some best_reads, Some best_readI -> Some (best_readI :: best_reads)
                 | Some best_reads, None -> Some (alt_readI :: best_reads)
                 | None, Some best_readI -> Some (best_readI :: alt_reads)
                 | _ -> None)
               refs refsI in
           let alt_reads = alt_readI :: alt_reads in
           alt_reads, refs)
         (alt_reads, refs) other_reads in
     refs

(* to include with Alt
let extend_partial_best_reads 
      (selected_reads : (('value,'dconstr,'constr,'func) Model.read as 'read) list list)
      (best_reads : (('value,'dconstr,'constr,'func) best_read as 'best_read) list)
      (check_alt_read : 'read -> ('read * ('value,'dconstr) Data.data) option)
    : 'best_read list =
  List.map2
    (fun reads best_read ->
      if best_read.matching
      then best_read (* already matches some refinement *)
      else
        (match List.find_map check_alt_read reads with
         | Some (best_read', data') ->
            {matching = true; read = best_read'; new_data = data'} (* new match *)
         | None -> best_read)) (* no change *)
    selected_reads best_reads

let make_alt
      (m1 : (('constr,'func) Model.model as 'model))
      (m2 : 'model)
      (best_reads : (('value,'dconstr,'constr,'func) best_read as 'best_read) list)
    : 'model * 'best_read list =
  (* making an alternative, model and data *)
  let m' = Alt (Undet, m1, m2) in
  let best_reads' =
    List.map
      (fun {matching, read, data} ->
        {matching; read; new_data = DAlt (matching, data)})
      best_reads in
  m', best_reads'
 *)

let refinements
      ~(asd : ('t,'constr,'func) Model.asd)
      ~(dl_model : ('t Kind.kind as 'kind) -> (('constr,'func) Model.model as 'model) -> dl)
      ~(dl_data : 'model -> (('value,'dconstr) Data.data as 'data) -> dl)
      ~(parseur_bests : 'model -> ('input,'value,'dconstr) Model.parseur_bests)
      ~(refinements_pat : 'constr -> 'model array -> 'data -> ('model * 'input) list) (* refined submodel with related new local data *)
      ~(postprocessing : 'constr -> 'model array -> 'model -> supp:int -> nb:int -> alt:bool -> 'best_read list
                         -> ('model * 'best_read list) Myseq.t) (* converting refined submodel, alt mode (true if partial match), support, and best reads to a new model and corresponding new data *)
      (* TODO: abstract on this: maybe combine a filtering predicate, 
         and a globally-defined autorefinement process *)

      ~(alpha : float)
      ~(max_refinements : int)
      
      ~(dl_M : dl) (* NOTE: dl_M does not matter for ranking because an invariant of parsing and refinement *)
      (k : 'kind)
      (m : 'model) (* local model at some path *)
      (reads : 'read list list) (* local data with read information *)
    : ('path * 'model (* refinement *) * int (* support *) * dl (* new DL *) * 'model (* new model*)) Myseq.t (* result: a sequence of path-wise refinements with support and estimate DL *) =
  let rec aux k m selected_reads other_reads_env =
  if selected_reads = [] then Myseq.empty
  else
    match k, m with
    | Kind.KVal t, Model.Pat (c,args) ->
       let k_args = asd#constr_args t c in
       Myseq.interleave
         (aux_pat k c args selected_reads
          :: Array.to_list
              (Array.mapi
               (fun i mi ->
                 aux k_args.(i) mi
                   (map_reads
                      (fun read ->
                        match read.Model.data with
                        | DVal (_, DPat (dc, args)) ->
                           let di = try args.(i) with _ -> assert false in
                           {read with Model.data = di}
                        | _ -> assert false)
                      selected_reads)
                   other_reads_env
                 |> Myseq.map (fun (p,r,supp,dl') -> Path.Field (c,i,p), r, supp, dl'))
               args))
                        
    | _, Model.Expr e -> Myseq.empty
    | Kind.KSeq k1, Model.Seq (n,lm1) ->
       Myseq.interleave
         (List.mapi
            (fun i mi ->
              aux k1 mi
                (map_reads
                   (fun read ->
                     match read.Model.data with
                     | DSeq (_,ld) -> {read with Model.data = List.nth ld i}
                     | _ -> assert false)
                   selected_reads)
                other_reads_env
              |> Myseq.map (fun (p,r,supp,dl') -> Path.Item (i,p), r, supp, dl'))
            lm1)
    | _, Model.Cst m1 -> raise TODO
    | _ -> assert false
  and aux_pat k c args selected_reads =
    let dl_m = dl_model k m in
    let dl_data_m = dl_data m in
    let refs =
      let refs_pat = refinements_pat c args in
      fun (read : _ Model.read) ->
      match read.data with
      | DVal (v, DPat (dc, dargs)) as data ->
         let rs =
           List.filter_map
             (fun (m',x) ->
               match parseur_bests m' x with
               | Result.Ok ((data',dl')::_) -> Some (m',data')
               | _ -> None)
             (refs_pat data) in
         (match asd#expr_opt k with
          | None -> rs (* no expression here *)
          | Some k1 ->
             let es = Expr.Index.lookup v read.index in
             Myseq.fold_left
               (fun rs e -> (Model.Expr e, Data.DVal (v, Data.DNone)) :: rs)
               rs (Expr.exprset_to_seq es))
      | _ -> assert false in
    let post = postprocessing c args in
    let r_best_reads = inter_union_reads refs selected_reads in
    let* m', best_reads = Mymap.to_seq r_best_reads in
    let supp, nb = best_reads_stats best_reads in
    let alt = (supp < nb) in
    let* m_new, best_reads = post m' ~supp ~nb ~alt best_reads in
    let m_new, best_reads =
      (* TODO if alt then make_alt m_new m best_reads
      else*) m_new, best_reads in
    let dl_m_new = dl_model k m_new in
    let dl_data_m_new = dl_data m_new in
    let dl_new =
      dl_M -. dl_m +. dl_m_new
      +. alpha *. Mdl.sum best_reads
                    (fun {matching; read; new_data} ->
                      read.dl -. dl_data_m read.data +. dl_data_m_new new_data) in
    Myseq.return (Path.This, m_new, supp, dl_new)         
  in
  let selected_reads = reads in
  let other_reads_env = [] in
  let* p, r, supp, dl' =
    aux k m selected_reads other_reads_env
    |> Myseq.sort (fun (p1,r1,supp1,dl1) (p2,r2,supp2,dl2) ->
           dl_compare dl1 dl2) (* support use for sorting in LIS UI *)
    |> Myseq.unique
    |> Myseq.slice ~limit:max_refinements in
  let m' = Model.refine p r m in
  Myseq.return (p, r, supp, dl', m')

