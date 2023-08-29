
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

type ('value,'dconstr,'var,'func) best_read =
  { matching : bool; (* matching flag *)
    read : ('value,'dconstr,'var,'func) Model.read; (* the selected best read *)
    new_data : ('value,'dconstr) Data.data } (* the new data *)

let best_reads_stats (best_reads : ('value,'dconstr,'var,'func) best_read list) : int * int = (* support, total *)
  List.fold_left
    (fun (supp,nb) best_read ->
      if best_read.matching
      then supp+1, nb+1
      else supp, nb+1)
    (0,0) best_reads

let inter_union_reads
      (get_rs : ('value,'dconstr,'var,'func) Model.read -> (('var,'constr,'func) Model.model * 'var Myseq.t * ('value,'dconstr) Data.data) list)
      (reads : ('value,'dconstr,'var,'func) Model.read list list)
    : (('var,'constr,'func) Model.model, 'var Myseq.t * ('value,'dconstr,'var,'func) best_read list) Mymap.t =
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
            (fun refs (r,varseq',data') ->
              if Mymap.mem r refs
              then refs
              else Mymap.add r (varseq', {matching = true; read; new_data = data'}) refs)
            refs refs_read)
        Mymap.empty reads in
    alt_read, refs
  in
  match List.rev reads with (* rev to have best_reads in right order at the end *)
  | [] -> assert false
  | example0_reads :: other_reads ->
     let alt_read0, refs0 = process_example example0_reads in
     let alt_reads = [alt_read0] in
     let refs = refs0 |> Mymap.map (fun (varseq', best_read) -> varseq', [best_read]) in
     let alt_reads, refs =
       List.fold_left
         (fun (alt_reads,refs) exampleI_reads ->
           let alt_readI, refsI = process_example exampleI_reads in
           let refs =
             Mymap.merge (* intersection(refs, refsI) *)
               (fun r varseq_best_reads_opt varseq_best_readI_opt ->
                 match varseq_best_reads_opt, varseq_best_readI_opt with
                 | Some (varseq, best_reads), Some (varseqI, best_readI) ->
                    Some (varseq, best_readI :: best_reads)
                 | Some (varseq, best_reads), None ->
                    Some (varseq, alt_readI :: best_reads)
                 | None, Some (varseqI, best_readI) ->
                    Some (varseqI, best_readI :: alt_reads)
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

let new_var (varseq : 'var Myseq.t) : 'var * 'var Myseq.t =
  match varseq () with
  | Myseq.Cons (x,varseq') -> x, varseq'
  | Myseq.Nil -> failwith "No more fresh variable (should be an infinite sequence"

type ('t,'value,'dconstr,'var,'constr,'func) refiner =
  nb_env_vars:int ->
  dl_M:dl -> (* current model DL *)
  (* NOTE: dl_M does not matter for ranking because an invariant of parsing and refinement *)
  't Kind.kind ->
  (('var,'constr,'func) Model.model as 'model) ->
  'var Myseq.t -> (* fresh variables viz the model *)
  ('value,'dconstr,'var,'func) Model.read list list ->
  ('constr Model.path * 'model (* refined submodel *) * int (* support *) * dl (* new DL *) * 'model (* new model *) * 'var Myseq.t (* remaining fresh vars *)) Myseq.t
(* result: a sequence of path-wise refinements with support and estimate DL *)
     
let refinements
      ~(xp_model : 'model html_xp)
      ~(alpha : float)
      ~(max_refinements : int)
      ~(asd : ('t,'constr,'func) Model.asd)
      ~(dl_model : nb_env_vars:int -> ('t Kind.kind as 'kind) -> (('var,'constr,'func) Model.model as 'model) -> dl)
      ~(dl_data : 'model -> (('value,'dconstr) Data.data as 'data) -> dl)
      ~(eval_parse_bests : 'kind -> 'model -> ('input,'value,'dconstr,'var) Model.eval_parse_bests)
      ~(refinements_pat : 'constr -> 'model array -> 'var Myseq.t -> 'data -> ('model * 'var Myseq.t * 'input) list) (* refined submodel with remaining fresh vars and related new parsing input *)
      ~(postprocessing : 'constr -> 'model array -> 'model -> supp:int -> nb:int -> alt:bool -> 'best_read list
                         -> ('model * 'best_read list) Myseq.t) (* converting refined submodel, alt mode (true if partial match), support, and best reads to a new model and corresponding new data *)
    (* TODO: abstract on this: maybe combine a filtering predicate, 
       and a globally-defined autorefinement process *)
    : ('t,'value,'dconstr,'var,'constr,'func) refiner =
  fun ~nb_env_vars ~dl_M k m varseq reads ->
  let rec aux ctx k m selected_reads other_reads_env =
  if selected_reads = [] then Myseq.empty
  else
    match k, m with
    | _, Model.Def (x,m1) ->
       aux ctx k m1 selected_reads other_reads_env
    | Kind.KVal t, Model.Pat (c,args) ->
       let k_args = asd#constr_args t c in
       Myseq.interleave
         (aux_pat ctx k m c args selected_reads
          :: Array.to_list
              (Array.mapi
                 (fun i mi ->
                   let ctxi = (fun p1 -> ctx (Model.Field (c,i,p1))) in
                   let ki = k_args.(i) in
                   aux ctxi ki mi
                     (map_reads
                        (fun read ->
                          match read.Model.data with
                          | DVal (_, DPat (dc, args)) ->
                             let di = try args.(i) with _ -> assert false in
                             {read with Model.data = di}
                          | _ -> assert false)
                        selected_reads)
                     other_reads_env)
                 args))
                        
    | _, Model.Expr e -> Myseq.empty
    | Kind.KSeq k1, Model.Seq (n,lm1) ->
       Myseq.interleave
         (List.mapi
            (fun i mi ->
              let ctxi = (fun p1 -> ctx (Model.Item (i,p1))) in
              aux ctxi k1 mi
                (map_reads
                   (fun read ->
                     match read.Model.data with
                     | DSeq (_,ld) -> {read with Model.data = List.nth ld i}
                     | _ -> assert false)
                   selected_reads)
                other_reads_env)
            lm1)
    | _, Model.Cst m1 -> raise TODO
    | _ -> assert false
  and aux_pat ctx k m c args selected_reads =
    let p = ctx Model.This in (* local path *)
    let dl_m = dl_model ~nb_env_vars k m in
    let dl_data_m = dl_data m in
    let refs =
      let refs_pat = refinements_pat c args varseq in
      fun (read : _ Model.read) ->
      match read.data with
      | DVal (v, DPat (dc, dargs)) as data ->
         let rs =
           List.filter_map
             (fun (m',varseq',input) ->
               match eval_parse_bests k m' read.bindings input with
               | Result.Ok ((data',dl')::_) -> Some (m',varseq',data')
               | _ -> None)
             (refs_pat data) in
         (match asd#expr_opt k with
          | None -> rs (* no expression here *)
          | Some k1 ->
             let es = Expr.Index.lookup v read.index in
             Myseq.fold_left
               (fun rs e -> (Model.Expr e, varseq, Data.DVal (v, Data.DNone)) :: rs)
               rs (Expr.exprset_to_seq es))
      | _ -> assert false in
    let post = postprocessing c args in
    let r_best_reads = inter_union_reads refs selected_reads in
    let* m', (varseq', best_reads) = Mymap.to_seq r_best_reads in
    let supp, nb = best_reads_stats best_reads in
    let alt = (supp < nb) in
    let* m_new, best_reads = post m' ~supp ~nb ~alt best_reads in
    let m_new, best_reads =
      (* TODO if alt then make_alt m_new m best_reads
      else*) m_new, best_reads in
    let dl_m_new = dl_model ~nb_env_vars k m_new in
    let dl_data_m_new = dl_data m_new in
    let dl_new =
      dl_M -. dl_m +. dl_m_new
      +. alpha *. Mdl.sum best_reads
                    (fun {matching; read; new_data} ->
                      read.dl -. dl_data_m read.data +. dl_data_m_new new_data) in
    Myseq.return (p, m_new, varseq', supp, dl_new)         
  in
  let selected_reads = reads in
  let other_reads_env = [] in
  let* p, r, varseq', supp, dl' =
    aux Model.ctx0 k m selected_reads other_reads_env
    |> Myseq.sort (fun (p1,r1,vs1,supp1,dl1) (p2,r2,vs2,supp2,dl2) ->
           dl_compare dl1 dl2) (* support use for sorting in LIS UI *)
    |> Myseq.unique
    |> Myseq.slice ~limit:max_refinements in
  let m' = Model.refine p r m in
  Myseq.return (p, r, supp, dl', m', varseq')


let task_refinements
      ~(binding_vars : ('var,'constr,'func) Model.model -> 'var Expr.binding_vars)
      ~(input_refinements : ('t,'value,'dconstr,'var,'constr,'func) refiner)
      ~(output_refinements : ('t,'value,'dconstr,'var,'constr,'func) refiner)
      
      (m : (('t,'var,'constr,'func) Task_model.task_model) as 'task_model)
      (prs : ('value,'dconstr,'var,'func) Task_model.pairs_reads)
      (dsri : ('value,'dconstr,'var,'func) Task_model.reads)
      (dsro : ('value,'dconstr,'var,'func) Task_model.reads)
    : (('var,'constr,'func) Task_model.refinement * 'task_model) Myseq.t =
  Myseq.concat (* TODO: rather order by estimated dl *)
    [ (let* p, ri, suppi, dli', mi, varseqi =
         input_refinements ~nb_env_vars:0 ~dl_M:prs.dl_mi
           m.input_kind m.input_model m.input_varseq dsri.reads in
       let nb_env_vars = Bintree.cardinal (binding_vars mi) in
       Myseq.return
         (Task_model.Rinput (p,ri,suppi,dli'),
          {m with input_model = mi; input_varseq = varseqi; nb_env_vars}));
      (let* p, ro, suppo, dlo', mo, varseqo =
         output_refinements ~nb_env_vars:m.nb_env_vars ~dl_M:prs.dl_mo
           m.output_kind m.output_model m.output_varseq dsro.reads in
       Myseq.return
         (Task_model.Routput (p,ro,suppo,dlo'),
          {m with output_model = mo; output_varseq = varseqo})) ]

let task_prunings
      ~(input_prunings : ('t,'value,'dconstr,'var,'constr,'func) refiner)
      
      (m : (('t,'var,'constr,'func) Task_model.task_model as 'task_model))
      (dsri : ('value,'dconstr,'var,'func) Task_model.reads)
    : (('var,'constr,'func) Task_model.refinement * 'task_model) Myseq.t =
  let* pi, ri, suppi, dli', mi', varseqi' =
    input_prunings ~nb_env_vars:0 ~dl_M:dsri.dl_m
      m.input_kind m.input_model m.input_varseq dsri.reads in
  Myseq.return
    (Task_model.Rinput (pi,ri,suppi,dli'),
     {m with input_model = mi'; input_varseq = varseqi'})

