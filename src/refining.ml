
open Madil_common

(* computing model refinements from parsing data *)
   
let map_reads (f : 'read -> 'read) (reads : ('read list * bool) list) : ('read list * bool) list  =
  List.map
    (fun (example_reads, unselected_reads) ->
      List.map f example_reads, unselected_reads)
    reads

let filter_map_reads (f : 'read -> 'read option) (selected_reads : ('read list * bool) list) : ('read list * bool) list =
  (* returns: the result of applying [f] on [selected_reads] when [f] is defined *)
  List.filter_map
    (fun (example_reads, unselected_reads) ->
      let defined_example_reads, undefined_reads =
        List.partition_map
          (fun read ->
            match f read with
            | Some defined_read -> Either.Left defined_read
            | None -> Either.Right ())
          example_reads in
      if defined_example_reads = []
      then None
      else Some (defined_example_reads, unselected_reads || undefined_reads <> []))
    selected_reads

type ('value,'dconstr,'var,'func) best_read =
  { unselected_reads : bool; (* flag for out-of-branch alt reads *)
    matching : bool; (* matching flag *)
    read : ('value,'dconstr,'var,'func) Model.read; (* the selected best read, first one when matching=false *)
    new_data : ('value,'dconstr) Data.data } (* the new data, the old data when matching=false *)

let best_reads_stats (best_reads : ('value,'dconstr,'var,'func) best_read list) : int * int = (* support, total *)
  List.fold_left
    (fun (supp,nb) best_read ->
      if best_read.matching then supp+1, nb+1 (* positive *)
      else if best_read.unselected_reads then supp, nb (* out of scope *)
      else supp, nb+1) (* negative *)
    (0,0) best_reads

let inter_union_reads
      (get_rs : ('value,'dconstr,'var,'func) Model.read -> ('ref * 'var Myseq.t * ('value,'dconstr) Data.data) list)
      (reads : (('value,'dconstr,'var,'func) Model.read list * bool) list)
    : ('ref, 'var Myseq.t * ('value,'dconstr,'var,'func) best_read list) Mymap.t =
  (* given a function extracting refinements (submodels) from each read,
     return a set of such refinements, each mapped to the dl-shortest reads supporting it, along with new data *)
  let process_example reads unselected_reads =
    assert (reads <> []);
    let read0 = List.hd reads in
    let alt_read = {unselected_reads; matching = false; read = read0; new_data = read0.Model.data} in
    let refs =
      List.fold_left
        (fun refs read ->
          let refs_read = get_rs read in
          List.fold_left (* union(refs, refs_read) *)
            (fun refs (r,varseq',data') ->
              if Mymap.mem r refs
              then refs
              else Mymap.add r (varseq', {unselected_reads; matching = true; read; new_data = data'}) refs)
            refs refs_read)
        Mymap.empty reads in
    alt_read, refs
  in
  match List.rev reads with (* rev to have best_reads in right order at the end *)
  | [] -> assert false
  | (example0_reads, example0_unselected_reads) :: other_reads ->
     let alt_read0, refs0 = process_example example0_reads example0_unselected_reads in
     let alt_reads = [alt_read0] in
     let refs = refs0 |> Mymap.map (fun (varseq', best_read) -> varseq', [best_read]) in
     let alt_reads, refs = (* TODO: is alt_read(s) necessary here? *)
       List.fold_left
         (fun (alt_reads,refs) (exampleI_reads, exampleI_unselected_reads) ->
           let alt_readI, refsI = process_example exampleI_reads exampleI_unselected_reads in
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

let extend_partial_best_reads
      (selected_reads : ((('value,'dconstr,'var,'func) Model.read as 'read) list * bool) list)
      (best_reads : (('value,'dconstr,'var,'func) best_read as 'best_read) list)
      (check_alt_read : 'read -> ('read * ('value,'dconstr) Data.data) option)
    : 'best_read list =
  List.map2
    (fun (reads, unselected_reads) best_read ->
      if best_read.matching
      then best_read (* already matches some refinement *)
      else
        (match List.find_map check_alt_read reads with
         | Some (best_read', data') ->
            {unselected_reads = best_read.unselected_reads;
             matching = true; read = best_read'; new_data = data'} (* new match *)
         | None -> best_read)) (* no change *)
    selected_reads best_reads

let new_var (varseq : 'var Myseq.t) : 'var * 'var Myseq.t =
  match varseq () with
  | Myseq.Cons (x,varseq') -> x, varseq'
  | Myseq.Nil -> failwith "No more fresh variable (should be an infinite sequence"

let make_alt_if_allowed_and_needed
      ~(allowed : bool) ~(nb : int) ~(supp : int)
      (m_true : (('typ,'var,'const,'func) Model.model as 'model))
      (m_false : 'model)
      (varseq : 'var Myseq.t)
      (best_reads : (('value,'dconstr,'var,'func) best_read as 'best_read) list)
    : ('model * 'var Myseq.t * 'best_read list) Myseq.t =
  if supp = nb then (* no need for alternative *)
    Myseq.return (m_true, varseq, best_reads)
  else if allowed then
    (* making an alternative, model and data *)
    let xc, varseq' = new_var varseq in
    let prob = float supp /. float nb in
    let m' = Model.Alt (xc, Undet prob, m_true, m_false) in
    let best_reads' =
      List.map
        (fun {unselected_reads; matching; read; new_data} ->
          let prob = if matching then prob else 1. -. prob in
          let new_data = Data.D (Data.value new_data, DAlt (prob, matching, new_data)) in
          {unselected_reads; matching; read; new_data})
        best_reads in
    Myseq.return (m', varseq', best_reads')
  else (* alt not allowed *)
    Myseq.empty

type ('typ,'value,'dconstr,'var,'constr,'func) refiner =
  nb_env_vars:int ->
  dl_M:dl -> (* current model DL *)
  (* NOTE: dl_M does not matter for ranking because an invariant of parsing and refinement *)
  (('typ,'var,'constr,'func) Model.model as 'model) ->
  'var Myseq.t -> (* fresh variables viz the model *)
  ('value,'dconstr,'var,'func) Model.read list list
  -> ('constr Model.path (* refinement location *)
      * 'model (* refined submodel *)
      * int (* support *)
      * dl (* new DL *)
      * 'model (* new model, after applying refinement *)
      * 'var Myseq.t (* remaining fresh vars *)
     ) Myseq.t
  (* result: a sequence of path-wise refinements with support and estimate DL *)

let refinements
      ~(xp_model : 'model html_xp)
      ~(alpha : float)
      ~(max_refinements : int)
      ~(asd : ('typ,'constr,'func) Model.asd)
      ~(data_of_value : 'typ -> 'value -> 'data result)
      ~(value_of_bool : bool -> 'value)
      ~(dl_model : nb_env_vars:int -> (('typ,'var,'constr,'func) Model.model as 'model) -> dl)
      ~(dl_data : (('value,'dconstr) Data.data as 'data) -> dl)
      ~(eval_parse_bests : 'model -> ('input,'value,'dconstr,'var) Model.eval_parse_bests)
      ~(refinements_pat : 'typ -> 'constr -> 'model array -> ('var Myseq.t as 'varseq) -> 'data -> ('model * 'var Myseq.t * 'input) list) (* refined submodel with remaining fresh vars and related new parsing input *)
      ~(postprocessing : 'typ -> 'constr -> 'model array -> 'model -> supp:int -> nb:int -> alt:bool -> 'best_read list
                         -> ('model * 'best_read list) Myseq.t) (* converting refined submodel, alt mode (true if partial match), support, and best reads to a new model and corresponding new data *)
    : ('typ,'value,'dconstr,'var,'constr,'func) refiner =
  fun ~nb_env_vars ~dl_M m0 varseq0 reads ->
  let aux_gen (type r)
        ctx m selected_reads
        (read_refs : 'read -> (r * 'varseq * 'data) list)
        (postprocessing : r -> 'varseq -> supp:int -> nb:int -> alt:bool -> 'best_reads -> ('model * 'varseq * 'best_reads) Myseq.t)
      : ('path * 'model * 'varseq * int * dl) Myseq.t =
    let p = ctx Model.This in (* local path *)
    let dl_m = dl_model ~nb_env_vars m in
    let r_best_reads = inter_union_reads read_refs selected_reads in
    let* r, (varseq', best_reads) = Mymap.to_seq r_best_reads in
    let supp, nb = best_reads_stats best_reads in
    let alt = (supp < nb) in
    let* m_new, varseq', best_reads = postprocessing r varseq' ~supp ~nb ~alt best_reads in
    let dl_m_new = dl_model ~nb_env_vars m_new in
    let dl_new =
      dl_M -. dl_m +. dl_m_new
      +. alpha *. Mdl.sum best_reads
                    (fun {matching; read; new_data} ->
                      if matching
                      then
                        let dl_d = dl_data read.data in
                        let dl_d_new = dl_data new_data in
                        read.dl -. dl_d +. dl_d_new
                      else 0.) (* no change in this case *) in
    let dl_new = dl_round dl_new in (* rounding to absorb float error accumulation *)
    Myseq.return (p, m_new, varseq', supp, dl_new)
  in
  let rec aux ctx m selected_reads =
  if selected_reads = [] then Myseq.empty
  else
    match m with
    | Model.Def (x,m1) ->
       aux ctx m1 selected_reads
    | Model.Pat (t,c,args) ->
       Myseq.interleave
         (aux_expr ctx m selected_reads
          :: aux_pat ctx m t c args selected_reads
          :: Array.to_list
              (Array.mapi
                 (fun i mi ->
                   let ctxi = (fun p1 -> ctx (Model.Field (c,i,p1))) in
                   aux ctxi mi
                     (map_reads
                        (fun read ->
                          match read.Model.data with
                          | D (_, DPat (dc, args)) ->
                             let di = try args.(i) with _ -> assert false in
                             {read with Model.data = di}
                          | _ -> assert false)
                        selected_reads))
                 args))
    | Model.Fail -> assert false
    | Model.Alt (xc,c,m1,m2) ->
       Myseq.interleave
         [ aux_expr ctx m selected_reads;
           
           (match c with
            | Undet _ ->
               Myseq.concat
                 [ aux_alt_cond_undet ctx m xc c m1 m2 selected_reads;
                   aux_alt_prune ctx m m1 m2 selected_reads ]
            | True | False -> assert false
            | BoolExpr _ -> Myseq.empty);
           
           (let ctx1 = (fun p1 -> ctx (Model.Branch (true,p1))) in
            let sel1 =
              filter_map_reads
                (fun (read : _ Model.read) ->
                  match read.data with
                  | D (_, DAlt (prob,b,d12)) ->
                     if b
                     then Some {read with data=d12}
                     else None
                  | _ -> assert false)
                selected_reads in
            aux ctx1 m1 sel1);
                        
           (let ctx2 = (fun p1 -> ctx (Model.Branch (false,p1))) in
            let sel2 =
              filter_map_reads
                (fun (read : _ Model.read) ->
                  match read.data with
                  | D (_, DAlt (prob,b,d12)) ->
                     if not b
                     then Some {read with data=d12}
                     else None
                  | _ -> assert false)
                selected_reads in
            aux ctx2 m2 sel2) ]
                        
    | Model.Seq (n,k1,lm1) ->
       Myseq.interleave
         (List.mapi
            (fun i mi ->
              let ctxi = (fun p1 -> ctx (Model.Item (i,p1))) in
              aux ctxi mi
                (map_reads
                   (fun read ->
                     match read.Model.data with
                     | D (_, DSeq (_,ld)) -> {read with Model.data = List.nth ld i}
                     | _ -> assert false)
                   selected_reads))
            lm1)
    | Model.Cst m1 -> raise TODO
    | Model.Expr (k,e) -> Myseq.empty
  and aux_expr ctx m selected_reads =
    let t = Model.typ m in
    match asd#expr_opt t with
    | None -> Myseq.empty (* no expression here *)
    | Some t1 ->
       let allowed = asd#alt_opt t in
       aux_gen ctx m selected_reads
         (fun (read : _ Model.read) ->
           let v = Data.value read.data in
           match data_of_value t v with (* new data for an expression *)
           | Result.Ok dv ->
              let es = Expr.Index.lookup v (Lazy.force read.lazy_index) in
              Myseq.fold_left
                (fun rs e -> (e, varseq0, dv) :: rs)
                [] (Expr.Exprset.to_seq es)
           | Result.Error _ -> assert false)
         (fun e varseq' ~supp ~nb ~alt best_reads ->
           let m_new = Model.Expr (t,e) in
           make_alt_if_allowed_and_needed
             ~allowed ~supp ~nb
             m_new m varseq' best_reads)
  and aux_pat ctx m t c args selected_reads =
    let allowed = asd#alt_opt t in
    aux_gen ctx m selected_reads
      (fun (read : _ Model.read) ->
        match read.data with
        | D (v, DPat (dc, dargs)) as data ->
           List.filter_map
             (fun (m',varseq',input) ->
               match eval_parse_bests m' read.bindings input with
               | Result.Ok ((data',dl')::_) -> Some (m',varseq',data')
               | _ -> None)
             (refinements_pat t c args varseq0 data)
        | _ -> assert false)
      (fun m' varseq' ~supp ~nb ~alt best_reads ->
        let* m_new, best_reads =
          postprocessing t c args m' ~supp ~nb ~alt best_reads in
        make_alt_if_allowed_and_needed
          ~allowed ~supp ~nb
          m_new m varseq' best_reads)
  and aux_alt_prune ctx m m1 m2 selected_reads =
    aux_gen ctx m selected_reads
      (fun (read : _ Model.read) ->
        match read.data with
        | Data.D (_, DAlt (prob, b, d12)) ->
           if b
           then [m1, varseq0, d12]
           else [m2, varseq0, d12]
        | _ -> assert false)
      (fun m' varseq' ~supp ~nb ~alt best_reads ->
        if supp = nb
        then Myseq.return (m', varseq', best_reads)
        else Myseq.empty)
  and aux_alt_cond_undet ctx m xc c m1 m2 selected_reads =
    aux_gen ctx m selected_reads
      (fun (read : _ Model.read) ->
        match read.data with
        | Data.D (v, DAlt (_prob, true, d1)) ->
           let vc = value_of_bool true in
           let es : _ Expr.Exprset.t = Expr.Index.lookup vc (Lazy.force read.lazy_index) in
           Myseq.fold_left
             (fun rs e -> (e, varseq0, Data.D (v, DAlt (1., true, d1))) :: rs)
             [] (Expr.Exprset.to_seq es)
        | Data.D (_, DAlt (_, false, _)) ->
           (* we only look for true expressions because the index does not contain all false expressions *)
           (* extend_partial_best_reads below compensates for that *)
           []
        | _ -> assert false)
      (fun e varseq' ~supp ~nb ~alt best_reads ->
        let best_reads =
          (*if supp <= 1
          then best_reads (* the condition should be valid for at least two examples *)
          else*) (* too strict, given low number of examples *)
            extend_partial_best_reads
              selected_reads best_reads
              (fun read ->
                match read.data with
                | D (v, DAlt (_prob, b, d1)) ->
                   if not b && not (Expr.Exprset.mem e (Expr.Index.lookup (value_of_bool true) (Lazy.force read.lazy_index)))
                   then Some (read, D (v, DAlt (1., false, d1)))
                   else None
                | _ -> assert false) in
        let supp1, nb1 = best_reads_stats best_reads in
        if supp < nb (* discriminating cond *)
           && supp1 = nb1 (* valid cond for all examples *)
        then
          let c_new = Model.BoolExpr e in
          let m_new = Model.Alt (xc, c_new, m1, m2) in
          Myseq.return (m_new, varseq', best_reads)
        else Myseq.empty)
  in
  let selected_reads =
    (* the flag for each example indicates whether there are other reads, used with Alt *)
    List.map (fun example_reads -> (example_reads, false)) reads in
  let* p, r, varseq', supp, dl' =
    aux Model.ctx0 m0 selected_reads
    |> Myseq.sort (fun (p1,r1,vs1,supp1,dl1) (p2,r2,vs2,supp2,dl2) ->
           dl_compare dl1 dl2)
    |> Myseq.slice ~limit:max_refinements in
  let m' = Model.refine p r m0 in
  Myseq.return (p, r, supp, dl', m', varseq')

  
let task_refinements
      ~(binding_vars : ('typ,'var,'constr,'func) Model.model -> 'var Expr.binding_vars)
      ~(input_refinements : ('typ,'value,'dconstr,'var,'constr,'func) refiner)
      ~(output_refinements : ('typ,'value,'dconstr,'var,'constr,'func) refiner)
      
      (m : (('typ,'var,'constr,'func) Task_model.task_model) as 'task_model)
      (prs : ('value,'dconstr,'var,'func) Task_model.pairs_reads)
      (dsri : ('value,'dconstr,'var,'func) Task_model.reads)
      (dsro : ('value,'dconstr,'var,'func) Task_model.reads)
    : (('typ,'var,'constr,'func) Task_model.refinement * 'task_model) Myseq.t = (* QUICK Myseq.next *)
  Myseq.interleave (* TODO: rather order by estimated dl *)
    [ (let* p, ri, suppi, dli', mi, varseqi =
         input_refinements ~nb_env_vars:0 ~dl_M:prs.dl_mi
           m.input_model m.input_varseq dsri.reads in
       let nb_env_vars = Bintree.cardinal (binding_vars mi) in
       Myseq.return
         (Task_model.Rinput (p,ri,suppi,dli'),
          {m with input_model = mi; input_varseq = varseqi; nb_env_vars}));
      (let* p, ro, suppo, dlo', mo, varseqo =
         output_refinements ~nb_env_vars:m.nb_env_vars ~dl_M:prs.dl_mo
           m.output_model m.output_varseq dsro.reads in
       Myseq.return
         (Task_model.Routput (p,ro,suppo,dlo'),
          {m with output_model = mo; output_varseq = varseqo})) ]

let task_prunings
      ~(input_prunings : ('typ,'value,'dconstr,'var,'constr,'func) refiner)
      
      (m : (('typ,'var,'constr,'func) Task_model.task_model as 'task_model))
      (dsri : ('value,'dconstr,'var,'func) Task_model.reads)
    : (('typ,'var,'constr,'func) Task_model.refinement * 'task_model) Myseq.t = (* QUICK Myseq.next *)
  let* pi, ri, suppi, dli', mi', varseqi' =
    input_prunings ~nb_env_vars:0 ~dl_M:dsri.dl_m
      m.input_model m.input_varseq dsri.reads in
  Myseq.return
    (Task_model.Rinput (pi,ri,suppi,dli'),
     {m with input_model = mi'; input_varseq = varseqi'})

