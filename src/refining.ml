
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
      (get_rs : ('value,'dconstr,'var,'func) Model.read -> ('ref * 'var Myseq.t * ('value,'dconstr) Data.data) list)
      (reads : ('value,'dconstr,'var,'func) Model.read list list)
    : ('ref, 'var Myseq.t * ('value,'dconstr,'var,'func) best_read list) Mymap.t =
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

let extend_partial_best_reads 
      (selected_reads : (('value,'dconstr,'var,'func) Model.read as 'read) list list)
      (best_reads : (('value,'dconstr,'var,'func) best_read as 'best_read) list)
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

let new_var (varseq : 'var Myseq.t) : 'var * 'var Myseq.t =
  match varseq () with
  | Myseq.Cons (x,varseq') -> x, varseq'
  | Myseq.Nil -> failwith "No more fresh variable (should be an infinite sequence"

let make_alt_if_allowed_and_needed
      ~(allowed : bool) ~(nb : int) ~(supp : int)
      (m_true : (('var,'constr,'func) Model.model as 'model))
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
        (fun {matching; read; new_data} ->
          {matching; read; new_data = D (Data.value new_data, DAlt (matching, new_data))})
        best_reads in
    Myseq.return (m', varseq', best_reads')
  else (* alt not allowed *)
    Myseq.empty

type ('t,'value,'dconstr,'var,'constr,'func) refiner =
  nb_env_vars:int ->
  dl_M:dl -> (* current model DL *)
  (* NOTE: dl_M does not matter for ranking because an invariant of parsing and refinement *)
  't Kind.kind ->
  (('var,'constr,'func) Model.model as 'model) ->
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
      ~(asd : ('t,'constr,'func) Model.asd)
      ~(value_of_bool : bool -> 'value)
      ~(dl_model : nb_env_vars:int -> ('t Kind.kind as 'kind) -> (('var,'constr,'func) Model.model as 'model) -> dl)
      ~(dl_data : 'model -> (('value,'dconstr) Data.data as 'data) -> dl)
      ~(eval_parse_bests : 'kind -> 'model -> ('input,'value,'dconstr,'var) Model.eval_parse_bests)
      ~(refinements_pat : 'constr -> 'model array -> ('var Myseq.t as 'varseq) -> 'data -> ('model * 'var Myseq.t * 'input) list) (* refined submodel with remaining fresh vars and related new parsing input *)
      ~(postprocessing : 'constr -> 'model array -> 'model -> supp:int -> nb:int -> alt:bool -> 'best_read list
                         -> ('model * 'best_read list) Myseq.t) (* converting refined submodel, alt mode (true if partial match), support, and best reads to a new model and corresponding new data *)
    : ('t,'value,'dconstr,'var,'constr,'func) refiner =
  fun ~nb_env_vars ~dl_M k0 m0 varseq0 reads ->
  let aux_gen (type r)
        ctx k m selected_reads
        (read_refs : 'read -> (r * 'varseq * 'data) list)
        (postprocessing : r -> 'varseq -> supp:int -> nb:int -> alt:bool -> 'best_reads -> ('model * 'varseq * 'best_reads) Myseq.t)
      : ('path * 'model * 'varseq * int * dl) Myseq.t =
    let p = ctx Model.This in (* local path *)
    let dl_m = dl_model ~nb_env_vars k m in
    let dl_data_m = dl_data m in
    let r_best_reads = inter_union_reads read_refs selected_reads in
    let* r, (varseq', best_reads) = Mymap.to_seq r_best_reads in
    let supp, nb = best_reads_stats best_reads in
    let alt = (supp < nb) in
    let* m_new, varseq', best_reads = postprocessing r varseq' ~supp ~nb ~alt best_reads in
    let dl_m_new = dl_model ~nb_env_vars k m_new in
    let dl_data_m_new = dl_data m_new in
    let dl_new =
      dl_M -. dl_m +. dl_m_new
      +. alpha *. Mdl.sum best_reads
                    (fun {matching; read; new_data} ->
                      read.dl -. dl_data_m read.data +. dl_data_m_new new_data) in
    Myseq.return (p, m_new, varseq', supp, dl_new)
  in
  let rec aux ctx k m selected_reads other_reads_env =
  if selected_reads = [] then Myseq.empty
  else
    match k, m with
    | _, Model.Def (x,m1) ->
       aux ctx k m1 selected_reads other_reads_env
    | Kind.KVal t, Model.Pat (c,args) ->
       let k_args = asd#constr_args t c in
       Myseq.interleave
         (aux_expr ctx k m selected_reads
          :: aux_pat ctx k m c args selected_reads
          :: Array.to_list
              (Array.mapi
                 (fun i mi ->
                   let ctxi = (fun p1 -> ctx (Model.Field (c,i,p1))) in
                   let ki = k_args.(i) in
                   aux ctxi ki mi
                     (map_reads
                        (fun read ->
                          match read.Model.data with
                          | D (_, DPat (dc, args)) ->
                             let di = try args.(i) with _ -> assert false in
                             {read with Model.data = di}
                          | _ -> assert false)
                        selected_reads)
                     other_reads_env)
                 args))
    | _, Model.Fail -> Myseq.empty
    | _, Model.Alt (xc,c,m1,m2) ->
       Myseq.interleave (* TODO: add expressions *)
         [ aux_expr ctx k m selected_reads;
           
           (match c with
            | Undet _ -> aux_alt_cond_undet ctx k m xc c m1 m2 selected_reads
            | True | False | BoolExpr _ -> Myseq.empty);
           
           (let ctx1 = (fun p1 -> ctx (Model.Branch (true,p1))) in
            let sel1, other1 =
              partition_map_reads
                (fun (read : _ Model.read) ->
                  match read.data with
                  | D (_, DAlt (b,d12)) ->
                     if b
                     then Result.Ok {read with data=d12}
                     else Result.Error read.env
                  | _ -> assert false)
                selected_reads
                other_reads_env in
            aux ctx1 k m1 sel1 other1);
                        
           (let ctx2 = (fun p1 -> ctx (Model.Branch (false,p1))) in
            let sel2, other2 =
              partition_map_reads
                (fun (read : _ Model.read) ->
                  match read.data with
                  | D (_, DAlt (b,d12)) ->
                     if not b
                     then Result.Ok {read with data=d12}
                     else Result.Error read.env
                  | _ -> assert false)
                selected_reads
                other_reads_env in
            aux ctx2 k m2 sel2 other2) ]
                        
    | Kind.KSeq k1, Model.Seq (n,lm1) ->
       Myseq.interleave
         (List.mapi
            (fun i mi ->
              let ctxi = (fun p1 -> ctx (Model.Item (i,p1))) in
              aux ctxi k1 mi
                (map_reads
                   (fun read ->
                     match read.Model.data with
                     | D (_, DSeq (_,ld)) -> {read with Model.data = List.nth ld i}
                     | _ -> assert false)
                   selected_reads)
                other_reads_env)
            lm1)
    | _, Model.Cst m1 -> raise TODO
    | _, Model.Expr e -> Myseq.empty
    | _ -> assert false
  and aux_expr ctx k m selected_reads =
    aux_gen ctx k m selected_reads
      (fun (read : _ Model.read) ->
        let v = Data.value read.data in
        match asd#expr_opt k with
        | None -> [] (* no expression here *)
        | Some k1 ->
           let es = Expr.Index.lookup v read.index in
           Myseq.fold_left
             (fun rs e -> (e, varseq0, Data.D (v, Data.DNone)) :: rs)
             [] (Expr.Exprset.to_seq es))
      (fun e varseq' ~supp ~nb ~alt best_reads ->
        let m_new = Model.Expr e in
        make_alt_if_allowed_and_needed
          ~allowed:(asd#alt_opt k) ~supp ~nb
          m_new m varseq' best_reads)
  and aux_pat ctx k m c args selected_reads =
    aux_gen ctx k m selected_reads
      (fun (read : _ Model.read) ->
        match read.data with
        | D (v, DPat (dc, dargs)) as data ->
           List.filter_map
             (fun (m',varseq',input) ->
               match eval_parse_bests k m' read.bindings input with
               | Result.Ok ((data',dl')::_) -> Some (m',varseq',data')
               | _ -> None)
             (refinements_pat c args varseq0 data)
        | _ -> assert false)
      (fun m' varseq' ~supp ~nb ~alt best_reads ->
        let* m_new, best_reads =
          postprocessing c args m' ~supp ~nb ~alt best_reads in
        make_alt_if_allowed_and_needed
          ~allowed:(asd#alt_opt k) ~supp ~nb
          m_new m varseq' best_reads)
  and aux_alt_cond_undet ctx k m xc c m1 m2 selected_reads =
    aux_gen ctx k m selected_reads
      (fun (read : _ Model.read) ->
        match read.data with
        | Data.D (_, DAlt (true, _)) as d ->
           let v = value_of_bool true in
           let es : _ Expr.Exprset.t = Expr.Index.lookup v read.index in
           Myseq.fold_left
             (fun rs e -> (e, varseq0, d) :: rs)
             [] (Expr.Exprset.to_seq es)
        | Data.D (_, DAlt (false, _)) ->
           (* we only look for true expressions because the index does not contain all false expressions *)
           (* extend_partial_best_reads below compensates for that *)
           []
        | _ -> assert false)
      (fun e varseq' ~supp ~nb ~alt best_reads ->
        let best_reads =
          if supp <= 1
          then best_reads (* the condition should be valid for at least two examples *)
          else
            extend_partial_best_reads
              selected_reads best_reads
              (fun read ->
                match read.data with
                | D (_, DAlt (b, _)) ->
                   if not b && not (Expr.Exprset.mem e (Expr.Index.lookup (value_of_bool true) read.index))
                   then Some (read, read.data)
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
  Myseq.prof "Model.refinements" (
  let selected_reads = reads in
  let other_reads_env = [] in
  let* p, r, varseq', supp, dl' =
    aux Model.ctx0 k0 m0 selected_reads other_reads_env
    |> Myseq.sort (fun (p1,r1,vs1,supp1,dl1) (p2,r2,vs2,supp2,dl2) ->
           dl_compare dl1 dl2) (* support use for sorting in LIS UI *)
    |> Myseq.unique
    |> Myseq.slice ~limit:max_refinements in
  let m' = Model.refine p r m0 in
  Myseq.return (p, r, supp, dl', m', varseq'))


let task_refinements
      ~(binding_vars : ('var,'constr,'func) Model.model -> 'var Expr.binding_vars)
      ~(input_refinements : ('t,'value,'dconstr,'var,'constr,'func) refiner)
      ~(output_refinements : ('t,'value,'dconstr,'var,'constr,'func) refiner)
      
      (m : (('t,'var,'constr,'func) Task_model.task_model) as 'task_model)
      (prs : ('value,'dconstr,'var,'func) Task_model.pairs_reads)
      (dsri : ('value,'dconstr,'var,'func) Task_model.reads)
      (dsro : ('value,'dconstr,'var,'func) Task_model.reads)
    : (('var,'constr,'func) Task_model.refinement * 'task_model) Myseq.t =
  Myseq.interleave (* TODO: rather order by estimated dl *)
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

