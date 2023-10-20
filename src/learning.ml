
open Madil_common
open Task_model

(* learning *)

let learn
      ~(alpha : float)
      ~(read_pairs :
          pruning:bool -> env:'data ->
          (('t,'value,'var,'constr,'func) Task_model.task_model as 'task_model) ->
          'value Task.pair list ->
          (('typ,'value,'dconstr,'var,'func) Task_model.pairs_reads as 'pairs_reads) result)
      ~(task_refinements :
          'task_model -> 'pairs_reads ->
          (('typ,'value,'dconstr,'var,'func) Task_model.reads as 'reads) -> 'reads ->
          ((('typ,'value,'var,'constr,'func) Task_model.refinement as 'refinement) * 'task_model) Myseq.t)
      ~(task_prunings :
          'task_model -> 'reads ->
          ('refinement * 'task_model) Myseq.t)
      ~(log_reading :
          'refinement -> 'task_model ->
          status:[ `Success of ('pairs_reads * 'reads * 'reads * dl triple triple * dl)
                 | `Failure
                 | `Timeout
                 | `Error of exn] -> unit)
      ~(log_refining : 'refinement -> 'task_model -> 'pairs_reads -> dl -> unit)

      ~timeout_refine ~timeout_prune
      ~beam_width ~refine_degree
      ~env (* environment data to the input model *)
      ~init_task_model
      (pairs : 'value Task.pair list)
    : ('task_model * 'pairs_reads * bool) double
  = Common.prof "Model.learn_model" (fun () ->
  let norm_dl_model_data = make_norm_dl_model_data ~alpha () in
  let data_of_model ~pruning r m =
    try
      let res_opt =
        Result.to_option
          (let| prs = read_pairs ~pruning ~env m pairs in
           let drsi, drso = split_pairs_read prs in
           let dl_triples = norm_dl_model_data prs in
           let (lmi,lmo,lm), (ldi,ldo,ld), (_lmdi,_lmdo,lmd) = dl_triples in
           Result.Ok (prs,drsi,drso,dl_triples,lmd)) in
      let status =
        match res_opt with
        | Some res -> `Success res
        | None -> `Failure in
      log_reading r m ~status;
      res_opt
    with
    | exn ->
       let status =
         match exn with
         | Common.Timeout -> `Timeout
         | _ -> `Error exn in
       log_reading r m ~status;
       raise exn
  in
  let lm_refine, timed_out_refine =      
    print_endline "REFINING PHASE";
    Mdl.Strategy.beam
      ~timeout:timeout_refine
      ~beam_width
      ~refine_degree
      ~m0:(RInit, init_task_model)
      ~data:(fun (r,m) -> data_of_model ~pruning:false r m)
      ~code:(fun (r,m) (prs,dsri,dsro,dl_triples,lmd) -> lmd)
      ~refinements:(fun (r,m) (prs,dsri,dsro,dl_triples,lmd) dl ->
        log_refining r m prs dl;
        Common.prof "Learning.task_refinements" (fun () ->
            task_refinements m prs dsri dsro)) in
  match lm_refine with
  | [] -> assert false
  | ((_,m_refine), (psr_refine,_,_,_,_), _)::_ ->
     let lm_prune, timed_out_prune =
       if timeout_prune = 0 (* no pruning *)
       then lm_refine, timed_out_refine
       else (
         print_endline "PRUNING PHASE";
         Mdl.Strategy.beam
           ~timeout:timeout_prune
           ~beam_width:1
           ~refine_degree
           ~m0:(RInit, m_refine)
           ~data:(fun (r,m) -> data_of_model ~pruning:true r m)
           ~code:(fun (r,m) (prs,dsri,dsro,dl_triples,lmd) -> lmd)
           (* only parse ranks counted for input grids *)
           ~refinements:(fun (r,m) (prs,dsri,dsro,dl_triples,lmd) dl ->
             log_refining r m prs dl;
             Common.prof "Learning.task_prunings" (fun () ->
                 task_prunings m dsri))
       ) in
     match lm_prune with
     | [] -> assert false
     | ((_,m_prune), (psr_prune,_,_,_,_), _)::_ ->
        (m_refine, psr_refine, timed_out_refine),
        (m_prune, psr_prune, timed_out_prune))
