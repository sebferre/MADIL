
open Madil_common
open Task_model

(* learning : used by batch only, replicate changes in arc_lis *)

type ('typ,'value,'dconstr,'var,'constr,'func) results =
  { result_refining : ('typ,'value,'dconstr,'var,'constr,'func) results_phase;
    result_pruning : ('typ,'value,'dconstr,'var,'constr,'func) results_phase }
and ('typ,'value,'dconstr,'var,'constr,'func) results_phase =
  { task_model : ('typ,'value,'var,'constr,'func) Task_model.task_model;
    pairs_reads : ('typ,'value,'dconstr,'var,'func) Task_model.pairs_reads;
    timed_out : bool;
    memed_out: bool }

type ('typ,'value,'dconstr,'var,'constr,'func) state =
  { r : ('typ,'value,'var,'constr,'func) Task_model.refinement; (* last refinement *)
    m : ('typ,'value,'var,'constr,'func) Task_model.task_model; (* current task model *)
    prs : ('typ,'value,'dconstr,'var,'func) Task_model.pairs_reads; (* pairs reads *)
    drsi : ('typ,'value,'dconstr,'var,'func) Task_model.reads; (* input reads *)
    drso : ('typ,'value,'dconstr,'var,'func) Task_model.reads; (* output reads *)
    dl_triples : dl triple triple; (* all DLs *)
    ldo : dl; (* output data normalized DL *)
    ld : dl; (* data normalized DL *)
    lmd : dl; (* whole normalized DL *)
  }
    
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

      ~memout_refine ~timeout_refine ~timeout_prune
      ~(beam_width : int) ~(refine_degree : int)
      ~env (* environment data to the input model *)
      ~init_task_model
      (pairs : 'value Task.pair list)
    : ('typ,'value,'dconstr,'var,'constr,'func) results
  = Common.prof "Learning.learn" (fun () ->
  let norm_dl_model_data = make_norm_dl_model_data ~alpha () in
  let data_of_model ?pred ~pruning r m =
    try
      let state_opt =
        Result.to_option
          (let| prs = read_pairs ~pruning ~env m pairs in
           let dl_triples = norm_dl_model_data prs in
           let (_lmi,_lmo,_lm), (_ldi,ldo,ld), (_lmdi,_lmdo,lmd) = dl_triples in
           let| () =
             if pruning
             then (* checking that no loss on parsing ranks *)
               match pred with (* previous state *)
               | None -> Result.Ok () (* none, at initial state *)
               | Some (_rm0, state0, _) ->
                  if ld <= state0.ld
                  then Result.Ok ()
                  else Result.Error (Failure "The pruning degrades parsing rank")
             else Result.Ok () in
           let drsi, drso = split_pairs_read prs in
           Result.Ok {r; m; prs; drsi; drso; dl_triples; ldo; ld; lmd}) in
      let status =
        match state_opt with
        | Some state -> `Success (state.prs, state.drsi, state.drso, state.dl_triples, state.lmd)
        | None -> `Failure in
      log_reading r m ~status;
      state_opt
    with
    | exn ->
       let status =
         match exn with
         | Common.Timeout -> `Timeout
         | _ -> `Error exn in
       log_reading r m ~status;
       raise exn
  in
  (* experimental: triggers memory exhaustion, and process termination*)
  let r0, m0 = RInit, init_task_model in
  let state0 =
    match data_of_model ?pred:None ~pruning:false r0 m0 with
    | Some state0 -> state0
    | None -> failwith "Learning.learn: invalid initial task model" in
  let state_refine_ref = ref state0 in
  let rec loop_refine state delta conts =
    log_refining state.r state.m state.prs state.lmd;
    if state.ldo = 0. (* end of search *)
    then state_refine_ref := state
    else
      let lstate1 = (* computing the [refine_degree] most compressive valid refinements *)
        myseq_find_map_k refine_degree
          (fun (r1,m1) ->
            match data_of_model ?pred:None ~pruning:false r1 m1 with
            | None -> None (* failure to parse with model m1 *)
            | Some state1 ->
               if state1.lmd < state.lmd
               then Some state1
               else None)
          (task_refinements state.m state.prs state.drsi state.drso) in
      if lstate1 = [] (* no compressive refinement *)
      then (
        if state.lmd < (!state_refine_ref).lmd then
          state_refine_ref := state; (* recording current state as best state *)
        try (* jumping to most promising continuation *)
          let delta1, ostate1 = Bintree.min_elt conts in
          let state1 = ostate1#get in
          let conts = Bintree.remove_min_elt conts in
          print_endline "JUMPING"; (* TODO: be more precise on which jump *)
          loop_refine state1 delta1 conts
        with Not_found -> () ) (* no continuation *)
      else
        let lstate1 =
          List.stable_sort
            (fun state1 state2 -> Stdlib.compare state1.lmd state2.lmd)
            lstate1 in
        match lstate1 with
        | [] -> assert false
        | state1::others ->
           let lmd1 = state1.lmd in
           let conts =
             List.fold_left
               (fun res state2 ->
                 let ok =
                   match state1.r, state2.r with
                   | Task_model.Routput (_, Model.Expr _, _, _), _ -> false (* not for exprs *)
                   | Rinput (p1,sm1,_,_), Rinput (p2,sm2,_,_) -> p1 = p2 (* same path *)
                   | Routput (p1,sm1,_,_), Routput (p2,sm2,_,_) -> p1 = p2 (* same path *)
                   | _ -> false in
                 if ok
                 then
                   let lmd2 = state2.lmd in
                   let delta2 = delta +. (lmd2 -. lmd1) in
                   let ostate2 = object method get = state2 end in (* object to hide some mysterious functional value inside *)
                   Bintree.add (delta2, ostate2) res
                 else res)
               conts others in                 
           loop_refine state1 delta conts
  in
  let state_refine, timed_out_refine, memed_out_refine =
    print_endline "REFINING PHASE";
    let res_opt =
      Common.do_memout memout_refine (* 1000 *) (* Mbytes *)
        (fun () ->
          Common.do_timeout timeout_refine
            (fun () ->
              loop_refine state0 0. Bintree.empty)) in
    !state_refine_ref, (res_opt = Some None), (res_opt = None) in
  let result_refining =
    { task_model = state_refine.m;
      pairs_reads = state_refine.prs;
      timed_out = timed_out_refine;
      memed_out = memed_out_refine } in
  let lm_refine = [(state_refine.r, state_refine.m), state_refine, state_refine.lmd] in
(*
  let lm_refine, timed_out_refine =      
    print_endline "REFINING PHASE";
    Mdl.Strategy.beam
      ~timeout:timeout_refine
      ~beam_width
      ~refine_degree
      ~m0:(RInit, init_task_model)
      ~data:(fun ?pred (r,m) -> data_of_model ?pred ~pruning:false r m)
      ~code:(fun (r,m) (prs,dsri,dsro,dl_triples,lmd) -> lmd)
      ~refinements:(fun (r,m) (prs,dsri,dsro,dl_triples,lmd) dl ->
        log_refining r m prs dl;
        Printf.printf "--- %dM memory used ---\n" ((Gc.quick_stat()).Gc.heap_words * 8 / 1000000);
        Common.prof "Learning.task_refinements" (fun () ->
            task_refinements m prs dsri dsro)) in
  match lm_refine with
  | [] -> assert false
  | ((_,m_refine), (psr_refine,_,_,_,_), _)::_ ->
 *)   
     let lm_prune, timed_out_prune =
       if timeout_prune = 0 (* no pruning *)
       then lm_refine, timed_out_refine
       else (
         print_endline "PRUNING PHASE";
         Mdl.Strategy.beam
           ~timeout:timeout_prune
           ~beam_width:1
           ~refine_degree
           ~m0:(RInit, state_refine.m)
           ~data:(fun ?pred (r,m) -> data_of_model ?pred ~pruning:true r m)
           ~code:(fun (r,m) state -> state.lmd)
           (* only parse ranks counted for input grids *)
           ~refinements:(fun (r,m) state dl ->
             log_refining state.r state.m state.prs dl;
             Common.prof "Learning.task_prunings" (fun () ->
                 task_prunings state.m state.drsi))
       ) in
     match lm_prune with
     | [] -> assert false
     | ((_,m_prune), state_prune, _)::_ ->
        let result_pruning =
          { task_model = m_prune;
            pairs_reads = state_prune.prs;
            timed_out = timed_out_prune;
            memed_out = false } in
        { result_refining;
          result_pruning })
