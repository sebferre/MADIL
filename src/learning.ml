
open Madil_common
open Task_model

(* learning : used by batch only, replicate changes in arc_lis *)

type ('typ,'value,'var,'constr,'func) results =
  { result_refining : ('typ,'value,'var,'constr,'func) results_phase;
    result_pruning : ('typ,'value,'var,'constr,'func) results_phase }
and ('typ,'value,'var,'constr,'func) results_phase =
  { task_model : ('typ,'value,'var,'constr,'func) Task_model.task_model;
    pairs_reads : ('typ,'value,'constr,'var,'func) Task_model.pairs_reads;
    timed_out : bool;
    memed_out: bool;
    nsteps : int;
    nsteps_sol : int;
    njumps : int;
    njumps_sol : int;
  }

type ('typ,'value,'var,'constr,'func) state =
  { r : ('typ,'value,'var,'constr,'func) Task_model.refinement; (* last refinement *)
    m : ('typ,'value,'var,'constr,'func) Task_model.task_model; (* current task model *)
    prs : ('typ,'value,'constr,'var,'func) Task_model.pairs_reads; (* pairs reads *)
    drsi : ('typ,'value,'constr,'var,'func) Task_model.reads; (* input reads *)
    drso : ('typ,'value,'constr,'var,'func) Task_model.reads; (* output reads *)
    dl_split : dl_split; (* all DLs *)
    lmd : dl; (* whole normalized DL, with ldi=lri in pruning mode *)
    lrido : dl; (* input rank + output data normalized DL *)
  }

(* encapsulation of state and search path information *)
(* using an object to hide some mysterious functional value inside state that is a problem with Bintree *)
class ['state] ostate ?(from : ('state ostate * int (* rank *)) option) (state : 'state) =
  object (self)
    val nsteps_sol : int = (* nb of refinement steps from initial model *)
      match from with
      | None -> 0
      | Some (p,rank) -> 1 + p#nsteps_sol
    val jumps_sol : int list = (* reverse list of refinement ranks from initial model *)
      match from with
      | None -> []
      | Some (p,rank) -> rank :: p#jumps_sol
    val state : 'state = state (* reached state *)
    val parent_opt : 'state ostate option =
      match from with
      | None -> None
      | Some (p,rank) -> Some p
    val rank : int =
      match from with
      | None -> 0
      | Some (p,rank) -> rank
    
    method nsteps_sol = nsteps_sol
    method jumps_sol = jumps_sol
    method njumps_sol = List.fold_left (+) 0 jumps_sol
    method state = state
    method parent_opt = parent_opt
    method rank = rank 

    method print_jumps : unit =
      jumps_sol
      |> List.rev
      |> List.iter
           (function
            | 0 -> print_string " -"
            | rank -> print_char ' '; print_int rank)
  end

class virtual ['state] conts =
  (* mutable collection of search continuation points *)
  object
    method virtual is_empty : bool
    method virtual goto : 'state ostate (* selected refined state *)
                          -> unit
    method virtual push : 'state ostate (* final/completed state *)
                          -> 'state ostate list (* incomplete states as continuation points *)
                          -> unit (* added to collection, using information from final state *)
    method virtual pop : 'state ostate option (* most promising continuation point, removed from collection *)
  end

class virtual ['state,'fitness] conts_fitness = (* fitness function to specify ordering of continuations *)
  object (self)
    inherit ['state] conts
    val mutable conts : ('fitness * 'state ostate) Bintree.t = Bintree.empty
    method virtual fitness : 'state ostate -> 'state ostate -> 'fitness
    method is_empty = Bintree.is_empty conts
    method goto ostate = ()
    method push (final_ostate : 'state ostate) (jump_ostates : 'state ostate list) : unit =
      List.iter
        (fun jump_ostate ->
          let fitness = self#fitness final_ostate jump_ostate in
          conts <- Bintree.add (fitness, jump_ostate) conts)
        jump_ostates
    method pop : 'state ostate option =
      try
        let _, ostate = Bintree.min_elt conts in
        conts <- Bintree.remove_min_elt conts;
        Some ostate
      with Not_found -> None
  end

class ['state] conts_v0 =
  object
    constraint 'fitness = int * int
    inherit ['state, 'fitness] conts_fitness
    method fitness final_ostate jump_ostate =
      let _, njumps, sumdepths =
        List.fold_right
          (fun rank (depth, njumps, sumdepths) ->
            (depth + 1, njumps + rank,
             if rank > 0 then sumdepths + depth else sumdepths))
          jump_ostate#jumps_sol (0,0,0) in
      (njumps, sumdepths)
  end

class ['state] conts_v1 =
  object
    constraint 'fitness = int * int
    inherit ['state, 'fitness] conts_fitness
    method fitness final_ostate jump_ostate =
      (jump_ostate#nsteps_sol, List.hd jump_ostate#jumps_sol)
  end
let make_conts_v1 () = (new conts_v1 :> 'state conts)

class ['state] conts_softmax ~(temp : float) ~(make_subconts : unit -> 'state conts) =
  (* choosing a final based on softmax of the reached DL (lmd), tuned by temperature,
     then choosing a related cont according to a specified conts (make_subconts) *) 
  object
    inherit ['state] conts
    val mutable final_conts : (float (* exp(lmd) *) * 'state ostate, 'state conts) Mymap.t = Mymap.empty
    val mutable sum_exp : float = 0.

    method is_empty = Mymap.is_empty final_conts

    method goto ostate = ()
    
    method push final_ostate jump_ostates =
      let exp = 2. ** (-. final_ostate#state.lmd /. temp) in (* lower DL, higher weight *)
      let k = (-. exp, final_ostate) in (* negative for sorting by decreasing weight, final_ostate to distinguish same-exp finals *)
      let subconts =
        match Mymap.find_opt k final_conts with
        | Some subconts -> subconts
        | None -> (* new final *)
           let subconts = make_subconts () in
           final_conts <- Mymap.add k subconts final_conts;
           sum_exp <- exp +. sum_exp;
           subconts in
      subconts#push final_ostate jump_ostates

    method pop =
      (* final_conts used as probability distribution *)
      let threshold = Random.float sum_exp in (* drawing a position in prob distrib *)
      let last_i, _, subconts_opt = (* looking for the selected subconts *)
        Mymap.fold (* left-to-right traversal *)
          (fun (neg_exp_i,_ as k_i) subconts_i (i,th,subconts_opt as res) ->
            if subconts_opt = None
            then
              let th = th +. neg_exp_i in
              if th < 0. (* drawn element reached *)
              then (i, th, Some (i,k_i,subconts_i))
              else (i+1, th, subconts_opt)
            else res) (* already found *)
          final_conts (0, threshold, None) in
      match subconts_opt with
      | None -> None (* no more conts *)
      | Some (i, (neg_exp, _ as k), subconts) ->
         let ostate_opt = subconts#pop in
         assert (ostate_opt <> None);
         if subconts#is_empty (* empty subconts *)
         then ( (* updating *)
           final_conts <- Mymap.remove k final_conts;
           sum_exp <- sum_exp +. neg_exp
         );
         ostate_opt

  end

type 'node mcts_info = {
    mutable is_leaf : bool;
    mutable rollout_val : float option; (* final value after rollout from this node *)
    mutable count : int; (* nb visits *)
    mutable sumval : float; (* cumulated value *)
    mutable children : 'node list; (* children nodes, defined after 1st visit *)
  }

let init_info () : 'node mcts_info =
  { is_leaf = false;
    rollout_val = None;
    count = 0;
    sumval = 0.;
    children = [] }

class ['state] conts_mcts ?(c : float = sqrt 2.) (root : 'state ostate) =
  let value_of_ostate (ostate : 'node) : float =
    1. -. ostate#state.lmd /. 2. (* lmd normalized to [0,1] *)
  in
  object (self)
    inherit ['state] conts
    
    val mutable ostate_info : ('state ostate, 'state ostate mcts_info) Hashtbl.t = Hashtbl.create 103
    initializer
        let info = init_info () in
        info.is_leaf <- true;
        Hashtbl.add ostate_info root info
    
    method is_empty = assert false

    method private insert_child ostate =
      match ostate#parent_opt with
      | None -> assert false (* only root has no parent, inserted by initializer *)
      | Some parent ->
         let parent_info =
           try Hashtbl.find ostate_info parent
           with Not_found -> assert false in
         parent_info.children <- ostate :: parent_info.children;
         Hashtbl.add ostate_info ostate (init_info ())
    
    method goto ostate =
      self#insert_child ostate

    method private backpropagation value leaf_ostate =
      let leaf_info = try Hashtbl.find ostate_info leaf_ostate with _ -> assert false in
      (* leaf is no more a leaf *)
      leaf_info.is_leaf <- false;
      (* make leaf children new leaves *)
      List.iter
        (fun child_ostate ->
          let child_info = try Hashtbl.find ostate_info child_ostate with _ -> assert false in
          child_info.is_leaf <- true)
        leaf_info.children;
      (* backpropagate value to leaf and ancestors *)
      let rec aux ostate info =
        info.count <- info.count + 1;
        info.sumval <- info.sumval +. value;
        match ostate#parent_opt with
        | None -> ()
        | Some parent ->
           let parent_info = try Hashtbl.find ostate_info parent with _ -> assert false in
           aux parent parent_info
      in
      aux leaf_ostate leaf_info
    
    method push final_ostate jump_ostates =
      (* inserting new children *)
      List.iter self#insert_child jump_ostates;
      (* backpropagating information from final_ostate *)
      let value = value_of_ostate final_ostate in
      let rec find_leaf_ancestor ostate =
        let info = try Hashtbl.find ostate_info ostate with _ -> assert false in
        (* recording the rollout_value up to the leaf *)
        info.rollout_val <- Some value;
        if info.is_leaf
        then ostate
        else
          match ostate#parent_opt with
          | None -> assert false (* there must be a leaf above *)
          | Some parent -> find_leaf_ancestor parent
      in
      let leaf_ostate = find_leaf_ancestor final_ostate in
      self#backpropagation value leaf_ostate

    method pop =
      let rec selection ostate =
        let info = try Hashtbl.find ostate_info ostate with _ -> assert false in
        if info.is_leaf
        then
          match info.rollout_val with
          | None -> Some ostate (* compute rollout from there *)
          | Some value -> (* rollout already done, backpropagate and re-pop *)
             self#backpropagation value ostate;
             self#pop             
        else (* make UCB1 choice of a child *)
          let scored_children =
            List.map
              (fun child_ostate ->
                let child_info = try Hashtbl.find ostate_info child_ostate with _ -> assert false in
                let child_score =
                  let n = child_info.count in
                  let v = if n = 0 then 0. else child_info.sumval /. float n in (* exploitation *)
                  v +. c *. sqrt (log (float info.count) /. float (n+1)) in (* plus exploration *)
                child_score, - child_ostate#rank, child_ostate)
              info.children in
          let sorted_children = (* decreasing score, increasing rank *)
            List.rev (List.sort Stdlib.compare scored_children) in
          List.find_map
            (fun (_,_,child_ostate) -> selection child_ostate)
            sorted_children
      in
      selection root
  end

type resource_out =
  { timed_out : bool;
    memed_out : bool }

class ['state] search
        ~(make_conts : 'state ostate -> 'state conts)
        ~(refinements : 'state -> 'state list) (* must be sorted and filtered for exploration *)
        ~(stop_criteria : 'state -> bool)
        ~(k_state : 'state -> unit)
        (state0 : _ state as 'state) =
  let ostate0 = new ostate state0 in
  let conts = make_conts ostate0 in
  object (self)
    val mutable started = false
    val mutable stopped = false
    val mutable best_ostate = ostate0
    val mutable all_leaves = []
    val mutable nsteps = 0
    val mutable njumps = 0

    method best_ostate = best_ostate
    method best_leaves (k : int) : 'state ostate list =
      let sorted_leaves = (* sort by increasing DL, then left-right order in tree *)
        List.sort
          (fun ostate1 ostate2 ->
            Stdlib.compare
              (ostate1#state.lmd, List.rev ostate1#jumps_sol)
              (ostate2#state.lmd, List.rev ostate2#jumps_sol))
          all_leaves in
      list_take k sorted_leaves
    method nsteps = nsteps
    method njumps = njumps
    
    method rollout (ostate : 'state ostate) : 'state ostate =
      let rec aux ostate jump_ostates =
        let state = ostate#state in
        if state.lmd < best_ostate#state.lmd then
          best_ostate <- ostate;
        k_state state;
        if stop_criteria state (* end of search *)
        then (
          best_ostate <- ostate;
          stopped <- true;
          ostate)
        else
          let lstate1 = refinements state in
          let lostate1 =
            List.mapi
              (fun rank state1 -> new ostate ~from:(ostate,rank) state1)
              lstate1 in
          match lostate1 with
          | [] ->  (* no compressive refinement *)
             (* adding jump_ostates as continuations *)
             conts#push ostate jump_ostates;
             ostate
          | ostate1::others ->
             conts#goto ostate1;
             nsteps <- nsteps + 1;
             let () = (* showing point of choice *)
               if others <> [] then (
                 print_string "CHOICE AT";
                 ostate#print_jumps;
                 print_newline ()
               ) in
             aux ostate1 (List.rev_append others jump_ostates)
      in
      aux ostate []

    method next : 'state ostate option =
      if stopped then
        None
      else if not started then (
        started <- true;
        let ostate = self#rollout ostate0 in
        all_leaves <- ostate::all_leaves;
        Some ostate)
      else
        (* jumping to most promising continuation *)
        match conts#pop with
        | None -> None (* no continuation, end of search *)
        | Some ostate1 ->
           njumps <- njumps + 1;
           (* showing JUMP *)
           print_string "JUMP TO";
           ostate1#print_jumps;
           print_newline ();
           let ostate = self#rollout ostate1 in
           all_leaves <- ostate::all_leaves;
           Some ostate

    method iter
             ~(memout : int) ~(timeout : int)
             (k : 'state ostate -> unit)
           : resource_out =
      let rec aux () =
        match self#next with
        | Some ostate -> k ostate; aux ()
        | None -> ()
      in
      let res_opt =
        Common.do_memout memout (* Mbytes *)
          (fun () ->
            Common.do_timeout_gc (float timeout) (* seconds *)
              (fun () ->
                aux ())) in
      { timed_out = (res_opt = Some None);
        memed_out = (res_opt = None) }
  end

let sort_filter_refinements ~jump_width lstate1 =
  (* sort refinements, and keep the most compressive and alternative refinements for search *)
  let lstate1 =
    List.sort
      (fun state1 state2 ->
        Stdlib.compare (state1.lmd, state1.r) (state2.lmd, state2.r))
      lstate1 in
  match lstate1 with
  | [] -> []
  | state1::others ->
     let _, rev_others = (* retaining only other refinements on same side and path *)
       List.fold_left
         (fun (rank,res) state2 ->
           let ok =
             rank < jump_width &&
               (match state1.r, state2.r with
                | RInit, RInit -> true
                | RStep (side1,p1,sm1,_,_,_),
                  RStep (side2,p2,sm2,_,_,_) ->
                   side1 = side2 && p1 = p2 (* same side and path *)
                | _ -> false )in
           if ok
           then rank+1, state2::res
           else rank, res)
         (1, []) others in
     state1 :: List.rev rev_others

let select_refinements ~refine_degree ~jump_width ~data_of_model state refs =
  (* select [refine_degree] compressive refinements from sequence [refs], sort them, and filter alternative refinements *)
  refs
  |> myseq_find_map_k refine_degree
       (fun (r1,m1_res) ->
         let@ m1 = Result.to_option m1_res in
         match data_of_model ~pruning:false r1 m1 with
         | None -> None (* failure to parse with model m1 *)
         | Some state1 ->
            if state1.lmd < state.lmd
            then Some state1
            else None)
  |> sort_filter_refinements ~jump_width

let refining0
      ~refine_degree ~jump_width ~timeout_refine ~memout
      ~data_of_model ~task_refinements ~log_refining
      state0 =
  let refining =
    new search
      ~make_conts:(new conts_mcts ~c:(sqrt 2.))
      ~refinements:(fun state ->
        Common.prof "Learning.task_refinements" (fun () ->
            select_refinements ~refine_degree ~jump_width ~data_of_model state
              (task_refinements
                 ~include_expr:true
                 ~include_input:true
                 ~include_output:true
                 state.m state.prs state.drsi state.drso)))
      ~stop_criteria:(fun state -> state.lrido <= 0.)
      ~k_state:(fun state -> log_refining state.r state.m state.prs state.lmd state.lrido)
      state0 in
  let res_out =
    refining#iter
      ~memout ~timeout:timeout_refine
      (fun ostate -> ()) in
  let ostate_refine = refining#best_ostate in
  let state_refine = ostate_refine#state in
  state_refine,
  { task_model = state_refine.m;
    pairs_reads = state_refine.prs;
    timed_out = res_out.timed_out;
    memed_out = res_out.memed_out;
    nsteps = refining#nsteps;
    njumps = refining#njumps;
    nsteps_sol = ostate_refine#nsteps_sol;
    njumps_sol = ostate_refine#njumps_sol;
  }

let refining1
      ~refine_degree ~jump_width ~timeout_refine ~memout
      ~data_of_model ~task_refinements ~log_refining
      state0 =
  let search_in =
    new search
      ~make_conts:(new conts_mcts ~c:(sqrt 2.))
      ~refinements:(fun state ->
        Common.prof "Learning.task_refinements_in" (fun () ->
            select_refinements ~refine_degree ~jump_width ~data_of_model state
              (task_refinements
                 ~include_expr:false
                 ~include_input:true
                 ~include_output:false
                 state.m state.prs state.drsi state.drso)))
      ~stop_criteria:(fun state -> false)
      ~k_state:(fun state -> log_refining state.r state.m state.prs state.lmd state.lrido)
      state0 in
  let make_search_out (states_in : 'state list) : 'state search =
    new search
      ~make_conts:(new conts_mcts ~c:(sqrt 2.))
      ~refinements:(fun state ->
        if state == state0 && states_in <> []
        then
          List.rev_map
            (fun state -> {state with r = Task_model.RInit})
            states_in
        else
          Common.prof "Learning.task_refinements_out" (fun () ->
              select_refinements ~refine_degree ~jump_width ~data_of_model state
                (task_refinements
                   ~include_expr:true
                   ~include_input:false
                   ~include_output:true
                   state.m state.prs state.drsi state.drso)))
      ~stop_criteria:(fun state -> state.lrido <= 0.)
      ~k_state:(fun state -> log_refining state.r state.m state.prs state.lmd state.lrido)
      state0
  in
  print_endline "SEARCH OUT greedy";
  let search_out_0 = make_search_out [] in
  match search_out_0#next with
  | None -> assert false
  | Some ostate_out ->
     if ostate_out#state.lrido <= 0.
     then (* success *)
       let state_out = ostate_out#state in
       let nsteps = search_out_0#nsteps in
       state_out,
       { task_model = state_out.m;
         pairs_reads = state_out.prs;
         timed_out = false;
         memed_out = false;
         nsteps = nsteps;
         njumps = 0;
         nsteps_sol = nsteps;
         njumps_sol = 0 }
     else (
       print_endline "SEARCH IN OUT greedy";
       match search_in#next with
         | None -> assert false
         | Some ostate_in ->
            (* computing output model greedy *)
            let search_out_1 = make_search_out [ostate_in#state] in
            match search_out_1#next with
            | None -> assert false
            | Some ostate_out ->
               if ostate_out#state.lrido <= 0.
               then (* success *)
                 let state_out = ostate_out#state in
                 let nsteps = search_in#nsteps + search_out_1#nsteps in
                 state_out,
                 { task_model = state_out.m;
                   pairs_reads = state_out.prs;
                   timed_out = false;
                   memed_out = false;
                   nsteps = nsteps;
                   njumps = 0;
                   nsteps_sol = nsteps;
                   njumps_sol = 0 }
               else (
                 let timeout_in = timeout_refine / 6 in (* TODO: add parameter? *)
                 let timeout_out = timeout_refine - timeout_in in
                 (* searching best input model under timeout *)
                 print_endline "SEARCH IN mcts";
                 let res_in =
                   search_in#iter
                     ~memout ~timeout:timeout_in
                     (fun ostate -> ()) in
                 let ostates_in = search_in#best_leaves jump_width in (* TODO: use specific parameter? *)
                 (* searching best output model given chosen input model, under timeout *)
                 Printf.printf "FOUND %d input models\n" (List.length ostates_in);
                 print_endline "SEARCH OUT mcts";
                 let search_out_2 =
                   let states_in = List.map (fun ostate -> ostate#state) ostates_in in
                   make_search_out states_in in
                 let res_out =
                   search_out_2#iter
                     ~memout ~timeout:timeout_out
                     (fun ostate -> ()) in
                 let ostate_out = search_out_2#best_ostate in
                 let state_out = ostate_out#state in
                 let ostate_in =
                   try
                     let rank_in = List.hd (List.rev ostate_out#jumps_sol) in
                     List.nth ostates_in rank_in
                   with _ -> assert false in
                 Printf.printf "SOL %d + %d steps\n" ostate_in#nsteps_sol ostate_out#nsteps_sol;
                 state_out,
                 { task_model = state_out.m;
                   pairs_reads = state_out.prs;
                   timed_out = res_out.timed_out; (* no stop criteria for input *)
                   memed_out = res_in.memed_out || res_out.memed_out;
                   nsteps = search_in#nsteps + search_out_2#nsteps;
                   njumps = search_in#njumps + search_out_2#njumps;
                   nsteps_sol = ostate_in#nsteps_sol + ostate_out#nsteps_sol - 1; (* -1 because first output step chooses input model *)
                   njumps_sol = ostate_in#njumps_sol + ostate_out#njumps_sol }
               )
     )

let learn
      ~(alpha : float)
      ~(read_pairs :
          env:'data ->
          (('t,'value,'var,'constr,'func) Task_model.task_model as 'task_model) ->
          'value Task.pair list ->
          (('typ,'value,'constr,'var,'func) Task_model.pairs_reads as 'pairs_reads) result)
      ~(does_parse_value :
          ('t,'value,'var,'constr,'func) Model.model ->
          ('var,'typ,'value) Expr.bindings ->
          'value -> bool)
      ~(task_refinements :
          include_expr:bool ->
          include_input:bool ->
          include_output:bool ->
          'task_model -> 'pairs_reads ->
          (('typ,'value,'constr,'var,'func) Task_model.reads as 'reads) -> 'reads ->
          ((('typ,'value,'var,'constr,'func) Task_model.refinement as 'refinement) * 'task_model result) Myseq.t)
      ~(task_prunings :
          'task_model -> 'reads ->
          ('refinement * 'task_model result) Myseq.t)
      ~(log_reading :
          'refinement -> 'task_model ->
          status:[ `Success of ('pairs_reads * 'reads * 'reads * dl_split * dl)
                 | `Failure
                 | `Timeout
                 | `Error of exn] -> unit)
      ~(log_refining : 'refinement -> 'task_model -> 'pairs_reads -> dl -> dl -> unit)

      ~memout ~timeout_refine ~timeout_prune
      ~(jump_width : int) ~(refine_degree : int)
      ~(search_temperature : float)
      ~env (* environment data to the input model *)
      ~init_task_model
      (train_pairs : 'value Task.pair list)
      (test_inputs : 'value list)
    : ('typ,'value,'var,'constr,'func) results
  = Common.prof "Learning.learn" (fun () ->
  let norm_dl_model_data = make_norm_dl_model_data ~alpha () in
  let data_of_model ~pruning r m =
    try
      let state_opt =
        let@ prs = Result.to_option (read_pairs ~env m train_pairs) in
        if (* checking that the input model can parse the test inputs *)
          let mi = m.Task_model.input_model in
          List.for_all
            (fun vi -> does_parse_value mi Expr.bindings0 vi)
            test_inputs
        then
          let l = norm_dl_model_data prs in
          let drsi, drso = split_pairs_read prs in
          Some {r; m; prs; drsi; drso; dl_split=l;
                lmd = (if pruning then l.m.io +. l.r.i +. l.d.o else l.md.io);
                lrido = l.r.i +. l.d.o }
        else None in
      let status =
        match state_opt with
        | Some state -> `Success (state.prs, state.drsi, state.drso, state.dl_split, state.lmd)
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
  (* initialization *)
  let r0, m0 = RInit, init_task_model in
  let state0 =
    match data_of_model ~pruning:false r0 m0 with
    | Some state0 -> state0
    | None -> failwith "Learning.learn: invalid initial task model" in

  print_endline "REFINING PHASE";
  let state_refine, result_refining =
    refining1
      ~refine_degree ~jump_width ~timeout_refine ~memout
      ~data_of_model ~task_refinements ~log_refining
      state0 in
  (* pruning phase *) (* TODO: use search to define it *)
  let state_prune_ref = ref state_refine in
  let nsteps_prune_ref = ref 0 in
  let rec loop_prune state =
    log_refining state.r state.m state.prs state.lmd state.lrido;
    let lstate1 = (* computing the [refine_degree] most compressive valid refinements *)
      myseq_find_map_k refine_degree
        (fun (r1,m1_res) ->
          let@ m1 = Result.to_option m1_res in
          match data_of_model ~pruning:true r1 m1 with
          | None -> None (* failure to parse with model m1 *)
          | Some state1 ->
             if state1.lmd < state.lmd && state1.lrido <= state.lrido (* must not degrade parse ranks and output data *)
             then Some state1
             else None)
        (Common.prof "Learning.task_prunings" (fun () ->
             task_prunings state.m state.drsi)) in
    let lstate1 =
      List.sort
        (fun state1 state2 ->
          Stdlib.compare (state1.lmd, state1.r) (state2.lmd, state2.r))
        lstate1 in
    match lstate1 with
    | [] -> ()
    | state1::_ ->
       incr nsteps_prune_ref;
       state_prune_ref := state1; (* recording current state as best state *)
       loop_prune state1
  in
  let state_prune, timed_out_prune, memed_out_prune =
    print_endline "PRUNING PHASE";
    let res_opt =
      Common.do_memout memout (* Mbytes *)
        (fun () ->
          Common.do_timeout_gc (float timeout_prune)
            (fun () ->
              let () =
                match data_of_model ~pruning:true RInit state_refine.m with
                | Some state0prune ->
                   state_prune_ref := state0prune
                | None -> assert false in
              loop_prune !state_prune_ref)) in
    !state_prune_ref, (res_opt = Some None), (res_opt = None) in
  let result_pruning =
    { task_model = state_prune.m;
      pairs_reads = state_prune.prs;
      timed_out = timed_out_prune;
      memed_out = memed_out_prune;
      nsteps = result_refining.nsteps + !nsteps_prune_ref;
      njumps = result_refining.njumps;
      nsteps_sol = result_refining.nsteps_sol;
      njumps_sol = result_refining.njumps_sol;
    } in
  (* finalization *)
  { result_refining;
    result_pruning })
