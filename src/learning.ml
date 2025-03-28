
open Madil_common
open Task_model

(* learning : used by batch only, replicate changes in arc_lis *)

type ('typ,'value,'distrib,'var,'constr,'func) results =
  { result_refining : ('typ,'value,'distrib,'var,'constr,'func) results_phase;
    result_pruning : ('typ,'value,'distrib,'var,'constr,'func) results_phase }
and ('typ,'value,'distrib,'var,'constr,'func) results_phase =
  { task_model : ('typ,'value,'var,'constr,'func) Task_model.task_model;
    pairs_reads : ('typ,'value,'distrib,'constr,'var,'func) Task_model.pairs_reads;
    timed_out : bool;
    memed_out: bool;
    nsteps : int;
    nsteps_sol : int;
    njumps : int;
    njumps_sol : int;
  }

type ('typ,'value,'distrib,'var,'constr,'func) state =
  { r : ('typ,'value,'var,'constr,'func) Task_model.refinement; (* last refinement *)
    m : ('typ,'value,'var,'constr,'func) Task_model.task_model; (* current task model *)
    prs : ('typ,'value,'distrib,'constr,'var,'func) Task_model.pairs_reads; (* pairs reads *)
    drsi : ('typ,'value,'distrib,'constr,'var,'func) Task_model.reads; (* input reads *)
    drso : ('typ,'value,'distrib,'constr,'var,'func) Task_model.reads; (* output reads *)
    dl_split : dl_split; (* all DLs *)
    ldescr : dl; (* whole DL, without ldi in pruning mode *)
    lpred : dl; (* input rank + output rank + output data DL *)
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
  (* choosing a final based on softmax of the reached DL (ldescr), tuned by temperature,
     then choosing a related cont according to a specified conts (make_subconts) *) 
  object
    inherit ['state] conts
    val mutable final_conts : (float (* exp(ldescr) *) * 'state ostate, 'state conts) Mymap.t = Mymap.empty
    val mutable sum_exp : float = 0.

    method is_empty = Mymap.is_empty final_conts

    method goto ostate = ()
    
    method push final_ostate jump_ostates =
      let exp = 2. ** (-. final_ostate#state.ldescr /. temp) in (* lower DL, higher weight *)
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
    1. -. ostate#state.ldescr /. 2. (* ldescr normalized to [0,1] *)
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
        ~(k_state : 'state -> unit)
        (state0 : _ state as 'state) =
  let ostate0 = new ostate state0 in
  let conts = make_conts ostate0 in
  object (self)
    val mutable started = false
    val mutable best_ostate = ostate0
    val mutable all_leaves = []
    val mutable nsteps = 0
    val mutable njumps = 0

    method best_ostate = best_ostate
    method all_leaves = all_leaves
    method nsteps = nsteps
    method njumps = njumps
    
    method rollout (ostate : 'state ostate) : 'state ostate =
      let rec aux ostate jump_ostates =
        let state = ostate#state in
        let best_state = best_ostate#state in
        if state.lpred < best_state.lpred
           || state.lpred = best_state.lpred && state.ldescr < best_state.ldescr then
          best_ostate <- ostate;
        k_state state;
        if state.lpred <= 0. then ( (* no further compression needed *)
          conts#push ostate jump_ostates;
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
      if not started then (
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
             (k : 'state ostate -> bool) (* return true to continue, false to stop iteration *)
           : resource_out =
      let rec aux () =
        match self#next with
        | Some ostate -> if k ostate then aux () else ()
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

let sort_filter_refinements ~refinement_branching lstate1 =
  (* sort refinements, and keep the most compressive and alternative refinements for search *)
  let lstate1 =
    List.sort
      (fun state1 state2 ->
        Stdlib.compare (state1.ldescr, state1.r) (state2.ldescr, state2.r))
      lstate1 in
  match lstate1 with
  | [] -> []
  | state1::others ->
     let _, rev_others = (* retaining only other refinements on same side and path *)
       List.fold_left
         (fun (rank,res) state2 ->
           let ok =
             rank < refinement_branching &&
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

let select_refinements ~refine_degree ~refinement_branching ~data_of_model state refs =
  (* select [refine_degree] compressive refinements from sequence [refs], sort them, and filter alternative refinements *)
  refs
  |> myseq_find_map_k refine_degree
       (fun (r1,m1_res) ->
         let@ m1 = Result.to_option m1_res in
         match data_of_model ~pruning:false r1 m1 with
         | None -> None (* failure to parse with model m1 *)
         | Some state1 ->
            if state1.ldescr < state.ldescr
            then Some state1
            else None)
  |> sort_filter_refinements ~refinement_branching

let refining0
      ~refine_degree ~refinement_branching ~input_branching ~solution_pool
      ~timeout_refine ~memout
      ~data_of_model ~task_refinements ~log_refining
      state0 =
  let refining =
    new search
      ~make_conts:(new conts_mcts ~c:(sqrt 2.))
      ~refinements:(fun state ->
        Common.prof "Learning.task_refinements" (fun () ->
            select_refinements ~refine_degree ~refinement_branching ~data_of_model state
              (task_refinements
                 ~include_expr:true
                 ~include_input:true
                 ~include_output:true
                 state.m state.prs state.drsi state.drso)))
      ~k_state:(fun state -> log_refining state.r state.m state.prs state.ldescr state.lpred)
      state0 in
  let res_out =
    let cpt = ref solution_pool in
    refining#iter
      ~memout ~timeout:timeout_refine
      (fun ostate ->
        if ostate#state.lpred <= 0.
        then (decr cpt; !cpt > 0)
        else true) in
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

let sort_filter_inputs ~input_branching all_leaves : 'state ostate list =
  (* returns k search tree leaves combining compression and diversity of paths *)
  (* best leaf, then best leaf of each 1-prefix, then best leaf of each 2-prefix, etc. *)
  let leaves =
    List.map
      (fun ostate -> (ostate#state.ldescr, List.rev ostate#jumps_sol, ostate))
      all_leaves in
  let sorted_leaves = (* sort by increasing DL *)
    leaves
    |> List.sort Stdlib.compare in
  let rec aux (partition : (dl * int list * 'state ostate) list list) (rev_res : 'state ostate list) =
    let heads, tails =
      List.fold_left
        (fun (heads,tails) part ->
          match part with
          | [] -> assert false
          | [h] -> h::heads, tails (* part becomes empty *)
          | h::t -> h::heads, t::tails)
        ([],[]) partition in
    let sorted_heads = List.sort Stdlib.compare heads in
    let rev_res = (* new result *)
      List.fold_left
        (fun rev_res (_,_,ostate) -> ostate::rev_res)
        rev_res sorted_heads in
    if tails = []
    then List.rev rev_res
    else
      let refined_partition =
        List.fold_left
          (fun res part ->
            let subrevparts =
              Common.group_by (* WARNING: reverse order in subparts *)
                (fun (_,jumps,_) -> match jumps with [] -> None | rank::_ -> Some rank)
                part in
            List.fold_left
              (fun res (key,rev_subpart) ->
                assert (rev_subpart <> []);
                let subpart = (* removing jumps head for next stages *)
                  List.rev_map (* re-establish original order *)
                    (fun (dl,jumps,ostate as x) ->
                      match jumps with
                      | [] -> x
                      | _::jumps1 -> (dl,jumps1,ostate))
                    rev_subpart in
                assert (subpart = List.sort Stdlib.compare subpart); (* REM *)
                subpart :: res)
              res subrevparts)
          [] tails in
      aux refined_partition rev_res
  in
  if sorted_leaves = []
  then []
  else list_take input_branching (aux [sorted_leaves] [])

let refining1
      ~refine_degree ~refinement_branching ~input_branching ~solution_pool
      ~timeout_refine ~memout
      ~data_of_model ~task_refinements ~log_refining
      state0 =
  let make_search_in () =
    new search
      ~make_conts:(new conts_mcts ~c:(sqrt 2.))
      ~refinements:(fun state ->
        Common.prof "Learning.task_refinements_in" (fun () ->
            select_refinements ~refine_degree ~refinement_branching ~data_of_model state
              (task_refinements
                 ~include_expr:false
                 ~include_input:true
                 ~include_output:false
                 state.m state.prs state.drsi state.drso)))
      ~k_state:(fun state -> log_refining state.r state.m state.prs state.ldescr state.lpred)
      state0 in
  let make_search_out (states_in : 'state list) : 'state search =
    new search
      ~make_conts:(new conts_mcts ~c:(sqrt 2.))
      ~refinements:(fun state ->
        if state == state0 && states_in <> []
        then
          List.map
            (fun state -> {state with r = Task_model.RInit})
            states_in
        else
          Common.prof "Learning.task_refinements_out" (fun () ->
              select_refinements ~refine_degree ~refinement_branching ~data_of_model state
                (task_refinements
                   ~include_expr:true
                   ~include_input:false
                   ~include_output:true
                   state.m state.prs state.drsi state.drso)))
      ~k_state:(fun state -> log_refining state.r state.m state.prs state.ldescr state.lpred)
      state0
  in
  print_endline "SEARCH OUT greedy";
  let search_out_0 = make_search_out [] in
  let _res_out =
    search_out_0#iter
      ~memout ~timeout:10
      (fun ostate -> false) in
  let ostate_out = search_out_0#best_ostate in
  if ostate_out#state.lpred <= 0.
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
    let search_in_1 = make_search_in () in
    let res_in =
      search_in_1#iter
        ~memout ~timeout:10
        (fun ostate -> false) in
    let ostate_in = search_in_1#best_ostate in
    (* computing output model greedy *)
    let search_out_1 = make_search_out [ostate_in#state] in
    let _res_out =
      search_out_1#iter
        ~memout ~timeout:10
        (fun ostate -> false) in
    let ostate_out = search_out_1#best_ostate in
    if ostate_out#state.lpred <= 0.
    then (* success *)
      let state_out = ostate_out#state in
      let nsteps = search_in_1#nsteps + search_out_1#nsteps in
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
      let timeout_refine = timeout_refine - 30 in
      let timeout_in = timeout_refine / 6 in (* TODO: add parameter? *)
      let timeout_out = timeout_refine - timeout_in in
      (* searching best input model under timeout *)
      print_endline "SEARCH IN mcts";
      let search_in_2 =
        if res_in.memed_out || res_in.timed_out
        then make_search_in ()
        else search_in_1 in
      let res_in =
        search_in_2#iter
          ~memout ~timeout:timeout_in
          (fun ostate -> true) in
      let ostates_in =
        let all_leaves = search_in_2#all_leaves in
        let selected_leaves =
          sort_filter_inputs ~input_branching all_leaves in
        Printf.printf "SEARCH selected %d/%d input models at those paths\n"
          (List.length selected_leaves)
          (List.length all_leaves);
        List.iteri (fun i ostate ->
            Printf.printf "%2d: dl=%.9f at " i ostate#state.ldescr;
            ostate#print_jumps;
            print_newline ()
          ) selected_leaves;
        selected_leaves in
      (* searching best output model given chosen input model, under timeout *)
      print_endline "SEARCH OUT mcts";
      let search_out_2 =
        let states_in = List.map (fun ostate1 -> ostate1#state) ostates_in in
        make_search_out states_in in
      let res_out =
        search_out_2#iter
          ~memout ~timeout:timeout_out
          (fun ostate -> ostate#state.lpred > 0.) in
      let ostate_out = search_out_2#best_ostate in
      let state_out = ostate_out#state in
      let ostate_in =
        try
          let rank_in = List.hd (List.rev ostate_out#jumps_sol) in
          List.nth ostates_in rank_in
        with _ -> assert false in
      let () = (* showing solution information *)
        Printf.printf "SOL %d + %d steps\n" ostate_in#nsteps_sol ostate_out#nsteps_sol;
        Printf.printf "IN  dl=%.3f at path " ostate_in#state.ldescr;
        ostate_in#print_jumps; print_newline ();
        Printf.printf "OUT dl=%.3f at path " ostate_out#state.ldescr;
        ostate_out#print_jumps; print_newline () in
      state_out,
      { task_model = state_out.m;
        pairs_reads = state_out.prs;
        timed_out = res_out.timed_out; (* no stop criteria for input *)
        memed_out = res_in.memed_out || res_out.memed_out;
        nsteps = search_in_2#nsteps + search_out_2#nsteps;
        njumps = search_in_2#njumps + search_out_2#njumps;
        nsteps_sol = ostate_in#nsteps_sol + ostate_out#nsteps_sol - 1; (* -1 because first output step chooses input model *)
        njumps_sol = ostate_in#njumps_sol + ostate_out#njumps_sol }
    )
  )

let learn
      ~(alpha : float)
      ~(read_pairs :
          (('t,'value,'var,'constr,'func) Task_model.task_model as 'task_model) ->
          'value Task.pair list -> 'distrib -> 'distrib ->
          (('typ,'value,'distrib,'constr,'var,'func) Task_model.pairs_reads as 'pairs_reads) result)
      ~(does_parse_value :
          ('t,'value,'var,'constr,'func) Model.model ->
          ('var,'typ,'value) Expr.bindings ->
          'value -> 'distrib -> bool)
      ~(task_refinements :
          include_expr:bool ->
          include_input:bool ->
          include_output:bool ->
          'task_model -> 'pairs_reads ->
          (('typ,'value,'distrib,'constr,'var,'func) Task_model.reads as 'reads) -> 'reads ->
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
      ~(refinement_branching : int) ~(input_branching : int)
      ~(refine_degree : int) ~(solution_pool : int)
      ~(search_temperature : float)
      ~init_task_model
      (train_pairs : 'value Task.pair list)
      (test_inputs : 'value list)
      (distrib_i : 'distrib)
      (distrib_o : 'distrib)
    : ('typ,'value,'distrib,'var,'constr,'func) results
  = Common.prof "Learning.learn" (fun () ->
  let norm_dl_model_data = make_norm_dl_model_data ~alpha () in
  let data_of_model ~pruning r m =
    try
      let state_opt =
        let@ prs = Result.to_option (read_pairs m train_pairs distrib_i distrib_o) in
        if (* checking that the input model can parse the test inputs *)
          let mi = m.Task_model.input_model in
          List.for_all
            (fun vi -> does_parse_value mi Expr.bindings0 vi distrib_i)
            test_inputs
        then
          let l = norm_dl_model_data prs in
          let drsi, drso = split_pairs_read prs in
          Some {r; m; prs; drsi; drso; dl_split=l;
                ldescr = (if pruning then l.m.io +. l.pred else l.descr);
                lpred = l.pred }
        else None in
      let status =
        match state_opt with
        | Some state -> `Success (state.prs, state.drsi, state.drso, state.dl_split, state.ldescr)
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
    refining0
      ~refine_degree ~refinement_branching ~input_branching ~solution_pool
      ~timeout_refine ~memout
      ~data_of_model ~task_refinements ~log_refining
      state0 in
  (* pruning phase *) (* TODO: use search to define it *)
  let state_prune_ref = ref state_refine in
  let nsteps_prune_ref = ref 0 in
  let rec loop_prune state =
    log_refining state.r state.m state.prs state.ldescr state.lpred;
    let lstate1 = (* computing the [refine_degree] most compressive valid refinements *)
      myseq_find_map_k refine_degree
        (fun (r1,m1_res) ->
          let@ m1 = Result.to_option m1_res in
          match data_of_model ~pruning:true r1 m1 with
          | None -> None (* failure to parse with model m1 *)
          | Some state1 ->
             if state1.ldescr < state.ldescr && state1.lpred <= state.lpred (* must not degrade parse ranks and output data *)
             then Some state1
             else None)
        (Common.prof "Learning.task_prunings" (fun () ->
             task_prunings state.m state.drsi)) in
    let lstate1 =
      List.sort
        (fun state1 state2 ->
          Stdlib.compare (state1.ldescr, state1.r) (state2.ldescr, state2.r))
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
