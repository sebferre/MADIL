
open Madil_common

(* === command line options === *)

let training = ref true (* should be set to false on evaluation set *)
let start_rank = ref max_int
let timeout_refine = ref 60
let timeout_prune = ref 10
let timeout_predict = ref 10
let verbose = ref 1
let viz = ref false
let pause = ref 0. (* TODO: not used in code *)

(* === printing and checking functions === *)

let print_dl_md
      ~alpha =
  fun psr -> (* model+data DL *)
  let (lmi,lmo,lm), (ldi,ldo,ld), (lmdi, lmdo, lmd) =
    Task_model.dl_model_data ~alpha psr in
  Printf.printf "DL input  with Mi: L = %.1f + %.1f = %.1f\n" lmi ldi lmdi;
  Printf.printf "DL output with Mo: L = %.1f + %.1f = %.1f\n" lmo ldo lmdo;
  Printf.printf "DL input+output M: L = %.1f + %.1f = %.1f\n" lm ld lmd;
  ldo

let print_dl_task_model
      ~read_pairs
      ~alpha
      ~env0 =
  fun name task model ->
  read_pairs
    ~pruning:false
    ~env:env0
    model task.Task.train
  |> Result.fold
       ~ok:(fun psr -> ignore (print_dl_md ~alpha psr))
       ~error:(fun exn -> raise exn)

(* === monitoring learning === *)

type measures = (string * [`Tasks|`Bits|`MRR|`Seconds] * float) list

let print_measures count ms =
  List.iter
    (fun (a,t,v) ->
     match t with
     | `Tasks -> Printf.printf "%s = %.2f tasks (%.2f%%)\n" a v (100. *. v /. float count)
     | `Bits -> Printf.printf "%s = %.1f bits (%.1f bits/task)\n" a v (v /. float count)
     | `MRR -> Printf.printf "%s = %.2f\n" a (v /. float count)
     | `Seconds -> Printf.printf "%s = %.1f sec (%.1f sec/task)\n" a v (v /. float count))
    ms;
  print_newline ()

let apply_model
      ~apply =
  fun ~env m x_i info_o ->
  let res_opt =
    Common.do_timeout !timeout_predict (fun () ->
        apply ~env m x_i info_o) in
  match res_opt with
  | Some res -> res
  | None -> Result.Error (Failure "The model could not be applied in the allocated timeout.")
  
let score_learned_model
      ~(input_of_data : ('value,'dconstr) Data.data -> 'input)
      ~(xp_data : ('value,'dconstr) Data.data html_xp)
      ~read (* model read *)
      ~kind_i (* input top kind *)
      ~env0 (* input env data *)
      ~apply
      ~info_o (* generation output info *)
      
      name
      (m : ('t,'constr,'func) Task_model.task_model)
      (train_test : [ `TRAIN of ('value,'dconstr,'constr,'func) Task_model.pairs_reads
                    | `TEST ])
      (examples : 'input Task.pair list)
    : float * float * float (* micro success, macro success, MRR *) =
  let pp_data = Xprint.to_stdout (xp_data ~html:false) in
  let _, nb_ex, nb_correct, sum_rrank =
    List.fold_left
      (fun (i,nb_ex,nb_correct,sum_rrank) {Task.input; output} ->
        Printf.printf "\n## instance %d\n" i;
        if !training then (
          match train_test with
          | `TRAIN psr ->
             print_endline "\n> Input and output best reading:";
             let reads_pair = try List.nth psr.reads (i-1) with _ -> assert false in
             Common.sub_list reads_pair 0 1
             |> List.iter (fun (gri, gro, _) ->
                    let {Model.env=envi; data=gdi; dl=dli} = gri in
                    let {Model.env=envo; data=gdo; dl=dlo} = gro in
                    print_newline ();
                    pp_data gdi; Printf.printf "   (%.1f bits)\n" dli;
                    pp_data gdo; Printf.printf "   (%.1f bits)\n" dlo)
                    (* TODO if !viz then
                      Grid.pp_grids [Model.grid_of_data_as_template gdi.data;
                                     Model.grid_of_data_as_template gdo.data]) *)
          | `TEST -> ()
        );
        if !verbose >= 2 then (
          print_endline "\n> Best input readings:";
          let input_reads =
            match train_test with
            | `TRAIN psr -> Result.Ok (List.nth psr.Task_model.inputs_reads (i-1))
            | `TEST -> read
                         ~dl_assuming_contents_known:false
                         ~env:env0 ~bindings:Path.bindings0
                         kind_i m.Task_model.input_model input in
          ( match input_reads with
            | Result.Ok reads ->
               List.iter
                 (fun {Model.data=gdi; dl=dli} ->
                   pp_data gdi;
                   Printf.printf "  (%.1f bits)\n" dli)
                 reads
            | Result.Error _ ->
               print_endline "(No input readings)"
          ));
        print_endline "\n> Output prediction from input (up to 3 trials):";
        let score, rank, label, _failed_derived_grids =
	  match apply_model ~apply ~env:env0 m input info_o with
	  | Result.Ok gdi_gdo_s ->
             List.fold_left
               (fun (score,rank,label,failed_derived_grids) (gdi, gdo) ->
                 let derived = input_of_data gdo in
                 if score=1 then
                   score, rank, label, failed_derived_grids (* already success *)
                 else if rank > 3 then
                   score, rank, label, failed_derived_grids (* at most 3 trials *)
                 else if List.mem derived failed_derived_grids then
                   score, rank, label, failed_derived_grids (* already derived that grid and it failed *)
                 else ( (* score=0 && rank <= 3 && new derived_grid *)
                   Printf.printf ">> Trial %d\n" rank;
                   if !training then (
                     print_string "di: "; pp_data gdi; print_newline ();
                     print_string "do: "; pp_data gdo; print_newline ()
                   (* TODO if !grid_viz then Grid.pp_grids [Model2.grid_of_data_as_template gdi.data] *)
                   );
	           ( if derived = output
		     then (
                       if !training then (
                         print_endline "correct output grid"
                       (* TODO if !viz then Grid.pp_grids [derived] *)
                       );
                       1, rank, "SUCCESS", failed_derived_grids
                     )
		     else (
                        (* TODO if !training then (
                          print_grid_diff ~grid:output ~derived_grid:derived diff); *)
                       0, rank+1, "FAILURE", derived::failed_derived_grids )
                   )
               ))
               (0,1,"FAILURE",[]) gdi_gdo_s
	  | Result.Error exn ->
             print_endline (Printexc.to_string exn);
             0, 0, "ERROR", [] in
        let tt = match train_test with `TRAIN _ -> "TRAIN" | `TEST -> "TEST" in
        let str_rank =
          if score = 0
          then "-"
          else
            match rank with
            | 1 -> "1st"
            | 2 -> "2nd"
            | 3 -> "3rd"
            | _ -> assert false in
	Printf.printf "\n%s %s/%d: %d %s (%s)\n" tt name i score str_rank label;
	i+1,
        nb_ex+1,
        nb_correct+score,
        (if score=1 then sum_rrank +. 1. /. float rank else sum_rrank))
      (1,0,0,0.) examples in
  let micro = float nb_correct /. float nb_ex in
  let macro = if nb_correct = nb_ex then 1. else 0. in
  let mrr = sum_rrank /. float nb_ex in
  micro, macro, mrr
       
let print_learned_model
      ~input_of_data
      ~xp_data ~xp_task_model
      ~read ~learn ~apply
      ~alpha ~refine_degree
      ~env0 ~kind_i ~init_task_model ~info_o
      (name : string) (task : 'a Task.task)
    : measures =
  let pp_task_model = Xprint.to_stdout (xp_task_model ~html:false) in
  Common.prof "Test.print_learned_model" (fun () ->
  let runtime, res =
    Common.chrono (fun () ->
        learn
          ~timeout_refine:(!timeout_refine)
          ~timeout_prune:(!timeout_prune)
          ~beam_width:1 ~refine_degree
          ~env:env0
          ~init_task_model
          task.train)
  in
  match res with
  | Common.Exn exn ->
      print_endline (Printexc.to_string exn);
      Printexc.print_backtrace stdout;
      let ms =
        [ "runtime-learning", `Seconds, runtime;
          "bits-train-error", `Bits, 0.; (* dummy value *)
	  "acc-train-micro", `Tasks, 0.;
	  "acc-train-macro", `Tasks, 0.;
          "acc-train-mrr", `MRR, 0.;
	  "acc-test-micro", `Tasks, 0.;
	  "acc-test-macro", `Tasks, 0.;
          "acc-test-mrr", `MRR, 0.;
        ] in
      ms    
  | Common.Val ((m_refine,psr_refine,timed_out_refine), (m_prune,psr_prune,timed_out_prune)) ->
     if timed_out_refine then print_endline "TIMEOUT";
     print_endline "\n# Learned model (decriptive, before pruning):";
     pp_task_model m_refine;
     print_newline ();
     let _ = print_dl_md ~alpha psr_refine in
     print_endline "\n# Learned model (predictive, after pruning):";
     pp_task_model m_prune;
     print_newline ();
     let ldo = print_dl_md ~alpha psr_prune in
     print_endline "\n# train input/output grids";
     let micro_train, macro_train, mrr_train =
       score_learned_model
         ~xp_data ~read ~input_of_data ~kind_i ~env0 ~apply ~info_o
         name m_prune (`TRAIN psr_prune) task.train in
     print_endline "\n# Test input/output grids";
     let micro_test, macro_test, mrr_test =
       score_learned_model
         ~xp_data ~read ~input_of_data ~kind_i ~env0 ~apply ~info_o
         name m_prune (`TEST) task.test in
     print_endline "\n# Performance measures on task";
     let ms =
       [ "runtime-learning", `Seconds, runtime;
         "bits-train-error", `Bits, ldo;
	 "acc-train-micro", `Tasks, micro_train;
	 "acc-train-macro", `Tasks, macro_train;
         "acc-train-mrr", `MRR, mrr_train;
	 "acc-test-micro", `Tasks, micro_test;
	 "acc-test-macro", `Tasks, macro_test;
         "acc-test-mrr", `MRR, mrr_test;
       ] in
     print_measures 1 ms;
     ms)
               

(* === main === *)
  
let task_of_name
      ~data_of_json
      dir name =
  Task.from_file ~data_of_json (Filename.concat dir name)

let process_task
      ~input_of_data
      ~xp_data ~xp_task_model
      ~read ~learn ~apply
      ~read_pairs
      ~alpha ~refine_degree
      ~get_init_task_model
      name task
      count sum_ms =
      let env0, kind_i, init_task_model, info_o = get_init_task_model name task in
      print_endline "\n# evaluating init_task_model";
      print_dl_task_model
        ~read_pairs ~alpha ~env0
        name task init_task_model;
      print_endline "\n# learning a model for train pairs";
      let ms =
        print_learned_model
          ~xp_data ~xp_task_model
          ~read ~learn ~apply ~input_of_data
          ~alpha ~env0 ~kind_i ~info_o
          ~init_task_model ~refine_degree name task in
      count := !count+1;
      sum_ms :=
	if !sum_ms = []
	then ms
	else
	  List.map2
	    (fun (a,t,sum_v) (a',t',v) ->
	     assert (a=a' && t=t');
	     (a,t,sum_v+.v))
	    !sum_ms ms

let summarize_tasks count sum_ms =
  Printf.printf "\n## performance measures averaged over %d tasks\n" count;
  print_measures count sum_ms;
  flush stdout
  
let main
      ~(data_of_json : Yojson.Safe.t -> 'input)
      ~(input_of_data : 'data -> 'input)
      ~(xp_data : (('value,'dconstr) Data.data as 'data) html_xp)
      ~(xp_task_model : (('t,'constr,'func) Task_model.task_model as 'task_model) html_xp)
      ~(read : dl_assuming_contents_known:bool -> env:'data -> bindings:(('value,'constr) Path.bindings as 'bindings) -> ('t Kind.kind as 'kind) -> (('constr,'func) Model.model as 'model) -> 'input -> 'read list result) 
      ~(learn : timeout_refine:int -> timeout_prune:int -> beam_width:int -> refine_degree:int -> env:'data -> init_task_model:'task_model -> 'input Task.pair list -> ('task_model * 'pairs_reads * bool) double)
      ~(apply : env:'data -> 'task_model -> 'input -> 'info -> ('data * 'data) list result)
      ~(read_pairs : pruning:bool -> env:'data -> 'task_model -> 'input Task.pair list -> 'pairs_reads result)
      ~(alpha : float)
      ~(refine_degree : int)
      ~(get_init_task_model : string -> 'input Task.task -> 'data * 'kind * 'task_model * 'info)
      ()
    : unit =
  let () = Printexc.record_backtrace true in
  let dir = ref "." in
  let names = ref [] in
  Arg.parse
    ["-dir", String (fun s ->
                 dir := s;
                 names :=
                   Sys.readdir !dir
                   |> Array.to_list
                   |> List.filter (fun name -> Filename.check_suffix name ".json")
                   |> List.sort Stdlib.compare), "Find tasks in the chosen directory";
     "-all", Unit (fun () -> ()), "Use all tasks in the chosen directory (default)";
     "-sample",
        Int (fun n -> Random.self_init (); names := Common.list_sample ~size:n !names),
	"Use the first N tasks in the chosen set";
     "-tasks", String (fun ids ->
	     let ids = String.split_on_char ',' ids in
	     names :=
	       !names
	       |> List.filter
		    (fun name ->
                      Filename.check_suffix name ".json"
		      && ids
		         |> List.exists
			      (fun id ->
                                let n_id = String.length id in
			        n_id <= String.length name && String.sub name 0 n_id = id))), "Use the tasks specified by their prefix (comma-separated)";
     "-r", Set_int start_rank, "Start processing with this task rank (only useful for error recovery)";
     "-eval", Unit (fun () -> training := false), "Evaluation mode to avoid disclosing task contents";
     "-timeout_refine", Set_int timeout_refine, "Learning/refining timeout per task (default: 60s)";
     "-timeout_prune", Set_int timeout_prune, "Learning/pruning timeout per task (default: 10s)";
     "-viz", Set viz, "Show train strings, as understood by the model";
     "-pause", Set_float pause, "Time delay (in seconds, default=0.0) at each step during learning, useful in combination with -viz";
     "-v", Set_int verbose, "Verbose level (default=1)";
    ]
    (fun str -> ())
    "test [-dir PATH] [-all|-sample N|-tasks ID,ID,...] [-r N] [-alpha N] [-timeout_refine N] [-timeout_prune] [-viz [-pause T]] [-v N]";
  
  print_endline "## options";
  Printf.printf "alpha = %.1f\n" alpha;
  Printf.printf "mode = %s\n" (if !training then "training" else "evaluation");
  Printf.printf "timeout_refine = %d\n" !timeout_refine;
  Printf.printf "timeout_prune = %d\n" !timeout_prune;
  Printf.printf "timeout_predict = %d\n" !timeout_predict;
  print_newline ();
  
  let nb_tasks = List.length !names in
  let count = ref 0 in
  let sum_ms = ref [] in
  let _ =
    List.fold_left
      (fun rank name ->
        if rank <= !start_rank then (
          let task = task_of_name ~data_of_json !dir name in
          print_endline "=====================================";
          Printf.printf "[-%d] Checking task %s: %d train, %d test\n"
	    rank name
	    (List.length task.Task.train)
	    (List.length task.Task.test);
          process_task
            ~xp_data ~xp_task_model
            ~read ~learn ~apply ~input_of_data
            ~read_pairs
            ~alpha ~refine_degree
            ~get_init_task_model
            name task
            count sum_ms
        );
       rank-1)
      nb_tasks !names in
  summarize_tasks !count !sum_ms;
  Common.prerr_profiling ()
