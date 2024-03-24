
open Madil_common

module Make (Domain : Madil.DOMAIN) =
  struct
    include Madil.Make(Domain)

(* === command line options === *)

let training = ref true (* should be set to false on evaluation set *)
let start_rank = ref max_int
let memout = ref 5000
let timeout_refine = ref 60
let timeout_prune = ref 10
let timeout_predict = ref 10
let verbose = ref 1
let viz = ref false
let pause = ref 0. (* TODO: not used in code *)

(* === printing and checking functions === *)

let print_dl_md psr = (* model+data DL *)
  let l : Task_model.dl_split = Task_model.dl_model_data ~alpha:(!alpha) psr in
  Printf.printf "DL input  with Mi: L = %.1f + %.1f = %.1f\n" l.m.i l.d.i l.md.i;
  Printf.printf "DL output with Mo: L = %.1f + %.1f = %.1f\n" l.m.o l.d.o l.md.o;
  Printf.printf "DL input+output M: L = %.1f + %.1f = %.1f\n" l.m.io l.d.io l.md.io;
  l.r.i +. l.d.o

let print_dl_task_model ~env name task model =
  read_pairs
    ~env
    model task.Task.train
  |> Result.fold
       ~ok:(fun psr -> ignore (print_dl_md psr))
       ~error:(fun exn -> raise exn)

(* === monitoring learning === *)

type measures = (string * [`Tasks|`Bits|`MRR|`Seconds|`Steps|`Jumps|`ModelElts] * float) list

let print_measures count ms =
  List.iter
    (fun (a,t,v) ->
     match t with
     | `Tasks -> Printf.printf "%s = %.2f tasks (%.2f%%)\n" a v (100. *. v /. float count)
     | `Bits -> Printf.printf "%s = %.1f bits (%.1f bits/task)\n" a v (v /. float count)
     | `MRR -> Printf.printf "%s = %.2f\n" a (v /. float count)
     | `Seconds -> Printf.printf "%s = %.1f sec (%.1f sec/task)\n" a v (v /. float count)
     | `Steps -> Printf.printf "%s = %.0f steps (%.1f steps/task)\n" a v (v /. float count)
     | `Jumps -> Printf.printf "%s = %.0f jumps (%.1f jumps/task)\n" a v (v /. float count)
     | `ModelElts -> Printf.printf "%s = %.0f model elts (%.1f elts/task)\n" a v (v /. float count))
    ms;
  print_newline ()

let apply_model ~env m v_i info_o =
  try
    let res_opt =
      Common.do_timeout !timeout_predict (fun () ->
          apply ~env m v_i info_o) in
    match res_opt with
    | Some res -> res
    | None -> Result.Error (Failure "The model could not be applied in the allocated timeout.")
  with exn -> Result.Error exn
  
let score_learned_model
      ~env (* input env data *)
      ~info_o (* generation output info *)      
      name
      (m : task_model)
      (train_test : [ `TRAIN of pairs_reads
                    | `TEST ])
      (examples : task_pair list)
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
            | `TEST ->
               let input_reads, _ =
                 Myseq.take (!max_nb_reads)
                   (read
                      ~env ~bindings:Expr.bindings0
                      m.Task_model.input_model input) in
               if input_reads = []
               then Result.Error Not_found
               else Result.Ok input_reads in
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
	  match apply_model ~env m input info_o with
	  | Result.Ok gdi_gdo_s ->
             List.fold_left
               (fun (score,rank,label,failed_derived_grids) (gdi, gdo, dl) ->
                 let derived = Data.value gdo in
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
                     print_string "do: "; pp_data gdo; print_newline ();
                     Printf.printf "DL = %.3f\n" dl; 
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
      ~env ~init_task_model ~info_o
      (name : string) (task : task)
    : measures =
  let pp_task_model = Xprint.to_stdout (xp_task_model ~html:false) in
  Common.prof "Test.print_learned_model" (fun () ->
  let runtime, res =
    Common.chrono (fun () ->
        learn
          ~memout:(!memout)
          ~timeout_refine:(!timeout_refine)
          ~timeout_prune:(!timeout_prune)
          ~jump_width:(!jump_width) ~refine_degree:(!max_refinements)
          ~env ~init_task_model
          task.train)
  in
  match res with
  | Common.Exn exn ->
      print_endline (Printexc.to_string exn);
      Printexc.print_backtrace stdout;
      let ms =
        [ "runtime-learning", `Seconds, runtime;
          "nb-steps", `Steps, 0.;
          "nb-steps-sol", `Steps, 0.;
          "nb-jumps", `Jumps, 0.;
          "model-size", `ModelElts, 0.;
          "bits-train-error", `Bits, 0.; (* dummy value *)
	  "acc-train-micro", `Tasks, 0.;
	  "acc-train-macro", `Tasks, 0.;
          "acc-train-mrr", `MRR, 0.;
	  "acc-test-micro", `Tasks, 0.;
	  "acc-test-macro", `Tasks, 0.;
          "acc-test-mrr", `MRR, 0.;
        ] in
      ms    
  | Common.Val (res : _ Learning.results) -> (* ((m_refine,psr_refine,timed_out_refine), (m_prune,psr_prune,timed_out_prune)) -> *)
     let learned_task_model = res.result_pruning.task_model in
     if res.result_refining.timed_out then print_endline "TIMEOUT";
     if res.result_refining.memed_out then print_endline "MEMOUT";
     print_endline "\n# Learned model (decriptive, before pruning):";
     pp_task_model res.result_refining.task_model;
     print_newline ();
     let _ = print_dl_md res.result_refining.pairs_reads in
     print_endline "\n# Learned model (predictive, after pruning):";
     pp_task_model learned_task_model;
     print_newline ();
     let lrido = print_dl_md res.result_pruning.pairs_reads in
     print_endline "\n# train input/output grids";
     let micro_train, macro_train, mrr_train =
       score_learned_model
         ~env ~info_o
         name learned_task_model (`TRAIN res.result_pruning.pairs_reads) task.train in
     print_endline "\n# Test input/output grids";
     let micro_test, macro_test, mrr_test =
       score_learned_model
         ~env ~info_o
         name learned_task_model (`TEST) task.test in
     print_endline "\n# Performance measures on task";
     let ms =
       [ "runtime-learning", `Seconds, runtime;
         "nb-steps", `Steps, float res.result_pruning.nsteps;
         "nb-steps-sol", `Steps, float res.result_pruning.nsteps_sol;
         "nb-jumps", `Jumps, float res.result_pruning.njumps;
         "model-size", `ModelElts, float (size_task_model learned_task_model);
         "bits-train-error", `Bits, lrido;
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
  
let task_of_name dir name =
  task_from_file (Filename.concat dir name)

let process_task
      name task
      count sum_ms =
      let {env; varseq; input_model; output_model; output_generator_info=info_o} = get_init_config name task in
      let init_task_model = make_task_model varseq input_model output_model in
      print_endline "\n# evaluating init_task_model";
      print_dl_task_model ~env name task init_task_model;
      print_endline "\n# learning a model for train pairs";
      let ms =
        print_learned_model
          ~env ~info_o
          ~init_task_model name task in
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
  
let main () : unit =
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
     "-timeout_predict", Set_int timeout_predict, "Prediction timeout per test case (default: 10s)";
     "-viz", Set viz, "Show train strings, as understood by the model";
     "-pause", Set_float pause, "Time delay (in seconds, default=0.0) at each step during learning, useful in combination with -viz";
     "-v", Set_int verbose, "Verbose level (default=1)";
    ]
    (fun str -> ())
    "test [-dir PATH] [-all|-sample N|-tasks ID,ID,...] [-r N] [-eval] [-timeout_refine N] [-timeout_prune] [-viz [-pause T]] [-v N]";
  
  print_endline "## options";
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
          let task = task_of_name !dir name in
          print_endline "=====================================";
          Printf.printf "[-%d] Checking task %s: %d train, %d test\n"
	    rank name
	    (List.length task.Task.train)
	    (List.length task.Task.test);
          process_task
            name task
            count sum_ms;
          reset_memoization ()
        );
       rank-1)
      nb_tasks !names in
  summarize_tasks !count !sum_ms;
  Common.prerr_profiling ()

  end
