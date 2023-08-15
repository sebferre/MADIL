
open Madil_common
open Kind
open Data
open Path
open Model

(* task models *)
   
type ('t,'constr,'func) task_model =
  { input_kind : 't kind;
    input_model : ('constr,'func) model; (* no reference *)
    nb_env_paths : int; (* nb of visible paths in input model *)
    output_kind : 't kind;
    output_model : ('constr,'func) model
  }
       
let xp_task_model
      ~(xp_model : ('constr,'func) model html_xp)
    :  ('t,'constr,'func) task_model html_xp =
  fun ~html print m ->
  xp_model ~html print m.input_model;
  print#string (if html then " ➜ " else "\n➜\n");
  xp_model ~html print m.output_model

(* pair reading and encoding *)
  
type ('value,'dconstr,'constr,'func) pairs_reads =
  (* result of reading a list of pairs of grids *)
  { dl_mi : dl; (* input model DL *)
    dl_mo : dl; (* output model DL *)
    inputs_reads : (('value,'dconstr,'constr,'func) read as 'read) list list; (* outer list over example inputs, inner list over parses *)
    reads : ('read * 'read * dl) list list; (* outer list over examples, inner list over parses, sorted in increasing DL *)
  }

let read_pairs
      ~(dl_task_model : (('t,'constr,'func) task_model as 'task_model) -> dl * dl)
      ~(read : ?dl_assuming_contents_known:bool ->
               env:(('value,'dconstr) data as 'data) ->
               bindings:(('value,'constr) bindings as 'bindings) ->
               't kind -> (('constr,'func) model as 'model) -> 'input -> 'read list result)
      ~(get_bindings : 'model -> 'data -> 'bindings)
      
      ?(pruning = false)
      ~(env : 'data)
      (m : 'task_model)
      (pairs : 'input Task.pair list)
    : ('value,'dconstr,'constr,'func) pairs_reads result =
  Common.prof "Task_model.read_pairs" (fun () ->
  (* takes model, input env+docs, output docs *)
  let dl_mi, dl_mo = dl_task_model m in
  let| inputs_reads_reads =
    pairs
    |> list_map_result
         (fun {Task.input; output} ->
           let| input_reads =
             read
               ~dl_assuming_contents_known:pruning
               ~env ~bindings:bindings0
               m.input_kind m.input_model input in (* no diff allowed during training *)
           let| pair_reads = 
             let+|+ ri = Result.Ok input_reads in      
             let+|+ ro =
               read
                 ~env:ri.data ~bindings:(get_bindings m.input_model ri.data)
                 m.output_kind m.output_model output in
             let dl = ri.dl +. ro.dl in
             Result.Ok [(ri,ro,dl)] in
           let pair_reads =
             pair_reads
             |> List.stable_sort (fun (_,_,dl1) (_,_,dl2) -> dl_compare dl1 dl2)
           (* TODO |> limit_dl (fun (_,_,dl) -> dl) *) in (* bounding by dl_factor *) 
           Result.Ok (input_reads, pair_reads)) in
  let inputs_reads, reads = List.split inputs_reads_reads in
  Result.Ok {dl_mi; dl_mo; inputs_reads; reads})

type ('value,'dconstr,'constr,'func) reads =
  { dl_m : dl; (* DL of the model *)
    reads : ('value,'dconstr,'constr,'func) read list list; (* outer list over docs, inner list over parses, sorted in increasing DL *)
  }
  
let split_pairs_read
      (prs : ('value,'dconstr,'constr,'func) pairs_reads) : ('value,'dconstr,'constr,'func) reads double =
  let project_reads proj =
    List.map
      (fun pair_reads ->
        pair_reads
        |> List.map proj)
      prs.reads in
  let inputs_reads = project_reads (fun (dri,_,_) -> dri) in
  let outputs_reads = project_reads (fun (_,dro,_) -> dro) in
  let dsri = { dl_m = prs.dl_mi; reads = inputs_reads } in
  let dsro = { dl_m = prs.dl_mo; reads = outputs_reads } in
  dsri, dsro

  
(* pair encoding *)

let dl_model_data
      ~(alpha : float)
      (psr : ('value,'dconstr,'constr,'func) pairs_reads) : dl triple triple = (* QUICK *)
  let lmi = psr.dl_mi in
  let lmo = psr.dl_mo in
  let ldi, ldo =
    List.fold_left
      (fun (ldi,ldo) ->
        function
        | (ri,ro,dl)::_ -> (ldi +. ri.dl, ldo +. ro.dl)
        | _ -> assert false)
      (0.,0.) psr.reads in
  let ldi, ldo = alpha *. ldi, alpha *. ldo in
  let lmdi = lmi +. ldi in
  let lmdo = lmo +. ldo in
  (lmi, lmo, lmi +. lmo),
  (ldi, ldo, ldi +. ldo),
  (lmdi, lmdo, lmdi +. lmdo)

let make_norm_dl_model_data
      ~(alpha : float)
      () : ('value,'dconstr,'constr,'func) pairs_reads -> dl triple triple =
  let lmdi0 = ref (-1.) in
  let lmdo0 = ref (-1.) in
  fun psr ->
  let (lmi,lmo,lm), (ldi,ldo,ld), (lmdi,lmdo,lmd) =
    dl_model_data ~alpha psr in
  let () = (* setting initial DLs *)
    if !lmdi0 < 0.
    then ( lmdi0 := lmdi; lmdo0 := lmdo ) in
  let nlmi, nldi, nlmdi = lmi /. !lmdi0, ldi /. !lmdi0, lmdi /. !lmdi0 in
  let nlmo, nldo, nlmdo = lmo /. !lmdo0, ldo /. !lmdo0, lmdo /. !lmdo0 in
  (nlmi, nlmo, nlmi +. nlmo),
  (nldi, nldo, nldi +. nldo),
  (nlmdi, nlmdo, nlmdi +. nlmdo)


(* applying a task model to an input *)

let apply
      ~(read : ?dl_assuming_contents_known:bool ->
               env:(('value,'dconstr) data as 'data) ->
               bindings:(('value,'constr) bindings as 'bindings) ->
               't kind -> (('constr,'func) model as 'model) -> 'input ->
               ('value,'dconstr,'constr,'func) read list result)
      ~(get_bindings : 'model -> 'data -> 'bindings)
      ~(write : bindings:'bindings ->
                't kind -> 'model -> 'info -> 'data result)
      ~(env : 'data)
      (m : ('t,'constr,'func) task_model) (x_i : 'input) (info_o : 'info)
    : (('data * 'data) list, exn) Result.t =
  Common.prof "Model.apply" (fun () ->
  let+|+ read_i =
    read
      ~dl_assuming_contents_known:true ~env ~bindings:bindings0
      m.input_kind m.input_model x_i in
  let data_i = read_i.data in
  let| data_o =
    write
      ~bindings:(get_bindings m.input_model data_i)
      m.output_kind m.output_model info_o in
  Result.Ok [(data_i, data_o)])

(* refinements *)
  
type ('constr,'func) refinement =
  | RInit
  | Rinput of 'constr path * ('constr,'func) model * int (* support *) * dl (* estimated result DL *)
  | Routput of 'constr path * ('constr,'func) model * int (* support *) * dl (* estimated result DL *)

let refinement_support : ('constr,'func) refinement -> int = function
  | RInit -> (-1)
  | Rinput (_,_,supp,_) -> supp
  | Routput (_,_,supp,_) -> supp             

let xp_refinement
      ~(xp_path : 'constr path html_xp)
      ~(xp_model : ('constr,'func) model html_xp)
    : ('constr,'func) refinement html_xp =
  let rec aux ~html print = function
    | RInit -> print#string "init"
    | Rinput (p,ri,supp,dl') -> aux2 ~html print " In." p ri supp dl' "i"
    | Routput (p,ro,supp,dl') -> aux2 ~html print " Out." p ro supp dl' "o"
  and aux2 ~html print in_out p r supp dl' i_o =
    if dl' <> 0. (* undefined value *) then
      print#string (Printf.sprintf " / ~%.3f%s)  " dl' i_o);
    print#string in_out;
    xp_path ~html print p;
    print#string " ← ";
    xp_model ~html print r;
    if supp <> 0 (* undefined value *) then
      aux_support ~html print supp
  and aux_support ~html print supp =
    print#string " ("; print#int supp; print#string ")"
  in
  aux

let refine (r : ('constr,'func) refinement) (m : ('t,'constr,'func) task_model)
    : (('constr,'func) refinement * ('t,'constr,'func) task_model) result =
  match r with
  | RInit -> Result.Error (Failure "Task_model.refine")
  | Rinput (p,ri,supp,dl') ->
     Result.Ok (r, {m with input_model = Model.refine p ri m.input_model})
  | Routput (p,ro,supp,dl') ->
     Result.Ok (r, {m with output_model = Model.refine p ro m.output_model})

