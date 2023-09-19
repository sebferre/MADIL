
open Madil_common
open Kind
open Data
open Model

(* task models *)
   
type ('t,'var,'constr,'func) task_model =
  { input_model : ('t,'var,'constr,'func) model; (* no reference *)
    input_varseq : 'var Myseq.t;
    nb_env_vars : int; (* nb of visible vars in input model *)
    output_model : ('t,'var,'constr,'func) model;
    output_varseq : 'var Myseq.t
  }
       
let xp_task_model
      ~(xp_model : ('t,'var,'constr,'func) model html_xp)
    :  ('t,'var,'constr,'func) task_model html_xp =
  fun ~html print m ->
  xp_model ~html print m.input_model;
  print#string "\n ⬇ \n";
  xp_model ~html print m.output_model

(* pair reading and encoding *)
  
type ('value,'dconstr,'var,'func) pairs_reads =
  (* result of reading a list of pairs of grids *)
  { dl_mi : dl; (* input model DL *)
    dl_mo : dl; (* output model DL *)
    inputs_reads : (('value,'dconstr,'var,'func) read as 'read) list list; (* outer list over example inputs, inner list over parses *)
    reads : ('read * 'read * dl) list list; (* outer list over examples, inner list over parses, sorted in increasing DL *)
  }

let read_pairs
      ~(dl_task_model : (('t,'var,'constr,'func) task_model as 'task_model) -> dl * dl)
      ~(read : dl_assuming_contents_known:bool ->
               env:(('value,'dconstr) data as 'data) ->
               bindings:(('var,'value) Expr.bindings as 'bindings) ->
               (('t,'var,'constr,'func) model as 'model) -> 'value -> 'read list result)
      ~(get_bindings : 'model -> 'data -> 'bindings)
      
      ~(pruning : bool)
      ~(env : 'data)
      (m : 'task_model)
      (pairs : 'value Task.pair list)
    : ('value,'dconstr,'var,'func) pairs_reads result =
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
               ~env ~bindings:Expr.bindings0
               m.input_model input in (* no diff allowed during training *)
           let| pair_reads = 
             let+|+ ri = Result.Ok input_reads in
             let bindings = get_bindings m.input_model ri.data in
             let+|+ ro =
               read
                 ~dl_assuming_contents_known:false
                 ~env:ri.data ~bindings
                 m.output_model output in
             let dl = ri.dl +. ro.dl in
             Result.Ok [(ri,ro,dl)] in
           let pair_reads =
             pair_reads
             |> List.stable_sort (fun (_,_,dl1) (_,_,dl2) -> dl_compare dl1 dl2)
           (* TODO |> limit_dl (fun (_,_,dl) -> dl) *) in (* bounding by dl_factor *) 
           Result.Ok (input_reads, pair_reads)) in
  let inputs_reads, reads = List.split inputs_reads_reads in
  Result.Ok {dl_mi; dl_mo; inputs_reads; reads})

type ('value,'dconstr,'var,'func) reads =
  { dl_m : dl; (* DL of the model *)
    reads : ('value,'dconstr,'var,'func) read list list; (* outer list over docs, inner list over parses, sorted in increasing DL *)
  }
  
let split_pairs_read
      (prs : ('value,'dconstr,'var,'func) pairs_reads) : ('value,'dconstr,'var,'func) reads double =
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
      (psr : ('value,'dconstr,'var,'func) pairs_reads) : dl triple triple = (* QUICK *)
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
      () : ('value,'dconstr,'var,'func) pairs_reads -> dl triple triple =
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
      ~(read : dl_assuming_contents_known:bool ->
               env:(('value,'dconstr) data as 'data) ->
               bindings:(('var,'value) Expr.bindings as 'bindings) ->
               (('t,'var,'constr,'func) model as 'model) -> 'value ->
               ('value,'dconstr,'var,'func) read list result)
      ~(get_bindings : 'model -> 'data -> 'bindings)
      ~(write : bindings:'bindings ->
                'model -> 'info -> ('data * 'value) result)
      ~(env : 'data)
      (m : ('t,'var,'constr,'func) task_model) (v_i : 'value) (info_o : 'info)
    : ('data * 'data * 'value) list result =
  Common.prof "Task_model.apply" (fun () ->
  let+|+ read_i =
    read
      ~dl_assuming_contents_known:true ~env ~bindings:Expr.bindings0
      m.input_model v_i in
  let data_i = read_i.data in
  let bindings = get_bindings m.input_model data_i in
  let| data_o, v_o =
    write
      ~bindings
      m.output_model info_o in
  Result.Ok [(data_i, data_o, v_o)])

(* refinements *)
  
type ('t,'var,'constr,'func) refinement =
  | RInit
  | Rinput of 'constr path * ('t,'var,'constr,'func) model * int (* support *) * dl (* estimated result DL *)
  | Routput of 'constr path * ('t,'var,'constr,'func) model * int (* support *) * dl (* estimated result DL *)

let refinement_support : ('t,'var,'constr,'func) refinement -> int = function
  | RInit -> (-1)
  | Rinput (_,_,supp,_) -> supp
  | Routput (_,_,supp,_) -> supp             

let xp_refinement
      ~(xp_path : 'constr path html_xp)
      ~(xp_model : ('t,'var,'constr,'func) model html_xp)
    : ('t,'var,'constr,'func) refinement html_xp =
  let rec aux ~html print = function
    | RInit -> print#string "init"
    | Rinput (p,ri,supp,dl') -> aux2 ~html print " In" p ri supp dl' "i"
    | Routput (p,ro,supp,dl') -> aux2 ~html print " Out" p ro supp dl' "o"
  and aux2 ~html print in_out p r supp dl' i_o =
    (* if dl' <> 0. (* undefined value *) then (* showing DL estimate *)
      print#string (Printf.sprintf " (~%.3f) " dl'); *)
    xp_model ~html print r;
    if supp <> 0 (* undefined value *) then
      aux_support ~html print supp;
    print#string " → ";
    print#string in_out;
    xp_path ~html print p    
  and aux_support ~html print supp =
    print#string " ("; print#int supp; print#string ")"
  in
  aux

let refine (r : ('t,'var,'constr,'func) refinement) (m : ('t,'var,'constr,'func) task_model)
    : (('t,'var,'constr,'func) refinement * ('t,'var,'constr,'func) task_model) result =
  match r with
  | RInit -> Result.Error (Failure "Task_model.refine")
  | Rinput (p,ri,supp,dl') ->
     Result.Ok (r, {m with input_model = Model.refine p ri m.input_model})
  | Routput (p,ro,supp,dl') ->
     Result.Ok (r, {m with output_model = Model.refine p ro m.output_model})
