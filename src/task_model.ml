
open Madil_common
open Data
open Model

(* task models *)
   
type ('typ,'value,'var,'constr,'func) task_model =
  { varseq : 'var Myseq.t; (* variable generator *)
    input_model : ('typ,'value,'var,'constr,'func) model; (* no reference *)
    nb_env_vars : int; (* nb of visible vars in input model *)
    output_model : ('typ,'value,'var,'constr,'func) model;
  }

let make
      (varseq : 'var Myseq.t)
      (input_model : ('typ,'value,'var,'constr,'func) model)
      (output_model : ('typ,'value,'var,'constr,'func) model)
    : ('typ,'value,'var,'constr,'func) task_model =
  let env_vars = binding_vars input_model in
  let nb_env_vars = Bintree.cardinal env_vars in
  { varseq;
    input_model;
    nb_env_vars;
    output_model }
                                                 
let xp_task_model
      ~(xp_model : ('typ,'value,'var,'constr,'func) model html_xp)
    :  ('typ,'value,'var,'constr,'func) task_model html_xp =
  fun ~html print m ->
  xp_model ~html print m.input_model;
  print#string "\n ⬇ \n";
  xp_model ~html print m.output_model

(* pair reading and encoding *)
  
type ('typ,'value,'dconstr,'var,'func) pairs_reads =
  (* result of reading a list of pairs of grids *)
  { dl_mi : dl; (* input model DL *)
    dl_mo : dl; (* output model DL *)
    inputs_reads : (('typ,'value,'dconstr,'var,'func) read as 'read) list list; (* outer list over example inputs, inner list over parses *)
    reads : ('read * 'read * dl) list list; (* outer list over examples, inner list over parses, sorted in increasing DL *)
  }

let read_pairs
      ~(max_nb_reads : int)
      ~(dl_task_model : (('typ,'value,'var,'constr,'func) task_model as 'task_model) -> dl * dl)
      ~(read : dl_assuming_contents_known:bool ->
               env:(('value,'dconstr) data as 'data) ->
               bindings:(('var,'typ,'value) Expr.bindings as 'bindings) ->
               (('typ,'value,'var,'constr,'func) model as 'model) -> 'value -> 'read Myseq.t (*list result*))
      ~(get_bindings : 'model -> 'data -> 'bindings)
      
      ~(pruning : bool)
      ~(env : 'data)
      (m : 'task_model)
      (pairs : 'value Task.pair list)
    : ('typ,'value,'dconstr,'var,'func) pairs_reads result =
  Common.prof "Task_model.read_pairs" (fun () ->
  let dl_mi, dl_mo = dl_task_model m in
  let| inputs_reads_reads =
    pairs
    |> list_map_result
         (fun {Task.input; output} ->
           let _, input_reads, pair_reads =
             myseq_bind_sample_fair
               ~size1:max_nb_reads ~size2:max_nb_reads
               (read
                  ~dl_assuming_contents_known:pruning
                  ~env
                  ~bindings:Expr.bindings0
                  m.input_model input)
               (fun ri ->
                 let bindings = get_bindings m.input_model ri.data in
                 let* ro =
                   read
                     ~dl_assuming_contents_known:false
                     ~env:ri.data
                     ~bindings
                     m.output_model output in
                 Myseq.return (ri, ro, ri.dl +. ro.dl)) in
           if input_reads = [] (* implies pair_reads = [] *)
           then Result.Error Model.Parse_failure (* TODO: distinguish source *)
           else
             let pair_reads =
               List.stable_sort
                 (fun (_,_,dl1) (_,_,dl2) -> dl_compare dl1 dl2)
                 pair_reads in
             Result.Ok (input_reads, pair_reads)) in
  let inputs_reads, reads = List.split inputs_reads_reads in
  Result.Ok {dl_mi; dl_mo; inputs_reads; reads})

type ('typ,'value,'dconstr,'var,'func) reads =
  { dl_m : dl; (* DL of the model *)
    reads : ('typ,'value,'dconstr,'var,'func) read list list; (* outer list over docs, inner list over parses, sorted in increasing DL *)
  }
  
let split_pairs_read
      (prs : ('typ,'value,'dconstr,'var,'func) pairs_reads) : ('typ,'value,'dconstr,'var,'func) reads double =
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
      (psr : ('typ,'value,'dconstr,'var,'func) pairs_reads) : dl triple triple = (* QUICK *)
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
      () : ('typ,'value,'dconstr,'var,'func) pairs_reads -> dl triple triple =
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
      ~(max_nb_reads : int)
      ~(max_nb_writes : int)
      ~(read : dl_assuming_contents_known:bool ->
               env:(('value,'dconstr) data as 'data) ->
               bindings:(('var,'typ,'value) Expr.bindings as 'bindings) ->
               (('typ,'value,'var,'constr,'func) model as 'model) -> 'value ->
               ('typ,'value,'dconstr,'var,'func) read Myseq.t)
      ~(get_bindings : 'model -> 'data -> 'bindings)
      ~(write : bindings:'bindings ->
                'model -> 'info -> ('data * dl) Myseq.t)
      ~(env : 'data)
      (m : ('typ,'value,'var,'constr,'func) task_model) (v_i : 'value) (info_o : 'info)
    : ('data * 'data * dl) list result =
  Common.prof "Task_model.apply" (fun () ->
  let some_parse, _lri, l_di_do_dl =
    myseq_bind_sample_fair
      ~size1:max_nb_reads ~size2:max_nb_writes
      (read
         ~dl_assuming_contents_known:true
         ~env ~bindings:Expr.bindings0
         m.input_model v_i)
      (fun read_i ->
        let data_i = read_i.data in
        let bindings = get_bindings m.input_model data_i in
        let* data_o, dl_o = 
          write
            ~bindings
            m.output_model info_o in
        let dl = read_i.dl +. dl_o in
        Myseq.return (data_i, data_o, dl)) in
  if l_di_do_dl = []
  then Result.Error (if some_parse
                     then Model.Generate_failure
                     else Model.Parse_failure)
  else
    let l_di_do_dl =
      List.stable_sort
        (fun (_,_,dl1) (_,_,dl2) -> dl_compare dl1 dl2)
        l_di_do_dl in
    Result.Ok l_di_do_dl)


(* refinements *)
  
type ('typ,'value,'var,'constr,'func) refinement =
  | RInit
  | Rinput of ('var,'constr) path * ('typ,'value,'var,'constr,'func) model * int (* support *) * dl (* estimated result DL *)
  | Routput of ('var,'constr) path * ('typ,'value,'var,'constr,'func) model * int (* support *) * dl (* estimated result DL *)

let refinement_support : ('typ,'value,'var,'constr,'func) refinement -> int = function
  | RInit -> (-1)
  | Rinput (_,_,supp,_) -> supp
  | Routput (_,_,supp,_) -> supp             

let xp_refinement
      ~(xp_path : ('var,'constr) path html_xp)
      ~(xp_model : ('typ,'value,'var,'constr,'func) model html_xp)
    : ('typ,'value,'var,'constr,'func) refinement html_xp =
  let rec aux ~html print = function
    | RInit -> print#string "init"
    | Rinput (p,ri,supp,dl') -> aux2 ~html print " In" p ri supp dl' "i"
    | Routput (p,ro,supp,dl') -> aux2 ~html print " Out" p ro supp dl' "o"
  and aux2 ~html print in_out p r supp dl' i_o =
    (* if dl' <> 0. (* undefined value *) then (* showing DL estimate *)
      print#string (Printf.sprintf " (~%.3f) " dl'); *)
    if supp <> 0 (* undefined value *) then
      aux_support ~html print supp;
    print#string in_out;
    xp_path ~html print p;
    print#string " ← "; (* → *)
    xp_html_elt "span" ~classe:"model-refinement" ~html print
      (fun () -> xp_model ~html print r)
  and aux_support ~html print supp =
    print#string " #"; print#int supp; print#string " "
  in
  aux

let refine (r : ('typ,'value,'var,'constr,'func) refinement) (m : ('typ,'value,'var,'constr,'func) task_model)
    : (('typ,'value,'var,'constr,'func) refinement * ('typ,'value,'var,'constr,'func) task_model) result =
  match r with
  | RInit -> Result.Error (Failure "Task_model.refine")
  | Rinput (p,ri,supp,dl') ->
     let m' = make m.varseq (Model.refine p ri m.input_model) m.output_model in
     Result.Ok (r, m')
  | Routput (p,ro,supp,dl') ->
     let m' = make m.varseq m.input_model (Model.refine p ro m.output_model) in
     Result.Ok (r, m')
