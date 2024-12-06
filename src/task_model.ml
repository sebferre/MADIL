
open Madil_common
open Data
open Model

(* task models *)
   
type ('typ,'value,'var,'constr,'func) task_model =
  { varseq : 'var Myseq.t; (* variable generator *)
    input_model : ('typ,'value,'var,'constr,'func) model; (* no reference *)
    env_vars : ('var,'typ) Expr.binding_vars; (* references in input model *)
    nb_env_vars : int; (* nb of visible vars in input model *)
    output_model : ('typ,'value,'var,'constr,'func) model;
  }

let make
      ~(binding_vars : ('typ,'value,'var,'constr,'func) model -> ('var,'typ) Expr.binding_vars)
      (varseq : 'var Myseq.t)
      (input_model : ('typ,'value,'var,'constr,'func) model)
      (output_model : ('typ,'value,'var,'constr,'func) model)
    : ('typ,'value,'var,'constr,'func) task_model =
  let env_vars = binding_vars input_model in
  let nb_env_vars = Mymap.cardinal env_vars in
  { varseq;
    input_model;
    env_vars;
    nb_env_vars;
    output_model }
                                                 
let xp_task_model
      ~(xp_model : ('typ,'value,'var,'constr,'func) model html_xp)
    :  ('typ,'value,'var,'constr,'func) task_model html_xp =
  fun ~html print m ->
  xp_model ~html print m.input_model;
  print#string "\n ⬇ \n";
  xp_model ~html print m.output_model

let size_task_model_ast
      ~(asd : ('typ,'asd_typ,'constr,'func) asd)
      (m : ('typ,'value,'var,'constr,'func) task_model) : int =
  Model.size_model_ast ~asd m.input_model
  + Model.size_model_ast ~asd m.output_model

(* pair reading and encoding *)
  
type ('typ,'value,'constr,'var,'func) pairs_reads =
  (* result of reading a list of pairs of grids *)
  { dl_mi : dl; (* input model DL *)
    dl_mo : dl; (* output model DL *)
    inputs_reads : (('typ,'value,'constr,'var,'func) read as 'read) list list; (* outer list over example inputs, inner list over parses *)
    reads : ('read * 'read * dl) list list; (* outer list over examples, inner list over parses, sorted in increasing DL *)
  }

let read_pairs
      ~(max_nb_reads : int)
      ~(dl_task_model : (('typ,'value,'var,'constr,'func) task_model as 'task_model) -> dl * dl)
      ~(read : bindings:(('var,'typ,'value) Expr.bindings as 'bindings) ->
               (('typ,'value,'var,'constr,'func) model as 'model) -> 'value -> 'read Myseq.t (*list result*))
      ~(get_bindings : 'model -> 'data -> 'bindings)
      
      (m : 'task_model)
      (pairs : 'value Task.pair list)
    : ('typ,'value,'constr,'var,'func) pairs_reads result =
  Common.prof "Task_model.read_pairs" (fun () ->
  let dl_mi, dl_mo = Common.prof "Task_model.read_pairs/dl_task_model" (fun () -> dl_task_model m) in
  let| inputs_reads_reads =
    pairs
    |> list_map_result
         (fun {Task.input; output} ->
           let _, input_reads, pair_reads =
             myseq_bind_sample_fair
               ~size1:max_nb_reads ~size2:max_nb_reads
               (read
                  ~bindings:Expr.bindings0
                  m.input_model input)
               (fun ri ->
                 let bindings = get_bindings m.input_model ri.data in
                 let* ro =
                   read
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

type ('typ,'value,'constr,'var,'func) reads =
  { dl_m : dl; (* DL of the model *)
    reads : ('typ,'value,'constr,'var,'func) read list list; (* outer list over docs, inner list over parses, sorted in increasing DL *)
  }
  
let split_pairs_read
      (prs : ('typ,'value,'constr,'var,'func) pairs_reads) : ('typ,'value,'constr,'var,'func) reads double =
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

type dl_io =
  { i : dl; (* input *)
    o : dl; (* output *)
    io : dl; (* input+output *)
  }
type dl_split =
  { m : dl_io; (* model *)
    r : dl_io; (* rank *)
    d : dl_io; (* data, including rank *)
    md : dl_io; (* model+data *)
    descr : dl; (* for description *)
    pred : dl; (* for prediction *)
  }

let dl_model_data
      ~(alpha : float)
      (psr : ('typ,'value,'constr,'var,'func) pairs_reads) : dl_split = (* QUICK *)
  let lmi = psr.dl_mi in
  let lmo = psr.dl_mo in
  let lri, lro, ldi, ldo =
    List.fold_left
      (fun (lri, lro, ldi,ldo) ->
        function
        | (ri,ro,dl)::_ -> (lri +. ri.dl_rank, lro +. ro.dl_rank,
                            ldi +. ri.dl, ldo +. ro.dl)
        | _ -> assert false)
      (0.,0.,0.,0.) psr.reads in
  let lri, lro = alpha *. lri, alpha *. lro in
  let ldi, ldo = alpha *. ldi, alpha *. ldo in
  let lmdi = lmi +. ldi in
  let lmdo = lmo +. ldo in
  { m = {i=lmi; o=lmo; io=lmi +. lmo};
    r = {i=lri; o=lro; io=lri +. lro};
    d = {i=ldi; o=ldo; io=ldi +. ldo};
    md = {i=lmdi; o=lmdo; io=lmdi +. lmdo};
    descr = lmdi +. lmdo;
    pred = lri +. lro +. ldo;
  }

let make_norm_dl_model_data
      ~(alpha : float)
      () : ('typ,'value,'constr,'var,'func) pairs_reads -> dl_split =
  let lmdi0 = ref (-1.) in
  let lmdo0 = ref (-1.) in
  fun psr ->
  let l = dl_model_data ~alpha psr in
  let () = (* setting initial DLs *)
    if !lmdi0 < 0.
    then ( lmdi0 := l.md.i; lmdo0 := l.md.o ) in
  let nlmi, nlri, nldi, nlmdi =
    l.m.i /. !lmdi0, l.r.i /. !lmdi0, l.d.i /. !lmdi0, l.md.i /. !lmdi0 in
  let nlmo, nlro, nldo, nlmdo = l.m.o /. !lmdo0, l.r.o /. !lmdo0, l.d.o /. !lmdo0, l.md.o /. !lmdo0 in
  { m = {i=nlmi; o=nlmo; io=nlmi +. nlmo};
    r = {i=nlri; o=nlro; io=nlri +. nlro};
    d = {i=nldi; o=nldo; io=nldi +. nldo};
    md = {i=nlmdi; o=nlmdo; io=nlmdi +. nlmdo};
    descr = nlmdi +. nlmdo;
    pred = nlri +. nlro +. nldo;
  }


(* applying a task model to an input *)

let apply
      ~(max_nb_reads : int)
      ~(max_nb_writes : int)
      ~(read : bindings:(('var,'typ,'value) Expr.bindings as 'bindings) ->
               (('typ,'value,'var,'constr,'func) model as 'model) -> 'value ->
               ('typ,'value,'constr,'var,'func) read Myseq.t)
      ~(get_bindings : 'model -> 'data -> 'bindings)
      ~(write : bindings:'bindings ->
                'model -> 'info -> ('data * dl) Myseq.t)

      (m : ('typ,'value,'var,'constr,'func) task_model) (v_i : 'value) (info_o : 'info)
    : ('data * 'data * dl) list result =
  Common.prof "Task_model.apply" (fun () ->
  let some_parse, _lri, l_di_do_dl =
    myseq_bind_sample_fair
      ~size1:max_nb_reads ~size2:max_nb_writes
      (read
         ~bindings:Expr.bindings0
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
    let _, rev_l_di_do_dl = (* removing duplicate generated values *)
      List.fold_left
        (fun (seen,res) (di,do_,dl as x) ->
          let vo = Data.value do_ in
          if List.mem vo seen
          then (seen, res)
          else (vo::seen, x::res))
        ([],[]) l_di_do_dl in
    Result.Ok (List.rev rev_l_di_do_dl))


(* refinements *)

type ('typ,'value,'var,'constr,'func) refinement =
  | RInit
  | RStep of [`Input|`Output] * ('var,'constr) path * ('typ,'value,'var,'constr,'func) model (* new submodel *) * int (* support *) * dl result (* estimated result DL or error *) * ('typ,'value,'var,'constr,'func) model (* new model *)

let refinement_support : ('typ,'value,'var,'constr,'func) refinement -> int = function
  | RInit -> (-1)
  | RStep (_,_,_,supp,_,_) -> supp

let xp_refinement
      ~(xp_path : ('var,'constr) path html_xp)
      ~(xp_model : ('typ,'value,'var,'constr,'func) model html_xp)
    : ('typ,'value,'var,'constr,'func) refinement html_xp =
  let rec aux ~html print = function
    | RInit -> print#string "init"
    | RStep (side,p,ri,supp,dl'_res,m') ->
       let in_out, i_o =
         match side with
         | `Input -> " In", "i"
         | `Output -> " Out", "o" in
       aux2 ~html print in_out p ri supp dl'_res i_o
  and aux2 ~html print in_out p r supp dl'_res i_o =
    (* (match dl'_res with
     | Result.Ok dl' when dl' <> 0. (* undefined value *) -> (* showing DL estimate *)
        print#string (Printf.sprintf " (~%.1f) " dl')
     | _ -> ()); *)
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
