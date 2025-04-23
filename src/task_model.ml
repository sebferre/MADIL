
open Madil_common
open Data
open Model

(* pair encoding *)

type dl_io =
  { i : dl; (* input *)
    o : dl; (* output *)
  }

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
      ~(asd : ('typ,'asd_typ) asd)
      (m : ('typ,'value,'var,'constr,'func) task_model) : int =
  Model.size_model_ast ~asd m.input_model
  + Model.size_model_ast ~asd m.output_model

(* pair reading and encoding *)
  
type ('typ,'value,'distrib,'constr,'var,'func) pairs_reads =
  (* result of reading a list of pairs of grids *)
  { dl0 : dl_io; (* initial DLs *)
    dl_m : dl_io; (* model DLs *)
    inputs_reads : (('typ,'value,'distrib,'constr,'var,'func) read as 'read) list list; (* outer list over example inputs, inner list over parses *)
    reads : ('read * 'read * dl) list list; (* outer list over examples, inner list over parses, sorted in increasing DL *)
  }

let read_pairs
      ~(max_nb_reads : int)
      ~(dl_task_model : (('typ,'value,'var,'constr,'func) task_model as 'task_model) -> dl_io)
      ~(read : bindings:(('var,'typ,'value) Expr.bindings as 'bindings) ->
               (('typ,'value,'var,'constr,'func) model as 'model) -> 'value -> 'distrib -> 'read Myseq.t (*list result*))
      ~(get_bindings : 'model -> 'data -> 'bindings)
      
      (m : 'task_model)
      (pairs : 'value Task.pair list)
      (distrib_i : 'distrib)
      (distrib_o : 'distrib)
      (dl0 : dl_io)
    : ('typ,'value,'distrib,'constr,'var,'func) pairs_reads result =
  Common.prof "Task_model.read_pairs" (fun () ->
  let dl_m = Common.prof "Task_model.read_pairs/dl_task_model" (fun () -> dl_task_model m) in
  let| inputs_reads_reads =
    pairs
    |> list_map_result
         (fun {Task.input; output} ->
           let _, input_reads, pair_reads =
             myseq_bind_sample_fair
               ~size1:max_nb_reads ~size2:max_nb_reads
               (read
                  ~bindings:Expr.bindings0
                  m.input_model input distrib_i)
               (fun ri ->
                 let bindings = get_bindings m.input_model ri.data in
                 let* ro =
                   read
                     ~bindings
                     m.output_model output distrib_o in
                 let ndl = ri.dl /. dl0.i +. ro.dl /. dl0.o in (* normalized DL *)
                 Myseq.return (ri, ro, ndl)) in
           if input_reads = [] (* implies pair_reads = [] *)
           then Result.Error Model.Parse_failure (* TODO: distinguish source *)
           else
             let pair_reads =
               List.stable_sort
                 (fun (_,_,ndl1) (_,_,ndl2) -> dl_compare ndl1 ndl2) (* on normalized DLs *)
                 pair_reads in
             Result.Ok (input_reads, pair_reads)) in
  let inputs_reads, reads = List.split inputs_reads_reads in
  Result.Ok {dl0; dl_m; inputs_reads; reads})

type ('typ,'value,'distrib,'constr,'var,'func) reads =
  { dl0 : dl; (* initial DL *)
    dl_m : dl; (* DL of the model *)
    reads : ('typ,'value,'distrib,'constr,'var,'func) read list list; (* outer list over docs, inner list over parses, sorted in increasing DL *)
  }
  
let split_pairs_read
      (prs : ('typ,'value,'distrib,'constr,'var,'func) pairs_reads) : ('typ,'value,'distrib,'constr,'var,'func) reads double =
  let project_reads proj =
    List.map
      (fun pair_reads ->
        pair_reads
        |> List.map proj)
      prs.reads in
  let inputs_reads = project_reads (fun (dri,_,_) -> dri) in
  let outputs_reads = project_reads (fun (_,dro,_) -> dro) in
  let dsri = { dl0 = prs.dl0.i; dl_m = prs.dl_m.i; reads = inputs_reads } in
  let dsro = { dl0 = prs.dl0.o; dl_m = prs.dl_m.o; reads = outputs_reads } in
  dsri, dsro

  
(* pair encoding *)

type dl_split =
  { m : dl_io; (* model *)
    r : dl_io; (* rank *)
    d : dl_io; (* data, including rank *)
    md : dl_io; (* model+data *)
    descr_refine : dl; (* for refining, normalized *)
    descr_prune : dl; (* for pruning, normalized *)
    pred : dl; (* for prediction, normalized *)
  }

(* make sure to normalize when adding input and output DLs *)

let dl_init (* initial input/output DLs, used for normalization *)
      ~(alpha : float)
      ~(encoding_dany : 'value -> 'distrib -> 'encoding)
      ~(dl_of_encoding : 'encoding -> dl)

      (pairs : 'value Task.pair list)
      (distrib_i : 'distrib)
      (distrib_o : 'distrib)
    : dl_io =
  let lm0 = Model.dl0 in
  (* rank 0 *)
  let sum_ldi, sum_ldo =
    List.fold_left
      (fun (sum_ldi, sum_ldo) {Task.input; output} ->
        let ldi = dl_of_encoding (encoding_dany input distrib_i) in
        let ldo = dl_of_encoding (encoding_dany output distrib_o) in
        sum_ldi +. ldi, sum_ldo +. ldo)
      (0., 0.) pairs in
  let i = lm0 +. alpha *. sum_ldi in
  let o = lm0 +. alpha *. sum_ldo in
  assert (i > 0. && o > 0.);
  {i; o}

let dl_model_data
      ~(alpha : float)
      (psr : ('typ,'value,'distrib,'constr,'var,'func) pairs_reads) : dl_split = (* QUICK *)
  let l0 = psr.dl0 in
  let lm = psr.dl_m in
  let lri, lro, ldi, ldo =
    List.fold_left
      (fun (lri, lro, ldi, ldo) ->
        function
        | (ri,ro,ndl)::_ -> (lri +. ri.dl_rank, lro +. ro.dl_rank,
                             ldi +. ri.dl, ldo +. ro.dl)
        | _ -> assert false)
      (0.,0.,0.,0.) psr.reads in
  let lri, lro = alpha *. lri, alpha *. lro in
  let ldi, ldo = alpha *. ldi, alpha *. ldo in
  let lmdi = lm.i +. ldi in
  let lmdo = lm.o +. ldo in
  { m = lm;
    r = {i=lri; o=lro};
    d = {i=ldi; o=ldo};
    md = {i=lmdi; o=lmdo};
    descr_refine = lmdi /. l0.i +. lmdo /. l0.o;
    descr_prune = (lm.i +. lri) /. l0.i +. lmdo /. l0.o;
    pred = lri /. l0.i +. ldo /. l0.o;
  }


(* applying a task model to an input *)

let apply
      ~(max_nb_reads : int)
      ~(max_nb_writes : int)
      ~(read : bindings:(('var,'typ,'value) Expr.bindings as 'bindings) ->
               (('typ,'value,'var,'constr,'func) model as 'model) -> 'value -> 'distrib ->
               ('typ,'value,'distrib,'constr,'var,'func) read Myseq.t)
      ~(get_bindings : 'model -> 'data -> 'bindings)
      ~(write : bindings:'bindings ->
                'model -> 'distrib -> ('data * dl) Myseq.t)

      (m : ('typ,'value,'var,'constr,'func) task_model)
      (v_i : 'value)
      (r_i : 'distrib)
      (r_o : 'distrib)
      (dl0 : dl_io)
    : ('data * 'data * dl) list result =
  Common.prof "Task_model.apply" (fun () ->
  let some_parse, _lri, l_di_do_ndl =
    myseq_bind_sample_fair
      ~size1:max_nb_reads ~size2:max_nb_writes
      (read
         ~bindings:Expr.bindings0
         m.input_model v_i r_i)
      (fun read_i ->
        let data_i = read_i.data in
        let bindings = get_bindings m.input_model data_i in
        let* data_o, dl_o = 
          write
            ~bindings
            m.output_model r_o in
        let ndl = read_i.dl /. dl0.i +. dl_o /. dl0.o in (* normalized DL *)
        Myseq.return (data_i, data_o, ndl)) in
  if l_di_do_ndl = []
  then Result.Error (if some_parse
                     then Model.Generate_failure
                     else Model.Parse_failure)
  else
    let l_di_do_ndl =
      List.stable_sort
        (fun (_,_,ndl1) (_,_,ndl2) -> dl_compare ndl1 ndl2)
        l_di_do_ndl in
    let _, rev_l_di_do_ndl = (* removing duplicate generated values *)
      List.fold_left
        (fun (seen,res) (di,do_,ndl as x) ->
          let vo = Data.value do_ in
          if List.mem vo seen
          then (seen, res)
          else (vo::seen, x::res))
        ([],[]) l_di_do_ndl in
    Result.Ok (List.rev rev_l_di_do_ndl))


(* refinements *)

type ('typ,'value,'var,'constr,'func) refinement =
  | RInit
  | RStep of [`Input|`Output|`Expr] * ('var,'constr) path * ('typ,'value,'var,'constr,'func) model (* new submodel *) * int (* support *)

let refinement_support : ('typ,'value,'var,'constr,'func) refinement -> int = function
  | RInit -> (-1)
  | RStep (_,_,_,supp) -> supp

let xp_refinement
      ~(xp_path : ('var,'constr) path html_xp)
      ~(xp_model : ('typ,'value,'var,'constr,'func) model html_xp)
    : ('typ,'value,'var,'constr,'func) refinement html_xp =
  let rec aux ~html print = function
    | RInit -> print#string "init"
    | RStep (side,p,ri,supp) ->
       let in_out, i_o =
         match side with
         | `Input -> " In", "i"
         | `Output -> " Out", "o"
         | `Expr -> " Expr", "e" in
       aux2 ~html print in_out p ri supp i_o
  and aux2 ~html print in_out p r supp i_o =
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
