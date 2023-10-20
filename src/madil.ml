
open Madil_common

module type BASIC_TYPES =
  sig
    (* basic types and language definitions *)
    
    type value
    val xp_value : value html_xp
    val value_of_json : Yojson.Safe.t -> value

    type typ
    val typ_bool : typ
    val xp_typ : typ html_xp

    type dconstr
    val xp_dpat : dconstr -> unit html_xp array -> unit html_xp

    type var
    val xp_var : var html_xp

    type constr
    val xp_pat : constr -> unit html_xp array -> unit html_xp
    val xp_field : (constr * int) html_xp

    type func
    val xp_func : func html_xp

    val asd : (typ,constr,func) Model.asd

    type generator_info
    type input
    type encoding
              
  end

module type TYPES =
  sig
    include BASIC_TYPES

    (* defined types *)

    type task_pair = value Task.pair
    type task = value Task.task
              
    type data = (value,dconstr) Data.data
    val xp_data : data html_xp
              
    type path = constr Model.path
    val xp_path : path html_xp

    type varseq = var Myseq.t
    type binding_vars = var Expr.binding_vars
    type bindings = (var,typ,value) Expr.bindings
          
    type expr = (var,func) Expr.expr
    val xp_expr : expr html_xp

    type model = (typ,value,var,constr,func) Model.model
    val xp_model : model html_xp

    type asd = (typ,constr,func) Model.asd

    type task_model = (typ,value,var,constr,func) Task_model.task_model
    val xp_task_model : task_model html_xp

    type refinement = (typ,value,var,constr,func) Task_model.refinement
    val xp_refinement : refinement html_xp

    type read = (typ,value,dconstr,var,func) Model.read
    type reads = (typ,value,dconstr,var,func) Task_model.reads
    type pairs_reads = (typ,value,dconstr,var,func) Task_model.pairs_reads

    type generator = (generator_info,value,dconstr) Model.generator
    type parseur = (input,value,dconstr) Model.parseur

    type expr_index = (typ,value,var,func) Expr.Index.t

    type best_reads = (typ,value,dconstr,var,func) Refining.best_read list

    type status = (* reading status during learning *)
      [ `Success of (pairs_reads * reads * reads * dl triple triple * dl)
      | `Failure
      | `Timeout
      | `Error of exn ]

  end

module Defined_types (T : BASIC_TYPES) =
  struct
    open T
       
    (* defined types *)

    type task_pair = value Task.pair
    type task = value Task.task
              
    type data = (value,dconstr) Data.data
    let xp_data : data html_xp = Data.xp_data ~xp_value ~xp_dpat
                               
    type path = constr Model.path
    let xp_path : path html_xp = Model.xp_path ~xp_field

    type varseq = var Myseq.t
    type binding_vars = var Expr.binding_vars
    type bindings = (var,typ,value) Expr.bindings
          
    type expr = (var,func) Expr.expr
    let xp_expr : expr html_xp = Expr.xp_expr ~xp_var ~xp_func

    type model = (typ,value,var,constr,func) Model.model
    let xp_model : model html_xp = Model.xp_model ~xp_var ~xp_pat ~xp_func

    type asd = (typ,constr,func) Model.asd

    type task_model = (typ,value,var,constr,func) Task_model.task_model
    let xp_task_model : task_model html_xp = Task_model.xp_task_model ~xp_model

    type refinement = (typ,value,var,constr,func) Task_model.refinement
    let xp_refinement : refinement html_xp = Task_model.xp_refinement ~xp_path ~xp_model

    type read = (typ,value,dconstr,var,func) Model.read
    type reads = (typ,value,dconstr,var,func) Task_model.reads
    type pairs_reads = (typ,value,dconstr,var,func) Task_model.pairs_reads
                     
    type generator = (generator_info,value,dconstr) Model.generator
    type parseur = (input,value,dconstr) Model.parseur

    type expr_index = (typ,value,var,func) Expr.Index.t

    type best_reads = (typ,value,dconstr,var,func) Refining.best_read list

    type status = (* reading status during learning *)
      [ `Success of (pairs_reads * reads * reads * dl triple triple * dl)
      | `Failure
      | `Timeout
      | `Error of exn ]
                     
  end
  
module type DOMAIN =
  sig
    (* parameters *)

    val max_nb_parse : int ref
    val max_nb_reads : int ref
    val max_nb_writes : int ref
    val alpha : float ref
    val max_refinements : int ref

    include TYPES

    val bool_of_value : value -> bool result
    val value_of_bool : bool -> value
    val value_of_seq : value array -> value (* value for a data sequence *)      

    (* bindings and evaluation *)

    val eval_func : func -> value Ndtree.t array -> value Ndtree.t result
    val eval_unbound_var : var -> value Ndtree.t result
    val eval_arg : unit -> value Ndtree.t result

    (* model-based generation and parsing *)

    val generator_pat : typ -> constr -> generator array -> generator

    val input_of_value : value -> input
    val parseur_value : value -> parseur
    val parseur_pat : typ -> constr -> parseur array -> parseur

    (* description lengths *)
      
    val encoding_dpat : dconstr -> encoding array -> encoding
    val encoding_alt : dl (* choice *) -> encoding -> encoding
    val encoding_seq : dl (* seq len *) -> encoding array -> encoding
    val encoding_expr_value : value -> encoding
    val dl_of_encoding : encoding -> dl

    val dl_constr_params : typ -> constr -> dl
    val dl_func_params : func -> dl
    val dl_var : nb_env_vars:int -> var -> dl
      
    (* expression index *)

    val make_index : bindings -> expr_index

    (* refining *)

    val refinements_pat : typ -> constr -> model array -> varseq -> data Ndtree.t -> (model * varseq * input Ndtree.t) list
    val refinements_postprocessing : typ -> constr -> model array -> model -> supp:int -> nb:int -> alt:bool -> best_reads -> (model * best_reads) Myseq.t

    val prunings_pat : typ -> constr -> model array -> varseq -> data Ndtree.t -> (model * varseq * input Ndtree.t) list
    val prunings_postprocessing : typ -> constr -> model array -> model -> supp:int -> nb:int -> alt:bool -> best_reads -> (model * best_reads) Myseq.t

    (* learning *)

    val get_init_task_model : string (* task name *) -> task -> data (* env0 *) * task_model * generator_info
    val log_reading : refinement -> task_model -> status:status -> unit
    val log_refining : refinement -> task_model -> pairs_reads -> dl -> unit

    val default_name_task : string * task

    (* memoization *)
      
    val reset_memoization : unit -> unit

  end

module Make (Domain : DOMAIN) =
  struct
    include Domain

    (* bindings and evaluation *)
                  
    let binding_vars : model -> binding_vars =
      Model.binding_vars
  
    let get_bindings : model -> data -> bindings =
      Model.get_bindings
        ~typ_bool
        ~value_of_bool

    let eval_expr : expr -> bindings -> value Ndtree.t result =
      Expr.eval
        ~eval_unbound_var
        ~eval_func
        ~eval_arg
      
    let eval : model -> bindings -> model result =
      Model.eval
        ~asd
        ~eval_expr
        ~bool_of_value

    (* model-based generation and parsing *)
      
    let generator : model -> generator =
      Model.generator
        ~generator_pat
        ~value_of_seq

    let parseur : model -> parseur =
      Model.parseur
        ~parseur_value
        ~parseur_pat
        ~value_of_seq

    (* description lengths *)
      
    let dl_data : data -> dl =
      Model.dl_data
        ~encoding_dpat
        ~encoding_alt
        ~encoding_seq
        ~encoding_expr_value
        ~dl_of_encoding

    let (dl_model, reset_dl_model) : (nb_env_vars:int -> model -> dl) * (unit -> unit) =
      let nb_expr_ast, reset_nb_expr_ast =
        Expr.nb_expr_ast
          ~funcs:asd#funcs in
      let size_model_ast =
        Model.size_model_ast
          ~asd in
      let nb_model_ast, reset_nb_model_ast =
        Model.nb_model_ast
          ~typ_bool
          ~asd
          ~nb_expr_ast in
      let dl_model_params =
        Model.dl_model_params
          ~dl_constr_params
          ~dl_func_params in
      Model.dl
        ~size_model_ast
        ~nb_model_ast
        ~dl_model_params
        ~dl_var,
      (fun () ->
        reset_nb_expr_ast ();
        reset_nb_model_ast ())

    (* reading and writing *)

    let eval_parse_bests =
      Model.eval_parse_bests
        ~max_nb_parse:(!max_nb_parse)
        ~eval
        ~parseur
        ~dl_data

    let read =
      Model.read
        ~input_of_value
        ~eval
        ~eval_parse_bests

    let write =
      Model.write
        ~eval
        ~generator
        ~dl_data

    (* refining *)

    let refinements =
      Refining.refinements
        ~xp_model
        ~asd
        ~typ_bool
        ~value_of_bool
        ~dl_model
        ~dl_data
        ~eval_parse_bests
        ~refinements_pat
        ~postprocessing:refinements_postprocessing
        ~alpha:(!alpha)
        ~max_refinements:(!max_refinements)

    let prunings =
      Refining.refinements
        ~xp_model
        ~asd
        ~typ_bool
        ~value_of_bool
        ~dl_model
        ~dl_data
        ~eval_parse_bests
        ~refinements_pat:prunings_pat
        ~postprocessing:prunings_postprocessing
        ~alpha:(!alpha)
        ~max_refinements:(!max_refinements)

    (* task models *)

    let dl_task_model (m : task_model) : dl * dl =
      dl_model ~nb_env_vars:0
        m.input_model,
      dl_model ~nb_env_vars:m.nb_env_vars
        m.output_model
    
    let read_pairs =
      Task_model.read_pairs
        ~max_nb_reads:(!max_nb_reads)
        ~dl_task_model
        ~read
        ~get_bindings
        ~make_index

    let apply =
      Task_model.apply
        ~max_nb_reads:(!max_nb_reads)
        ~max_nb_writes:(!max_nb_writes)
        ~read
        ~get_bindings
        ~write

    let task_refinements =
      Refining.task_refinements
        ~binding_vars
        ~input_refinements:refinements
        ~output_refinements:refinements

    let task_prunings =
      Refining.task_prunings
        ~input_prunings:prunings
    
    let learn =
      Learning.learn
        ~alpha:(!alpha)
        ~read_pairs
        ~task_refinements
        ~task_prunings
        ~log_reading
        ~log_refining
      
    (* tasks *)

    let task_of_json : Yojson.Safe.t -> task =
      Task.task_of_json
        ~value_of_json

    let task_from_filename_contents : string -> string -> task =
      Task.from_filename_contents
        ~value_of_json

    let task_from_file : string -> task =
      Task.from_file
        ~value_of_json

    (* memory management *)
      
    let reset_memoization () =
      reset_dl_model ();
      reset_memoization ()

  end
