
open Madil_common

module type BASIC_TYPES =
  sig
    (* basic types and language definitions *)
    
    type typ
    val typ_bool : typ
    val xp_typ : typ html_xp

    type value
    val xp_value : value html_xp
    val value_of_json : Yojson.Safe.t -> value
    val json_of_value : value -> Yojson.Safe.t

    type distrib
    val xp_distrib : distrib html_xp
    
    type var
    val xp_var : var html_xp
    val var0 : var
    
    type constr
    val xp_any : typ -> unit html_xp
    val xp_pat : constr -> unit html_xp array -> unit html_xp array -> unit html_xp
    val xp_field : (constr * int) html_xp

    type func
    val xp_func : func html_xp

    val asd : (typ,typ) Model.asd

    type encoding
              
  end

module type TYPES =
  sig
    include BASIC_TYPES

    (* defined types *)

    type task_pair = value Task.pair
    type task = value Task.task
              
    type data = (value,distrib,constr) Data.data
    val xp_data : data html_xp
              
    type path = (var,constr) Model.path
    val xp_path : path html_xp

    type varseq = var Myseq.t
    type binding_vars = (var,typ) Expr.binding_vars
    type bindings = (var,typ,value) Expr.bindings
    val xp_bindings : bindings html_xp
          
    type expr = (typ,value,var,func) Expr.expr
    val xp_expr : expr html_xp

    type model = (typ,value,var,constr,func) Model.model
    val xp_model : model html_xp

    type asd = (typ,typ) Model.asd

    type task_model = (typ,value,var,constr,func) Task_model.task_model
    val xp_task_model : task_model html_xp

    type refinement = (typ,value,var,constr,func) Task_model.refinement
    val xp_refinement : refinement html_xp

    type read = (typ,value,distrib,constr,var,func) Model.read
    type reads = (typ,value,distrib,constr,var,func) Task_model.reads
    type pairs_reads = (typ,value,distrib,constr,var,func) Task_model.pairs_reads

    type generator = (distrib,var,typ,value,constr) Model.generator
    type parseur = (distrib,var,typ,value,constr) Model.parseur

    type expr_index = (typ,value,var,func) Expr.index
    val xp_expr_index : ?on_typ:(typ -> bool) -> expr_index html_xp

    type best_reads = (typ,value,distrib,constr,var,func) Refining.best_read list

    type status = (* reading status during learning *)
      [ `Success of (pairs_reads * reads * reads * Task_model.dl_split * dl)
      | `Failure
      | `Timeout
      | `Error of exn ]

    type init_config =
      { varseq : varseq;
        input_model : model;
        output_model : model;
        input_distrib : distrib;
        output_distrib : distrib }

  end

module Defined_types (T : BASIC_TYPES) =
  struct
    open T
       
    (* defined types *)

    type task_pair = value Task.pair
    type task = value Task.task
              
    type data = (value,distrib,constr) Data.data
    let xp_data : data html_xp = Data.xp_data ~xp_value ~xp_distrib ~xp_pat
                               
    type path = (var,constr) Model.path
    let xp_path : path html_xp = Model.xp_path ~xp_var ~xp_field

    type varseq = var Myseq.t
    type binding_vars = (var,typ) Expr.binding_vars
    type bindings = (var,typ,value) Expr.bindings
    let xp_bindings : bindings html_xp = Expr.xp_bindings ~xp_var ~xp_typ ~xp_value
          
    type expr = (typ,value,var,func) Expr.expr
    let xp_expr : expr html_xp = Expr.xp_expr ~xp_value ~xp_var ~xp_func

    type model = (typ,value,var,constr,func) Model.model
    let xp_model : model html_xp = Model.xp_model ~xp_value ~xp_var ~xp_any ~xp_pat ~xp_func

    type asd = (typ,typ) Model.asd

    type task_model = (typ,value,var,constr,func) Task_model.task_model
    let xp_task_model : task_model html_xp = Task_model.xp_task_model ~xp_model

    type refinement = (typ,value,var,constr,func) Task_model.refinement
    let xp_refinement : refinement html_xp = Task_model.xp_refinement ~xp_path ~xp_model

    type read = (typ,value,distrib,constr,var,func) Model.read
    type reads = (typ,value,distrib,constr,var,func) Task_model.reads
    type pairs_reads = (typ,value,distrib,constr,var,func) Task_model.pairs_reads
                     
    type generator = (distrib,var,typ,value,constr) Model.generator
    type parseur = (distrib,var,typ,value,constr) Model.parseur

    type expr_index = (typ,value,var,func) Expr.index
    let xp_expr_index : ?on_typ:(typ -> bool) -> expr_index html_xp =
      fun ?on_typ ~html print index ->
      index#xp ~xp_typ ~xp_value ~xp_var ~xp_func ~html print ()

    type best_reads = (typ,value,distrib,constr,var,func) Refining.best_read list

    class type cconstr = (* class definition of a constr *)
      object
        method xp_pat : unit html_xp array -> unit html_xp array -> unit html_xp
        method xp_field : int html_xp
        method generator_pat : typ -> value array -> generator array -> generator
        method parseur_pat : typ -> value array -> parseur array -> parseur
        method encoding_pat : value array -> encoding array -> encoding
        method dl_params : typ -> dl
        method refinements_pat : typ -> model array -> value -> model list
        method prunings_pat : typ -> model array -> value -> model list
      end

    class type cfunc = (* class definition of a func *)
      object
        method xp : unit html_xp
        method eval : value array -> value result
        method dl_params : typ -> dl
      end
    
    type status = (* reading status during learning *)
      [ `Success of (pairs_reads * reads * reads * Task_model.dl_split * dl)
      | `Failure
      | `Timeout
      | `Error of exn ]

    type init_config =
      { varseq : varseq;
        input_model : model;
        output_model : model;
        input_distrib : distrib;
        output_distrib : distrib }
                     
  end
  
module type DOMAIN =
  sig
    (* parameters *)

    val max_nb_parse : int ref
    val max_nb_reads : int ref
    val max_nb_writes : int ref
    val alpha : float ref
    val max_expr_size : int ref
    val max_expr_refinements_per_read : int ref
    val max_expr_refinements_per_var : int ref
    (* DEPR val max_refinement_steps : int ref *)
    val max_refinements : int ref
    val refinement_branching : int ref
    val input_branching : int ref
    val solution_pool : int ref
    val search_temperature : float ref

    include TYPES

    val bool_of_value : value -> bool result
    val value_of_bool : bool -> value
    
    (* bindings and evaluation *)

    val eval_func : func -> value array -> value result
    val eval_unbound_var : var -> value result
    val eval_arg : unit -> value result

    (* model-based generation and parsing *)

    val generator_value : value -> generator
    val generator_any : typ -> generator
    val generator_pat : typ -> constr -> value array -> generator array -> generator

    val parseur_value : value -> value -> bool
    val parseur_pat : typ -> constr -> value array -> parseur array -> parseur

    (* description lengths *)

    val encoding_dany : value -> distrib -> encoding
    val encoding_dpat : constr -> value array -> encoding array -> encoding
    val encoding_alt : dl (* choice *) -> encoding -> encoding
    val encoding_expr_value : value -> encoding
    val dl_of_encoding : encoding -> dl

    val dl_value : typ -> value -> dl
    val dl_var : nb_env_vars:int -> typ -> var -> dl
    val dl_constr_params : typ -> constr -> dl
    val dl_func_params : typ -> func -> dl
      
    (* expression index *)

    val make_index : bindings -> expr_index

    (* refining *)

    (* DEPR val decompositions : typ -> value list list -> model list *)

    val refinements_any : typ -> value -> model list
    val refinements_pat : typ -> constr -> model array -> value -> model list
    val refinements_pat_expr : env_vars:binding_vars -> typ -> value -> model list
    val refinements_postprocessing : typ -> model -> model -> supp:int -> nb:int -> alt:bool -> best_reads -> (model * best_reads) Myseq.t

    val prunings_value : typ -> value -> model list
    val prunings_any : typ -> value -> model list
    val prunings_pat : typ -> constr -> model array -> value -> model list
    val prunings_postprocessing : typ -> model -> model -> supp:int -> nb:int -> alt:bool -> best_reads -> (model * best_reads) Myseq.t

    (* learning *)
      
    val get_init_config : string (* task name *) -> task -> init_config
    val log_reading : refinement -> task_model -> status:status -> unit
    val log_refining : refinement -> task_model -> pairs_reads -> dl (* lmd *)  -> dl (* lrido *) -> dl (* lema *) -> unit

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
        ~typ_bool
  
    let get_bindings : model -> data -> bindings =
      Model.get_bindings
        ~typ_bool
        ~value_of_bool

    let eval_expr : expr -> bindings -> value result =
      Expr.eval
        ~eval_unbound_var
        ~eval_func
        ~eval_arg
      
    (* model-based generation and parsing *)
      
    let generator : model -> bindings -> generator =
      Model.generator
        ~eval_expr
        ~bool_of_value
        ~generator_value
        ~generator_any
        ~generator_pat

    let parseur : model -> bindings -> parseur =
      Model.parseur
        ~eval_expr
        ~bool_of_value
        ~parseur_value
        ~parseur_pat

    (* description lengths *)
      
    let dl_data : data -> dl =
      Model.dl_data
        ~encoding_dany
        ~encoding_dpat
        ~encoding_alt
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
          ~dl_value
          ~dl_constr_params
          ~dl_func_params in
      Model.dl
        ~size_model_ast
        ~nb_model_ast
        ~dl_model_params
        ~dl_var
        ~xp_model
        ~xp_typ,
      (fun () ->
        reset_nb_expr_ast ();
        reset_nb_model_ast ())

    (* reading and writing *)

    let parse_bests =
      Model.parse_bests
        ~max_nb_parse:(!max_nb_parse)
        ~parseur
        ~dl_data

    let does_parse_value =
      Model.does_parse_value
        ~parseur
    
    let read =
      Model.read
        ~parse_bests

    let write =
      Model.write
        ~generator
        ~dl_data

    (* refining *)

    let refinements =
      Refining.refinements
        ~pruning:false
        ~xp_value
        ~xp_model
        ~asd
        ~typ_bool
        ~value_of_bool
        ~var0
        ~dl_model
        ~dl_data
        ~parse_bests
        ~make_index
        (* DEPR ~decompositions *)
        ~refinements_value:(fun t v -> []) (* TODO: is a custom definition useful? *)
        ~refinements_any
        ~refinements_pat
        ~refinements_pat_expr
        ~postprocessing:refinements_postprocessing
        ~alpha:(!alpha)
        ~max_expr_refinements_per_read:(!max_expr_refinements_per_read)
        ~max_expr_refinements_per_var:(!max_expr_refinements_per_var)
        (* DEPR ~max_steps:(!max_refinement_steps) *)
        ~max_refinements:(!max_refinements)

    let prunings =
      Refining.refinements
        ~pruning:true
        ~xp_value
        ~xp_model
        ~asd
        ~typ_bool
        ~value_of_bool
        ~var0
        ~dl_model
        ~dl_data
        ~parse_bests
        ~make_index
        (* DEPR ~decompositions:(fun t value -> []) *)
        ~refinements_value:prunings_value
        ~refinements_any:prunings_any
        ~refinements_pat:prunings_pat
        ~refinements_pat_expr:(fun ~env_vars t value -> [])
        ~postprocessing:prunings_postprocessing
        ~alpha:(!alpha)
        ~max_expr_refinements_per_read:(!max_expr_refinements_per_read)
        ~max_expr_refinements_per_var:(!max_expr_refinements_per_var)
        (* DEPR ~max_steps:(!max_refinement_steps) *)
        ~max_refinements:(!max_refinements)

    (* task models *)

    let make_task_model =
      Task_model.make
        ~binding_vars

    let size_task_model (m : task_model) : int =
      Task_model.size_task_model_ast ~asd m
    
    let dl_task_model (m : task_model) : Task_model.dl_io =
      { i = dl_model ~nb_env_vars:0 m.input_model;
        o = dl_model ~nb_env_vars:m.nb_env_vars m.output_model }
    
    let dl_init =
      Task_model.dl_init
        ~alpha:(!alpha)
        ~encoding_dany
        ~dl_of_encoding
    
    let read_pairs =
      Task_model.read_pairs
        ~max_nb_reads:(!max_nb_reads)
        ~dl_task_model
        ~read
        ~get_bindings

    let apply =
      Task_model.apply
        ~max_nb_reads:(!max_nb_reads)
        ~max_nb_writes:(!max_nb_writes)
        ~read
        ~get_bindings
        ~write

    let task_refinements =
      Refining.task_refinements
        ~alpha:(!alpha)
        ~binding_vars
        ~input_refinements:refinements
        ~output_refinements:refinements

    let task_prunings =
      Refining.task_prunings
        ~alpha:(!alpha)
        ~binding_vars
        ~input_prunings:prunings
    
    let learn =
      Learning.learn
        ~alpha:(!alpha)
        ~read_pairs
        ~does_parse_value
        ~dl_init
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
