
open Madil_common

module type BASIC_TYPES =
  sig
    (* basic types and language definitions *)
    
    type value
    val xp_value : value html_xp
    val value_of_json : Yojson.Safe.t -> value

    type t
    val xp_type : t html_xp

    type dconstr
    val xp_dconstr : dconstr html_xp

    type constr
    val xp_constr : constr html_xp
    val xp_field : (constr * int) html_xp

    type func
    val xp_func : func html_xp

    val asd : (t,constr,func) Model.asd

    type generator_info
    type input
    type encoder_info
              
  end

module type TYPES =
  sig
    include BASIC_TYPES

    (* defined types *)

    type task_pair = value Task.pair
    type task = value Task.task
              
    type kind = t Kind.kind
    val xp_kind : kind html_xp

    type signature = t Kind.signature
    val xp_signature : signature html_xp
          
    type data = (value,dconstr) Data.data
    val xp_data : data html_xp
              
    type path = constr Path.path
    val xp_path : path html_xp

    type binding_paths = constr Path.binding_paths
    type bindings = (value,constr) Path.bindings
          
    type expr = (constr,func) Expr.expr
    val xp_expr : expr html_xp

    type model = (constr,func) Model.model
    val xp_model : model html_xp

    type asd = (t,constr,func) Model.asd

    type task_model = (t,constr,func) Task_model.task_model
    val xp_task_model : task_model html_xp

    type refinement = (constr,func) Task_model.refinement
    val xp_refinement : refinement html_xp

    type read = (value,dconstr,constr,func) Model.read
    type reads = (value,dconstr,constr,func) Task_model.reads
    type pairs_reads = (value,dconstr,constr,func) Task_model.pairs_reads

    type generator = (generator_info,value,dconstr) Model.generator
    type parseur = (input,value,dconstr) Model.parseur
    type encoder = (encoder_info,value,dconstr) Model.encoder

    type expr_index = (value,constr,func) Expr.Index.t

    type best_reads = (value,dconstr,constr,func) Refining.best_read list

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
              
    type kind = t Kind.kind
    let xp_kind : kind html_xp = Kind.xp_kind ~xp_type

    type signature = t Kind.signature
    let xp_signature : signature html_xp = Kind.xp_signature ~xp_type
          
    type data = (value,dconstr) Data.data
    let xp_data : data html_xp = Data.xp_data ~xp_value ~xp_dconstr
              
    type path = constr Path.path
    let xp_path : path html_xp = Path.xp_path ~xp_field

    type binding_paths = constr Path.binding_paths
    type bindings = (value,constr) Path.bindings
          
    type expr = (constr,func) Expr.expr
    let xp_expr : expr html_xp = Expr.xp_expr ~xp_field ~xp_func

    type model = (constr,func) Model.model
    let xp_model : model html_xp = Model.xp_model ~xp_constr ~xp_field ~xp_func

    type asd = (t,constr,func) Model.asd

    type task_model = (t,constr,func) Task_model.task_model
    let xp_task_model : task_model html_xp = Task_model.xp_task_model ~xp_model

    type refinement = (constr,func) Task_model.refinement
    let xp_refinement : refinement html_xp = Task_model.xp_refinement ~xp_path ~xp_model

    type read = (value,dconstr,constr,func) Model.read
    type reads = (value,dconstr,constr,func) Task_model.reads
    type pairs_reads = (value,dconstr,constr,func) Task_model.pairs_reads
                     
    type generator = (generator_info,value,dconstr) Model.generator
    type parseur = (input,value,dconstr) Model.parseur
    type encoder = (encoder_info,value,dconstr) Model.encoder

    type expr_index = (value,constr,func) Expr.Index.t

    type best_reads = (value,dconstr,constr,func) Refining.best_read list

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
    val max_parse_dl_factor : float ref
    val max_nb_reads : int ref
    val alpha : float ref
    val max_refinements : int ref

    include TYPES

    (* bindings and evaluation *)

    val visible_path : path -> kind -> bool
    val constr_value_opt : path -> kind -> value -> dconstr -> value option
    val seq_value_opt : path -> kind -> value list -> value option
      
    val eval_func : func -> value array -> value result
    val eval_unbound_path : path -> value result
    val eval_arg : unit -> value result
    val model_of_value : kind -> value -> model result

    (* model-based generation and parsing *)

    val generator_pat : constr -> generator array -> generator
    val value_of_data : data -> value

    val input_of_value : value -> input
    val parseur_pat : constr -> parseur array -> parseur

    (* description lengths *)
      
    val encoder_pat : constr -> encoder array -> encoder
    val info_expr : encoder_info -> data -> encoder_info
    val encoder_info_of_data : data -> encoder_info

    val dl_constr_params : constr -> dl
    val dl_func_params : func -> dl
    val dl_path : nb_env_paths:int -> path -> dl
      
    (* expression index *)

    val make_index : bindings -> expr_index

    (* refining *)

    val refinements_pat : constr -> model array -> data -> (model * input) list
    val refinements_postprocessing : constr -> model array -> model -> supp:int -> nb:int -> alt:bool -> best_reads -> (model * best_reads) Myseq.t

    val prunings_pat : constr -> model array -> data -> (model * input) list
    val prunings_postprocessing : constr -> model array -> model -> supp:int -> nb:int -> alt:bool -> best_reads -> (model * best_reads) Myseq.t

    (* learning *)

    val get_init_task_model : string (* task name *) -> task -> data (* env0 *) * task_model * generator_info
    val log_reading : refinement -> task_model -> status:status -> unit
    val log_refining : refinement -> task_model -> pairs_reads -> dl -> unit

    val default_name_task : string * task
      
  end

module Make (Domain : DOMAIN) =
  struct
    include Domain

    (* bindings and evaluation *)
                  
    let binding_paths : kind -> model -> binding_paths =
      Model.binding_paths
        ~asd
        ~visible_path
  
    let get_bindings : kind -> model -> data -> bindings =
      Model.get_bindings
        ~asd
        ~constr_value_opt
        ~seq_value_opt

    let eval : kind -> model -> bindings -> model result =
      Model.eval
        ~asd
        ~eval_func
        ~eval_unbound_path
        ~eval_arg
        ~model_of_value

    (* model-based generation and parsing *)
      
    let generator : model -> generator =
      Model.generator
        ~generator_pat

    let parseur : model -> parseur =
      Model.parseur
        ~parseur_pat

    (* description lengths *)
      
    let encoder : model -> encoder =
      Model.encoder
        ~encoder_pat
        ~info_expr

    let dl_data (m : model) : data -> dl =
      let enc = encoder m in
      fun d ->
      let info = encoder_info_of_data d in
      let dl, _ = enc info d in
      dl

    let dl_model : nb_env_paths:int -> kind -> model -> dl =
      Model.dl
        ~asd
        ~dl_constr_params
        ~dl_func_params
        ~dl_path

    (* reading and writing *)

    let eval_parse_bests =
      Model.eval_parse_bests
        ~max_nb_parse:(!max_nb_parse)
        ~eval
        ~parseur
        ~dl_data

    let read =
      Model.read
        ~max_parse_dl_factor:(!max_parse_dl_factor)
        ~max_nb_reads:(!max_nb_reads)
        ~input_of_value
        ~eval
        ~eval_parse_bests
        ~make_index

    let write =
      Model.write
        ~eval
        ~generator
        ~value_of_data

    (* refining *)

    let refinements =
      Refining.refinements
        ~asd
        ~dl_model
        ~dl_data
        ~eval_parse_bests
        ~refinements_pat
        ~postprocessing:refinements_postprocessing
        ~alpha:(!alpha)
        ~max_refinements:(!max_refinements)

    let prunings =
      Refining.refinements
        ~asd
        ~dl_model
        ~dl_data
        ~eval_parse_bests
        ~refinements_pat:prunings_pat
        ~postprocessing:prunings_postprocessing
        ~alpha:(!alpha)
        ~max_refinements:(!max_refinements)

    (* task models *)

    let dl_task_model (m : task_model) : dl * dl =
      dl_model ~nb_env_paths:0
        m.input_kind m.input_model,
      dl_model ~nb_env_paths:m.nb_env_paths
        m.output_kind m.output_model
    
    let read_pairs =
      Task_model.read_pairs
        ~dl_task_model
        ~read
        ~get_bindings

    let apply =
      Task_model.apply
        ~read
        ~get_bindings
        ~write

    let task_refinements =
      Refining.task_refinements
        ~binding_paths
        ~input_refinements:refinements
        ~output_refinements:refinements

    let task_prunings =
      Refining.task_prunings
        ~input_prunings:refinements
    
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

  end
