
open Madil_common

let debug = ref false (* set to true to return all candidate refinements with causes for not being valid *)

exception No_local_parse
exception Failed_postprocessing
exception Alt_not_allowed
exception Alt_cannot_be_pruned
exception Cond_expr_not_valid

(* computing model refinements from parsing data *)

type ('typ,'value,'constr,'var,'func) read = ('typ,'value,'constr,'var,'func) Model.read * ('value,'constr) Data.data
   
let map_reads (f : 'read -> 'data -> 'data) (reads : ('readdata list * bool) list) : ('readdata list * bool) list  =
  List.map
    (fun (example_reads, unselected_reads) ->
      List.map
        (fun (read,data) ->
          let data' = f read data in
          (read, data'))
        example_reads,
      unselected_reads)
    reads
  
let filter_map_reads (f : 'read -> 'data -> 'data option) (selected_reads : ('readdata list * bool) list) : ('readdata list * bool) list =
  List.filter_map
    (fun (example_reads, unselected_reads) ->
      let defined_example_reads, undefined_reads =
        List.partition_map
          (fun (read,data) ->
            match f read data with
            | None -> Either.Right ()
            | Some data' -> Either.Left (read, data'))
          example_reads in
      if defined_example_reads = []
      then None
      else Some (defined_example_reads, unselected_reads || undefined_reads <> []))
    selected_reads

type ('typ,'value,'constr,'var,'func) best_read = (* should be named best_read *)
  { unselected_reads : bool; (* flag for out-of-branch alt reads *)
    matching : bool; (* matching flag *)
    read : ('typ,'value,'constr,'var,'func) Model.read; (* the selected best read, first one when matching=false *)
    data : ('value,'constr) Data.data;
    new_data : ('value,'constr) Data.data; (* the new data when matching=true, the old data when matching=false *)
  }

let best_reads_stats (best_reads : ('typ,'value,'constr,'var,'func) best_read list) : int * int = (* support, total *)
  List.fold_left
    (fun (supp,nb) best_read ->
      if best_read.matching then supp+1, nb+1 (* positive *)
      else if best_read.unselected_reads then supp, nb (* out of scope *)
      else supp, nb+1) (* negative *)
    (0,0) best_reads

let inter_union_reads
      (get_rs : (('typ,'value,'constr,'var,'func) read as 'read) -> ('ref * 'var Myseq.t * 'data result) list)
      (reads : ('readdata list * bool) list)
    : ('ref, 'var Myseq.t * ('typ,'value,'constr,'var,'func) best_read list result) Mymap.t =
  (* given a function extracting refinements (submodels) from each read,
     return a set of such refinements, each mapped to the dl-shortest reads supporting it, along with new data *)
  let process_example reads unselected_reads =
    Common.prof "Refining.inter_union_reads/process_example" (fun () ->
    assert (reads <> []);
    let read0, data0 = List.hd reads in
    let alt_read = {unselected_reads; matching = false; read = read0; data = data0; new_data = data0} in
    let refs =
      List.fold_left
        (fun refs (read,data) ->
          let refs_read =
            Common.prof "Refining.inter_union_reads/process_example/get_rs" (fun () ->
            get_rs (read,data)) in
          List.fold_left (* union(refs, refs_read) *)
            (fun refs (r,varseq',new_data_res) ->
              if Mymap.mem r refs
              then refs
              else
                let best_read =
                  let| new_data = new_data_res in
                  Result.Ok {unselected_reads; matching = true; read; data; new_data} in
                Mymap.add r (varseq', best_read) refs)
            refs refs_read)
        Mymap.empty reads in
    alt_read, refs)
  in
  Common.prof "Refining.inter_union_reads" (fun () ->
  match List.rev reads with (* rev to have best_reads in right order at the end *)
  | [] -> assert false
  | (example0_reads, example0_unselected_reads) :: other_reads ->
     let alt_read0, refs0 = process_example example0_reads example0_unselected_reads in
     let alt_reads = [alt_read0] in
     let refs =
       refs0
       |> Mymap.map
            (fun (varseq', best_read0) ->
              match best_read0 with
              | Result.Ok best_read0 -> varseq', [best_read0], []
              | Result.Error err -> varseq', [alt_read0], [err]) in
     let alt_reads, refs = (* TODO: is alt_read(s) necessary here? *)
       List.fold_left
         (fun (alt_reads,refs) (exampleI_reads, exampleI_unselected_reads) ->
           let alt_readI, refsI = process_example exampleI_reads exampleI_unselected_reads in
           let refs =
             Common.prof "Refining.inter_union_reads/merge" (fun () ->
             Mymap.merge (* intersection(refs, refsI) *)
               (fun r varseq_best_reads_opt varseq_best_readI_opt ->
                 match varseq_best_reads_opt, varseq_best_readI_opt with
                 | Some (varseq, best_reads, errs), Some (varseqI, best_readI) ->
                    (match best_readI with
                     | Result.Ok best_readI ->
                        Some (varseq, best_readI :: best_reads, errs)
                     | Result.Error errI ->
                        Some (varseq, alt_readI :: best_reads, errI :: errs))
                 | Some (varseq, best_reads, errs), None ->
                    Some (varseq, alt_readI :: best_reads, errs)
                 | None, Some (varseqI, best_readI) ->
                    (match best_readI with
                     | Result.Ok best_readI ->
                        Some (varseqI, best_readI :: alt_reads, [No_local_parse])
                     | Result.Error errI ->
                        Some (varseqI, alt_readI :: alt_reads, [errI; No_local_parse]))
                 | _ -> assert false (* None *))
               refs refsI) in
           let alt_reads = alt_readI :: alt_reads in
           alt_reads, refs)
         (alt_reads, refs) other_reads in
     Mymap.map
       (fun (varseq', best_reads, errs) ->
         if List.for_all (fun err -> err = No_local_parse) errs (* no error or only parse failures *)
         then (varseq', Result.Ok best_reads)
         else (varseq', Result.Error (List.hd errs))) (* unexpected error *)
       refs)

let extend_partial_best_reads
      (selected_reads : ((('typ,'value,'constr,'var,'func) read as 'read) list * bool) list)
      (best_reads : (('typ,'value,'constr,'var,'func) best_read as 'best_read) list)
      (check_alt_read : 'read -> ('read * 'data) option)
    : 'best_read list =
  List.map2
    (fun (reads, unselected_reads) best_read ->
      if best_read.matching
      then best_read (* already matches some refinement *)
      else
        (match List.find_map check_alt_read reads with
         | Some ((read,data), new_data) ->
            {unselected_reads = best_read.unselected_reads; matching = true;
             read; data; new_data} (* new match *)
         | None -> best_read)) (* no change *)
    selected_reads best_reads

let new_var (varseq : 'var Myseq.t) : 'var * 'var Myseq.t =
  match varseq () with
  | Myseq.Cons (x,varseq') -> x, varseq'
  | Myseq.Nil -> failwith "No more fresh variable (should be an infinite sequence"

let make_alt_if_allowed_and_needed
      ~(allowed : bool) ~(nb : int) ~(supp : int)
      (m_true : (('typ,'value,'var,'const,'func) Model.model as 'model))
      (m_false : 'model)
      (varseq : 'var Myseq.t)
      (best_reads : (('typ,'value,'constr,'var,'func) best_read as 'best_read) list)
    : ('model * 'var Myseq.t * 'best_read list result) Myseq.t =
  if supp = nb then (* no need for alternative *)
    Myseq.return (m_true, varseq, Result.Ok best_reads)
  else if allowed then
    (* making an alternative, model and data *)
    let xc, varseq' = new_var varseq in
    let prob = float supp /. float nb in
    let m' = Model.Alt (xc, Undet prob, m_true, m_false) in
    let best_reads' =
      List.map
        (fun {unselected_reads; matching; read; data; new_data} ->
          let prob = if matching then prob else 1. -. prob in
          let new_data = Data.DAlt (prob, matching, new_data) in
          {unselected_reads; matching; read; data; new_data})
        best_reads in
    Myseq.return (m', varseq', Result.Ok best_reads')
  else (* alt not allowed *)
    if !debug
    then Myseq.return (m_true, varseq, Result.Error Alt_not_allowed)
    else Myseq.empty

type ('typ,'value,'var,'constr,'func) refiner =
  nb_env_vars:int ->
  env_vars:('var,'typ) Expr.binding_vars ->
  dl_M:dl -> (* current model DL *)
  (* NOTE: dl_M does not matter for ranking because an invariant of parsing and refinement *)
  (('typ,'value,'var,'constr,'func) Model.model as 'model) ->
  'var Myseq.t -> (* fresh variables viz the model *)
  ('typ,'value,'constr,'var,'func) Model.read list list
  -> (('var,'constr) Model.path (* refinement location *)
      * 'model (* refined submodel *)
      * int (* support *)
      * dl result (* new DL or error *)
      * 'model (* new model, after applying refinement *)
      * 'var Myseq.t (* remaining fresh vars *)
     ) Myseq.t
  (* result: a sequence of path-wise refinements with support and estimate DL *)

let refinements
      ~(pruning : bool)
      ~(xp_value : 'value html_xp)
      ~(xp_model : 'model html_xp)
      ~(alpha : float)
      ~(max_expr_size : int)
      ~(max_expr_refinements_per_read : int)
      ~(max_expr_refinements_per_var : int)
      ~(max_refinements : int)
      ~(asd : ('typ,'constr,'func) Model.asd)
      ~(typ_bool : 'typ)
      ~(value_of_bool : bool -> 'value)
      ~(dl_model : nb_env_vars:int -> (('typ,'value,'var,'constr,'func) Model.model as 'model) -> dl)
      ~(dl_data : (('value,'constr) Data.data as 'data) -> dl)
      ~(input_of_value : 'typ -> 'value -> 'input)
      ~(parse_bests : 'model -> ('input,'var,'typ,'value,'constr) Model.parse_bests)
      ~(make_index : ('var,'typ,'value) Expr.bindings -> ('typ,'value,'var,'func) Expr.Index.t)      
      ~(decompositions : env_vars:('var,'typ) Expr.binding_vars -> 'typ -> 'varseq -> 'value list list -> ('model * 'varseq) list)
      ~(refinements_value : 'typ -> 'value -> 'varseq -> ('model * 'varseq) list)
      ~(refinements_any : env_vars:('var,'typ) Expr.binding_vars -> 'typ -> 'varseq -> 'value -> ('model * 'varseq) list)
      ~(refinements_pat : env_vars:('var,'typ) Expr.binding_vars -> 'typ -> 'constr -> 'model array -> ('var Myseq.t as 'varseq) -> 'value -> ('model * 'varseq) list) (* refined submodel with remaining fresh vars *)
      ~(postprocessing : 'typ -> 'model -> 'model -> supp:int -> nb:int -> alt:bool -> 'best_read list
                         -> ('model * 'best_read list) Myseq.t) (* converting refined submodel, alt mode (true if partial match), support, and best reads to a new model and corresponding new data *)
    : ('typ,'value,'var,'constr,'func) refiner =

  let parse_best m bindings input = Common.prof "Refining.refinements/parse_best" (fun () ->
    try
      match parse_bests m bindings input with
      | Result.Ok ((d',dl')::_) -> Result.Ok d'
      | _ -> Result.Error No_local_parse
    with exn ->
      if !debug
      then Result.Error exn (* to assign unexpected errors to individual refinements, for easier debugging *)
      else raise exn) (* otherwise, make those errors silent *)
  in
  fun ~nb_env_vars ~env_vars ~dl_M m0 varseq0 reads ->
  Myseq.prof "Refining.refinements" (
  let aux_dl_new dl_m m_new best_reads =
    let dl_m_new = dl_model ~nb_env_vars m_new in
    let dl_new =
      dl_M -. dl_m +. dl_m_new
      +. alpha *. Mdl.sum best_reads
                    (fun {matching; read; data; new_data} ->
                      if matching
                      then
                        let dl_d = dl_data data in
                        let dl_d_new = dl_data new_data in
                        read.dl -. dl_d +. dl_d_new
                      else read.dl) (* no change in this case *) in
    dl_round dl_new (* rounding to absorb float error accumulation *)
  in
  let aux_gen (type r)
        ctx m varseq selected_reads (* ctx is reverse path *)
        (read_refs : 'read * 'data -> (r * 'varseq * 'data result) list)
        (model_of_ref : r -> 'model)
        (postprocessing : 'model -> 'varseq -> supp:int -> nb:int -> alt:bool -> 'best_reads -> ('model * 'varseq * 'best_reads result) Myseq.t)
      : ('path * 'model * 'varseq * int * dl result) Myseq.t =
    Myseq.prof "Refining.refinements/aux_gen" (
    let p = List.rev ctx in (* local path *)
    let dl_m = dl_model ~nb_env_vars m in
    let selected_reads = (* local re-parsing of data from value for comparability with m' *)
      Common.prof "Refining.refinements/aux_gen/reparsing" (fun () ->
      map_reads
        (fun read data ->
          let v = Data.value data in
          let input = input_of_value (Model.typ m) v in
          match parse_best m read.Model.bindings input with
          | Result.Ok data -> data
          | _ -> (* should not happen *)
             print_endline "ERROR failed local parsing with current model";
             print_string "local model: "; pp_endline xp_model m;
             print_string "parsed value: "; pp_endline xp_value v;
             data)
        selected_reads) in
    let r_best_reads = inter_union_reads read_refs selected_reads in
    let* r, (varseq', best_reads_res) = Mymap.to_seq r_best_reads in
    let m_new = model_of_ref r in
    match best_reads_res with
    | Result.Error error ->
       if !debug
       then Myseq.return (p, m_new, varseq', 0, Result.Error error)
       else Myseq.empty
    | Result.Ok best_reads ->
       let supp, nb = best_reads_stats best_reads in
       if supp = 0 then (* only alt_reads, no parse at all *)
         if !debug
         then Myseq.return (p, m_new, varseq', supp, Result.Error No_local_parse)
         else Myseq.empty
       else
         let alt = (supp < nb) in
         let* m_new, varseq', best_reads_res =
           postprocessing m_new varseq' ~supp ~nb ~alt best_reads in
         match best_reads_res with
         | Result.Error error ->
            if !debug
            then Myseq.return (p, m_new, varseq', supp, Result.Error error)
            else Myseq.empty
         | Result.Ok best_reads ->
            let dl_new = aux_dl_new dl_m m_new best_reads in
            Myseq.return (p, m_new, varseq', supp, Result.Ok dl_new))
  in
  let rec aux ctx m varseq selected_reads =
  Myseq.prof "Refining.refinements/aux" (
  if selected_reads = [] then Myseq.empty
  else
    match m with
    | Model.Def (x,m1) ->
       let ctx = [Model.Alias (x,ctx)] in
       aux ctx m1 varseq selected_reads
    | Model.Any t ->
       Myseq.interleave
         [aux_expr ctx m varseq selected_reads;
          aux_any_pat ctx m varseq t (refinements_any ~env_vars t) selected_reads;
          aux_decomp ctx t m varseq selected_reads]
    | Model.Pat (t,c,args) ->
       Myseq.interleave
         (aux_expr ctx m varseq selected_reads
          :: aux_any_pat ctx m varseq t (refinements_pat ~env_vars t c args) selected_reads
          :: Array.to_list
              (Array.mapi
                 (fun i mi ->
                   let ctxi = Model.Field (c,i)::ctx in
                   aux ctxi mi varseq
                     (map_reads
                        (fun read -> function
                         | Data.DPat (_, dc, args) ->
                            assert (i >= 0 && i < Array.length args);
                            args.(i)
                         | _ -> assert false)
                        selected_reads))
                 args))
    | Model.Alt (xc,c,m1,m2) ->
       Myseq.interleave
         [ aux_expr ctx m varseq selected_reads;
           
           (match c with
            | Undet _ ->
               if pruning
               then aux_alt_prune ctx m m1 m2 varseq selected_reads
               else aux_alt_cond_undet ctx m xc c m1 m2 varseq selected_reads
            | BoolExpr _ -> Myseq.empty);
           
           (let ctx1 = Model.Branch true :: ctx in
            let sel1 =
              filter_map_reads
                (fun read -> function
                 | Data.DAlt (prob,b,d12) ->
                    if b
                    then Some d12
                    else None
                 | _ -> assert false)
                selected_reads in
            aux ctx1 m1 varseq sel1);
                        
           (let ctx2 = Model.Branch false :: ctx in
            let sel2 =
              filter_map_reads
                (fun read -> function
                 | Data.DAlt (prob,b,d12) ->
                    if not b
                    then Some d12
                    else None
                 | _ -> assert false)
                selected_reads in
            aux ctx2 m2 varseq sel2) ]
    | Model.Expr (k, Expr.Const (t,v)) ->
       if pruning (* pruning constants *)
       then
         aux_gen ctx m varseq selected_reads
           (fun (read, data : _ read) ->
             refinements_value t v varseq
             |> List.map (fun (m',varseq') -> (m',varseq', Result.Ok data)))
           (fun m' -> m')
           (fun m' varseq' ~supp ~nb ~alt best_reads ->
             Myseq.return (m', varseq', Result.Ok best_reads))
       else (*Myseq.empty*)
         (* generalizing constant into variable expression *)
         aux_expr ctx m varseq selected_reads
         |> Myseq.filter
              (fun (p,m',varseq',supp,dl') ->
                match m' with
                | Model.Expr (_, Expr.Const _) -> false
                | _ -> true)
    | Model.Expr (k,e) -> Myseq.empty
    | Model.Derived t -> Myseq.empty)
  and aux_decomp ctx t m varseq selected_reads =
    let p = List.rev ctx in
    let dl_m = dl_model ~nb_env_vars m in
    let nb = List.length selected_reads in
    let vss =
      List.map
        (fun (example,_) ->
          List.map
            (fun (read,data) ->
              Data.value data)
            example)
        selected_reads in
    let refs =
      decompositions ~env_vars t varseq vss
      |> List.fold_left
           (fun refs (m',varseq') ->
             let selected_reads' =
               filter_map_reads
                 (fun read data ->
                   let v = Data.value data in
                   let input = input_of_value t v in
                   (*let data_res = parse_best m read.Model.bindings input in*)
                   let data'_res = parse_best m' read.Model.bindings input in
                   (* (match data_res, data'_res with (* checking data DL invariance *)
                    | Result.Ok data, Result.Ok data' ->
                       let dl = dl_data data in
                       let dl' = dl_data data' in
                       if dl_round dl <> dl_round dl'
                       then Printf.printf "ERROR decomposition data DL: %.5f vs %.5f\n" dl dl' 
                       else print_endline "OK decomposition data DL"
                    | _ -> ()); *)
                   Result.to_option data'_res)
                 selected_reads in
             let supp = List.length selected_reads' in
             if supp = nb
             then (m',varseq', Result.Ok selected_reads')::refs
             else
               if !debug
               then (m',varseq', Result.Error No_local_parse)::refs
               else refs)
           [] in
    Myseq.interleave
      (List.map
         (fun (m', varseq', selected_reads'_res) ->
    match m', selected_reads'_res with
    | Model.Pat (_t, c, args), Result.Ok selected_reads' ->
       let dl_m' = dl_model ~nb_env_vars m' in
       let n = Array.length args in
       Myseq.interleave
         (Array.to_list
            (Array.mapi
               (fun i arg_i ->
                 let ctx_i = Model.Field (c,i)::ctx in
                 let ctx_i, m_i =
                   match arg_i with
                   | Model.Def (x,m_i) -> [Model.Alias (x,ctx_i)], m_i
                   | _ -> ctx_i, arg_i in
                 let selected_reads_i =
                   map_reads
                     (fun read -> function
                      | Data.DPat (_,_c,dargs) ->
                         assert (Array.length dargs = n);
                         dargs.(i)
                      | _ -> assert false)
                     selected_reads' in
                 let* p_i, m'_i, varseq', supp, dl'_i_res =
                   aux ctx_i m_i varseq' selected_reads_i in
                 let m'_i =
                   match arg_i with
                   | Model.Def (x,_) -> Model.Def (x,m'_i)
                   | _ -> m'_i in
                 let m' =
                   let args' = Array.copy args in
                   args'.(i) <- m'_i;
                   Model.make_pat t c args' in
                 let dl'_res = (* adding extra-cost of decomposition on model, assuming no cost on data *)
                   let| dl'_i = dl'_i_res in
                   Result.Ok (dl'_i -. dl_m +. dl_m') in
                 Myseq.return (p, m', varseq', supp, dl'_res)) (* pattern c(args) is assumed DL-invariant *)
               args))
    | _, Result.Error error ->
       if !debug
       then Myseq.return (p, m', varseq', 0, Result.Error error)
       else Myseq.empty
    | _ ->
       if !debug
       then Myseq.return (p, m', varseq', 0, Result.Error (Failure "decompositions must be patterns"))
       else Myseq.empty)
         refs)
  and aux_expr ctx m varseq selected_reads = (* QUICK *)
    if pruning then Myseq.empty
    else
    let t = Model.typ m in
    match asd#expr_opt t with
    | false, [] -> Myseq.empty (* no expression here *)
    | const_ok, ts1 ->
       let allowed = asd#alt_opt t in
       aux_gen ctx m varseq selected_reads
         (fun (read, data : _ read) -> Common.prof "Refining.refinements/aux_expr/get_rs" (fun () ->
           let v = Data.value data in
           let s_expr = (* index expressions evaluating to v *)
             Myseq.interleave
               (List.map
                  (fun t1 ->
                    Expr.Exprset.to_seq ~max_expr_size
                      (Expr.Index.lookup (t1, v)
                         (Model.force_index ~make_index read)))
                  ts1) in
           let s_expr = (* is v_tree a constant ndtree? *)
             if const_ok
             then Myseq.cons (Expr.Const (t,v)) s_expr
             else s_expr in
           s_expr
           |> Myseq.slice ~offset:0 ~limit:max_expr_refinements_per_read
           |> Myseq.fold_left
                (fun refs e ->
                  let me = Model.make_expr t e in
                  let data' = Data.make_dexpr v in
                  (me, varseq, Result.Ok data')::refs)
                []))
         (fun m' -> m')
         (fun m' varseq' ~supp ~nb ~alt best_reads ->
           Myseq.if_not_empty_else
             (let* m', best_reads = postprocessing t m m' ~supp ~nb ~alt best_reads in
              make_alt_if_allowed_and_needed
                ~allowed ~supp ~nb
                m' m varseq' best_reads)
             (if !debug
              then Myseq.return (m', varseq', Result.Error Failed_postprocessing)
              else Myseq.empty))
       |> Myseq.sort (fun (p1,r1,_,supp1,dl1_res) (p2,r2,_,supp2,dl2_res) ->
              let c = Stdlib.compare supp2 supp1 in (* higher support first *)
              if c = 0
              then
                match dl1_res, dl2_res with
                | Result.Ok dl1, Result.Ok dl2 ->
                   let c1 = dl_compare dl1 dl2 in
                   if c1 = 0
                   then Stdlib.compare (p1,r1) (p2,r2)
                   else c1
                | Result.Ok _, _ -> -1
                | _, Result.Ok _ -> 1
                | _ -> 0
              else c)
       |> Myseq.slice ~limit:max_expr_refinements_per_var
  and aux_any_pat ctx m varseq t get_refs selected_reads =
    let allowed = asd#alt_opt t in
    aux_gen ctx m varseq selected_reads
      (fun (read, data : _ read) -> Common.prof "Refining.refinements/aux_any/get_rs" (fun () ->
        let v = Data.value data in
        let input = input_of_value t v in
        get_refs varseq v
        |> List.fold_left
             (fun refs (m',varseq') ->
               let data'_res = parse_best m' read.bindings input in
               match data'_res with
               | Result.Ok data' ->
                  (m',varseq', data'_res)::refs (* could add what follows as an alternative *)
               | Result.Error error -> (* does not match new model *)
                  if !debug
                  then (m',varseq', data'_res)::refs
                  else refs)
             []))
      (fun m' -> m')
      (fun m' varseq' ~supp ~nb ~alt best_reads ->
        Myseq.if_not_empty_else
          (let* m', best_reads =
             postprocessing t m m' ~supp ~nb ~alt best_reads in
           make_alt_if_allowed_and_needed
             ~allowed ~supp ~nb
             m' m varseq' best_reads)
          (if !debug
           then Myseq.return (m', varseq', Result.Error Failed_postprocessing)
           else Myseq.empty))
  and aux_alt_prune ctx m m1 m2 varseq selected_reads =
    aux_gen ctx m varseq selected_reads
      (fun (read, data : _ read) ->
        match data with
        | Data.DAlt (prob, b, d12) ->
           if b
           then [m1, varseq, Result.Ok d12]
           else [m2, varseq, Result.Ok d12]
        | _ -> assert false)
      (fun m' -> m')
      (fun m' varseq' ~supp ~nb ~alt best_reads ->
        if supp = nb
        then Myseq.return (m', varseq', Result.Ok best_reads)
        else
          if !debug
          then Myseq.return (m', varseq', Result.Error Alt_cannot_be_pruned)
          else Myseq.empty)
  and aux_alt_cond_undet ctx m xc c m1 m2 varseq selected_reads =
    aux_gen ctx m varseq selected_reads
      (fun (read, data : _ read) ->
        match data with
        | Data.DAlt (_prob, b, d12) ->
           let vc = value_of_bool b in
           let es : _ Expr.Exprset.t =
             Expr.Index.lookup (typ_bool, vc)
               (Model.force_index ~make_index read) in
           let new_data = Data.DAlt (1.,b,d12) in
           Myseq.fold_left
             (fun rs e -> (e, varseq, Result.Ok new_data) :: rs)
             [] (Expr.Exprset.to_seq ~max_expr_size es)
        | _ -> assert false)
      (fun e ->
        let c_new = Model.BoolExpr e in
        Model.Alt (xc, c_new, m1, m2))
      (fun m' varseq' ~supp ~nb ~alt best_reads ->
        if supp = nb
        then Myseq.return (m', varseq', Result.Ok best_reads)
        else
          if !debug
          then Myseq.return (m', varseq', Result.Error Cond_expr_not_valid)
          else Myseq.empty)
  in
  let selected_reads =
    (* the flag for each example indicates whether there are other reads, used with Alt *)
    List.map
      (fun example_reads ->
        let example_reads =
          List.map
            (fun (read : _ Model.read) ->
              (read, read.data))
            example_reads in
        (example_reads, false))
      reads in
  let* p, r, varseq', supp, dl'_res =
    aux Model.ctx0 m0 varseq0 selected_reads
    |> Myseq.sort (fun (p1,r1,vs1,supp1,dl1_res) (p2,r2,vs2,supp2,dl2_res) ->
           match dl1_res, dl2_res with
           | Result.Ok dl1, Result.Ok dl2 ->
              let c1 = dl_compare dl1 dl2 in
              if c1 = 0
              then Stdlib.compare (p1,r1) (p2,r2)
              else c1
           | Result.Ok _, _ -> -1
           | _, Result.Ok _ -> 1
           | _ -> 0)
    |> Myseq.slice ~limit:max_refinements in
  let m' = Model.refine p r m0 in
  Myseq.return (p, r, supp, dl'_res, m', varseq'))


let task_refinements
      ~(binding_vars : ('typ,'value,'var,'constr,'func) Model.model -> ('var,'typ) Expr.binding_vars)
      ~(input_refinements : ('typ,'value,'var,'constr,'func) refiner)
      ~(output_refinements : ('typ,'value,'var,'constr,'func) refiner)
      
      (m : (('typ,'value,'var,'constr,'func) Task_model.task_model) as 'task_model)
      (prs : ('typ,'value,'constr,'var,'func) Task_model.pairs_reads)
      (dsri : ('typ,'value,'constr,'var,'func) Task_model.reads)
      (dsro : ('typ,'value,'constr,'var,'func) Task_model.reads)
    : (('typ,'value,'var,'constr,'func) Task_model.refinement * 'task_model result) Myseq.t = (* QUICK Myseq.next *)
  Myseq.interleave (* TODO: rather order by estimated dl *)
    [ (let* p, ri, suppi, dli'_res, mi', varseq =
         input_refinements ~nb_env_vars:0 ~env_vars:Expr.binding_vars0 ~dl_M:prs.dl_mi
           m.input_model m.varseq dsri.reads in
       let m'_res =
         let| _ = dli'_res in
         Result.Ok (Task_model.make ~binding_vars varseq mi' m.output_model) in 
       Myseq.return (Task_model.RStep (`Input,p,ri,suppi,dli'_res,mi'),m'_res));

      (let* p, ro, suppo, dlo'_res, mo', varseq =
         output_refinements ~nb_env_vars:m.nb_env_vars ~env_vars:m.env_vars ~dl_M:prs.dl_mo
           m.output_model m.varseq dsro.reads in
       let m'_res =
         let| _ = dlo'_res in
         Result.Ok (Task_model.make ~binding_vars varseq m.input_model mo') in
       Myseq.return (Task_model.RStep (`Output,p,ro,suppo,dlo'_res,mo'),m'_res)) ]

let task_prunings
      ~(binding_vars : ('typ,'value,'var,'constr,'func) Model.model -> ('var,'typ) Expr.binding_vars)
      ~(input_prunings : ('typ,'value,'var,'constr,'func) refiner)
      
      (m : (('typ,'value,'var,'constr,'func) Task_model.task_model as 'task_model))
      (dsri : ('typ,'value,'constr,'var,'func) Task_model.reads)
    : (('typ,'value,'var,'constr,'func) Task_model.refinement * 'task_model result) Myseq.t = (* QUICK Myseq.next *)
  let* pi, ri, suppi, dli'_res, mi', varseq =
    input_prunings ~nb_env_vars:0 ~env_vars:Expr.binding_vars0 ~dl_M:dsri.dl_m
      m.input_model m.varseq dsri.reads in
  let m'_res =
    let| _ = dli'_res in
    Result.Ok (Task_model.make ~binding_vars varseq mi' m.output_model) in
  Myseq.return (Task_model.RStep (`Input,pi,ri,suppi,dli'_res,mi'),m'_res)
