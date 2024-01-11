
open Madil_common
open Ndtree.Operators

(* computing model refinements from parsing data *)

type ('typ,'value,'dconstr,'var,'func) read = ('typ,'value,'dconstr,'var,'func) Model.read * ('value,'dconstr) Data.data Ndtree.t
   
let map_reads (f : 'data -> 'data) (reads : ('read list * bool) list) : ('read list * bool) list  =
  List.map
    (fun (example_reads, unselected_reads) ->
      List.map
        (fun (read,data) ->
          let data' = Ndtree.map f data in
          (read, data'))
        example_reads,
      unselected_reads)
    reads

let filter_map_reads (f : 'data -> 'data option) (selected_reads : ('read list * bool) list) : ('read list * bool) list =
  (* returns: the result of applying [f] on [selected_reads] when [f] is defined *)
  List.filter_map
    (fun (example_reads, unselected_reads) ->
      let defined_example_reads, undefined_reads =
        List.partition_map
          (fun (read,data) ->
            let data' = Ndtree.map_filter f data in
            if Ndtree.for_all (fun d -> d = None) data' (* TODO: this is not so elegant *)
            then Either.Right () (* this case might be avoided *)
            else Either.Left (read, data'))
          example_reads in
      if defined_example_reads = []
      then None
      else Some (defined_example_reads, unselected_reads || undefined_reads <> []))
    selected_reads

let bind_reads (f : 'data -> 'data array) (reads : (('read * 'data Ndtree.t) list * bool) list) : (('read * 'data Ndtree.t) list * bool) list  =
  List.map
    (fun (example_reads, unselected_reads) ->
      List.map
        (fun (read,data) ->
          let data' =
            let<* d_opt = data in
            match d_opt with
            | None -> Ndtree.pack1 [|None|]
            | Some d -> Ndtree.pack1 (Array.map Option.some (f d)) in
          (read, data'))
        example_reads,
      unselected_reads)
    reads

let map_reads_ndtree (f_ndtree : 'data Ndtree.t -> 'data Ndtree.t) (reads : ('read list * bool) list) : ('read list * bool) list  =
  List.map
    (fun (example_reads, unselected_reads) ->
      List.map
        (fun (read,data) ->
          let data' = f_ndtree data in
          (read, data'))
        example_reads,
      unselected_reads)
    reads
  
type ('typ,'value,'dconstr,'var,'func) best_read = (* should be named best_read *)
  { unselected_reads : bool; (* flag for out-of-branch alt reads *)
    matching : bool; (* matching flag *)
    read : ('typ,'value,'dconstr,'var,'func) Model.read; (* the selected best read, first one when matching=false *)
    data : ('value,'dconstr) Data.data Ndtree.t;
    new_data : ('value,'dconstr) Data.data Ndtree.t } (* the new data, the old data when matching=false *)

let best_reads_stats (best_reads : ('typ,'value,'dconstr,'var,'func) best_read list) : int * int = (* support, total *)
  List.fold_left
    (fun (supp,nb) best_read ->
      if best_read.matching then supp+1, nb+1 (* positive *)
      else if best_read.unselected_reads then supp, nb (* out of scope *)
      else supp, nb+1) (* negative *)
    (0,0) best_reads

let inter_union_reads
      (get_rs : (('typ,'value,'dconstr,'var,'func) read as 'read) -> ('ref * 'var Myseq.t * 'data Ndtree.t) list)
      (reads : ('readdata list * bool) list)
    : ('ref, 'var Myseq.t * ('typ,'value,'dconstr,'var,'func) best_read list) Mymap.t =
  (* given a function extracting refinements (submodels) from each read,
     return a set of such refinements, each mapped to the dl-shortest reads supporting it, along with new data *)
  let process_example reads unselected_reads =
    assert (reads <> []);
    let read0, data0 = List.hd reads in
    let alt_read = {unselected_reads; matching = false; read = read0; data = data0; new_data = data0} in
    let refs =
      List.fold_left
        (fun refs (read,data) ->
          let refs_read = get_rs (read,data) in
          List.fold_left (* union(refs, refs_read) *)
            (fun refs (r,varseq',new_data) ->
              if Mymap.mem r refs
              then refs
              else Mymap.add r (varseq', {unselected_reads; matching = true; read; data; new_data}) refs)
            refs refs_read)
        Mymap.empty reads in
    alt_read, refs
  in
  match List.rev reads with (* rev to have best_reads in right order at the end *)
  | [] -> assert false
  | (example0_reads, example0_unselected_reads) :: other_reads ->
     let alt_read0, refs0 = process_example example0_reads example0_unselected_reads in
     let alt_reads = [alt_read0] in
     let refs = refs0 |> Mymap.map (fun (varseq', best_read) -> varseq', [best_read]) in
     let alt_reads, refs = (* TODO: is alt_read(s) necessary here? *)
       List.fold_left
         (fun (alt_reads,refs) (exampleI_reads, exampleI_unselected_reads) ->
           let alt_readI, refsI = process_example exampleI_reads exampleI_unselected_reads in
           let refs =
             Mymap.merge (* intersection(refs, refsI) *)
               (fun r varseq_best_reads_opt varseq_best_readI_opt ->
                 match varseq_best_reads_opt, varseq_best_readI_opt with
                 | Some (varseq, best_reads), Some (varseqI, best_readI) ->
                    Some (varseq, best_readI :: best_reads)
                 | Some (varseq, best_reads), None ->
                    Some (varseq, alt_readI :: best_reads)
                 | None, Some (varseqI, best_readI) ->
                    Some (varseqI, best_readI :: alt_reads)
                 | _ -> None)
               refs refsI in
           let alt_reads = alt_readI :: alt_reads in
           alt_reads, refs)
         (alt_reads, refs) other_reads in
     refs

let extend_partial_best_reads
      (selected_reads : ((('typ,'value,'dconstr,'var,'func) read as 'read) list * bool) list)
      (best_reads : (('typ,'value,'dconstr,'var,'func) best_read as 'best_read) list)
      (check_alt_read : 'read -> ('read * 'data Ndtree.t) option)
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
      (best_reads : (('typ,'value,'dconstr,'var,'func) best_read as 'best_read) list)
    : ('model * 'var Myseq.t * 'best_read list) Myseq.t =
  if supp = nb then (* no need for alternative *)
    Myseq.return (m_true, varseq, best_reads)
  else if allowed then
    (* making an alternative, model and data *)
    let xc, varseq' = new_var varseq in
    let prob = float supp /. float nb in
    let m' = Model.Alt (xc, Undet prob, m_true, m_false) in
    let best_reads' =
      List.map
        (fun {unselected_reads; matching; read; data; new_data} ->
          let prob = if matching then prob else 1. -. prob in
          let new_data =
            Ndtree.map
              (fun new_d ->
                Data.D (Data.value new_d, DAlt (prob, matching, new_d)))
              new_data in
          {unselected_reads; matching; read; data; new_data})
        best_reads in
    Myseq.return (m', varseq', best_reads')
  else (* alt not allowed *)
    Myseq.empty

let make_cons m1' m varseq1' =
  let x0, varseq' = new_var varseq1' in
  let x1, varseq' = new_var varseq' in
  let m' = Model.make_cons
             (Model.make_def x0 m1')
             (Model.make_def x1 m) in
  m', varseq'
       
type ('typ,'value,'dconstr,'var,'constr,'func) refiner =
  nb_env_vars:int ->
  env_vars:('var,'typ) Expr.binding_vars ->
  dl_M:dl -> (* current model DL *)
  (* NOTE: dl_M does not matter for ranking because an invariant of parsing and refinement *)
  (('typ,'value,'var,'constr,'func) Model.model as 'model) ->
  'var Myseq.t -> (* fresh variables viz the model *)
  ('typ,'value,'dconstr,'var,'func) Model.read list list
  -> (('var,'constr) Model.path (* refinement location *)
      * 'model (* refined submodel *)
      * int (* support *)
      * dl (* new DL *)
      * 'model (* new model, after applying refinement *)
      * 'var Myseq.t (* remaining fresh vars *)
     ) Myseq.t
  (* result: a sequence of path-wise refinements with support and estimate DL *)

let refinements
      ~(xp_model : 'model html_xp)
      ~(alpha : float)
      ~(max_refinements : int)
      ~(asd : ('typ,'constr,'func) Model.asd)
      ~(typ_bool : 'typ)
      ~(value_of_bool : bool -> 'value)
      ~(dl_model : nb_env_vars:int -> (('typ,'value,'var,'constr,'func) Model.model as 'model) -> dl)
      ~(dl_data : (('value,'dconstr) Data.data as 'data) -> dl)
      ~(eval : 'model -> ('var,'typ,'value) Expr.bindings -> 'model result)
      ~(input_of_value : 'typ -> 'value -> 'input)
      ~(parse_bests : 'model -> ?is:(int list) -> ('input,'value,'dconstr) Model.parse_bests)
      ~(make_index : ('var,'typ,'value) Expr.bindings -> ('typ,'value,'var,'func) Expr.Index.t)      
      ~(refinements_value : 'typ -> 'value -> 'varseq -> ('model * 'varseq) list)
      ~(refinements_pat : env_vars:('var,'typ) Expr.binding_vars -> 'typ -> 'constr -> 'model array -> ('var Myseq.t as 'varseq) -> 'data -> ('model * 'varseq) list) (* refined submodel with remaining fresh vars *)
      ~(postprocessing : 'typ -> 'constr -> 'model array -> 'model -> supp:int -> nb:int -> alt:bool -> 'best_read list
                         -> ('model * 'best_read list) Myseq.t) (* converting refined submodel, alt mode (true if partial match), support, and best reads to a new model and corresponding new data *)
    : ('typ,'value,'dconstr,'var,'constr,'func) refiner =

  let parse_best m is input =
    match parse_bests m ~is input with
    | Result.Ok ((d',dl')::_) -> Result.Ok d'
    | _ -> Result.Error Not_found
  in
  fun ~nb_env_vars ~env_vars ~dl_M m0 varseq0 reads ->
  let aux_gen (type r)
        ctx m selected_reads (* ctx is reverse path *)
        (read_refs : 'read * 'data Ndtree.t -> (r * 'varseq * 'data Ndtree.t) list)
        (postprocessing : r -> 'varseq -> supp:int -> nb:int -> alt:bool -> 'best_reads -> ('model * 'varseq * 'best_reads) Myseq.t)
      : ('path * 'model * 'varseq * int * dl) Myseq.t =
    let p = List.rev ctx in (* local path *)
    let dl_m = dl_model ~nb_env_vars m in
    let r_best_reads = inter_union_reads read_refs selected_reads in
    let* r, (varseq', best_reads) = Mymap.to_seq r_best_reads in
    let supp, nb = best_reads_stats best_reads in
    let alt = (supp < nb) in
    let* m_new, varseq', best_reads = postprocessing r varseq' ~supp ~nb ~alt best_reads in
    let dl_m_new = dl_model ~nb_env_vars m_new in
    let dl_new =
      dl_M -. dl_m +. dl_m_new
      +. alpha *. Mdl.sum best_reads
                    (fun {matching; read; data; new_data} ->
                      if matching
                      then
                        let dl_d =
                          Ndtree.fold
                            ~scalar:(function Some d -> dl_data d | None -> 0.)
                            ~vector:array_float_sum
                            data in
                        let dl_d_new =
                          Ndtree.fold
                            ~scalar:(function Some d -> dl_data d | None -> 0.)
                            ~vector:array_float_sum
                            new_data in
                        read.dl -. dl_d +. dl_d_new
                      else 0.) (* no change in this case *) in
    let dl_new = dl_round dl_new in (* rounding to absorb float error accumulation *)
    Myseq.return (p, m_new, varseq', supp, dl_new)
  in
  let rec aux ctx m selected_reads =
  if selected_reads = [] then Myseq.empty
  else
    match m with
    | Model.Def (x,m1) ->
       let ctx = [Model.Alias (x,ctx)] in
       aux ctx m1 selected_reads
    | Model.Pat (t,c,args) ->
       Myseq.interleave
         (aux_expr ctx m selected_reads
          :: aux_pat ctx m t c args selected_reads
          :: Array.to_list
              (Array.mapi
                 (fun i mi ->
                   let ctxi = Model.Field (c,i)::ctx in
                   aux ctxi mi
                     (map_reads
                        (function
                         | Data.D (_, DPat (dc, args)) ->
                            assert (i >= 0 && i < Array.length args);
                            args.(i)
                         | _ -> assert false)
                        selected_reads))
                 args))
    | Model.Fail -> assert false
    | Model.Alt (xc,c,m1,m2) ->
       Myseq.interleave
         [ aux_expr ctx m selected_reads;
           
           (match c with
            | Undet _ ->
               Myseq.concat
                 [ aux_alt_cond_undet ctx m xc c m1 m2 selected_reads;
                   aux_alt_prune ctx m m1 m2 selected_reads ]
            | True | False -> assert false
            | BoolExpr _ -> Myseq.empty);
           
           (let ctx1 = Model.Branch true :: ctx in
            let sel1 =
              filter_map_reads
                (function
                 | Data.D (_, DAlt (prob,b,d12)) ->
                    if b
                    then Some d12
                    else None
                 | _ -> assert false)
                selected_reads in
            aux ctx1 m1 sel1);
                        
           (let ctx2 = Model.Branch false :: ctx in
            let sel2 =
              filter_map_reads
                (function
                 | Data.D (_, DAlt (prob,b,d12)) ->
                    if not b
                    then Some d12
                    else None
                 | _ -> assert false)
                selected_reads in
            aux ctx2 m2 sel2) ]
    | Model.Loop (rlen,m1) -> (* TODO: add exprs *)
       aux ctx m1
         (bind_reads
            (function
             | Data.D (_, DSeq (_,_,ds1)) -> ds1
             | _ -> assert false)
            selected_reads)
    | Model.Nil t -> Myseq.empty
    | Model.Cons (m0,m1) ->
       Myseq.interleave
         [ aux_expr ctx m selected_reads;
           
           (let ctx0 = Model.Head :: ctx in
            let sel0 =
              map_reads_ndtree
                (fun data ->
                  match Ndtree.head_opt data with
                  | Some data0 -> data0
                  | None -> assert false)
                selected_reads in
            aux ctx0 m0 sel0);

           (let ctx1 = Model.Tail :: ctx in
            let sel1 =
              map_reads_ndtree
                (fun data ->
                  match Ndtree.tail_opt data with
                  | Some data1 -> data1
                  | None -> assert false)
                selected_reads in
            aux ctx1 m1 sel1);

           (* pruning Cons *)
           (if Model.is_index_invariant m1
            then
              let m1 = Model.undef m1 in
              aux_gen ctx m selected_reads
                (fun (read, data : _ read) ->
                  [m1, varseq0, data])
                (* not m0 because it raises ndim errors because scalar becomes vector *)
                (fun m' varseq' ~supp ~nb ~alt best_reads ->
                  Myseq.return (m', varseq', best_reads))
            else Myseq.empty) ]
    | Model.Expr (k, Expr.Const (t,v)) ->
       (* only for pruning, TODO optimize *)
       aux_gen ctx m selected_reads
         (fun (read, data : _ read) ->
           refinements_value t v varseq0
           |> List.map (fun (m',varseq') -> (m',varseq',data)))
         (fun m' varseq' ~supp ~nb ~alt best_reads ->
           Myseq.return (m', varseq', best_reads))
    | Model.Expr (k,e) -> Myseq.empty
    | Model.Value _ -> assert false
  and aux_expr ctx m selected_reads =
    let t = Model.typ m in
    match asd#expr_opt t with
    | false, [] -> Myseq.empty (* no expression here *)
    | const_ok, ts1 ->
       let allowed = asd#alt_opt t in
       let m_is_index_invariant = Model.is_index_invariant m in
       aux_gen ctx m selected_reads
         (fun (read, data : _ read) ->
           let rec aux refs depth ndim v_tree d_tree vd_trees =
             (* considering successively v_tree, v_tree[0], v_tree[0,0]... *)
             let s_expr = (* index expressions evaluating to v_tree *)
               let* t1 = Myseq.from_list ts1 in
               Expr.Exprset.to_seq
                 (Expr.Index.lookup (t1, v_tree)
                    (Model.force_index ~make_index read)) in
             let s_expr = (* is v_tree a constant ndtree? *)
               if const_ok then
                 match Ndtree.is_constant v_tree with
                 | Some vc -> Myseq.cons (Expr.Const (t,vc)) s_expr
                 | None -> s_expr
               else s_expr in
             let refs =
               Myseq.fold_left
                 (fun refs e ->
                   let rec aux_cons refs is_const me varseq d_tree' vd_trees =
                     (* adding Cons around e, and replacing head by d_tree', depth times *)
                     match vd_trees with
                     | [] -> (me,varseq,d_tree')::refs
                     | (v_tree1, d_tree1)::vd_trees1 ->
                        let is_const1 = is_const && Ndtree.is_constant v_tree1 <> None in
                        let me1, varseq1, d_tree1' =
                          if is_const1
                          then (* me explains all of v_tree *)
                            let d_tree1' = Ndtree.map Data.make_dexpr v_tree1 in
                            me, varseq, d_tree1'
                          else
                            let me1, varseq1 = make_cons me m varseq in
                            let d_tree1' = Ndtree.replace_head d_tree1 d_tree' in
                            me1, varseq1, d_tree1' in
                        aux_cons refs is_const1 me1 varseq1 d_tree1' vd_trees1
                   in
                   let is_const = (ndim = 0) in (* only applicable on scalar exprs *)
                   let me = Model.make_expr t e in
                   let d_tree' = (* values in v_tree/d_tree are explained by expr *)
                     Ndtree.map Data.make_dexpr v_tree in
                   aux_cons refs is_const me varseq0 d_tree' vd_trees)
                 refs s_expr in
             if ndim >= 1 && m_is_index_invariant (* not m_is_nil_or_cons *)
             then
               match Ndtree.head_opt v_tree, Ndtree.head_opt d_tree with
               | Some v_tree_0, Some d_tree_0 ->
                  aux refs (depth+1) (ndim-1) v_tree_0 d_tree_0 ((v_tree,d_tree)::vd_trees)
               | _ ->
                  (Model.make_nil t, varseq0, d_tree) :: refs (* empty ndtree *)
             else refs
           in
           let v_tree = Ndtree.map Data.value data in
           aux [] 0 (Ndtree.ndim v_tree) v_tree data [])
         (fun m_new varseq' ~supp ~nb ~alt best_reads ->
           make_alt_if_allowed_and_needed
             ~allowed ~supp ~nb
             m_new m varseq' best_reads)
  and aux_pat ctx m t c args selected_reads =
    let allowed = asd#alt_opt t in
    let ok_cons = Model.is_index_invariant m in
    aux_gen ctx m selected_reads
      (fun (read, data : _ read) ->
        let input_tree =
          Ndtree.map
            (fun d -> input_of_value t (Data.value d))
            data in
        match Ndtree.choose data with (* TODO: should be at index [0,...,0] *)
        | None -> []
        | Some d -> (* computing refinements on a sample data *)
           refinements_pat ~env_vars t c args varseq0 d
           |> List.fold_left
                (fun refs (m',varseq') ->
                  let ref_cons = (* considering the need to nest m' into Cons *)
                    let| m'_eval = eval m' read.bindings in
                    let rec aux_cons data input_tree = (* itering through heads of heads *)
                      let data'_res =
                        Ndtree.mapi_result
                          (fun is input -> parse_best m'_eval is input)
                          input_tree in
                      match data'_res with
                      | Result.Ok data' ->
                         Result.Ok (m',varseq',data') (* could add what follows as an alternative *)
                      | _ -> (* does not match full sequence, look at head *)
                         match ok_cons, Ndtree.head_opt data, Ndtree.head_opt input_tree with
                         | true, Some data1, Some input_tree1 ->
                            let| m1', varseq1', data1' = aux_cons data1 input_tree1 in
                            assert (Ndtree.ndim data1' = Ndtree.ndim data1);
                            let m', varseq' = make_cons m' m varseq' in
                            let data' = Ndtree.replace_head data data1' in
                            Result.Ok (m',varseq',data')
                         | _ -> Result.Error Not_found
                    in
                    aux_cons data input_tree in
                  match ref_cons with (* adding it to refs *)
                  | Result.Ok ref_cons -> ref_cons::refs
                  | Result.Error _ -> refs)
                [])
      (fun m' varseq' ~supp ~nb ~alt best_reads ->
        let* m_new, best_reads =
          postprocessing t c args m' ~supp ~nb ~alt best_reads in
        make_alt_if_allowed_and_needed
          ~allowed ~supp ~nb
          m_new m varseq' best_reads)
  and aux_alt_prune ctx m m1 m2 selected_reads =
    aux_gen ctx m selected_reads
      (fun (read, data : _ read) ->
        if Ndtree.for_all_defined
             (function
              | Data.D (_, DAlt (prob, b, d12)) -> b
              | _ -> assert false)
             data then
          let data1 =
            Ndtree.map_filter
              (function
               | Data.D (_, DAlt (prob, b, d12)) -> if b then Some d12 else None
               | _ -> assert false)
              data in
          [m1, varseq0, data1]
        else if Ndtree.for_all_defined
             (function
              | Data.D (_, DAlt (prob, b, d12)) -> not b
              | _ -> assert false)
             data then
          let data2 =
            Ndtree.map_filter
              (function
               | Data.D (_, DAlt (prob, b, d12)) -> if not b then Some d12 else None
               | _ -> assert false)
              data in
          [m2, varseq0, data2]
        else [])
(*        match read.data with
        | Data.D (_, DAlt (prob, b, d12)) ->
           if b
           then [m1, varseq0, d12]
           else [m2, varseq0, d12]
        | _ -> assert false) *)
      (fun m' varseq' ~supp ~nb ~alt best_reads ->
        if supp = nb
        then Myseq.return (m', varseq', best_reads)
        else Myseq.empty)
  and aux_alt_cond_undet ctx m xc c m1 m2 selected_reads =
    aux_gen ctx m selected_reads
      (fun (read, data : _ read) ->
        let vc_tree =
          Ndtree.map
          (function
           | Data.D (v, DAlt (_prob, b, d12)) -> value_of_bool b
           | _ -> assert false)
          data in
        let es : _ Expr.Exprset.t =
          Expr.Index.lookup (typ_bool, vc_tree)
            (Model.force_index ~make_index read) in
        let new_data = (* new data *)
          Ndtree.map
            (function
             | Data.D (v, DAlt (_prob, b, d12)) -> Data.D (v, DAlt (1.,b,d12))
             | _ -> assert false)
            data in
        Myseq.fold_left
          (fun rs e -> (e, varseq0, new_data) :: rs)
          [] (Expr.Exprset.to_seq es))
      (fun e varseq' ~supp ~nb ~alt best_reads ->
        if supp = nb
        then
          let c_new = Model.BoolExpr e in
          let m_new = Model.Alt (xc, c_new, m1, m2) in
          Myseq.return (m_new, varseq', best_reads)
        else Myseq.empty)
(* too clumsy - above code is more symmetrical wrt true/false but issue about missing false condition expressions
      (fun (read : _ Model.read) ->        
        match read.data with
        | Data.D (v, DAlt (_prob, true, d1)) ->
           let vc = value_of_bool true in
           let es : _ Expr.Exprset.t = Expr.Index.lookup (typ_bool, Ndtree.scalar vc) (Lazy.force read.lazy_index) in
           Myseq.fold_left
             (fun rs e -> (e, varseq0, Data.D (v, DAlt (1., true, d1))) :: rs)
             [] (Expr.Exprset.to_seq es)
        | Data.D (_, DAlt (_, false, _)) ->
           (* we only look for true expressions because the index does not contain all false expressions *)
           (* extend_partial_best_reads below compensates for that *)
           []
        | _ -> assert false)
      (fun e varseq' ~supp ~nb ~alt best_reads ->
        let best_reads =
          (*if supp <= 1
          then best_reads (* the condition should be valid for at least two examples *)
          else*) (* too strict, given low number of examples *)
            extend_partial_best_reads
              selected_reads best_reads
              (fun read ->
                match read.data with
                | D (v, DAlt (_prob, b, d1)) ->
                   let v_true = value_of_bool true in
                   if not b && not (Expr.Exprset.mem e (Expr.Index.lookup (typ_bool, Ndtree.scalar v_true) (Lazy.force read.lazy_index)))
                   then Some (read, D (v, DAlt (1., false, d1)))
                   else None
                | _ -> assert false) in
        let supp1, nb1 = best_reads_stats best_reads in
        if supp < nb (* discriminating cond *)
           && supp1 = nb1 (* valid cond for all examples *)
        then
          let c_new = Model.BoolExpr e in
          let m_new = Model.Alt (xc, c_new, m1, m2) in
          Myseq.return (m_new, varseq', best_reads)
        else Myseq.empty)
 *)
  in
  let selected_reads =
    (* the flag for each example indicates whether there are other reads, used with Alt *)
    List.map
      (fun example_reads ->
        let example_reads =
          List.map
            (fun (read : _ Model.read) ->
              (read, Ndtree.scalar (Some read.data)))
            example_reads in
        (example_reads, false))
      reads in
  let* p, r, varseq', supp, dl' =
    aux Model.ctx0 m0 selected_reads
    |> Myseq.sort (fun (p1,r1,vs1,supp1,dl1) (p2,r2,vs2,supp2,dl2) ->
           dl_compare dl1 dl2)
    |> Myseq.slice ~limit:max_refinements in
  let m' = Model.refine p r m0 in
  Myseq.return (p, r, supp, dl', m', varseq')

  
let task_refinements
      ~(binding_vars : ('typ,'value,'var,'constr,'func) Model.model -> ('var,'typ) Expr.binding_vars)
      ~(input_refinements : ('typ,'value,'dconstr,'var,'constr,'func) refiner)
      ~(output_refinements : ('typ,'value,'dconstr,'var,'constr,'func) refiner)
      
      (m : (('typ,'value,'var,'constr,'func) Task_model.task_model) as 'task_model)
      (prs : ('typ,'value,'dconstr,'var,'func) Task_model.pairs_reads)
      (dsri : ('typ,'value,'dconstr,'var,'func) Task_model.reads)
      (dsro : ('typ,'value,'dconstr,'var,'func) Task_model.reads)
    : (('typ,'value,'var,'constr,'func) Task_model.refinement * 'task_model) Myseq.t = (* QUICK Myseq.next *)
  Myseq.interleave (* TODO: rather order by estimated dl *)
    [ (let* p, ri, suppi, dli', mi, varseq =
         input_refinements ~nb_env_vars:0 ~env_vars:Expr.binding_vars0 ~dl_M:prs.dl_mi
           m.input_model m.varseq dsri.reads in
       let m' = Task_model.make ~binding_vars varseq mi m.output_model in 
       Myseq.return (Task_model.Rinput (p,ri,suppi,dli'), m'));

      (let* p, ro, suppo, dlo', mo, varseq =
         output_refinements ~nb_env_vars:m.nb_env_vars ~env_vars:m.env_vars ~dl_M:prs.dl_mo
           m.output_model m.varseq dsro.reads in
       let m' = Task_model.make ~binding_vars varseq m.input_model mo in
       Myseq.return (Task_model.Routput (p,ro,suppo,dlo'), m')) ]

let task_prunings
      ~(binding_vars : ('typ,'value,'var,'constr,'func) Model.model -> ('var,'typ) Expr.binding_vars)
      ~(input_prunings : ('typ,'value,'dconstr,'var,'constr,'func) refiner)
      
      (m : (('typ,'value,'var,'constr,'func) Task_model.task_model as 'task_model))
      (dsri : ('typ,'value,'dconstr,'var,'func) Task_model.reads)
    : (('typ,'value,'var,'constr,'func) Task_model.refinement * 'task_model) Myseq.t = (* QUICK Myseq.next *)
  let* pi, ri, suppi, dli', mi', varseq =
    input_prunings ~nb_env_vars:0 ~env_vars:Expr.binding_vars0 ~dl_M:dsri.dl_m
      m.input_model m.varseq dsri.reads in
  let m' = Task_model.make ~binding_vars varseq mi' m.output_model in
  Myseq.return (Task_model.Rinput (pi,ri,suppi,dli'), m')
