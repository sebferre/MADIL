
open Madil_common
open Js_of_ocaml

module Make (Domain : Madil.DOMAIN) =
  struct
    include Madil.Make(Domain)

let _ = Common.prof_on := false (* required because primitive unix_times not supported by js_of_ocaml *)

(* binding operator to force x's effects to take place before running f *)
(* typical case: x changes the DOM, f () is a long computation *)
let ( let> ) x f =
  ignore x;
  ignore
    (Dom_html.window##setTimeout
       (Js.wrap_callback f)
       0.)
  
(* ---- LIS -------- *)
        
type task_input = (string * task) Focus.input (* name, data *)

type learning_stage = Build | Prune
                
type arc_state =
  { name : string; (* task name *)
    task : task; (* task *)
    norm_dl_model_data : pairs_reads -> dl triple triple;
    stage : learning_stage;
    refinement : refinement; (* previous refinement *)
    refinement_support : int;
    env : data; (* nil env *)
    model : task_model; (* current model *)
    info_o : generator_info; (* for output generation *)
    prs : pairs_reads; (* pair reads *)
    dsri : reads; (* input reads *)
    dsro : reads; (* output reads *)
    dls : Mdl.bits triple triple; (* DL components *)
    norm_dls : Mdl.bits triple triple; (* normalized DL components *)
    norm_dl : Mdl.bits; (* global normalized DL *)
    mutable suggestions : arc_suggestion list;
  }
and arc_suggestion =
  | InputTask of task_input
  | ResetTask
  | ChangeStage of arc_state
  | RefinedState of arc_state * bool (* compressive *)

type arc_focus = arc_state
               
type arc_extent = arc_state

let rec state_of_model (name : string) (task : task) norm_dl_model_data (stage : learning_stage) (refinement : refinement) (env : data) (model : task_model) (info_o : generator_info) : (arc_state, exn) Result.t =
  let| prs = read_pairs ~pruning:(stage = Prune) ~env model task.train in
  let dsri, dsro = Task_model.split_pairs_read prs in
  let dls = Task_model.dl_model_data ~alpha:(!alpha) prs in
  let (_, _, (_,_,norm_dl) as norm_dls) = norm_dl_model_data prs in
  Result.Ok
    { name; task;
      norm_dl_model_data;
      stage;
      refinement;
      refinement_support = Task_model.refinement_support refinement;
      env; model; info_o;
      prs; dsri; dsro;
      dls;
      norm_dls;
      norm_dl;
      suggestions = [] }  
               
let initial_focus (name : string) (task : task) : arc_focus =
  let norm_dl_model_data = Task_model.make_norm_dl_model_data ~alpha:(!alpha) () in
  let env, init_model, info_o = get_init_task_model name task in
  match state_of_model name task norm_dl_model_data Build Task_model.RInit env init_model info_o with
  | Result.Ok s -> s
  | Result.Error exn -> raise exn

        
class arc_place (lis : arc_lis) (focus : arc_focus) =
object
  inherit [arc_lis,arc_focus,arc_extent,arc_suggestion] Lis.place lis focus

  method eval k_extent k_suggestions =
    k_extent focus;
    if focus.suggestions = [] then (
      Jsutils.firebug "Computing suggestions...";
      let _, suggestions = (* selecting up to [refine_degree] compressive refinements, keeping other for information *)
        (match focus.stage with
         | Build -> task_refinements focus.model focus.prs focus.dsri focus.dsro
         | Prune -> task_prunings focus.model focus.dsri)
        |> Myseq.fold_left
             (fun (quota_compressive,suggestions as res) (r,m) ->
               if quota_compressive <= 0
               then res (* TODO: stop generating sequence *)
               else
                 match state_of_model focus.name focus.task focus.norm_dl_model_data focus.stage r focus.env m focus.info_o with
                 | Result.Ok state ->
                    if state.norm_dl < focus.norm_dl
                    then (quota_compressive - 1, state::suggestions)
                    else (quota_compressive, state::suggestions)
                 | Result.Error _ -> res)
             (!max_refinements, []) in
      let suggestions =
        suggestions
        |> List.rev (* to preserve ordering from sequence *) 
        |> List.sort (* sorting by decreasing support, then increasing DL *)
             (fun s1 s2 -> Stdlib.compare
                             ((*s2.refinement_support,*) s1.norm_dl)
                             ((*s1.refinement_support,*) s2.norm_dl)) in
      let suggestions =
        InputTask (new Focus.input default_name_task)
        :: ResetTask
        :: List.map (fun s ->
               let compressive = s.norm_dl < focus.norm_dl in
               RefinedState ((s :> arc_state), compressive))
             suggestions
        @ (let new_stage =
             match focus.stage with
             | Build -> Prune
             | Prune -> Build in
           match state_of_model focus.name focus.task focus.norm_dl_model_data
                   new_stage Task_model.RInit focus.env focus.model focus.info_o with
           | Result.Ok s -> [ChangeStage s]
           | Result.Error exn -> print_endline (Printexc.to_string exn); []) in
      Jsutils.firebug "Suggestions computed";
      focus.suggestions <- suggestions
    );
    let suggestions = (* suggestion list in Fablis format *)
      focus.suggestions
      |> List.map (fun sugg -> `Sugg sugg) in
    k_suggestions [suggestions]

  method activate = function
    | InputTask i ->
       let name, task = i#get in
       let state = initial_focus name task in
       Some (new arc_place lis state)
    | ResetTask ->
       Some (new arc_place lis (initial_focus focus.name focus.task))
    | ChangeStage s ->
       Some (new arc_place lis s)
    | RefinedState (s,_) ->
       Some (new arc_place lis s)

  method abort = ()

  method json = raise TODO

  method results = raise TODO
end

and arc_lis =
object (self)
  inherit [arc_place] Lis.lis

  method initial_place =
    let name0, task0 = default_name_task in
    let state0 = initial_focus name0 task0 in
    new arc_place (self :> arc_lis) state0

  method place_of_json json = raise TODO
end

let make_lis (args : (string * string) list) =
  new arc_lis

(* ------- WEBAPP --------- *)
  
type arc_word

type arc_input = [`Task of task_input]

let html = true (* for xprinters *)
               
let html_dl dl =
  Printf.sprintf "%.3f" dl
   
let xml_of_focus focus =
  let (mi,mo,m), (di,do_,d), (mdi,mdo,md) = focus.dls in
  [Syntax.Block
     [[Syntax.Kwd (Printf.sprintf "Task %s [%s]"
                     focus.name
                     (match focus.stage with
                      | Build -> "building stage"
                      | Prune -> "pruning stage"))];
      [Syntax.Kwd (Printf.sprintf "DL = %f" focus.norm_dl)];
      [Syntax.Kwd (Printf.sprintf "DL = %.3f = %.3fm + %.3fd = (%.3fmi + %.3fmo) + (%.3fdi + %.3fdo) = %.3fi + %.3fo" md m d mi mo di do_ mdi mdo)];
      [Syntax.Kwd (Xprint.to_string (xp_model ~html) (*~ctx:ctx0*) focus.model.input_model)];
      [Syntax.Kwd " ➜ "];
      [Syntax.Kwd (Xprint.to_string (xp_model ~html) (*~ctx:ctx0*) focus.model.output_model)]]]
  
let html_of_word (w : arc_word) : Html.t = assert false

let html_info_of_input (input : arc_input) : Html.input_info =
  match input with
  | `Task input ->
     Html.fileElt_info
       (Some ".json, .csv")
       (fun (fname,contents) k ->
         let task_name = Filename.chop_extension (Filename.basename fname) in
         let task = task_from_filename_contents fname contents in
         input#set (task_name, task);
         k ())
                                         
let html_of_suggestion ~input_dico = function
  | InputTask i ->
     let info = html_info_of_input (`Task i) in
     let key = input_dico#add info in
     Html.html_of_input_info key info ^ " a task"
  | ResetTask ->
     "reset current task"
  | ChangeStage s ->
     Jsutils.escapeHTML
       (Printf.sprintf "(%f) switch to %s stage " s.norm_dl
          (match s.stage with Build -> "building" | Prune -> "pruning"))
  | RefinedState (s,compressive) ->
     Html.span ~classe:(if compressive then "compressive" else "non-compressive")
       (Printf.sprintf "(%f)  " s.norm_dl
        ^ Xprint.to_string (xp_refinement ~html) s.refinement)

let html_of_value v =
  Xprint.to_string (xp_value ~html) v
    
let html_of_row_from_data data =
  Xprint.to_string (xp_data ~html) data

let html_row_pair html_i html_o =
  html_i ^ "<br/> ➜ <br/>" ^ html_o
    
type col = ColExample | ColDescr | ColPred
type cell =
  | Example of value * value
  | Descr of read * read
  | Pred of value * (data * data * value) list (* expected value, all preds (input data, output data, output value) *)
  | Error of string
                                    
let html_of_cell : cell -> Html.t = function
  | Example (vi,vo) ->
     html_row_pair
       (html_of_value vi)
       (html_of_value vo)
  | Descr (ri,ro) ->
     html_row_pair
       (html_of_row_from_data ri.data)
       (html_of_row_from_data ro.data)
     ^ Printf.sprintf "<br/>DL = %.3f = %.3fi + %.3fo" (ri.dl +. ro.dl) ri.dl ro.dl
  | Pred (expected_vo, l_di_do_vo) ->
     String.concat (if html then "<br/>" else "\n")
       (List.map
          (fun (di,_do,vo) ->
            html_row_pair
              (html_of_row_from_data di)
              (html_of_value vo))
          l_di_do_vo)
  | Error msg -> Jsutils.escapeHTML msg
        
let w_focus : (arc_word, unit, arc_focus) Widget_focus.widget =
  new Widget_focus.widget
    ~id:"lis-focus"
    ~html_of_word

let w_suggestions : arc_suggestion Widget_suggestions.widget =
  new Widget_suggestions.widget
    ~id:"lis-suggestions"
    ~html_of_suggestion

let cols = [ColExample, (); ColDescr, (); ColPred, ()]
let w_results : (col, unit, cell) Widget_table.widget =
  new Widget_table.widget
    ~id:"lis-results"
    ~html_of_column:(fun (col,()) ->
      let html =
        match col with
        | ColExample -> "Example"
        | ColDescr -> "Description"
        | ColPred -> "Prediction" in
      None, None, None, html)
    ~html_of_cell


let render_place place k =
  let get_pred ~test m vi vo =
    let focus = place#focus in
    match apply ~env:focus.env m vi focus.info_o with
    | Result.Ok [] -> Error "No valid prediction"
    | Result.Ok l_di_do_vopred -> Pred (vo, if test then l_di_do_vopred else [List.hd l_di_do_vopred])
    | Result.Error exn -> Error (Printexc.to_string exn)
  in
 Jsutils.jquery "#lis-suggestions" (fun elt_lis ->
  let> _ = Jsutils.toggle_class elt_lis "computing" in (* turn on *)
  let xml = xml_of_focus place#focus in
  w_focus#set_syntax xml;
  place#eval
    (fun ext ->
      let l_bindings =
        List.map
          (fun pair ->
            let {Task.input=vi; output=vo} = pair in
            let pred = get_pred ~test:true ext.model vi vo in
            [ ColExample, Example (vi,vo);
              ColPred, pred ])
          ext.task.test in
      let l_bindings =
        List.fold_right2
          (fun pair reads l_bindings ->
            let {Task.input=vi; output=vo} = pair in
            let descr =
              match reads with
              | (in_r,out_r,dl)::_ -> Descr (in_r,out_r) (* using only first read *)
              | [] -> Error "No valid description" in
            let pred = get_pred ~test:false ext.model vi vo in
            let row =
              [ ColExample, Example (vi,vo);
                ColDescr, descr;
                ColPred, pred ] in
            row::l_bindings)
          ext.task.train ext.prs.reads l_bindings in
      w_results#set_contents cols l_bindings)
    (fun suggestions ->
      w_suggestions#set_suggestions ["col-md-12 col-xs-12"] suggestions;
      let suggestion_handler =
        (fun sugg ->
          match place#activate sugg with
          | Some p -> k ~push_in_history:true p
          | None -> assert false) in
      w_suggestions#on_suggestion_selection suggestion_handler;
      let _on = Jsutils.toggle_class elt_lis "computing" in (* turn off *)
      ()))


let handle_document_keydown ev place k =
  false

let error_message : exn -> string = function
  | exn -> "Unexpected error: " ^ Printexc.to_string exn

let main () =
  Jsutils.firebug "Start...";
  Webapp.start
    ~make_lis
    ~render_place
    ~handle_document_keydown
    ~error_message

  end
