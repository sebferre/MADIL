
type 'value pair = { input : 'value; output : 'value }
type 'value task = { train : 'value pair list; test : 'value pair list }

let rec task_of_json
      ~(value_of_json : Yojson.Safe.t -> 'value)
        : Yojson.Safe.t -> 'value task =
  let rec aux = function
    | `Assoc ["train", `List trains; "test", `List tests]
      | `Assoc ["test", `List tests; "train", `List trains] ->
       { train = List.map aux_pair trains;
         test = List.map aux_pair tests }
    | `Assoc ["train", `List trains] ->
       { train = List.map aux_pair trains;
         test = [] }
    | _ -> invalid_arg "Invalid JSON task"
  and aux_pair = function
    | `Assoc ["input", input; "output", output]
      | `Assoc ["output", output; "input", input] ->
       { input = value_of_json input;
         output = value_of_json output }
    | _ -> invalid_arg "Invalid JSON pair"
  in
  aux

let from_filename_contents
      ~(value_of_json : Yojson.Safe.t -> 'value)
      (filename : string) (contents : string) : 'value task =
  if Filename.check_suffix filename ".json" then
    let json = Yojson.Safe.from_string contents in
    task_of_json ~value_of_json json
  else failwith "Unexpected task file format"

let from_file
      ~(value_of_json : Yojson.Safe.t -> 'value)
      (filename : string) : 'value task =
  if Filename.check_suffix filename ".json" then
    let json = Yojson.Safe.from_file filename in
    task_of_json ~value_of_json json
  else failwith "Unexpected task file format"
