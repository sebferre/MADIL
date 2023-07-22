
type 'a pair = { input : 'a; output : 'a }
type 'a task = { train : 'a pair list; test : 'a pair list }

let rec task_of_json
      ~(data_of_json : Yojson.Safe.t -> 'a)
        : Yojson.Safe.t -> 'a task =
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
       { input = data_of_json input;
         output = data_of_json output }
    | _ -> invalid_arg "Invalid JSON pair"
  in
  aux

let from_filename_contents
      ~(data_of_json : Yojson.Safe.t -> 'a)
      (filename : string) (contents : string) : 'a task =
  if Filename.check_suffix filename ".json" then
    let json = Yojson.Safe.from_string contents in
    task_of_json ~data_of_json json
  else failwith "Unexpected task file format"

let from_file
      ~(data_of_json : Yojson.Safe.t -> 'a)
      (filename : string) : 'a task =
  if Filename.check_suffix filename ".json" then
    let json = Yojson.Safe.from_file filename in
    task_of_json ~data_of_json json
  else failwith "Unexpected task file format"
