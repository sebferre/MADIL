
type 'value pair = { input : 'value; output : 'value }
type 'value task = { train : 'value pair list; test : 'value pair list }

let rec task_of_json
      ~(value_of_json : Yojson.Safe.t -> 'value)
        : Yojson.Safe.t -> 'value task =
  let rec aux = function
    | `Assoc fields ->
       let trains =
         match List.assoc_opt "train" fields with
         | Some (`List trains) -> trains
         | _ -> invalid_arg "Invalid JSON task: missing train field" in
       let tests =
         match List.assoc_opt "test" fields with
         | Some (`List tests) -> tests
         | _ -> [] in
       { train = List.map aux_pair trains;
         test = List.map aux_pair tests }
    | _ -> invalid_arg "Invalid JSON task"
  and aux_pair = function
    | `Assoc fields ->
       let input =
         match List.assoc_opt "input" fields with
         | Some i -> value_of_json i
         | None -> invalid_arg "Invalid JSON pair: missing input" in
       let output =
         match List.assoc_opt "output" fields with
         | Some o -> value_of_json o
         | None -> invalid_arg "Invalid JSON pair: missing output" in
       { input; output }
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
