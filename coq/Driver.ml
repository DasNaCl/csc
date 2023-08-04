open Parser

let maybe_read_line () =
  try Some(read_line())
  with End_of_file -> None

let rec input_loop acc =
  match maybe_read_line () with
  | Some(line) -> input_loop (acc @ [line])
  | None -> String.concat "\n" acc

let run_program input =
  Printf.printf "input: %s\n\n" input;
  let parse_result = string2expr (input |> String.to_seq |> List.of_seq) in
  match parse_result with
  | Some prog ->
    begin
      Printf.printf "%s\n" (expr2string prog |> List.to_seq |> String.of_seq)
    end
  | None -> Printf.printf "parse error"

let read_whole_file filename =
    let ch = open_in_bin filename in
    let s = really_input_string ch (in_channel_length ch) in
    close_in ch;
    s

let run_file file =
  run_program (read_whole_file file)

let main () =
  if Array.length Sys.argv = 1 then
    let input_str = input_loop [] in
    run_program input_str
  else
    List.iter (fun file -> run_file file) (List.tl (Array.to_list Sys.argv))

let _ = main ()

