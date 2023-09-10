open Proofrules.ProofRule

let usage_msg = "Nope2ULSynth -ex <file1> -grm <file2> -o <file3>"
let examples_filename = ref ""
let grammar_filename = ref ""
let output_filename = ref ""

let speclist =
  [
    ("-ex", Arg.Set_string examples_filename, "Set input examples filename.");
    ("-grm", Arg.Set_string grammar_filename, "Set input grammar filename.");
    ("-o", Arg.Set_string output_filename, "Set output filename.");
  ]

let () =
  Arg.parse speclist (fun _ -> ()) usage_msg;
  let trp =
    Nopeparser.triple Nopelexer.read
      (Lexing.from_string
         (String.concat "\n"
            (Array.to_list
               (Array.append
                  (Arg.read_arg !examples_filename)
                  (Arg.read_arg !grammar_filename)))))
  in
  let out_channel = open_out !output_filename in
  Printf.fprintf out_channel "%s" (trip_to_parseable_str trp)
