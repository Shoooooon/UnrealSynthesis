open ULSynth.ProofRule
open ULSynth.ProofStrat

let usage_msg = "ULSynth [-holes] [-vectors] <file1>"
let holes = ref false
let vectors = ref false
let filename = ref ""

let speclist =
  [
    ( "-vectors",
      Arg.Set vectors,
      "Set this flag if your specification is over vector-states." );
    ( "-holes",
      Arg.Set holes,
      "Set this flag if you have holes in your specification." );
  ]

let handle_filename file = filename := file

let () =
  Arg.parse speclist handle_filename usage_msg;
  let hole_synth = if !holes then HOLE_SYNTH else INVS_SPECIFIED
  and vector_mode = if !vectors then VECTOR_STATE else SIMPLE in
  print_endline
    (ruleApp_tostr
       (prove
          (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
             (Lexing.from_string
                (String.concat "\n" (Array.to_list (Arg.read_arg !filename)))))
          hole_synth vector_mode))
