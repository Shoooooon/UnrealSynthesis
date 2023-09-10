open Proofrules.ProofRule
open ULSynth.ProofStrat

let usage_msg = "ULSynth [-holes] [-vectors] <file1>"
let holes = ref INVS_SPECIFIED
let vectors = ref SIMPLE
let concise = ref false
let filename = ref ""

let speclist =
  [
    ( "-vectors",
      Arg.String
        (fun s ->
          match s with
          | "infinite" -> vectors := VECTOR_STATE
          | "finite" -> vectors := FINITE_VECTOR_STATE
          | _ -> vectors := SIMPLE),
      "Set this flag to specify vector-state mode (simple, finite, infinite). \
       Default is simple." );
    ( "-holes",
      Arg.Unit (fun _ -> holes := HOLE_SYNTH),
      "Set this flag if you have holes in your specification." );
    ( "-concise",
      Arg.Set concise,
      "Set this flag if want output 'proven' or 'unproven' instead of a \
       printed proof." );
  ]

let handle_filename file = filename := file

let () =
  Arg.parse speclist handle_filename usage_msg;
  let pf =
    prove
      (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
         (Lexing.from_string
            (String.concat "\n" (Array.to_list (Arg.read_arg !filename)))))
      !holes !vectors
  in
  if !concise then
    print_endline (if is_correct pf then "proven" else "unproven")
  else print_endline (ruleApp_tostr pf)
