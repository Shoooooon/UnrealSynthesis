open Proofrules.ProofRule
open ULSynth.ProofStrat

let usage_msg =
  "ULSynth [-holes] [-hole-template] [-vectors] [-no-vc-simplify] [-concise] [-context] <file1>"

let holes = ref INVS_SPECIFIED
let vectors = ref SIMPLE
let sygus_template = ref NONE
let vc_simp = ref QUANTIFY_COLLECT
let exp_only = ref STMTS
let concise = ref false
let context = ref false
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
    ( "-hole-template",
      Arg.String
        (fun s ->
          match s with
          | "bitvector" -> sygus_template := BITVEC
          | _ -> sygus_template := NONE),
      "Set this flag if you want to guide sygus hole search with a template \
       grammar." );
    ( "-holes",
      Arg.Unit (fun _ -> holes := HOLE_SYNTH),
      "Set this flag if you have holes in your specification." );
    ( "-no-vc-simplify",
      Arg.Unit (fun _ -> vc_simp := NO_SIMP),
      "Set this flag if you would like to disable quantifier collection to \
       simply verification conditions before discharging them." );
    ( "-expression",
      Arg.Unit (fun _ -> exp_only := EXPRESSIONS_ONLY),
      "Set this flag if your set of programs contains no statements and you \
       would like to use this fact in your nonterminal summaries. Note this  \n\
      \       feature is not yet supported when target preconditions have \
       auxiliary variables." );
    ( "-concise",
      Arg.Set concise,
      "Set this flag if want output 'proven' or 'unproven' instead of a \
       printed proof." );
    ( "-context",
      Arg.Set context,
      "Set this flag if you want to specify a preproved context in the input file." );
  ]

let handle_filename file = filename := file

let () =
  Arg.parse speclist handle_filename usage_msg;
  let ctx, trip = 
    if !context 
      then (ULSynth.Claimparser.ctxtrip ULSynth.Claimlexer.read
        (Lexing.from_string
            (String.concat "\n" (Array.to_list (Arg.read_arg !filename)))))
      else [], (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
      (Lexing.from_string
          (String.concat "\n" (Array.to_list (Arg.read_arg !filename)))))
    in
  let pf =
    prove
      ctx trip
      !holes !vectors !sygus_template !vc_simp !exp_only
  in
  if !concise then
    print_endline (if is_correct pf then "proven" else "unproven")
  else print_endline (ruleApp_tostr pf)
