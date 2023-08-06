open ULSynth.ProofRule
open ULSynth.ProofStrat

let () =
  if Array.length Sys.argv != 2 then
    print_endline "Incorrect number of arguments."
  else
    let filename = Array.get Sys.argv 1 in
    print_endline
      (ruleApp_tostr
         (prove
            (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
               (Lexing.from_string
                  (String.concat "\n" (Array.to_list (Arg.read_arg filename)))))
            HOLE_SYNTH))
