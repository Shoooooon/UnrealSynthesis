open Logic.Formula
open Logic.Variable

(* Utilities for discharging implications --
   The idea will be to spawn processes to invoke Z3 or whichever solver.
   We will generate a function that collects the process and makes sure it verified correctly, returning if not.
   At the end of the proof construction, we will run these functions; if none of them error, the proof is correct.
   Otherwise, an implication is incorrect (or a check did not complete).*)

let rec to_smt_helper_term term =
  match term with
  | Int i ->
      if i < 0 then Printf.sprintf "(- %d)" (-1 * i) else Printf.sprintf "%d" i
  | TVar v -> var_tostr (TermVar v)
  | Minus t -> Printf.sprintf "(- %s)" (to_smt_helper_term t)
  | Plus (t1, t2) ->
      Printf.sprintf "(+ %s %s)" (to_smt_helper_term t1) (to_smt_helper_term t2)

let rec to_smt_helper form =
  match form with
  | True -> "true"
  | False -> "false"
  | And (b1, b2) ->
      Printf.sprintf "(and %s %s)" (to_smt_helper b1) (to_smt_helper b2)
  | Or (b1, b2) ->
      Printf.sprintf "(or %s %s)" (to_smt_helper b1) (to_smt_helper b2)
  | Not b -> Printf.sprintf "(not %s)" (to_smt_helper b)
  | Implies (b1, b2) ->
      Printf.sprintf "(=> %s %s)" (to_smt_helper b1) (to_smt_helper b2)
  | BVar v -> var_tostr (BoolVar v)
  | Equals (t1, t2) ->
      Printf.sprintf "(= %s %s)" (to_smt_helper_term t1) (to_smt_helper_term t2)
  | Less (t1, t2) ->
      Printf.sprintf "(< %s %s)" (to_smt_helper_term t1) (to_smt_helper_term t2)
  | Iff (b1, b2) ->
      Printf.sprintf "(= %s %s)" (to_smt_helper b1) (to_smt_helper b2)
  | Exists (TermVar v, b) ->
      Printf.sprintf "(exists ((%s Int) ) %s)" (var_tostr (TermVar v))
        (to_smt_helper b)
  | Exists (BoolVar v, b) ->
      Printf.sprintf "(exists ((%s Bool) ) %s)" (var_tostr (BoolVar v))
        (to_smt_helper b)
  | Forall (TermVar v, b) ->
      Printf.sprintf "(forall ((%s Int) ) %s)" (var_tostr (TermVar v))
        (to_smt_helper b)
  | Forall (BoolVar v, b) ->
      Printf.sprintf "(forall ((%s Bool) ) %s)" (var_tostr (BoolVar v))
        (to_smt_helper b)
  | Hole (s, arg_list) ->
      Printf.sprintf "(%s %s)" s
        (String.concat " " (List.map to_smt_helper_exp arg_list))

and to_smt_helper_exp e =
  match e with Term t -> to_smt_helper_term t | Boolean b -> to_smt_helper b

module VS = Set.Make (Logic.Variable)

let rec free_vars_term term bound_vars =
  match term with
  | Int _ -> VS.empty
  | TVar v ->
      if VS.mem (TermVar v) bound_vars then VS.empty
      else VS.singleton (TermVar v)
  | Minus t -> free_vars_term t bound_vars
  | Plus (t1, t2) ->
      VS.union (free_vars_term t1 bound_vars) (free_vars_term t2 bound_vars)

let rec free_vars form bound_vars =
  match form with
  | True -> VS.empty
  | False -> VS.empty
  | And (b1, b2) -> VS.union (free_vars b1 bound_vars) (free_vars b2 bound_vars)
  | Or (b1, b2) -> VS.union (free_vars b1 bound_vars) (free_vars b2 bound_vars)
  | Not b -> free_vars b bound_vars
  | Implies (b1, b2) ->
      VS.union (free_vars b1 bound_vars) (free_vars b2 bound_vars)
  | BVar v ->
      if VS.mem (BoolVar v) bound_vars then VS.empty
      else VS.singleton (BoolVar v)
  | Equals (t1, t2) ->
      VS.union (free_vars_term t1 bound_vars) (free_vars_term t2 bound_vars)
  | Less (t1, t2) ->
      VS.union (free_vars_term t1 bound_vars) (free_vars_term t2 bound_vars)
  | Iff (b1, b2) -> VS.union (free_vars b1 bound_vars) (free_vars b2 bound_vars)
  | Exists (v, b) -> free_vars b (VS.add v bound_vars)
  | Forall (v, b) -> free_vars b (VS.add v bound_vars)
  | Hole (_, arg_list) ->
      List.fold_left
        (fun set arg -> VS.union set (free_vars_exp arg bound_vars))
        VS.empty arg_list

and free_vars_exp exp bound_vars =
  match exp with
  | Term t -> free_vars_term t bound_vars
  | Boolean b -> free_vars b bound_vars

let to_negated_smt form name =
  Printf.sprintf
    ";%s\n(set-info :status unknown)\n%s(assert\n(not\n%s\n)\n )\n(check-sat)"
    name
    (VS.fold
       (fun var str ->
         match var with
         | BoolVar _ ->
             Printf.sprintf "%s(declare-const %s Bool)\n" str (var_tostr var)
         | TermVar _ ->
             Printf.sprintf "%s(declare-const %s Int)\n" str (var_tostr var))
       (free_vars form VS.empty) "")
    (to_smt_helper form)

let parse_func_decl definition_str =
  SMT2Parser.Parser.fun_decl SMT2Parser.Lexer.read
    (Lexing.from_string definition_str)

(* Hole checking/manipulating functions *)
let rec has_holes form =
  match form with
  | True -> false
  | False -> false
  | BVar _ -> false
  | And (l, r) -> has_holes l || has_holes r
  | Or (l, r) -> has_holes l || has_holes r
  | Not _ -> false
  | Implies (l, r) -> has_holes l || has_holes r
  | Equals (_, _) -> false
  | Less (_, _) -> false
  | Iff (l, r) -> has_holes l || has_holes r
  | Exists (_, body) -> has_holes body
  | Forall (_, body) -> has_holes body
  | Hole (_, _) -> true

let rec get_holes form =
  match form with
  | True -> []
  | False -> []
  | BVar _ -> []
  | And (l, r) -> List.append (get_holes l) (get_holes r)
  | Or (l, r) -> List.append (get_holes l) (get_holes r)
  | Not _ -> []
  | Implies (l, r) -> List.append (get_holes l) (get_holes r)
  | Equals (_, _) -> []
  | Less (_, _) -> []
  | Iff (l, r) -> List.append (get_holes l) (get_holes r)
  | Exists (_, body) -> get_holes body
  | Forall (_, body) -> get_holes body
  | Hole (h, vl) -> [ (h, vl) ]

(* Spawn a process to check the implication.
   Return a blocking function that confirms implication is valid. *)
type file_pair = { name_num : int; form : formula }

(* Returns a function that can be used to check implication.
   Such a function must take a hyp:Formula and conclusion:Formula and return a bool lazy.*)
let no_hole_implicator () =
  let file_logger = ref [] and file_counter = ref 0 in
  let no_hole_implies hyp conc =
    (* Write SMT2 File *)
    (* let filename_map character =
         match character with
         | '=' -> 'e'
         | '>' -> 'g'
         | '<' -> 'l'
         | '+' -> 'p'
         | '!' -> 'n'
         | '&' -> 'a'
         | c -> c
       in *)
    (* If the file named by our fresh counter exists, skip the number. It could be important to someone else. *)
    while Sys.file_exists (Printf.sprintf "Implication%d.smt" !file_counter) do
      file_counter := !file_counter + 1
    done;
    (* If we have not dispatched a query for this implication... *)
    if
      not
        (List.mem
           (Implies (hyp, conc))
           (List.map (fun a -> a.form) !file_logger))
    then (
      let filename_pref =
        Printf.sprintf "Implication%d" !file_counter
        (* String.map filename_map (form_tostr (Implies (hyp, conc))) *)
      in
      (* Set up the file and record in the structure. *)
      let oc = open_out (Printf.sprintf "%s.smt" filename_pref) in
      Printf.fprintf oc "%s" (to_negated_smt (Implies (hyp, conc)) "test");
      close_out oc;
      file_logger :=
        List.cons
          { name_num = !file_counter; form = Implies (hyp, conc) }
          !file_logger;
      file_counter := !file_counter;
      (* Fork and exec a query *)
      let kid_pid = Unix.fork () in
      if kid_pid = 0 then (
        let fd =
          Unix.openfile
            (Printf.sprintf "%s.out" filename_pref)
            [ O_CREAT; O_WRONLY ] 0
        in
        Unix.dup2 fd Unix.stdout;
        Unix.execvp "z3"
          (Array.of_list
             [ "z3"; "-smt2"; Printf.sprintf "%s.smt" filename_pref ]))
      else
        (* Return function that collects SMT result *)
        lazy
          (if Unix.waitpid [] kid_pid <> (kid_pid, WEXITED 0) then false
           else
             let f_channel = open_in (Printf.sprintf "%s.out" filename_pref) in
             input_line f_channel = "unsat")
      (* TODO: It might be good to have the below behavior be the default in both branches, but waitpid might be better. *)
      (* If the query was already run, just read the result. *))
    else
      let name_num =
        (List.find (fun a -> a.form = Implies (hyp, conc)) !file_logger)
          .name_num
      in
      let filename_pref = Printf.sprintf "Implication%d" name_num in
      lazy
        (while not (Sys.file_exists (Printf.sprintf "%s.out" filename_pref)) do
           Unix.sleep 1
         done;
         let f_channel = open_in (Printf.sprintf "%s.out" filename_pref) in
         input_line f_channel = "unsat")
  in
  no_hole_implies

(* Returns a function that can be used to check implication and a function to synthesize solutions to holes.
   Such an implication checking function must take a hyp:Formula and conclusion:Formula and return a bool lazy.
   The synthesis function expects no inputs, as they are stored in a persistent context carried along with the returned functions.*)
let implicator_synth () =
  (* Create persistent context to track synthesis constraints. *)
  let constraint_logger = ref []
  and (synth_mapper : ((string * variable list) * formula) list option ref) =
    ref None
  and file_counter = ref 0
  and has_solutions = ref None
  and no_hole_implies = no_hole_implicator () in
  let synthesize_hole_values =
    lazy
      (match !synth_mapper with
      | Some s -> s
      | None ->
          (* Find distinct holes and rename vars (to write synth-invs later). Also set the synth-mapper.*)
          let hole_list =
            List.fold_left
              (fun list (name, vl) ->
                if List.exists (fun (s, _) -> String.equal name s) list then
                  list
                else List.cons (name, vl) list)
              []
              (List.flatten
                 (List.map
                    (fun aconstraint -> get_holes aconstraint)
                    !constraint_logger))
          in
          let i = ref 0 in
          let hole_list =
            List.map
              (fun (s, vl) ->
                ( s,
                  List.map
                    (fun v ->
                      match v with
                      | Term _ ->
                          i := !i + 1;
                          TermVar (T (Printf.sprintf "a_%d" !i))
                      | Boolean _ ->
                          i := !i + 1;
                          BoolVar (B (Printf.sprintf "a_%d" !i)))
                    vl ))
              hole_list
          in
          (* Assemble .sy file *)
          (* Make file *)
          while
            Sys.file_exists (Printf.sprintf "Synthesis%d.sy" !file_counter)
          do
            file_counter := !file_counter + 1
          done;
          let filename_pref = Printf.sprintf "Synthesis%d" !file_counter in
          (* Set up the file and record in the structure. *)
          let oc = open_out (Printf.sprintf "%s.sy" filename_pref) in
          Printf.fprintf oc "(set-logic LIA)\n\n";
          (* Declare free variables *)
          let f_vars =
            List.fold_left
              (fun set aconstraint ->
                VS.union set (free_vars aconstraint VS.empty))
              VS.empty !constraint_logger
          in
          Printf.fprintf oc "%s\n"
            (VS.fold
               (fun var str ->
                 match var with
                 | BoolVar _ ->
                     Printf.sprintf "%s(declare-var %s Bool)\n" str
                       (var_tostr var)
                 | TermVar _ ->
                     Printf.sprintf "%s(declare-var %s Int)\n" str
                       (var_tostr var))
               f_vars "");
          (* Declare Holes to synthesize *)
          Printf.fprintf oc "%s\n"
            (String.concat "\n"
               (List.map
                  (fun (s, vl) ->
                    Printf.sprintf "(synth-inv %s (%s))" s
                      (String.concat " "
                         (List.map
                            (fun var ->
                              match var with
                              | BoolVar _ ->
                                  Printf.sprintf "(%s Bool)" (var_tostr var)
                              | TermVar _ ->
                                  Printf.sprintf "(%s Int)" (var_tostr var))
                            vl)))
                  hole_list));
          (* Write constraints. *)
          Printf.fprintf oc "%s\n"
            (String.concat "\n"
               (List.map
                  (fun aconstraint ->
                    Printf.sprintf "(constraint %s)" (to_smt_helper aconstraint))
                  !constraint_logger));

          Printf.fprintf oc "(check-synth)";
          close_out oc;

          (* Dispatch synthesis to solver *)
          (* Fork and exec a query *)
          let kid_pid = Unix.fork () in
          if kid_pid = 0 then (
            (* Run synthesis via cvc5 *)
            let fd =
              Unix.openfile
                (Printf.sprintf "%s.out" filename_pref)
                [ O_CREAT; O_WRONLY ] 0
            in
            Unix.dup2 fd Unix.stdout;
            Unix.execvp "cvc5"
              (Array.of_list [ "cvc5"; Printf.sprintf "%s.sy" filename_pref ])
            (* Wait. If can't synth, then record no solutions.
                Else, record existenct of a solution, store solution, and return it as string (for now).
                TODO: Parse string so a mapping is returned instead; the contents of the mapping can be subbed intop the proof. *))
          else if Unix.waitpid [] kid_pid <> (kid_pid, WEXITED 0) then (
            has_solutions := Some false;
            [])
          else
            let output = Arg.read_arg (Printf.sprintf "%s.out" filename_pref) in
            has_solutions := Some (Array.get output 0 = "(");
            if Array.get output 0 = "(" then (
              let syn_list =
                List.map
                  (fun (name, body) ->
                    (List.find (fun (h, _) -> h = name) hole_list, body))
                  (List.map
                     (fun decl_str -> parse_func_decl decl_str)
                     (Array.to_list
                        (Array.sub output 1 (Array.length output - 2))))
              in
              synth_mapper := Some syn_list;
              syn_list)
            else [])
  in

  let implies hyp conc =
    (* If there are no holes, discharge separately. *)
    if not (has_holes (Implies (hyp, conc))) then no_hole_implies hyp conc
    else (
      (* If holes are present, then add the constraint to our list *)
      constraint_logger := List.cons (Implies (hyp, conc)) !constraint_logger;
      lazy
        (match !has_solutions with
        | None -> (
            ignore (Lazy.force synthesize_hole_values);
            match !has_solutions with None -> false | Some s -> s)
        | Some s -> s))
  in

  (implies, synthesize_hole_values)
