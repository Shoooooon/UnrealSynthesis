(* open Logic.Formula
   open Programs.Program
   open Programs.NonTerminal *)

(* let check_proof_no_hole_simple trip expected =
  let pf =
    ULSynth.ProofStrat.prove trip ULSynth.ProofStrat.INVS_SPECIFIED
      ULSynth.ProofStrat.SIMPLE ULSynth.ProofStrat.NONE ULSynth.ProofStrat.QUANTIFY_COLLECT
  in
  let a = Proofrules.ProofRule.ruleApp_tostr pf in
  if not (compare a expected = 0) then (
    print_endline a;
    print_endline "")

let check_proof_no_hole_finite_vec trip expected =
  let pf =
    ULSynth.ProofStrat.prove trip ULSynth.ProofStrat.INVS_SPECIFIED
      ULSynth.ProofStrat.FINITE_VECTOR_STATE ULSynth.ProofStrat.NONE ULSynth.ProofStrat.QUANTIFY_COLLECT
  in
  let a = Proofrules.ProofRule.ruleApp_tostr pf in
  if not (compare a expected = 0) then (
    print_endline a;
    print_endline "")

let check_proof_with_hole_finite_vec trip expected =
  let pf =
    ULSynth.ProofStrat.prove trip ULSynth.ProofStrat.HOLE_SYNTH
      ULSynth.ProofStrat.FINITE_VECTOR_STATE ULSynth.ProofStrat.NONE ULSynth.ProofStrat.QUANTIFY_COLLECT
  in
  let a = Proofrules.ProofRule.ruleApp_tostr pf in
  if not (compare a expected = 0) then (
    print_endline a;
    print_endline "")

let check_proof_no_hole_vector_state trip expected =
  let pf =
    ULSynth.ProofStrat.prove trip ULSynth.ProofStrat.INVS_SPECIFIED
      ULSynth.ProofStrat.VECTOR_STATE ULSynth.ProofStrat.NONE ULSynth.ProofStrat.QUANTIFY_COLLECT
  in
  let a = Proofrules.ProofRule.ruleApp_tostr pf in
  if not (compare a expected = 0) then (
    print_endline a;
    print_endline "")

let check_proof_with_hole_simple trip expected_pf =
   let pf =
     ULSynth.ProofStrat.prove trip ULSynth.ProofStrat.HOLE_SYNTH
       ULSynth.ProofStrat.SIMPLE ULSynth.ProofStrat.NONE ULSynth.ProofStrat.QUANTIFY_COLLECT
   in
   let pf_str = Proofrules.ProofRule.ruleApp_tostr pf in
   if not (compare pf_str expected_pf = 0) then (
     print_endline pf_str;
     print_endline "")

let eq_int_term (t1, t2) = Logic.Formula.Equals (ITerm t1, ITerm t2)
let less_int_term (t1, t2) = Logic.Formula.Less (ITerm t1, ITerm t2) *)
(* let eq_bitv_term (t1, t2) = Logic.Formula.Equals (BitvTerm t1, BitvTerm t2) *)
(* let less_bitv_term (t1, t2) = Logic.Formula.Less (BitvTerm t1, BitvTerm t2) *)

(* let test_axiom =
     check_proof_no_hole_simple
       { pre = False; prog = Term (Numeric (Int 1)); post = False }
       "Int: -> {F} 1 {F}\nWeaken: {F} 1 {F} -> {F} 1 {F}";
     check_proof_no_hole_simple
       { pre = True; prog = Term (Numeric (Int 0)); post = eq_int_term (Int 0, ITVar ET) }
       "Int: -> {(0 == 0)} 0 {(0 == e_t)}\n\
        Weaken: {(0 == 0)} 0 {(0 == e_t)} -> {T} 0 {(0 == e_t)}";
     check_proof_no_hole_simple
       { pre = False; prog = Boolean False; post = BVar BT }
       "False: -> {F} F {b_t}\nWeaken: {F} F {b_t} -> {F} F {b_t}";
     check_proof_no_hole_simple
       { pre = True; prog = Boolean True; post = BVar BT }
       "True: -> {T} T {b_t}\nWeaken: {T} T {b_t} -> {T} T {b_t}"

let test_not =
check_proof_no_hole_simple
  { pre = True; prog = Boolean (Not False); post = BVar BT }
  "False: -> {!F} F {!b_t}\n\
  Not: {!F} F {!b_t} -> {!F} !F {b_t}\n\
  Weaken: {!F} !F {b_t} -> {T} !F {b_t}"

let test_binary =
(* Plus *)
check_proof_no_hole_simple
  {
    pre = Not True;
    prog = Term (Numeric (Plus (Int 1, Int 1)));
    post = eq_int_term (ITVar ET, Int 2);
  }
  "Int: -> {((1 + 1) == 2)} 1 {((e_t + 1) == 2)}\n\
  Int: -> {((fresh1 + 1) == 2)} 1 {((fresh1 + e_t) == 2)}\n\
  Plus: {((1 + 1) == 2)} 1 {((e_t + 1) == 2)}, {((fresh1 + 1) == 2)} 1 \
  {((fresh1 + e_t) == 2)} -> {((1 + 1) == 2)} (1 + 1) {(e_t == 2)}\n\
  Weaken: {((1 + 1) == 2)} (1 + 1) {(e_t == 2)} -> {!T} (1 + 1) {(e_t == 2)}";
(* And *)
check_proof_no_hole_simple
  {
    pre = And (True, And (True, False));
    prog = Boolean (And (True, And (True, False)));
    post = BVar BT;
  }
  "True: -> {(T && (T && F))} T {(b_t && (T && F))}\n\
    True: -> {(fresh1 && (T && F))} T {(fresh1 && (b_t && F))}\n\
    False: -> {(fresh1 && (fresh2 && F))} F {(fresh1 && (fresh2 && b_t))}\n\
    And: {(fresh1 && (T && F))} T {(fresh1 && (b_t && F))}, {(fresh1 && \
    (fresh2 && F))} F {(fresh1 && (fresh2 && b_t))} -> {(fresh1 && (T && F))} \
    (T && F) {(fresh1 && b_t)}\n\
    And: {(T && (T && F))} T {(b_t && (T && F))}, {(fresh1 && (T && F))} (T \
    && F) {(fresh1 && b_t)} -> {(T && (T && F))} (T && (T && F)) {b_t}\n\
    Weaken: {(T && (T && F))} (T && (T && F)) {b_t} -> {(T && (T && F))} (T \
    && (T && F)) {b_t}";
  (* Or *)
  check_proof_no_hole_simple
    {
      pre = True;
      prog = Boolean (And (True, Or (True, False)));
      post = BVar BT;
    }
    "True: -> {(T && (T || F))} T {(b_t && (T || F))}\n\
    True: -> {(fresh1 && (T || F))} T {(fresh1 && (b_t || F))}\n\
    False: -> {(fresh1 && (fresh2 || F))} F {(fresh1 && (fresh2 || b_t))}\n\
    Or: {(fresh1 && (T || F))} T {(fresh1 && (b_t || F))}, {(fresh1 && \
    (fresh2 || F))} F {(fresh1 && (fresh2 || b_t))} -> {(fresh1 && (T || F))} \
    (T || F) {(fresh1 && b_t)}\n\
    And: {(T && (T || F))} T {(b_t && (T || F))}, {(fresh1 && (T || F))} (T \
    || F) {(fresh1 && b_t)} -> {(T && (T || F))} (T && (T || F)) {b_t}\n\
    Weaken: {(T && (T || F))} (T && (T || F)) {b_t} -> {T} (T && (T || F)) \
    {b_t}";
  (* Equals *)
  check_proof_no_hole_simple
    {
      pre = eq_int_term (Int 0, ITVar (T "x"));
      prog = Boolean (Equals (Numeric (Int 0), Numeric (Var "x")));
      post = BVar BT;
    }
    "Int: -> {(0 == x)} 0 {(e_t == x)}\n\
    Var: -> {(fresh1 == x)} x {(fresh1 == e_t)}\n\
    Equals: {(0 == x)} 0 {(e_t == x)}, {(fresh1 == x)} x {(fresh1 == e_t)} -> \
    {(0 == x)} (0 = x) {b_t}\n\
    Weaken: {(0 == x)} (0 = x) {b_t} -> {(0 == x)} (0 = x) {b_t}";
  (* Less *)
  check_proof_no_hole_simple
    {
      pre = Not (less_int_term (Int 0, ITVar (T "x")));
      prog = Boolean (Less (Int 0, Var "x"));
      post = Not (BVar BT);
    }
    "Int: -> {!(0 < x)} 0 {!(e_t < x)}\n\
    Var: -> {!(fresh1 < x)} x {!(fresh1 < e_t)}\n\
    Less: {!(0 < x)} 0 {!(e_t < x)}, {!(fresh1 < x)} x {!(fresh1 < e_t)} -> \
    {!(0 < x)} (0 < x) {!b_t}\n\
    Weaken: {!(0 < x)} (0 < x) {!b_t} -> {!(0 < x)} (0 < x) {!b_t}"

let test_ITE =
  (* Numeric ITE *)
  check_proof_no_hole_simple
    {
      pre = False;
      prog = Term (Numeric (ITE (Equals (Numeric (Var "x"), Numeric (Int 0)), Int 1, Var "x")));
      post = eq_int_term (ITVar ET, ITVar (T "x"));
    }
    "Var: -> {(((x == 0) => (1 == x)) && (!(x == 0) => (x == x)))} x {(((e_t \
    == 0) => (1 == x)) && (!(e_t == 0) => (x == x)))}\n\
    Int: -> {(((fresh1 == 0) => (1 == x)) && (!(fresh1 == 0) => (x == x)))} 0 \
    {(((fresh1 == e_t) => (1 == x)) && (!(fresh1 == e_t) => (x == x)))}\n\
    Equals: {(((x == 0) => (1 == x)) && (!(x == 0) => (x == x)))} x {(((e_t \
    == 0) => (1 == x)) && (!(e_t == 0) => (x == x)))}, {(((fresh1 == 0) => (1 \
    == x)) && (!(fresh1 == 0) => (x == x)))} 0 {(((fresh1 == e_t) => (1 == \
    x)) && (!(fresh1 == e_t) => (x == x)))} -> {(((x == 0) => (1 == x)) && \
    (!(x == 0) => (x == x)))} (x = 0) {((b_t => (1 == x)) && (!b_t => (x == \
    x)))}\n\
    Int: -> {(1 == x)} 1 {(e_t == x)}\n\
    Var: -> {(x == x)} x {(e_t == x)}\n\
    ITE: {(((x == 0) => (1 == x)) && (!(x == 0) => (x == x)))} (x = 0) {((b_t \
    => (1 == x)) && (!b_t => (x == x)))}, {(1 == x)} 1 {(e_t == x)}, {(x == \
    x)} x {(e_t == x)} -> {(((x == 0) => (1 == x)) && (!(x == 0) => (x == \
    x)))} (if (x = 0) then 1 else x) {(e_t == x)}\n\
    Weaken: {(((x == 0) => (1 == x)) && (!(x == 0) => (x == x)))} (if (x = 0) \
    then 1 else x) {(e_t == x)} -> {F} (if (x = 0) then 1 else x) {(e_t == \
    x)}";
  (* Stmt ITE *)
  check_proof_no_hole_simple
    {
      pre = True;
      prog =
        Stmt
          (ITE
            (Equals (Numeric (Int 1), Numeric (Var "x")), Assign ("x", Int 0), Assign ("x", Int 1)));
      post = eq_int_term (ITVar (T "x"), Int 1);
    }
    "Int: -> {(((1 == x) => (0 == 1)) && (!(1 == x) => (1 == 1)))} 1 {(((e_t \
    == x) => (0 == 1)) && (!(e_t == x) => (1 == 1)))}\n\
    Var: -> {(((fresh1 == x) => (0 == 1)) && (!(fresh1 == x) => (1 == 1)))} x \
    {(((fresh1 == e_t) => (0 == 1)) && (!(fresh1 == e_t) => (1 == 1)))}\n\
    Equals: {(((1 == x) => (0 == 1)) && (!(1 == x) => (1 == 1)))} 1 {(((e_t \
    == x) => (0 == 1)) && (!(e_t == x) => (1 == 1)))}, {(((fresh1 == x) => (0 \
    == 1)) && (!(fresh1 == x) => (1 == 1)))} x {(((fresh1 == e_t) => (0 == \
    1)) && (!(fresh1 == e_t) => (1 == 1)))} -> {(((1 == x) => (0 == 1)) && \
    (!(1 == x) => (1 == 1)))} (1 = x) {((b_t => (0 == 1)) && (!b_t => (1 == \
    1)))}\n\
    Int: -> {(0 == 1)} 0 {(e_t == 1)}\n\
    Assign: {(0 == 1)} 0 {(e_t == 1)} -> {(0 == 1)} (x := 0) {(x == 1)}\n\
    Int: -> {(1 == 1)} 1 {(e_t == 1)}\n\
    Assign: {(1 == 1)} 1 {(e_t == 1)} -> {(1 == 1)} (x := 1) {(x == 1)}\n\
    ITE: {(((1 == x) => (0 == 1)) && (!(1 == x) => (1 == 1)))} (1 = x) {((b_t \
    => (0 == 1)) && (!b_t => (1 == 1)))}, {(0 == 1)} (x := 0) {(x == 1)}, {(1 \
    == 1)} (x := 1) {(x == 1)} -> {(((1 == x) => (0 == 1)) && (!(1 == x) => \
    (1 == 1)))} (if (1 = x) then (x := 0) else (x := 1)) {(x == 1)}\n\
    FALSE!!!Weaken: {(((1 == x) => (0 == 1)) && (!(1 == x) => (1 == 1)))} (if \
    (1 = x) then (x := 0) else (x := 1)) {(x == 1)} -> {T} (if (1 = x) then \
    (x := 0) else (x := 1)) {(x == 1)}"

let test_stmt =
  (* Assign *)
  check_proof_no_hole_simple
    {
      pre = False;
      prog = Stmt (Assign ("x", Plus (Int 1, Int 1)));
      post = eq_int_term (ITVar (T "x"), Int 2);
    }
    "Int: -> {((1 + 1) == 2)} 1 {((e_t + 1) == 2)}\n\
    Int: -> {((fresh1 + 1) == 2)} 1 {((fresh1 + e_t) == 2)}\n\
    Plus: {((1 + 1) == 2)} 1 {((e_t + 1) == 2)}, {((fresh1 + 1) == 2)} 1 \
    {((fresh1 + e_t) == 2)} -> {((1 + 1) == 2)} (1 + 1) {(e_t == 2)}\n\
    Assign: {((1 + 1) == 2)} (1 + 1) {(e_t == 2)} -> {((1 + 1) == 2)} (x := \
    (1 + 1)) {(x == 2)}\n\
    Weaken: {((1 + 1) == 2)} (x := (1 + 1)) {(x == 2)} -> {F} (x := (1 + 1)) \
    {(x == 2)}";
  (* Seq *)
  check_proof_no_hole_simple
    {
      pre = True;
      prog = Stmt (Seq (Assign ("x", Plus (Int 1, Int 1)), Assign ("x", Int 1)));
      post = eq_int_term (ITVar (T "x"), Int 1);
    }
    "Int: -> {(1 == 1)} 1 {(1 == 1)}\n\
    Int: -> {(1 == 1)} 1 {(1 == 1)}\n\
    Plus: {(1 == 1)} 1 {(1 == 1)}, {(1 == 1)} 1 {(1 == 1)} -> {(1 == 1)} (1 + \
    1) {(1 == 1)}\n\
    Assign: {(1 == 1)} (1 + 1) {(1 == 1)} -> {(1 == 1)} (x := (1 + 1)) {(1 == \
    1)}\n\
    Int: -> {(1 == 1)} 1 {(e_t == 1)}\n\
    Assign: {(1 == 1)} 1 {(e_t == 1)} -> {(1 == 1)} (x := 1) {(x == 1)}\n\
    Seq: {(1 == 1)} (x := (1 + 1)) {(1 == 1)}, {(1 == 1)} (x := 1) {(x == 1)} \
    -> {(1 == 1)} ((x := (1 + 1)); (x := 1)) {(x == 1)}\n\
    Weaken: {(1 == 1)} ((x := (1 + 1)); (x := 1)) {(x == 1)} -> {T} ((x := (1 \
    + 1)); (x := 1)) {(x == 1)}"

let test_while =
  (* Bad While *)
  check_proof_no_hole_simple
    {
      pre = True;
      prog = Stmt (While (False, True, Assign ("x", Int 1)));
      post = eq_int_term (ITVar (T "x"), Int 1);
    }
    "False: -> {(T => ((!F => (x == 1)) && (F => T)))} F {(T => ((!b_t => (x \
    == 1)) && (b_t => T)))}\n\
    FALSE!!!Weaken: {(T => ((!F => (x == 1)) && (F => T)))} F {(T => ((!b_t \
    => (x == 1)) && (b_t => T)))} -> {T} F {(T => ((!b_t => (x == 1)) && (b_t \
    => T)))}\n\
    Int: -> {T} 1 {T}\n\
    Assign: {T} 1 {T} -> {T} (x := 1) {T}\n\
    While: {T} F {(T => ((!b_t => (x == 1)) && (b_t => T)))}, {T} (x := 1) \
    {T} -> {T} (while F do (Inv=T) (x := 1)) {(x == 1)}\n\
    Weaken: {T} (while F do (Inv=T) (x := 1)) {(x == 1)} -> {T} (while F do \
    (Inv=T) (x := 1)) {(x == 1)}";
  check_proof_no_hole_simple
    {
      pre = less_int_term (ITVar (T "x"), Int 4);
      prog =
        Stmt
          (While
            ( Less (Var "x", Plus (Int 1, Plus (Int 1, Int 1))),
              True,
              Assign ("x", Plus (Var "x", Plus (Int 1, Int 1))) ));
      post = eq_int_term (ITVar (T "x"), Int 3);
    }
    "Var: -> {(T => ((!(x < (1 + (1 + 1))) => (x == 3)) && ((x < (1 + (1 + \
    1))) => T)))} x {(T => ((!(e_t < (1 + (1 + 1))) => (x == 3)) && ((e_t < \
    (1 + (1 + 1))) => T)))}\n\
    Int: -> {(T => ((!(fresh1 < (1 + (1 + 1))) => (x == 3)) && ((fresh1 < (1 \
    + (1 + 1))) => T)))} 1 {(T => ((!(fresh1 < (e_t + (1 + 1))) => (x == 3)) \
    && ((fresh1 < (e_t + (1 + 1))) => T)))}\n\
    Int: -> {(T => ((!(fresh1 < (fresh2 + (1 + 1))) => (x == 3)) && ((fresh1 \
    < (fresh2 + (1 + 1))) => T)))} 1 {(T => ((!(fresh1 < (fresh2 + (e_t + \
    1))) => (x == 3)) && ((fresh1 < (fresh2 + (e_t + 1))) => T)))}\n\
    Int: -> {(T => ((!(fresh1 < (fresh2 + (fresh3 + 1))) => (x == 3)) && \
    ((fresh1 < (fresh2 + (fresh3 + 1))) => T)))} 1 {(T => ((!(fresh1 < \
    (fresh2 + (fresh3 + e_t))) => (x == 3)) && ((fresh1 < (fresh2 + (fresh3 + \
    e_t))) => T)))}\n\
    Plus: {(T => ((!(fresh1 < (fresh2 + (1 + 1))) => (x == 3)) && ((fresh1 < \
    (fresh2 + (1 + 1))) => T)))} 1 {(T => ((!(fresh1 < (fresh2 + (e_t + 1))) \
    => (x == 3)) && ((fresh1 < (fresh2 + (e_t + 1))) => T)))}, {(T => \
    ((!(fresh1 < (fresh2 + (fresh3 + 1))) => (x == 3)) && ((fresh1 < (fresh2 \
    + (fresh3 + 1))) => T)))} 1 {(T => ((!(fresh1 < (fresh2 + (fresh3 + \
    e_t))) => (x == 3)) && ((fresh1 < (fresh2 + (fresh3 + e_t))) => T)))} -> \
    {(T => ((!(fresh1 < (fresh2 + (1 + 1))) => (x == 3)) && ((fresh1 < \
    (fresh2 + (1 + 1))) => T)))} (1 + 1) {(T => ((!(fresh1 < (fresh2 + e_t)) \
    => (x == 3)) && ((fresh1 < (fresh2 + e_t)) => T)))}\n\
    Plus: {(T => ((!(fresh1 < (1 + (1 + 1))) => (x == 3)) && ((fresh1 < (1 + \
    (1 + 1))) => T)))} 1 {(T => ((!(fresh1 < (e_t + (1 + 1))) => (x == 3)) && \
    ((fresh1 < (e_t + (1 + 1))) => T)))}, {(T => ((!(fresh1 < (fresh2 + (1 + \
    1))) => (x == 3)) && ((fresh1 < (fresh2 + (1 + 1))) => T)))} (1 + 1) {(T \
    => ((!(fresh1 < (fresh2 + e_t)) => (x == 3)) && ((fresh1 < (fresh2 + \
    e_t)) => T)))} -> {(T => ((!(fresh1 < (1 + (1 + 1))) => (x == 3)) && \
    ((fresh1 < (1 + (1 + 1))) => T)))} (1 + (1 + 1)) {(T => ((!(fresh1 < e_t) \
    => (x == 3)) && ((fresh1 < e_t) => T)))}\n\
    Less: {(T => ((!(x < (1 + (1 + 1))) => (x == 3)) && ((x < (1 + (1 + 1))) \
    => T)))} x {(T => ((!(e_t < (1 + (1 + 1))) => (x == 3)) && ((e_t < (1 + \
    (1 + 1))) => T)))}, {(T => ((!(fresh1 < (1 + (1 + 1))) => (x == 3)) && \
    ((fresh1 < (1 + (1 + 1))) => T)))} (1 + (1 + 1)) {(T => ((!(fresh1 < e_t) \
    => (x == 3)) && ((fresh1 < e_t) => T)))} -> {(T => ((!(x < (1 + (1 + 1))) \
    => (x == 3)) && ((x < (1 + (1 + 1))) => T)))} (x < (1 + (1 + 1))) {(T => \
    ((!b_t => (x == 3)) && (b_t => T)))}\n\
    FALSE!!!Weaken: {(T => ((!(x < (1 + (1 + 1))) => (x == 3)) && ((x < (1 + \
    (1 + 1))) => T)))} (x < (1 + (1 + 1))) {(T => ((!b_t => (x == 3)) && (b_t \
    => T)))} -> {T} (x < (1 + (1 + 1))) {(T => ((!b_t => (x == 3)) && (b_t => \
    T)))}\n\
    Var: -> {T} x {T}\n\
    Int: -> {T} 1 {T}\n\
    Int: -> {T} 1 {T}\n\
    Plus: {T} 1 {T}, {T} 1 {T} -> {T} (1 + 1) {T}\n\
    Plus: {T} x {T}, {T} (1 + 1) {T} -> {T} (x + (1 + 1)) {T}\n\
    Assign: {T} (x + (1 + 1)) {T} -> {T} (x := (x + (1 + 1))) {T}\n\
    While: {T} (x < (1 + (1 + 1))) {(T => ((!b_t => (x == 3)) && (b_t => \
    T)))}, {T} (x := (x + (1 + 1))) {T} -> {T} (while (x < (1 + (1 + 1))) do \
    (Inv=T) (x := (x + (1 + 1)))) {(x == 3)}\n\
    Weaken: {T} (while (x < (1 + (1 + 1))) do (Inv=T) (x := (x + (1 + 1)))) \
    {(x == 3)} -> {(x < 4)} (while (x < (1 + (1 + 1))) do (Inv=T) (x := (x + \
    (1 + 1)))) {(x == 3)}";

  check_proof_no_hole_simple
    {
      pre =
        And
          ( less_int_term (ITVar (T "x"), Int 5),
            Exists
              ( IntTermVar (T "k"),
                eq_int_term (ITVar (T "x"), Plus (ITVar (T "k"), ITVar (T "k")))
              ) );
      prog =
        Stmt
          (While
            ( Less (Var "x", Plus (Int 1, Plus (Int 1, Int 1))),
              And
                ( less_int_term (ITVar (T "x"), Int 5),
                  Exists
                    ( IntTermVar (T "k"),
                      eq_int_term
                        (ITVar (T "x"), Plus (ITVar (T "k"), ITVar (T "k"))) )
                ),
              Assign ("x", Plus (Var "x", Plus (Int 1, Int 1))) ));
      post = eq_int_term (ITVar (T "x"), Int 4);
    }
    "Var: -> {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(x < (1 + (1 + \
    1))) => (x == 4)) && ((x < (1 + (1 + 1))) => (((x + (1 + 1)) < 5) && \
    ((Exists k). ((x + (1 + 1)) == (k + k)))))))} x {(((x < 5) && ((Exists \
    k). (x == (k + k)))) => ((!(e_t < (1 + (1 + 1))) => (x == 4)) && ((e_t < \
    (1 + (1 + 1))) => (((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == \
    (k + k)))))))}\n\
    Int: -> {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(fresh1 < (1 + \
    (1 + 1))) => (x == 4)) && ((fresh1 < (1 + (1 + 1))) => (((x + (1 + 1)) < \
    5) && ((Exists k). ((x + (1 + 1)) == (k + k)))))))} 1 {(((x < 5) && \
    ((Exists k). (x == (k + k)))) => ((!(fresh1 < (e_t + (1 + 1))) => (x == \
    4)) && ((fresh1 < (e_t + (1 + 1))) => (((x + (1 + 1)) < 5) && ((Exists \
    k). ((x + (1 + 1)) == (k + k)))))))}\n\
    Int: -> {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(fresh1 < \
    (fresh2 + (1 + 1))) => (x == 4)) && ((fresh1 < (fresh2 + (1 + 1))) => \
    (((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + k)))))))} 1 \
    {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(fresh1 < (fresh2 + \
    (e_t + 1))) => (x == 4)) && ((fresh1 < (fresh2 + (e_t + 1))) => (((x + (1 \
    + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + k)))))))}\n\
    Int: -> {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(fresh1 < \
    (fresh2 + (fresh3 + 1))) => (x == 4)) && ((fresh1 < (fresh2 + (fresh3 + \
    1))) => (((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + \
    k)))))))} 1 {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(fresh1 < \
    (fresh2 + (fresh3 + e_t))) => (x == 4)) && ((fresh1 < (fresh2 + (fresh3 + \
    e_t))) => (((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + \
    k)))))))}\n\
    Plus: {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(fresh1 < (fresh2 \
    + (1 + 1))) => (x == 4)) && ((fresh1 < (fresh2 + (1 + 1))) => (((x + (1 + \
    1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + k)))))))} 1 {(((x < 5) && \
    ((Exists k). (x == (k + k)))) => ((!(fresh1 < (fresh2 + (e_t + 1))) => (x \
    == 4)) && ((fresh1 < (fresh2 + (e_t + 1))) => (((x + (1 + 1)) < 5) && \
    ((Exists k). ((x + (1 + 1)) == (k + k)))))))}, {(((x < 5) && ((Exists k). \
    (x == (k + k)))) => ((!(fresh1 < (fresh2 + (fresh3 + 1))) => (x == 4)) && \
    ((fresh1 < (fresh2 + (fresh3 + 1))) => (((x + (1 + 1)) < 5) && ((Exists \
    k). ((x + (1 + 1)) == (k + k)))))))} 1 {(((x < 5) && ((Exists k). (x == \
    (k + k)))) => ((!(fresh1 < (fresh2 + (fresh3 + e_t))) => (x == 4)) && \
    ((fresh1 < (fresh2 + (fresh3 + e_t))) => (((x + (1 + 1)) < 5) && ((Exists \
    k). ((x + (1 + 1)) == (k + k)))))))} -> {(((x < 5) && ((Exists k). (x == \
    (k + k)))) => ((!(fresh1 < (fresh2 + (1 + 1))) => (x == 4)) && ((fresh1 < \
    (fresh2 + (1 + 1))) => (((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + \
    1)) == (k + k)))))))} (1 + 1) {(((x < 5) && ((Exists k). (x == (k + k)))) \
    => ((!(fresh1 < (fresh2 + e_t)) => (x == 4)) && ((fresh1 < (fresh2 + \
    e_t)) => (((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + \
    k)))))))}\n\
    Plus: {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(fresh1 < (1 + (1 \
    + 1))) => (x == 4)) && ((fresh1 < (1 + (1 + 1))) => (((x + (1 + 1)) < 5) \
    && ((Exists k). ((x + (1 + 1)) == (k + k)))))))} 1 {(((x < 5) && ((Exists \
    k). (x == (k + k)))) => ((!(fresh1 < (e_t + (1 + 1))) => (x == 4)) && \
    ((fresh1 < (e_t + (1 + 1))) => (((x + (1 + 1)) < 5) && ((Exists k). ((x + \
    (1 + 1)) == (k + k)))))))}, {(((x < 5) && ((Exists k). (x == (k + k)))) \
    => ((!(fresh1 < (fresh2 + (1 + 1))) => (x == 4)) && ((fresh1 < (fresh2 + \
    (1 + 1))) => (((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + \
    k)))))))} (1 + 1) {(((x < 5) && ((Exists k). (x == (k + k)))) => \
    ((!(fresh1 < (fresh2 + e_t)) => (x == 4)) && ((fresh1 < (fresh2 + e_t)) \
    => (((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + k)))))))} \
    -> {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(fresh1 < (1 + (1 + \
    1))) => (x == 4)) && ((fresh1 < (1 + (1 + 1))) => (((x + (1 + 1)) < 5) && \
    ((Exists k). ((x + (1 + 1)) == (k + k)))))))} (1 + (1 + 1)) {(((x < 5) && \
    ((Exists k). (x == (k + k)))) => ((!(fresh1 < e_t) => (x == 4)) && \
    ((fresh1 < e_t) => (((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == \
    (k + k)))))))}\n\
    Less: {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(x < (1 + (1 + \
    1))) => (x == 4)) && ((x < (1 + (1 + 1))) => (((x + (1 + 1)) < 5) && \
    ((Exists k). ((x + (1 + 1)) == (k + k)))))))} x {(((x < 5) && ((Exists \
    k). (x == (k + k)))) => ((!(e_t < (1 + (1 + 1))) => (x == 4)) && ((e_t < \
    (1 + (1 + 1))) => (((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == \
    (k + k)))))))}, {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(fresh1 \
    < (1 + (1 + 1))) => (x == 4)) && ((fresh1 < (1 + (1 + 1))) => (((x + (1 + \
    1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + k)))))))} (1 + (1 + 1)) \
    {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(fresh1 < e_t) => (x == \
    4)) && ((fresh1 < e_t) => (((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + \
    1)) == (k + k)))))))} -> {(((x < 5) && ((Exists k). (x == (k + k)))) => \
    ((!(x < (1 + (1 + 1))) => (x == 4)) && ((x < (1 + (1 + 1))) => (((x + (1 \
    + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + k)))))))} (x < (1 + (1 \
    + 1))) {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!b_t => (x == 4)) \
    && (b_t => (((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + \
    k)))))))}\n\
    Weaken: {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(x < (1 + (1 + \
    1))) => (x == 4)) && ((x < (1 + (1 + 1))) => (((x + (1 + 1)) < 5) && \
    ((Exists k). ((x + (1 + 1)) == (k + k)))))))} (x < (1 + (1 + 1))) {(((x < \
    5) && ((Exists k). (x == (k + k)))) => ((!b_t => (x == 4)) && (b_t => \
    (((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + k)))))))} -> \
    {T} (x < (1 + (1 + 1))) {(((x < 5) && ((Exists k). (x == (k + k)))) => \
    ((!b_t => (x == 4)) && (b_t => (((x + (1 + 1)) < 5) && ((Exists k). ((x + \
    (1 + 1)) == (k + k)))))))}\n\
    Var: -> {(((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + \
    k))))} x {(((e_t + (1 + 1)) < 5) && ((Exists k). ((e_t + (1 + 1)) == (k + \
    k))))}\n\
    Int: -> {(((fresh1 + (1 + 1)) < 5) && ((Exists k). ((fresh1 + (1 + 1)) == \
    (k + k))))} 1 {(((fresh1 + (e_t + 1)) < 5) && ((Exists k). ((fresh1 + \
    (e_t + 1)) == (k + k))))}\n\
    Int: -> {(((fresh1 + (fresh2 + 1)) < 5) && ((Exists k). ((fresh1 + \
    (fresh2 + 1)) == (k + k))))} 1 {(((fresh1 + (fresh2 + e_t)) < 5) && \
    ((Exists k). ((fresh1 + (fresh2 + e_t)) == (k + k))))}\n\
    Plus: {(((fresh1 + (1 + 1)) < 5) && ((Exists k). ((fresh1 + (1 + 1)) == \
    (k + k))))} 1 {(((fresh1 + (e_t + 1)) < 5) && ((Exists k). ((fresh1 + \
    (e_t + 1)) == (k + k))))}, {(((fresh1 + (fresh2 + 1)) < 5) && ((Exists \
    k). ((fresh1 + (fresh2 + 1)) == (k + k))))} 1 {(((fresh1 + (fresh2 + \
    e_t)) < 5) && ((Exists k). ((fresh1 + (fresh2 + e_t)) == (k + k))))} -> \
    {(((fresh1 + (1 + 1)) < 5) && ((Exists k). ((fresh1 + (1 + 1)) == (k + \
    k))))} (1 + 1) {(((fresh1 + e_t) < 5) && ((Exists k). ((fresh1 + e_t) == \
    (k + k))))}\n\
    Plus: {(((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + k))))} \
    x {(((e_t + (1 + 1)) < 5) && ((Exists k). ((e_t + (1 + 1)) == (k + \
    k))))}, {(((fresh1 + (1 + 1)) < 5) && ((Exists k). ((fresh1 + (1 + 1)) == \
    (k + k))))} (1 + 1) {(((fresh1 + e_t) < 5) && ((Exists k). ((fresh1 + \
    e_t) == (k + k))))} -> {(((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + \
    1)) == (k + k))))} (x + (1 + 1)) {((e_t < 5) && ((Exists k). (e_t == (k + \
    k))))}\n\
    Assign: {(((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + \
    k))))} (x + (1 + 1)) {((e_t < 5) && ((Exists k). (e_t == (k + k))))} -> \
    {(((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + k))))} (x := \
    (x + (1 + 1))) {((x < 5) && ((Exists k). (x == (k + k))))}\n\
    While: {T} (x < (1 + (1 + 1))) {(((x < 5) && ((Exists k). (x == (k + \
    k)))) => ((!b_t => (x == 4)) && (b_t => (((x + (1 + 1)) < 5) && ((Exists \
    k). ((x + (1 + 1)) == (k + k)))))))}, {(((x + (1 + 1)) < 5) && ((Exists \
    k). ((x + (1 + 1)) == (k + k))))} (x := (x + (1 + 1))) {((x < 5) && \
    ((Exists k). (x == (k + k))))} -> {((x < 5) && ((Exists k). (x == (k + \
    k))))} (while (x < (1 + (1 + 1))) do (Inv=((x < 5) && ((Exists k). (x == \
    (k + k))))) (x := (x + (1 + 1)))) {(x == 4)}\n\
    Weaken: {((x < 5) && ((Exists k). (x == (k + k))))} (while (x < (1 + (1 + \
    1))) do (Inv=((x < 5) && ((Exists k). (x == (k + k))))) (x := (x + (1 + \
    1)))) {(x == 4)} -> {((x < 5) && ((Exists k). (x == (k + k))))} (while (x \
    < (1 + (1 + 1))) do (Inv=((x < 5) && ((Exists k). (x == (k + k))))) (x := \
    (x + (1 + 1)))) {(x == 4)}"

let test_nonrec_nonterm =
  (* Expression *)
  check_proof_no_hole_simple
    {
      pre = True;
      prog =
        Numeric
          (NNTerm
            {
              name = "N";
              expansions = lazy [ Int 1; Plus (Int 1, Int 0) ];
              strongest = lazy None;
            });
      post = less_int_term (ITVar ET, Int 2);
    }
    "Int: -> {(1 < 2)} 1 {(e_t < 2)}\n\
    Int: -> {((1 + 0) < 2)} 1 {((e_t + 0) < 2)}\n\
    Int: -> {((fresh1 + 0) < 2)} 0 {((fresh1 + e_t) < 2)}\n\
    Plus: {((1 + 0) < 2)} 1 {((e_t + 0) < 2)}, {((fresh1 + 0) < 2)} 0 \
    {((fresh1 + e_t) < 2)} -> {((1 + 0) < 2)} (1 + 0) {(e_t < 2)}\n\
    GrmDisj: {(1 < 2)} 1 {(e_t < 2)}, {((1 + 0) < 2)} (1 + 0) {(e_t < 2)} -> \
    {((T && (1 < 2)) && ((1 + 0) < 2))} N {(e_t < 2)}\n\
    Weaken: {((T && (1 < 2)) && ((1 + 0) < 2))} N {(e_t < 2)} -> {T} N {(e_t \
    < 2)}";

  (* Boolean *)
  check_proof_no_hole_simple
    {
      pre = True;
      prog =
        Boolean
          (BNTerm
            {
              name = "B";
              expansions = lazy [ True; Equals (Numeric (Int 0), Numeric (Int 0)) ];
              strongest = lazy None;
            });
      post = BVar BT;
    }
    "True: -> {T} T {b_t}\n\
    Int: -> {(0 == 0)} 0 {(e_t == 0)}\n\
    Int: -> {(fresh1 == 0)} 0 {(fresh1 == e_t)}\n\
    Equals: {(0 == 0)} 0 {(e_t == 0)}, {(fresh1 == 0)} 0 {(fresh1 == e_t)} -> \
    {(0 == 0)} (0 = 0) {b_t}\n\
    GrmDisj: {T} T {b_t}, {(0 == 0)} (0 = 0) {b_t} -> {((T && T) && (0 == \
    0))} B {b_t}\n\
    Weaken: {((T && T) && (0 == 0))} B {b_t} -> {T} B {b_t}";

  (* Statement *)
  check_proof_no_hole_simple
    {
      pre = True;
      prog =
        Stmt
          (SNTerm
            {
              name = "S";
              expansions =
                lazy
                  [
                    Assign ("x", Int 1);
                    Seq (Assign ("x", Int 0), Assign ("x", Int 1));
                  ];
              strongest = lazy None;
            });
      post = eq_int_term (ITVar (T "x"), Int 1);
    }
    "Int: -> {(1 == 1)} 1 {(e_t == 1)}\n\
    Assign: {(1 == 1)} 1 {(e_t == 1)} -> {(1 == 1)} (x := 1) {(x == 1)}\n\
    Int: -> {(1 == 1)} 0 {(1 == 1)}\n\
    Assign: {(1 == 1)} 0 {(1 == 1)} -> {(1 == 1)} (x := 0) {(1 == 1)}\n\
    Int: -> {(1 == 1)} 1 {(e_t == 1)}\n\
    Assign: {(1 == 1)} 1 {(e_t == 1)} -> {(1 == 1)} (x := 1) {(x == 1)}\n\
    Seq: {(1 == 1)} (x := 0) {(1 == 1)}, {(1 == 1)} (x := 1) {(x == 1)} -> \
    {(1 == 1)} ((x := 0); (x := 1)) {(x == 1)}\n\
    GrmDisj: {(1 == 1)} (x := 1) {(x == 1)}, {(1 == 1)} ((x := 0); (x := 1)) \
    {(x == 1)} -> {((T && (1 == 1)) && (1 == 1))} S {(x == 1)}\n\
    Weaken: {((T && (1 == 1)) && (1 == 1))} S {(x == 1)} -> {T} S {(x == 1)}"

let test_rec_nonterm_no_hole =
  (* Expression *)
  let rec n =
    {
      name = "N";
      expansions = lazy [ Int 1; Plus (Int 1, NNTerm n) ];
      strongest =
        lazy
          (Some
            ( [
                (IntTermVar ET, IntTermVar (T "e_t_2"));
                (BoolVar BT, BoolVar (B "b_t_2"));
              ],
              less_int_term (Int 0, ITVar ET) ));
    }
  in
  check_proof_no_hole_simple
    {
      pre = True;
      prog = Term (Numeric (NNTerm n));
      post = less_int_term (Int 0, ITVar ET);
    }
    "Int: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < e_t)] \
    {(0 < e_t)}] |- {(0 < 1)} 1 {(0 < e_t)}\n\
    Int: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < e_t)] \
    {(0 < e_t)}] |- {((Forall fresh2). ((0 < fresh2) => (0 < (1 + fresh2))))} \
    1 {((Forall fresh2). ((0 < fresh2) => (0 < (e_t + fresh2))))}\n\
    ApplyHP: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < \
    e_t)] {(0 < e_t)}] |- {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N \
    MGF=(0 < e_t)] {(0 < e_t)}\n\
    Adapt: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < e_t)] \
    {(0 < e_t)}] |- {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < \
    e_t)] {(0 < e_t)} -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N \
    MGF=(0 < e_t)] {(0 < e_t)}] |- {((Forall fresh2). ((0 < fresh2) => (0 < \
    (fresh1 + fresh2))))} [N MGF=(0 < e_t)] {(0 < (fresh1 + e_t))}\n\
    Plus: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < e_t)] {(0 \
    < e_t)}] |- {((Forall fresh2). ((0 < fresh2) => (0 < (1 + fresh2))))} 1 \
    {((Forall fresh2). ((0 < fresh2) => (0 < (e_t + fresh2))))}, [{((T && \
    (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < e_t)] {(0 < e_t)}] |- \
    {((Forall fresh2). ((0 < fresh2) => (0 < (fresh1 + fresh2))))} [N MGF=(0 \
    < e_t)] {(0 < (fresh1 + e_t))} -> [{((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [N MGF=(0 < e_t)] {(0 < e_t)}] |- {((Forall fresh2). ((0 < \
    fresh2) => (0 < (1 + fresh2))))} (1 + [N MGF=(0 < e_t)]) {(0 < e_t)}\n\
    HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < e_t)] {(0 < \
    e_t)}] |- {(0 < 1)} 1 {(0 < e_t)}, [{((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [N MGF=(0 < e_t)] {(0 < e_t)}] |- {((Forall fresh2). ((0 < \
    fresh2) => (0 < (1 + fresh2))))} (1 + [N MGF=(0 < e_t)]) {(0 < e_t)} -> \
    {((T && (0 < 1)) && ((Forall fresh2). ((0 < fresh2) => (0 < (1 + \
    fresh2)))))} [N MGF=(0 < e_t)] {(0 < e_t)}\n\
    Weaken: {((T && (0 < 1)) && ((Forall fresh2). ((0 < fresh2) => (0 < (1 + \
    fresh2)))))} [N MGF=(0 < e_t)] {(0 < e_t)} -> {((T && (e_t == e_t_2)) && \
    (b_t <-> b_t_2))} [N MGF=(0 < e_t)] {(0 < e_t)}\n\
    Adapt: {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < e_t)] {(0 \
    < e_t)} -> {((Forall fresh1). ((0 < fresh1) => (0 < fresh1)))} [N MGF=(0 \
    < e_t)] {(0 < e_t)}\n\
    Weaken: {((Forall fresh1). ((0 < fresh1) => (0 < fresh1)))} [N MGF=(0 < \
    e_t)] {(0 < e_t)} -> {T} [N MGF=(0 < e_t)] {(0 < e_t)}";

  (* Boolean *)
  let rec b =
    {
      name = "B";
      expansions =
        lazy [ Equals (Numeric (Var "x"), Numeric (Int 1)); Or (BNTerm b, Equals (Numeric (Var "x"), Numeric (Int 0))) ];
      strongest =
        lazy
          (Some
            ( [
                (IntTermVar ET, IntTermVar (T "e_t_2"));
                (BoolVar BT, BoolVar (B "b_t_2"));
              ],
              Implies (eq_int_term (ITVar (T "x"), Int 1), BVar BT) ));
    }
  in
  check_proof_no_hole_simple
    {
      pre = eq_int_term (ITVar (T "x"), Int 1);
      prog = Boolean (BNTerm b);
      post = BVar BT;
    }
    "Var: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
    b_t)] {((x == 1) => b_t)}] |- {((x == 1) => (x == 1))} x {((x == 1) => \
    (e_t == 1))}\n\
    Int: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
    b_t)] {((x == 1) => b_t)}] |- {((x == 1) => (fresh1 == 1))} 1 {((x == 1) \
    => (fresh1 == e_t))}\n\
    Equals: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
    b_t)] {((x == 1) => b_t)}] |- {((x == 1) => (x == 1))} x {((x == 1) => \
    (e_t == 1))}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == \
    1) => b_t)] {((x == 1) => b_t)}] |- {((x == 1) => (fresh1 == 1))} 1 {((x \
    == 1) => (fresh1 == e_t))} -> [{((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [B MGF=((x == 1) => b_t)] {((x == 1) => b_t)}] |- {((x == 1) => \
    (x == 1))} (x = 1) {((x == 1) => b_t)}\n\
    ApplyHP: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == \
    1) => b_t)] {((x == 1) => b_t)}] |- {((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [B MGF=((x == 1) => b_t)] {((x == 1) => b_t)}\n\
    Adapt: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
    b_t)] {((x == 1) => b_t)}] |- {((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [B MGF=((x == 1) => b_t)] {((x == 1) => b_t)} -> [{((T && (e_t \
    == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => b_t)] {((x == 1) => \
    b_t)}] |- {((Forall fresh2). (((x == 1) => fresh2) => ((x == 1) => \
    (fresh2 || (x == 0)))))} [B MGF=((x == 1) => b_t)] {((x == 1) => (b_t || \
    (x == 0)))}\n\
    Var: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
    b_t)] {((x == 1) => b_t)}] |- {((x == 1) => (fresh1 || (x == 0)))} x {((x \
    == 1) => (fresh1 || (e_t == 0)))}\n\
    Int: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
    b_t)] {((x == 1) => b_t)}] |- {((x == 1) => (fresh1 || (fresh2 == 0)))} 0 \
    {((x == 1) => (fresh1 || (fresh2 == e_t)))}\n\
    Equals: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
    b_t)] {((x == 1) => b_t)}] |- {((x == 1) => (fresh1 || (x == 0)))} x {((x \
    == 1) => (fresh1 || (e_t == 0)))}, [{((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [B MGF=((x == 1) => b_t)] {((x == 1) => b_t)}] |- {((x == 1) => \
    (fresh1 || (fresh2 == 0)))} 0 {((x == 1) => (fresh1 || (fresh2 == e_t)))} \
    -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
    b_t)] {((x == 1) => b_t)}] |- {((x == 1) => (fresh1 || (x == 0)))} (x = \
    0) {((x == 1) => (fresh1 || b_t))}\n\
    Or: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
    b_t)] {((x == 1) => b_t)}] |- {((Forall fresh2). (((x == 1) => fresh2) => \
    ((x == 1) => (fresh2 || (x == 0)))))} [B MGF=((x == 1) => b_t)] {((x == \
    1) => (b_t || (x == 0)))}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} \
    [B MGF=((x == 1) => b_t)] {((x == 1) => b_t)}] |- {((x == 1) => (fresh1 \
    || (x == 0)))} (x = 0) {((x == 1) => (fresh1 || b_t))} -> [{((T && (e_t \
    == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => b_t)] {((x == 1) => \
    b_t)}] |- {((Forall fresh2). (((x == 1) => fresh2) => ((x == 1) => \
    (fresh2 || (x == 0)))))} ([B MGF=((x == 1) => b_t)] || (x = 0)) {((x == \
    1) => b_t)}\n\
    HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
    b_t)] {((x == 1) => b_t)}] |- {((x == 1) => (x == 1))} (x = 1) {((x == 1) \
    => b_t)}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) \
    => b_t)] {((x == 1) => b_t)}] |- {((Forall fresh2). (((x == 1) => fresh2) \
    => ((x == 1) => (fresh2 || (x == 0)))))} ([B MGF=((x == 1) => b_t)] || (x \
    = 0)) {((x == 1) => b_t)} -> {((T && ((x == 1) => (x == 1))) && ((Forall \
    fresh2). (((x == 1) => fresh2) => ((x == 1) => (fresh2 || (x == 0))))))} \
    [B MGF=((x == 1) => b_t)] {((x == 1) => b_t)}\n\
    Weaken: {((T && ((x == 1) => (x == 1))) && ((Forall fresh2). (((x == 1) \
    => fresh2) => ((x == 1) => (fresh2 || (x == 0))))))} [B MGF=((x == 1) => \
    b_t)] {((x == 1) => b_t)} -> {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} \
    [B MGF=((x == 1) => b_t)] {((x == 1) => b_t)}\n\
    Adapt: {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
    b_t)] {((x == 1) => b_t)} -> {((Forall fresh2). (((x == 1) => fresh2) => \
    fresh2))} [B MGF=((x == 1) => b_t)] {b_t}\n\
    Weaken: {((Forall fresh2). (((x == 1) => fresh2) => fresh2))} [B MGF=((x \
    == 1) => b_t)] {b_t} -> {(x == 1)} [B MGF=((x == 1) => b_t)] {b_t}";

  (* Statement + Numeric *)
  (* This proof I have not yet hand-checked. *)
  let rec n =
    {
      name = "N";
      expansions = lazy [ Int 1; Plus (Int 0, NNTerm n) ];
      strongest =
        lazy
          (Some
            ( [
                (IntTermVar ET, IntTermVar (T "e_t_2"));
                (BoolVar BT, BoolVar (B "b_t_2"));
              ],
              eq_int_term (Int 1, ITVar ET) ));
    }
  and s =
    {
      name = "S";
      expansions =
        lazy
          [
            Assign ("x", NNTerm n);
            Seq (SNTerm s, Assign ("x", Plus (Var "x", NNTerm n)));
          ];
      strongest =
        lazy
          (Some
            ( [
                (IntTermVar ET, IntTermVar (T "e_t_2"));
                (BoolVar BT, BoolVar (B "b_t_2"));
                (IntTermVar (T "x"), IntTermVar (T "x_2"));
              ],
              less_int_term (Int 0, ITVar (T "x")) ));
    }
  in
  check_proof_no_hole_simple
    {
      pre = eq_int_term (ITVar (T "x"), Int 1);
      prog = Stmt (SNTerm s);
      post = less_int_term (Int (-1), ITVar (T "x"));
    }
    "Int: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] \
    {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {(1 == 1)} 1 {(1 == e_t)}\n\
    Int: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] \
    {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((1 == fresh2) => \
    (1 == (0 + fresh2))))} 0 {((Forall fresh2). ((1 == fresh2) => (1 == (e_t \
    + fresh2))))}\n\
    ApplyHP: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == \
    e_t)] {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [N MGF=(1 == e_t)] {(1 == e_t)}\n\
    Adapt: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] \
    {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [N MGF=(1 == e_t)] {(1 == e_t)} -> [{((T && (e_t == e_t_2)) && \
    (b_t <-> b_t_2))} [N MGF=(1 == e_t)] {(1 == e_t)}, {(((T && (e_t == \
    e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- \
    {((Forall fresh2). ((1 == fresh2) => (1 == (fresh1 + fresh2))))} [N \
    MGF=(1 == e_t)] {(1 == (fresh1 + e_t))}\n\
    Plus: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] \
    {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((1 == fresh2) => \
    (1 == (0 + fresh2))))} 0 {((Forall fresh2). ((1 == fresh2) => (1 == (e_t \
    + fresh2))))}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == \
    e_t)] {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((1 == fresh2) => \
    (1 == (fresh1 + fresh2))))} [N MGF=(1 == e_t)] {(1 == (fresh1 + e_t))} -> \
    [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] {(1 == \
    e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((1 == fresh2) => (1 == (0 \
    + fresh2))))} (0 + [N MGF=(1 == e_t)]) {(1 == e_t)}\n\
    HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] {(1 \
    == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=(0 < x)] {(0 < x)}] |- {(1 == 1)} 1 {(1 == e_t)}, [{((T && (e_t == \
    e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] {(1 == e_t)}, {(((T && \
    (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < \
    x)}] |- {((Forall fresh2). ((1 == fresh2) => (1 == (0 + fresh2))))} (0 + \
    [N MGF=(1 == e_t)]) {(1 == e_t)} -> [{(((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((T && (1 == 1)) \
    && ((Forall fresh2). ((1 == fresh2) => (1 == (0 + fresh2)))))} [N MGF=(1 \
    == e_t)] {(1 == e_t)}\n\
    Weaken: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=(0 < x)] {(0 < x)}] |- {((T && (1 == 1)) && ((Forall fresh2). ((1 == \
    fresh2) => (1 == (0 + fresh2)))))} [N MGF=(1 == e_t)] {(1 == e_t)} -> \
    [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < \
    x)] {(0 < x)}] |- {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 \
    == e_t)] {(1 == e_t)}\n\
    Adapt: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=(0 < x)] {(0 < x)}] |- {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} \
    [N MGF=(1 == e_t)] {(1 == e_t)} -> [{(((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh1). \
    ((1 == fresh1) => (0 < fresh1)))} [N MGF=(1 == e_t)] {(0 < e_t)}\n\
    Assign: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh1). ((1 == fresh1) => (0 < \
    fresh1)))} [N MGF=(1 == e_t)] {(0 < e_t)} -> [{(((T && (e_t == e_t_2)) && \
    (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall \
    fresh1). ((1 == fresh1) => (0 < fresh1)))} (x := [N MGF=(1 == e_t)]) {(0 \
    < x)}\n\
    ApplyHP: -> [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} \
    [S MGF=(0 < x)] {(0 < x)}] |- {(((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}\n\
    Adapt: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=(0 < x)] {(0 < x)}] |- {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) \
    && (x == x_2))} [S MGF=(0 < x)] {(0 < x)} -> [{(((T && (e_t == e_t_2)) && \
    (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall \
    fresh4). ((0 < fresh4) => ((Forall fresh2). ((1 == fresh2) => (0 < \
    (fresh4 + fresh2))))))} [S MGF=(0 < x)] {((Forall fresh2). ((1 == fresh2) \
    => (0 < (x + fresh2))))}\n\
    Var: -> [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((1 == fresh2) => (0 < (x + \
    fresh2))))} x {((Forall fresh2). ((1 == fresh2) => (0 < (e_t + fresh2))))}\n\
    Int: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] \
    {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {(1 == 1)} 1 {(1 == e_t)}\n\
    Int: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] \
    {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((1 == fresh2) => \
    (1 == (0 + fresh2))))} 0 {((Forall fresh2). ((1 == fresh2) => (1 == (e_t \
    + fresh2))))}\n\
    ApplyHP: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == \
    e_t)] {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [N MGF=(1 == e_t)] {(1 == e_t)}\n\
    Adapt: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] \
    {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [N MGF=(1 == e_t)] {(1 == e_t)} -> [{((T && (e_t == e_t_2)) && \
    (b_t <-> b_t_2))} [N MGF=(1 == e_t)] {(1 == e_t)}, {(((T && (e_t == \
    e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- \
    {((Forall fresh2). ((1 == fresh2) => (1 == (fresh1 + fresh2))))} [N \
    MGF=(1 == e_t)] {(1 == (fresh1 + e_t))}\n\
    Plus: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] \
    {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((1 == fresh2) => \
    (1 == (0 + fresh2))))} 0 {((Forall fresh2). ((1 == fresh2) => (1 == (e_t \
    + fresh2))))}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == \
    e_t)] {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((1 == fresh2) => \
    (1 == (fresh1 + fresh2))))} [N MGF=(1 == e_t)] {(1 == (fresh1 + e_t))} -> \
    [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] {(1 == \
    e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((1 == fresh2) => (1 == (0 \
    + fresh2))))} (0 + [N MGF=(1 == e_t)]) {(1 == e_t)}\n\
    HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] {(1 \
    == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=(0 < x)] {(0 < x)}] |- {(1 == 1)} 1 {(1 == e_t)}, [{((T && (e_t == \
    e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] {(1 == e_t)}, {(((T && \
    (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < \
    x)}] |- {((Forall fresh2). ((1 == fresh2) => (1 == (0 + fresh2))))} (0 + \
    [N MGF=(1 == e_t)]) {(1 == e_t)} -> [{(((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((T && (1 == 1)) \
    && ((Forall fresh2). ((1 == fresh2) => (1 == (0 + fresh2)))))} [N MGF=(1 \
    == e_t)] {(1 == e_t)}\n\
    Weaken: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=(0 < x)] {(0 < x)}] |- {((T && (1 == 1)) && ((Forall fresh2). ((1 == \
    fresh2) => (1 == (0 + fresh2)))))} [N MGF=(1 == e_t)] {(1 == e_t)} -> \
    [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < \
    x)] {(0 < x)}] |- {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 \
    == e_t)] {(1 == e_t)}\n\
    Adapt: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=(0 < x)] {(0 < x)}] |- {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} \
    [N MGF=(1 == e_t)] {(1 == e_t)} -> [{(((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). \
    ((1 == fresh2) => (0 < (fresh1 + fresh2))))} [N MGF=(1 == e_t)] {(0 < \
    (fresh1 + e_t))}\n\
    Plus: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((1 == fresh2) => (0 < (x + \
    fresh2))))} x {((Forall fresh2). ((1 == fresh2) => (0 < (e_t + \
    fresh2))))}, [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((1 == fresh2) => \
    (0 < (fresh1 + fresh2))))} [N MGF=(1 == e_t)] {(0 < (fresh1 + e_t))} -> \
    [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < \
    x)] {(0 < x)}] |- {((Forall fresh2). ((1 == fresh2) => (0 < (x + \
    fresh2))))} (x + [N MGF=(1 == e_t)]) {(0 < e_t)}\n\
    Assign: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((1 == fresh2) => (0 < (x + \
    fresh2))))} (x + [N MGF=(1 == e_t)]) {(0 < e_t)} -> [{(((T && (e_t == \
    e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- \
    {((Forall fresh2). ((1 == fresh2) => (0 < (x + fresh2))))} (x := (x + [N \
    MGF=(1 == e_t)])) {(0 < x)}\n\
    Seq: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh4). ((0 < fresh4) => ((Forall \
    fresh2). ((1 == fresh2) => (0 < (fresh4 + fresh2))))))} [S MGF=(0 < x)] \
    {((Forall fresh2). ((1 == fresh2) => (0 < (x + fresh2))))}, [{(((T && \
    (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < \
    x)}] |- {((Forall fresh2). ((1 == fresh2) => (0 < (x + fresh2))))} (x := \
    (x + [N MGF=(1 == e_t)])) {(0 < x)} -> [{(((T && (e_t == e_t_2)) && (b_t \
    <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall \
    fresh4). ((0 < fresh4) => ((Forall fresh2). ((1 == fresh2) => (0 < \
    (fresh4 + fresh2))))))} ([S MGF=(0 < x)]; (x := (x + [N MGF=(1 == \
    e_t)]))) {(0 < x)}\n\
    HP: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh1). ((1 == fresh1) => (0 < \
    fresh1)))} (x := [N MGF=(1 == e_t)]) {(0 < x)}, [{(((T && (e_t == e_t_2)) \
    && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- \
    {((Forall fresh4). ((0 < fresh4) => ((Forall fresh2). ((1 == fresh2) => \
    (0 < (fresh4 + fresh2))))))} ([S MGF=(0 < x)]; (x := (x + [N MGF=(1 == \
    e_t)]))) {(0 < x)} -> {((T && ((Forall fresh1). ((1 == fresh1) => (0 < \
    fresh1)))) && ((Forall fresh4). ((0 < fresh4) => ((Forall fresh2). ((1 == \
    fresh2) => (0 < (fresh4 + fresh2)))))))} [S MGF=(0 < x)] {(0 < x)}\n\
    Weaken: {((T && ((Forall fresh1). ((1 == fresh1) => (0 < fresh1)))) && \
    ((Forall fresh4). ((0 < fresh4) => ((Forall fresh2). ((1 == fresh2) => (0 \
    < (fresh4 + fresh2)))))))} [S MGF=(0 < x)] {(0 < x)} -> {(((T && (e_t == \
    e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}\n\
    Adapt: {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=(0 < x)] {(0 < x)} -> {((Forall fresh3). ((0 < fresh3) => (-1 < \
    fresh3)))} [S MGF=(0 < x)] {(-1 < x)}\n\
    Weaken: {((Forall fresh3). ((0 < fresh3) => (-1 < fresh3)))} [S MGF=(0 < \
    x)] {(-1 < x)} -> {(x == 1)} [S MGF=(0 < x)] {(-1 < x)}"

let test_rec_nonterm_with_hole =
  (* One Boolean Hole *)
  let rec b =
    {
      name = "B";
      expansions =
        lazy [ Equals (Numeric (Var "x"), Numeric (Int 1)); Or (BNTerm b, Equals (Numeric (Var "x"), Numeric (Int 0))) ];
      strongest =
        lazy
          (Some
            ( [
                (IntTermVar ET, IntTermVar (T "e_t_2"));
                (BoolVar BT, BoolVar (B "b_t_2"));
              ],
              BHole
                ("hole", [ Boolean (BVar BT); Term (ITerm (ITVar (T "x"))) ])
            ));
    }
  in
  check_proof_with_hole_simple
    {
      pre = eq_int_term (ITVar (T "x"), Int 1);
      prog = Boolean (BNTerm b);
      post = BVar BT;
    }
    "Var: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
    || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (x == 1))} x {(!(1 == x) \
    || (e_t == 1))}\n\
    Int: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
    || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (fresh1 == 1))} 1 {(!(1 \
    == x) || (fresh1 == e_t))}\n\
    Equals: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
    || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (x == 1))} x {(!(1 == x) \
    || (e_t == 1))}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
    MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (fresh1 \
    == 1))} 1 {(!(1 == x) || (fresh1 == e_t))} -> [{((T && (e_t == e_t_2)) && \
    (b_t <-> b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)}] |- \
    {(!(1 == x) || (x == 1))} (x = 1) {(!(1 == x) || b_t)}\n\
    ApplyHP: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == \
    x) || b_t)] {(!(1 == x) || b_t)}] |- {((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)}\n\
    Adapt: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || \
    b_t)] {(!(1 == x) || b_t)}] |- {((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)} -> [{((T && (e_t \
    == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || \
    b_t)}] |- {((Forall fresh2). ((!(1 == x) || fresh2) => (!(1 == x) || \
    (fresh2 || (x == 0)))))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || (b_t \
    || (x == 0)))}\n\
    Var: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
    || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (fresh1 || (x == 0)))} x \
    {(!(1 == x) || (fresh1 || (e_t == 0)))}\n\
    Int: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
    || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (fresh1 || (fresh2 == \
    0)))} 0 {(!(1 == x) || (fresh1 || (fresh2 == e_t)))}\n\
    Equals: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
    || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (fresh1 || (x == 0)))} x \
    {(!(1 == x) || (fresh1 || (e_t == 0)))}, [{((T && (e_t == e_t_2)) && (b_t \
    <-> b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == \
    x) || (fresh1 || (fresh2 == 0)))} 0 {(!(1 == x) || (fresh1 || (fresh2 == \
    e_t)))} -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == \
    x) || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (fresh1 || (x == \
    0)))} (x = 0) {(!(1 == x) || (fresh1 || b_t))}\n\
    Or: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || \
    b_t)] {(!(1 == x) || b_t)}] |- {((Forall fresh2). ((!(1 == x) || fresh2) \
    => (!(1 == x) || (fresh2 || (x == 0)))))} [B MGF=(!(1 == x) || b_t)] \
    {(!(1 == x) || (b_t || (x == 0)))}, [{((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) \
    || (fresh1 || (x == 0)))} (x = 0) {(!(1 == x) || (fresh1 || b_t))} -> \
    [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || b_t)] \
    {(!(1 == x) || b_t)}] |- {((Forall fresh2). ((!(1 == x) || fresh2) => \
    (!(1 == x) || (fresh2 || (x == 0)))))} ([B MGF=(hole (b_t, x))] || (x = \
    0)) {(!(1 == x) || b_t)}\n\
    HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || \
    b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (x == 1))} (x = 1) {(!(1 == \
    x) || b_t)}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == \
    x) || b_t)] {(!(1 == x) || b_t)}] |- {((Forall fresh2). ((!(1 == x) || \
    fresh2) => (!(1 == x) || (fresh2 || (x == 0)))))} ([B MGF=(hole (b_t, \
    x))] || (x = 0)) {(!(1 == x) || b_t)} -> {((T && (!(1 == x) || (x == 1))) \
    && ((Forall fresh2). ((!(1 == x) || fresh2) => (!(1 == x) || (fresh2 || \
    (x == 0))))))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)}\n\
    Weaken: {((T && (!(1 == x) || (x == 1))) && ((Forall fresh2). ((!(1 == x) \
    || fresh2) => (!(1 == x) || (fresh2 || (x == 0))))))} [B MGF=(!(1 == x) \
    || b_t)] {(!(1 == x) || b_t)} -> {((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)}\n\
    Adapt: {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || \
    b_t)] {(!(1 == x) || b_t)} -> {((Forall fresh2). ((!(1 == x) || fresh2) \
    => fresh2))} [B MGF=(!(1 == x) || b_t)] {b_t}\n\
    Weaken: {((Forall fresh2). ((!(1 == x) || fresh2) => fresh2))} [B \
    MGF=(!(1 == x) || b_t)] {b_t} -> {(x == 1)} [B MGF=(!(1 == x) || b_t)] \
    {b_t}";

  (* "(define-fun hole ((a_1 Bool) (a_2 Int)) Bool (or (not (= 1 a_2)) a_1))" *)

  (* Statement + Numeric *)
  (* This proof I have not yet hand-checked. *)
  let rec n =
    {
      name = "N";
      expansions = lazy [ Int 1; Plus (Int 0, NNTerm n) ];
      strongest =
        lazy
          (Some
            ( [
                (IntTermVar ET, IntTermVar (T "e_t_2"));
                (BoolVar BT, BoolVar (B "b_t_2"));
              ],
              BHole ("n_hole", [ Term (ITerm (ITVar ET)) ]) ));
    }
  and s =
    {
      name = "S";
      expansions =
        lazy
          [
            Assign ("x", NNTerm n);
            Seq (SNTerm s, Assign ("x", Plus (Var "x", NNTerm n)));
          ];
      strongest =
        lazy
          (Some
            ( [
                (IntTermVar ET, IntTermVar (T "e_t_2"));
                (BoolVar BT, BoolVar (B "b_t_2"));
                (IntTermVar (T "x"), IntTermVar (T "x_2"));
              ],
              BHole ("s_hole", [ Term (ITerm (ITVar (T "x"))) ]) ));
    }
  in
  check_proof_with_hole_simple
    {
      pre = eq_int_term (ITVar (T "x"), Int 1);
      prog = Stmt (SNTerm s);
      post = less_int_term (Int (-1), ITVar (T "x"));
    }
    "Int: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
    {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {(1 == \
    1)} 1 {(e_t == 1)}\n\
    Int: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
    {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- \
    {((Forall fresh2). ((fresh2 == 1) => ((0 + fresh2) == 1)))} 0 {((Forall \
    fresh2). ((fresh2 == 1) => ((e_t + fresh2) == 1)))}\n\
    ApplyHP: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == \
    1)] {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((T && \
    (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] {(e_t == 1)}\n\
    Adapt: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
    {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((T && \
    (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] {(e_t == 1)} -> \
    [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] {(e_t == \
    1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). \
    ((fresh2 == 1) => ((fresh1 + fresh2) == 1)))} [N MGF=(e_t == 1)] \
    {((fresh1 + e_t) == 1)}\n\
    Plus: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
    {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- \
    {((Forall fresh2). ((fresh2 == 1) => ((0 + fresh2) == 1)))} 0 {((Forall \
    fresh2). ((fresh2 == 1) => ((e_t + fresh2) == 1)))}, [{((T && (e_t == \
    e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] {(e_t == 1)}, {(((T && \
    (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 \
    == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). ((fresh2 == 1) => \
    ((fresh1 + fresh2) == 1)))} [N MGF=(e_t == 1)] {((fresh1 + e_t) == 1)} -> \
    [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] {(e_t == \
    1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). \
    ((fresh2 == 1) => ((0 + fresh2) == 1)))} (0 + [N MGF=(n_hole (e_t))]) \
    {(e_t == 1)}\n\
    HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
    {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {(1 == \
    1)} 1 {(e_t == 1)}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N \
    MGF=(e_t == 1)] {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == \
    x))}] |- {((Forall fresh2). ((fresh2 == 1) => ((0 + fresh2) == 1)))} (0 + \
    [N MGF=(n_hole (e_t))]) {(e_t == 1)} -> [{(((T && (e_t == e_t_2)) && (b_t \
    <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 \
    == x))}] |- {((T && (1 == 1)) && ((Forall fresh2). ((fresh2 == 1) => ((0 \
    + fresh2) == 1))))} [N MGF=(e_t == 1)] {(e_t == 1)}\n\
    Weaken: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((T && (1 == 1)) \
    && ((Forall fresh2). ((fresh2 == 1) => ((0 + fresh2) == 1))))} [N \
    MGF=(e_t == 1)] {(e_t == 1)} -> [{(((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == \
    x))}] |- {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
    {(e_t == 1)}\n\
    Adapt: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((T && (e_t == \
    e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] {(e_t == 1)} -> [{(((T && \
    (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 \
    == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh1). ((fresh1 == 1) => \
    ((0 < fresh1) || (0 == fresh1))))} [N MGF=(e_t == 1)] {((0 < e_t) || (0 \
    == e_t))}\n\
    Assign: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh1). \
    ((fresh1 == 1) => ((0 < fresh1) || (0 == fresh1))))} [N MGF=(e_t == 1)] \
    {((0 < e_t) || (0 == e_t))} -> [{(((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == \
    x))}] |- {((Forall fresh1). ((fresh1 == 1) => ((0 < fresh1) || (0 == \
    fresh1))))} (x := [N MGF=(n_hole (e_t))]) {((0 < x) || (0 == x))}\n\
    ApplyHP: -> [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} \
    [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {(((T && (e_t \
    == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == \
    x))] {((0 < x) || (0 == x))}\n\
    Adapt: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {(((T && (e_t == \
    e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] \
    {((0 < x) || (0 == x))} -> [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) \
    && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- \
    {((Forall fresh4). (((0 < fresh4) || (0 == fresh4)) => ((Forall fresh2). \
    ((fresh2 == 1) => ((0 < (fresh4 + fresh2)) || (0 == (fresh4 + \
    fresh2)))))))} [S MGF=((0 < x) || (0 == x))] {((Forall fresh2). ((fresh2 \
    == 1) => ((0 < (x + fresh2)) || (0 == (x + fresh2)))))}\n\
    Var: -> [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). \
    ((fresh2 == 1) => ((0 < (x + fresh2)) || (0 == (x + fresh2)))))} x \
    {((Forall fresh2). ((fresh2 == 1) => ((0 < (e_t + fresh2)) || (0 == (e_t \
    + fresh2)))))}\n\
    Int: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
    {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {(1 == \
    1)} 1 {(e_t == 1)}\n\
    Int: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
    {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- \
    {((Forall fresh2). ((fresh2 == 1) => ((0 + fresh2) == 1)))} 0 {((Forall \
    fresh2). ((fresh2 == 1) => ((e_t + fresh2) == 1)))}\n\
    ApplyHP: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == \
    1)] {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((T && \
    (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] {(e_t == 1)}\n\
    Adapt: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
    {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((T && \
    (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] {(e_t == 1)} -> \
    [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] {(e_t == \
    1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). \
    ((fresh2 == 1) => ((fresh1 + fresh2) == 1)))} [N MGF=(e_t == 1)] \
    {((fresh1 + e_t) == 1)}\n\
    Plus: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
    {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- \
    {((Forall fresh2). ((fresh2 == 1) => ((0 + fresh2) == 1)))} 0 {((Forall \
    fresh2). ((fresh2 == 1) => ((e_t + fresh2) == 1)))}, [{((T && (e_t == \
    e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] {(e_t == 1)}, {(((T && \
    (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 \
    == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). ((fresh2 == 1) => \
    ((fresh1 + fresh2) == 1)))} [N MGF=(e_t == 1)] {((fresh1 + e_t) == 1)} -> \
    [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] {(e_t == \
    1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). \
    ((fresh2 == 1) => ((0 + fresh2) == 1)))} (0 + [N MGF=(n_hole (e_t))]) \
    {(e_t == 1)}\n\
    HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
    {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {(1 == \
    1)} 1 {(e_t == 1)}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N \
    MGF=(e_t == 1)] {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == \
    x))}] |- {((Forall fresh2). ((fresh2 == 1) => ((0 + fresh2) == 1)))} (0 + \
    [N MGF=(n_hole (e_t))]) {(e_t == 1)} -> [{(((T && (e_t == e_t_2)) && (b_t \
    <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 \
    == x))}] |- {((T && (1 == 1)) && ((Forall fresh2). ((fresh2 == 1) => ((0 \
    + fresh2) == 1))))} [N MGF=(e_t == 1)] {(e_t == 1)}\n\
    Weaken: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((T && (1 == 1)) \
    && ((Forall fresh2). ((fresh2 == 1) => ((0 + fresh2) == 1))))} [N \
    MGF=(e_t == 1)] {(e_t == 1)} -> [{(((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == \
    x))}] |- {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
    {(e_t == 1)}\n\
    Adapt: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((T && (e_t == \
    e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] {(e_t == 1)} -> [{(((T && \
    (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 \
    == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). ((fresh2 == 1) => \
    ((0 < (fresh1 + fresh2)) || (0 == (fresh1 + fresh2)))))} [N MGF=(e_t == \
    1)] {((0 < (fresh1 + e_t)) || (0 == (fresh1 + e_t)))}\n\
    Plus: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). \
    ((fresh2 == 1) => ((0 < (x + fresh2)) || (0 == (x + fresh2)))))} x \
    {((Forall fresh2). ((fresh2 == 1) => ((0 < (e_t + fresh2)) || (0 == (e_t \
    + fresh2)))))}, [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
    x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- \
    {((Forall fresh2). ((fresh2 == 1) => ((0 < (fresh1 + fresh2)) || (0 == \
    (fresh1 + fresh2)))))} [N MGF=(e_t == 1)] {((0 < (fresh1 + e_t)) || (0 == \
    (fresh1 + e_t)))} -> [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x \
    == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- \
    {((Forall fresh2). ((fresh2 == 1) => ((0 < (x + fresh2)) || (0 == (x + \
    fresh2)))))} (x + [N MGF=(n_hole (e_t))]) {((0 < e_t) || (0 == e_t))}\n\
    Assign: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). \
    ((fresh2 == 1) => ((0 < (x + fresh2)) || (0 == (x + fresh2)))))} (x + [N \
    MGF=(n_hole (e_t))]) {((0 < e_t) || (0 == e_t))} -> [{(((T && (e_t == \
    e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] \
    {((0 < x) || (0 == x))}] |- {((Forall fresh2). ((fresh2 == 1) => ((0 < (x \
    + fresh2)) || (0 == (x + fresh2)))))} (x := (x + [N MGF=(n_hole (e_t))])) \
    {((0 < x) || (0 == x))}\n\
    Seq: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh4). \
    (((0 < fresh4) || (0 == fresh4)) => ((Forall fresh2). ((fresh2 == 1) => \
    ((0 < (fresh4 + fresh2)) || (0 == (fresh4 + fresh2)))))))} [S MGF=((0 < \
    x) || (0 == x))] {((Forall fresh2). ((fresh2 == 1) => ((0 < (x + fresh2)) \
    || (0 == (x + fresh2)))))}, [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) \
    && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- \
    {((Forall fresh2). ((fresh2 == 1) => ((0 < (x + fresh2)) || (0 == (x + \
    fresh2)))))} (x := (x + [N MGF=(n_hole (e_t))])) {((0 < x) || (0 == x))} \
    -> [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh4). \
    (((0 < fresh4) || (0 == fresh4)) => ((Forall fresh2). ((fresh2 == 1) => \
    ((0 < (fresh4 + fresh2)) || (0 == (fresh4 + fresh2)))))))} ([S \
    MGF=(s_hole (x))]; (x := (x + [N MGF=(n_hole (e_t))]))) {((0 < x) || (0 \
    == x))}\n\
    HP: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh1). \
    ((fresh1 == 1) => ((0 < fresh1) || (0 == fresh1))))} (x := [N MGF=(n_hole \
    (e_t))]) {((0 < x) || (0 == x))}, [{(((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == \
    x))}] |- {((Forall fresh4). (((0 < fresh4) || (0 == fresh4)) => ((Forall \
    fresh2). ((fresh2 == 1) => ((0 < (fresh4 + fresh2)) || (0 == (fresh4 + \
    fresh2)))))))} ([S MGF=(s_hole (x))]; (x := (x + [N MGF=(n_hole \
    (e_t))]))) {((0 < x) || (0 == x))} -> {((T && ((Forall fresh1). ((fresh1 \
    == 1) => ((0 < fresh1) || (0 == fresh1))))) && ((Forall fresh4). (((0 < \
    fresh4) || (0 == fresh4)) => ((Forall fresh2). ((fresh2 == 1) => ((0 < \
    (fresh4 + fresh2)) || (0 == (fresh4 + fresh2))))))))} [S MGF=((0 < x) || \
    (0 == x))] {((0 < x) || (0 == x))}\n\
    Weaken: {((T && ((Forall fresh1). ((fresh1 == 1) => ((0 < fresh1) || (0 \
    == fresh1))))) && ((Forall fresh4). (((0 < fresh4) || (0 == fresh4)) => \
    ((Forall fresh2). ((fresh2 == 1) => ((0 < (fresh4 + fresh2)) || (0 == \
    (fresh4 + fresh2))))))))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 \
    == x))} -> {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} \
    [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}\n\
    Adapt: {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
    MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))} -> {((Forall fresh3). \
    (((0 < fresh3) || (0 == fresh3)) => (-1 < fresh3)))} [S MGF=((0 < x) || \
    (0 == x))] {(-1 < x)}\n\
    Weaken: {((Forall fresh3). (((0 < fresh3) || (0 == fresh3)) => (-1 < \
    fresh3)))} [S MGF=((0 < x) || (0 == x))] {(-1 < x)} -> {(x == 1)} [S \
    MGF=((0 < x) || (0 == x))] {(-1 < x)}"

let test_triple_parse =
  let a =
    Proofrules.ProofRule.trip_tostr
      (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
        (Lexing.from_string "[] {|true|} Stmt (:= x 0) {|false|}"))
  in
  if a <> "{T} (x := 0) {F}" then print_endline a else ();
  let a =
    Proofrules.ProofRule.trip_tostr
      (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
        (Lexing.from_string "[] {|true|} Bool (or (= x x) (< 1 0)) {|false|}"))
  in
  if a <> "{T} ((x = x) || (1 < 0)) {F}" then print_endline a else ();
  let a =
    Proofrules.ProofRule.trip_tostr
      (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
        (Lexing.from_string
            "[Int N : [1] : None] {|true|} Int (+ 0 1) {|false|}"))
  in
  if a <> "{T} (0 + 1) {F}" then print_endline a else ();

  check_proof_no_hole_simple
    (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
      (Lexing.from_string
          "[Int N : [1, (+ 1 0)] : None] {|true|} Int Nonterm N {|(< e_t 2)|}"))
    "Int: -> {(1 < 2)} 1 {(e_t < 2)}\n\
    Int: -> {((1 + 0) < 2)} 1 {((e_t + 0) < 2)}\n\
    Int: -> {((fresh1 + 0) < 2)} 0 {((fresh1 + e_t) < 2)}\n\
    Plus: {((1 + 0) < 2)} 1 {((e_t + 0) < 2)}, {((fresh1 + 0) < 2)} 0 \
    {((fresh1 + e_t) < 2)} -> {((1 + 0) < 2)} (1 + 0) {(e_t < 2)}\n\
    GrmDisj: {(1 < 2)} 1 {(e_t < 2)}, {((1 + 0) < 2)} (1 + 0) {(e_t < 2)} -> \
    {((T && (1 < 2)) && ((1 + 0) < 2))} N {(e_t < 2)}\n\
    Weaken: {((T && (1 < 2)) && ((1 + 0) < 2))} N {(e_t < 2)} -> {T} N {(e_t \
    < 2)}";

  check_proof_with_hole_simple
    (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
      (Lexing.from_string
          "[Bool B : [(= x 1), (or Nonterm B (= x 0))] : Some ([(Int e_t, Int \
          e_t_2) ; (Bool b_t, Bool b_t_2)] : (Hole : hole [Bool b_t, Int \
          x]))] {|(= x 1)|} Bool Nonterm B {|b_t|}"))
    "Var: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
    || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (x == 1))} x {(!(1 == x) \
    || (e_t == 1))}\n\
    Int: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
    || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (fresh1 == 1))} 1 {(!(1 \
    == x) || (fresh1 == e_t))}\n\
    Equals: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
    || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (x == 1))} x {(!(1 == x) \
    || (e_t == 1))}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
    MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (fresh1 \
    == 1))} 1 {(!(1 == x) || (fresh1 == e_t))} -> [{((T && (e_t == e_t_2)) && \
    (b_t <-> b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)}] |- \
    {(!(1 == x) || (x == 1))} (x = 1) {(!(1 == x) || b_t)}\n\
    ApplyHP: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == \
    x) || b_t)] {(!(1 == x) || b_t)}] |- {((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)}\n\
    Adapt: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || \
    b_t)] {(!(1 == x) || b_t)}] |- {((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)} -> [{((T && (e_t \
    == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || \
    b_t)}] |- {((Forall fresh2). ((!(1 == x) || fresh2) => (!(1 == x) || \
    (fresh2 || (x == 0)))))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || (b_t \
    || (x == 0)))}\n\
    Var: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
    || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (fresh1 || (x == 0)))} x \
    {(!(1 == x) || (fresh1 || (e_t == 0)))}\n\
    Int: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
    || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (fresh1 || (fresh2 == \
    0)))} 0 {(!(1 == x) || (fresh1 || (fresh2 == e_t)))}\n\
    Equals: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
    || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (fresh1 || (x == 0)))} x \
    {(!(1 == x) || (fresh1 || (e_t == 0)))}, [{((T && (e_t == e_t_2)) && (b_t \
    <-> b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == \
    x) || (fresh1 || (fresh2 == 0)))} 0 {(!(1 == x) || (fresh1 || (fresh2 == \
    e_t)))} -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == \
    x) || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (fresh1 || (x == \
    0)))} (x = 0) {(!(1 == x) || (fresh1 || b_t))}\n\
    Or: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || \
    b_t)] {(!(1 == x) || b_t)}] |- {((Forall fresh2). ((!(1 == x) || fresh2) \
    => (!(1 == x) || (fresh2 || (x == 0)))))} [B MGF=(!(1 == x) || b_t)] \
    {(!(1 == x) || (b_t || (x == 0)))}, [{((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) \
    || (fresh1 || (x == 0)))} (x = 0) {(!(1 == x) || (fresh1 || b_t))} -> \
    [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || b_t)] \
    {(!(1 == x) || b_t)}] |- {((Forall fresh2). ((!(1 == x) || fresh2) => \
    (!(1 == x) || (fresh2 || (x == 0)))))} ([B MGF=(hole (b_t, x))] || (x = \
    0)) {(!(1 == x) || b_t)}\n\
    HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || \
    b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (x == 1))} (x = 1) {(!(1 == \
    x) || b_t)}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == \
    x) || b_t)] {(!(1 == x) || b_t)}] |- {((Forall fresh2). ((!(1 == x) || \
    fresh2) => (!(1 == x) || (fresh2 || (x == 0)))))} ([B MGF=(hole (b_t, \
    x))] || (x = 0)) {(!(1 == x) || b_t)} -> {((T && (!(1 == x) || (x == 1))) \
    && ((Forall fresh2). ((!(1 == x) || fresh2) => (!(1 == x) || (fresh2 || \
    (x == 0))))))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)}\n\
    Weaken: {((T && (!(1 == x) || (x == 1))) && ((Forall fresh2). ((!(1 == x) \
    || fresh2) => (!(1 == x) || (fresh2 || (x == 0))))))} [B MGF=(!(1 == x) \
    || b_t)] {(!(1 == x) || b_t)} -> {((T && (e_t == e_t_2)) && (b_t <-> \
    b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)}\n\
    Adapt: {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || \
    b_t)] {(!(1 == x) || b_t)} -> {((Forall fresh2). ((!(1 == x) || fresh2) \
    => fresh2))} [B MGF=(!(1 == x) || b_t)] {b_t}\n\
    Weaken: {((Forall fresh2). ((!(1 == x) || fresh2) => fresh2))} [B \
    MGF=(!(1 == x) || b_t)] {b_t} -> {(x == 1)} [B MGF=(!(1 == x) || b_t)] \
    {b_t}";

  check_proof_no_hole_vector_state
    (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
      (Lexing.from_string
          "[] {|forall ((i Int)) true |} Stmt (:= x 0) {|forall ((i Int)) (= \
          x[i] 4)|}"))
    "Int: -> {((Forall i). (0 == 4))} 0 {((Forall i). (e_t[i] == 4))}\n\
    Assign: {((Forall i). (0 == 4))} 0 {((Forall i). (e_t[i] == 4))} -> \
    {((Forall i). (0 == 4))} (x := 0) {((Forall i). (x[i] == 4))}\n\
    FALSE!!!Weaken: {((Forall i). (0 == 4))} (x := 0) {((Forall i). (x[i] == \
    4))} -> {((Forall i). T)} (x := 0) {((Forall i). (x[i] == 4))}";

  check_proof_no_hole_vector_state
    (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
      (Lexing.from_string
          "[Bool B : [(= x 1), (or Nonterm B (= x 0))] : Some ([(AInt e_t, \
          AInt e_t_2) ; (ABool b_t, ABool b_t_2)] : forall ((i Int)) (or \
          b_t[i] (not (= 1 x[i]))))] {|forall ((i Int)) (= x[i] 1)|} Bool \
          Nonterm B {|forall ((i Int)) b_t[i]|}"))
    "Var: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] \
    {((Forall i). (b_t[i] || !(1 == x[i])))}] |- {((Forall i). ((x[i] == 1) \
    || !(1 == x[i])))} x {((Forall i). ((e_t[i] == 1) || !(1 == x[i])))}\n\
    Int: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] \
    {((Forall i). (b_t[i] || !(1 == x[i])))}] |- {((Forall i). ((fresh1[i] == \
    1) || !(1 == x[i])))} 1 {((Forall i). ((fresh1[i] == e_t[i]) || !(1 == \
    x[i])))}\n\
    Equals: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] \
    {((Forall i). (b_t[i] || !(1 == x[i])))}] |- {((Forall i). ((x[i] == 1) \
    || !(1 == x[i])))} x {((Forall i). ((e_t[i] == 1) || !(1 == x[i])))}, \
    [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] {((Forall i). \
    (b_t[i] || !(1 == x[i])))}] |- {((Forall i). ((fresh1[i] == 1) || !(1 == \
    x[i])))} 1 {((Forall i). ((fresh1[i] == e_t[i]) || !(1 == x[i])))} -> \
    [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] {((Forall i). \
    (b_t[i] || !(1 == x[i])))}] |- {((Forall i). ((x[i] == 1) || !(1 == \
    x[i])))} (x = 1) {((Forall i). (b_t[i] || !(1 == x[i])))}\n\
    ApplyHP: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] \
    {((Forall i). (b_t[i] || !(1 == x[i])))}] |- {((T && ((Forall i). (e_t[i] \
    == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall \
    i). (b_t[i] || !(1 == x[i])))] {((Forall i). (b_t[i] || !(1 == x[i])))}\n\
    Adapt: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] \
    {((Forall i). (b_t[i] || !(1 == x[i])))}] |- {((T && ((Forall i). (e_t[i] \
    == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall \
    i). (b_t[i] || !(1 == x[i])))] {((Forall i). (b_t[i] || !(1 == x[i])))} \
    -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] \
    <-> b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] {((Forall \
    i). (b_t[i] || !(1 == x[i])))}] |- {((Forall fresh2). (((Forall i). \
    (fresh2[i] || !(1 == x[i]))) => ((Forall i). ((fresh2[i] || (x[i] == 0)) \
    || !(1 == x[i])))))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] \
    {((Forall i). ((b_t[i] || (x[i] == 0)) || !(1 == x[i])))}\n\
    Var: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] \
    {((Forall i). (b_t[i] || !(1 == x[i])))}] |- {((Forall i). ((fresh1[i] || \
    (x[i] == 0)) || !(1 == x[i])))} x {((Forall i). ((fresh1[i] || (e_t[i] == \
    0)) || !(1 == x[i])))}\n\
    Int: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] \
    {((Forall i). (b_t[i] || !(1 == x[i])))}] |- {((Forall i). ((fresh1[i] || \
    (fresh2[i] == 0)) || !(1 == x[i])))} 0 {((Forall i). ((fresh1[i] || \
    (fresh2[i] == e_t[i])) || !(1 == x[i])))}\n\
    Equals: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] \
    {((Forall i). (b_t[i] || !(1 == x[i])))}] |- {((Forall i). ((fresh1[i] || \
    (x[i] == 0)) || !(1 == x[i])))} x {((Forall i). ((fresh1[i] || (e_t[i] == \
    0)) || !(1 == x[i])))}, [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 \
    == x[i])))] {((Forall i). (b_t[i] || !(1 == x[i])))}] |- {((Forall i). \
    ((fresh1[i] || (fresh2[i] == 0)) || !(1 == x[i])))} 0 {((Forall i). \
    ((fresh1[i] || (fresh2[i] == e_t[i])) || !(1 == x[i])))} -> [{((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] {((Forall i). \
    (b_t[i] || !(1 == x[i])))}] |- {((Forall i). ((fresh1[i] || (x[i] == 0)) \
    || !(1 == x[i])))} (x = 0) {((Forall i). ((fresh1[i] || b_t[i]) || !(1 == \
    x[i])))}\n\
    Or: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] \
    <-> b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] {((Forall \
    i). (b_t[i] || !(1 == x[i])))}] |- {((Forall fresh2). (((Forall i). \
    (fresh2[i] || !(1 == x[i]))) => ((Forall i). ((fresh2[i] || (x[i] == 0)) \
    || !(1 == x[i])))))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] \
    {((Forall i). ((b_t[i] || (x[i] == 0)) || !(1 == x[i])))}, [{((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] {((Forall i). \
    (b_t[i] || !(1 == x[i])))}] |- {((Forall i). ((fresh1[i] || (x[i] == 0)) \
    || !(1 == x[i])))} (x = 0) {((Forall i). ((fresh1[i] || b_t[i]) || !(1 == \
    x[i])))} -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] \
    {((Forall i). (b_t[i] || !(1 == x[i])))}] |- {((Forall fresh2). (((Forall \
    i). (fresh2[i] || !(1 == x[i]))) => ((Forall i). ((fresh2[i] || (x[i] == \
    0)) || !(1 == x[i])))))} ([B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] \
    || (x = 0)) {((Forall i). (b_t[i] || !(1 == x[i])))}\n\
    HP: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] \
    <-> b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] {((Forall \
    i). (b_t[i] || !(1 == x[i])))}] |- {((Forall i). ((x[i] == 1) || !(1 == \
    x[i])))} (x = 1) {((Forall i). (b_t[i] || !(1 == x[i])))}, [{((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] {((Forall i). \
    (b_t[i] || !(1 == x[i])))}] |- {((Forall fresh2). (((Forall i). \
    (fresh2[i] || !(1 == x[i]))) => ((Forall i). ((fresh2[i] || (x[i] == 0)) \
    || !(1 == x[i])))))} ([B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] || \
    (x = 0)) {((Forall i). (b_t[i] || !(1 == x[i])))} -> {((T && ((Forall i). \
    ((x[i] == 1) || !(1 == x[i])))) && ((Forall fresh2). (((Forall i). \
    (fresh2[i] || !(1 == x[i]))) => ((Forall i). ((fresh2[i] || (x[i] == 0)) \
    || !(1 == x[i]))))))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] \
    {((Forall i). (b_t[i] || !(1 == x[i])))}\n\
    Weaken: {((T && ((Forall i). ((x[i] == 1) || !(1 == x[i])))) && ((Forall \
    fresh2). (((Forall i). (fresh2[i] || !(1 == x[i]))) => ((Forall i). \
    ((fresh2[i] || (x[i] == 0)) || !(1 == x[i]))))))} [B MGF=((Forall i). \
    (b_t[i] || !(1 == x[i])))] {((Forall i). (b_t[i] || !(1 == x[i])))} -> \
    {((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] {((Forall i). \
    (b_t[i] || !(1 == x[i])))}\n\
    Adapt: {((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] \
    {((Forall i). (b_t[i] || !(1 == x[i])))} -> {((Forall fresh2). (((Forall \
    i). (fresh2[i] || !(1 == x[i]))) => ((Forall i). fresh2[i])))} [B \
    MGF=((Forall i). (b_t[i] || !(1 == x[i])))] {((Forall i). b_t[i])}\n\
    Weaken: {((Forall fresh2). (((Forall i). (fresh2[i] || !(1 == x[i]))) => \
    ((Forall i). fresh2[i])))} [B MGF=((Forall i). (b_t[i] || !(1 == x[i])))] \
    {((Forall i). b_t[i])} -> {((Forall i). (x[i] == 1))} [B MGF=((Forall i). \
    (b_t[i] || !(1 == x[i])))] {((Forall i). b_t[i])}"

let test_axiom_vector_states =
  check_proof_no_hole_vector_state
    { pre = False; prog = Term (Numeric (Int 1)); post = False }
    "Int: -> {F} 1 {F}\nWeaken: {F} 1 {F} -> {F} 1 {F}";
  check_proof_no_hole_vector_state
    {
      pre = True;
      prog = Term (Numeric (Int 0));
      post = eq_int_term (Int 0, AITVar (ITApp (ET, Int 1)));
    }
    "Int: -> {(0 == 0)} 0 {(0 == e_t[1])}\n\
    Weaken: {(0 == 0)} 0 {(0 == e_t[1])} -> {T} 0 {(0 == e_t[1])}";
  check_proof_no_hole_vector_state
    {
      pre = False;
      prog = Boolean False;
      post = Forall (IntTermVar (T "i"), ABVar (BApp (BT, ITVar (T "i"))));
    }
    "False: -> {((Forall i). F)} F {((Forall i). b_t[i])}\n\
    Weaken: {((Forall i). F)} F {((Forall i). b_t[i])} -> {F} F {((Forall i). \
    b_t[i])}";
  check_proof_no_hole_vector_state
    {
      pre = True;
      prog = Boolean True;
      post = Exists (IntTermVar (T "i"), ABVar (BApp (BT, ITVar (T "i"))));
    }
    "True: -> {((Exists i). T)} T {((Exists i). b_t[i])}\n\
    Weaken: {((Exists i). T)} T {((Exists i). b_t[i])} -> {T} T {((Exists i). \
    b_t[i])}"

let test_not_vector_states =
  check_proof_no_hole_vector_state
    {
      pre = True;
      prog = Boolean (Not False);
      post = Exists (IntTermVar (T "i"), ABVar (BApp (BT, ITVar (T "i"))));
    }
    "False: -> {((Exists i). !F)} F {((Exists i). !b_t[i])}\n\
    Not: {((Exists i). !F)} F {((Exists i). !b_t[i])} -> {((Exists i). !F)} \
    !F {((Exists i). b_t[i])}\n\
    Weaken: {((Exists i). !F)} !F {((Exists i). b_t[i])} -> {T} !F {((Exists \
    i). b_t[i])}"

let test_binary_vector_states =
  (* Plus *)
  check_proof_no_hole_vector_state
    {
      pre = Not True;
      prog = Term (Numeric (Plus (Int 1, Int 1)));
      post =
        Exists
          ( IntTermVar (T "i"),
            eq_int_term (AITVar (ITApp (ET, ITVar (T "i"))), Int 2) );
    }
    "Int: -> {((Exists i). ((1 + 1) == 2))} 1 {((Exists i). ((e_t[i] + 1) == \
    2))}\n\
    Int: -> {((Exists i). ((fresh1[i] + 1) == 2))} 1 {((Exists i). \
    ((fresh1[i] + e_t[i]) == 2))}\n\
    Plus: {((Exists i). ((1 + 1) == 2))} 1 {((Exists i). ((e_t[i] + 1) == \
    2))}, {((Exists i). ((fresh1[i] + 1) == 2))} 1 {((Exists i). ((fresh1[i] \
    + e_t[i]) == 2))} -> {((Exists i). ((1 + 1) == 2))} (1 + 1) {((Exists i). \
    (e_t[i] == 2))}\n\
    Weaken: {((Exists i). ((1 + 1) == 2))} (1 + 1) {((Exists i). (e_t[i] == \
    2))} -> {!T} (1 + 1) {((Exists i). (e_t[i] == 2))}";
  (* And *)
  check_proof_no_hole_vector_state
    {
      pre = And (True, And (True, False));
      prog = Boolean (And (True, And (True, False)));
      post = ABVar (BApp (BT, Int 0));
    }
    "True: -> {(T && (T && F))} T {(b_t[0] && (T && F))}\n\
    True: -> {(fresh1[0] && (T && F))} T {(fresh1[0] && (b_t[0] && F))}\n\
    False: -> {(fresh1[0] && (fresh2[0] && F))} F {(fresh1[0] && (fresh2[0] \
    && b_t[0]))}\n\
    And: {(fresh1[0] && (T && F))} T {(fresh1[0] && (b_t[0] && F))}, \
    {(fresh1[0] && (fresh2[0] && F))} F {(fresh1[0] && (fresh2[0] && \
    b_t[0]))} -> {(fresh1[0] && (T && F))} (T && F) {(fresh1[0] && b_t[0])}\n\
    And: {(T && (T && F))} T {(b_t[0] && (T && F))}, {(fresh1[0] && (T && \
    F))} (T && F) {(fresh1[0] && b_t[0])} -> {(T && (T && F))} (T && (T && \
    F)) {b_t[0]}\n\
    Weaken: {(T && (T && F))} (T && (T && F)) {b_t[0]} -> {(T && (T && F))} \
    (T && (T && F)) {b_t[0]}";
  (* Or *)
  check_proof_no_hole_vector_state
    {
      pre = True;
      prog = Boolean (And (True, Or (True, False)));
      post =
        Exists
          ( IntTermVar (T "i"),
            Exists
              ( IntTermVar (T "j"),
                Iff
                  ( ABVar (BApp (BT, ITVar (T "j"))),
                    ABVar (BApp (BT, ITVar (T "i"))) ) ) );
    }
    "True: -> {((Exists i). ((Exists j). ((T && (T || F)) <-> (T && (T || \
    F)))))} T {((Exists i). ((Exists j). ((b_t[j] && (T || F)) <-> (b_t[i] && \
    (T || F)))))}\n\
    True: -> {((Exists i). ((Exists j). ((fresh1[j] && (T || F)) <-> \
    (fresh1[i] && (T || F)))))} T {((Exists i). ((Exists j). ((fresh1[j] && \
    (b_t[j] || F)) <-> (fresh1[i] && (b_t[i] || F)))))}\n\
    False: -> {((Exists i). ((Exists j). ((fresh1[j] && (fresh2[j] || F)) <-> \
    (fresh1[i] && (fresh2[i] || F)))))} F {((Exists i). ((Exists j). \
    ((fresh1[j] && (fresh2[j] || b_t[j])) <-> (fresh1[i] && (fresh2[i] || \
    b_t[i])))))}\n\
    Or: {((Exists i). ((Exists j). ((fresh1[j] && (T || F)) <-> (fresh1[i] && \
    (T || F)))))} T {((Exists i). ((Exists j). ((fresh1[j] && (b_t[j] || F)) \
    <-> (fresh1[i] && (b_t[i] || F)))))}, {((Exists i). ((Exists j). \
    ((fresh1[j] && (fresh2[j] || F)) <-> (fresh1[i] && (fresh2[i] || F)))))} \
    F {((Exists i). ((Exists j). ((fresh1[j] && (fresh2[j] || b_t[j])) <-> \
    (fresh1[i] && (fresh2[i] || b_t[i])))))} -> {((Exists i). ((Exists j). \
    ((fresh1[j] && (T || F)) <-> (fresh1[i] && (T || F)))))} (T || F) \
    {((Exists i). ((Exists j). ((fresh1[j] && b_t[j]) <-> (fresh1[i] && \
    b_t[i]))))}\n\
    And: {((Exists i). ((Exists j). ((T && (T || F)) <-> (T && (T || F)))))} \
    T {((Exists i). ((Exists j). ((b_t[j] && (T || F)) <-> (b_t[i] && (T || \
    F)))))}, {((Exists i). ((Exists j). ((fresh1[j] && (T || F)) <-> \
    (fresh1[i] && (T || F)))))} (T || F) {((Exists i). ((Exists j). \
    ((fresh1[j] && b_t[j]) <-> (fresh1[i] && b_t[i]))))} -> {((Exists i). \
    ((Exists j). ((T && (T || F)) <-> (T && (T || F)))))} (T && (T || F)) \
    {((Exists i). ((Exists j). (b_t[j] <-> b_t[i])))}\n\
    Weaken: {((Exists i). ((Exists j). ((T && (T || F)) <-> (T && (T || \
    F)))))} (T && (T || F)) {((Exists i). ((Exists j). (b_t[j] <-> b_t[i])))} \
    -> {T} (T && (T || F)) {((Exists i). ((Exists j). (b_t[j] <-> b_t[i])))}";
  (* Equals *)
  check_proof_no_hole_vector_state
    {
      pre = eq_int_term (Int 0, AITVar (ITApp (T "x", Int 4)));
      prog = Boolean (Equals (Numeric (Int 0), Numeric (Var "x")));
      post = And (ABVar (BApp (BT, Int 0)), ABVar (BApp (BT, Int 12)));
    }
    "Int: -> {((0 == x[0]) && (0 == x[12]))} 0 {((e_t[0] == x[0]) && (e_t[12] \
    == x[12]))}\n\
    Var: -> {((fresh1[0] == x[0]) && (fresh1[12] == x[12]))} x {((fresh1[0] \
    == e_t[0]) && (fresh1[12] == e_t[12]))}\n\
    Equals: {((0 == x[0]) && (0 == x[12]))} 0 {((e_t[0] == x[0]) && (e_t[12] \
    == x[12]))}, {((fresh1[0] == x[0]) && (fresh1[12] == x[12]))} x \
    {((fresh1[0] == e_t[0]) && (fresh1[12] == e_t[12]))} -> {((0 == x[0]) && \
    (0 == x[12]))} (0 = x) {(b_t[0] && b_t[12])}\n\
    FALSE!!!Weaken: {((0 == x[0]) && (0 == x[12]))} (0 = x) {(b_t[0] && \
    b_t[12])} -> {(0 == x[4])} (0 = x) {(b_t[0] && b_t[12])}";
  (* Less *)
  check_proof_no_hole_vector_state
    {
      pre =
        Forall
          ( IntTermVar (T "j"),
            Not (less_int_term (Int 0, AITVar (ITApp (T "x", ITVar (T "j")))))
          );
      prog = Boolean (Less (Int 0, Var "x"));
      post = Or (ABVar (BApp (BT, Int 0)), Not (ABVar (BApp (BT, Int 12))));
    }
    "Int: -> {((0 < x[0]) || !(0 < x[12]))} 0 {((e_t[0] < x[0]) || !(e_t[12] < \
    x[12]))}\n\
    Var: -> {((fresh1[0] < x[0]) || !(fresh1[12] < x[12]))} x {((fresh1[0] < \
    e_t[0]) || !(fresh1[12] < e_t[12]))}\n\
    Less: {((0 < x[0]) || !(0 < x[12]))} 0 {((e_t[0] < x[0]) || !(e_t[12] < \
    x[12]))}, {((fresh1[0] < x[0]) || !(fresh1[12] < x[12]))} x {((fresh1[0] \
    < e_t[0]) || !(fresh1[12] < e_t[12]))} -> {((0 < x[0]) || !(0 < x[12]))} \
    (0 < x) {(b_t[0] || !b_t[12])}\n\
    Weaken: {((0 < x[0]) || !(0 < x[12]))} (0 < x) {(b_t[0] || !b_t[12])} -> \
    {((Forall j). !(0 < x[j]))} (0 < x) {(b_t[0] || !b_t[12])}"

let test_nonrec_nonterm_vector_state =
  (* Expression *)
  check_proof_no_hole_vector_state
    {
      pre = True;
      prog =
        Numeric
          (NNTerm
            {
              name = "N";
              expansions = lazy [ Int 1; Plus (Int 1, Int 0) ];
              strongest = lazy None;
            });
      post = less_int_term (AITVar (ITApp (ET, Int 4)), Int 2);
    }
    "Int: -> {(1 < 2)} 1 {(e_t[4] < 2)}\n\
    Int: -> {((1 + 0) < 2)} 1 {((e_t[4] + 0) < 2)}\n\
    Int: -> {((fresh1[4] + 0) < 2)} 0 {((fresh1[4] + e_t[4]) < 2)}\n\
    Plus: {((1 + 0) < 2)} 1 {((e_t[4] + 0) < 2)}, {((fresh1[4] + 0) < 2)} 0 \
    {((fresh1[4] + e_t[4]) < 2)} -> {((1 + 0) < 2)} (1 + 0) {(e_t[4] < 2)}\n\
    GrmDisj: {(1 < 2)} 1 {(e_t[4] < 2)}, {((1 + 0) < 2)} (1 + 0) {(e_t[4] < \
    2)} -> {((T && (1 < 2)) && ((1 + 0) < 2))} N {(e_t[4] < 2)}\n\
    Weaken: {((T && (1 < 2)) && ((1 + 0) < 2))} N {(e_t[4] < 2)} -> {T} N \
    {(e_t[4] < 2)}";

  (* Boolean *)
  check_proof_no_hole_vector_state
    {
      pre = True;
      prog =
        Boolean
          (BNTerm
            {
              name = "B";
              expansions = lazy [ True; Equals (Numeric (Int 0),Numeric (Int 0)) ];
              strongest = lazy None;
            });
      post = ABVar (BApp (BT, Int 6));
    }
    "True: -> {T} T {b_t[6]}\n\
    Int: -> {(0 == 0)} 0 {(e_t[6] == 0)}\n\
    Int: -> {(fresh1[6] == 0)} 0 {(fresh1[6] == e_t[6])}\n\
    Equals: {(0 == 0)} 0 {(e_t[6] == 0)}, {(fresh1[6] == 0)} 0 {(fresh1[6] == \
    e_t[6])} -> {(0 == 0)} (0 = 0) {b_t[6]}\n\
    GrmDisj: {T} T {b_t[6]}, {(0 == 0)} (0 = 0) {b_t[6]} -> {((T && T) && (0 \
    == 0))} B {b_t[6]}\n\
    Weaken: {((T && T) && (0 == 0))} B {b_t[6]} -> {T} B {b_t[6]}";

  (* Statement *)
  check_proof_no_hole_vector_state
    {
      pre = True;
      prog =
        Stmt
          (SNTerm
            {
              name = "S";
              expansions =
                lazy
                  [
                    Assign ("x", Int 1);
                    Seq (Assign ("x", Int 0), Assign ("x", Int 1));
                  ];
              strongest = lazy None;
            });
      post =
        Exists
          ( IntTermVar (T "i"),
            eq_int_term (AITVar (ITApp (T "x", ITVar (T "i"))), Int 1) );
    }
    "Int: -> {((Exists i). (1 == 1))} 1 {((Exists i). (e_t[i] == 1))}\n\
    Assign: {((Exists i). (1 == 1))} 1 {((Exists i). (e_t[i] == 1))} -> \
    {((Exists i). (1 == 1))} (x := 1) {((Exists i). (x[i] == 1))}\n\
    Int: -> {((Exists i). (1 == 1))} 0 {((Exists i). (1 == 1))}\n\
    Assign: {((Exists i). (1 == 1))} 0 {((Exists i). (1 == 1))} -> {((Exists \
    i). (1 == 1))} (x := 0) {((Exists i). (1 == 1))}\n\
    Int: -> {((Exists i). (1 == 1))} 1 {((Exists i). (e_t[i] == 1))}\n\
    Assign: {((Exists i). (1 == 1))} 1 {((Exists i). (e_t[i] == 1))} -> \
    {((Exists i). (1 == 1))} (x := 1) {((Exists i). (x[i] == 1))}\n\
    Seq: {((Exists i). (1 == 1))} (x := 0) {((Exists i). (1 == 1))}, \
    {((Exists i). (1 == 1))} (x := 1) {((Exists i). (x[i] == 1))} -> \
    {((Exists i). (1 == 1))} ((x := 0); (x := 1)) {((Exists i). (x[i] == 1))}\n\
    GrmDisj: {((Exists i). (1 == 1))} (x := 1) {((Exists i). (x[i] == 1))}, \
    {((Exists i). (1 == 1))} ((x := 0); (x := 1)) {((Exists i). (x[i] == 1))} \
    -> {((T && ((Exists i). (1 == 1))) && ((Exists i). (1 == 1)))} S \
    {((Exists i). (x[i] == 1))}\n\
    Weaken: {((T && ((Exists i). (1 == 1))) && ((Exists i). (1 == 1)))} S \
    {((Exists i). (x[i] == 1))} -> {T} S {((Exists i). (x[i] == 1))}"

let test_rec_nonterm_no_hole_vector_state =
  (* Expression *)
  let rec n =
    {
      name = "N";
      expansions = lazy [ Int 1; Plus (Int 1, NNTerm n) ];
      strongest =
        lazy
          (Some
            ( [
                (AIntTermVar ET, AIntTermVar (T "e_t_2"));
                (ABoolVar BT, ABoolVar (B "b_t_2"));
              ],
              less_int_term (Int 0, AITVar (ITApp (ET, Int 0))) ));
    }
  in
  check_proof_no_hole_vector_state
    {
      pre = True;
      prog = Term (Numeric (NNTerm n));
      post = less_int_term (Int 0, AITVar (ITApp (ET, Int 0)));
    }
    "Int: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=(0 < e_t[0])] {(0 < e_t[0])}] |- {(0 < \
    1)} 1 {(0 < e_t[0])}\n\
    Int: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=(0 < e_t[0])] {(0 < e_t[0])}] |- \
    {((Forall fresh2). ((0 < fresh2[0]) => (0 < (1 + fresh2[0]))))} 1 \
    {((Forall fresh2). ((0 < fresh2[0]) => (0 < (e_t[0] + fresh2[0]))))}\n\
    ApplyHP: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=(0 < e_t[0])] {(0 < e_t[0])}] |- {((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=(0 < e_t[0])] {(0 < e_t[0])}\n\
    Adapt: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=(0 < e_t[0])] {(0 < e_t[0])}] |- {((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=(0 < e_t[0])] {(0 < e_t[0])} -> [{((T && ((Forall i). \
    (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N MGF=(0 \
    < e_t[0])] {(0 < e_t[0])}] |- {((Forall fresh2). ((0 < fresh2[0]) => (0 < \
    (fresh1[0] + fresh2[0]))))} [N MGF=(0 < e_t[0])] {(0 < (fresh1[0] + \
    e_t[0]))}\n\
    Plus: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=(0 < e_t[0])] {(0 < e_t[0])}] |- \
    {((Forall fresh2). ((0 < fresh2[0]) => (0 < (1 + fresh2[0]))))} 1 \
    {((Forall fresh2). ((0 < fresh2[0]) => (0 < (e_t[0] + fresh2[0]))))}, \
    [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=(0 < e_t[0])] {(0 < e_t[0])}] |- {((Forall fresh2). \
    ((0 < fresh2[0]) => (0 < (fresh1[0] + fresh2[0]))))} [N MGF=(0 < e_t[0])] \
    {(0 < (fresh1[0] + e_t[0]))} -> [{((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N MGF=(0 < e_t[0])] \
    {(0 < e_t[0])}] |- {((Forall fresh2). ((0 < fresh2[0]) => (0 < (1 + \
    fresh2[0]))))} (1 + [N MGF=(0 < e_t[0])]) {(0 < e_t[0])}\n\
    HP: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] \
    <-> b_t_2[i])))} [N MGF=(0 < e_t[0])] {(0 < e_t[0])}] |- {(0 < 1)} 1 {(0 \
    < e_t[0])}, [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=(0 < e_t[0])] {(0 < e_t[0])}] |- \
    {((Forall fresh2). ((0 < fresh2[0]) => (0 < (1 + fresh2[0]))))} (1 + [N \
    MGF=(0 < e_t[0])]) {(0 < e_t[0])} -> {((T && (0 < 1)) && ((Forall \
    fresh2). ((0 < fresh2[0]) => (0 < (1 + fresh2[0])))))} [N MGF=(0 < \
    e_t[0])] {(0 < e_t[0])}\n\
    Weaken: {((T && (0 < 1)) && ((Forall fresh2). ((0 < fresh2[0]) => (0 < (1 \
    + fresh2[0])))))} [N MGF=(0 < e_t[0])] {(0 < e_t[0])} -> {((T && ((Forall \
    i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N \
    MGF=(0 < e_t[0])] {(0 < e_t[0])}\n\
    Adapt: {((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=(0 < e_t[0])] {(0 < e_t[0])} -> {((Forall \
    fresh1). ((0 < fresh1[0]) => (0 < fresh1[0])))} [N MGF=(0 < e_t[0])] {(0 \
    < e_t[0])}\n\
    Weaken: {((Forall fresh1). ((0 < fresh1[0]) => (0 < fresh1[0])))} [N \
    MGF=(0 < e_t[0])] {(0 < e_t[0])} -> {T} [N MGF=(0 < e_t[0])] {(0 < \
    e_t[0])}";

  (* Boolean *)
  let rec b =
    {
      name = "B";
      expansions =
        lazy [ Equals (Numeric (Var "x"),Numeric (Int 1)); Or (BNTerm b, Equals (Numeric (Var "x"),Numeric (Int 0))) ];
      strongest =
        lazy
          (Some
            ( [
                (AIntTermVar ET, AIntTermVar (T "e_t_2"));
                (ABoolVar BT, ABoolVar (B "b_t_2"));
              ],
              Forall
                ( IntTermVar (T "i"),
                  Implies
                    ( eq_int_term (AITVar (ITApp (T "x", ITVar (T "i"))), Int 1),
                      ABVar (BApp (BT, ITVar (T "i"))) ) ) ));
    }
  in
  check_proof_no_hole_vector_state
    {
      pre =
        Forall
          ( IntTermVar (T "i"),
            eq_int_term (AITVar (ITApp (T "x", ITVar (T "i"))), Int 1) );
      prog = Boolean (BNTerm b);
      post = Forall (IntTermVar (T "i"), ABVar (BApp (BT, ITVar (T "i"))));
    }
    "Var: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] \
    {((Forall i). ((x[i] == 1) => b_t[i]))}] |- {((Forall i). ((x[i] == 1) => \
    (x[i] == 1)))} x {((Forall i). ((x[i] == 1) => (e_t[i] == 1)))}\n\
    Int: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] \
    {((Forall i). ((x[i] == 1) => b_t[i]))}] |- {((Forall i). ((x[i] == 1) => \
    (fresh1[i] == 1)))} 1 {((Forall i). ((x[i] == 1) => (fresh1[i] == \
    e_t[i])))}\n\
    Equals: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] \
    {((Forall i). ((x[i] == 1) => b_t[i]))}] |- {((Forall i). ((x[i] == 1) => \
    (x[i] == 1)))} x {((Forall i). ((x[i] == 1) => (e_t[i] == 1)))}, [{((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] {((Forall i). \
    ((x[i] == 1) => b_t[i]))}] |- {((Forall i). ((x[i] == 1) => (fresh1[i] == \
    1)))} 1 {((Forall i). ((x[i] == 1) => (fresh1[i] == e_t[i])))} -> [{((T \
    && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] {((Forall i). \
    ((x[i] == 1) => b_t[i]))}] |- {((Forall i). ((x[i] == 1) => (x[i] == \
    1)))} (x = 1) {((Forall i). ((x[i] == 1) => b_t[i]))}\n\
    ApplyHP: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] \
    {((Forall i). ((x[i] == 1) => b_t[i]))}] |- {((T && ((Forall i). (e_t[i] \
    == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall \
    i). ((x[i] == 1) => b_t[i]))] {((Forall i). ((x[i] == 1) => b_t[i]))}\n\
    Adapt: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] \
    {((Forall i). ((x[i] == 1) => b_t[i]))}] |- {((T && ((Forall i). (e_t[i] \
    == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall \
    i). ((x[i] == 1) => b_t[i]))] {((Forall i). ((x[i] == 1) => b_t[i]))} -> \
    [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] {((Forall i). \
    ((x[i] == 1) => b_t[i]))}] |- {((Forall fresh2). (((Forall i). ((x[i] == \
    1) => fresh2[i])) => ((Forall i). ((x[i] == 1) => (fresh2[i] || (x[i] == \
    0))))))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] {((Forall i). \
    ((x[i] == 1) => (b_t[i] || (x[i] == 0))))}\n\
    Var: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] \
    {((Forall i). ((x[i] == 1) => b_t[i]))}] |- {((Forall i). ((x[i] == 1) => \
    (fresh1[i] || (x[i] == 0))))} x {((Forall i). ((x[i] == 1) => (fresh1[i] \
    || (e_t[i] == 0))))}\n\
    Int: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] \
    {((Forall i). ((x[i] == 1) => b_t[i]))}] |- {((Forall i). ((x[i] == 1) => \
    (fresh1[i] || (fresh2[i] == 0))))} 0 {((Forall i). ((x[i] == 1) => \
    (fresh1[i] || (fresh2[i] == e_t[i]))))}\n\
    Equals: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] \
    {((Forall i). ((x[i] == 1) => b_t[i]))}] |- {((Forall i). ((x[i] == 1) => \
    (fresh1[i] || (x[i] == 0))))} x {((Forall i). ((x[i] == 1) => (fresh1[i] \
    || (e_t[i] == 0))))}, [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => \
    b_t[i]))] {((Forall i). ((x[i] == 1) => b_t[i]))}] |- {((Forall i). \
    ((x[i] == 1) => (fresh1[i] || (fresh2[i] == 0))))} 0 {((Forall i). ((x[i] \
    == 1) => (fresh1[i] || (fresh2[i] == e_t[i]))))} -> [{((T && ((Forall i). \
    (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [B \
    MGF=((Forall i). ((x[i] == 1) => b_t[i]))] {((Forall i). ((x[i] == 1) => \
    b_t[i]))}] |- {((Forall i). ((x[i] == 1) => (fresh1[i] || (x[i] == 0))))} \
    (x = 0) {((Forall i). ((x[i] == 1) => (fresh1[i] || b_t[i])))}\n\
    Or: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] \
    <-> b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] {((Forall \
    i). ((x[i] == 1) => b_t[i]))}] |- {((Forall fresh2). (((Forall i). ((x[i] \
    == 1) => fresh2[i])) => ((Forall i). ((x[i] == 1) => (fresh2[i] || (x[i] \
    == 0))))))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] {((Forall i). \
    ((x[i] == 1) => (b_t[i] || (x[i] == 0))))}, [{((T && ((Forall i). (e_t[i] \
    == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall \
    i). ((x[i] == 1) => b_t[i]))] {((Forall i). ((x[i] == 1) => b_t[i]))}] |- \
    {((Forall i). ((x[i] == 1) => (fresh1[i] || (x[i] == 0))))} (x = 0) \
    {((Forall i). ((x[i] == 1) => (fresh1[i] || b_t[i])))} -> [{((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] {((Forall i). \
    ((x[i] == 1) => b_t[i]))}] |- {((Forall fresh2). (((Forall i). ((x[i] == \
    1) => fresh2[i])) => ((Forall i). ((x[i] == 1) => (fresh2[i] || (x[i] == \
    0))))))} ([B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] || (x = 0)) \
    {((Forall i). ((x[i] == 1) => b_t[i]))}\n\
    HP: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] \
    <-> b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] {((Forall \
    i). ((x[i] == 1) => b_t[i]))}] |- {((Forall i). ((x[i] == 1) => (x[i] == \
    1)))} (x = 1) {((Forall i). ((x[i] == 1) => b_t[i]))}, [{((T && ((Forall \
    i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [B \
    MGF=((Forall i). ((x[i] == 1) => b_t[i]))] {((Forall i). ((x[i] == 1) => \
    b_t[i]))}] |- {((Forall fresh2). (((Forall i). ((x[i] == 1) => \
    fresh2[i])) => ((Forall i). ((x[i] == 1) => (fresh2[i] || (x[i] == \
    0))))))} ([B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] || (x = 0)) \
    {((Forall i). ((x[i] == 1) => b_t[i]))} -> {((T && ((Forall i). ((x[i] == \
    1) => (x[i] == 1)))) && ((Forall fresh2). (((Forall i). ((x[i] == 1) => \
    fresh2[i])) => ((Forall i). ((x[i] == 1) => (fresh2[i] || (x[i] == \
    0)))))))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] {((Forall i). \
    ((x[i] == 1) => b_t[i]))}\n\
    Weaken: {((T && ((Forall i). ((x[i] == 1) => (x[i] == 1)))) && ((Forall \
    fresh2). (((Forall i). ((x[i] == 1) => fresh2[i])) => ((Forall i). ((x[i] \
    == 1) => (fresh2[i] || (x[i] == 0)))))))} [B MGF=((Forall i). ((x[i] == \
    1) => b_t[i]))] {((Forall i). ((x[i] == 1) => b_t[i]))} -> {((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] {((Forall i). \
    ((x[i] == 1) => b_t[i]))}\n\
    Adapt: {((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] \
    {((Forall i). ((x[i] == 1) => b_t[i]))} -> {((Forall fresh2). (((Forall \
    i). ((x[i] == 1) => fresh2[i])) => ((Forall i). fresh2[i])))} [B \
    MGF=((Forall i). ((x[i] == 1) => b_t[i]))] {((Forall i). b_t[i])}\n\
    Weaken: {((Forall fresh2). (((Forall i). ((x[i] == 1) => fresh2[i])) => \
    ((Forall i). fresh2[i])))} [B MGF=((Forall i). ((x[i] == 1) => b_t[i]))] \
    {((Forall i). b_t[i])} -> {((Forall i). (x[i] == 1))} [B MGF=((Forall i). \
    ((x[i] == 1) => b_t[i]))] {((Forall i). b_t[i])}";

  (* Statement + Numeric *)
  (* This proof I have not yet hand-checked. *)
  let rec n =
    {
      name = "N";
      expansions = lazy [ Int 1; Plus (Int 0, NNTerm n) ];
      strongest =
        lazy
          (Some
            ( [
                (AIntTermVar ET, AIntTermVar (T "e_t_2"));
                (ABoolVar BT, ABoolVar (B "b_t_2"));
              ],
              Forall
                ( IntTermVar (T "i"),
                  eq_int_term (Int 1, AITVar (ITApp (ET, ITVar (T "i")))) ) ));
    }
  and s =
    {
      name = "S";
      expansions =
        lazy
          [
            Assign ("x", NNTerm n);
            Seq (SNTerm s, Assign ("x", Plus (Var "x", NNTerm n)));
          ];
      strongest =
        lazy
          (Some
            ( [
                (AIntTermVar ET, AIntTermVar (T "e_t_2"));
                (ABoolVar BT, ABoolVar (B "b_t_2"));
                (AIntTermVar (T "x"), AIntTermVar (T "x_2"));
              ],
              Forall
                ( IntTermVar (T "i"),
                  less_int_term (Int 0, AITVar (ITApp (T "x", ITVar (T "i"))))
                ) ));
    }
  in
  check_proof_no_hole_vector_state
    {
      pre = eq_int_term (AITVar (ITApp (T "x", Int 1)), Int 1);
      prog = Stmt (SNTerm s);
      post = less_int_term (Int (-1), AITVar (ITApp (T "x", Int 1)));
    }
    "Int: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall \
    i). (1 == e_t[i]))}, {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} \
    [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    i). (1 == 1))} 1 {((Forall i). (1 == e_t[i]))}\n\
    Int: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall \
    i). (1 == e_t[i]))}, {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} \
    [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    fresh2). (((Forall i). (1 == fresh2[i])) => ((Forall i). (1 == (0 + \
    fresh2[i])))))} 0 {((Forall fresh2). (((Forall i). (1 == fresh2[i])) => \
    ((Forall i). (1 == (e_t[i] + fresh2[i])))))}\n\
    ApplyHP: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall \
    i). (1 == e_t[i]))}, {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} \
    [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (1 == \
    e_t[i]))}\n\
    Adapt: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall \
    i). (1 == e_t[i]))}, {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} \
    [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (1 == \
    e_t[i]))} -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall \
    i). (1 == e_t[i]))}, {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} \
    [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    fresh2). (((Forall i). (1 == fresh2[i])) => ((Forall i). (1 == (fresh1[i] \
    + fresh2[i])))))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (1 == \
    (fresh1[i] + e_t[i])))}\n\
    Plus: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall \
    i). (1 == e_t[i]))}, {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} \
    [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    fresh2). (((Forall i). (1 == fresh2[i])) => ((Forall i). (1 == (0 + \
    fresh2[i])))))} 0 {((Forall fresh2). (((Forall i). (1 == fresh2[i])) => \
    ((Forall i). (1 == (e_t[i] + fresh2[i])))))}, [{((T && ((Forall i). \
    (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N \
    MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (1 == e_t[i]))}, {(((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Forall i). (0 < \
    x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall fresh2). (((Forall i). \
    (1 == fresh2[i])) => ((Forall i). (1 == (fresh1[i] + fresh2[i])))))} [N \
    MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (1 == (fresh1[i] + \
    e_t[i])))} -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall \
    i). (b_t[i] <-> b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] \
    {((Forall i). (1 == e_t[i]))}, {(((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] \
    == x_2[i])))} [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < \
    x[i]))}] |- {((Forall fresh2). (((Forall i). (1 == fresh2[i])) => \
    ((Forall i). (1 == (0 + fresh2[i])))))} (0 + [N MGF=((Forall i). (1 == \
    e_t[i]))]) {((Forall i). (1 == e_t[i]))}\n\
    HP: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] \
    <-> b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (1 == \
    e_t[i]))}, {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    i). (1 == 1))} 1 {((Forall i). (1 == e_t[i]))}, [{((T && ((Forall i). \
    (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N \
    MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (1 == e_t[i]))}, {(((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Forall i). (0 < \
    x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall fresh2). (((Forall i). \
    (1 == fresh2[i])) => ((Forall i). (1 == (0 + fresh2[i])))))} (0 + [N \
    MGF=((Forall i). (1 == e_t[i]))]) {((Forall i). (1 == e_t[i]))} -> [{(((T \
    && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Forall i). (0 < \
    x[i]))] {((Forall i). (0 < x[i]))}] |- {((T && ((Forall i). (1 == 1))) && \
    ((Forall fresh2). (((Forall i). (1 == fresh2[i])) => ((Forall i). (1 == \
    (0 + fresh2[i]))))))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall i). \
    (1 == e_t[i]))}\n\
    Weaken: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((T && \
    ((Forall i). (1 == 1))) && ((Forall fresh2). (((Forall i). (1 == \
    fresh2[i])) => ((Forall i). (1 == (0 + fresh2[i]))))))} [N MGF=((Forall \
    i). (1 == e_t[i]))] {((Forall i). (1 == e_t[i]))} -> [{(((T && ((Forall \
    i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Forall i). (0 < x[i]))] \
    {((Forall i). (0 < x[i]))}] |- {((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N MGF=((Forall i). \
    (1 == e_t[i]))] {((Forall i). (1 == e_t[i]))}\n\
    Adapt: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (1 == \
    e_t[i]))} -> [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall \
    i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    fresh1). (((Forall i). (1 == fresh1[i])) => ((Forall i). (0 < \
    fresh1[i]))))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (0 < \
    e_t[i]))}\n\
    Assign: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    fresh1). (((Forall i). (1 == fresh1[i])) => ((Forall i). (0 < \
    fresh1[i]))))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (0 < \
    e_t[i]))} -> [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall \
    i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    fresh1). (((Forall i). (1 == fresh1[i])) => ((Forall i). (0 < \
    fresh1[i]))))} (x := [N MGF=((Forall i). (1 == e_t[i]))]) {((Forall i). \
    (0 < x[i]))}\n\
    ApplyHP: -> [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {(((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Forall i). (0 < \
    x[i]))] {((Forall i). (0 < x[i]))}\n\
    Adapt: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {(((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Forall i). (0 < \
    x[i]))] {((Forall i). (0 < x[i]))} -> [{(((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] \
    == x_2[i])))} [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < \
    x[i]))}] |- {((Forall fresh4). (((Forall i). (0 < fresh4[i])) => ((Forall \
    fresh2). (((Forall i). (1 == fresh2[i])) => ((Forall i). (0 < (fresh4[i] \
    + fresh2[i])))))))} [S MGF=((Forall i). (0 < x[i]))] {((Forall fresh2). \
    (((Forall i). (1 == fresh2[i])) => ((Forall i). (0 < (x[i] + \
    fresh2[i])))))}\n\
    Var: -> [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    fresh2). (((Forall i). (1 == fresh2[i])) => ((Forall i). (0 < (x[i] + \
    fresh2[i])))))} x {((Forall fresh2). (((Forall i). (1 == fresh2[i])) => \
    ((Forall i). (0 < (e_t[i] + fresh2[i])))))}\n\
    Int: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall \
    i). (1 == e_t[i]))}, {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} \
    [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    i). (1 == 1))} 1 {((Forall i). (1 == e_t[i]))}\n\
    Int: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall \
    i). (1 == e_t[i]))}, {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} \
    [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    fresh2). (((Forall i). (1 == fresh2[i])) => ((Forall i). (1 == (0 + \
    fresh2[i])))))} 0 {((Forall fresh2). (((Forall i). (1 == fresh2[i])) => \
    ((Forall i). (1 == (e_t[i] + fresh2[i])))))}\n\
    ApplyHP: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall \
    i). (1 == e_t[i]))}, {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} \
    [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (1 == \
    e_t[i]))}\n\
    Adapt: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall \
    i). (1 == e_t[i]))}, {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} \
    [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (1 == \
    e_t[i]))} -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall \
    i). (1 == e_t[i]))}, {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} \
    [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    fresh2). (((Forall i). (1 == fresh2[i])) => ((Forall i). (1 == (fresh1[i] \
    + fresh2[i])))))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (1 == \
    (fresh1[i] + e_t[i])))}\n\
    Plus: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall \
    i). (1 == e_t[i]))}, {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} \
    [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    fresh2). (((Forall i). (1 == fresh2[i])) => ((Forall i). (1 == (0 + \
    fresh2[i])))))} 0 {((Forall fresh2). (((Forall i). (1 == fresh2[i])) => \
    ((Forall i). (1 == (e_t[i] + fresh2[i])))))}, [{((T && ((Forall i). \
    (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N \
    MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (1 == e_t[i]))}, {(((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Forall i). (0 < \
    x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall fresh2). (((Forall i). \
    (1 == fresh2[i])) => ((Forall i). (1 == (fresh1[i] + fresh2[i])))))} [N \
    MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (1 == (fresh1[i] + \
    e_t[i])))} -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall \
    i). (b_t[i] <-> b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] \
    {((Forall i). (1 == e_t[i]))}, {(((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] \
    == x_2[i])))} [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < \
    x[i]))}] |- {((Forall fresh2). (((Forall i). (1 == fresh2[i])) => \
    ((Forall i). (1 == (0 + fresh2[i])))))} (0 + [N MGF=((Forall i). (1 == \
    e_t[i]))]) {((Forall i). (1 == e_t[i]))}\n\
    HP: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] \
    <-> b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (1 == \
    e_t[i]))}, {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    i). (1 == 1))} 1 {((Forall i). (1 == e_t[i]))}, [{((T && ((Forall i). \
    (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N \
    MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (1 == e_t[i]))}, {(((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Forall i). (0 < \
    x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall fresh2). (((Forall i). \
    (1 == fresh2[i])) => ((Forall i). (1 == (0 + fresh2[i])))))} (0 + [N \
    MGF=((Forall i). (1 == e_t[i]))]) {((Forall i). (1 == e_t[i]))} -> [{(((T \
    && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Forall i). (0 < \
    x[i]))] {((Forall i). (0 < x[i]))}] |- {((T && ((Forall i). (1 == 1))) && \
    ((Forall fresh2). (((Forall i). (1 == fresh2[i])) => ((Forall i). (1 == \
    (0 + fresh2[i]))))))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall i). \
    (1 == e_t[i]))}\n\
    Weaken: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((T && \
    ((Forall i). (1 == 1))) && ((Forall fresh2). (((Forall i). (1 == \
    fresh2[i])) => ((Forall i). (1 == (0 + fresh2[i]))))))} [N MGF=((Forall \
    i). (1 == e_t[i]))] {((Forall i). (1 == e_t[i]))} -> [{(((T && ((Forall \
    i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Forall i). (0 < x[i]))] \
    {((Forall i). (0 < x[i]))}] |- {((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N MGF=((Forall i). \
    (1 == e_t[i]))] {((Forall i). (1 == e_t[i]))}\n\
    Adapt: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (1 == \
    e_t[i]))} -> [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall \
    i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    fresh2). (((Forall i). (1 == fresh2[i])) => ((Forall i). (0 < (fresh1[i] \
    + fresh2[i])))))} [N MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (0 < \
    (fresh1[i] + e_t[i])))}\n\
    Plus: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    fresh2). (((Forall i). (1 == fresh2[i])) => ((Forall i). (0 < (x[i] + \
    fresh2[i])))))} x {((Forall fresh2). (((Forall i). (1 == fresh2[i])) => \
    ((Forall i). (0 < (e_t[i] + fresh2[i])))))}, [{(((T && ((Forall i). \
    (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Forall i). (0 < x[i]))] \
    {((Forall i). (0 < x[i]))}] |- {((Forall fresh2). (((Forall i). (1 == \
    fresh2[i])) => ((Forall i). (0 < (fresh1[i] + fresh2[i])))))} [N \
    MGF=((Forall i). (1 == e_t[i]))] {((Forall i). (0 < (fresh1[i] + \
    e_t[i])))} -> [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall \
    i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    fresh2). (((Forall i). (1 == fresh2[i])) => ((Forall i). (0 < (x[i] + \
    fresh2[i])))))} (x + [N MGF=((Forall i). (1 == e_t[i]))]) {((Forall i). \
    (0 < e_t[i]))}\n\
    Assign: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    fresh2). (((Forall i). (1 == fresh2[i])) => ((Forall i). (0 < (x[i] + \
    fresh2[i])))))} (x + [N MGF=((Forall i). (1 == e_t[i]))]) {((Forall i). \
    (0 < e_t[i]))} -> [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} \
    [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    fresh2). (((Forall i). (1 == fresh2[i])) => ((Forall i). (0 < (x[i] + \
    fresh2[i])))))} (x := (x + [N MGF=((Forall i). (1 == e_t[i]))])) \
    {((Forall i). (0 < x[i]))}\n\
    Seq: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall \
    fresh4). (((Forall i). (0 < fresh4[i])) => ((Forall fresh2). (((Forall \
    i). (1 == fresh2[i])) => ((Forall i). (0 < (fresh4[i] + fresh2[i])))))))} \
    [S MGF=((Forall i). (0 < x[i]))] {((Forall fresh2). (((Forall i). (1 == \
    fresh2[i])) => ((Forall i). (0 < (x[i] + fresh2[i])))))}, [{(((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Forall i). (0 < \
    x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall fresh2). (((Forall i). \
    (1 == fresh2[i])) => ((Forall i). (0 < (x[i] + fresh2[i])))))} (x := (x + \
    [N MGF=((Forall i). (1 == e_t[i]))])) {((Forall i). (0 < x[i]))} -> \
    [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Forall i). (0 < \
    x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall fresh4). (((Forall i). \
    (0 < fresh4[i])) => ((Forall fresh2). (((Forall i). (1 == fresh2[i])) => \
    ((Forall i). (0 < (fresh4[i] + fresh2[i])))))))} ([S MGF=((Forall i). (0 \
    < x[i]))]; (x := (x + [N MGF=((Forall i). (1 == e_t[i]))]))) {((Forall \
    i). (0 < x[i]))}\n\
    HP: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] \
    <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Forall i). \
    (0 < x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall fresh1). (((Forall \
    i). (1 == fresh1[i])) => ((Forall i). (0 < fresh1[i]))))} (x := [N \
    MGF=((Forall i). (1 == e_t[i]))]) {((Forall i). (0 < x[i]))}, [{(((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Forall i). (0 < \
    x[i]))] {((Forall i). (0 < x[i]))}] |- {((Forall fresh4). (((Forall i). \
    (0 < fresh4[i])) => ((Forall fresh2). (((Forall i). (1 == fresh2[i])) => \
    ((Forall i). (0 < (fresh4[i] + fresh2[i])))))))} ([S MGF=((Forall i). (0 \
    < x[i]))]; (x := (x + [N MGF=((Forall i). (1 == e_t[i]))]))) {((Forall \
    i). (0 < x[i]))} -> {((T && ((Forall fresh1). (((Forall i). (1 == \
    fresh1[i])) => ((Forall i). (0 < fresh1[i]))))) && ((Forall fresh4). \
    (((Forall i). (0 < fresh4[i])) => ((Forall fresh2). (((Forall i). (1 == \
    fresh2[i])) => ((Forall i). (0 < (fresh4[i] + fresh2[i]))))))))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}\n\
    Weaken: {((T && ((Forall fresh1). (((Forall i). (1 == fresh1[i])) => \
    ((Forall i). (0 < fresh1[i]))))) && ((Forall fresh4). (((Forall i). (0 < \
    fresh4[i])) => ((Forall fresh2). (((Forall i). (1 == fresh2[i])) => \
    ((Forall i). (0 < (fresh4[i] + fresh2[i]))))))))} [S MGF=((Forall i). (0 \
    < x[i]))] {((Forall i). (0 < x[i]))} -> {(((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] \
    == x_2[i])))} [S MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))}\n\
    Adapt: {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Forall i). (0 < x[i]))] {((Forall i). (0 < x[i]))} -> {((Forall \
    fresh3). (((Forall i). (0 < fresh3[i])) => (-1 < fresh3[1])))} [S \
    MGF=((Forall i). (0 < x[i]))] {(-1 < x[1])}\n\
    Weaken: {((Forall fresh3). (((Forall i). (0 < fresh3[i])) => (-1 < \
    fresh3[1])))} [S MGF=((Forall i). (0 < x[i]))] {(-1 < x[1])} -> {(x[1] == \
    1)} [S MGF=((Forall i). (0 < x[i]))] {(-1 < x[1])}"

let test_ITE_vector_states =
  (* Numeric ITE *)
  check_proof_no_hole_vector_state
    {
      pre =
        Forall
          ( IntTermVar (T "i"),
            eq_int_term (ITVar (T "i"), AITVar (ITApp (T "x", ITVar (T "i"))))
          );
      prog = Term (Numeric (ITE (Equals (Numeric (Var "x"), Numeric (Int 0)), Int 1, Var "x")));
      post =
        Forall
          ( IntTermVar (T "i"),
            Implies
              ( less_int_term (Int 1, ITVar (T "i")),
                less_int_term (Int 1, AITVar (ITApp (ET, ITVar (T "i")))) ) );
    }
    "Var: -> {((Forall i). ((F || (T && (1 < i))) => ((F || ((!(x[i] == 0) && \
    T) && (1 < x[i]))) || (((x[i] == 0) && T) && (1 < 1)))))} x {((Forall i). \
    ((F || (T && (1 < i))) => ((F || ((!(e_t[i] == 0) && T) && (1 < x[i]))) \
    || (((e_t[i] == 0) && T) && (1 < 1)))))}\n\
    Int: -> {((Forall i). ((F || (T && (1 < i))) => ((F || ((!(fresh1[i] == \
    0) && T) && (1 < x[i]))) || (((fresh1[i] == 0) && T) && (1 < 1)))))} 0 \
    {((Forall i). ((F || (T && (1 < i))) => ((F || ((!(fresh1[i] == e_t[i]) \
    && T) && (1 < x[i]))) || (((fresh1[i] == e_t[i]) && T) && (1 < 1)))))}\n\
    Equals: {((Forall i). ((F || (T && (1 < i))) => ((F || ((!(x[i] == 0) && \
    T) && (1 < x[i]))) || (((x[i] == 0) && T) && (1 < 1)))))} x {((Forall i). \
    ((F || (T && (1 < i))) => ((F || ((!(e_t[i] == 0) && T) && (1 < x[i]))) \
    || (((e_t[i] == 0) && T) && (1 < 1)))))}, {((Forall i). ((F || (T && (1 < \
    i))) => ((F || ((!(fresh1[i] == 0) && T) && (1 < x[i]))) || (((fresh1[i] \
    == 0) && T) && (1 < 1)))))} 0 {((Forall i). ((F || (T && (1 < i))) => ((F \
    || ((!(fresh1[i] == e_t[i]) && T) && (1 < x[i]))) || (((fresh1[i] == \
    e_t[i]) && T) && (1 < 1)))))} -> {((Forall i). ((F || (T && (1 < i))) => \
    ((F || ((!(x[i] == 0) && T) && (1 < x[i]))) || (((x[i] == 0) && T) && (1 \
    < 1)))))} (x = 0) {((Forall i). ((F || (T && (1 < i))) => ((F || \
    ((!b_t[i] && T) && (1 < x[i]))) || ((b_t[i] && T) && (1 < 1)))))}\n\
    Int: -> {((Forall i). ((F || (T && (1 < i))) => ((F || ((!fresh1[i] && T) \
    && (1 < x[i]))) || ((fresh1[i] && T) && (1 < 1)))))} 1 {((Forall i). ((F \
    || (T && (1 < i))) => ((F || ((!fresh1[i] && T) && (1 < x[i]))) || \
    ((fresh1[i] && T) && (1 < e_t[i])))))}\n\
    Var: -> {((Forall i). ((F || (T && (1 < i))) => ((F || ((!fresh1[i] && T) \
    && (1 < x[i]))) || ((fresh1[i] && T) && (1 < fresh2[i])))))} x {((Forall \
    i). ((F || (T && (1 < i))) => ((F || ((!fresh1[i] && T) && (1 < e_t[i]))) \
    || ((fresh1[i] && T) && (1 < fresh2[i])))))}\n\
    ITE: {((Forall i). ((F || (T && (1 < i))) => ((F || ((!(x[i] == 0) && T) \
    && (1 < x[i]))) || (((x[i] == 0) && T) && (1 < 1)))))} (x = 0) {((Forall \
    i). ((F || (T && (1 < i))) => ((F || ((!b_t[i] && T) && (1 < x[i]))) || \
    ((b_t[i] && T) && (1 < 1)))))}, {((Forall i). ((F || (T && (1 < i))) => \
    ((F || ((!fresh1[i] && T) && (1 < x[i]))) || ((fresh1[i] && T) && (1 < \
    1)))))} 1 {((Forall i). ((F || (T && (1 < i))) => ((F || ((!fresh1[i] && \
    T) && (1 < x[i]))) || ((fresh1[i] && T) && (1 < e_t[i])))))}, {((Forall \
    i). ((F || (T && (1 < i))) => ((F || ((!fresh1[i] && T) && (1 < x[i]))) \
    || ((fresh1[i] && T) && (1 < fresh2[i])))))} x {((Forall i). ((F || (T && \
    (1 < i))) => ((F || ((!fresh1[i] && T) && (1 < e_t[i]))) || ((fresh1[i] \
    && T) && (1 < fresh2[i])))))} -> {((Forall i). ((F || (T && (1 < i))) => \
    ((F || ((!(x[i] == 0) && T) && (1 < x[i]))) || (((x[i] == 0) && T) && (1 \
    < 1)))))} (if (x = 0) then 1 else x) {((Forall i). ((1 < i) => (1 < \
    e_t[i])))}\n\
    Weaken: {((Forall i). ((F || (T && (1 < i))) => ((F || ((!(x[i] == 0) && \
    T) && (1 < x[i]))) || (((x[i] == 0) && T) && (1 < 1)))))} (if (x = 0) \
    then 1 else x) {((Forall i). ((1 < i) => (1 < e_t[i])))} -> {((Forall i). \
    (i == x[i]))} (if (x = 0) then 1 else x) {((Forall i). ((1 < i) => (1 < \
    e_t[i])))}";
  (* Numeric ITE with Recursive Nonterminal *)
  let rec n =
    {
      name = "N";
      expansions = lazy [ Int 1; Plus (Int 1, NNTerm n) ];
      strongest =
        lazy
          (Some
            ( [
                (AIntTermVar ET, AIntTermVar (T "e_t_2"));
                (ABoolVar BT, ABoolVar (B "b_t_2"));
              ],
              Exists
                ( IntTermVar (T "n"),
                  Forall
                    ( IntTermVar (T "i"),
                      eq_int_term
                        (ITVar (T "n"), AITVar (ITApp (ET, ITVar (T "i")))) )
                ) ));
    }
  in
  check_proof_no_hole_vector_state
    {
      pre =
        Forall
          ( IntTermVar (T "i"),
            eq_int_term (ITVar (T "i"), AITVar (ITApp (T "x", ITVar (T "i"))))
          );
      prog = Term (Numeric (ITE (Equals (Numeric (Var "x"), Numeric (NNTerm n)), Int 1, Var "x")));
      post =
        Forall
          ( IntTermVar (T "n"),
            Exists
              ( IntTermVar (T "i"),
                less_int_term (ITVar (T "n"), AITVar (ITApp (ET, ITVar (T "i"))))
              ) );
    }
    "Var: -> {((Forall fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) \
    => ((Forall n). ((Exists i). ((F || ((!(x[i] == fresh2[i]) && T) && (n < \
    x[i]))) || (((x[i] == fresh2[i]) && T) && (n < 1)))))))} x {((Forall \
    fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Forall n). \
    ((Exists i). ((F || ((!(e_t[i] == fresh2[i]) && T) && (n < x[i]))) || \
    (((e_t[i] == fresh2[i]) && T) && (n < 1)))))))}\n\
    Int: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}] |- {((Exists n). \
    ((Forall i). (n == 1)))} 1 {((Exists n). ((Forall i). (n == e_t[i])))}\n\
    Int: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}] |- {((Forall \
    fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Exists n). \
    ((Forall i). (n == (1 + fresh2[i]))))))} 1 {((Forall fresh2). (((Exists \
    n). ((Forall i). (n == fresh2[i]))) => ((Exists n). ((Forall i). (n == \
    (e_t[i] + fresh2[i]))))))}\n\
    ApplyHP: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}] |- {((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == e_t[i])))] {((Exists \
    n). ((Forall i). (n == e_t[i])))}\n\
    Adapt: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}] |- {((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == e_t[i])))] {((Exists \
    n). ((Forall i). (n == e_t[i])))} -> [{((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). \
    ((Forall i). (n == e_t[i])))] {((Exists n). ((Forall i). (n == \
    e_t[i])))}] |- {((Forall fresh2). (((Exists n). ((Forall i). (n == \
    fresh2[i]))) => ((Exists n). ((Forall i). (n == (fresh1[i] + \
    fresh2[i]))))))} [N MGF=((Exists n). ((Forall i). (n == e_t[i])))] \
    {((Exists n). ((Forall i). (n == (fresh1[i] + e_t[i]))))}\n\
    Plus: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}] |- {((Forall \
    fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Exists n). \
    ((Forall i). (n == (1 + fresh2[i]))))))} 1 {((Forall fresh2). (((Exists \
    n). ((Forall i). (n == fresh2[i]))) => ((Exists n). ((Forall i). (n == \
    (e_t[i] + fresh2[i]))))))}, [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) \
    && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). \
    (n == e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}] |- \
    {((Forall fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => \
    ((Exists n). ((Forall i). (n == (fresh1[i] + fresh2[i]))))))} [N \
    MGF=((Exists n). ((Forall i). (n == e_t[i])))] {((Exists n). ((Forall i). \
    (n == (fresh1[i] + e_t[i]))))} -> [{((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). \
    ((Forall i). (n == e_t[i])))] {((Exists n). ((Forall i). (n == \
    e_t[i])))}] |- {((Forall fresh2). (((Exists n). ((Forall i). (n == \
    fresh2[i]))) => ((Exists n). ((Forall i). (n == (1 + fresh2[i]))))))} (1 \
    + [N MGF=((Exists n). ((Forall i). (n == e_t[i])))]) {((Exists n). \
    ((Forall i). (n == e_t[i])))}\n\
    HP: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] \
    <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == e_t[i])))] \
    {((Exists n). ((Forall i). (n == e_t[i])))}] |- {((Exists n). ((Forall \
    i). (n == 1)))} 1 {((Exists n). ((Forall i). (n == e_t[i])))}, [{((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == e_t[i])))] {((Exists \
    n). ((Forall i). (n == e_t[i])))}] |- {((Forall fresh2). (((Exists n). \
    ((Forall i). (n == fresh2[i]))) => ((Exists n). ((Forall i). (n == (1 + \
    fresh2[i]))))))} (1 + [N MGF=((Exists n). ((Forall i). (n == e_t[i])))]) \
    {((Exists n). ((Forall i). (n == e_t[i])))} -> {((T && ((Exists n). \
    ((Forall i). (n == 1)))) && ((Forall fresh2). (((Exists n). ((Forall i). \
    (n == fresh2[i]))) => ((Exists n). ((Forall i). (n == (1 + \
    fresh2[i])))))))} [N MGF=((Exists n). ((Forall i). (n == e_t[i])))] \
    {((Exists n). ((Forall i). (n == e_t[i])))}\n\
    Weaken: {((T && ((Exists n). ((Forall i). (n == 1)))) && ((Forall \
    fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Exists n). \
    ((Forall i). (n == (1 + fresh2[i])))))))} [N MGF=((Exists n). ((Forall \
    i). (n == e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))} -> {((T \
    && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == e_t[i])))] {((Exists \
    n). ((Forall i). (n == e_t[i])))}\n\
    Adapt: {((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))} -> {((Forall \
    fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Forall n). \
    ((Exists i). ((F || ((!(fresh1[i] == fresh2[i]) && T) && (n < x[i]))) || \
    (((fresh1[i] == fresh2[i]) && T) && (n < 1)))))))} [N MGF=((Exists n). \
    ((Forall i). (n == e_t[i])))] {((Forall n). ((Exists i). ((F || \
    ((!(fresh1[i] == e_t[i]) && T) && (n < x[i]))) || (((fresh1[i] == e_t[i]) \
    && T) && (n < 1)))))}\n\
    Equals: {((Forall fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) \
    => ((Forall n). ((Exists i). ((F || ((!(x[i] == fresh2[i]) && T) && (n < \
    x[i]))) || (((x[i] == fresh2[i]) && T) && (n < 1)))))))} x {((Forall \
    fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Forall n). \
    ((Exists i). ((F || ((!(e_t[i] == fresh2[i]) && T) && (n < x[i]))) || \
    (((e_t[i] == fresh2[i]) && T) && (n < 1)))))))}, {((Forall fresh2). \
    (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Forall n). ((Exists \
    i). ((F || ((!(fresh1[i] == fresh2[i]) && T) && (n < x[i]))) || \
    (((fresh1[i] == fresh2[i]) && T) && (n < 1)))))))} [N MGF=((Exists n). \
    ((Forall i). (n == e_t[i])))] {((Forall n). ((Exists i). ((F || \
    ((!(fresh1[i] == e_t[i]) && T) && (n < x[i]))) || (((fresh1[i] == e_t[i]) \
    && T) && (n < 1)))))} -> {((Forall fresh2). (((Exists n). ((Forall i). (n \
    == fresh2[i]))) => ((Forall n). ((Exists i). ((F || ((!(x[i] == \
    fresh2[i]) && T) && (n < x[i]))) || (((x[i] == fresh2[i]) && T) && (n < \
    1)))))))} (x = [N MGF=((Exists n). ((Forall i). (n == e_t[i])))]) \
    {((Forall n). ((Exists i). ((F || ((!b_t[i] && T) && (n < x[i]))) || \
    ((b_t[i] && T) && (n < 1)))))}\n\
    Int: -> {((Forall n). ((Exists i). ((F || ((!fresh1[i] && T) && (n < \
    x[i]))) || ((fresh1[i] && T) && (n < 1)))))} 1 {((Forall n). ((Exists i). \
    ((F || ((!fresh1[i] && T) && (n < x[i]))) || ((fresh1[i] && T) && (n < \
    e_t[i])))))}\n\
    Var: -> {((Forall n). ((Exists i). ((F || ((!fresh1[i] && T) && (n < \
    x[i]))) || ((fresh1[i] && T) && (n < fresh2[i])))))} x {((Forall n). \
    ((Exists i). ((F || ((!fresh1[i] && T) && (n < e_t[i]))) || ((fresh1[i] \
    && T) && (n < fresh2[i])))))}\n\
    ITE: {((Forall fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => \
    ((Forall n). ((Exists i). ((F || ((!(x[i] == fresh2[i]) && T) && (n < \
    x[i]))) || (((x[i] == fresh2[i]) && T) && (n < 1)))))))} (x = [N \
    MGF=((Exists n). ((Forall i). (n == e_t[i])))]) {((Forall n). ((Exists \
    i). ((F || ((!b_t[i] && T) && (n < x[i]))) || ((b_t[i] && T) && (n < \
    1)))))}, {((Forall n). ((Exists i). ((F || ((!fresh1[i] && T) && (n < \
    x[i]))) || ((fresh1[i] && T) && (n < 1)))))} 1 {((Forall n). ((Exists i). \
    ((F || ((!fresh1[i] && T) && (n < x[i]))) || ((fresh1[i] && T) && (n < \
    e_t[i])))))}, {((Forall n). ((Exists i). ((F || ((!fresh1[i] && T) && (n \
    < x[i]))) || ((fresh1[i] && T) && (n < fresh2[i])))))} x {((Forall n). \
    ((Exists i). ((F || ((!fresh1[i] && T) && (n < e_t[i]))) || ((fresh1[i] \
    && T) && (n < fresh2[i])))))} -> {((Forall fresh2). (((Exists n). \
    ((Forall i). (n == fresh2[i]))) => ((Forall n). ((Exists i). ((F || \
    ((!(x[i] == fresh2[i]) && T) && (n < x[i]))) || (((x[i] == fresh2[i]) && \
    T) && (n < 1)))))))} (if (x = [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))]) then 1 else x) {((Forall n). ((Exists i). (n < e_t[i])))}\n\
    Weaken: {((Forall fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) \
    => ((Forall n). ((Exists i). ((F || ((!(x[i] == fresh2[i]) && T) && (n < \
    x[i]))) || (((x[i] == fresh2[i]) && T) && (n < 1)))))))} (if (x = [N \
    MGF=((Exists n). ((Forall i). (n == e_t[i])))]) then 1 else x) {((Forall \
    n). ((Exists i). (n < e_t[i])))} -> {((Forall i). (i == x[i]))} (if (x = \
    [N MGF=((Exists n). ((Forall i). (n == e_t[i])))]) then 1 else x) \
    {((Forall n). ((Exists i). (n < e_t[i])))}";
  (* Stmt ITE *)
  check_proof_no_hole_vector_state
    {
      pre =
        Exists
          ( IntTermVar (T "i"),
            Exists
              ( IntTermVar (T "j"),
                And
                  ( eq_int_term (Int 0, AITVar (ITApp (T "x", ITVar (T "i")))),
                    eq_int_term (Int 1, AITVar (ITApp (T "x", ITVar (T "j"))))
                  ) ) );
      prog =
        Stmt
          (ITE
            (Equals (Numeric (Int 1), Numeric (Var "x")), Assign ("x", Int 0), Assign ("x", Int 1)));
      post =
        Exists
          ( IntTermVar (T "i"),
            Exists
              ( IntTermVar (T "j"),
                And
                  ( eq_int_term (Int 0, AITVar (ITApp (T "x", ITVar (T "i")))),
                    eq_int_term (Int 1, AITVar (ITApp (T "x", ITVar (T "j"))))
                  ) ) );
    }
    "Int: -> {((Exists i). ((Exists j). (((F || ((!(1 == x[i]) && T) && (0 == \
    1))) || (((1 == x[i]) && T) && (0 == 0))) && ((F || ((!(1 == x[j]) && T) \
    && (1 == 1))) || (((1 == x[j]) && T) && (1 == 0))))))} 1 {((Exists i). \
    ((Exists j). (((F || ((!(e_t[i] == x[i]) && T) && (0 == 1))) || (((e_t[i] \
    == x[i]) && T) && (0 == 0))) && ((F || ((!(e_t[j] == x[j]) && T) && (1 == \
    1))) || (((e_t[j] == x[j]) && T) && (1 == 0))))))}\n\
    Var: -> {((Exists i). ((Exists j). (((F || ((!(fresh1[i] == x[i]) && T) \
    && (0 == 1))) || (((fresh1[i] == x[i]) && T) && (0 == 0))) && ((F || \
    ((!(fresh1[j] == x[j]) && T) && (1 == 1))) || (((fresh1[j] == x[j]) && T) \
    && (1 == 0))))))} x {((Exists i). ((Exists j). (((F || ((!(fresh1[i] == \
    e_t[i]) && T) && (0 == 1))) || (((fresh1[i] == e_t[i]) && T) && (0 == \
    0))) && ((F || ((!(fresh1[j] == e_t[j]) && T) && (1 == 1))) || \
    (((fresh1[j] == e_t[j]) && T) && (1 == 0))))))}\n\
    Equals: {((Exists i). ((Exists j). (((F || ((!(1 == x[i]) && T) && (0 == \
    1))) || (((1 == x[i]) && T) && (0 == 0))) && ((F || ((!(1 == x[j]) && T) \
    && (1 == 1))) || (((1 == x[j]) && T) && (1 == 0))))))} 1 {((Exists i). \
    ((Exists j). (((F || ((!(e_t[i] == x[i]) && T) && (0 == 1))) || (((e_t[i] \
    == x[i]) && T) && (0 == 0))) && ((F || ((!(e_t[j] == x[j]) && T) && (1 == \
    1))) || (((e_t[j] == x[j]) && T) && (1 == 0))))))}, {((Exists i). \
    ((Exists j). (((F || ((!(fresh1[i] == x[i]) && T) && (0 == 1))) || \
    (((fresh1[i] == x[i]) && T) && (0 == 0))) && ((F || ((!(fresh1[j] == \
    x[j]) && T) && (1 == 1))) || (((fresh1[j] == x[j]) && T) && (1 == \
    0))))))} x {((Exists i). ((Exists j). (((F || ((!(fresh1[i] == e_t[i]) && \
    T) && (0 == 1))) || (((fresh1[i] == e_t[i]) && T) && (0 == 0))) && ((F || \
    ((!(fresh1[j] == e_t[j]) && T) && (1 == 1))) || (((fresh1[j] == e_t[j]) \
    && T) && (1 == 0))))))} -> {((Exists i). ((Exists j). (((F || ((!(1 == \
    x[i]) && T) && (0 == 1))) || (((1 == x[i]) && T) && (0 == 0))) && ((F || \
    ((!(1 == x[j]) && T) && (1 == 1))) || (((1 == x[j]) && T) && (1 == \
    0))))))} (1 = x) {((Exists i). ((Exists j). (((F || ((!b_t[i] && T) && (0 \
    == 1))) || ((b_t[i] && T) && (0 == 0))) && ((F || ((!b_t[j] && T) && (1 \
    == 1))) || ((b_t[j] && T) && (1 == 0))))))}\n\
    Int: -> {((Exists i). ((Exists j). (((F || ((!fresh1[i] && T) && (0 == \
    1))) || ((fresh1[i] && T) && (0 == 0))) && ((F || ((!fresh1[j] && T) && \
    (1 == 1))) || ((fresh1[j] && T) && (1 == 0))))))} 0 {((Exists i). \
    ((Exists j). (((F || ((!fresh1[i] && T) && (0 == 1))) || ((fresh1[i] && \
    T) && (0 == e_t[i]))) && ((F || ((!fresh1[j] && T) && (1 == 1))) || \
    ((fresh1[j] && T) && (1 == e_t[j]))))))}\n\
    Assign: {((Exists i). ((Exists j). (((F || ((!fresh1[i] && T) && (0 == \
    1))) || ((fresh1[i] && T) && (0 == 0))) && ((F || ((!fresh1[j] && T) && \
    (1 == 1))) || ((fresh1[j] && T) && (1 == 0))))))} 0 {((Exists i). \
    ((Exists j). (((F || ((!fresh1[i] && T) && (0 == 1))) || ((fresh1[i] && \
    T) && (0 == e_t[i]))) && ((F || ((!fresh1[j] && T) && (1 == 1))) || \
    ((fresh1[j] && T) && (1 == e_t[j]))))))} -> {((Exists i). ((Exists j). \
    (((F || ((!fresh1[i] && T) && (0 == 1))) || ((fresh1[i] && T) && (0 == \
    0))) && ((F || ((!fresh1[j] && T) && (1 == 1))) || ((fresh1[j] && T) && \
    (1 == 0))))))} (x := 0) {((Exists i). ((Exists j). (((F || ((!fresh1[i] \
    && T) && (0 == 1))) || ((fresh1[i] && T) && (0 == x[i]))) && ((F || \
    ((!fresh1[j] && T) && (1 == 1))) || ((fresh1[j] && T) && (1 == x[j]))))))}\n\
    Int: -> {((Exists i). ((Exists j). (((F || ((!fresh1[i] && T) && (0 == \
    1))) || ((fresh1[i] && T) && (0 == fresh3[i]))) && ((F || ((!fresh1[j] && \
    T) && (1 == 1))) || ((fresh1[j] && T) && (1 == fresh3[j]))))))} 1 \
    {((Exists i). ((Exists j). (((F || ((!fresh1[i] && T) && (0 == e_t[i]))) \
    || ((fresh1[i] && T) && (0 == fresh3[i]))) && ((F || ((!fresh1[j] && T) \
    && (1 == e_t[j]))) || ((fresh1[j] && T) && (1 == fresh3[j]))))))}\n\
    Assign: {((Exists i). ((Exists j). (((F || ((!fresh1[i] && T) && (0 == \
    1))) || ((fresh1[i] && T) && (0 == fresh3[i]))) && ((F || ((!fresh1[j] && \
    T) && (1 == 1))) || ((fresh1[j] && T) && (1 == fresh3[j]))))))} 1 \
    {((Exists i). ((Exists j). (((F || ((!fresh1[i] && T) && (0 == e_t[i]))) \
    || ((fresh1[i] && T) && (0 == fresh3[i]))) && ((F || ((!fresh1[j] && T) \
    && (1 == e_t[j]))) || ((fresh1[j] && T) && (1 == fresh3[j]))))))} -> \
    {((Exists i). ((Exists j). (((F || ((!fresh1[i] && T) && (0 == 1))) || \
    ((fresh1[i] && T) && (0 == fresh3[i]))) && ((F || ((!fresh1[j] && T) && \
    (1 == 1))) || ((fresh1[j] && T) && (1 == fresh3[j]))))))} (x := 1) \
    {((Exists i). ((Exists j). (((F || ((!fresh1[i] && T) && (0 == x[i]))) || \
    ((fresh1[i] && T) && (0 == fresh3[i]))) && ((F || ((!fresh1[j] && T) && \
    (1 == x[j]))) || ((fresh1[j] && T) && (1 == fresh3[j]))))))}\n\
    ITE: {((Exists i). ((Exists j). (((F || ((!(1 == x[i]) && T) && (0 == \
    1))) || (((1 == x[i]) && T) && (0 == 0))) && ((F || ((!(1 == x[j]) && T) \
    && (1 == 1))) || (((1 == x[j]) && T) && (1 == 0))))))} (1 = x) {((Exists \
    i). ((Exists j). (((F || ((!b_t[i] && T) && (0 == 1))) || ((b_t[i] && T) \
    && (0 == 0))) && ((F || ((!b_t[j] && T) && (1 == 1))) || ((b_t[j] && T) \
    && (1 == 0))))))}, {((Exists i). ((Exists j). (((F || ((!fresh1[i] && T) \
    && (0 == 1))) || ((fresh1[i] && T) && (0 == 0))) && ((F || ((!fresh1[j] \
    && T) && (1 == 1))) || ((fresh1[j] && T) && (1 == 0))))))} (x := 0) \
    {((Exists i). ((Exists j). (((F || ((!fresh1[i] && T) && (0 == 1))) || \
    ((fresh1[i] && T) && (0 == x[i]))) && ((F || ((!fresh1[j] && T) && (1 == \
    1))) || ((fresh1[j] && T) && (1 == x[j]))))))}, {((Exists i). ((Exists \
    j). (((F || ((!fresh1[i] && T) && (0 == 1))) || ((fresh1[i] && T) && (0 \
    == fresh3[i]))) && ((F || ((!fresh1[j] && T) && (1 == 1))) || ((fresh1[j] \
    && T) && (1 == fresh3[j]))))))} (x := 1) {((Exists i). ((Exists j). (((F \
    || ((!fresh1[i] && T) && (0 == x[i]))) || ((fresh1[i] && T) && (0 == \
    fresh3[i]))) && ((F || ((!fresh1[j] && T) && (1 == x[j]))) || ((fresh1[j] \
    && T) && (1 == fresh3[j]))))))} -> {((Exists i). ((Exists j). (((F || \
    ((!(1 == x[i]) && T) && (0 == 1))) || (((1 == x[i]) && T) && (0 == 0))) \
    && ((F || ((!(1 == x[j]) && T) && (1 == 1))) || (((1 == x[j]) && T) && (1 \
    == 0))))))} (if (1 = x) then (x := 0) else (x := 1)) {((Exists i). \
    ((Exists j). ((0 == x[i]) && (1 == x[j]))))}\n\
    Weaken: {((Exists i). ((Exists j). (((F || ((!(1 == x[i]) && T) && (0 == \
    1))) || (((1 == x[i]) && T) && (0 == 0))) && ((F || ((!(1 == x[j]) && T) \
    && (1 == 1))) || (((1 == x[j]) && T) && (1 == 0))))))} (if (1 = x) then \
    (x := 0) else (x := 1)) {((Exists i). ((Exists j). ((0 == x[i]) && (1 == \
    x[j]))))} -> {((Exists i). ((Exists j). ((0 == x[i]) && (1 == x[j]))))} \
    (if (1 = x) then (x := 0) else (x := 1)) {((Exists i). ((Exists j). ((0 \
    == x[i]) && (1 == x[j]))))}";
  (* Example 5.1 -- Commented out bc Vampire solver not powerful enough to solve, so it hangs until timeout. *)
  let rec n =
    {
      name = "N";
      expansions = lazy [ Int 1; Plus (Int 1, NNTerm n) ];
      strongest =
        lazy
          (Some
            ( [
                (AIntTermVar ET, AIntTermVar (T "e_t_2"));
                (ABoolVar BT, ABoolVar (B "b_t_2"));
              ],
              Exists
                ( IntTermVar (T "n"),
                  Forall
                    ( IntTermVar (T "i"),
                      eq_int_term
                        (ITVar (T "n"), AITVar (ITApp (ET, ITVar (T "i")))) )
                ) ));
    }
  in
  let rec s =
    {
      name = "S";
      expansions =
        lazy
          [
            ITE (Equals (Numeric (Var "y"), Numeric (NNTerm n)), Assign ("x", NNTerm n), SNTerm s);
            (* Assign ("x", NNTerm n); *)
          ];
      strongest =
        lazy
          (Some
            ( [
                (AIntTermVar ET, AIntTermVar (T "e_t_2"));
                (ABoolVar BT, ABoolVar (B "b_t_2"));
                (AIntTermVar (T "x"), AIntTermVar (T "x_2"));
              ],
              Exists
                ( IntTermVar (T "n"),
                  Exists
                    ( IntTermVar (T "m"),
                      Forall
                        ( IntTermVar (T "i"),
                          Implies
                            ( less_int_term
                                ( ITVar (T "n"),
                                  AITVar (ITApp (T "y", ITVar (T "i"))) ),
                              eq_int_term
                                ( ITVar (T "m"),
                                  AITVar (ITApp (T "x", ITVar (T "i"))) ) ) )
                    ) ) ));
    }
  in
  check_proof_no_hole_vector_state
    {
      pre =
        Forall
          ( IntTermVar (T "i"),
            And
              ( eq_int_term
                  (ITVar (T "i"), AITVar (ITApp (T "y", ITVar (T "i")))),
                eq_int_term (Int (-1), AITVar (ITApp (T "x", ITVar (T "i")))) )
          );
      prog = Stmt (SNTerm s);
      post =
        Exists
          ( IntTermVar (T "i"),
            Not
              (eq_int_term
                ( AITVar (ITApp (T "y", ITVar (T "i"))),
                  AITVar (ITApp (T "x", ITVar (T "i"))) )) );
    }
    "Var: -> [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))}] |- {((Forall fresh3). (((Exists n). ((Forall i). (n == \
    fresh3[i]))) => ((Forall fresh2). (((Exists n). ((Forall i). (n == \
    fresh2[i]))) => ((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall \
    i). (((F || ((!(y[i] == fresh3[i]) && T) && (n < y[i]))) || (((y[i] == \
    fresh3[i]) && T) && (n < y[i]))) => ((F || ((!(y[i] == fresh3[i]) && T) \
    && (m == fresh5[i]))) || (((y[i] == fresh3[i]) && T) && (m == \
    fresh2[i])))))))))))))} y {((Forall fresh3). (((Exists n). ((Forall i). \
    (n == fresh3[i]))) => ((Forall fresh2). (((Exists n). ((Forall i). (n == \
    fresh2[i]))) => ((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall \
    i). (((F || ((!(e_t[i] == fresh3[i]) && T) && (n < y[i]))) || (((e_t[i] \
    == fresh3[i]) && T) && (n < y[i]))) => ((F || ((!(e_t[i] == fresh3[i]) && \
    T) && (m == fresh5[i]))) || (((e_t[i] == fresh3[i]) && T) && (m == \
    fresh2[i])))))))))))))}\n\
    Int: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && ((Forall \
    i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Exists n). ((Forall \
    i). (n == 1)))} 1 {((Exists n). ((Forall i). (n == e_t[i])))}\n\
    Int: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && ((Forall \
    i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Forall fresh2). \
    (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Exists n). ((Forall \
    i). (n == (1 + fresh2[i]))))))} 1 {((Forall fresh2). (((Exists n). \
    ((Forall i). (n == fresh2[i]))) => ((Exists n). ((Forall i). (n == \
    (e_t[i] + fresh2[i]))))))}\n\
    ApplyHP: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && ((Forall \
    i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((T && ((Forall i). \
    (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N \
    MGF=((Exists n). ((Forall i). (n == e_t[i])))] {((Exists n). ((Forall i). \
    (n == e_t[i])))}\n\
    Adapt: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && ((Forall \
    i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((T && ((Forall i). \
    (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N \
    MGF=((Exists n). ((Forall i). (n == e_t[i])))] {((Exists n). ((Forall i). \
    (n == e_t[i])))} -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n \
    == e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Forall \
    fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Exists n). \
    ((Forall i). (n == (fresh1[i] + fresh2[i]))))))} [N MGF=((Exists n). \
    ((Forall i). (n == e_t[i])))] {((Exists n). ((Forall i). (n == (fresh1[i] \
    + e_t[i]))))}\n\
    Plus: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && ((Forall \
    i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Forall fresh2). \
    (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Exists n). ((Forall \
    i). (n == (1 + fresh2[i]))))))} 1 {((Forall fresh2). (((Exists n). \
    ((Forall i). (n == fresh2[i]))) => ((Exists n). ((Forall i). (n == \
    (e_t[i] + fresh2[i]))))))}, [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) \
    && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). \
    (n == e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Forall \
    fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Exists n). \
    ((Forall i). (n == (fresh1[i] + fresh2[i]))))))} [N MGF=((Exists n). \
    ((Forall i). (n == e_t[i])))] {((Exists n). ((Forall i). (n == (fresh1[i] \
    + e_t[i]))))} -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall \
    i). (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && ((Forall \
    i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Forall fresh2). \
    (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Exists n). ((Forall \
    i). (n == (1 + fresh2[i]))))))} (1 + [N MGF=((Exists n). ((Forall i). (n \
    == e_t[i])))]) {((Exists n). ((Forall i). (n == e_t[i])))}\n\
    HP: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] \
    <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == e_t[i])))] \
    {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && ((Forall i). \
    (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Exists n). ((Forall \
    i). (n == 1)))} 1 {((Exists n). ((Forall i). (n == e_t[i])))}, [{((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == e_t[i])))] {((Exists \
    n). ((Forall i). (n == e_t[i])))}, {(((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] \
    == x_2[i])))} [S MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))}] |- {((Forall fresh2). (((Exists n). ((Forall i). (n \
    == fresh2[i]))) => ((Exists n). ((Forall i). (n == (1 + fresh2[i]))))))} \
    (1 + [N MGF=((Exists n). ((Forall i). (n == e_t[i])))]) {((Exists n). \
    ((Forall i). (n == e_t[i])))} -> [{(((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] \
    == x_2[i])))} [S MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))}] |- {((T && ((Exists n). ((Forall i). (n == 1)))) && \
    ((Forall fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => \
    ((Exists n). ((Forall i). (n == (1 + fresh2[i])))))))} [N MGF=((Exists \
    n). ((Forall i). (n == e_t[i])))] {((Exists n). ((Forall i). (n == \
    e_t[i])))}\n\
    Weaken: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))}] |- {((T && ((Exists n). ((Forall i). (n == 1)))) && ((Forall \
    fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Exists n). \
    ((Forall i). (n == (1 + fresh2[i])))))))} [N MGF=((Exists n). ((Forall \
    i). (n == e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))} -> \
    [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == e_t[i])))] {((Exists \
    n). ((Forall i). (n == e_t[i])))}\n\
    Adapt: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))}] |- {((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall \
    i). (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))} -> [{(((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Forall \
    fresh3). (((Exists n). ((Forall i). (n == fresh3[i]))) => ((Forall \
    fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Forall \
    fresh5). (((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall i). (((F || \
    ((!(fresh1[i] == fresh3[i]) && T) && (n < y[i]))) || (((fresh1[i] == \
    fresh3[i]) && T) && (n < y[i]))) => ((F || ((!(fresh1[i] == fresh3[i]) && \
    T) && (m == fresh5[i]))) || (((fresh1[i] == fresh3[i]) && T) && (m == \
    fresh2[i])))))))))))))} [N MGF=((Exists n). ((Forall i). (n == e_t[i])))] \
    {((Forall fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => \
    ((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => \
    (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall i). (((F || \
    ((!(fresh1[i] == e_t[i]) && T) && (n < y[i]))) || (((fresh1[i] == e_t[i]) \
    && T) && (n < y[i]))) => ((F || ((!(fresh1[i] == e_t[i]) && T) && (m == \
    fresh5[i]))) || (((fresh1[i] == e_t[i]) && T) && (m == \
    fresh2[i])))))))))))}\n\
    Equals: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))}] |- {((Forall fresh3). (((Exists n). ((Forall i). (n == \
    fresh3[i]))) => ((Forall fresh2). (((Exists n). ((Forall i). (n == \
    fresh2[i]))) => ((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall \
    i). (((F || ((!(y[i] == fresh3[i]) && T) && (n < y[i]))) || (((y[i] == \
    fresh3[i]) && T) && (n < y[i]))) => ((F || ((!(y[i] == fresh3[i]) && T) \
    && (m == fresh5[i]))) || (((y[i] == fresh3[i]) && T) && (m == \
    fresh2[i])))))))))))))} y {((Forall fresh3). (((Exists n). ((Forall i). \
    (n == fresh3[i]))) => ((Forall fresh2). (((Exists n). ((Forall i). (n == \
    fresh2[i]))) => ((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall \
    i). (((F || ((!(e_t[i] == fresh3[i]) && T) && (n < y[i]))) || (((e_t[i] \
    == fresh3[i]) && T) && (n < y[i]))) => ((F || ((!(e_t[i] == fresh3[i]) && \
    T) && (m == fresh5[i]))) || (((e_t[i] == fresh3[i]) && T) && (m == \
    fresh2[i])))))))))))))}, [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} \
    [S MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))}] |- {((Forall fresh3). (((Exists n). ((Forall i). (n == \
    fresh3[i]))) => ((Forall fresh2). (((Exists n). ((Forall i). (n == \
    fresh2[i]))) => ((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall \
    i). (((F || ((!(fresh1[i] == fresh3[i]) && T) && (n < y[i]))) || \
    (((fresh1[i] == fresh3[i]) && T) && (n < y[i]))) => ((F || ((!(fresh1[i] \
    == fresh3[i]) && T) && (m == fresh5[i]))) || (((fresh1[i] == fresh3[i]) \
    && T) && (m == fresh2[i])))))))))))))} [N MGF=((Exists n). ((Forall i). \
    (n == e_t[i])))] {((Forall fresh2). (((Exists n). ((Forall i). (n == \
    fresh2[i]))) => ((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall \
    i). (((F || ((!(fresh1[i] == e_t[i]) && T) && (n < y[i]))) || \
    (((fresh1[i] == e_t[i]) && T) && (n < y[i]))) => ((F || ((!(fresh1[i] == \
    e_t[i]) && T) && (m == fresh5[i]))) || (((fresh1[i] == e_t[i]) && T) && \
    (m == fresh2[i])))))))))))} -> [{(((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] \
    == x_2[i])))} [S MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))}] |- {((Forall fresh3). (((Exists n). ((Forall i). (n \
    == fresh3[i]))) => ((Forall fresh2). (((Exists n). ((Forall i). (n == \
    fresh2[i]))) => ((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall \
    i). (((F || ((!(y[i] == fresh3[i]) && T) && (n < y[i]))) || (((y[i] == \
    fresh3[i]) && T) && (n < y[i]))) => ((F || ((!(y[i] == fresh3[i]) && T) \
    && (m == fresh5[i]))) || (((y[i] == fresh3[i]) && T) && (m == \
    fresh2[i])))))))))))))} (y = [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))]) {((Forall fresh2). (((Exists n). ((Forall i). (n == \
    fresh2[i]))) => ((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall \
    i). (((F || ((!b_t[i] && T) && (n < y[i]))) || ((b_t[i] && T) && (n < \
    y[i]))) => ((F || ((!b_t[i] && T) && (m == fresh5[i]))) || ((b_t[i] && T) \
    && (m == fresh2[i])))))))))))}\n\
    Int: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && ((Forall \
    i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Exists n). ((Forall \
    i). (n == 1)))} 1 {((Exists n). ((Forall i). (n == e_t[i])))}\n\
    Int: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && ((Forall \
    i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Forall fresh2). \
    (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Exists n). ((Forall \
    i). (n == (1 + fresh2[i]))))))} 1 {((Forall fresh2). (((Exists n). \
    ((Forall i). (n == fresh2[i]))) => ((Exists n). ((Forall i). (n == \
    (e_t[i] + fresh2[i]))))))}\n\
    ApplyHP: -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && ((Forall \
    i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((T && ((Forall i). \
    (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N \
    MGF=((Exists n). ((Forall i). (n == e_t[i])))] {((Exists n). ((Forall i). \
    (n == e_t[i])))}\n\
    Adapt: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && ((Forall \
    i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((T && ((Forall i). \
    (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N \
    MGF=((Exists n). ((Forall i). (n == e_t[i])))] {((Exists n). ((Forall i). \
    (n == e_t[i])))} -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && \
    ((Forall i). (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n \
    == e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Forall \
    fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Exists n). \
    ((Forall i). (n == (fresh1[i] + fresh2[i]))))))} [N MGF=((Exists n). \
    ((Forall i). (n == e_t[i])))] {((Exists n). ((Forall i). (n == (fresh1[i] \
    + e_t[i]))))}\n\
    Plus: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && ((Forall \
    i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Forall fresh2). \
    (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Exists n). ((Forall \
    i). (n == (1 + fresh2[i]))))))} 1 {((Forall fresh2). (((Exists n). \
    ((Forall i). (n == fresh2[i]))) => ((Exists n). ((Forall i). (n == \
    (e_t[i] + fresh2[i]))))))}, [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) \
    && ((Forall i). (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). \
    (n == e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Forall \
    fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Exists n). \
    ((Forall i). (n == (fresh1[i] + fresh2[i]))))))} [N MGF=((Exists n). \
    ((Forall i). (n == e_t[i])))] {((Exists n). ((Forall i). (n == (fresh1[i] \
    + e_t[i]))))} -> [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall \
    i). (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && ((Forall \
    i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Forall fresh2). \
    (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Exists n). ((Forall \
    i). (n == (1 + fresh2[i]))))))} (1 + [N MGF=((Exists n). ((Forall i). (n \
    == e_t[i])))]) {((Exists n). ((Forall i). (n == e_t[i])))}\n\
    HP: [{((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] \
    <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == e_t[i])))] \
    {((Exists n). ((Forall i). (n == e_t[i])))}, {(((T && ((Forall i). \
    (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && \
    ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). \
    ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Exists n). ((Forall \
    i). (n == 1)))} 1 {((Exists n). ((Forall i). (n == e_t[i])))}, [{((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == e_t[i])))] {((Exists \
    n). ((Forall i). (n == e_t[i])))}, {(((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] \
    == x_2[i])))} [S MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))}] |- {((Forall fresh2). (((Exists n). ((Forall i). (n \
    == fresh2[i]))) => ((Exists n). ((Forall i). (n == (1 + fresh2[i]))))))} \
    (1 + [N MGF=((Exists n). ((Forall i). (n == e_t[i])))]) {((Exists n). \
    ((Forall i). (n == e_t[i])))} -> [{(((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] \
    == x_2[i])))} [S MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))}] |- {((T && ((Exists n). ((Forall i). (n == 1)))) && \
    ((Forall fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => \
    ((Exists n). ((Forall i). (n == (1 + fresh2[i])))))))} [N MGF=((Exists \
    n). ((Forall i). (n == e_t[i])))] {((Exists n). ((Forall i). (n == \
    e_t[i])))}\n\
    Weaken: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))}] |- {((T && ((Exists n). ((Forall i). (n == 1)))) && ((Forall \
    fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Exists n). \
    ((Forall i). (n == (1 + fresh2[i])))))))} [N MGF=((Exists n). ((Forall \
    i). (n == e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))} -> \
    [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == e_t[i])))] {((Exists \
    n). ((Forall i). (n == e_t[i])))}\n\
    Adapt: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))}] |- {((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall \
    i). (b_t[i] <-> b_t_2[i])))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Exists n). ((Forall i). (n == e_t[i])))} -> [{(((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Forall \
    fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Forall \
    fresh5). (((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall i). (((F || \
    ((!fresh1[i] && T) && (n < y[i]))) || ((fresh1[i] && T) && (n < y[i]))) \
    => ((F || ((!fresh1[i] && T) && (m == fresh5[i]))) || ((fresh1[i] && T) \
    && (m == fresh2[i])))))))))))} [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))] {((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). ((n \
    < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall i). \
    (((F || ((!fresh1[i] && T) && (n < y[i]))) || ((fresh1[i] && T) && (n < \
    y[i]))) => ((F || ((!fresh1[i] && T) && (m == fresh5[i]))) || ((fresh1[i] \
    && T) && (m == e_t[i])))))))))}\n\
    Assign: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))}] |- {((Forall fresh2). (((Exists n). ((Forall i). (n == \
    fresh2[i]))) => ((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall \
    i). (((F || ((!fresh1[i] && T) && (n < y[i]))) || ((fresh1[i] && T) && (n \
    < y[i]))) => ((F || ((!fresh1[i] && T) && (m == fresh5[i]))) || \
    ((fresh1[i] && T) && (m == fresh2[i])))))))))))} [N MGF=((Exists n). \
    ((Forall i). (n == e_t[i])))] {((Forall fresh5). (((Exists n). ((Exists \
    m). ((Forall i). ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). \
    ((Exists m). ((Forall i). (((F || ((!fresh1[i] && T) && (n < y[i]))) || \
    ((fresh1[i] && T) && (n < y[i]))) => ((F || ((!fresh1[i] && T) && (m == \
    fresh5[i]))) || ((fresh1[i] && T) && (m == e_t[i])))))))))} -> [{(((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Forall \
    fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Forall \
    fresh5). (((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall i). (((F || \
    ((!fresh1[i] && T) && (n < y[i]))) || ((fresh1[i] && T) && (n < y[i]))) \
    => ((F || ((!fresh1[i] && T) && (m == fresh5[i]))) || ((fresh1[i] && T) \
    && (m == fresh2[i])))))))))))} (x := [N MGF=((Exists n). ((Forall i). (n \
    == e_t[i])))]) {((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall \
    i). (((F || ((!fresh1[i] && T) && (n < y[i]))) || ((fresh1[i] && T) && (n \
    < y[i]))) => ((F || ((!fresh1[i] && T) && (m == fresh5[i]))) || \
    ((fresh1[i] && T) && (m == x[i])))))))))}\n\
    ApplyHP: -> [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))}] |- {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall \
    i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))}\n\
    Adapt: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))}] |- {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall \
    i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))} -> [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall \
    i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))}] |- {((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall \
    i). (((F || ((!fresh1[i] && T) && (n < y[i]))) || ((fresh1[i] && T) && (n \
    < y[i]))) => ((F || ((!fresh1[i] && T) && (m == fresh5[i]))) || \
    ((fresh1[i] && T) && (m == fresh3[i])))))))))} [S MGF=((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). \
    ((Exists m). ((Forall i). (((F || ((!fresh1[i] && T) && (n < y[i]))) || \
    ((fresh1[i] && T) && (n < y[i]))) => ((F || ((!fresh1[i] && T) && (m == \
    x[i]))) || ((fresh1[i] && T) && (m == fresh3[i])))))))}\n\
    ITE: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))}] |- {((Forall fresh3). (((Exists n). ((Forall i). (n == \
    fresh3[i]))) => ((Forall fresh2). (((Exists n). ((Forall i). (n == \
    fresh2[i]))) => ((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall \
    i). (((F || ((!(y[i] == fresh3[i]) && T) && (n < y[i]))) || (((y[i] == \
    fresh3[i]) && T) && (n < y[i]))) => ((F || ((!(y[i] == fresh3[i]) && T) \
    && (m == fresh5[i]))) || (((y[i] == fresh3[i]) && T) && (m == \
    fresh2[i])))))))))))))} (y = [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))]) {((Forall fresh2). (((Exists n). ((Forall i). (n == \
    fresh2[i]))) => ((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall \
    i). (((F || ((!b_t[i] && T) && (n < y[i]))) || ((b_t[i] && T) && (n < \
    y[i]))) => ((F || ((!b_t[i] && T) && (m == fresh5[i]))) || ((b_t[i] && T) \
    && (m == fresh2[i])))))))))))}, [{(((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] \
    == x_2[i])))} [S MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))}] |- {((Forall fresh2). (((Exists n). ((Forall i). (n \
    == fresh2[i]))) => ((Forall fresh5). (((Exists n). ((Exists m). ((Forall \
    i). ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). \
    ((Forall i). (((F || ((!fresh1[i] && T) && (n < y[i]))) || ((fresh1[i] && \
    T) && (n < y[i]))) => ((F || ((!fresh1[i] && T) && (m == fresh5[i]))) || \
    ((fresh1[i] && T) && (m == fresh2[i])))))))))))} (x := [N MGF=((Exists \
    n). ((Forall i). (n == e_t[i])))]) {((Forall fresh5). (((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == fresh5[i]))))) => ((Exists \
    n). ((Exists m). ((Forall i). (((F || ((!fresh1[i] && T) && (n < y[i]))) \
    || ((fresh1[i] && T) && (n < y[i]))) => ((F || ((!fresh1[i] && T) && (m \
    == fresh5[i]))) || ((fresh1[i] && T) && (m == x[i])))))))))}, [{(((T && \
    ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] <-> \
    b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Forall \
    fresh5). (((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall i). (((F || \
    ((!fresh1[i] && T) && (n < y[i]))) || ((fresh1[i] && T) && (n < y[i]))) \
    => ((F || ((!fresh1[i] && T) && (m == fresh5[i]))) || ((fresh1[i] && T) \
    && (m == fresh3[i])))))))))} [S MGF=((Exists n). ((Exists m). ((Forall \
    i). ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). ((Forall \
    i). (((F || ((!fresh1[i] && T) && (n < y[i]))) || ((fresh1[i] && T) && (n \
    < y[i]))) => ((F || ((!fresh1[i] && T) && (m == x[i]))) || ((fresh1[i] && \
    T) && (m == fresh3[i])))))))} -> [{(((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] \
    == x_2[i])))} [S MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))}] |- {((Forall fresh3). (((Exists n). ((Forall i). (n \
    == fresh3[i]))) => ((Forall fresh2). (((Exists n). ((Forall i). (n == \
    fresh2[i]))) => ((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall \
    i). (((F || ((!(y[i] == fresh3[i]) && T) && (n < y[i]))) || (((y[i] == \
    fresh3[i]) && T) && (n < y[i]))) => ((F || ((!(y[i] == fresh3[i]) && T) \
    && (m == fresh5[i]))) || (((y[i] == fresh3[i]) && T) && (m == \
    fresh2[i])))))))))))))} (if (y = [N MGF=((Exists n). ((Forall i). (n == \
    e_t[i])))]) then (x := [N MGF=((Exists n). ((Forall i). (n == e_t[i])))]) \
    else [S MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))]) {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))}\n\
    HP: [{(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). (b_t[i] \
    <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S MGF=((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))] {((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))}] |- {((Forall \
    fresh3). (((Exists n). ((Forall i). (n == fresh3[i]))) => ((Forall \
    fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => ((Forall \
    fresh5). (((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall i). (((F || ((!(y[i] \
    == fresh3[i]) && T) && (n < y[i]))) || (((y[i] == fresh3[i]) && T) && (n \
    < y[i]))) => ((F || ((!(y[i] == fresh3[i]) && T) && (m == fresh5[i]))) || \
    (((y[i] == fresh3[i]) && T) && (m == fresh2[i])))))))))))))} (if (y = [N \
    MGF=((Exists n). ((Forall i). (n == e_t[i])))]) then (x := [N \
    MGF=((Exists n). ((Forall i). (n == e_t[i])))]) else [S MGF=((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))]) {((Exists n). \
    ((Exists m). ((Forall i). ((n < y[i]) => (m == x[i])))))} -> {(T && \
    ((Forall fresh3). (((Exists n). ((Forall i). (n == fresh3[i]))) => \
    ((Forall fresh2). (((Exists n). ((Forall i). (n == fresh2[i]))) => \
    ((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => \
    (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall i). (((F || \
    ((!(y[i] == fresh3[i]) && T) && (n < y[i]))) || (((y[i] == fresh3[i]) && \
    T) && (n < y[i]))) => ((F || ((!(y[i] == fresh3[i]) && T) && (m == \
    fresh5[i]))) || (((y[i] == fresh3[i]) && T) && (m == \
    fresh2[i]))))))))))))))} [S MGF=((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == x[i])))))}\n\
    FALSE!!!Weaken: {(T && ((Forall fresh3). (((Exists n). ((Forall i). (n == \
    fresh3[i]))) => ((Forall fresh2). (((Exists n). ((Forall i). (n == \
    fresh2[i]))) => ((Forall fresh5). (((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == fresh5[i]))))) => ((Exists n). ((Exists m). ((Forall \
    i). (((F || ((!(y[i] == fresh3[i]) && T) && (n < y[i]))) || (((y[i] == \
    fresh3[i]) && T) && (n < y[i]))) => ((F || ((!(y[i] == fresh3[i]) && T) \
    && (m == fresh5[i]))) || (((y[i] == fresh3[i]) && T) && (m == \
    fresh2[i]))))))))))))))} [S MGF=((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == x[i])))))] {((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == x[i])))))} -> {(((T && ((Forall i). (e_t[i] == \
    e_t_2[i]))) && ((Forall i). (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] \
    == x_2[i])))} [S MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))}\n\
    Adapt: {(((T && ((Forall i). (e_t[i] == e_t_2[i]))) && ((Forall i). \
    (b_t[i] <-> b_t_2[i]))) && ((Forall i). (x[i] == x_2[i])))} [S \
    MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))] {((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))} -> {((Forall fresh3). (((Exists n). ((Exists m). ((Forall i). \
    ((n < y[i]) => (m == fresh3[i]))))) => ((Exists i). !(y[i] == \
    fresh3[i]))))} [S MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) \
    => (m == x[i])))))] {((Exists i). !(y[i] == x[i]))}\n\
    Weaken: {((Forall fresh3). (((Exists n). ((Exists m). ((Forall i). ((n < \
    y[i]) => (m == fresh3[i]))))) => ((Exists i). !(y[i] == fresh3[i]))))} [S \
    MGF=((Exists n). ((Exists m). ((Forall i). ((n < y[i]) => (m == \
    x[i])))))] {((Exists i). !(y[i] == x[i]))} -> {((Forall i). ((i == y[i]) \
    && (-1 == x[i])))} [S MGF=((Exists n). ((Exists m). ((Forall i). ((n < \
    y[i]) => (m == x[i])))))] {((Exists i). !(y[i] == x[i]))}"

let test_stmt_vector_states =
  (* Assign *)
  check_proof_no_hole_vector_state
    {
      pre = False;
      prog = Stmt (Assign ("x", Plus (Int 1, Var "x")));
      post =
        Forall
          ( IntTermVar (T "i"),
            eq_int_term
              ( AITVar (ITApp (T "x", ITVar (T "i"))),
                Plus (Int 2, ITVar (T "i")) ) );
    }
    "Int: -> {((Forall i). ((1 + x[i]) == (2 + i)))} 1 {((Forall i). ((e_t[i] \
    + x[i]) == (2 + i)))}\n\
    Var: -> {((Forall i). ((fresh1[i] + x[i]) == (2 + i)))} x {((Forall i). \
    ((fresh1[i] + e_t[i]) == (2 + i)))}\n\
    Plus: {((Forall i). ((1 + x[i]) == (2 + i)))} 1 {((Forall i). ((e_t[i] + \
    x[i]) == (2 + i)))}, {((Forall i). ((fresh1[i] + x[i]) == (2 + i)))} x \
    {((Forall i). ((fresh1[i] + e_t[i]) == (2 + i)))} -> {((Forall i). ((1 + \
    x[i]) == (2 + i)))} (1 + x) {((Forall i). (e_t[i] == (2 + i)))}\n\
    Assign: {((Forall i). ((1 + x[i]) == (2 + i)))} (1 + x) {((Forall i). \
    (e_t[i] == (2 + i)))} -> {((Forall i). ((1 + x[i]) == (2 + i)))} (x := (1 \
    + x)) {((Forall i). (x[i] == (2 + i)))}\n\
    Weaken: {((Forall i). ((1 + x[i]) == (2 + i)))} (x := (1 + x)) {((Forall \
    i). (x[i] == (2 + i)))} -> {F} (x := (1 + x)) {((Forall i). (x[i] == (2 + \
    i)))}";
  (* Seq *)
  check_proof_no_hole_vector_state
    {
      pre = True;
      prog = Stmt (Seq (Assign ("x", Plus (Int 1, Int 1)), Assign ("x", Int 1)));
      post =
        Forall
          ( IntTermVar (T "i"),
            eq_int_term (AITVar (ITApp (T "x", ITVar (T "i"))), Int 1) );
    }
    "Int: -> {((Forall i). (1 == 1))} 1 {((Forall i). (1 == 1))}\n\
    Int: -> {((Forall i). (1 == 1))} 1 {((Forall i). (1 == 1))}\n\
    Plus: {((Forall i). (1 == 1))} 1 {((Forall i). (1 == 1))}, {((Forall i). \
    (1 == 1))} 1 {((Forall i). (1 == 1))} -> {((Forall i). (1 == 1))} (1 + 1) \
    {((Forall i). (1 == 1))}\n\
    Assign: {((Forall i). (1 == 1))} (1 + 1) {((Forall i). (1 == 1))} -> \
    {((Forall i). (1 == 1))} (x := (1 + 1)) {((Forall i). (1 == 1))}\n\
    Int: -> {((Forall i). (1 == 1))} 1 {((Forall i). (e_t[i] == 1))}\n\
    Assign: {((Forall i). (1 == 1))} 1 {((Forall i). (e_t[i] == 1))} -> \
    {((Forall i). (1 == 1))} (x := 1) {((Forall i). (x[i] == 1))}\n\
    Seq: {((Forall i). (1 == 1))} (x := (1 + 1)) {((Forall i). (1 == 1))}, \
    {((Forall i). (1 == 1))} (x := 1) {((Forall i). (x[i] == 1))} -> \
    {((Forall i). (1 == 1))} ((x := (1 + 1)); (x := 1)) {((Forall i). (x[i] \
    == 1))}\n\
    Weaken: {((Forall i). (1 == 1))} ((x := (1 + 1)); (x := 1)) {((Forall i). \
    (x[i] == 1))} -> {T} ((x := (1 + 1)); (x := 1)) {((Forall i). (x[i] == \
    1))}"

(* let test_bv =
   check_proof_no_hole_simple
       { pre = False; prog = Term (Bitvec (Bitv "#x0004c000")); post = False }
       "Bitv: -> {F} #x0004c000 {F}\n\
        Weaken: {F} #x0004c000 {F} -> {F} #x0004c000 {F}";
     check_proof_no_hole_simple
       {
         pre = True;
         prog = Term (Bitvec (Bitv "#x00000000"));
         post = eq_bitv_term (Bitv "#x00000000", BitvTVar ET);
       }
       "Bitv: -> {(#x00000000 == #x00000000)} #x00000000 {(#x00000000 == e_t)}\n\
        Weaken: {(#x00000000 == #x00000000)} #x00000000 {(#x00000000 == e_t)} -> \
        {T} #x00000000 {(#x00000000 == e_t)}";
     check_proof_no_hole_simple
       {
         pre = False;
         prog =
           Term
             (Bitvec
                (BitvITE
                   ( Equals (Bitvec (BitvVar "x"), Bitvec (Bitv "#x00000000")),
                     Bitv "#x00000001",
                     BitvVar "x" )));
         post = eq_bitv_term (BitvTVar ET, BitvTVar (T "x"));
       }
       "Var: -> {(((x == #x00000000) => (#x00000001 == x)) && (!(x == #x00000000) \
        => (x == x)))} x {(((e_t == #x00000000) => (#x00000001 == x)) && (!(e_t \
        == #x00000000) => (x == x)))}\n\
        Bitv: -> {(((fresh1 == #x00000000) => (#x00000001 == x)) && (!(fresh1 == \
        #x00000000) => (x == x)))} #x00000000 {(((fresh1 == e_t) => (#x00000001 \
        == x)) && (!(fresh1 == e_t) => (x == x)))}\n\
        Equals: {(((x == #x00000000) => (#x00000001 == x)) && (!(x == #x00000000) \
        => (x == x)))} x {(((e_t == #x00000000) => (#x00000001 == x)) && (!(e_t \
        == #x00000000) => (x == x)))}, {(((fresh1 == #x00000000) => (#x00000001 \
        == x)) && (!(fresh1 == #x00000000) => (x == x)))} #x00000000 {(((fresh1 \
        == e_t) => (#x00000001 == x)) && (!(fresh1 == e_t) => (x == x)))} -> \
        {(((x == #x00000000) => (#x00000001 == x)) && (!(x == #x00000000) => (x \
        == x)))} (x = #x00000000) {((b_t => (#x00000001 == x)) && (!b_t => (x == \
        x)))}\n\
        Bitv: -> {(#x00000001 == x)} #x00000001 {(e_t == x)}\n\
        Var: -> {(x == x)} x {(e_t == x)}\n\
        ITE: {(((x == #x00000000) => (#x00000001 == x)) && (!(x == #x00000000) => \
        (x == x)))} (x = #x00000000) {((b_t => (#x00000001 == x)) && (!b_t => (x \
        == x)))}, {(#x00000001 == x)} #x00000001 {(e_t == x)}, {(x == x)} x {(e_t \
        == x)} -> {(((x == #x00000000) => (#x00000001 == x)) && (!(x == \
        #x00000000) => (x == x)))} (if (x = #x00000000) then #x00000001 else x) \
        {(e_t == x)}\n\
        Weaken: {(((x == #x00000000) => (#x00000001 == x)) && (!(x == #x00000000) \
        => (x == x)))} (if (x = #x00000000) then #x00000001 else x) {(e_t == x)} \
        -> {F} (if (x = #x00000000) then #x00000001 else x) {(e_t == x)}";

     let rec b =
       {
         name = "B";
         expansions =
           lazy
             [
               Equals (Bitvec (BitvVar "x"), Bitvec (Bitv "#x00000001"));
               Or
                 ( BNTerm b,
                   Equals (Bitvec (BitvVar "x"), Bitvec (Bitv "#x00000000")) );
             ];
         strongest =
           lazy
             (Some
                ( [
                    (BitvTermVar ET, BitvTermVar (T "e_t_2"));
                    (BoolVar BT, BoolVar (B "b_t_2"));
                  ],
                  Implies
                    (eq_bitv_term (BitvTVar (T "x"), Bitv "#x00000001"), BVar BT)
                ));
       }
     in
     check_proof_no_hole_simple
       {
         pre = eq_bitv_term (BitvTVar (T "x"), Bitv "#x00000001");
         prog = Boolean (BNTerm b);
         post = BVar BT;
       }
       "Var: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == \
        #x00000001) => b_t)] {((x == #x00000001) => b_t)}] |- {((x == #x00000001) \
        => (x == #x00000001))} x {((x == #x00000001) => (e_t == #x00000001))}\n\
        Bitv: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == \
        #x00000001) => b_t)] {((x == #x00000001) => b_t)}] |- {((x == #x00000001) \
        => (fresh1 == #x00000001))} #x00000001 {((x == #x00000001) => (fresh1 == \
        e_t))}\n\
        Equals: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == \
        #x00000001) => b_t)] {((x == #x00000001) => b_t)}] |- {((x == #x00000001) \
        => (x == #x00000001))} x {((x == #x00000001) => (e_t == #x00000001))}, \
        [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == #x00000001) \
        => b_t)] {((x == #x00000001) => b_t)}] |- {((x == #x00000001) => (fresh1 \
        == #x00000001))} #x00000001 {((x == #x00000001) => (fresh1 == e_t))} -> \
        [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == #x00000001) \
        => b_t)] {((x == #x00000001) => b_t)}] |- {((x == #x00000001) => (x == \
        #x00000001))} (x = #x00000001) {((x == #x00000001) => b_t)}\n\
        ApplyHP: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == \
        #x00000001) => b_t)] {((x == #x00000001) => b_t)}] |- {((T && (e_t == \
        e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == #x00000001) => b_t)] {((x == \
        #x00000001) => b_t)}\n\
        Adapt: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == \
        #x00000001) => b_t)] {((x == #x00000001) => b_t)}] |- {((T && (e_t == \
        e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == #x00000001) => b_t)] {((x == \
        #x00000001) => b_t)} -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
        MGF=((x == #x00000001) => b_t)] {((x == #x00000001) => b_t)}] |- \
        {((Forall fresh2). (((x == #x00000001) => fresh2) => ((x == #x00000001) \
        => (fresh2 || (x == #x00000000)))))} [B MGF=((x == #x00000001) => b_t)] \
        {((x == #x00000001) => (b_t || (x == #x00000000)))}\n\
        Var: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == \
        #x00000001) => b_t)] {((x == #x00000001) => b_t)}] |- {((x == #x00000001) \
        => (fresh1 || (x == #x00000000)))} x {((x == #x00000001) => (fresh1 || \
        (e_t == #x00000000)))}\n\
        Bitv: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == \
        #x00000001) => b_t)] {((x == #x00000001) => b_t)}] |- {((x == #x00000001) \
        => (fresh1 || (fresh2 == #x00000000)))} #x00000000 {((x == #x00000001) => \
        (fresh1 || (fresh2 == e_t)))}\n\
        Equals: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == \
        #x00000001) => b_t)] {((x == #x00000001) => b_t)}] |- {((x == #x00000001) \
        => (fresh1 || (x == #x00000000)))} x {((x == #x00000001) => (fresh1 || \
        (e_t == #x00000000)))}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
        MGF=((x == #x00000001) => b_t)] {((x == #x00000001) => b_t)}] |- {((x == \
        #x00000001) => (fresh1 || (fresh2 == #x00000000)))} #x00000000 {((x == \
        #x00000001) => (fresh1 || (fresh2 == e_t)))} -> [{((T && (e_t == e_t_2)) \
        && (b_t <-> b_t_2))} [B MGF=((x == #x00000001) => b_t)] {((x == \
        #x00000001) => b_t)}] |- {((x == #x00000001) => (fresh1 || (x == \
        #x00000000)))} (x = #x00000000) {((x == #x00000001) => (fresh1 || b_t))}\n\
        Or: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == \
        #x00000001) => b_t)] {((x == #x00000001) => b_t)}] |- {((Forall fresh2). \
        (((x == #x00000001) => fresh2) => ((x == #x00000001) => (fresh2 || (x == \
        #x00000000)))))} [B MGF=((x == #x00000001) => b_t)] {((x == #x00000001) \
        => (b_t || (x == #x00000000)))}, [{((T && (e_t == e_t_2)) && (b_t <-> \
        b_t_2))} [B MGF=((x == #x00000001) => b_t)] {((x == #x00000001) => b_t)}] \
        |- {((x == #x00000001) => (fresh1 || (x == #x00000000)))} (x = \
        #x00000000) {((x == #x00000001) => (fresh1 || b_t))} -> [{((T && (e_t == \
        e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == #x00000001) => b_t)] {((x == \
        #x00000001) => b_t)}] |- {((Forall fresh2). (((x == #x00000001) => \
        fresh2) => ((x == #x00000001) => (fresh2 || (x == #x00000000)))))} ([B \
        MGF=((x == #x00000001) => b_t)] || (x = #x00000000)) {((x == #x00000001) \
        => b_t)}\n\
        HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == \
        #x00000001) => b_t)] {((x == #x00000001) => b_t)}] |- {((x == #x00000001) \
        => (x == #x00000001))} (x = #x00000001) {((x == #x00000001) => b_t)}, \
        [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == #x00000001) \
        => b_t)] {((x == #x00000001) => b_t)}] |- {((Forall fresh2). (((x == \
        #x00000001) => fresh2) => ((x == #x00000001) => (fresh2 || (x == \
        #x00000000)))))} ([B MGF=((x == #x00000001) => b_t)] || (x = #x00000000)) \
        {((x == #x00000001) => b_t)} -> {((T && ((x == #x00000001) => (x == \
        #x00000001))) && ((Forall fresh2). (((x == #x00000001) => fresh2) => ((x \
        == #x00000001) => (fresh2 || (x == #x00000000))))))} [B MGF=((x == \
        #x00000001) => b_t)] {((x == #x00000001) => b_t)}\n\
        Weaken: {((T && ((x == #x00000001) => (x == #x00000001))) && ((Forall \
        fresh2). (((x == #x00000001) => fresh2) => ((x == #x00000001) => (fresh2 \
        || (x == #x00000000))))))} [B MGF=((x == #x00000001) => b_t)] {((x == \
        #x00000001) => b_t)} -> {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
        MGF=((x == #x00000001) => b_t)] {((x == #x00000001) => b_t)}\n\
        Adapt: {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == \
        #x00000001) => b_t)] {((x == #x00000001) => b_t)} -> {((Forall fresh2). \
        (((x == #x00000001) => fresh2) => fresh2))} [B MGF=((x == #x00000001) => \
        b_t)] {b_t}\n\
        Weaken: {((Forall fresh2). (((x == #x00000001) => fresh2) => fresh2))} [B \
        MGF=((x == #x00000001) => b_t)] {b_t} -> {(x == #x00000001)} [B MGF=((x \
        == #x00000001) => b_t)] {b_t}";

     (* One Boolean Hole *)
     let rec b =
          {
            name = "B";
            expansions =
              lazy
                [
                  Equals (Bitvec (BitvVar "x"), Bitvec (Bitv "#x00000001"));
                  Or
                    ( BNTerm b,
                      Equals (Bitvec (BitvVar "x"), Bitvec (Bitv "#x00000000")) );
                ];
            strongest =
              lazy
                (Some
                   ( [
                       (BitvTermVar ET, BitvTermVar (T "e_t_2"));
                       (BoolVar BT, BoolVar (B "b_t_2"));
                     ],
                     BHole
                       ( "hole",
                         [ Boolean (BVar BT); Term (BitvTerm (BitvTVar (T "x"))) ] )
                   ));
          }
        in
        check_proof_with_hole_simple
          {
            pre = eq_bitv_term (BitvTVar (T "x"), Bitv "#x00000001");
            prog = Boolean (BNTerm b);
            post = BVar BT;
          }
          "Var: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (x == #x00000001))} x \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (e_t == #x00000001))}\n\
           Bitv: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh1 == #x00000001))} \
           #x00000001 {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh1 == e_t))}\n\
           Equals: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (x == #x00000001))} x \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (e_t == #x00000001))}, [{((T \
           && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh1 == #x00000001))} \
           #x00000001 {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh1 == e_t))} -> [{((T \
           && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (x == #x00000001))} (x = \
           #x00000001) {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}\n\
           ApplyHP: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- {((T && (e_t == \
           e_t_2)) && (b_t <-> b_t_2))} [B MGF=((#b00000000000000000000000000000000 \
           < (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}\n\
           Adapt: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- {((T && (e_t == \
           e_t_2)) && (b_t <-> b_t_2))} [B MGF=((#b00000000000000000000000000000000 \
           < (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)} -> [{((T && (e_t == \
           e_t_2)) && (b_t <-> b_t_2))} [B MGF=((#b00000000000000000000000000000000 \
           < (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- {((Forall fresh2). \
           (((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || fresh2) => \
           ((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh2 || (x == \
           #x00000000)))))} [B MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (b_t || (x == #x00000000)))}\n\
           Var: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh1 || (x == \
           #x00000000)))} x {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh1 || (e_t == \
           #x00000000)))}\n\
           Bitv: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh1 || (fresh2 == \
           #x00000000)))} #x00000000 {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh1 || (fresh2 == e_t)))}\n\
           Equals: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh1 || (x == \
           #x00000000)))} x {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh1 || (e_t == \
           #x00000000)))}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh1 || (fresh2 == \
           #x00000000)))} #x00000000 {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh1 || (fresh2 == \
           e_t)))} -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh1 || (x == \
           #x00000000)))} (x = #x00000000) {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh1 || b_t))}\n\
           Or: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- {((Forall fresh2). \
           (((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || fresh2) => \
           ((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh2 || (x == \
           #x00000000)))))} [B MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (b_t || (x == \
           #x00000000)))}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh1 || (x == \
           #x00000000)))} (x = #x00000000) {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh1 || b_t))} -> [{((T \
           && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- {((Forall fresh2). \
           (((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || fresh2) => \
           ((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh2 || (x == \
           #x00000000)))))} ([B MGF=(hole (b_t, x))] || (x = #x00000000)) \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}\n\
           HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (x == #x00000001))} (x = \
           #x00000001) {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}, [{((T && (e_t == \
           e_t_2)) && (b_t <-> b_t_2))} [B MGF=((#b00000000000000000000000000000000 \
           < (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}] |- {((Forall fresh2). \
           (((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || fresh2) => \
           ((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh2 || (x == \
           #x00000000)))))} ([B MGF=(hole (b_t, x))] || (x = #x00000000)) \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)} -> {((T && \
           ((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (x == #x00000001))) && \
           ((Forall fresh2). (((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || fresh2) => \
           ((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh2 || (x == \
           #x00000000))))))} [B MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}\n\
           Weaken: {((T && ((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (x == #x00000001))) && \
           ((Forall fresh2). (((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || fresh2) => \
           ((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || (fresh2 || (x == \
           #x00000000))))))} [B MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)} -> {((T && (e_t == \
           e_t_2)) && (b_t <-> b_t_2))} [B MGF=((#b00000000000000000000000000000000 \
           < (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)}\n\
           Adapt: {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] \
           {((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)} -> {((Forall fresh2). \
           (((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || fresh2) => fresh2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] {b_t}\n\
           Weaken: {((Forall fresh2). (((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || fresh2) => fresh2))} [B \
           MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] {b_t} -> {(x == \
           #x00000001)} [B MGF=((#b00000000000000000000000000000000 < \
           (#b00000000000000000000000000000001 - x)) || b_t)] {b_t}";
  (* check_proof_no_hole_simple
     (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
        (Lexing.from_string
           "[Bitvec BIT : [#x00000001, (bvadd #x00000001 #x00000000)] : None] \
            {|true|} Bitvec Nonterm BIT {|(bv< e_t #x00000002)|}"))
     "Bitv: -> {(#x00000001 < #x00000002)} #x00000001 {(e_t < #x00000002)}\n\
      Bitv: -> {((#x00000001 + #x00000000) < #x00000002)} #x00000001 {((e_t + \
      #x00000000) < #x00000002)}\n\
      Bitv: -> {((fresh1 + #x00000000) < #x00000002)} #x00000000 {((fresh1 + \
      e_t) < #x00000002)}\n\
      BvAdd: {((#x00000001 + #x00000000) < #x00000002)} #x00000001 {((e_t + \
      #x00000000) < #x00000002)}, {((fresh1 + #x00000000) < #x00000002)} \
      #x00000000 {((fresh1 + e_t) < #x00000002)} -> {((#x00000001 + #x00000000) \
      < #x00000002)} (#x00000001 + #x00000000) {(e_t < #x00000002)}\n\
      GrmDisj: {(#x00000001 < #x00000002)} #x00000001 {(e_t < #x00000002)}, \
      {((#x00000001 + #x00000000) < #x00000002)} (#x00000001 + #x00000000) \
      {(e_t < #x00000002)} -> {((T && (#x00000001 < #x00000002)) && \
      ((#x00000001 + #x00000000) < #x00000002))} BIT {(e_t < #x00000002)}\n\
      Weaken: {((T && (#x00000001 < #x00000002)) && ((#x00000001 + #x00000000) \
      < #x00000002))} BIT {(e_t < #x00000002)} -> {T} BIT {(e_t < #x00000002)}"; *)
  (* check_proof_with_hole_finite_vec
    (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
       (Lexing.from_string
          "[Bitvec E : [x, y, (bvand Nonterm E Nonterm E)] : Some ([(ABitvec \
           e_t, ABitvec\n\
          \      e_t_2)] : (Hole : hole [ABitvec e_t, ABitvec x, ABitvec y]))]\n\
          \      {|(and (bv= x[2] #x000000f7) (and (bv= y[2] #x0000002c) (and \
           (bv= x[1] #x00000009) (bv= y[1] #x00000006))))|} Bitvec Nonterm E \
           {|(not (and (bv= e_t[1] #x0000000f) (bv= e_t[2] #x00000123)))|}"
          (* "[Bitvec E : [x, y, (bvnot Nonterm E), (bvor Nonterm E Nonterm E)] : Some ([(ABitvec e_t, ABitvec e_t_2)] : (=> (and (bv= x[2] #x000000f7) (and (bv= y[2] #x0000002c) (and (bv= x[1] #x00000009) (bv= y[1] #x00000006)))) (<-> (bv= #x00000020 (bvand e_t[1] #x00000020)) (bv= #x00000000 (bvand e_t[2] #x00000020)))))]
             {|(and (bv= x[2] #x000000f7) (and (bv= y[2] #x0000002c) (and (bv= x[1] #x00000009) (bv= y[1] #x00000006))))|} Bitvec Nonterm E {|(not (and (bv= e_t[1] #x00000000) (bv= e_t[2] #x00000024)))|}
                      " *)))
    "" *) *)

let () =
  test_axiom;
  test_not;
  test_binary;
  test_ITE;
  test_stmt;
  test_while;
  test_nonrec_nonterm;
  test_rec_nonterm_no_hole;
  test_rec_nonterm_with_hole;
  test_triple_parse;
  test_axiom_vector_states;
  test_not_vector_states;
  test_binary_vector_states;
  test_stmt_vector_states;
  test_nonrec_nonterm_vector_state;
  test_rec_nonterm_no_hole_vector_state;
  test_ITE_vector_states;
  test_bv
*)