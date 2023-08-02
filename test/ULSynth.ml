open Logic.Formula
open Programs.Program
open ULSynth.ProofRule
open Programs.NonTerminal

let check_proof_no_hole trip expected =
  let pf = prove trip INVS_SPECIFIED in
  let a = ruleApp_tostr pf in
  if not (compare a expected = 0) then print_endline a

let check_proof_with_hole trip expected_pf =
  let pf = prove trip HOLE_SYNTH in
  let pf_str = ruleApp_tostr pf in
  if not (compare pf_str expected_pf = 0) then print_endline pf_str

let test_axiom =
  check_proof_no_hole
    { pre = False; prog = Numeric One; post = False }
    "One: -> {F} 1 {F}\nWeaken: {F} 1 {F} -> {F} 1 {F}";
  check_proof_no_hole
    { pre = True; prog = Numeric Zero; post = Equals (Int 0, TVar ET) }
    "Zero: -> {(0 == 0)} 0 {(0 == e_t)}\n\
     Weaken: {(0 == 0)} 0 {(0 == e_t)} -> {T} 0 {(0 == e_t)}";
  check_proof_no_hole
    { pre = False; prog = Boolean False; post = BVar BT }
    "False: -> {F} F {b_t}\nWeaken: {F} F {b_t} -> {F} F {b_t}";
  check_proof_no_hole
    { pre = True; prog = Boolean True; post = BVar BT }
    "True: -> {T} T {b_t}\nWeaken: {T} T {b_t} -> {T} T {b_t}"

let test_not =
  check_proof_no_hole
    { pre = True; prog = Boolean (Not False); post = BVar BT }
    "False: -> {!F} F {!b_t}\n\
     Not: {!F} F {!b_t} -> {!F} !F {b_t}\n\
     Weaken: {!F} !F {b_t} -> {T} !F {b_t}"

let test_binary =
  (* Plus *)
  check_proof_no_hole
    {
      pre = Not True;
      prog = Numeric (Plus (One, One));
      post = Equals (TVar ET, Int 2);
    }
    "One: -> {((1 + 1) == 2)} 1 {((e_t + 1) == 2)}\n\
     One: -> {((fresh1 + 1) == 2)} 1 {((fresh1 + e_t) == 2)}\n\
     Plus: {((1 + 1) == 2)} 1 {((e_t + 1) == 2)}, {((fresh1 + 1) == 2)} 1 \
     {((fresh1 + e_t) == 2)} -> {((1 + 1) == 2)} (1 + 1) {(e_t == 2)}\n\
     Weaken: {((1 + 1) == 2)} (1 + 1) {(e_t == 2)} -> {!T} (1 + 1) {(e_t == 2)}";
  (* And *)
  check_proof_no_hole
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
  check_proof_no_hole
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
  check_proof_no_hole
    {
      pre = Equals (Int 0, TVar (T "x"));
      prog = Boolean (Equals (Zero, Var "x"));
      post = BVar BT;
    }
    "Zero: -> {(0 == x)} 0 {(e_t == x)}\n\
     Var: -> {(fresh1 == x)} x {(fresh1 == e_t)}\n\
     Equals: {(0 == x)} 0 {(e_t == x)}, {(fresh1 == x)} x {(fresh1 == e_t)} -> \
     {(0 == x)} (0 = x) {b_t}\n\
     Weaken: {(0 == x)} (0 = x) {b_t} -> {(0 == x)} (0 = x) {b_t}";
  (* Less *)
  check_proof_no_hole
    {
      pre = Not (Less (Int 0, TVar (T "x")));
      prog = Boolean (Less (Zero, Var "x"));
      post = Not (BVar BT);
    }
    "Zero: -> {!(0 < x)} 0 {!(e_t < x)}\n\
     Var: -> {!(fresh1 < x)} x {!(fresh1 < e_t)}\n\
     Less: {!(0 < x)} 0 {!(e_t < x)}, {!(fresh1 < x)} x {!(fresh1 < e_t)} -> \
     {!(0 < x)} (0 < x) {!b_t}\n\
     Weaken: {!(0 < x)} (0 < x) {!b_t} -> {!(0 < x)} (0 < x) {!b_t}"

let test_ITE =
  (* Numeric ITE *)
  check_proof_no_hole
    {
      pre = False;
      prog = Numeric (ITE (Equals (Var "x", Zero), One, Var "x"));
      post = Equals (TVar ET, TVar (T "x"));
    }
    "Var: -> {(((x == 0) => (1 == x)) && (!(x == 0) => (x == x)))} x {(((e_t \
     == 0) => (1 == x)) && (!(e_t == 0) => (x == x)))}\n\
     Zero: -> {(((fresh1 == 0) => (1 == x)) && (!(fresh1 == 0) => (x == x)))} \
     0 {(((fresh1 == e_t) => (1 == x)) && (!(fresh1 == e_t) => (x == x)))}\n\
     Equals: {(((x == 0) => (1 == x)) && (!(x == 0) => (x == x)))} x {(((e_t \
     == 0) => (1 == x)) && (!(e_t == 0) => (x == x)))}, {(((fresh1 == 0) => (1 \
     == x)) && (!(fresh1 == 0) => (x == x)))} 0 {(((fresh1 == e_t) => (1 == \
     x)) && (!(fresh1 == e_t) => (x == x)))} -> {(((x == 0) => (1 == x)) && \
     (!(x == 0) => (x == x)))} (x = 0) {((b_t => (1 == x)) && (!b_t => (x == \
     x)))}\n\
     One: -> {(1 == x)} 1 {(e_t == x)}\n\
     Var: -> {(x == x)} x {(e_t == x)}\n\
     ITE: {(((x == 0) => (1 == x)) && (!(x == 0) => (x == x)))} (x = 0) {((b_t \
     => (1 == x)) && (!b_t => (x == x)))}, {(1 == x)} 1 {(e_t == x)}, {(x == \
     x)} x {(e_t == x)} -> {(((x == 0) => (1 == x)) && (!(x == 0) => (x == \
     x)))} (if (x = 0) then 1 else x) {(e_t == x)}\n\
     Weaken: {(((x == 0) => (1 == x)) && (!(x == 0) => (x == x)))} (if (x = 0) \
     then 1 else x) {(e_t == x)} -> {F} (if (x = 0) then 1 else x) {(e_t == \
     x)}";
  (* Stmt ITE *)
  check_proof_no_hole
    {
      pre = True;
      prog =
        Stmt
          (ITE (Equals (One, Var "x"), Assign ("x", Zero), Assign ("x", One)));
      post = Equals (TVar (T "x"), Int 1);
    }
    "One: -> {(((1 == x) => (0 == 1)) && (!(1 == x) => (1 == 1)))} 1 {(((e_t \
     == x) => (0 == 1)) && (!(e_t == x) => (1 == 1)))}\n\
     Var: -> {(((fresh1 == x) => (0 == 1)) && (!(fresh1 == x) => (1 == 1)))} x \
     {(((fresh1 == e_t) => (0 == 1)) && (!(fresh1 == e_t) => (1 == 1)))}\n\
     Equals: {(((1 == x) => (0 == 1)) && (!(1 == x) => (1 == 1)))} 1 {(((e_t \
     == x) => (0 == 1)) && (!(e_t == x) => (1 == 1)))}, {(((fresh1 == x) => (0 \
     == 1)) && (!(fresh1 == x) => (1 == 1)))} x {(((fresh1 == e_t) => (0 == \
     1)) && (!(fresh1 == e_t) => (1 == 1)))} -> {(((1 == x) => (0 == 1)) && \
     (!(1 == x) => (1 == 1)))} (1 = x) {((b_t => (0 == 1)) && (!b_t => (1 == \
     1)))}\n\
     Zero: -> {(0 == 1)} 0 {(e_t == 1)}\n\
     Assign: {(0 == 1)} 0 {(e_t == 1)} -> {(0 == 1)} (x := 0) {(x == 1)}\n\
     One: -> {(1 == 1)} 1 {(e_t == 1)}\n\
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
  check_proof_no_hole
    {
      pre = False;
      prog = Stmt (Assign ("x", Plus (One, One)));
      post = Equals (TVar (T "x"), Int 2);
    }
    "One: -> {((1 + 1) == 2)} 1 {((e_t + 1) == 2)}\n\
     One: -> {((fresh1 + 1) == 2)} 1 {((fresh1 + e_t) == 2)}\n\
     Plus: {((1 + 1) == 2)} 1 {((e_t + 1) == 2)}, {((fresh1 + 1) == 2)} 1 \
     {((fresh1 + e_t) == 2)} -> {((1 + 1) == 2)} (1 + 1) {(e_t == 2)}\n\
     Assign: {((1 + 1) == 2)} (1 + 1) {(e_t == 2)} -> {((1 + 1) == 2)} (x := \
     (1 + 1)) {(x == 2)}\n\
     Weaken: {((1 + 1) == 2)} (x := (1 + 1)) {(x == 2)} -> {F} (x := (1 + 1)) \
     {(x == 2)}";
  (* Seq *)
  check_proof_no_hole
    {
      pre = True;
      prog = Stmt (Seq (Assign ("x", Plus (One, One)), Assign ("x", One)));
      post = Equals (TVar (T "x"), Int 1);
    }
    "One: -> {(1 == 1)} 1 {(1 == 1)}\n\
     One: -> {(1 == 1)} 1 {(1 == 1)}\n\
     Plus: {(1 == 1)} 1 {(1 == 1)}, {(1 == 1)} 1 {(1 == 1)} -> {(1 == 1)} (1 + \
     1) {(1 == 1)}\n\
     Assign: {(1 == 1)} (1 + 1) {(1 == 1)} -> {(1 == 1)} (x := (1 + 1)) {(1 == \
     1)}\n\
     One: -> {(1 == 1)} 1 {(e_t == 1)}\n\
     Assign: {(1 == 1)} 1 {(e_t == 1)} -> {(1 == 1)} (x := 1) {(x == 1)}\n\
     Seq: {(1 == 1)} (x := (1 + 1)) {(1 == 1)}, {(1 == 1)} (x := 1) {(x == 1)} \
     -> {(1 == 1)} ((x := (1 + 1)); (x := 1)) {(x == 1)}\n\
     Weaken: {(1 == 1)} ((x := (1 + 1)); (x := 1)) {(x == 1)} -> {T} ((x := (1 \
     + 1)); (x := 1)) {(x == 1)}"

let test_while =
  (* Bad While *)
  check_proof_no_hole
    {
      pre = True;
      prog = Stmt (While (False, True, Assign ("x", One)));
      post = Equals (TVar (T "x"), Int 1);
    }
    "False: -> {(T => ((!F => (x == 1)) && (F => T)))} F {(T => ((!b_t => (x \
     == 1)) && (b_t => T)))}\n\
     FALSE!!!Weaken: {(T => ((!F => (x == 1)) && (F => T)))} F {(T => ((!b_t \
     => (x == 1)) && (b_t => T)))} -> {T} F {(T => ((!b_t => (x == 1)) && (b_t \
     => T)))}\n\
     One: -> {T} 1 {T}\n\
     Assign: {T} 1 {T} -> {T} (x := 1) {T}\n\
     While: {T} F {(T => ((!b_t => (x == 1)) && (b_t => T)))}, {T} (x := 1) \
     {T} -> {T} (while F do (Inv=T) (x := 1)) {(x == 1)}\n\
     Weaken: {T} (while F do (Inv=T) (x := 1)) {(x == 1)} -> {T} (while F do \
     (Inv=T) (x := 1)) {(x == 1)}";
  check_proof_no_hole
    {
      pre = Less (TVar (T "x"), Int 4);
      prog =
        Stmt
          (While
             ( Less (Var "x", Plus (One, Plus (One, One))),
               True,
               Assign ("x", Plus (Var "x", Plus (One, One))) ));
      post = Equals (TVar (T "x"), Int 3);
    }
    "Var: -> {(T => ((!(x < (1 + (1 + 1))) => (x == 3)) && ((x < (1 + (1 + \
     1))) => T)))} x {(T => ((!(e_t < (1 + (1 + 1))) => (x == 3)) && ((e_t < \
     (1 + (1 + 1))) => T)))}\n\
     One: -> {(T => ((!(fresh1 < (1 + (1 + 1))) => (x == 3)) && ((fresh1 < (1 \
     + (1 + 1))) => T)))} 1 {(T => ((!(fresh1 < (e_t + (1 + 1))) => (x == 3)) \
     && ((fresh1 < (e_t + (1 + 1))) => T)))}\n\
     One: -> {(T => ((!(fresh1 < (fresh2 + (1 + 1))) => (x == 3)) && ((fresh1 \
     < (fresh2 + (1 + 1))) => T)))} 1 {(T => ((!(fresh1 < (fresh2 + (e_t + \
     1))) => (x == 3)) && ((fresh1 < (fresh2 + (e_t + 1))) => T)))}\n\
     One: -> {(T => ((!(fresh1 < (fresh2 + (fresh3 + 1))) => (x == 3)) && \
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
     One: -> {T} 1 {T}\n\
     One: -> {T} 1 {T}\n\
     Plus: {T} 1 {T}, {T} 1 {T} -> {T} (1 + 1) {T}\n\
     Plus: {T} x {T}, {T} (1 + 1) {T} -> {T} (x + (1 + 1)) {T}\n\
     Assign: {T} (x + (1 + 1)) {T} -> {T} (x := (x + (1 + 1))) {T}\n\
     While: {T} (x < (1 + (1 + 1))) {(T => ((!b_t => (x == 3)) && (b_t => \
     T)))}, {T} (x := (x + (1 + 1))) {T} -> {T} (while (x < (1 + (1 + 1))) do \
     (Inv=T) (x := (x + (1 + 1)))) {(x == 3)}\n\
     Weaken: {T} (while (x < (1 + (1 + 1))) do (Inv=T) (x := (x + (1 + 1)))) \
     {(x == 3)} -> {(x < 4)} (while (x < (1 + (1 + 1))) do (Inv=T) (x := (x + \
     (1 + 1)))) {(x == 3)}";

  check_proof_no_hole
    {
      pre =
        And
          ( Less (TVar (T "x"), Int 5),
            Exists
              ( TermVar (T "k"),
                Equals (TVar (T "x"), Plus (TVar (T "k"), TVar (T "k"))) ) );
      prog =
        Stmt
          (While
             ( Less (Var "x", Plus (One, Plus (One, One))),
               And
                 ( Less (TVar (T "x"), Int 5),
                   Exists
                     ( TermVar (T "k"),
                       Equals (TVar (T "x"), Plus (TVar (T "k"), TVar (T "k")))
                     ) ),
               Assign ("x", Plus (Var "x", Plus (One, One))) ));
      post = Equals (TVar (T "x"), Int 4);
    }
    "Var: -> {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(x < (1 + (1 + \
     1))) => (x == 4)) && ((x < (1 + (1 + 1))) => (((x + (1 + 1)) < 5) && \
     ((Exists k). ((x + (1 + 1)) == (k + k)))))))} x {(((x < 5) && ((Exists \
     k). (x == (k + k)))) => ((!(e_t < (1 + (1 + 1))) => (x == 4)) && ((e_t < \
     (1 + (1 + 1))) => (((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == \
     (k + k)))))))}\n\
     One: -> {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(fresh1 < (1 + \
     (1 + 1))) => (x == 4)) && ((fresh1 < (1 + (1 + 1))) => (((x + (1 + 1)) < \
     5) && ((Exists k). ((x + (1 + 1)) == (k + k)))))))} 1 {(((x < 5) && \
     ((Exists k). (x == (k + k)))) => ((!(fresh1 < (e_t + (1 + 1))) => (x == \
     4)) && ((fresh1 < (e_t + (1 + 1))) => (((x + (1 + 1)) < 5) && ((Exists \
     k). ((x + (1 + 1)) == (k + k)))))))}\n\
     One: -> {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(fresh1 < \
     (fresh2 + (1 + 1))) => (x == 4)) && ((fresh1 < (fresh2 + (1 + 1))) => \
     (((x + (1 + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + k)))))))} 1 \
     {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(fresh1 < (fresh2 + \
     (e_t + 1))) => (x == 4)) && ((fresh1 < (fresh2 + (e_t + 1))) => (((x + (1 \
     + 1)) < 5) && ((Exists k). ((x + (1 + 1)) == (k + k)))))))}\n\
     One: -> {(((x < 5) && ((Exists k). (x == (k + k)))) => ((!(fresh1 < \
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
     One: -> {(((fresh1 + (1 + 1)) < 5) && ((Exists k). ((fresh1 + (1 + 1)) == \
     (k + k))))} 1 {(((fresh1 + (e_t + 1)) < 5) && ((Exists k). ((fresh1 + \
     (e_t + 1)) == (k + k))))}\n\
     One: -> {(((fresh1 + (fresh2 + 1)) < 5) && ((Exists k). ((fresh1 + \
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
  check_proof_no_hole
    {
      pre = True;
      prog =
        Numeric
          (NNTerm
             {
               name = "N";
               expansions = lazy [ One; Plus (One, Zero) ];
               strongest = None;
             });
      post = Less (TVar ET, Int 2);
    }
    "One: -> {(1 < 2)} 1 {(e_t < 2)}\n\
     One: -> {((1 + 0) < 2)} 1 {((e_t + 0) < 2)}\n\
     Zero: -> {((fresh1 + 0) < 2)} 0 {((fresh1 + e_t) < 2)}\n\
     Plus: {((1 + 0) < 2)} 1 {((e_t + 0) < 2)}, {((fresh1 + 0) < 2)} 0 \
     {((fresh1 + e_t) < 2)} -> {((1 + 0) < 2)} (1 + 0) {(e_t < 2)}\n\
     GrmDisj: {(1 < 2)} 1 {(e_t < 2)}, {((1 + 0) < 2)} (1 + 0) {(e_t < 2)} -> \
     {((T && (1 < 2)) && ((1 + 0) < 2))} N {(e_t < 2)}\n\
     Weaken: {((T && (1 < 2)) && ((1 + 0) < 2))} N {(e_t < 2)} -> {T} N {(e_t \
     < 2)}";

  (* Boolean *)
  check_proof_no_hole
    {
      pre = True;
      prog =
        Boolean
          (BNTerm
             {
               name = "B";
               expansions = lazy [ True; Equals (Zero, Zero) ];
               strongest = None;
             });
      post = BVar BT;
    }
    "True: -> {T} T {b_t}\n\
     Zero: -> {(0 == 0)} 0 {(e_t == 0)}\n\
     Zero: -> {(fresh1 == 0)} 0 {(fresh1 == e_t)}\n\
     Equals: {(0 == 0)} 0 {(e_t == 0)}, {(fresh1 == 0)} 0 {(fresh1 == e_t)} -> \
     {(0 == 0)} (0 = 0) {b_t}\n\
     GrmDisj: {T} T {b_t}, {(0 == 0)} (0 = 0) {b_t} -> {((T && T) && (0 == \
     0))} B {b_t}\n\
     Weaken: {((T && T) && (0 == 0))} B {b_t} -> {T} B {b_t}";

  (* Statement *)
  check_proof_no_hole
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
                     Assign ("x", One);
                     Seq (Assign ("x", Zero), Assign ("x", One));
                   ];
               strongest = None;
             });
      post = Equals (TVar (T "x"), Int 1);
    }
    "One: -> {(1 == 1)} 1 {(e_t == 1)}\n\
     Assign: {(1 == 1)} 1 {(e_t == 1)} -> {(1 == 1)} (x := 1) {(x == 1)}\n\
     Zero: -> {(1 == 1)} 0 {(1 == 1)}\n\
     Assign: {(1 == 1)} 0 {(1 == 1)} -> {(1 == 1)} (x := 0) {(1 == 1)}\n\
     One: -> {(1 == 1)} 1 {(e_t == 1)}\n\
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
      expansions = lazy [ One; Plus (One, NNTerm n) ];
      strongest =
        Some
          ( [
              (TermVar ET, TermVar (T "e_t_2"));
              (BoolVar BT, BoolVar (B "b_t_2"));
            ],
            Less (Int 0, TVar ET) );
    }
  in
  check_proof_no_hole
    { pre = True; prog = Numeric (NNTerm n); post = Less (Int 0, TVar ET) }
    "One: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < e_t)] \
     {(0 < e_t)}] |- {(0 < 1)} 1 {(0 < e_t)}\n\
     One: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < e_t)] \
     {(0 < e_t)}] |- {((Forall fresh2). ((Forall fresh3). ((0 < fresh2) => (0 \
     < (1 + fresh2)))))} 1 {((Forall fresh2). ((Forall fresh3). ((0 < fresh2) \
     => (0 < (e_t + fresh2)))))}\n\
     ApplyHP: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < \
     e_t)] {(0 < e_t)}] |- {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N \
     MGF=(0 < e_t)] {(0 < e_t)}\n\
     Adapt: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < e_t)] \
     {(0 < e_t)}] |- {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < \
     e_t)] {(0 < e_t)} -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N \
     MGF=(0 < e_t)] {(0 < e_t)}] |- {((Forall fresh2). ((Forall fresh3). ((0 < \
     fresh2) => (0 < (fresh1 + fresh2)))))} [N MGF=(0 < e_t)] {(0 < (fresh1 + \
     e_t))}\n\
     Plus: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < e_t)] {(0 \
     < e_t)}] |- {((Forall fresh2). ((Forall fresh3). ((0 < fresh2) => (0 < (1 \
     + fresh2)))))} 1 {((Forall fresh2). ((Forall fresh3). ((0 < fresh2) => (0 \
     < (e_t + fresh2)))))}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N \
     MGF=(0 < e_t)] {(0 < e_t)}] |- {((Forall fresh2). ((Forall fresh3). ((0 < \
     fresh2) => (0 < (fresh1 + fresh2)))))} [N MGF=(0 < e_t)] {(0 < (fresh1 + \
     e_t))} -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < e_t)] \
     {(0 < e_t)}] |- {((Forall fresh2). ((Forall fresh3). ((0 < fresh2) => (0 \
     < (1 + fresh2)))))} (1 + [N MGF=(0 < e_t)]) {(0 < e_t)}\n\
     HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < e_t)] {(0 < \
     e_t)}] |- {(0 < 1)} 1 {(0 < e_t)}, [{((T && (e_t == e_t_2)) && (b_t <-> \
     b_t_2))} [N MGF=(0 < e_t)] {(0 < e_t)}] |- {((Forall fresh2). ((Forall \
     fresh3). ((0 < fresh2) => (0 < (1 + fresh2)))))} (1 + [N MGF=(0 < e_t)]) \
     {(0 < e_t)} -> {((T && (0 < 1)) && ((Forall fresh2). ((Forall fresh3). \
     ((0 < fresh2) => (0 < (1 + fresh2))))))} [N MGF=(0 < e_t)] {(0 < e_t)}\n\
     Weaken: {((T && (0 < 1)) && ((Forall fresh2). ((Forall fresh3). ((0 < \
     fresh2) => (0 < (1 + fresh2))))))} [N MGF=(0 < e_t)] {(0 < e_t)} -> {((T \
     && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < e_t)] {(0 < e_t)}\n\
     Adapt: {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(0 < e_t)] {(0 \
     < e_t)} -> {((Forall fresh1). ((Forall fresh2). ((0 < fresh1) => (0 < \
     fresh1))))} [N MGF=(0 < e_t)] {(0 < e_t)}\n\
     Weaken: {((Forall fresh1). ((Forall fresh2). ((0 < fresh1) => (0 < \
     fresh1))))} [N MGF=(0 < e_t)] {(0 < e_t)} -> {T} [N MGF=(0 < e_t)] {(0 < \
     e_t)}";

  (* Boolean *)
  let rec b =
    {
      name = "B";
      expansions =
        lazy [ Equals (Var "x", One); Or (BNTerm b, Equals (Var "x", Zero)) ];
      strongest =
        Some
          ( [
              (TermVar ET, TermVar (T "e_t_2"));
              (BoolVar BT, BoolVar (B "b_t_2"));
            ],
            Implies (Equals (TVar (T "x"), Int 1), BVar BT) );
    }
  in
  check_proof_no_hole
    {
      pre = Equals (TVar (T "x"), Int 1);
      prog = Boolean (BNTerm b);
      post = BVar BT;
    }
    "Var: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
     b_t)] {((x == 1) => b_t)}] |- {((x == 1) => (x == 1))} x {((x == 1) => \
     (e_t == 1))}\n\
     One: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
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
     b_t)}] |- {((Forall fresh1). ((Forall fresh2). (((x == 1) => fresh2) => \
     ((x == 1) => (fresh2 || (x == 0))))))} [B MGF=((x == 1) => b_t)] {((x == \
     1) => (b_t || (x == 0)))}\n\
     Var: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
     b_t)] {((x == 1) => b_t)}] |- {((x == 1) => (fresh1 || (x == 0)))} x {((x \
     == 1) => (fresh1 || (e_t == 0)))}\n\
     Zero: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) \
     => b_t)] {((x == 1) => b_t)}] |- {((x == 1) => (fresh1 || (fresh2 == \
     0)))} 0 {((x == 1) => (fresh1 || (fresh2 == e_t)))}\n\
     Equals: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
     b_t)] {((x == 1) => b_t)}] |- {((x == 1) => (fresh1 || (x == 0)))} x {((x \
     == 1) => (fresh1 || (e_t == 0)))}, [{((T && (e_t == e_t_2)) && (b_t <-> \
     b_t_2))} [B MGF=((x == 1) => b_t)] {((x == 1) => b_t)}] |- {((x == 1) => \
     (fresh1 || (fresh2 == 0)))} 0 {((x == 1) => (fresh1 || (fresh2 == e_t)))} \
     -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
     b_t)] {((x == 1) => b_t)}] |- {((x == 1) => (fresh1 || (x == 0)))} (x = \
     0) {((x == 1) => (fresh1 || b_t))}\n\
     Or: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
     b_t)] {((x == 1) => b_t)}] |- {((Forall fresh1). ((Forall fresh2). (((x \
     == 1) => fresh2) => ((x == 1) => (fresh2 || (x == 0))))))} [B MGF=((x == \
     1) => b_t)] {((x == 1) => (b_t || (x == 0)))}, [{((T && (e_t == e_t_2)) \
     && (b_t <-> b_t_2))} [B MGF=((x == 1) => b_t)] {((x == 1) => b_t)}] |- \
     {((x == 1) => (fresh1 || (x == 0)))} (x = 0) {((x == 1) => (fresh1 || \
     b_t))} -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) \
     => b_t)] {((x == 1) => b_t)}] |- {((Forall fresh1). ((Forall fresh2). \
     (((x == 1) => fresh2) => ((x == 1) => (fresh2 || (x == 0))))))} ([B \
     MGF=((x == 1) => b_t)] || (x = 0)) {((x == 1) => b_t)}\n\
     HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
     b_t)] {((x == 1) => b_t)}] |- {((x == 1) => (x == 1))} (x = 1) {((x == 1) \
     => b_t)}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) \
     => b_t)] {((x == 1) => b_t)}] |- {((Forall fresh1). ((Forall fresh2). \
     (((x == 1) => fresh2) => ((x == 1) => (fresh2 || (x == 0))))))} ([B \
     MGF=((x == 1) => b_t)] || (x = 0)) {((x == 1) => b_t)} -> {((T && ((x == \
     1) => (x == 1))) && ((Forall fresh1). ((Forall fresh2). (((x == 1) => \
     fresh2) => ((x == 1) => (fresh2 || (x == 0)))))))} [B MGF=((x == 1) => \
     b_t)] {((x == 1) => b_t)}\n\
     Weaken: {((T && ((x == 1) => (x == 1))) && ((Forall fresh1). ((Forall \
     fresh2). (((x == 1) => fresh2) => ((x == 1) => (fresh2 || (x == 0)))))))} \
     [B MGF=((x == 1) => b_t)] {((x == 1) => b_t)} -> {((T && (e_t == e_t_2)) \
     && (b_t <-> b_t_2))} [B MGF=((x == 1) => b_t)] {((x == 1) => b_t)}\n\
     Adapt: {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=((x == 1) => \
     b_t)] {((x == 1) => b_t)} -> {((Forall fresh1). ((Forall fresh2). (((x == \
     1) => fresh2) => fresh2)))} [B MGF=((x == 1) => b_t)] {b_t}\n\
     Weaken: {((Forall fresh1). ((Forall fresh2). (((x == 1) => fresh2) => \
     fresh2)))} [B MGF=((x == 1) => b_t)] {b_t} -> {(x == 1)} [B MGF=((x == 1) \
     => b_t)] {b_t}";

  (* Statement + Numeric *)
  (* This proof I have not yet hand-checked. *)
  let rec n =
    {
      name = "N";
      expansions = lazy [ One; Plus (Zero, NNTerm n) ];
      strongest =
        Some
          ( [
              (TermVar ET, TermVar (T "e_t_2"));
              (BoolVar BT, BoolVar (B "b_t_2"));
            ],
            Equals (Int 1, TVar ET) );
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
        Some
          ( [
              (TermVar ET, TermVar (T "e_t_2"));
              (BoolVar BT, BoolVar (B "b_t_2"));
              (TermVar (T "x"), TermVar (T "x_2"));
            ],
            Less (Int 0, TVar (T "x")) );
    }
  in
  check_proof_no_hole
    {
      pre = Equals (TVar (T "x"), Int 1);
      prog = Stmt (SNTerm s);
      post = Less (Int (-1), TVar (T "x"));
    }
    "One: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] \
     {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
     x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {(1 == 1)} 1 {(1 == e_t)}\n\
     Zero: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] \
     {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
     x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((Forall fresh3). \
     ((1 == fresh2) => (1 == (0 + fresh2)))))} 0 {((Forall fresh2). ((Forall \
     fresh3). ((1 == fresh2) => (1 == (e_t + fresh2)))))}\n\
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
     {((Forall fresh2). ((Forall fresh3). ((1 == fresh2) => (1 == (fresh1 + \
     fresh2)))))} [N MGF=(1 == e_t)] {(1 == (fresh1 + e_t))}\n\
     Plus: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] \
     {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
     x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((Forall fresh3). \
     ((1 == fresh2) => (1 == (0 + fresh2)))))} 0 {((Forall fresh2). ((Forall \
     fresh3). ((1 == fresh2) => (1 == (e_t + fresh2)))))}, [{((T && (e_t == \
     e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] {(1 == e_t)}, {(((T && \
     (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < \
     x)}] |- {((Forall fresh2). ((Forall fresh3). ((1 == fresh2) => (1 == \
     (fresh1 + fresh2)))))} [N MGF=(1 == e_t)] {(1 == (fresh1 + e_t))} -> \
     [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] {(1 == \
     e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((Forall fresh3). ((1 == \
     fresh2) => (1 == (0 + fresh2)))))} (0 + [N MGF=(1 == e_t)]) {(1 == e_t)}\n\
     HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] {(1 \
     == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=(0 < x)] {(0 < x)}] |- {(1 == 1)} 1 {(1 == e_t)}, [{((T && (e_t == \
     e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] {(1 == e_t)}, {(((T && \
     (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < \
     x)}] |- {((Forall fresh2). ((Forall fresh3). ((1 == fresh2) => (1 == (0 + \
     fresh2)))))} (0 + [N MGF=(1 == e_t)]) {(1 == e_t)} -> [{(((T && (e_t == \
     e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- \
     {((T && (1 == 1)) && ((Forall fresh2). ((Forall fresh3). ((1 == fresh2) \
     => (1 == (0 + fresh2))))))} [N MGF=(1 == e_t)] {(1 == e_t)}\n\
     Weaken: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=(0 < x)] {(0 < x)}] |- {((T && (1 == 1)) && ((Forall fresh2). \
     ((Forall fresh3). ((1 == fresh2) => (1 == (0 + fresh2))))))} [N MGF=(1 == \
     e_t)] {(1 == e_t)} -> [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x \
     == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((T && (e_t == e_t_2)) && (b_t \
     <-> b_t_2))} [N MGF=(1 == e_t)] {(1 == e_t)}\n\
     Adapt: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=(0 < x)] {(0 < x)}] |- {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} \
     [N MGF=(1 == e_t)] {(1 == e_t)} -> [{(((T && (e_t == e_t_2)) && (b_t <-> \
     b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh1). \
     ((Forall fresh2). ((1 == fresh1) => (0 < fresh1))))} [N MGF=(1 == e_t)] \
     {(0 < e_t)}\n\
     Assign: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh1). ((Forall fresh2). ((1 == \
     fresh1) => (0 < fresh1))))} [N MGF=(1 == e_t)] {(0 < e_t)} -> [{(((T && \
     (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < \
     x)}] |- {((Forall fresh1). ((Forall fresh2). ((1 == fresh1) => (0 < \
     fresh1))))} (x := [N MGF=(1 == e_t)]) {(0 < x)}\n\
     ApplyHP: -> [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} \
     [S MGF=(0 < x)] {(0 < x)}] |- {(((T && (e_t == e_t_2)) && (b_t <-> \
     b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}\n\
     Adapt: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=(0 < x)] {(0 < x)}] |- {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) \
     && (x == x_2))} [S MGF=(0 < x)] {(0 < x)} -> [{(((T && (e_t == e_t_2)) && \
     (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall \
     fresh1). ((Forall fresh4). ((Forall fresh5). ((0 < fresh5) => ((Forall \
     fresh2). ((Forall fresh3). ((1 == fresh2) => (0 < (fresh5 + \
     fresh2)))))))))} [S MGF=(0 < x)] {((Forall fresh2). ((Forall fresh3). ((1 \
     == fresh2) => (0 < (x + fresh2)))))}\n\
     Var: -> [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((Forall fresh3). ((1 == \
     fresh2) => (0 < (x + fresh2)))))} x {((Forall fresh2). ((Forall fresh3). \
     ((1 == fresh2) => (0 < (e_t + fresh2)))))}\n\
     One: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] \
     {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
     x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {(1 == 1)} 1 {(1 == e_t)}\n\
     Zero: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] \
     {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
     x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((Forall fresh3). \
     ((1 == fresh2) => (1 == (0 + fresh2)))))} 0 {((Forall fresh2). ((Forall \
     fresh3). ((1 == fresh2) => (1 == (e_t + fresh2)))))}\n\
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
     {((Forall fresh2). ((Forall fresh3). ((1 == fresh2) => (1 == (fresh1 + \
     fresh2)))))} [N MGF=(1 == e_t)] {(1 == (fresh1 + e_t))}\n\
     Plus: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] \
     {(1 == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
     x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((Forall fresh3). \
     ((1 == fresh2) => (1 == (0 + fresh2)))))} 0 {((Forall fresh2). ((Forall \
     fresh3). ((1 == fresh2) => (1 == (e_t + fresh2)))))}, [{((T && (e_t == \
     e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] {(1 == e_t)}, {(((T && \
     (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < \
     x)}] |- {((Forall fresh2). ((Forall fresh3). ((1 == fresh2) => (1 == \
     (fresh1 + fresh2)))))} [N MGF=(1 == e_t)] {(1 == (fresh1 + e_t))} -> \
     [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] {(1 == \
     e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((Forall fresh3). ((1 == \
     fresh2) => (1 == (0 + fresh2)))))} (0 + [N MGF=(1 == e_t)]) {(1 == e_t)}\n\
     HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] {(1 \
     == e_t)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=(0 < x)] {(0 < x)}] |- {(1 == 1)} 1 {(1 == e_t)}, [{((T && (e_t == \
     e_t_2)) && (b_t <-> b_t_2))} [N MGF=(1 == e_t)] {(1 == e_t)}, {(((T && \
     (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < \
     x)}] |- {((Forall fresh2). ((Forall fresh3). ((1 == fresh2) => (1 == (0 + \
     fresh2)))))} (0 + [N MGF=(1 == e_t)]) {(1 == e_t)} -> [{(((T && (e_t == \
     e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- \
     {((T && (1 == 1)) && ((Forall fresh2). ((Forall fresh3). ((1 == fresh2) \
     => (1 == (0 + fresh2))))))} [N MGF=(1 == e_t)] {(1 == e_t)}\n\
     Weaken: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=(0 < x)] {(0 < x)}] |- {((T && (1 == 1)) && ((Forall fresh2). \
     ((Forall fresh3). ((1 == fresh2) => (1 == (0 + fresh2))))))} [N MGF=(1 == \
     e_t)] {(1 == e_t)} -> [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x \
     == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((T && (e_t == e_t_2)) && (b_t \
     <-> b_t_2))} [N MGF=(1 == e_t)] {(1 == e_t)}\n\
     Adapt: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=(0 < x)] {(0 < x)}] |- {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} \
     [N MGF=(1 == e_t)] {(1 == e_t)} -> [{(((T && (e_t == e_t_2)) && (b_t <-> \
     b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). \
     ((Forall fresh3). ((1 == fresh2) => (0 < (fresh1 + fresh2)))))} [N MGF=(1 \
     == e_t)] {(0 < (fresh1 + e_t))}\n\
     Plus: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((Forall fresh3). ((1 == \
     fresh2) => (0 < (x + fresh2)))))} x {((Forall fresh2). ((Forall fresh3). \
     ((1 == fresh2) => (0 < (e_t + fresh2)))))}, [{(((T && (e_t == e_t_2)) && \
     (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall \
     fresh2). ((Forall fresh3). ((1 == fresh2) => (0 < (fresh1 + fresh2)))))} \
     [N MGF=(1 == e_t)] {(0 < (fresh1 + e_t))} -> [{(((T && (e_t == e_t_2)) && \
     (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}] |- {((Forall \
     fresh2). ((Forall fresh3). ((1 == fresh2) => (0 < (x + fresh2)))))} (x + \
     [N MGF=(1 == e_t)]) {(0 < e_t)}\n\
     Assign: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh2). ((Forall fresh3). ((1 == \
     fresh2) => (0 < (x + fresh2)))))} (x + [N MGF=(1 == e_t)]) {(0 < e_t)} -> \
     [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < \
     x)] {(0 < x)}] |- {((Forall fresh2). ((Forall fresh3). ((1 == fresh2) => \
     (0 < (x + fresh2)))))} (x := (x + [N MGF=(1 == e_t)])) {(0 < x)}\n\
     Seq: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh1). ((Forall fresh4). ((Forall \
     fresh5). ((0 < fresh5) => ((Forall fresh2). ((Forall fresh3). ((1 == \
     fresh2) => (0 < (fresh5 + fresh2)))))))))} [S MGF=(0 < x)] {((Forall \
     fresh2). ((Forall fresh3). ((1 == fresh2) => (0 < (x + fresh2)))))}, \
     [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < \
     x)] {(0 < x)}] |- {((Forall fresh2). ((Forall fresh3). ((1 == fresh2) => \
     (0 < (x + fresh2)))))} (x := (x + [N MGF=(1 == e_t)])) {(0 < x)} -> \
     [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < \
     x)] {(0 < x)}] |- {((Forall fresh1). ((Forall fresh4). ((Forall fresh5). \
     ((0 < fresh5) => ((Forall fresh2). ((Forall fresh3). ((1 == fresh2) => (0 \
     < (fresh5 + fresh2)))))))))} ([S MGF=(0 < x)]; (x := (x + [N MGF=(1 == \
     e_t)]))) {(0 < x)}\n\
     HP: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=(0 < x)] {(0 < x)}] |- {((Forall fresh1). ((Forall fresh2). ((1 == \
     fresh1) => (0 < fresh1))))} (x := [N MGF=(1 == e_t)]) {(0 < x)}, [{(((T \
     && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] \
     {(0 < x)}] |- {((Forall fresh1). ((Forall fresh4). ((Forall fresh5). ((0 \
     < fresh5) => ((Forall fresh2). ((Forall fresh3). ((1 == fresh2) => (0 < \
     (fresh5 + fresh2)))))))))} ([S MGF=(0 < x)]; (x := (x + [N MGF=(1 == \
     e_t)]))) {(0 < x)} -> {((T && ((Forall fresh1). ((Forall fresh2). ((1 == \
     fresh1) => (0 < fresh1))))) && ((Forall fresh1). ((Forall fresh4). \
     ((Forall fresh5). ((0 < fresh5) => ((Forall fresh2). ((Forall fresh3). \
     ((1 == fresh2) => (0 < (fresh5 + fresh2))))))))))} [S MGF=(0 < x)] {(0 < \
     x)}\n\
     Weaken: {((T && ((Forall fresh1). ((Forall fresh2). ((1 == fresh1) => (0 \
     < fresh1))))) && ((Forall fresh1). ((Forall fresh4). ((Forall fresh5). \
     ((0 < fresh5) => ((Forall fresh2). ((Forall fresh3). ((1 == fresh2) => (0 \
     < (fresh5 + fresh2))))))))))} [S MGF=(0 < x)] {(0 < x)} -> {(((T && (e_t \
     == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=(0 < x)] {(0 < x)}\n\
     Adapt: {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=(0 < x)] {(0 < x)} -> {((Forall fresh1). ((Forall fresh2). ((Forall \
     fresh3). ((0 < fresh3) => (-1 < fresh3)))))} [S MGF=(0 < x)] {(-1 < x)}\n\
     Weaken: {((Forall fresh1). ((Forall fresh2). ((Forall fresh3). ((0 < \
     fresh3) => (-1 < fresh3)))))} [S MGF=(0 < x)] {(-1 < x)} -> {(x == 1)} [S \
     MGF=(0 < x)] {(-1 < x)}"

let test_rec_nonterm_with_hole =
  (* One Boolean Hole *)
  let rec b =
    {
      name = "B";
      expansions =
        lazy [ Equals (Var "x", One); Or (BNTerm b, Equals (Var "x", Zero)) ];
      strongest =
        Some
          ( [
              (TermVar ET, TermVar (T "e_t_2"));
              (BoolVar BT, BoolVar (B "b_t_2"));
            ],
            Hole ("hole", [ Boolean (BVar BT); Term (TVar (T "x")) ]) );
    }
  in
  check_proof_with_hole
    {
      pre = Equals (TVar (T "x"), Int 1);
      prog = Boolean (BNTerm b);
      post = BVar BT;
    }
    "Var: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
     || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (x == 1))} x {(!(1 == x) \
     || (e_t == 1))}\n\
     One: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
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
     b_t)}] |- {((Forall fresh1). ((Forall fresh2). ((!(1 == x) || fresh2) => \
     (!(1 == x) || (fresh2 || (x == 0))))))} [B MGF=(!(1 == x) || b_t)] {(!(1 \
     == x) || (b_t || (x == 0)))}\n\
     Var: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
     || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (fresh1 || (x == 0)))} x \
     {(!(1 == x) || (fresh1 || (e_t == 0)))}\n\
     Zero: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
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
     b_t)] {(!(1 == x) || b_t)}] |- {((Forall fresh1). ((Forall fresh2). ((!(1 \
     == x) || fresh2) => (!(1 == x) || (fresh2 || (x == 0))))))} [B MGF=(!(1 \
     == x) || b_t)] {(!(1 == x) || (b_t || (x == 0)))}, [{((T && (e_t == \
     e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || \
     b_t)}] |- {(!(1 == x) || (fresh1 || (x == 0)))} (x = 0) {(!(1 == x) || \
     (fresh1 || b_t))} -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
     MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)}] |- {((Forall fresh1). \
     ((Forall fresh2). ((!(1 == x) || fresh2) => (!(1 == x) || (fresh2 || (x \
     == 0))))))} ([B MGF=(hole (b_t, x))] || (x = 0)) {(!(1 == x) || b_t)}\n\
     HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || \
     b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (x == 1))} (x = 1) {(!(1 == \
     x) || b_t)}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == \
     x) || b_t)] {(!(1 == x) || b_t)}] |- {((Forall fresh1). ((Forall fresh2). \
     ((!(1 == x) || fresh2) => (!(1 == x) || (fresh2 || (x == 0))))))} ([B \
     MGF=(hole (b_t, x))] || (x = 0)) {(!(1 == x) || b_t)} -> {((T && (!(1 == \
     x) || (x == 1))) && ((Forall fresh1). ((Forall fresh2). ((!(1 == x) || \
     fresh2) => (!(1 == x) || (fresh2 || (x == 0)))))))} [B MGF=(!(1 == x) || \
     b_t)] {(!(1 == x) || b_t)}\n\
     Weaken: {((T && (!(1 == x) || (x == 1))) && ((Forall fresh1). ((Forall \
     fresh2). ((!(1 == x) || fresh2) => (!(1 == x) || (fresh2 || (x == \
     0)))))))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)} -> {((T && (e_t \
     == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || \
     b_t)}\n\
     Adapt: {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || \
     b_t)] {(!(1 == x) || b_t)} -> {((Forall fresh1). ((Forall fresh2). ((!(1 \
     == x) || fresh2) => fresh2)))} [B MGF=(!(1 == x) || b_t)] {b_t}\n\
     Weaken: {((Forall fresh1). ((Forall fresh2). ((!(1 == x) || fresh2) => \
     fresh2)))} [B MGF=(!(1 == x) || b_t)] {b_t} -> {(x == 1)} [B MGF=(!(1 == \
     x) || b_t)] {b_t}";

  (* "(define-fun hole ((a_1 Bool) (a_2 Int)) Bool (or (not (= 1 a_2)) a_1))" *)

  (* Statement + Numeric *)
  (* This proof I have not yet hand-checked. *)
  let rec n =
    {
      name = "N";
      expansions = lazy [ One; Plus (Zero, NNTerm n) ];
      strongest =
        Some
          ( [
              (TermVar ET, TermVar (T "e_t_2"));
              (BoolVar BT, BoolVar (B "b_t_2"));
            ],
            Hole ("n_hole", [ Term (TVar ET) ]) );
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
        Some
          ( [
              (TermVar ET, TermVar (T "e_t_2"));
              (BoolVar BT, BoolVar (B "b_t_2"));
              (TermVar (T "x"), TermVar (T "x_2"));
            ],
            Hole ("s_hole", [ Term (TVar (T "x")) ]) );
    }
  in
  check_proof_no_hole
    {
      pre = Equals (TVar (T "x"), Int 1);
      prog = Stmt (SNTerm s);
      post = Less (Int (-1), TVar (T "x"));
    }
    "One: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
     {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
     x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {(1 == \
     1)} 1 {(e_t == 1)}\n\
     Zero: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
     {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
     x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- \
     {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((0 + fresh2) == \
     1))))} 0 {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((e_t + \
     fresh2) == 1))))}\n\
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
     ((Forall fresh3). ((fresh2 == 1) => ((fresh1 + fresh2) == 1))))} [N \
     MGF=(e_t == 1)] {((fresh1 + e_t) == 1)}\n\
     Plus: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
     {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
     x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- \
     {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((0 + fresh2) == \
     1))))} 0 {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((e_t + \
     fresh2) == 1))))}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N \
     MGF=(e_t == 1)] {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> \
     b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == \
     x))}] |- {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((fresh1 \
     + fresh2) == 1))))} [N MGF=(e_t == 1)] {((fresh1 + e_t) == 1)} -> [{((T \
     && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] {(e_t == 1)}, \
     {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < \
     x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). ((Forall \
     fresh3). ((fresh2 == 1) => ((0 + fresh2) == 1))))} (0 + [N MGF=(n_hole \
     (e_t))]) {(e_t == 1)}\n\
     HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
     {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
     x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {(1 == \
     1)} 1 {(e_t == 1)}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N \
     MGF=(e_t == 1)] {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> \
     b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == \
     x))}] |- {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((0 + \
     fresh2) == 1))))} (0 + [N MGF=(n_hole (e_t))]) {(e_t == 1)} -> [{(((T && \
     (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 \
     == x))] {((0 < x) || (0 == x))}] |- {((T && (1 == 1)) && ((Forall \
     fresh2). ((Forall fresh3). ((fresh2 == 1) => ((0 + fresh2) == 1)))))} [N \
     MGF=(e_t == 1)] {(e_t == 1)}\n\
     Weaken: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((T && (1 == 1)) \
     && ((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((0 + fresh2) == \
     1)))))} [N MGF=(e_t == 1)] {(e_t == 1)} -> [{(((T && (e_t == e_t_2)) && \
     (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) \
     || (0 == x))}] |- {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N \
     MGF=(e_t == 1)] {(e_t == 1)}\n\
     Adapt: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((T && (e_t == \
     e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] {(e_t == 1)} -> [{(((T && \
     (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 \
     == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh1). ((Forall fresh2). \
     ((fresh1 == 1) => ((0 < fresh1) || (0 == fresh1)))))} [N MGF=(e_t == 1)] \
     {((0 < e_t) || (0 == e_t))}\n\
     Assign: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh1). \
     ((Forall fresh2). ((fresh1 == 1) => ((0 < fresh1) || (0 == fresh1)))))} \
     [N MGF=(e_t == 1)] {((0 < e_t) || (0 == e_t))} -> [{(((T && (e_t == \
     e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] \
     {((0 < x) || (0 == x))}] |- {((Forall fresh1). ((Forall fresh2). ((fresh1 \
     == 1) => ((0 < fresh1) || (0 == fresh1)))))} (x := [N MGF=(n_hole \
     (e_t))]) {((0 < x) || (0 == x))}\n\
     ApplyHP: -> [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} \
     [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {(((T && (e_t \
     == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == \
     x))] {((0 < x) || (0 == x))}\n\
     Adapt: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {(((T && (e_t == \
     e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] \
     {((0 < x) || (0 == x))} -> [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) \
     && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- \
     {((Forall fresh1). ((Forall fresh4). ((Forall fresh5). (((0 < fresh5) || \
     (0 == fresh5)) => ((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => \
     ((0 < (fresh5 + fresh2)) || (0 == (fresh5 + fresh2))))))))))} [S MGF=((0 \
     < x) || (0 == x))] {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => \
     ((0 < (x + fresh2)) || (0 == (x + fresh2))))))}\n\
     Var: -> [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). \
     ((Forall fresh3). ((fresh2 == 1) => ((0 < (x + fresh2)) || (0 == (x + \
     fresh2))))))} x {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => \
     ((0 < (e_t + fresh2)) || (0 == (e_t + fresh2))))))}\n\
     One: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
     {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
     x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {(1 == \
     1)} 1 {(e_t == 1)}\n\
     Zero: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
     {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
     x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- \
     {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((0 + fresh2) == \
     1))))} 0 {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((e_t + \
     fresh2) == 1))))}\n\
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
     ((Forall fresh3). ((fresh2 == 1) => ((fresh1 + fresh2) == 1))))} [N \
     MGF=(e_t == 1)] {((fresh1 + e_t) == 1)}\n\
     Plus: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
     {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
     x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- \
     {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((0 + fresh2) == \
     1))))} 0 {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((e_t + \
     fresh2) == 1))))}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N \
     MGF=(e_t == 1)] {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> \
     b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == \
     x))}] |- {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((fresh1 \
     + fresh2) == 1))))} [N MGF=(e_t == 1)] {((fresh1 + e_t) == 1)} -> [{((T \
     && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] {(e_t == 1)}, \
     {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < \
     x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). ((Forall \
     fresh3). ((fresh2 == 1) => ((0 + fresh2) == 1))))} (0 + [N MGF=(n_hole \
     (e_t))]) {(e_t == 1)}\n\
     HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] \
     {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
     x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {(1 == \
     1)} 1 {(e_t == 1)}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N \
     MGF=(e_t == 1)] {(e_t == 1)}, {(((T && (e_t == e_t_2)) && (b_t <-> \
     b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == \
     x))}] |- {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((0 + \
     fresh2) == 1))))} (0 + [N MGF=(n_hole (e_t))]) {(e_t == 1)} -> [{(((T && \
     (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 \
     == x))] {((0 < x) || (0 == x))}] |- {((T && (1 == 1)) && ((Forall \
     fresh2). ((Forall fresh3). ((fresh2 == 1) => ((0 + fresh2) == 1)))))} [N \
     MGF=(e_t == 1)] {(e_t == 1)}\n\
     Weaken: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((T && (1 == 1)) \
     && ((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((0 + fresh2) == \
     1)))))} [N MGF=(e_t == 1)] {(e_t == 1)} -> [{(((T && (e_t == e_t_2)) && \
     (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) \
     || (0 == x))}] |- {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [N \
     MGF=(e_t == 1)] {(e_t == 1)}\n\
     Adapt: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((T && (e_t == \
     e_t_2)) && (b_t <-> b_t_2))} [N MGF=(e_t == 1)] {(e_t == 1)} -> [{(((T && \
     (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 \
     == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). ((Forall fresh3). \
     ((fresh2 == 1) => ((0 < (fresh1 + fresh2)) || (0 == (fresh1 + \
     fresh2))))))} [N MGF=(e_t == 1)] {((0 < (fresh1 + e_t)) || (0 == (fresh1 \
     + e_t)))}\n\
     Plus: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). \
     ((Forall fresh3). ((fresh2 == 1) => ((0 < (x + fresh2)) || (0 == (x + \
     fresh2))))))} x {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => \
     ((0 < (e_t + fresh2)) || (0 == (e_t + fresh2))))))}, [{(((T && (e_t == \
     e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] \
     {((0 < x) || (0 == x))}] |- {((Forall fresh2). ((Forall fresh3). ((fresh2 \
     == 1) => ((0 < (fresh1 + fresh2)) || (0 == (fresh1 + fresh2))))))} [N \
     MGF=(e_t == 1)] {((0 < (fresh1 + e_t)) || (0 == (fresh1 + e_t)))} -> \
     [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 \
     < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). \
     ((Forall fresh3). ((fresh2 == 1) => ((0 < (x + fresh2)) || (0 == (x + \
     fresh2))))))} (x + [N MGF=(n_hole (e_t))]) {((0 < e_t) || (0 == e_t))}\n\
     Assign: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). \
     ((Forall fresh3). ((fresh2 == 1) => ((0 < (x + fresh2)) || (0 == (x + \
     fresh2))))))} (x + [N MGF=(n_hole (e_t))]) {((0 < e_t) || (0 == e_t))} -> \
     [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 \
     < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh2). \
     ((Forall fresh3). ((fresh2 == 1) => ((0 < (x + fresh2)) || (0 == (x + \
     fresh2))))))} (x := (x + [N MGF=(n_hole (e_t))])) {((0 < x) || (0 == x))}\n\
     Seq: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh1). \
     ((Forall fresh4). ((Forall fresh5). (((0 < fresh5) || (0 == fresh5)) => \
     ((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((0 < (fresh5 + \
     fresh2)) || (0 == (fresh5 + fresh2))))))))))} [S MGF=((0 < x) || (0 == \
     x))] {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((0 < (x + \
     fresh2)) || (0 == (x + fresh2))))))}, [{(((T && (e_t == e_t_2)) && (b_t \
     <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 \
     == x))}] |- {((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => ((0 < \
     (x + fresh2)) || (0 == (x + fresh2))))))} (x := (x + [N MGF=(n_hole \
     (e_t))])) {((0 < x) || (0 == x))} -> [{(((T && (e_t == e_t_2)) && (b_t \
     <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 \
     == x))}] |- {((Forall fresh1). ((Forall fresh4). ((Forall fresh5). (((0 < \
     fresh5) || (0 == fresh5)) => ((Forall fresh2). ((Forall fresh3). ((fresh2 \
     == 1) => ((0 < (fresh5 + fresh2)) || (0 == (fresh5 + fresh2))))))))))} \
     ([S MGF=(s_hole (x))]; (x := (x + [N MGF=(n_hole (e_t))]))) {((0 < x) || \
     (0 == x))}\n\
     HP: [{(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}] |- {((Forall fresh1). \
     ((Forall fresh2). ((fresh1 == 1) => ((0 < fresh1) || (0 == fresh1)))))} \
     (x := [N MGF=(n_hole (e_t))]) {((0 < x) || (0 == x))}, [{(((T && (e_t == \
     e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S MGF=((0 < x) || (0 == x))] \
     {((0 < x) || (0 == x))}] |- {((Forall fresh1). ((Forall fresh4). ((Forall \
     fresh5). (((0 < fresh5) || (0 == fresh5)) => ((Forall fresh2). ((Forall \
     fresh3). ((fresh2 == 1) => ((0 < (fresh5 + fresh2)) || (0 == (fresh5 + \
     fresh2))))))))))} ([S MGF=(s_hole (x))]; (x := (x + [N MGF=(n_hole \
     (e_t))]))) {((0 < x) || (0 == x))} -> {((T && ((Forall fresh1). ((Forall \
     fresh2). ((fresh1 == 1) => ((0 < fresh1) || (0 == fresh1)))))) && \
     ((Forall fresh1). ((Forall fresh4). ((Forall fresh5). (((0 < fresh5) || \
     (0 == fresh5)) => ((Forall fresh2). ((Forall fresh3). ((fresh2 == 1) => \
     ((0 < (fresh5 + fresh2)) || (0 == (fresh5 + fresh2)))))))))))} [S MGF=((0 \
     < x) || (0 == x))] {((0 < x) || (0 == x))}\n\
     Weaken: {((T && ((Forall fresh1). ((Forall fresh2). ((fresh1 == 1) => ((0 \
     < fresh1) || (0 == fresh1)))))) && ((Forall fresh1). ((Forall fresh4). \
     ((Forall fresh5). (((0 < fresh5) || (0 == fresh5)) => ((Forall fresh2). \
     ((Forall fresh3). ((fresh2 == 1) => ((0 < (fresh5 + fresh2)) || (0 == \
     (fresh5 + fresh2)))))))))))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || \
     (0 == x))} -> {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == \
     x_2))} [S MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))}\n\
     Adapt: {(((T && (e_t == e_t_2)) && (b_t <-> b_t_2)) && (x == x_2))} [S \
     MGF=((0 < x) || (0 == x))] {((0 < x) || (0 == x))} -> {((Forall fresh1). \
     ((Forall fresh2). ((Forall fresh3). (((0 < fresh3) || (0 == fresh3)) => \
     (-1 < fresh3)))))} [S MGF=((0 < x) || (0 == x))] {(-1 < x)}\n\
     Weaken: {((Forall fresh1). ((Forall fresh2). ((Forall fresh3). (((0 < \
     fresh3) || (0 == fresh3)) => (-1 < fresh3)))))} [S MGF=((0 < x) || (0 == \
     x))] {(-1 < x)} -> {(x == 1)} [S MGF=((0 < x) || (0 == x))] {(-1 < x)}"

let test_triple_parse =
  print_endline
    (trip_tostr
       (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
          (Lexing.from_string "[] {|true|} Stmt (:= x 0) {|false|}")));
  print_endline
    (trip_tostr
       (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
          (Lexing.from_string "[] {|true|} Bool (or (= x x) (< 1 0)) {|false|}")));
  print_endline
    (trip_tostr
       (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
          (Lexing.from_string
             "[Int N : [1] : None] {|true|} Int (+ 0 1) {|false|}")));

  check_proof_no_hole
    (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
       (Lexing.from_string
          "[Int N : [1, (+ 1 0)] : None] {|true|} Int Nonterm N {|(< e_t 2)|}"))
    "One: -> {(1 < 2)} 1 {(e_t < 2)}\n\
     One: -> {((1 + 0) < 2)} 1 {((e_t + 0) < 2)}\n\
     Zero: -> {((fresh1 + 0) < 2)} 0 {((fresh1 + e_t) < 2)}\n\
     Plus: {((1 + 0) < 2)} 1 {((e_t + 0) < 2)}, {((fresh1 + 0) < 2)} 0 \
     {((fresh1 + e_t) < 2)} -> {((1 + 0) < 2)} (1 + 0) {(e_t < 2)}\n\
     GrmDisj: {(1 < 2)} 1 {(e_t < 2)}, {((1 + 0) < 2)} (1 + 0) {(e_t < 2)} -> \
     {((T && (1 < 2)) && ((1 + 0) < 2))} N {(e_t < 2)}\n\
     Weaken: {((T && (1 < 2)) && ((1 + 0) < 2))} N {(e_t < 2)} -> {T} N {(e_t \
     < 2)}";

  check_proof_with_hole
    (ULSynth.Claimparser.ultriple ULSynth.Claimlexer.read
       (Lexing.from_string
          "[Bool B : [(= x 1), (or Nonterm B (= x 0))] : Some ([(Int e_t, Int \
           e_t_2) ; (Bool b_t, Bool b_t_2)] : (Hole : hole [Bool b_t, Int x]))] {|(= x 1)|} Bool Nonterm B {|b_t|}"))
    "Var: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
     || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (x == 1))} x {(!(1 == x) \
     || (e_t == 1))}\n\
     One: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
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
     b_t)}] |- {((Forall fresh1). ((Forall fresh2). ((!(1 == x) || fresh2) => \
     (!(1 == x) || (fresh2 || (x == 0))))))} [B MGF=(!(1 == x) || b_t)] {(!(1 \
     == x) || (b_t || (x == 0)))}\n\
     Var: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
     || b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (fresh1 || (x == 0)))} x \
     {(!(1 == x) || (fresh1 || (e_t == 0)))}\n\
     Zero: -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) \
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
     b_t)] {(!(1 == x) || b_t)}] |- {((Forall fresh1). ((Forall fresh2). ((!(1 \
     == x) || fresh2) => (!(1 == x) || (fresh2 || (x == 0))))))} [B MGF=(!(1 \
     == x) || b_t)] {(!(1 == x) || (b_t || (x == 0)))}, [{((T && (e_t == \
     e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || \
     b_t)}] |- {(!(1 == x) || (fresh1 || (x == 0)))} (x = 0) {(!(1 == x) || \
     (fresh1 || b_t))} -> [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B \
     MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)}] |- {((Forall fresh1). \
     ((Forall fresh2). ((!(1 == x) || fresh2) => (!(1 == x) || (fresh2 || (x \
     == 0))))))} ([B MGF=(hole (b_t, x))] || (x = 0)) {(!(1 == x) || b_t)}\n\
     HP: [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || \
     b_t)] {(!(1 == x) || b_t)}] |- {(!(1 == x) || (x == 1))} (x = 1) {(!(1 == \
     x) || b_t)}, [{((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == \
     x) || b_t)] {(!(1 == x) || b_t)}] |- {((Forall fresh1). ((Forall fresh2). \
     ((!(1 == x) || fresh2) => (!(1 == x) || (fresh2 || (x == 0))))))} ([B \
     MGF=(hole (b_t, x))] || (x = 0)) {(!(1 == x) || b_t)} -> {((T && (!(1 == \
     x) || (x == 1))) && ((Forall fresh1). ((Forall fresh2). ((!(1 == x) || \
     fresh2) => (!(1 == x) || (fresh2 || (x == 0)))))))} [B MGF=(!(1 == x) || \
     b_t)] {(!(1 == x) || b_t)}\n\
     Weaken: {((T && (!(1 == x) || (x == 1))) && ((Forall fresh1). ((Forall \
     fresh2). ((!(1 == x) || fresh2) => (!(1 == x) || (fresh2 || (x == \
     0)))))))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || b_t)} -> {((T && (e_t \
     == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || b_t)] {(!(1 == x) || \
     b_t)}\n\
     Adapt: {((T && (e_t == e_t_2)) && (b_t <-> b_t_2))} [B MGF=(!(1 == x) || \
     b_t)] {(!(1 == x) || b_t)} -> {((Forall fresh1). ((Forall fresh2). ((!(1 \
     == x) || fresh2) => fresh2)))} [B MGF=(!(1 == x) || b_t)] {b_t}\n\
     Weaken: {((Forall fresh1). ((Forall fresh2). ((!(1 == x) || fresh2) => \
     fresh2)))} [B MGF=(!(1 == x) || b_t)] {b_t} -> {(x == 1)} [B MGF=(!(1 == \
     x) || b_t)] {b_t}"

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
  test_triple_parse
