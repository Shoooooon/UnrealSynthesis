open ULSynth.Formula
open ULSynth.Program
open ULSynth.ProofRule
(* open ULSynth.NonTerminal *)

let check_proof trip expected =
  let a = ruleApp_tostr (prove trip) in
  if not (compare a expected = 0) then
    print_endline (ruleApp_tostr (prove trip))

let test_axiom =
  check_proof
    { pre = False; prog = Numeric One; post = False }
    "One: -> {F} 1 {F}\nWeaken: {F} 1 {F} -> {F} 1 {F}";
  check_proof
    { pre = True; prog = Numeric Zero; post = Equals (Int 0, TVar ET) }
    "Zero: -> {(0 == 0)} 0 {(0 == e_t)}\n\
     Weaken: {(0 == 0)} 0 {(0 == e_t)} -> {T} 0 {(0 == e_t)}";
  check_proof
    { pre = False; prog = Boolean False; post = BVar BT }
    "False: -> {F} F {b_t}\nWeaken: {F} F {b_t} -> {F} F {b_t}";
  check_proof
    { pre = True; prog = Boolean True; post = BVar BT }
    "True: -> {T} T {b_t}\nWeaken: {T} T {b_t} -> {T} T {b_t}"

let test_not =
  check_proof
    { pre = True; prog = Boolean (Not False); post = BVar BT }
    "False: -> {!F} F {!b_t}\n\
     Not: {!F} F {!b_t} -> {!F} !F {b_t}\n\
     Weaken: {!F} !F {b_t} -> {T} !F {b_t}"

let test_binary =
  (* Plus *)
  check_proof
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
  check_proof
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
  check_proof
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
  check_proof
    {
      pre = Equals (Int 0, TVar (Var "x"));
      prog = Boolean (Equals (Zero, Var "x"));
      post = BVar BT;
    }
    "Zero: -> {(0 == x)} 0 {(e_t == x)}\n\
     Var: -> {(fresh1 == x)} x {(fresh1 == e_t)}\n\
     Equals: {(0 == x)} 0 {(e_t == x)}, {(fresh1 == x)} x {(fresh1 == e_t)} -> \
     {(0 == x)} (0 = x) {b_t}\n\
     Weaken: {(0 == x)} (0 = x) {b_t} -> {(0 == x)} (0 = x) {b_t}";
  (* Less *)
  check_proof
    {
      pre = Not (Less (Int 0, TVar (Var "x")));
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
  check_proof
    {
      pre = False;
      prog = Numeric (ITE (Equals (Var "x", Zero), One, Var "x"));
      post = Equals (TVar ET, TVar (Var "x"));
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
  check_proof
    {
      pre = True;
      prog =
        Stmt
          (ITE (Equals (One, Var "x"), Assign ("x", Zero), Assign ("x", One)));
      post = Equals (TVar (Var "x"), Int 1);
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
  check_proof
    {
      pre = False;
      prog = Stmt (Assign ("x", Plus (One, One)));
      post = Equals (TVar (Var "x"), Int 2);
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
  check_proof
    {
      pre = True;
      prog = Stmt (Seq (Assign ("x", Plus (One, One)), Assign ("x", One)));
      post = Equals (TVar (Var "x"), Int 1);
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
  check_proof
    {
      pre = True;
      prog = Stmt (While (False, True, Assign ("x", One)));
      post = Equals (TVar (Var "x"), Int 1);
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
  check_proof
    {
      pre = Less (TVar (Var "x"), Int 4);
      prog =
        Stmt
          (While
             ( Less (Var "x", Plus (One, Plus (One, One))),
               True,
               Assign ("x", Plus (Var "x", Plus (One, One))) ));
      post = Equals (TVar (Var "x"), Int 3);
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

  check_proof
    {
      pre =
        And
          ( Less (TVar (Var "x"), Int 5),
            Exists
              ( Var "k",
                Equals (TVar (Var "x"), Plus (TVar (Var "k"), TVar (Var "k")))
              ) );
      prog =
        Stmt
          (While
             ( Less (Var "x", Plus (One, Plus (One, One))),
               And
                 ( Less (TVar (Var "x"), Int 5),
                   Exists
                     ( Var "k",
                       Equals
                         (TVar (Var "x"), Plus (TVar (Var "k"), TVar (Var "k")))
                     ) ),
               Assign ("x", Plus (Var "x", Plus (One, One))) ));
      post = Equals (TVar (Var "x"), Int 4);
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
   check_proof
     {
       pre = True;
       prog = Numeric (NTerm {name  = "N"; expansions = [One; Plus (One, Zero)]; strongest = None});
       post = Less (TVar (ET), Int 2)
     }
     "One: -> {((1 + 0) < 2)} 1 {((e_t + 0) < 2)}\n\
     Zero: -> {((fresh1 + 0) < 2)} 0 {((fresh1 + e_t) < 2)}\n\
     Plus: {((1 + 0) < 2)} 1 {((e_t + 0) < 2)}, {((fresh1 + 0) < 2)} 0 {((fresh1 + e_t) < 2)} -> {((1 + 0) < 2)} (1 + 0) {(e_t < 2)}\n\
     One: -> {(1 < 2)} 1 {(e_t < 2)}\n\
     GrmDisj: {((1 + 0) < 2)} (1 + 0) {(e_t < 2)}, {(1 < 2)} 1 {(e_t < 2)} -> {((T && ((1 + 0) < 2)) && (1 < 2))} N {(e_t < 2)}\n\
     Weaken: {((T && ((1 + 0) < 2)) && (1 < 2))} N {(e_t < 2)} -> {T} N {(e_t < 2)}"

let () =
  test_axiom;
  test_not;
  test_binary;
  test_stmt;
  test_ITE;
  test_while;
  test_nonrec_nonterm
