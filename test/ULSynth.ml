open ULSynth.Formula
open ULSynth.Program
open ULSynth.ProofRule

let check_proof trip expected =
  if not (ruleApp_tostr (prove trip) = expected) then
    print_endline (ruleApp_tostr (prove trip))


let test_axiom =
  (check_proof {pre = (False); prog = (Numeric One); post = (False)} "One: -> {F} 1 {F}\nWeaken: {F} 1 {F} -> {F} 1 {F}");
  (check_proof {pre = (True); prog = (Numeric Zero); post = (Equals ((Int 0), (TVar ET)))} "Zero: -> {(0 == 0)} 0 {(0 == e_t)}\nWeaken: {(0 == 0)} 0 {(0 == e_t)} -> {T} 0 {(0 == e_t)}");
  (check_proof {pre = (False); prog = (Boolean False); post = (BVar BT)} "False: -> {F} F {b_t}\nWeaken: {F} F {b_t} -> {F} F {b_t}");
  (check_proof {pre = (True); prog = (Boolean True); post = (BVar BT)} "True: -> {T} T {b_t}\nWeaken: {T} T {b_t} -> {T} T {b_t}");;

   
let test_not =
  (check_proof {pre = (True); prog = (Boolean (Not False)); post = (BVar BT)} "False: -> {!F} F {!b_t}\nNot: {!F} F {!b_t} -> {!F} !F {b_t}\nWeaken: {!F} !F {b_t} -> {T} !F {b_t}");;


let test_binary = 
  (* Plus *)
  (check_proof {pre = (Not True); prog = (Numeric (Plus (One, One))); post = (Equals ((TVar ET), (Int 2)))} "One: -> {((1 + 1) == 2)} 1 {((e_t + 1) == 2)}\nOne: -> {((fresh1 + 1) == 2)} 1 {((fresh1 + e_t) == 2)}\nPlus: {((1 + 1) == 2)} 1 {((e_t + 1) == 2)}, {((fresh1 + 1) == 2)} 1 {((fresh1 + e_t) == 2)} -> {((1 + 1) == 2)} (1 + 1) {(e_t == 2)}\nWeaken: {((1 + 1) == 2)} (1 + 1) {(e_t == 2)} -> {!T} (1 + 1) {(e_t == 2)}");
  (* And *)
  (check_proof {pre = (And (True, (And (True, False)))); prog = (Boolean (And (True, (And (True, False))))); post = (BVar BT)} "True: -> {(T && (T && F))} T {(b_t && (T && F))}\nTrue: -> {(fresh1 && (T && F))} T {(fresh1 && (b_t && F))}\nFalse: -> {(fresh1 && (fresh2 && F))} F {(fresh1 && (fresh2 && b_t))}\nAnd: {(fresh1 && (T && F))} T {(fresh1 && (b_t && F))}, {(fresh1 && (fresh2 && F))} F {(fresh1 && (fresh2 && b_t))} -> {(fresh1 && (T && F))} (T && F) {(fresh1 && b_t)}\nAnd: {(T && (T && F))} T {(b_t && (T && F))}, {(fresh1 && (T && F))} (T && F) {(fresh1 && b_t)} -> {(T && (T && F))} (T && (T && F)) {b_t}\nWeaken: {(T && (T && F))} (T && (T && F)) {b_t} -> {(T && (T && F))} (T && (T && F)) {b_t}");
  (* Or *)
  (check_proof {pre = (True); prog = (Boolean (And (True, (Or (True, False))))); post = (BVar BT)} "True: -> {(T && (T || F))} T {(b_t && (T || F))}\nTrue: -> {(fresh1 && (T || F))} T {(fresh1 && (b_t || F))}\nFalse: -> {(fresh1 && (fresh2 || F))} F {(fresh1 && (fresh2 || b_t))}\nOr: {(fresh1 && (T || F))} T {(fresh1 && (b_t || F))}, {(fresh1 && (fresh2 || F))} F {(fresh1 && (fresh2 || b_t))} -> {(fresh1 && (T || F))} (T || F) {(fresh1 && b_t)}\nAnd: {(T && (T || F))} T {(b_t && (T || F))}, {(fresh1 && (T || F))} (T || F) {(fresh1 && b_t)} -> {(T && (T || F))} (T && (T || F)) {b_t}\nWeaken: {(T && (T || F))} (T && (T || F)) {b_t} -> {T} (T && (T || F)) {b_t}");
  (* Equals *)
  (check_proof {pre = (Equals ((Int 0), (TVar (Var "x")))); prog = (Boolean (Equals (Zero, (Var "x")))); post = (BVar BT)} "Zero: -> {(0 == x)} 0 {(e_t == x)}\nVar: -> {(fresh1 == x)} x {(fresh1 == e_t)}\nEquals: {(0 == x)} 0 {(e_t == x)}, {(fresh1 == x)} x {(fresh1 == e_t)} -> {(0 == x)} (0 = x) {b_t}\nWeaken: {(0 == x)} (0 = x) {b_t} -> {(0 == x)} (0 = x) {b_t}");
  (* Less *)
  (check_proof {pre = (Not (Less ((Int 0), (TVar (Var "x"))))); prog = (Boolean (Less (Zero, (Var "x")))); post = (Not (BVar BT))} "Zero: -> {!(0 < x)} 0 {!(e_t < x)}\nVar: -> {!(fresh1 < x)} x {!(fresh1 < e_t)}\nLess: {!(0 < x)} 0 {!(e_t < x)}, {!(fresh1 < x)} x {!(fresh1 < e_t)} -> {!(0 < x)} (0 < x) {!b_t}\nWeaken: {!(0 < x)} (0 < x) {!b_t} -> {!(0 < x)} (0 < x) {!b_t}");;

let test_ITE = 
  (* Numeric ITE *)
  (check_proof {pre = False; prog = (Numeric (ITE ((Equals ((Var "x"), Zero)), One, Var "x"))); post = Equals((TVar ET), (TVar (Var "x")))} "Var: -> {(((x == 0) => (1 == x)) && (!(x == 0) => (x == x)))} x {(((e_t == 0) => (1 == x)) && (!(e_t == 0) => (x == x)))}\nZero: -> {(((fresh1 == 0) => (1 == x)) && (!(fresh1 == 0) => (x == x)))} 0 {(((fresh1 == e_t) => (1 == x)) && (!(fresh1 == e_t) => (x == x)))}\nEquals: {(((x == 0) => (1 == x)) && (!(x == 0) => (x == x)))} x {(((e_t == 0) => (1 == x)) && (!(e_t == 0) => (x == x)))}, {(((fresh1 == 0) => (1 == x)) && (!(fresh1 == 0) => (x == x)))} 0 {(((fresh1 == e_t) => (1 == x)) && (!(fresh1 == e_t) => (x == x)))} -> {(((x == 0) => (1 == x)) && (!(x == 0) => (x == x)))} (x = 0) {((b_t => (1 == x)) && (!b_t => (x == x)))}\nOne: -> {(1 == x)} 1 {(e_t == x)}\nVar: -> {(x == x)} x {(e_t == x)}\nITE: {(((x == 0) => (1 == x)) && (!(x == 0) => (x == x)))} (x = 0) {((b_t => (1 == x)) && (!b_t => (x == x)))}, {(1 == x)} 1 {(e_t == x)}, {(x == x)} x {(e_t == x)} -> {(((x == 0) => (1 == x)) && (!(x == 0) => (x == x)))} (if (x = 0) then 1 else x) {(e_t == x)}\nWeaken: {(((x == 0) => (1 == x)) && (!(x == 0) => (x == x)))} (if (x = 0) then 1 else x) {(e_t == x)} -> {F} (if (x = 0) then 1 else x) {(e_t == x)}");
  (* Stmt ITE *)
  (check_proof {pre = True; prog = (Stmt (ITE ((Equals (One, Var "x")), (Assign ("x", (Zero))), (Assign ("x", (One)))))); post=(Equals ((TVar (Var "x")), (Int 1)))} "One: -> {(((1 == x) => (0 == 1)) && (!(1 == x) => (1 == 1)))} 1 {(((e_t == x) => (0 == 1)) && (!(e_t == x) => (1 == 1)))}\nVar: -> {(((fresh1 == x) => (0 == 1)) && (!(fresh1 == x) => (1 == 1)))} x {(((fresh1 == e_t) => (0 == 1)) && (!(fresh1 == e_t) => (1 == 1)))}\nEquals: {(((1 == x) => (0 == 1)) && (!(1 == x) => (1 == 1)))} 1 {(((e_t == x) => (0 == 1)) && (!(e_t == x) => (1 == 1)))}, {(((fresh1 == x) => (0 == 1)) && (!(fresh1 == x) => (1 == 1)))} x {(((fresh1 == e_t) => (0 == 1)) && (!(fresh1 == e_t) => (1 == 1)))} -> {(((1 == x) => (0 == 1)) && (!(1 == x) => (1 == 1)))} (1 = x) {((b_t => (0 == 1)) && (!b_t => (1 == 1)))}\nZero: -> {(0 == 1)} 0 {(e_t == 1)}\nAssign: {(0 == 1)} 0 {(e_t == 1)} -> {(0 == 1)} (x := 0) {(x == 1)}\nOne: -> {(1 == 1)} 1 {(e_t == 1)}\nAssign: {(1 == 1)} 1 {(e_t == 1)} -> {(1 == 1)} (x := 1) {(x == 1)}\nITE: {(((1 == x) => (0 == 1)) && (!(1 == x) => (1 == 1)))} (1 = x) {((b_t => (0 == 1)) && (!b_t => (1 == 1)))}, {(0 == 1)} (x := 0) {(x == 1)}, {(1 == 1)} (x := 1) {(x == 1)} -> {(((1 == x) => (0 == 1)) && (!(1 == x) => (1 == 1)))} (if (1 = x) then (x := 0) else (x := 1)) {(x == 1)}\nFALSE!!!Weaken: {(((1 == x) => (0 == 1)) && (!(1 == x) => (1 == 1)))} (if (1 = x) then (x := 0) else (x := 1)) {(x == 1)} -> {T} (if (1 = x) then (x := 0) else (x := 1)) {(x == 1)}");;

let test_stmt =
  (* Assign *)
  (check_proof {pre = False; prog = (Stmt (Assign ("x", (Plus (One, One))))); post = (Equals ((TVar (Var "x")), (Int 2)))} "One: -> {((1 + 1) == 2)} 1 {((e_t + 1) == 2)}\nOne: -> {((fresh1 + 1) == 2)} 1 {((fresh1 + e_t) == 2)}\nPlus: {((1 + 1) == 2)} 1 {((e_t + 1) == 2)}, {((fresh1 + 1) == 2)} 1 {((fresh1 + e_t) == 2)} -> {((1 + 1) == 2)} (1 + 1) {(e_t == 2)}\nAssign: {((1 + 1) == 2)} (1 + 1) {(e_t == 2)} -> {((1 + 1) == 2)} (x := (1 + 1)) {(x == 2)}");
  (* Seq *)
  (check_proof {pre = True; prog = (Stmt (Seq ((Assign ("x", (Plus (One, One)))), (Assign ("x", (One)))))); post = (Equals ((TVar (Var "x")), (Int 1)))} "One: -> {(1 == 1)} 1 {(1 == 1)}\nOne: -> {(1 == 1)} 1 {(1 == 1)}\nPlus: {(1 == 1)} 1 {(1 == 1)}, {(1 == 1)} 1 {(1 == 1)} -> {(1 == 1)} (1 + 1) {(1 == 1)}\nAssign: {(1 == 1)} (1 + 1) {(1 == 1)} -> {(1 == 1)} (x := (1 + 1)) {(1 == 1)}\nOne: -> {(1 == 1)} 1 {(e_t == 1)}\nAssign: {(1 == 1)} 1 {(e_t == 1)} -> {(1 == 1)} (x := 1) {(x == 1)}\nSeq: {(1 == 1)} (x := (1 + 1)) {(1 == 1)}, {(1 == 1)} (x := 1) {(x == 1)} -> {(1 == 1)} ((x := (1 + 1)); (x := 1)) {(x == 1)}");;

let test_while =
  (* Stmt ITE *)
  check_proof
    {
      pre = True;
      prog = Stmt (While (False, True, Assign ("x", One)));
      post = Equals (TVar (Var "x"), Int 1);
    }
    "False: -> {(T => ((!F => (x == 1)) && (F => T)))} F {(T => ((!b_t => (x == 1)) && (b_t => T)))}\n\
    FALSE!!!Weaken: {(T => ((!F => (x == 1)) && (F => T)))} F {(T => ((!b_t => (x == 1)) && (b_t => T)))} -> {T} F {(T => ((!b_t => (x == 1)) && (b_t => T)))}\n\
    One: -> {T} 1 {T}\n\
    Assign: {T} 1 {T} -> {T} (x := 1) {T}\n\
    While: {T} F {(T => ((!b_t => (x == 1)) && (b_t => T)))}, {T} (x := 1) {T} -> {T} (while F do (Inv=T) (x := 1)) {(x == 1)}\n\
    Weaken: {T} (while F do (Inv=T) (x := 1)) {(x == 1)} -> {T} (while F do (Inv=T) (x := 1)) {(x == 1)}"

let () =
  test_axiom;
  test_not;
  test_binary;
  test_stmt;
  test_ITE;
  test_while
