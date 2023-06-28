type variable = BT | ET | Var of string
type t = variable

let compare = compare
let var_tostr var = match var with BT -> "b_t" | ET -> "e_t" | Var v -> v
