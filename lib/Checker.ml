type checker = { form : string; func : unit -> bool }
type t = checker

let compare x y = String.compare x.form y.form
