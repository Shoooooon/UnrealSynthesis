type bitv_term_array_var = ET | T of string
type bitv_term_var = ET | T of string
type int_term_array_var = ET | T of string
type int_term_var = ET | T of string
type bool_array_var = BT | B of string
type bool_var = BT | B of string

type variable =
  | BoolVar of bool_var
  | IntTermVar of int_term_var
  | BitvTermVar of bitv_term_var
  | ABitvTermVar of bitv_term_array_var
  | ABoolVar of bool_array_var
  | AIntTermVar of int_term_array_var

(* Useful set and map modules. *)
module VS = Set.Make (struct
  type t = variable

  let compare = compare
end)

module VMap_AIT = Map.Make (struct
  type t = int_term_array_var

  let compare = compare
end)

module VMap_ABitvT = Map.Make (struct
  type t = bitv_term_array_var

  let compare = compare
end)

type vmaps = {
  int_map : int_term_array_var VMap_AIT.t;
  bitv_map : bitv_term_array_var VMap_ABitvT.t;
}

module VMap_AB = Map.Make (struct
  type t = bool_array_var

  let compare = compare
end)

let var_tostr var =
  match var with
  | BoolVar BT -> "b_t"
  | BoolVar (B b) -> b
  | ABoolVar BT -> "b_t"
  | ABoolVar (B b) -> b
  | IntTermVar ET -> "e_t"
  | IntTermVar (T t) -> t
  | AIntTermVar ET -> "e_t"
  | AIntTermVar (T t) -> t
  | BitvTermVar ET -> "e_t"
  | BitvTermVar (T t) -> t
  | ABitvTermVar ET -> "e_t"
  | ABitvTermVar (T t) -> t

let subs_var current_var to_replace expression =
  let repl =
    match current_var with
    | BoolVar BT -> to_replace = "b_t"
    | BoolVar (B b) -> b = to_replace
    | ABoolVar BT -> to_replace = "b_t"
    | ABoolVar (B b) -> b = to_replace
    | IntTermVar ET -> to_replace = "e_t"
    | IntTermVar (T t) -> to_replace = t
    | AIntTermVar ET -> to_replace = "e_t"
    | AIntTermVar (T t) -> to_replace = t
    | BitvTermVar ET -> to_replace = "e_t"
    | BitvTermVar (T t) -> to_replace = t
    | ABitvTermVar ET -> to_replace = "e_t"
    | ABitvTermVar (T t) -> to_replace = t
  in
  if repl then expression else current_var

(* Create a new variable with newvar_name as its name of the same type as var 1. *)
let new_var_of_same_type var1 newvar_name =
  match var1 with
  | BoolVar _ -> BoolVar (B newvar_name)
  | ABoolVar _ -> ABoolVar (B newvar_name)
  | IntTermVar _ -> IntTermVar (T newvar_name)
  | AIntTermVar _ -> AIntTermVar (T newvar_name)
  | BitvTermVar _ -> BitvTermVar (T newvar_name)
  | ABitvTermVar _ -> ABitvTermVar (T newvar_name)

(* let match_var var1 name =
   match current_var with
   | BoolVar BT -> name = "b_t"
   | BoolVar (B b) -> b = name
   | ABoolVar BT -> name = "b_t"
   | ABoolVar (B b) -> b = name
   | IntTermVar ET -> name = "e_t"
   | IntTermVar (T t) -> name = t
   | AIntTermVar ET -> name = "e_t"
   | AIntTermVar (T t) -> name = t *)

let to_array_var var =
  match var with
  | BoolVar BT -> ABoolVar BT
  | BoolVar (B bv) -> ABoolVar (B bv)
  | IntTermVar ET -> AIntTermVar ET
  | IntTermVar (T tv) -> AIntTermVar (T tv)
  | BitvTermVar ET -> ABitvTermVar ET
  | BitvTermVar (T btv) -> ABitvTermVar (T btv)
  | _ -> var
