{
  open Parser

  exception SyntaxError of string

  (* let bv_id = Printf.sprintf "(_ BitVec %d)" Logic.Formula.bvconst *)
(* 
  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = lexbuf.lex_curr_pos;
                 pos_lnum = pos.pos_lnum + 1
      } *)
}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let int = '-'? ['0'-'9'] ['0'-'9']*
let bitv = '#' ['b' 'x'] ['0'-'9'] ['0'-'9']*
let varName = ['a'-'z' 'A'-'Z']['0'-'9' 'a'-'z' 'A'-'Z' '_']*
(* let bv_id = bv_id *)

rule read =
  parse
  | white    { read lexbuf }
  | newline  { read lexbuf }
  | int      { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | bitv     { BITV (Lexing.lexeme lexbuf)}
  | "define-fun" {DEF_FUN}
  | "Int" {INT_KWD}
  | "(_ BitVec 32)" {BITVEC_KWD}
  | "Bool" {BOOL_KWD} 
  | "not" {NOT}
  | "and" {AND}
  | "or" {OR}
  | "+" {PLUS}
  | "-" {MINUS}
  | "=" {EQUALS}
  | ("bvult" | "<") {LESS}
  | "<=" {LESS_EQUALS}
  | ">" {GREATER}
  | ">=" {GREATER_EQUALS}
  | "bvadd" {BVADD}
  | "bvor" {BVOR}
  | "bvand" {BVAND}
  | "bvsub" {BVSUB}
  | "+" {PLUS}
  | "=>" {IMPLIES}
  | "exists" {EXISTS}
  | "forall" {FORALL}
  | "true"   { TRUE }
  | "false"  { FALSE }
  | '('      { LEFT_PAREN }
  | ')'      { RIGHT_PAREN }
  | varName {STRING (Lexing.lexeme lexbuf)}
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }