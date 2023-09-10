{
  open Nopeparser

  exception SyntaxError of string
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
let varName = ['a'-'z' 'A'-'Z']['0'-'9' 'a'-'z' 'A'-'Z' '_']*


rule read =
  parse
  | white    { read lexbuf }
  | newline  { read lexbuf }
  | int      { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | "synth-fun" {SYNTH_FUN}
  | "ite" {ITE}
  | "Int" {INT_KWD}
  | "Bool" {BOOL_KWD} 
  | "not" {NOT}
  | "and" {AND}
  | "or" {OR}
  | "+" {PLUS}
  | "=" {EQUALS}
  | "<" {LESS}
  | "<=" {LESS_EQUALS}
  | ">" {GREATER}
  | ">=" {GREATER_EQUALS}
  | "true"   { TRUE }
  | "false"  { FALSE }
  | '('      { LEFT_PAREN }
  | ')'      { RIGHT_PAREN }
  | varName {STRING (Lexing.lexeme lexbuf)}
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }