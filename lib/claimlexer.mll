{
  open Claimparser

  exception SyntaxError of string

}

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let int = '-'? ['0'-'9'] ['0'-'9']*
let bitv = '#' ['b' 'x'] ['0'-'9' 'a'- 'f'] ['0'-'9' 'a'- 'f']*
let varName = ['a'-'z' 'A'-'Z']['0'-'9' 'a'-'z' 'A'-'Z' '_']*


rule read =
  parse
  | white    { read lexbuf }
  | newline  { read lexbuf }
  | int      { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | bitv     { BITV (Lexing.lexeme lexbuf)}
  | "Int" {INT_KWD}
  | "ABitvec" {ARRAY_BITVEC_KWD}
  | "Bitvec" {BITVEC_KWD}
  | "Bool" {BOOL_KWD} 
  | "AInt" {ARRAY_INT_KWD}
  | "ABool" {ARRAY_BOOL_KWD} 
  | "Stmt" {STMT_KWD} 
  | "Nonterm" {NT_KWD}
  | "None" {NONE_KWD}
  | "AAutoHole" {ARRAY_AUTO_KWD}
  | "AutoHole" {AUTO_KWD}
  | "Some" {SOME_KWD}
  | "Hole" {HOLE_KWD}
  | "b_t" {BT}
  | "e_t" {ET}
  | "not" {NOT}
  | "and" {AND}
  | "or" {OR}
  | "bvadd" {BVADD}
  | "bvmult" {BVMULT}
  | "bvor" {BVOR}
  | "bvxor" {BVXOR}
  | "bvand" {BVAND}
  | "bvsub" {BVSUB}
  | "bvnot" {BVNEG}
  | "+" {PLUS}
  | "*" {TIMES}
  | "-" {MINUS}
  | "=" {EQUALS}
  | "bv=" {BVEQUALS}
  | "<->" {IFF}
  | "<" {LESS}
  | "bv<" {BVLESS}
  | "<=" {LESS_EQUALS}
  | ">" {GREATER}
  | ">=" {GREATER_EQUALS}
  | "=>" {IMPLIES}
  | ":=" {ASSIGN}
  | "bv:=" {BVASSIGN}
  | ";" {SEMICOLON}
  | "," {COMMA}
  | ":" {COLON}
  | "{|" {LEFT_FORM_DEMARCATOR}
  | "|}" {RIGHT_FORM_DEMARCATOR}
  | "skip" {SKIP}
  | "while" {WHILE}
  | "if" {IF}
  | "then" {THEN}
  | "else" {ELSE}
  | "exists" {EXISTS}
  | "forall" {FORALL}
  | "true"   { TRUE }
  | "false"  { FALSE }
  | '('      { LEFT_PAREN }
  | ')'      { RIGHT_PAREN }
  | '['      { LEFT_SQUARE }
  | ']'      { RIGHT_SQUARE }
  | varName {STRING (Lexing.lexeme lexbuf)}
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }