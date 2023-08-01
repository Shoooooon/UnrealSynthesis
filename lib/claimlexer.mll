{
  open Claimparser

  exception SyntaxError of string

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
  | "Int" {INT_KWD}
  | "Bool" {BOOL_KWD} 
  | "Stmt" {STMT_KWD}
  | "not" {NOT}
  | "and" {AND}
  | "or" {OR}
  | "+" {PLUS}
  | "-" {MINUS}
  | "=" {EQUALS}
  | "<" {LESS}
  | "<=" {LESS_EQUALS}
  | ">" {GREATER}
  | ">=" {GREATER_EQUALS}
  | "=>" {IMPLIES}
  | ":=" {ASSIGN}
  | ";" {SEMICOLON}
  | "{|" {LEFT_FORM_DEMARCATOR}
  | "|}" {RIGHT_FORM_DEMARCATOR}
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
  | varName {STRING (Lexing.lexeme lexbuf)}
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }