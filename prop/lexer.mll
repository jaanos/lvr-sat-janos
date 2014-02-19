{
  open Parser
}

rule lexeme = parse
    [' ' '\t' '\r' '\n']  { lexeme lexbuf }
  | "horn"      { HORN }
  | "sat"       { SAT }
  | "cnf"       { CNF }
  | "dnf"       { DNF }
  | "nnf"       { NNF }
  | 'T'         { TRUE }
  | 'F'         { FALSE }
  | '~'         { NOT }
  | "/\\"       { AND }
  | "/|\\"      { NAND }
  | "\\/"       { OR }
  | "\\|/"      { NOR }
  | '+'         { XOR }
  | "=>"        { IMPLIES }
  | "<=>"       { EQUIV }
  | '('         { LPAREN }
  | ')'         { RPAREN }
  | ":="        { SET }
  | ['a'-'z']['a'-'z' 'A'-'Z' '0'-'9']*  { LITERAL (Lexing.lexeme lexbuf) }
  | ['A'-'Z']['a'-'z' 'A'-'Z' '0'-'9']*  { VARIABLE (Lexing.lexeme lexbuf) }
  | eof         { EOF }
