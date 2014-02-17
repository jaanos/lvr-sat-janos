{
  open Parser
}

rule lexeme = parse
    [' ' '\t' '\r' '\n']  { lexeme lexbuf }
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
  | ['a'-'z']['a'-'z' 'A'-'Z']*  { LITERAL (Lexing.lexeme lexbuf) }
  | ['A'-'Z']['a'-'z' 'A'-'Z']*  { VARIABLE (Lexing.lexeme lexbuf) }
  | eof         { EOF }
