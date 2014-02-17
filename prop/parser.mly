%{
  open Syntax
%}

/* Lexemes */
%token <string> LITERAL
%token <string> VARIABLE
%token CNF
%token DNF
%token NNF
%token TRUE
%token FALSE
%token NOT
%token AND
%token NAND
%token OR
%token NOR
%token XOR
%token IMPLIES
%token EQUIV
%token LPAREN
%token RPAREN
%token SET
%token EOF

/* Precedence and associativity */
%left EQUIV
%right IMPLIES
%nonassoc NAND NOR
%left XOR
%left OR
%left AND
%nonassoc NOT

/* Top level rule */
%start toplevel
%type <Syntax.command> toplevel

%%

/* Grammar */

toplevel:
  | expression EOF                  { Expression $1 }
  | VARIABLE SET expression EOF     { Assignment ($1, $3) }
;

expression:
  | LITERAL                         { Literal $1 }
  | VARIABLE                        { Variable $1 }
  | TRUE                            { True }
  | FALSE                           { False }
  | NOT expression                  { Not $2 }
  | expression AND     expression   { And ($1, $3) }
  | expression NAND    expression   { NAnd ($1, $3) }
  | expression OR      expression   { Or ($1, $3) }
  | expression NOR     expression   { NOr ($1, $3) }
  | expression XOR     expression   { XOr ($1, $3) }
  | expression IMPLIES expression   { Implies ($1, $3) }
  | expression EQUIV   expression   { Equiv ($1, $3) }
  | LPAREN expression RPAREN        { $2 }
  | CNF expression                  { CNF $2 }
  | DNF expression                  { DNF $2 }
  | NNF expression                  { NNF $2 }

;
