(** The main program. *)

(** The end of file character. *)
let eof =
  match Sys.os_type with
      "Unix" | "Cygwin" -> "Ctrl-D"
    | "Win32" -> "Ctrl-Z"
    | _ -> "\"end of file\""
;;

(** The startup message. *)
let startup = "Propositional logic manipulator. Press " ^ eof ^ " to quit."
;;

(** Top level reads input, parses, evaluates and prints the result. *)
let main =
  print_endline startup ;
  let env = ref [] in
    try
      while true do
        print_string "> ";
        let str = read_line () in
          try
            match Parser.toplevel Lexer.lexeme (Lexing.from_string str) with
              | Syntax.Assignment (v, e) -> 
                  let e' = Eval.eval !env e in
                    env := (v, e')::!env ;
                    print_endline (v ^ " = " ^ (Syntax.string_of_expression e'))
              | Syntax.Expression e -> print_endline (Syntax.string_of_expression (Eval.eval !env e))
          with
        | Failure str -> print_endline ("Error: " ^ str)
        | Parsing.Parse_error -> print_endline "Syntax error."
      done 
    with
      End_of_file -> print_endline "\nGood bye."
;;
