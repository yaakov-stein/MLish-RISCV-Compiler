open Mlish_ast
open Scish_ast

(* This magic is used to glue the generated lexer and parser together.
 * Expect one command-line argument, a file to parse.
 * You do not need to understand this interaction with the system. *)


let parse_file () =
  let argv = Sys.argv in
  let _ = 
    if Array.length argv != 3
    then (prerr_string ("usage: " ^ argv.(0) ^ " [file-to-parse] [output file]\n");
    exit 1) in
  let ch = open_in argv.(1) in
  Ml_parse.program Ml_lex.lexer (Lexing.from_channel ch)

let type_prog prog =
  try
    let ty = Mlish_type_check.type_check_exp prog in
    print_string (tipe2string ty)
  with
    Mlish_type_check.TypeError -> print_string "\nType error"

let compile_prog prog = 
  let _ = Mlish_type_check.type_check_exp prog in
  Mlish_compile.compile_exp prog

(* let run_prog prog = Scish_eval.run prog *)

let _ = 
  let prog = parse_file() in
  let scish_prog = compile_prog prog in
  let cish_prog = Scish_compile.compile_exp scish_prog in
  let riscvcode = Cish_compile.compile cish_prog in
  let ch = open_out Sys.argv.(2) in
  let strs = List.map (fun x -> (Riscv.inst2string x) ^ "\n") riscvcode in
  let res = 
    "\t.text\n" ^
    "\t.align\t2\n" ^
    "\t.globl main\n" ^
    (String.concat "" strs) ^
    "\n\n" ^
    "\t.data\n" ^
    "\t.align 0\n"^
    "\n" in
  print_newline ();
  print_string res;
  output_string ch res

(* let _ = 
  let (mode, prog) = parse_file() in
  match mode with
  | Typecheck ->
     print_string (Mlish_ast.exp2string prog ^ "\n");
     flush stdout;
     type_prog prog
  | Compile ->
     let prog' = compile_prog prog in
     print_string (Scish_ast.exp2string prog' ^ "\n");
     let ans = run_prog prog' in
     print_string ("answer = "^(Scish_eval.val2string ans)^"\n") *)

(*
let dump p = print_string (Cish_ast.prog2string p)

let _ =
  let prog = parse_file() in
 let ans = run_prog prog in
(*
let _ =  print_string ("answer = "^(string_of_int ans)^"\n") in
*)
  dump (compile_prog prog)
*)
