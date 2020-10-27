#use "code-gen.ml";;
open Code_Gen;;

(*
* Compiler for ChezScheme subset, 2020
* Programmed by:
*   Itay Bouganim, 305278384
*   Sahar Vaya, 205583453
*)
let file_to_string f =
  let ic = open_in f in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s;;

let string_to_asts s = List.map Semantics.run_semantics (Tag_Parser.tag_parse_expressions (Reader.read_sexprs s));;
let primitive_names_to_labels = Code_Gen.primitive_names_to_labels;;

let make_prologue consts_tbl fvars_tbl =
  let fvar_offset fvar_name =
    try let offset = List.assoc fvar_name fvars_tbl in
      Printf.sprintf "FVAR(%d)" offset with Not_found -> raise X_unbound_value in
  let make_primitive_closure (prim, label) =
    "\tMAKE_CLOSURE(rax, SOB_NIL_ADDRESS, " ^ label  ^ ")\n\tmov qword " ^ fvar_offset prim ^ ", rax" in
  let constant_bytes (c, (a, s)) = s in
  ";;; All the macros and the scheme-object printing procedure
;;; are defined in compiler.s
%include \"compiler.s\"

section .bss
;;; This pointer is used to manage allocations on our heap.
malloc_pointer:
    resq 1

section .data
const_tbl:
" ^ (String.concat "\n" (List.map constant_bytes consts_tbl)) ^ "

;;; These macro definitions are required for the primitive
;;; definitions in the epilogue to work properly
%define SOB_VOID_ADDRESS CONST(" ^ (string_of_int (fst (List.assoc Void consts_tbl))) ^ ")
%define SOB_NIL_ADDRESS CONST(" ^ (string_of_int (fst (List.assoc (Sexpr Nil) consts_tbl))) ^ ")
%define SOB_FALSE_ADDRESS CONST(" ^ (string_of_int (fst (List.assoc (Sexpr (Bool false)) consts_tbl))) ^ ")
%define SOB_TRUE_ADDRESS CONST(" ^ (string_of_int  (fst (List.assoc (Sexpr (Bool true)) consts_tbl))) ^ ")

fvar_tbl:
" ^
  (* This line should be adapted to your fvar-addressing scheme.
     I.e., if you use direct labeling, you should output them here. *)
  (String.concat "\n" (List.map (fun (fvar_name, offset) ->
       Printf.sprintf "\tdq T_UNDEFINED\t; reserved for: %s, offset: %d" fvar_name offset) fvars_tbl)) ^ "

global main
section .text
main:
\tpush rbp

\t;; set up the heap
\tmov rdi, GB(4)
\tcall malloc
\tmov [malloc_pointer], rax

\t;; Set up the dummy activation frame
\t;; The dummy return address is T_UNDEFINED
\t;; (which a is a macro for 0) so that returning
\t;; from the top level (which SHOULD NOT HAPPEN
\t;; AND IS A BUG) will cause a segfault.
\tpush 0
\tpush qword SOB_NIL_ADDRESS
\tpush qword T_UNDEFINED
\tpush rsp
\tmov rbp,rsp

\t;; Set up the primitive stdlib fvars:
\t;; Since the primtive procedures are defined in assembly,
\t;; they are not generated by scheme (define ...) expressions.
\t;; This is where we emulate the missing (define ...) expressions
\t;; for all the primitive procedures.
" ^ (String.concat "\n" (List.map make_primitive_closure primitive_names_to_labels)) ^ "
\ncode_fragment:
\t;;; The user code compiled will be catenated here.
\t;;; It will be executed immediately after the closures for
\t;;; the primitive procedures are set up.\n
";;

(* You may populate this variable with a string containing the epilogue.
   You may load it from a file, you may write it here inline,
   you may just add things to prims.s (which gets catenated with the epilogue variable).
   Whatever floats your boat. You just have to make sure all the required
   primitive procedures are implemented and included in the output assembly. *)
let epilogue = file_to_string "epilogue.s";;

exception X_missing_input_file;;

try
  let infile = Sys.argv.(1) in
  let code = (file_to_string "stdlib.scm") ^ (file_to_string infile) in
  let asts = Code_Gen.rename_tags_asts (string_to_asts code) in
  let consts_tbl, tag_definitions = Code_Gen.make_consts_tbl asts in
  let fvars_tbl = Code_Gen.make_fvars_tbl asts in
  let generate = Code_Gen.generate consts_tbl fvars_tbl tag_definitions in
  let code_fragment = String.concat "\n\n"
      (List.map
         (fun ast -> (generate ast) ^ "\n\tcall write_sob_if_not_void\t; print sob")
         asts) in
  (* clean_exit contains instructions to clean the dummy stack
     and return exit code 0 ("all's well") from procedure main. *)
  let clean_exit =
    "\n\n\tmov rax, 0\n"^
    "\tadd rsp, 4*8\n" ^
    "\tpop rbp\n" ^
    "\tret\n\n" in
  let provided_primitives = file_to_string "prims.s" in

  print_string ((make_prologue consts_tbl fvars_tbl)  ^
                code_fragment ^ clean_exit ^
                provided_primitives ^ "\n" ^ epilogue)

with Invalid_argument(x) -> raise X_missing_input_file;;
