#use "semantic-analyser.ml";;

exception X_unbound_value

(*
* Code Generator for ChezScheme subset, 2020
* Programmed by:
*   Itay Bouganim, 305278384
*   Sahar Vaya, 205583453
*)
module type CODE_GEN = sig

  val rename_tags_asts : expr' list -> expr' list
  val make_consts_tbl : expr' list -> ((constant * (int * string)) list * (string * sexpr) list)
  val make_fvars_tbl : expr' list -> (string * int) list
  val generate : (constant * (int * string)) list -> (string * int) list -> (string * sexpr) list -> expr' -> string
  val primitive_names_to_labels : (string * string) list

end;;

module Code_Gen : CODE_GEN = struct

  (* Size of segments in SOBs *)
  let type_sz = 1 and value_sz =  1;;
  let pointer_sz = 8 and numeric_sz = 8;;

  (* Store and generate labels by name and type *)
  let label_counters = ref []
  let get_label expr desc =
    let concat_label = expr ^ "_" ^ desc in
    let label_counter = List.assoc_opt concat_label !label_counters in
    let label_counter = (match label_counter with
        | Some(counter) -> counter
        | None -> let counter = ref 0 in label_counters := ((concat_label, counter)::!label_counters); counter) in
    let increment_label_counter () =
      label_counter := 1 + !label_counter ; !label_counter in
    Printf.sprintf "l_%s_%s_%d" expr desc (increment_label_counter());;


  let set_of_list list comparator =
    List.fold_left (fun acc curr -> if List.exists (comparator curr) acc then acc else acc@[curr]) [] list;;


  let primitive_names_to_labels =
    ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
     "null?", "is_null"; "char?", "is_char"; "string?", "is_string";
     "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
     "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
     "symbol->string", "symbol_to_string";
     "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
     "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ";
     "car", "car"; "set-car!", "set_car"; "cdr", "cdr"; "set-cdr!", "set_cdr"; "cons", "cons"; "apply", "apply"];;
  let fvar_primitives = List.map (fun (name, _) -> name) primitive_names_to_labels;;


  let rename_tags_asts asts =
    let rec rename_tags ast_idx = function
      | Const'(Sexpr sexpr) -> Const'(Sexpr (rename_tags_sexpr ast_idx sexpr))
      | If'(test, dit, dif) -> If'(rename_tags ast_idx test, rename_tags ast_idx dit, rename_tags ast_idx dif)
      | Set'(var_name, expr) -> Set'(rename_tags ast_idx var_name, rename_tags ast_idx expr)
      | BoxSet'(var_name ,expr) -> BoxSet'(var_name, rename_tags ast_idx expr)
      | Def'(var_name, expr) -> Def'(rename_tags ast_idx var_name, rename_tags ast_idx expr)
      | Or' exprs -> Or'(List.map (rename_tags ast_idx) exprs)
      | Seq' exprs -> Seq'(List.map (rename_tags ast_idx) exprs)
      | LambdaSimple'(param_lst, body) -> LambdaSimple'(param_lst, rename_tags ast_idx body)
      | LambdaOpt'(param_lst, opt_param , body)-> LambdaOpt'(param_lst, opt_param , rename_tags ast_idx body)
      | Applic'(applic ,args) -> Applic'(rename_tags ast_idx applic, List.map (rename_tags ast_idx) args)
      | ApplicTP'(applic ,args)-> ApplicTP'(rename_tags ast_idx applic, List.map (rename_tags ast_idx) args)
      | expr' -> expr';
    and rename_tags_sexpr ast_idx = function
      | TaggedSexpr(tag, tagged_sexpr) -> TaggedSexpr(tag^ast_idx, rename_tags_sexpr ast_idx tagged_sexpr)
      | TagRef tag -> TagRef(tag^ast_idx)
      | Pair(car, cdr) -> Pair(rename_tags_sexpr ast_idx car, rename_tags_sexpr ast_idx cdr)
      | sexpr -> sexpr in
    List.mapi (fun index ast -> rename_tags (string_of_int (index + 1)) ast) asts


  let make_consts_tbl asts =
    let const_tbl_ref const_tbl key =
      try Printf.sprintf "CONST(%d)" (fst(List.assoc key const_tbl))
      with Not_found -> raise X_unbound_value in
    let rec collect_sexprs_as_consts = function
      | Const' const -> [const]
      | BoxSet'(_, expr) | Set'(_, expr) -> collect_sexprs_as_consts expr
      | If'(test, dit, dif) -> collect_sexprs_as_consts test@collect_sexprs_as_consts dit@collect_sexprs_as_consts dif
      | Def'(var_name, expr) -> collect_sexprs_as_consts var_name@collect_sexprs_as_consts expr
      | Or' exprs | Seq' exprs -> List.fold_left (fun const_lst expr -> const_lst@(collect_sexprs_as_consts expr) ) [] exprs
      | LambdaSimple'(_, body) |LambdaOpt'(_, _, body) -> collect_sexprs_as_consts body
      | Applic'(applic, args) | ApplicTP'(applic, args) -> collect_sexprs_as_consts applic@List.fold_left (fun const_lst expr -> const_lst@(collect_sexprs_as_consts expr) ) [] args
      | _ -> [];
    and replace_tags_in_sexpr sexpr = match sexpr with
      | Pair(car, cdr) -> Pair(replace_tags_in_sexpr car, replace_tags_in_sexpr cdr)
      | TaggedSexpr(name, sexpr) -> (replace_tags_in_sexpr sexpr)
      | _ -> sexpr;
    and expand_consts const tag_defs = match const with
      | Void -> ([Void], tag_defs)
      | Sexpr sexpr ->
        (let rec expand_sexprs tag_defs = (match sexpr with
             | Symbol sym -> ([Sexpr(String sym)]@[const], tag_defs)
             | Pair(car, cdr) ->
               let expanded_car = expand_consts (Sexpr car) tag_defs in
               let expanded_cdr = expand_consts (Sexpr cdr) tag_defs in
               (fst(expanded_car)@fst(expanded_cdr)@[Sexpr (replace_tags_in_sexpr sexpr)], snd(expanded_car)@snd(expanded_cdr))
             | TaggedSexpr(name, sexpr) ->
               let expanded_sexpr = expand_consts (Sexpr sexpr) tag_defs in
               (fst(expanded_sexpr), (name, (replace_tags_in_sexpr sexpr))::snd(expanded_sexpr))
             | TagRef _  -> ([], tag_defs)
             | _ -> ([const], tag_defs)) in expand_sexprs tag_defs);
    and construct_consts const_tbl const address = match const with
      | Void -> [(const, (address, Printf.sprintf "\tMAKE_VOID\t; const offset: %d" address))]
      | Sexpr sexpr -> (match sexpr with
          | Nil -> [(const, (address, Printf.sprintf "\tMAKE_NIL\t; const offset: %d, value: '()" address))]
          | Bool(true) -> [(const, (address, Printf.sprintf "\tMAKE_BOOL(%d)\t; const offset: %d, value: #t" 1 address))]
          | Bool(false) -> [(const, (address, Printf.sprintf "\tMAKE_BOOL(%d)\t; const offset: %d, value: #f" 0 address))]
          | Char char -> [(const, (address, Printf.sprintf "\tMAKE_LITERAL_CHAR(%d)\t; const offset: %d, value: \'%s\'" (int_of_char char) address (Char.escaped char)))]
          | Number(Int num) -> [(const, (address, Printf.sprintf "\tMAKE_LITERAL_INT(%d)\t; const offset: %d, value: %d" num address num))]
          | Number(Float num) -> [(const, (address, Printf.sprintf "\tMAKE_LITERAL_FLOAT(%f)\t; const offset: %d, value: %f" num address num))]
          | Symbol sym -> [(const, (address, Printf.sprintf "\tMAKE_LITERAL_SYMBOL(%s)\t; const offset: %d, value: '%s" (const_tbl_ref const_tbl (Sexpr(String sym))) address sym))]
          | String str -> let str_last_idx = String.length str - 1 in
            let indexed_str_chars = List.mapi (fun index char -> (char, index)) (string_to_list str) in
            [(const, (address, Printf.sprintf "\tMAKE_LITERAL_STRING %s\t; const offset: %d, value: \"%s\"" (List.fold_left (fun byte_str (char, index) ->
                 if str_last_idx = index then byte_str^Printf.sprintf "%d" (int_of_char char)
                 else byte_str^Printf.sprintf "%d, " (int_of_char char)) "" indexed_str_chars) address (String.escaped str)))]
          | Pair(car, cdr) -> (match car, cdr with
              | TagRef _, TagRef _ | TagRef _, _ | _, TagRef _ -> [(const, (address,  ""))]
              | _ -> [(const, (address, Printf.sprintf "\tMAKE_LITERAL_PAIR(%s, %s)\t; const offset: %d, value: Pair"
                                 (const_tbl_ref const_tbl (Sexpr car)) (const_tbl_ref const_tbl (Sexpr cdr)) address))])
          | _ -> raise X_this_should_not_happen);
    and assign_tag_refs const_tbl tag_defs const = try match const with
      | (Sexpr(Pair(car, cdr)), (address, "")) -> (match car, cdr with
          | TagRef name1, TagRef name2 ->
            let referenced_expr1 = List.assoc name1 tag_defs in let const_address1 = (const_tbl_ref const_tbl (Sexpr referenced_expr1)) in
            let referenced_expr2 = List.assoc name2 tag_defs in let const_address2 = (const_tbl_ref const_tbl (Sexpr referenced_expr2)) in
            ((fst const), (address, Printf.sprintf "\tMAKE_LITERAL_PAIR(%s, %s)\t; const offset: %d, value: Pair" const_address1 const_address2 address))
          | TagRef name, _ ->
            let referenced_expr = List.assoc name tag_defs in let const_address = (const_tbl_ref const_tbl (Sexpr referenced_expr)) in
            ((fst const), (address, Printf.sprintf "\tMAKE_LITERAL_PAIR(%s, %s)\t; const offset: %d, value: Pair" const_address (const_tbl_ref const_tbl (Sexpr cdr)) address))
          | _, TagRef name ->
            let referenced_expr = List.assoc name tag_defs in let const_address = (const_tbl_ref const_tbl (Sexpr referenced_expr)) in
            ((fst const), (address, Printf.sprintf "\tMAKE_LITERAL_PAIR(%s, %s)\t; const offset: %d, value: Pair" (const_tbl_ref const_tbl (Sexpr car)) const_address address))
          | _ -> raise X_syntax_error)
      | _ -> const with Not_found -> raise X_unbound_value in
    let const_size = function
      | Void -> type_sz
      | Sexpr sexpr -> (match sexpr with
          | Nil -> type_sz
          | Char _ | Bool _ -> type_sz + value_sz
          | Number _  | Symbol _ -> type_sz + numeric_sz
          | String str -> type_sz + numeric_sz + String.length str
          | Pair _ -> type_sz + pointer_sz + pointer_sz
          | _ -> 0) in
    let compare_consts const1 const2 = ((const1 = Void) && (const2 = Void)) || match const1, const2 with
      | Sexpr sexpr1, Sexpr sexpr2 -> sexpr_eq sexpr1 sexpr2
      | _ -> false in
    let initial_consts = [Void; Sexpr Nil; Sexpr(Bool false); Sexpr(Bool true)] in
    let const_tbl = List.fold_left (fun const_lst expr -> const_lst@(collect_sexprs_as_consts expr)) initial_consts asts in
    let const_tbl = set_of_list const_tbl compare_consts in
    let const_tbl, tag_definitions = List.fold_left (fun const_lst const ->
        let expanded_const = expand_consts const [] in
        (fst(const_lst)@fst(expanded_const), snd(const_lst)@snd(expanded_const))) ([], []) const_tbl in
    let const_tbl = set_of_list const_tbl compare_consts in
    let sized_const_tbl = List.map (fun const -> (const, const_size const)) const_tbl in
    let const_tbl = List.fold_left (fun (consts, offset) (const, size) -> (consts@(construct_consts consts const offset), offset+size)) ([], 0) sized_const_tbl in
    let const_tbl = (fst const_tbl) in (List.map (fun const -> assign_tag_refs const_tbl tag_definitions const) const_tbl, tag_definitions)


  let make_fvars_tbl asts =
    let rec make_fvars fvars ast =
      (match ast with
       | Const' _ | Var'(VarParam _) | Var'(VarBound _) | Box' _ | BoxGet' _  -> fvars
       | BoxSet'(_, expr) -> make_fvars fvars expr
       | If'(test, dit, dif) -> let fvars_test = (make_fvars fvars test) in let fvars_dit = (make_fvars fvars_test dit) in (make_fvars fvars_dit dif)
       | Seq' exprs | Or' exprs -> List.fold_left (fun fvar_lst expr -> make_fvars fvar_lst expr) fvars exprs
       | Set'(var_name, expr) | Def'(var_name, expr) -> let fvars_name = (make_fvars fvars var_name) in (make_fvars fvars_name expr)
       | LambdaSimple'(_, body) | LambdaOpt'(_, _, body) -> make_fvars fvars body
       | Applic'(applic, args) | ApplicTP'(applic, args) -> let fvars_applic = (make_fvars fvars applic) in (List.fold_left (fun fvar_lst arg -> make_fvars fvar_lst arg) fvars_applic args)
       | Var'(VarFree var_name) -> if List.mem var_name fvars then fvars else fvars@[var_name]) in
    let fvars = List.fold_left (fun fvar_lst ast -> make_fvars fvar_lst ast) fvar_primitives asts in
    List.mapi (fun index fvar -> (fvar, index)) (set_of_list fvars String.equal)


  let generate consts fvars tag_definitions e =
    let get_const_address const =
      try let const = (match const with
          | Void -> const
          | Sexpr sexpr -> Sexpr(let rec replace_sexpr_tags nested = function
              | TaggedSexpr(name, sexpr) -> (replace_sexpr_tags nested sexpr)
              | Pair(car, cdr) -> Pair(replace_sexpr_tags true car, replace_sexpr_tags true cdr)
              | TagRef name as ref -> if nested then ref else List.assoc name tag_definitions
              | sexpr -> sexpr in replace_sexpr_tags false sexpr)) in
        let const = List.assoc const consts in let address = (fst const) in let asm_val = (snd const)
        in let asm_val = String.trim asm_val in let asm_desc = String.lowercase_ascii (String.sub asm_val ((String.index asm_val '_') + 1) ((String.length asm_val) - 5)) in
        Printf.sprintf "CONST(%d)\t; const value: %s" address asm_desc
      with Not_found -> raise X_unbound_value in
    let get_fvar_address fvar =
      try let var_name, address = List.find (fun (fvar_name, address) -> fvar_name = fvar) fvars in Printf.sprintf "FVAR(%d)" address
      with Not_found -> raise X_unbound_value in
    let rec generate_expr env_size param_count = function
      | Const' const -> Printf.sprintf "\n\tmov rax, %s" (get_const_address const)
      | Var'(VarParam (var_name, minor)) -> Printf.sprintf "\n\tmov rax, PVAR(%d)\t ; rax = %s (PVAR %d)" minor var_name minor
      | Var'(VarBound(var_name, major, minor)) ->
        Printf.sprintf
          ("\n\tmov rax, LEX_ENV\t ; rax = lexical env" ^^
           "\n\tmov rax, qword [rax+WORD_SIZE*%d]\t; rax = lexical rib" ^^
           "\n\tmov rax, qword [rax+WORD_SIZE*%d]\t; rax = %s (BVAR %d, %d)")
          major minor var_name major minor
      | Var'(VarFree var_name) -> Printf.sprintf "\n\tmov rax, qword %s\t; rax = %s" (get_fvar_address var_name) (var_name ^ " (FVAR)")
      | Def'(var_name, expr) -> (match var_name with
          | Var'(VarFree var_name) ->
            Printf.sprintf
              ("\t;; DEFINE free var %s" ^^
               "\n%s" ^^
               "\n\tmov qword %s, rax\t; Define var %s = rax" ^^
               "\n\tRETURN_SOB_VOID" ^^
               "\n\t;; DEFINE end")
              var_name (generate_expr env_size param_count expr) (get_fvar_address var_name) var_name
          | _ -> raise X_syntax_error)
      | Set'(var_name, expr) -> (match var_name with
          | Var'(VarFree var_name) ->
            Printf.sprintf
              ("\t;; SET FVAR start" ^^
               "\n%s\n\tmov qword %s, rax\t; Set %s (free) = rax" ^^
               "\n\tRETURN_SOB_VOID" ^^
               "\n\t;; SET FVAR end")
              (generate_expr env_size param_count expr) (get_fvar_address var_name) var_name
          | Var'(VarParam(var_name, minor)) ->
            Printf.sprintf
              ("\t;; SET PVAR start" ^^
               "\n%s" ^^
               "\n\tmov PVAR(%d), rax\t; Set %s (param %d) = rax" ^^
               "\n\tRETURN_SOB_VOID" ^^
               "\n\t;; SET PVAR end")
              (generate_expr env_size param_count expr) minor var_name minor
          | Var'(VarBound(var_name, major, minor)) ->
            Printf.sprintf
              ("\t;; SET BVAR start" ^^
               "\n%s" ^^
               "\n\tmov rbx, LEX_ENV\t; rbx = lexical env" ^^
               "\n\tmov rbx, qword [rbx+WORD_SIZE*%d]\t; rbx = lexical rib" ^^
               "\n\tmov qword [rbx+WORD_SIZE*%d], rax\t; Set %s (bound %d, %d) = rax" ^^
               "\n\tRETURN_SOB_VOID" ^^
               "\n\t;; SET BVAR end")
              (generate_expr env_size param_count expr) major minor var_name major minor
          | _ -> raise X_syntax_error)
      | Seq' exprs -> (List.fold_left (fun exprs_asm expr ->
          exprs_asm^(
            Printf.sprintf
              ("\t; Sequence expression" ^^
               "\n%s" ^^
               "\n") (generate_expr env_size param_count expr))) "\t;; SEQUENCE expression start\n" exprs) ^ "\t;; SEQUENCE expression end"
      | Or' exprs ->
        let exit_lbl = get_label "or" "exit" in (List.fold_left (fun exprs_asm expr ->
            exprs_asm^(
              Printf.sprintf
                ("%s" ^^
                 "\n\tCHECK_SOB_FALSE" ^^
                 "\n\tjne %s\t; rax = #f, exit OR expression\n")
                (generate_expr env_size param_count expr) exit_lbl)) "\t;; OR expression start\n" exprs) ^ "\t;; OR expression end\n" ^ exit_lbl ^ ":"
      | If'(test, dit, dif) ->
        let else_lbl = get_label "if" "else" in let exit_lbl = get_label "if" "exit" in
        Printf.sprintf
          ("\t;; IF expression start" ^^
           "\n\t; Compute test" ^^
           "\n%s" ^^
           "\n\tCHECK_SOB_FALSE" ^^
           "\n\tje %s" ^^
           "\n\t; Compute dit" ^^
           "\n%s" ^^
           "\n\tjmp %s" ^^
           "\n%s:" ^^
           "\n\t; Compute dif" ^^
           "\n%s" ^^
           "\n\t;; IF expression end" ^^
           "\n%s:")
          (generate_expr env_size param_count test) else_lbl (generate_expr env_size param_count dit) exit_lbl else_lbl (generate_expr env_size param_count dif) exit_lbl
      | Box'(var) ->
        Printf.sprintf
          ("\t;; BOX variable expression start" ^^
           "\n%s" ^^
           "\n\tmov rdx, rax\t; rdx contains the result of computing the var" ^^
           "\n\tMALLOC rax, WORD_SIZE\t; allocate space for the box" ^^
           "\n\tmov [rax], rdx\t; store var in allocated space" ^^
           "\n\t;; BOX variable end")
          (generate_expr env_size param_count (Var' var))
      | BoxGet'(var) ->
        Printf.sprintf
          ("\t;; BOX GET expression start" ^^
           "\n%s" ^^
           "\n\tmov rax, qword [rax]" ^^
           "\n\t;; BOX GET expression end")
          (generate_expr env_size param_count (Var' var))
      | BoxSet'(var, expr) ->
        Printf.sprintf
          ("\t;; BOX SET expression start" ^^
           "\n%s" ^^
           "\n\tpush rax\t; store expression value in stack" ^^
           "\n%s" ^^
           "\n\tpop qword [rax]\t; rax = result of computing var, store computed expression value" ^^
           "\n\tRETURN_SOB_VOID" ^^
           "\n\t;; BOX SET expression end")
          (generate_expr env_size param_count expr) (generate_expr env_size param_count (Var' var))
      | Applic'(applic, args) ->
        Printf.sprintf
          ("\t;; APPLICATION start" ^^
           "\n\t; prepare the stack for procedure call" ^^
           "\n\tPUSH_MAGIC\t; push magic to stack" ^^
           "\n%s" ^^
           "\n\tpush %d\t; push argument count to stack" ^^
           "\n%s" ^^
           "\n\tcall verify_closure_on_applic\t; check that rax has type closure" ^^
           "\n\tCLOSURE_ENV rdx, rax\t; rdx = closure pointer to lexical enviorment" ^^
           "\n\tpush rdx\t; push application lexical enviorment to stack" ^^
           "\n\tCLOSURE_CODE rax, rax\t; rax = closure pointer to application code" ^^
           "\n\tcall rax\t; call application procedure" ^^
           "\n\t; Return from application" ^^
           "\n\tadd rsp, WORD_SIZE\t; pop lexical enviorment" ^^
           "\n\tpop rdx\t; pop argument count, rdx = argument count" ^^
           "\n\tinc rdx\t; rdx = argument count + 1" ^^
           "\n\tshl rdx, 3; rdx = 8*rdx = 8*(argument count + 1)" ^^
           "\n\tadd rsp, rdx\t; pop all arguments and arguments count" ^^
           "\n\t;; APPLICATION end\n")
          (List.fold_right (fun (arg, arg_idx) args ->
               args^Printf.sprintf "\n%s\n\tpush rax\t; push argument with index %d for application"
                 (generate_expr env_size param_count arg) arg_idx) (List.mapi (fun index arg -> (arg, index + 1)) args) "")
          (List.length args)
          (generate_expr env_size param_count applic)
      | ApplicTP'(applic, args) ->
        let arg_count = List.length args in
        let init_frame_size = 5 in
        Printf.sprintf
          ("\t;; TAIL POSITION APPLICATION start" ^^
           "\n\t; prepare the stack for procedure call" ^^
           "\n\tPUSH_MAGIC\t; push magic to stack" ^^
           "\n%s" ^^
           "\n\tpush %d\t; push argument count to stack" ^^
           "\n%s" ^^
           "\n\tcall verify_closure_on_applic\t; check that rax has type closure" ^^
           "\n\tCLOSURE_ENV rdx, rax\t; rdx = closure pointer to lexical enviorment" ^^
           "\n\tpush rdx\t; push application lexical enviorment to stack" ^^
           "\n\tpush qword [rbp+WORD_SIZE*1]\t; push old return address" ^^
           "\n\tpush qword [rbp]\t; push old rbp" ^^
           "\n\tSHIFT_FRAME %d\t; fixing the stack, shift stack frame" ^^
           "\n\tpop rbp" ^^
           "\n\tCLOSURE_CODE rax, rax\t; rax = closure pointer to application code" ^^
           "\n\tjmp rax\t; call application procedure" ^^
           "\n\t;; TAIL POSITION APPLICATION end\n")
          (List.fold_right (fun (arg, arg_idx) args ->
               args^Printf.sprintf "%s\n\tpush rax\t; push argument with index %d for tail application"
                 (generate_expr env_size param_count arg) arg_idx) (List.mapi (fun index arg -> (arg, index + 1)) args) "")
          arg_count
          (generate_expr env_size param_count applic)
          (arg_count + init_frame_size)
      | LambdaSimple'(param_lst, body) ->
        let param_error_lbl = get_label "lamnda_simple" "param_error" in
        let body_asm =
          Printf.sprintf
            ("\n\tcmp r8, ARG_COUNT\t; check r8 == passed param, passed params is equal to expected params" ^^
             "\n\tjne %s\t; error if passed param count does not match expected param count") (* param error label *)
            param_error_lbl in
        generate_lambda_expr body_asm param_lst false param_error_lbl env_size body
      | LambdaOpt'(param_lst, opt_param, body) ->
        let param_count = List.length param_lst in
        let param_error_lbl = get_label "lambda_opt" "param_error" in
        let adjust_stack_lbl = get_label "lambda_opt" "adjust_stack" in
        let adjust_stack_end_lbl = get_label "lambda_opt" "adjust_stack_end" in
        let body_asm =
          Printf.sprintf
            ("\n\tmov rdx, ARG_COUNT\t; rdx = parametes currently on stack" ^^
             "\n\tcmp rdx, r8\t; check r8 == passed param, passed params is equal to expected params" ^^
             "\n\tjb %s\t; error if passed param count does not match expected param count" ^^ (* param error label *)
             "\n\tmov rbx, SOB_NIL_ADDRESS\t; rbx = nil" ^^
             "\n%s:" ^^ (* adjust stack label *)
             "\n\tcmp r8, rdx\t; compare params on stack against expected params" ^^
             "\n\tje %s\t; params on stack are as expected by lambda" ^^ (* adjust stack end label *)
             "\n\tdec rdx\t; rdx -= 1" ^^
             "\n\tmov r10, ARG_AT(rdx)\t; r10 = param[rdx]" ^^
             "\n\tMAKE_PAIR(r9, r10, rbx)\t; create pair for additional params, r9 = Pair(r10, rbx)" ^^
             "\n\tmov rbx, r9\t; rbx = Pair(r10, rbx)" ^^
             "\n\tjmp %s\t; continue adjusting extra params" ^^ (* adjust stack label *)
             "\n%s:" ^^ (* adjust stack end label *)
             "\n\tSTORE_ARG(%d, rbx)\t; store created pair param (located in rbx) to param at index %d on stack")
            param_error_lbl adjust_stack_lbl adjust_stack_end_lbl adjust_stack_lbl adjust_stack_end_lbl param_count param_count in
        generate_lambda_expr body_asm param_lst true param_error_lbl env_size body;

    and generate_lambda_expr body_asm param_lst is_opt error_lbl env_size body =
      let label_mark = (if is_opt then "lambda_opt" else "lambda_simple") in
      let cont_lbl = get_label label_mark "cont" in let code_lbl = get_label label_mark "code" in
      let env_loop_lbl = get_label label_mark "env_loop" in let env_loop_end_lbl = get_label label_mark "env_loop_end" in
      let param_loop_lbl = get_label label_mark "param_loop" in let param_loop_end_lbl = get_label label_mark "param_loop_end" in
      let param_count = List.length param_lst in let comment_title = (if is_opt then "LAMBDA OPTIONAL" else "LAMBDA SIMPLE") in
      Printf.sprintf
        ("\n\t;; %s start" ^^
         "\n\t; create extended enviorment" ^^
         "\n\tmov rax, WORD_SIZE*%d\t; rax = |Enviorment| + 1 = %d + 1" ^^
         "\n\tMALLOC rax, rax\t; allocate space for extended enviorment" ^^
         "\n\tmov rcx, 0\t; i = copy current enviorment loop index" ^^
         "\n\tmov rbx, %d\t; rbx = current enviorment size" ^^
         "\n\tmov rdx, LEX_ENV\t; rdx = lexical enviorment" ^^
         "\n%s:" ^^ (* env loop label *)
         "\n\tcmp rcx, rbx\t; check i == current enviorment size = rbx" ^^
         "\n\tje %s\t; check finished copying current enviorment" ^^ (* env loop end label *)
         "\n\tmov r8, qword [rdx+WORD_SIZE*rcx]\t; r8 = lex_env[8*i]" ^^
         "\n\tmov [rax+rcx*WORD_SIZE+WORD_SIZE], r8\t; ext_env[8*i+8] = lex_env[8*i]" ^^
         "\n\tinc rcx\t; i += 1" ^^
         "\n\tjmp %s\t; continue looping on current enviorment" ^^ (* env loop label *)
         "\n%s:" ^^ (* env loop end label *)
         "\n\t; copy lambda parameters to first rib in the extended enviorment" ^^
         "\n\tmov rcx, 0\t; i = copy parameters index" ^^
         "\n\tmov rbx, ARG_COUNT" ^^
         "\n\tinc rbx\t; include magic in the argument count" ^^
         "\n\tmov r8, rbx\t; r8 = parameter count" ^^
         "\n\tshl rbx, 3\t; rbx = 8*rbx" ^^
         "\n\tMALLOC rdx, rbx\t; allocate space for new rib in extended enviorment" ^^
         "\n%s:" ^^ (* param loop label *)
         "\n\tcmp rcx, r8\t; check i == param count" ^^
         "\n\tje %s\t; finished iterating parameters" ^^ (* param loop end label *)
         "\n\tmov rbx, LEX_ENV\t; rbx = lexical enviorment" ^^
         "\n\tmov r9, ARG_AT(rcx)\t; r9 = params[i]" ^^
         "\n\tmov [rdx+rcx*WORD_SIZE], r9\t; lex_rib[i] = params[i] = r9" ^^
         "\n\tinc rcx\t; i += 1" ^^
         "\n\tjmp %s\t; finished copying parameters to new lex_rib\n" ^^ (* param loop label *)
         "\n%s:" ^^ (* param loop end label *)
         "\n\t; create closure with the extended enviorment created and lambda body code" ^^
         "\n\tmov [rax], rdx\t; ext_env[0] = new lex_rib" ^^
         "\n\tMAKE_CLOSURE(rdx, rax, %s)\t; rdx = closure(env: rax, code: %s), rax = ext_env" ^^
         "\n\tmov rax, rdx\t; rax = closure(env: ext_env, code: %s)" ^^
         "\n\tjmp %s\t; skip lambda body on creation of closure\n" ^^ (* cont label *)
         "\n\t; Lambda body - code to execute on lambda applic" ^^
         "\n%s:" ^^ (* code label *)
         "\n\tenter 0, 0" ^^
         "\n\n\tmov r8, %d\t; r8 = lambda param count" ^^
         "%s" ^^ (* Specific code for the lambda goes here *)
         "\n\t; lambda body start" ^^
         "\n%s" ^^
         "\n\t; lambda body end" ^^
         "\n\tleave" ^^
         "\n\tret" ^^
         "\n\t; Lambda body - finished executing lambda code" ^^
         "\n%s:" ^^ (* param error label *)
         "\n\t; incorrect number of arguments passed to lambda" ^^
         "\n\tcall param_count_error_exit" ^^
         "\n%s:\n" ^^ (* cont label *)
         "\t;; %s end")
        comment_title
        (env_size + 1) (env_size + 1)
        (env_size) env_loop_lbl env_loop_end_lbl env_loop_lbl env_loop_end_lbl
        param_loop_lbl param_loop_end_lbl param_loop_lbl param_loop_end_lbl
        code_lbl code_lbl code_lbl cont_lbl code_lbl param_count
        body_asm
        (generate_expr (env_size + 1) (if is_opt then (param_count + 1) else param_count) body)
        error_lbl cont_lbl
        comment_title
    in generate_expr 0 0 e;;
end;;