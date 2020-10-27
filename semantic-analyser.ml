#use "tag-parser.ml";;

type var =
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                            (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
    | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
    | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
    (List.for_all2 String.equal vars1 vars2) &&
    (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
    (String.equal var1 var2) &&
    (List.for_all2 String.equal vars1 vars2) &&
    (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
    (expr'_eq e1 e2) &&
    (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;


exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'

end;;

module Semantics : SEMANTICS = struct
  open Tag_Parser;;

  (*
  * Semantic Analyzer for ChezScheme, 2019
  * Programmed by:
  *   Itay Bouganim, 305278384
  *   Sahar Vaya, 205583453
  *)

  let annotate_lexical_scope_var var scope params =
    let rec find_param_index index = function
      | [] -> None
      | param::rest_params -> if param = var then Some index
        else find_param_index (index + 1) rest_params in
    let param_index = find_param_index 0 params in
    match param_index with
    | Some index -> Var'(VarParam(var, index))
    | None ->
      (let rec find_bound_in_scope major_idx = function
          | [] -> Var'(VarFree var)
          | scope_params::rest_scope ->
            (let param_index = find_param_index 0 scope_params in
             match param_index with
             | Some minor_idx -> Var'(VarBound(var, major_idx, minor_idx))
             | None -> find_bound_in_scope (major_idx + 1) rest_scope) in find_bound_in_scope (-1) scope);;

  let annotate_lexical_addresses e =
    let rec annotate_lexical_scope scope_params params =
      let annotate_expr expr = annotate_lexical_scope scope_params params expr in function
        | Const const -> Const'(const)
        | Var var_name -> annotate_lexical_scope_var var_name scope_params params
        | If(test, dif, dit) -> If'(annotate_expr test, annotate_expr dif, annotate_expr dit)
        | Seq exprs -> Seq'(List.map annotate_expr exprs)
        | Set(var_name, expr) -> Set'(annotate_expr var_name, annotate_expr expr)
        | Def(var_name, expr) -> Def'(annotate_expr var_name, annotate_expr expr)
        | Or exprs -> Or'(List.map annotate_expr exprs)
        | LambdaSimple(param_lst, body) -> LambdaSimple'(param_lst, annotate_lexical_scope (param_lst::scope_params) param_lst body)
        | LambdaOpt(param_lst, opt_param, body) ->
          (let all_params = List.append param_lst [opt_param] in
           LambdaOpt'(param_lst, opt_param, annotate_lexical_scope (all_params::scope_params) all_params body))
        | Applic(applic, args) -> Applic'(annotate_expr applic, List.map annotate_expr args) in annotate_lexical_scope [] [] e;;

  let annotate_tail_calls e =
    let rec annotate_expr_lst_tp in_tp = function
      | [] -> raise X_this_should_not_happen
      | [last_expr] -> [annotate_tp in_tp last_expr]
      | expr::rest_exprs -> List.append [(annotate_tp false expr)] (annotate_expr_lst_tp in_tp rest_exprs);
    and annotate_tp in_tp expr = match expr with
      | If'(test, dit, dif) -> If'(annotate_tp false test, annotate_tp in_tp dit, annotate_tp in_tp dif)
      | Seq' exprs -> Seq'(annotate_expr_lst_tp in_tp exprs)
      | Set'(var_name, expr) -> Set'(var_name, annotate_tp false expr)
      | Def'(var_name, expr) -> Def'(var_name, annotate_tp false expr)
      | Or' exprs -> Or'(annotate_expr_lst_tp in_tp exprs)
      | LambdaSimple'(param_lst, body) -> LambdaSimple'(param_lst, annotate_tp true body)
      | LambdaOpt'(param_lst, opt_param, body) -> LambdaOpt'(param_lst, opt_param, annotate_tp true body)
      | Applic'(applic, args) when in_tp -> ApplicTP'(annotate_tp false applic, List.map (annotate_tp false) args)
      | Applic'(applic, args) -> Applic'(annotate_tp false applic, List.map (annotate_tp false) args)
      | _ -> expr in annotate_tp false e;;

  let should_box param body =
    let rec read_write_occurrences check_func closure fst_scope same_param_ref = function
      | If'(test, dit, dif) ->
        (check_func closure fst_scope same_param_ref test)@(check_func closure fst_scope same_param_ref dit)@(check_func closure fst_scope same_param_ref dif)
      | Seq' exprs | Or' exprs ->
        (let read_write_closures = (List.map (fun (expr) -> (check_func closure fst_scope same_param_ref expr)) exprs) in
         List.fold_left (fun closures1 closures2 -> closures1@closures2) [] read_write_closures)
      | Set'(expr1, expr2) -> (check_func closure fst_scope same_param_ref expr1)@(check_func closure fst_scope same_param_ref expr2)
      | Def'(var_name, expr) -> (check_func closure fst_scope same_param_ref expr)
      | Applic'(applic, args) | ApplicTP'(applic, args) ->
        (let applic_args_closures = List.map (fun (expr) -> (check_func closure fst_scope same_param_ref expr)) args in
         check_func closure fst_scope same_param_ref applic@(List.fold_left (fun closures1 closures2 -> closures1@closures2) [] applic_args_closures))
      | LambdaSimple'(param_lst, body) -> check_closure check_func closure fst_scope same_param_ref param_lst body (ref body)
      | LambdaOpt'(param_lst, opt_param, body) -> check_closure check_func closure fst_scope same_param_ref (param_lst@[opt_param]) body (ref body)
      | BoxSet'(var_name, expr) -> (check_func closure fst_scope same_param_ref expr)
      | _ -> [];
    and check_closure check_func prev_closure fst_scope same_param_ref params body curr_closure =
      let override_param = List.mem param params in
      if fst_scope then check_func curr_closure false (not override_param) body
      else if same_param_ref then check_func prev_closure fst_scope (not override_param) body
      else check_func prev_closure fst_scope same_param_ref body;
    and read_occurrence closure fst_scope same_param_ref = function
      | Set'(Var'(VarBound(var_name, _, _)) as var, expr) | Set'(Var'(VarParam(var_name, _)) as var, expr) ->
        (let condition = (match var with
             | Var'(VarBound(var_name, _, _)) -> var_name = param && same_param_ref
             | Var'(VarParam(var_name, _)) -> var_name = param && same_param_ref && fst_scope
             | _ -> false) in
         if condition then (read_occurrence closure fst_scope same_param_ref expr)
         else read_occurrence closure fst_scope same_param_ref var@(read_occurrence closure fst_scope same_param_ref expr))
      | Var'(VarBound(var_name, _, _)) -> if param = var_name && same_param_ref then [!closure] else []
      | Var'(VarParam(var_name, _)) -> if param = var_name && fst_scope then [body] else []
      | expr' -> read_write_occurrences read_occurrence closure fst_scope same_param_ref expr';
    and write_occurrence closure fst_scope same_param_ref = function
      | Set'(Var'(VarBound(var_name, _, _)) ,expr) ->
        if var_name = param && same_param_ref then [!closure]@(write_occurrence closure fst_scope same_param_ref expr)
        else (write_occurrence closure fst_scope same_param_ref expr)
      | Set'(Var'(VarParam(var_name, _)),expr) ->
        if var_name = param && fst_scope then [body]@(write_occurrence closure fst_scope same_param_ref expr)
        else (write_occurrence closure fst_scope same_param_ref expr)
      | expr' -> read_write_occurrences write_occurrence closure fst_scope same_param_ref expr';
    and check_not_sharing_lexical_rib closure = function
      | [] -> false
      | curr_closure::closures -> if closure == curr_closure then check_not_sharing_lexical_rib closure closures else true in
    let read_closures = read_occurrence (ref body) true true body in
    let write_closures = write_occurrence (ref body) true true body in
    let map_check_read_write_diff_ribs closures opposite_closures =
      List.exists (fun indicator -> indicator = true) (List.map (fun closure -> check_not_sharing_lexical_rib closure closures) opposite_closures) in
    map_check_read_write_diff_ribs write_closures read_closures ||
    map_check_read_write_diff_ribs read_closures write_closures;;

  let box_lambda_params param_lst body =
    let to_box_params = List.filter (fun (param, minor_idx) -> should_box param body) (List.mapi (fun minor_idx param -> (param, minor_idx)) param_lst) in
    let box_param param body =
      let rec replace_occurences replace_func expr = match expr with
        | BoxSet'(var_name, expr) -> BoxSet'(var_name, replace_func expr)
        | If'(test, dit, dif) -> If'(replace_func test, replace_func dit, replace_func dif)
        | Seq' exprs -> Seq'(List.map (fun expr -> replace_func expr) exprs)
        | Or' exprs -> Or'(List.map (fun expr -> replace_func expr) exprs)
        | Set'(Var'(VarFree var_name) as var, expr) -> Set'(var, replace_func expr)
        | Def'(var_name, expr) -> Def'(var_name, replace_func expr)
        | LambdaSimple'(param_lst, body) as lambda ->
          if List.mem param param_lst then lambda else LambdaSimple'(param_lst, replace_func body)
        | LambdaOpt'(param_lst, opt_param, body) as lambda ->
          if List.mem param (param_lst@[opt_param]) then lambda else LambdaOpt'(param_lst, opt_param, replace_func body)
        | Applic'(applic, args) -> Applic'(replace_func applic, List.map (fun arg -> replace_func arg) args)
        | ApplicTP'(applic, args) -> ApplicTP'(replace_func applic, List.map (fun arg -> replace_func arg) args)
        | _ -> expr;
      and replace_get_occurences expr = match expr with
        | Var'(VarBound(var_name, _, _) as var) | Var'(VarParam(var_name, _) as var) ->
          if var_name = param then BoxGet'(var) else expr
        | Set'(Var'(VarBound(var_name, _, _)) as var, expr) | Set'(Var'(VarParam(var_name, _))  as var, expr) ->
          if var_name = param then Set'(var, replace_get_occurences expr)
          else Set'(replace_get_occurences var, replace_get_occurences expr)
        | expr' -> replace_occurences replace_get_occurences expr';
      and replace_set_occurences expr = match expr with
        | Set'(Var'(VarBound(var_name, _, _) as con_var) as var, expr) | Set'(Var'(VarParam(var_name, _) as con_var)  as var, expr) ->
          if var_name = param then BoxSet'(con_var, replace_set_occurences expr)
          else Set'(var, replace_set_occurences expr)
        | expr' -> replace_occurences replace_set_occurences expr' in
      replace_set_occurences (replace_get_occurences body) in
    let add_set_exprs expr =
      let set_box_exprs = List.fold_right (fun (param, minor_idx) set_exprs -> Set'(Var'(VarParam(param, minor_idx)), Box'(VarParam(param, minor_idx)))::set_exprs) to_box_params [] in
      if set_box_exprs <> [] then Seq'(set_box_exprs@[expr]) else expr in
    add_set_exprs (List.fold_right (fun (param, minor_idx) expr -> box_param param expr) to_box_params body);;

  let box_set e =
    let rec box_expr e = match e with
      | BoxSet'(var_name, expr) -> BoxSet'(var_name, box_expr expr)
      | If'(test, dit, dif) -> If'(box_expr test, box_expr dit, box_expr dif)
      | Seq' exprs -> Seq'(List.map box_expr exprs)
      | Set'(var_name, expr) -> Set'(var_name, box_expr expr)
      | Def'(var_name, expr) -> Def'(var_name, box_expr expr)
      | Or' exprs -> Or'(List.map box_expr exprs)
      | LambdaSimple'(param_lst, body) -> LambdaSimple'(param_lst, box_expr(box_lambda_params param_lst body))
      | LambdaOpt'(param_lst, opt_param, body) -> LambdaOpt'(param_lst, opt_param, box_expr(box_lambda_params (param_lst@[opt_param]) body))
      | Applic'(applic, args) -> Applic'(box_expr applic, List.map box_expr args)
      | ApplicTP'(applic, args) -> ApplicTP'(box_expr applic, List.map box_expr args)
      | _ -> e in box_expr e

  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr));;

end;; (* struct Semantics *)
