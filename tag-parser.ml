#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                          (expr_eq th1 th2) &&
                                          (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                           (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
    (List.for_all2 String.equal vars1 vars2) &&
    (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
    (String.equal var1 var2) &&
    (List.for_all2 String.equal vars1 vars2) &&
    (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
    (expr_eq e1 e2) &&
    (List.for_all2 expr_eq args1 args2)
  | _ -> false;;


exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct
  open Reader;;

  (*
  * Tag Parser from Sexpr to Expr for ChezScheme, 2019
  * Programmed by:
  *   Itay Bouganim, 305278384
  *   Sahar Vaya, 205583453
  *)
  let reserved_word_list =
    ["and"; "begin"; "cond"; "define"; "else";
     "if"; "lambda"; "let"; "let*"; "letrec"; "or";
     "quasiquote"; "quote"; "set!"; "unquote";
     "unquote-splicing"];;

  (* work on the tag parser starts here *)

  let rec check_dup_var_exists var_lst opt_var =
    match var_lst with
    | [] -> false
    | car::cdr -> List.exists ((=) car) cdr || opt_var = car || check_dup_var_exists cdr opt_var

  let rec pair_sexp_to_sexp_lst pair_sexpr =
    match pair_sexpr with
    | Nil -> []
    | Pair(sexpr, sexpr_rest) -> sexpr::(pair_sexp_to_sexp_lst sexpr_rest)
    | sexpr -> [sexpr]

  let sexp_lst_to_pair_lst sexp_lst =
    List.fold_right (fun sexpr1 sexpr2 -> Pair(sexpr1, sexpr2)) sexp_lst Nil;;

  let check_not_reserved_word word =
    if (andmap (fun reserved -> word <> reserved) reserved_word_list)
    then word else raise X_syntax_error

  let rec tag_parse reserved_args sexpr =
    match sexpr with
    | Bool _ | Number _ | Char _ | String _ | TagRef _ -> Const(Sexpr sexpr)
    | Symbol(sym_str) when (List.mem sym_str reserved_args) -> Var(sym_str)
    | Symbol(sym_str) -> Var(check_not_reserved_word sym_str)
    | TaggedSexpr(tag, Pair(Symbol("quote"), Pair(sexpr, Nil))) -> Const(Sexpr(TaggedSexpr(tag, sexpr)))
    | TaggedSexpr _ -> Const(Sexpr sexpr)
    | Pair(Symbol sym as applic, args) when (List.mem sym reserved_args) -> tag_parse_applic applic args reserved_args
    | Pair(Symbol "if", Pair(test, Pair(dit, maybe_dif))) -> tag_parse_if test dit maybe_dif reserved_args
    | Pair(Symbol "lambda", Pair(args, body)) -> tag_parse_lambda args body reserved_args
    | Pair(Symbol "or", args) -> tag_parse_or args reserved_args
    | Pair(Symbol "and", preds) -> expand_and reserved_args preds
    | Pair(Symbol "define", Pair(Pair(var_name_sexpr, arg_list), exprs)) -> expand_mit_define var_name_sexpr arg_list exprs reserved_args
    | Pair(Symbol "define", Pair(var_name_sexpr, value_sexpr)) -> tag_parse_define var_name_sexpr value_sexpr reserved_args
    | Pair(Symbol "set!", Pair(set_var_sexpr, Pair(set_value_sexpr, Nil))) -> Set((tag_parse reserved_args set_var_sexpr), (tag_parse reserved_args set_value_sexpr))
    | Pair(Symbol "begin", begin_sexprs) -> tag_parse_begin (pair_sexp_to_sexp_lst begin_sexprs) reserved_args
    | Pair(Symbol "let", Pair(ribs, body)) -> expand_let ribs body reserved_args
    | Pair(Symbol "let*", Pair(ribs, body)) -> expand_let_star ribs body reserved_args
    | Pair(Symbol "letrec", Pair(ribs, body)) -> expand_let_rec ribs body reserved_args
    | Pair(Symbol "cond", ribs) -> expand_cond (pair_sexp_to_sexp_lst ribs) reserved_args
    | Pair(Symbol "quote", Pair(sexp, Nil)) -> Const(Sexpr sexp)
    | Pair(Symbol "quasiquote", Pair(sexp, Nil)) -> tag_parse [] (expand_quasiquote sexp)
    | Pair(applic, args) -> tag_parse_applic applic args reserved_args
    | _ -> raise X_syntax_error;

  and tag_parse_if test dit maybe_dif reserved_args =
    If(tag_parse reserved_args test, tag_parse reserved_args dit,
       match maybe_dif with
       | Nil -> Const(Void)
       | Pair(dif, Nil) -> tag_parse reserved_args dif
       | _ -> raise X_syntax_error);

  and tag_parse_lambda_args = function
    | Nil -> ([], Nil)
    | (Symbol _) as optional -> ([], optional)
    | Pair(Symbol arg, rest_args) ->
      (match (tag_parse_lambda_args rest_args) with
       | (args, opt_args) -> (arg::args, opt_args))
    | _ -> raise X_syntax_error;

  and tag_parse_lambda args body reserved_args =
    let lambda_body = (pair_sexp_to_sexp_lst body) in
    match lambda_body with
    | [] -> raise X_syntax_error
    | _ ->
      ( let lambda_args = tag_parse_lambda_args args in
        let curr_reserved_args = List.filter (fun word -> List.mem word reserved_word_list) (fst lambda_args) in (* add opt *)
        let lambda_body = tag_parse_begin lambda_body (reserved_args@curr_reserved_args) in
        match lambda_args with
        | (arg_list, Nil) ->
          if check_dup_var_exists arg_list "" then raise X_syntax_error
          else LambdaSimple(arg_list, lambda_body)
        | (arg_list, opt_arg) ->
          (match opt_arg with
           | Symbol opt_arg_str ->
             if check_dup_var_exists arg_list opt_arg_str then raise X_syntax_error
             else LambdaOpt(arg_list, opt_arg_str, lambda_body)
           | _ -> raise X_syntax_error));

  and tag_parse_applic applic args reserved_args =
    Applic(tag_parse reserved_args applic, (List.map (tag_parse reserved_args) (pair_sexp_to_sexp_lst args)))

  and tag_parse_or args reserved_args =
    let arg_lst = pair_sexp_to_sexp_lst args in
    match arg_lst with
    | [] -> Const(Sexpr(Bool false))
    | [sexpr] -> tag_parse reserved_args sexpr
    | _ -> Or(List.map (tag_parse reserved_args) arg_lst)

  and tag_parse_define var_name_sexpr value_sexpr reserved_args =
    match var_name_sexpr with
    | Symbol sym_name ->
      (match value_sexpr with
       | Pair(def_value_sexpr, Nil) -> Def ((tag_parse reserved_args var_name_sexpr), (tag_parse reserved_args def_value_sexpr))
       | _ -> raise X_syntax_error)
    | _ -> raise X_syntax_error;

  and tag_parse_begin begin_sexprs reserved_args =
    match begin_sexprs with
    | [] -> Const(Void)
    | [sexpr] -> (tag_parse reserved_args sexpr)
    | _ -> Seq (List.map (tag_parse reserved_args) begin_sexprs);

  and expand_quasiquote sexpr =
    match sexpr with
    | Pair(Symbol("unquote"), Pair(sexpr, Nil)) -> sexpr
    | Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil)) ->
      raise X_syntax_error
    | Nil | Symbol _ -> Pair(Symbol "quote", Pair(sexpr, Nil))
    | Pair(car, cdr) ->
      (match (car, cdr) with
       | (Pair(Symbol("unquote-splicing"), Pair(car, Nil)), cdr) ->
         Pair(Symbol "append", Pair(car, Pair(expand_quasiquote cdr, Nil)))
       |(car, Pair(Symbol("unquote-splicing"), Pair(cdr, Nil))) ->
         Pair(Symbol "cons", Pair(expand_quasiquote car, Pair(cdr, Nil)))
       | _ -> Pair(Symbol "cons", Pair(expand_quasiquote car, Pair(expand_quasiquote cdr, Nil))))
    | _ -> sexpr;

  and expand_cond ribs reserved_args =
    match ribs with
    | [] -> Const(Void)
    | rib::rest_ribs -> (match rib with
        | Pair(Symbol "else", seq) -> tag_parse_begin (pair_sexp_to_sexp_lst seq) reserved_args
        | Pair(test, Pair(Symbol "=>", Pair(applic, Nil))) ->
          (let rest_exp = if rest_ribs = [] then Nil else Pair(Pair(Symbol "rest", Nil), Nil) in
           let if_exp = (Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), rest_exp))), Nil)) in
           let lambda_f = (Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair (applic, Nil))), Nil))) in
           let lambda_rest = LambdaSimple([], (expand_cond rest_ribs reserved_args)) in
           let expanded_let = (tag_parse reserved_args (Pair (Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(test, Nil)), Pair(lambda_f , Nil)), if_exp)))) in
           (match expanded_let with
            | Applic(LambdaSimple(args, If(test, dit, dif)), applic_lst) ->
              Applic(LambdaSimple((if rest_ribs = [] then args else args@["rest"]), If(test, dit, dif)), (if rest_ribs = [] then applic_lst else applic_lst@[lambda_rest]))
            | _ -> raise X_syntax_error))
        | Pair(test, Pair(Symbol "=>", Pair(applic, _))) -> raise X_syntax_error
        | Pair(test, sexprs) -> If(tag_parse reserved_args test, tag_parse_begin (pair_sexp_to_sexp_lst sexprs) reserved_args, expand_cond rest_ribs reserved_args)
        | _ -> raise X_syntax_error);

  and expand_let ribs body reserved_args =
    let exp_ribs = (pair_sexp_to_sexp_lst ribs) in
    let args = List.map(fun rib ->
        match rib with
        | Pair(param_name, Pair(expr, Nil)) -> param_name
        | _ -> raise X_syntax_error) exp_ribs in
    let args = (match (tag_parse_lambda_args (sexp_lst_to_pair_lst args)) with
        |  (arg_list, Nil) -> arg_list
        | _ -> raise X_syntax_error) in
    let params = List.map(fun arg ->
        match arg with
        | Pair(arg_name, Pair(expr, Nil)) -> expr
        | _ -> raise X_syntax_error) exp_ribs in
    let body = (match (tag_parse_begin (pair_sexp_to_sexp_lst body) reserved_args) with
        | Const(Void) -> raise X_syntax_error
        | begin_exp -> begin_exp) in
    Applic(LambdaSimple(args, body), (List.map (tag_parse reserved_args) params));

  and expand_let_star ribs body reserved_args =
    let exp_ribs = (pair_sexp_to_sexp_lst ribs) in
    match exp_ribs with
    | [] | [_] -> tag_parse reserved_args (Pair(Symbol("let"), Pair(ribs, body)))
    | rib::rest_ribs ->
      tag_parse reserved_args (Pair(Symbol("let"), Pair(Pair(rib, Nil), Pair(Pair(Symbol("let*"), Pair((sexp_lst_to_pair_lst rest_ribs), body)), Nil))));

  and expand_let_rec ribs body reserved_args =
    let expr_ribs = (pair_sexp_to_sexp_lst ribs) in
    let expanded_body = List.fold_right (fun expr1 expr2 -> Pair(expr1, expr2))
        (List.map2 (fun def_name expr -> Pair(Symbol "set!", Pair(def_name, Pair(expr, Nil))))
           (List.map(fun rib -> match rib with
                | Pair(def_name, Pair(expr, Nil)) -> def_name
                | _ -> raise X_syntax_error
              ) expr_ribs)
           (List.map (fun rib -> match rib with
                | Pair(def_name, Pair(expr, Nil)) -> expr
                | _ -> raise X_syntax_error
              ) expr_ribs)) body in
    let expanded_ribs = List.fold_right (fun expr1 expr2 -> Pair(expr1, expr2))
        (List.map (fun rib -> match rib with
             | Pair(def_name, Pair(expr, Nil)) -> Pair(def_name, Pair(Pair(Symbol("quote"), Pair(Symbol "whatever", Nil)), Nil))
             | _ -> raise X_syntax_error) expr_ribs) Nil in
    tag_parse reserved_args (Pair(Symbol "let", Pair(expanded_ribs, expanded_body)));

  and expand_and reserved_args = function
    | Pair(pred, Nil) -> tag_parse reserved_args pred
    | Pair(pred, Pair(next_pred, Nil)) -> If(tag_parse reserved_args pred, tag_parse reserved_args next_pred, Const(Sexpr (Bool false)))
    | Pair(pred, rest_preds) -> If(tag_parse reserved_args pred, tag_parse reserved_args (Pair (Symbol "and", rest_preds)), Const (Sexpr (Bool false)))
    | Nil -> Const (Sexpr (Bool true))
    | _ -> raise X_syntax_error;

  and expand_mit_define var_name_sexpr arg_list exprs reserved_args =
    match var_name_sexpr with
    | Symbol var_name -> tag_parse reserved_args (Pair(Symbol "define", Pair(Symbol var_name, Pair(Pair(Symbol "lambda", Pair(arg_list, exprs)), Nil))))
    | _ -> raise X_syntax_error;;

  let tag_parse_expression sexpr = tag_parse [] sexpr;;

  let tag_parse_expressions sexpr = List.map (tag_parse []) sexpr;;

end;; (* struct Tag_Parser *)
