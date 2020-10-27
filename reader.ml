#use "pc.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type number =
  | Int of int
  | Float of float;;

type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2)
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;

module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
  open PC;;

  (*
  * Sexpr Reader for ChezScheme, 2019
  * Programmed by:
  *   Itay Bouganim, 305278384
  *   Sahar Vaya, 205583453
  *)
  let normalize_scheme_symbol str =
    let s = string_to_list str in
    if (andmap
          (fun ch -> (ch = (lowercase_ascii ch)))
          s) then str
    else Printf.sprintf "|%s|" str;;


  (* Terminal parsers*)
  let t_digit = range '0' '9';;
  let t_lowercase_chars = range 'a' 'z';;
  let t_uppercase_chars = range 'A' 'Z';;


  (* Symbol parser *)
  let nt_symbol =
    let t_puncuation = one_of "!$^*-_=+<>?/:" in
    let t_uppercase_chars = pack t_uppercase_chars (fun ch -> lowercase_ascii ch) in
    let nt_symbol_char = disj_list [t_digit; t_puncuation; t_lowercase_chars; t_uppercase_chars] in
    let nt = plus nt_symbol_char in
    pack nt (fun sym -> Symbol (list_to_string sym));;


  (* Boolean parser *)
  let nt_boolean =
    let t_false = word_ci "#f" in
    let t_true = word_ci "#t" in
    let nt = disj (pack t_false (fun _ -> Bool false)) (pack t_true (fun _ -> Bool true)) in nt;;


  (* Number parser *)
  let nt_sign =
    let t_plus = pack (char '+') (fun _ -> 1) in
    let t_minus = pack (char '-') (fun _ -> -1) in
    let nt = pack (maybe (disj t_plus t_minus)) (function
        | None -> 1
        | Some(sign) -> sign) in nt;;

  let nt_natural = pack (plus t_digit) (fun str -> (list_to_string str));;
  let nt_integer_string = pack (caten nt_sign nt_natural) (fun (sign, natural) -> string_of_int (sign * (int_of_string natural)));;
  let nt_integer =
    pack nt_integer_string (fun num -> Number(Int (int_of_string num)));;

  let nt_float =
    let t_dec_point = pack (char '.') (fun _ -> '.') in
    let nt = caten (caten (caten nt_sign nt_integer_string) t_dec_point) (nt_natural) in
    let nt = pack nt (fun ((((sign, int_digits), dec_point)), frac_digits) -> (sign, float_of_string (int_digits ^ (String.make 1 dec_point) ^ frac_digits))) in
    pack nt (fun (sign, float) -> Number(Float ((float_of_int sign) *. float)));;


  (* Scientific notation parser *)
  let t_scientific_sign = pack (char_ci 'e') (fun _ -> 'e');;

  let nt_scientific_number_float =
    let nt = caten (caten nt_float t_scientific_sign) nt_integer in
    pack nt (fun ((base, _), exponent) ->
        match base, exponent with
        | Number(Float(num)), Number(Int(exp)) -> Number(Float(num *. (10. ** (float_of_int exp))))
        | _ -> raise X_no_match);;

  let nt_scientific_number_integer =
    let nt = caten (caten nt_integer t_scientific_sign) nt_integer in
    pack nt (fun ((base, _), exponent) ->
        match base, exponent with
        | Number(Int(num)), Number(Int(exp)) -> Number(Float((float_of_int num) *. (10. ** (float_of_int exp))))
        | _ -> raise X_no_match);;

  let nt_scientific_number = disj nt_scientific_number_float nt_scientific_number_integer;;


  (* Radix notation parser *)
  let nt_radix_number_prefix =
    let nt_radix = pack nt_natural (fun radix_str -> Number(Int(int_of_string radix_str))) in
    pack (caten (char '#') (caten (nt_radix) (char_ci 'r'))) (fun (_, (radix, _)) ->
        match radix with
        | Number(Int(radix)) -> if (radix >= 2 && radix <= 36) then radix else raise X_this_should_not_happen
        | _ -> raise X_no_match);
  and nt_radix_digits = plus (disj_list [t_digit; t_lowercase_chars; t_uppercase_chars]);;

  let calculate_radix_number radix sign rdx_digits starting_exponent =
    let rdx_digits_reversed = List.map lowercase_ascii (List.rev rdx_digits) in
    let rdx_number =
      (let rec create_rdx_number exponent acc char_lst =
         match char_lst with
         | [] -> acc
         | car :: cdr -> create_rdx_number (exponent + 1) (acc +. ((
             match car with
             | car when (car >= '0' && car <= '9') ->
               if ((int_of_char car - int_of_char '0') < radix)
               then float_of_int (int_of_char car - int_of_char '0') else raise X_this_should_not_happen
             | car when (car >= 'a' && car <= 'z') ->
               if ((int_of_char car - int_of_char 'a' + 10) < radix)
               then float_of_int (int_of_char car - int_of_char 'a' + 10) else raise X_this_should_not_happen
             | _ -> raise X_no_match
           ) *. ((float_of_int radix) ** (float_of_int exponent)))) cdr;
       in create_rdx_number starting_exponent 0. rdx_digits_reversed) in sign *. rdx_number;;

  let nt_radix_number_integer =
    let nt = caten nt_radix_number_prefix (caten nt_sign nt_radix_digits) in
    pack nt (fun (radix, (sign, rdx_digits)) -> Number(Int ((int_of_float (calculate_radix_number radix (float_of_int sign) rdx_digits 0)))));;

  let nt_radix_number_float =
    let nt = caten nt_radix_number_prefix (caten nt_sign (caten (caten nt_radix_digits (char '.')) nt_radix_digits)) in
    pack nt (fun (radix, (sign, ((int_part_lst, _), frac_part_lst))) ->
        let radix_number = List.append int_part_lst frac_part_lst in
        let dec_point_index = List.length int_part_lst in
        let radix_length = List.length radix_number in
        Number(Float ((calculate_radix_number radix (float_of_int sign) radix_number (dec_point_index - radix_length)))));;

  let nt_radix_number = disj nt_radix_number_float nt_radix_number_integer;;

  let nt_number = not_followed_by (disj_list [nt_radix_number; nt_scientific_number; nt_float; nt_integer]) nt_symbol;;


  (* String parser *)
  let nt_string_meta_char =
    let t_meta_char_return = pack (word_ci "\\r") (fun _ -> char_of_int 13) in
    let t_meta_char_newline = pack (word_ci "\\n") (fun _ -> char_of_int 10) in
    let t_meta_char_tab = pack (word_ci "\\t") (fun _ -> char_of_int 9) in
    let t_meta_char_page = pack (word_ci "\\f") (fun _ -> char_of_int 12) in
    let t_meta_char_backslash = pack (word_ci "\\\\") (fun _ -> char_of_int 92) in
    let t_meta_char_doublequote = pack (word_ci "\\\"") (fun _ -> char_of_int 34) in
    disj_list [t_meta_char_return; t_meta_char_newline; t_meta_char_tab; t_meta_char_page; t_meta_char_backslash; t_meta_char_doublequote];;

  let nt_string_literal_char = diff nt_any (one_of "\"\\");;

  let nt_string_chars =
    let nt_string_char = disj nt_string_meta_char nt_string_literal_char in
    star nt_string_char;;

  let nt_string =
    let nt_quote = char '\"' in
    let nt_str = pack (caten nt_quote nt_string_chars) (fun (_, str_lst) -> str_lst) in
    let nt_str = pack (caten nt_str nt_quote) (fun (str_lst, _) -> list_to_string str_lst) in
    let nt_str = pack nt_str (fun str -> String str) in nt_str;;


  (* Character parser *)
  let nt_named_char =
    let t_nul = pack (word_ci "nul") (fun _ -> char_of_int 0) in
    let t_newline = pack (word_ci "newline") (fun _ -> char_of_int 10) in
    let t_return = pack (word_ci "return") (fun _ -> char_of_int 13) in
    let t_tab = pack (word_ci "tab") (fun _ -> char_of_int 9) in
    let t_formfeed = pack (word_ci "page") (fun _ -> char_of_int 12) in
    let t_space = pack (word_ci "space") (fun _ -> char_of_int 32) in
    let named_char_lst = [t_nul; t_newline; t_return; t_tab; t_formfeed; t_space] in
    disj_list named_char_lst;;

  let nt_visible_char =
    let nt_not_visible = range (char_of_int 0) (char_of_int 32) in
    let t = diff nt_any nt_not_visible in t;;

  let nt_char =
    let t_char_prefix = word_ci "#\\" in
    let nt = disj nt_named_char nt_visible_char in
    let nt = caten t_char_prefix nt in
    let nt = pack nt (fun (_, ch) -> Char ch) in nt;;


  (* TagReference parser *)
  let nt_tag = pack (caten (caten (word "#{") nt_symbol) (char '}')) (fun ((_, symbol), _) ->
      match symbol with
      | Symbol(symbol_str) -> TagRef(symbol_str)
      | _ -> raise X_no_match);;


  (* Comments and Whitespaces parsers *)
  let nt_newline = char '\n';;
  let nt_whitespaces = pack (star nt_whitespace) (fun _ -> Nil);;

  let nt_comment =
    let t_comment_start = char ';' in
    let nt_comment = star (diff nt_any nt_newline) in
    let nt_comment = caten t_comment_start nt_comment in
    let nt_comment_end = disj nt_newline (pack nt_end_of_input (fun _ -> '\n')) in
    let nt_comment = caten nt_comment nt_comment_end in
    pack nt_comment (fun _ -> Nil);;


  (* SExpression, SExpression comments, Lists, Quotes and TaggedSExpressions parsers *)
  let dispose_left_right nt_left nt_right nt =
    let nt = caten nt_left nt in
    let nt = pack nt (function (_, exp) -> exp) in
    let nt = caten nt nt_right in
    let nt = pack nt (function (exp, _) -> exp) in
    nt;;

  let rec check_duplicate_tags sexpr =
    let tag_lst =
      (let rec generate_tag_lst tag_lst sexpr = match sexpr with
          | TaggedSexpr(tag, tagged_sexpr) -> tag :: (generate_tag_lst tag_lst tagged_sexpr)
          | Pair(sexpr1, sexpr2) -> List.append (generate_tag_lst tag_lst sexpr1) (generate_tag_lst tag_lst sexpr2)
          | _ -> tag_lst in generate_tag_lst [] sexpr) in
    (let rec check_duplicate = function
        | [] -> false
        | car::cdr -> List.exists ((fun tag1 tag2 -> tag1 = tag2) car) cdr || check_duplicate cdr in check_duplicate tag_lst)

  let rec nt_sexpr char_lst =
    let nts = disj_list [nt_boolean; nt_char; nt_number; nt_string; nt_symbol; nt_list; nt_dotted_list; nt_quote; nt_quasiquote; nt_unquote; nt_unquote_spliced; nt_sexpr_comment; nt_tagged_sexpr] in
    let nts = dispose_left_right nt_ignored nt_ignored nts in
    match (nts char_lst) with
    | (sexpr, char_lst) as result -> if not (check_duplicate_tags sexpr) then result else raise X_this_should_not_happen;

  and nt_sexpr_comment char_lst =
    let nt_sexp_comment_start = word_ci "#;" in
    let nt = pack (caten nt_sexp_comment_start nt_sexpr) (fun _ -> Nil) in
    nt char_lst;

  and nt_ignored char_lst =
    let nt = pack (star (disj_list [pack (nt_whitespace) (fun _ -> Nil); nt_comment; nt_sexpr_comment])) (fun _ -> Nil) in
    nt char_lst;

  and nt_list char_lst =
    let nt = star nt_sexpr in
    let nt = pack (dispose_left_right nt_ignored nt_ignored nt) (fun exp -> exp) in
    let nt = pack (caten (char '(') (caten nt (char ')'))) (fun (_, (sexpr_lst, _)) -> sexpr_lst) in
    let nt = pack nt (function
        | [] -> Nil
        | sexpr_lst -> List.fold_right (fun sexp1 sexp2 -> Pair(sexp1, sexp2)) sexpr_lst Nil) in
    nt char_lst;

  and nt_dotted_list char_lst =
    let nt_sexprs_pre_dot = plus nt_sexpr in
    let nt_sexpr_after_dot = pack (caten nt_sexpr (char ')')) (fun (sexp, _) -> sexp) in
    let nt = pack (caten (char '.') nt_sexpr_after_dot) (fun (_, sexp) -> sexp) in
    let nt = caten nt_sexprs_pre_dot nt in
    let nt = pack (caten (char '(') nt) (fun (_, sexpr_pair) -> sexpr_pair) in
    let nt = pack nt (fun (sexprs_lst, sexpr) ->
        match sexprs_lst with
        | [] -> raise X_no_match
        | sexpr_lst -> List.fold_right (fun sexp1 sexp2 -> Pair(sexp1, sexp2)) sexpr_lst sexpr) in
    nt char_lst;

  and nt_quote char_lst =
    let t_quoted = pack (word_ci "'") (fun _ -> "'") in
    let nt = pack (caten t_quoted nt_sexpr) (fun (_,sexp)-> Pair(Symbol("quote"), Pair(sexp, Nil))) in
    nt char_lst;

  and nt_quasiquote char_lst =
    let t_qquoted = pack (char '`') (fun _ -> '`') in
    let nt = pack (caten t_qquoted nt_sexpr) (fun (_,sexp)-> Pair(Symbol("quasiquote"), Pair(sexp, Nil))) in
    nt char_lst;

  and nt_unquote char_lst =
    let t_unquoted = pack (char ',') (fun _ -> ',') in
    let nt = pack (caten t_unquoted nt_sexpr) (fun (_,sexp)-> Pair(Symbol("unquote"), Pair(sexp, Nil))) in
    nt char_lst;

  and nt_unquote_spliced char_lst =
    let t_unquotedspliced = pack (word_ci ",@") (fun _ -> ",@") in
    let nt = pack (caten t_unquotedspliced nt_sexpr) (fun (_,sexp)-> Pair(Symbol("unquote-splicing"), Pair(sexp, Nil))) in
    nt char_lst;

  and nt_tagged_sexpr char_lst =
    let nt = pack nt_tag (fun tag ->
        match tag with
        | TagRef(tag_str) -> tag_str
        | _ -> raise X_no_match) in
    let nt = pack (caten nt (maybe (caten (char '=') nt_sexpr))) (fun (tag, maybe_sexpr) ->
        match maybe_sexpr with
        | Some((_, sexpr)) -> TaggedSexpr(tag, sexpr)
        | None -> TagRef(tag)) in nt char_lst;;


  let read_sexpr string =
    let char_lst = string_to_list string in
    match (nt_sexpr char_lst) with
    | (sexpr, []) -> sexpr
    | _ -> raise X_no_match;;

  let read_sexprs string =
    let char_lst = string_to_list string in
    let nt_sexprs = star nt_sexpr in
    match (nt_sexprs char_lst) with
    | (sexpr_ast, []) -> sexpr_ast
    | (sexpr_ast, rest) ->
      (match (nt_ignored rest) with
       | (_, []) -> sexpr_ast
       | _ -> raise X_no_match)

end;; (* struct Reader *)