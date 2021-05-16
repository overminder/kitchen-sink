open Base
module P = Parser_comb

type s_expr =
| S_atom of string
| S_list of s_list

and s_list = {
  xs: s_expr list;
  tail: s_expr option;
}

let p_ws = P.many (P.p_that Char.is_whitespace) |> P.map_p (fun _ -> ())
let p_ident = P.latter_p p_ws @@ P.many1 (P.p_that Char.is_alpha) |> P.map_p String.of_char_list

let rec p_expr () =
  P.orElse (P.lazy p_atom) p_list

and p_atom () =
  p_ident |> P.map_p (fun x -> S_atom x)

and p_list () =
  let lpar = P.latter_p p_ws (P.p_char '(') in
  let rpar = P.latter_p p_ws (P.p_char ')') in
  let exprs = P.many p_expr in
  P.latter_p lpar (P.former_p exprs rpar)
