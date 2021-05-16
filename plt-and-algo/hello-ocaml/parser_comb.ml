open Base

(* Simple continuation based parser combinator *)

type source = {
  s: string;
  ix: int;
}

let make_source s = {
  s;
  ix = 0
}

let source_get (s: source): (char * source) option =
  if s.ix < String.length s.s
    then Some (String.get s.s s.ix, { s with ix = s.ix + 1 })
    else None

type 'a parser = {
  run: 'r. source -> ('a * source -> unit) -> unit
}

let pure (a: 'a): 'a parser = {
  run = fun source k -> k (a, source)
}

let bind (ma: 'a parser) (f: 'a -> 'b parser): 'b parser = {
  run = fun source0 kb ->
    let ka (a, source1) = (f a).run source1 kb in 
    ma.run source0 ka
}

exception ParseError of string

(*
let fail (reason: string): 'a parser = {
  run = fun source _k -> raise (ParseError (reason, source))
}
*)

let p_that (ok: char -> bool): char parser = {
  run = fun source k -> match source_get source with
    | Some (c, source') when ok c -> k (c, source')
    | _ -> ()
}

let p_char c = p_that (Char.equal c)

(* Not interleaving though *)
let orElse (m1: 'a parser) (m2: 'a parser): 'a parser = {
  run = fun source k ->
    let _ = m1.run source k in
    m2.run source k
}

let map_p (f: 'a -> 'b) (p: 'a parser): 'b parser = {
  run = fun source k ->
    let k1 (a, source') = k (f a, source') in
    p.run source k1
}

let latter_p (m1: 'a parser) (m2: 'b parser): 'b parser =
  bind m1 (fun _ -> m2)

let former_p (m1: 'a parser) (m2: 'b parser): 'a parser =
  bind m1 (fun a -> bind m2 (fun _ -> pure a))

let rec many (ma: 'a parser): ('a list) parser =
  orElse (many1 ma) (pure [])
and many1 (ma: 'a parser): ('a list) parser =
  bind ma (fun x -> bind (many ma) (fun xs -> pure (x :: xs)))

let parseOne (type a) (ma: a parser) (s: string): a =
  let module M = struct exception Parsed of a end in
  try
    let _ = ma.run (make_source s) (fun (x, _source) -> raise (M.Parsed x)) in
    raise (ParseError "Nothing parsed")
  with M.Parsed x -> x
