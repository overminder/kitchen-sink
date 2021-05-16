let foo x =
  match x with
  | 1 -> 5
  | _ -> 6
;;

(* function (lambda case in Hs),
    ~:f for named param,
    as (@ in Hs) *)
let rec mapL ~f = function
  | [] as l -> l
  | x :: xs -> f x :: mapL xs ~f:f
;;

(* record: named product types *)
type p2d = {
  x: int;
  y: int;
}

type p3d = {
  x: int;
  y: int;
  z: int;
}

(* record field punning

   Also without the `: p2d` annotation, the arg type will be inferred as p3d. *)
let sum2d ({x; y}: p2d): int = x + y;;

let _ = sum2d { x = 5; y = 6 };;

(* sum types

   Also recursive type defs: `type ... and ...` *)
type 'a my_cons = {
  head: 'a;
  tail: 'a my_list
} and 'a my_list =
| My_cons of 'a my_cons
| My_nil
;;

let rec to_my_cons xs =
  match xs with
  | [] -> My_nil 
  | x :: xs -> My_cons { head = x; tail = to_my_cons xs }
;;

let arr = [|1;2;3|];;
arr.(0) <- 5;;
let _ = arr.(0) + 1;;

type id_gen = {
  mutable next_id: int;
}

let make_id_gen (): id_gen = { next_id = 0 };;

let get_next_id (g: id_gen): int =
  let res = g.next_id in
  g.next_id <- res + 1;
  res
;;
