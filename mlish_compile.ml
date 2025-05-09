module ML = Mlish_ast
module S = Scish_ast

exception ImplementMe
let rec compile_exp ((e,_):ML.exp) : S.exp = 
  match e with
  | Var (v) -> S.Var v
  | PrimApp (primop, exp_list) -> compile_primop primop exp_list
  | Fn (v, e) -> S.Lambda (v, compile_exp e)
  | App (e1, e2) -> S.App (compile_exp e1, compile_exp e2)
  | If (e1, e2, e3) -> S.If ((compile_exp e1), (compile_exp e2), (compile_exp e3))
  | Let (v, e1, e2) -> S.sLet v (compile_exp e1) (compile_exp e2)

and compile_primop (primop:ML.prim) (exp_list:ML.exp list) : S.exp =
  match primop with
  | Int i -> S.Int i
  | Bool b -> if b == true then S.Int 1 else S.Int 0
  | Unit -> S.Int 0
  | Pair | Cons -> S.PrimApp ((S.Cons), [(compile_exp (List.hd exp_list)); (compile_exp (List.nth exp_list 1))])
  | Fst | Hd -> S.PrimApp ((S.Fst), [compile_exp (List.hd exp_list)])
  | Snd | Tl -> S.PrimApp ((S.Snd), [compile_exp (List.hd exp_list)])
  | Nil -> S.PrimApp (S.Cons, [S.Int 0; S.Int 0])
  | IsNil -> 
    let evaluated_val = compile_exp (List.hd exp_list) in
    let first = S.PrimApp (S.Fst, [evaluated_val]) in
    let second = S.PrimApp (S.Snd, [evaluated_val]) in
    S.If (first, S.Int 0, S.If (second, S.Int 0, S.Int 1))
  | _ ->  S.PrimApp ((
    match primop with
    | Plus -> S.Plus | Minus -> S.Minus
    | Times -> S.Times | Div -> S.Div
    | Eq -> S.Eq | Lt -> S.Lt
  ), ([(compile_exp (List.hd exp_list)); (compile_exp (List.nth exp_list 1))]))
