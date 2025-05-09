open Mlish_ast

exception TypeError
exception NOT_FOUND of string
exception IMPLEMENT_ME

(**************************** HELPERS ****************************)

type ('k, 'v) varmap = ('k * 'v) list
let empty_varmap () : ('k, 'v) varmap = []
let insert_var (vm:('k, 'v) varmap) (k:'k) (v:'v) : ('k, 'v) varmap = (k, v)::vm
let rec lookup_var equals_f (vm:('k, 'v) varmap) (k:'k) : 'v = 
  match vm with
  | [] -> raise (NOT_FOUND ("Variable not found"))
  | ((key, value)::xs) -> if equals_f k key then value else lookup_var equals_f xs k

let type_error (s:string) = (print_string s; raise TypeError)

let guess () = Guess_t (ref None)

let unique_physical lst =
  let rec aux seen rest =
    (match rest with
    | [] -> seen
    | x :: xs ->
      if List.exists (fun y -> x == y) seen then aux seen xs
      else aux (x :: seen) xs) in
  aux [] lst

let tvarcounter = ref 0;;
let freshtvar () : string = 
  let curcount = !tvarcounter in
  tvarcounter := (curcount +1);
  "tvar"^(string_of_int curcount)

(************************* TYPE-INFERENCE *************************)

let rec type_check_exp (e:Mlish_ast.exp) : tipe = tc (empty_varmap()) e

and tc (env:(var * tipe_scheme) list) (exp:Mlish_ast.exp) : tipe =
  let (e, _) = exp in
  match e with
  | Var v -> instantiate (lookup_var (=) env v)
  | PrimApp(prim, exp_list) -> primop_tc prim env exp_list
  | Fn (v, e) -> 
    let g = guess() in
    Fn_t (g, (tc (insert_var env v (Forall([], g))) e))
  | App (e1, e2) ->
    let (t1, t2) = (tc env e1, tc env e2) in
    let g = guess() in
    if unify t1 (Fn_t (t2, g)) then g else raise TypeError
  | If (e1, e2, e3) -> 
    let (t1, t2, t3) = (tc env e1, tc env e2, tc env e3) in
    if (unify t1 Bool_t) && (unify t2 t3) then t2 else raise TypeError
  | Let (v, e1, e2) -> 
    let scheme = generalize env (tc env e1) in
    tc (insert_var env v scheme) e2

and primop_tc (primop:prim) (env:(var * tipe_scheme) list) (list:exp list) : tipe = 
  match primop with
  | Int _ -> Int_t
  | Bool _ -> Bool_t
  | Unit -> Unit_t
  | Plus | Minus | Times | Div ->
    let (t1, t2) = tc env (List.hd list), tc env (List.nth list 1) in
    if (unify t1 t2) && (unify t1 Int_t) then Int_t else raise TypeError
  | Eq | Lt ->
    let (t1, t2) = tc env (List.hd list), tc env (List.nth list 1) in
    if (unify t1 t2) && (unify t1 Int_t) then Bool_t else raise TypeError
  | Pair -> 
    Pair_t (tc env (List.hd list), tc env (List.nth list 1))
  | Fst -> 
    let t = (tc env (List.hd list)) in
    let (g1, g2) = (guess(), guess()) in
    if unify t (Pair_t (g1, g2)) then g1 else raise TypeError
  | Snd -> 
    let t = (tc env (List.hd list)) in
    let (g1, g2) = (guess(), guess()) in
    if unify t (Pair_t (g1, g2)) then g2 else raise TypeError
  | Nil -> List_t (Guess_t (ref None))
  | Cons -> 
    let (t1, t2) = (tc env (List.hd list), tc env (List.nth list 1)) in
    if unify (List_t t1) t2 then (List_t t1) else raise TypeError
  | IsNil -> 
    if unify (tc env (List.hd list)) (List_t (guess())) then Bool_t else raise TypeError
  | Hd -> 
    let g = guess() in
    if unify (tc env (List.hd list)) (List_t g) then g else raise TypeError
  | Tl -> 
    let t = (tc env (List.hd list)) in
    if unify t (List_t (guess())) then t else raise TypeError

and unify (t1:tipe) (t2:tipe) : bool = 
  if is_equal t1 t2 then true else (match t1, t2 with
  | Int_t, Int_t -> true
  | Bool_t, Bool_t -> true
  | Unit_t, Unit_t -> true
  | Pair_t (t1a, t1b), Pair_t (t2a, t2b) -> 
    unify t1a t2a && unify t1b t2b
  | List_t t1', List_t t2' -> unify t1' t2'
  | Guess_t g, _ -> (
    match !g with
    | Some t1' -> unify t1' t2
    | None -> if occurs g t2 then false else (g := Some t2; true)
  )
  | _, Guess_t _ -> unify t2 t1
  | Fn_t (t1a, t1b), Fn_t (t2a, t2b) -> 
    (unify t1a t2a && unify t1b t2b)
  | Pair_t (t1a, _), _ -> (unify t1a t2)
  | _, Pair_t (t2a, _) -> (unify t1 t2a)
  | _ -> false)
  
(* Here, we are checking for exact equality (do they occupy the same memory location) *)
and is_equal (t1:tipe) (t2:tipe) : bool = 
  if t1 == t2 then true else (match t1, t2 with
  | Guess_t g, _ -> (
    match !g with
    | Some t1' -> is_equal t1' t2
    | None -> (
      match t2 with
      | Guess_t g2 -> 
        (match !g2 with
        | Some t2' -> is_equal t1 t2'
        | None -> false)
      | _ -> false))
  | _, Guess_t _ -> is_equal t2 t1
  | _ -> false)

and occurs (g:tipe option ref) (t:tipe) : bool = 
  match t with
  | Guess_t g2 -> 
    (if g == g2 then true else match !g2 with
    | Some g2' -> occurs g g2'
    | None -> false)
  | List_t t2 -> occurs g t2
  | Fn_t (t2, t3) -> 
    (occurs g t2) || (occurs g t3)
  | Pair_t (t2, t3) -> 
    (occurs g t2) || (occurs g t3)
  | _ -> false

and instantiate (ts:tipe_scheme) : tipe = 
  match ts with
  | Forall (vars, t) -> 
    let b = List.fold_left (fun vm a -> (insert_var vm a (guess()))) (empty_varmap()) vars in
    substitute b t

and substitute (env:(tvar * tipe) list) (t:tipe) : tipe = 
  match t with
  | Tvar_t tvar -> lookup_var (=) env tvar
  | Int_t -> Int_t
  | Bool_t -> Bool_t
  | Unit_t -> Unit_t
  | Fn_t (v, e) -> Fn_t (substitute env v, substitute env e)
  | Pair_t (e1, e2) -> Pair_t (substitute env e1, substitute env e2)
  | List_t e -> List_t (substitute env e)
  | Guess_t g -> 
    (match !g with
    | None -> t
    | Some e -> substitute env e)
  
and generalize (env:(tvar * tipe_scheme) list) (t:tipe) : tipe_scheme = 
  let current_ftvs = unique_physical (guesses_from_tipe t) in 
  let env_ftvs = unique_physical (List.flatten (List.map (fun (x, Forall(_, t2)) -> guesses_from_tipe t2) env)) in
  let diff = List.filter (fun x -> not (List.mem x env_ftvs)) current_ftvs in
  let new_gs = List.map (fun g -> (g, freshtvar())) diff in
  let tc = sub_guess new_gs t in
  Forall (List.map snd new_gs, tc)

and sub_guess (new_gs:(tipe * tvar) list) (t:tipe) : tipe = 
  match t with
  | Tvar_t tvar -> Tvar_t tvar
  | Int_t -> Int_t
  | Bool_t -> Bool_t
  | Unit_t -> Unit_t
  | Fn_t (v, e) -> Fn_t (sub_guess new_gs v, sub_guess new_gs e)
  | Pair_t (e1, e2) -> Pair_t (sub_guess new_gs e1, sub_guess new_gs e2)
  | List_t e -> List_t (sub_guess new_gs e)
  | Guess_t g -> 
    (match !g with
    | None -> 
      (try 
        Tvar_t (lookup_var (==) new_gs t)
      with
        | NOT_FOUND _ -> t)
    | Some e -> sub_guess new_gs e)

and guesses_from_tipe (t:tipe) : tipe list = 
  match t with
  | Tvar_t _ | Int_t | Bool_t | Unit_t -> []
  | Fn_t (t1, t2) -> (guesses_from_tipe t1) @ (guesses_from_tipe t2)
  | Pair_t (t1, t2) -> (guesses_from_tipe t1) @ (guesses_from_tipe t2)
  | List_t t -> guesses_from_tipe t
  | Guess_t g -> 
      match !g with
      | Some t -> guesses_from_tipe t
      | None -> [t]
