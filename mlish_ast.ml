type var = string   (* program variables *)
type tvar = string  (* type variables *)
type pos = int

type tipe = 
  Tvar_t of tvar
| Int_t
| Bool_t
| Unit_t
| Fn_t of tipe * tipe
| Pair_t of tipe * tipe
| List_t of tipe
| Guess_t of tipe option ref

type tipe_scheme = Forall of (tvar list) * tipe

type prim = 
  Int of int
| Bool of bool
| Unit   (* unit value -- () *)
| Plus   (* add two ints *)
| Minus  (* subtract two ints *)
| Times  (* multiply two ints *)
| Div    (* divide two ints *)
| Eq     (* compare two ints for equality *)
| Lt     (* compare two ints for inequality *)
| Pair   (* create a pair from two values *)
| Fst    (* fetch the 1st component of a pair *)
| Snd    (* fetch the 2nd component of a pair *)
| Nil    (* the empty list *)
| Cons   (* create a list from two values *)
| IsNil  (* determine whether a list is Nil *)
| Hd     (* fetch the head of a list *)
| Tl     (* fetch the tail of a list *)

type rexp = 
  Var of var
| PrimApp of prim * exp list
| Fn of var * exp
| App of exp * exp
| If of exp * exp * exp
| Let of var * exp * exp
and exp = rexp * pos

(**********************************************************)
(* Pretty printing                                        *)
(**********************************************************)

let pptvarcounter = ref 0;;
let ppfreshtvar () : string = 
  let curcount = !pptvarcounter in
  pptvarcounter := (curcount +1);
  "ptvar"^(string_of_int curcount)


let primop2string p = 
  match p with
    Plus -> "PLUS"
  | Minus -> "MINUS"
  | Times -> "TIMES"
  | Div -> "DIV"
  | Cons -> "CONS"
  | Fst -> "FST"
  | Snd -> "SND"
  | Eq -> "EQ" 
  | Lt -> "LT"
  | Unit -> "UNIT"
  | Pair -> "PAIR"
  | Hd -> "HD"
  | Tl -> "TL"
  | Nil -> "NIL"
  | IsNil -> "IsNil"
  | Int i -> string_of_int i
  | Bool b -> string_of_bool b

let rec exp2string (e:exp):string = 
  let (e, _pos) = e in
  match e with
  | PrimApp(p,es) -> 
      "PRIMAPP(" ^ (primop2string p) ^ "," ^ (exps2string es) ^")"
  | Var x -> x
  | Fn(x,e) -> "FUN("^x^","^(exp2string e)^")"
  | App(e1,e2) -> "APP(" ^ (exps2string [e1;e2]) ^ ")"
  | If(e1,e2,e3) -> "IF("^(exps2string[e1;e2;e3]) ^ ")"
  | Let (v, e1, e2) -> "LET(" ^ v ^ "," ^ exp2string e1 ^ "," ^ exp2string e2 ^ ")"

and exps2string (es:exp list):string = 
  String.concat ", " (List.map exp2string es)


module RefOrd = struct
  type t = tipe option ref
  let compare r1 r2 =
    if r1 == r2 then 0
    else if Obj.repr r1 < Obj.repr r2 then -1 else 1
end

module RefMap = Map.Make(RefOrd)

let guess_var_map : string RefMap.t ref = ref RefMap.empty

let rec tipe_scheme2string (ts:tipe_scheme):string = 
  match ts with
  | Forall (tvars, t) -> "FORALL([" ^ String.concat "; " tvars ^ "], " ^ tipe2string t ^ ")"

and tipe2string (t:tipe):string = 
  (* print_string ("Got here - tipe2string\n");
  flush stdout; *)
  match t with
    Tvar_t tvar -> "'" ^ tvar
  | Int_t -> "int"
  | Bool_t -> "bool"
  | Unit_t -> "unit"
  | Fn_t (t1, t2) -> "(" ^ tipe2string t1 ^ ") -> (" ^ tipe2string t2 ^ ")"
  | Pair_t (t1, t2) -> "(" ^ tipe2string t1 ^ ") * (" ^ tipe2string t2 ^ ")"
  | List_t t -> "(" ^ tipe2string t ^ ") list"
  | Guess_t tr ->
     match !tr with
     | None -> 
        (* (try
          (* Try to find a name for this reference in the map *)
          "(Guess(None(" ^ tipe2string (Tvar_t (RefMap.find tr !guess_var_map)) ^ ")))"
        with Not_found ->
          (* If not found, generate a new name and add it to the map *)
          let tvar = ppfreshtvar () in
          guess_var_map := RefMap.add tr tvar !guess_var_map;
          "(Guess(None(" ^ tipe2string (Tvar_t tvar)) ^ ")))" *)
        let tvar = ppfreshtvar () in
        let ty = Tvar_t tvar in
        tr := Some ty;
        tipe2string ty
     | Some t -> 
      (* "(Guess(Some(" ^ tipe2string t ^ ")))" *)
      tipe2string t
