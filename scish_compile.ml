(* TODO:  your job is to map ScishAst expressions to CishAst functions. 
   The file sample_input.scish shows a sample Scish expression and the
   file sample_output.cish shows the output I get from my compiler.
   You will want to do your own test cases...
 *)

 exception Unimplemented

 (* generate fresh labels *)
 let label_counter = ref 0
 let new_int() = 
   let cur = !label_counter in 
   (label_counter := (!label_counter) + 1);
   cur
 
 let new_label() = "t" ^ (string_of_int (new_int()))
 
 let create_env () : 'a list = []
 
 let add_var (x : 'a) (env : 'a list) : 'a list = x :: env
 
 let rec index_of (x : 'a) (env : 'a list) (idx : int) : int =
   match env with
   | [] -> 0  (* If the element is not found, return 0 *)
   | hd :: tl -> if hd = x then idx else index_of x tl (idx + 1)
 
 let find_var_index (x : 'a) (env : 'a list) : int = index_of x env 0
 
 let rec compile_base_exp (l:string) (env:string list) (e:Scish_ast.exp) : Cish_ast.stmt = 
   match e with
   | Int x -> (Exp(Assign(l, ((Int x), 0)), 0), 0)
   | Var v -> (Exp(Assign(l, (get_variable_location v env)), 0), 0)
   | PrimApp(p, elist) -> compile_primop l env p elist
   | Lambda(v, e) -> raise Unimplemented
   | App(e1, e2) -> raise Unimplemented
   | If(e1, e2, e3) -> compile_if env e1 e2 e3
 
 and get_variable_location (v:string) (env:string list) : Cish_ast.exp =
   let depth = find_var_index v env in
   let rec load_creator init num =
     match num with
     | 0 -> (Cish_ast.Load(init), 0)
     | x -> 
       let new_init = (Cish_ast.Load(Binop((init), Plus, (Int 4, 0)), 0), 0) in
       load_creator new_init (num - 1)
   in
     (load_creator (Cish_ast.Var "dynenv", 0) depth)
 
 and compile_primop (result:string) (env:string list) (p:Scish_ast.primop) (elist:Scish_ast.exp list) : Cish_ast.stmt = 
   match p with
   | Plus | Minus | Times | Div | Eq | Lt -> 
     let t0 = new_label() in
     let t1 = new_label() in
     (Let(t0, (Int 0, 0), (Let(t1, (Int 0, 0), 
       (Seq(
         compile_base_exp t0 env (List.nth elist 0), 
         (Seq(
           compile_base_exp t1 env (List.nth elist 1),
           (Exp(Assign(result, (Binop((Var t0, 0), convert_op p, (Var t1, 0)), 0)), 0), 0)
         ), 0)), 0)
       ), 0)), 0)
   | Fst | Snd -> 
     let t0 = new_label() in
     (Let(t0, (Int 0, 0),
       (Seq(
         compile_base_exp t0 env (List.nth elist 0), 
         (Exp(Assign(result, convert_fst_snd (p, t0)), 0), 0)
       ), 0)
     ), 0)
   | Cons -> 
     let t0 = new_label() in
     let t1 = new_label() in
     let t2 = new_label() in
     let t3 = new_label() in
     (Let(t0, (Int 0, 0), (Let(t1, (Int 0, 0), 
       (Seq(
         compile_base_exp t0 env (List.nth elist 0), 
         (Seq(
           compile_base_exp t1 env (List.nth elist 1),
           (Let(t2, (Malloc((Int 8, 0)), 0), 
             (Let(t3, (Malloc((Int 8, 0)), 0), (Seq(
               (Exp(Store((Var t2, 0), (Var t1, 0)), 0), 0),
               (Seq(
                 (Exp(Store((Var t3, 0), (Var t0, 0)), 0), 0),
                 (Seq(
                   (Exp(Store((Binop((Var t3, 0), Plus, (Int 4, 0)), 0), (Var t2, 0)), 0), 0),
                   (Exp(Assign(result, (Var t3, 0)), 0), 0)
                 ), 0)
               ), 0)
             ), 0)), 0)
           ), 0)
         ), 0)
       ), 0)
     ), 0)), 0)
 
 and convert_fst_snd = function
   | (Fst, t0) -> (Load(Var t0, 0), 0)
   | (Snd, t0) -> (Load(Load(Binop((Var t0, 0), Plus, (Int 4, 0)), 0), 0), 0)
   | _ -> raise Unimplemented
 
 and convert_op = function
   | Plus -> Cish_ast.Plus
   | Minus -> Cish_ast.Minus
   | Times -> Cish_ast.Times
   | Div -> Cish_ast.Div
   | Eq -> Cish_ast.Eq
   | Lt -> Cish_ast.Lt
   | _ -> raise Unimplemented
 
 and compile_if (env:string list) (e1:Scish_ast.exp) (e2:Scish_ast.exp) (e3:Scish_ast.exp) : Cish_ast.stmt = 
   let t0 = new_label() in
   (Let(t0, (Int 0, 0), (Seq(
       (compile_base_exp t0 env e1),
       (Seq(
         (If((Var t0, 0), (compile_base_exp t0 env e2), (compile_base_exp t0 env e3)), 0),
         (Exp(Assign("result", (Var t0, 0)), 0), 0)
       ), 0)
     ), 0)
   ), 0)
 
 and get_func_call (vars:string list) (application:Cish_ast.stmt) (application2:Cish_ast.stmt) : Cish_ast.stmt = 
   (*t0 = *result;
     t1 = *(result+4);
     result = 3;
     t2 = result;
     result = malloc(8);
     *result = t2;
     *(result+4) = t1;
     result = t0(result); *)
   let func = new_label() in
   let env = new_label() in
   let v = new_label() in
   (Let(func, (Int 0, 0),
     (Let(env, (Int 0, 0), 
       (Let(v, (Int 0, 0), 
         (Seq(
           application,
           (Seq(
             (Exp(Assign(func, (Load((Var "result", 0)), 0)), 0), 0),
             (Seq(
               (Exp(Assign(env, (Load(Binop((Var "result", 0), Plus, (Int 4, 0)), 0), 0)), 0), 0),
               (Seq(
                 application2,
                 (Seq(
                   (Exp(Assign(v, (Var "result", 0)), 0), 0),
                   (Seq(
                     (Exp(Assign("result", (Malloc(Int 8, 0), 0)), 0), 0),
                     (Seq(
                       (Exp(Store((Var "result", 0), (Var v, 0)), 0), 0),
                       (Seq(
                         (Exp(Store((Binop((Var "result", 0), Plus, (Int 4, 0)), 0), (Var env, 0)), 0), 0),
                         (Exp(Assign("result", (Call((Var func, 0), [(Var "result", 0)]), 0)), 0), 0)
                       ), 0)
                     ), 0)
                   ), 0)
                 ), 0)
               ), 0)
             ), 0)
           ), 0)
         ), 0)
       ), 0)
     ), 0)
   ), 0)
 
 and get_setup (name:string) : Cish_ast.stmt =
   (Cish_ast.Seq(
     (Exp(Assign("result", (Malloc((Int 8, 0)), 0)), 0), 0),
     (Seq(
       (Exp(Store((Var "result", 0), (Var name, 0)), 0), 0),
       (Exp(Store((Binop((Var "result", 0), Plus, (Int 4, 0)), 0), (Var "dynenv", 0)), 0), 0)
     ), 0)), 0)
 
 and compile_app (name:string) (env:string list) (e:Scish_ast.exp) : (Cish_ast.func list * Cish_ast.stmt) = 
   match e with
   | App(e1, e2) -> 
     let new_label = new_label() in
     let (funcs, application) = compile_app name env e1 in
     let (funcs2, application2) : (Cish_ast.func list * Cish_ast.stmt) = (
       match e2 with
       | Lambda(_, _) | App(_, _) -> compile_app new_label [] e2
       | _ -> ([], compile_base_exp "result" [] e2)
     ) in
     let mod_application2 = (
       match e2 with
       | Lambda(_, _) | App(_, _) -> (Cish_ast.Seq(get_setup new_label, application2), 0) 
       | _ -> application2
     ) in
     (funcs @ funcs2, get_func_call env application mod_application2)
   | Lambda(v, e) -> 
     compile_lambda name (add_var v (create_env())) e
   | _ -> ([], compile_base_exp name env e)
 
 and compile_lambda (label:string) (env:string list) (e:Scish_ast.exp) : (Cish_ast.func list * Cish_ast.stmt) =
   match e with
   | App(e1, e2) -> 
     let new_label = new_label() in
     let (funcs, application) = compile_app label env e1 in
     let (funcs2, application2) : (Cish_ast.func list * Cish_ast.stmt) = (
       match e2 with
       | Lambda(_, _) | App(_, _) -> compile_app new_label [] e2
       | _ -> ([], compile_base_exp "result" [] e2)
     ) in
     let mod_application2 = (
       match e2 with
       | Lambda(_, _) | App(_, _) -> (Cish_ast.Seq(get_setup new_label, application2), 0) 
       | _ -> application2
     ) in
     (funcs @ funcs2, get_func_call env application mod_application2)
   | Lambda(v2, e2) -> 
     let name = new_label() in
     let (funcs, application) = compile_lambda name (add_var v2 env) e2 in
     let func = Cish_ast.Fn {name = label; args = ["dynenv"]; body = 
       (Let("result", (Int 0, 0), 
         (Seq(
           (Exp(Assign("result", (Malloc((Int 8, 0)), 0)), 0), 0),
           (Seq(
             (Exp(Store((Var "result", 0), (Var name, 0)), 0), 0),
             (Seq(
               (Exp(Store((Binop((Var "result", 0), Plus, (Int 4, 0)), 0), (Var "dynenv", 0)), 0), 0),
               (Return(Var "result", 0), 0)
             ), 0)
           ), 0)
         ), 0)
       ), 0); pos = 0 } in
       (func :: funcs, application)
   | _ -> 
     let func = Cish_ast.Fn {name = label; args = ["dynenv"]; body = 
       (Let("result", (Int 0, 0), 
         (Seq(
           (compile_base_exp "result" env e), 
           (Return(Var "result", 0), 0)
         ), 0)
       ), 0); pos = 0 } in
       ([func], (Cish_ast.skip, 0))
 
 let rec compile_exp (e:Scish_ast.exp) : Cish_ast.program = 
   match e with
   | Int x -> [Fn {name = "main"; args = []; body = (Return((Int x, 0)), 0); pos = 0 }]
   | Var v -> raise Unimplemented
   | PrimApp(p, elist) -> [Fn {name = "main"; args = []; body = 
       (Let("result", (Int 0, 0), (Seq((compile_primop "result" [] p elist), (Return(Var "result", 0), 0)), 0)), 0); pos = 0 }]
   | Lambda(v, e) -> raise Unimplemented
   | App(e1, e2) -> 
     let next_func = new_label() in
     let next_func2 = new_label() in
     let (funcs, application) : (Cish_ast.func list * Cish_ast.stmt) = compile_app next_func [] e1 in
     let (funcs2, application2) : (Cish_ast.func list * Cish_ast.stmt) = (
       match e2 with
       | Lambda(_, _) | App(_, _) -> compile_app next_func2 [] e2
       | _ -> ([], compile_base_exp "result" [] e2)
     ) in
     let mod_application2 = (
       match e2 with
       | Lambda(_, _) | App(_, _) -> (Cish_ast.Seq(get_setup next_func2, application2), 0) 
       | _ -> application2
     ) in
     funcs @ funcs2 @
     [Fn {name = "main"; args = []; body = 
     (Let("dynenv", (Int 0, 0),
       (Let("result", (Int 0, 0), 
         (Seq(
           get_setup next_func,
           (Seq(
             get_func_call [] application mod_application2,
             (Return(Var "result", 0), 0)
           ), 0)
         ), 0)
       ), 0)
     ), 0); pos = 0 }]
   | If(e1, e2, e3) -> [Fn {name = "main"; args = []; body = 
       (Let("result", (Int 0, 0), (Seq(compile_if [] e1 e2 e3, (Return(Var "result", 0), 0)), 0)), 0); pos = 0 }]
 