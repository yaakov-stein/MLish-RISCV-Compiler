open Cfg_ast
open Cfg
open Riscv
open Spill

exception Implement_Me
exception FatalError

(************************************)

(** This is the hook for your compiler. Please keep your
    implementation contained to this file, plus, optionally the file
    cfg.ml *)

(***********************************)

(**
   Here is a template for one strategy to get a basic implementation
   working, which would just require implementing reg_alloc to map
   temporaries to registers.

   For each function, it calls Cfg_ast.fn2blocks to convert it into a
   Cfg representation of basic blocks, then calls a register allocator
   to map temporaries to registers, and finally uses Cfg_compile to
   convert the Cfg blocks to RISC-V.

   But you don't have to use this approach!
*)


(* 
 * How do we do Register Allocation?
 * 1) We'll get our interference graph 
 * 2) We need to create the Register Allocation Stack
 * 3) Unroll the stack and assign colors
 *)

type decision = Var of var | Reg of Riscv.reg

let available_regs : Riscv.reg list = [
    R18; R19; R20; R21; R22; R23; R24; R25; R26; R27;
]

let rec lookup_node (node: 'a) (l:('a * 'b) list) : 'b option = 
    match l with
    | [] -> None
    | (n,i)::xs -> if n = node then Some i else lookup_node node xs

let rec create_reg_alloc_stack (igraph:interfere_graph) : igraph_node list =
    let nodes : NodeSet.t = IUGraph.nodes igraph in
    if NodeSet.is_empty nodes then []
    else 
        let smallest_node = get_min_degree_node (NodeSet.elements nodes) igraph in
        let updated_graph = IUGraph.rmNode smallest_node igraph in
        smallest_node::(create_reg_alloc_stack updated_graph)

and get_min_degree_node (nodes:igraph_node list) (igraph:interfere_graph) : igraph_node = 
    let rec helper (n:igraph_node list) (m:int) (smallest_node:igraph_node) =
        match n with
        | [] -> smallest_node
        | x::xs -> 
            let cur_degree = IUGraph.degree x igraph in
            let cur_min = min cur_degree m in
            if cur_min = cur_degree then 
                helper xs cur_min x
            else 
                helper xs m smallest_node
    in
    helper nodes max_int (List.hd nodes)

let rec color_vars (stack:igraph_node list) (igraph:interfere_graph) : (igraph_node * int) list = 
    let rec helper (s:igraph_node list) (coloring:(igraph_node * int) list) = 
        match s with
        | [] -> coloring
        | x::xs -> 
            let connected_colors = get_adjacent_colors (IUGraph.adj x igraph) coloring in
            helper xs ((x, choose_color connected_colors)::coloring)
        in
    helper stack []

and get_adjacent_colors (adj:NodeSet.t) (coloring:(igraph_node * int) list) : int list =
    NodeSet.fold (fun n acc -> 
        match lookup_node n coloring with
        | None -> acc
        | Some i -> i::acc
    ) adj []

and choose_color (colors:int list) : int = 
    let rec helper (guess:int) = 
        if List.mem guess colors then helper (guess + 1)
        else guess 
    in
    helper 1

let rec assign_registers (colored_vars:(igraph_node * int) list) (available_regs:Riscv.reg list) : ((igraph_node * Riscv.reg) list * var list) = 
    let rec helper (remaining_colors:(igraph_node * int) list) (remaining_regs:Riscv.reg list) (assignments:(int * decision) list) = 
        match remaining_colors with
        | [] -> assignments
        | (n, i)::xs -> (
            match lookup_node i assignments with
            | None -> (
                match remaining_regs with
                | [] -> (
                    match n with
                    | VarNode v -> helper xs [] ((i,Var v)::assignments)
                    | _ -> raise FatalError)
                | y::ys -> helper xs ys ((i,Reg y)::assignments))
            | Some r -> helper xs remaining_regs assignments
        )
    in 
    let (updated_regs, assignments) = ensure_register_consistency colored_vars available_regs in
    let mapping = helper colored_vars updated_regs assignments in
    let (reg_map, var_list) = List.fold_right(
        fun (i, d) (regs, vars) ->
            match d with
            | Reg r -> ((i, r)::regs, vars)
            | Var v -> (regs, v::vars)) mapping ([], [])
        in
    (List.fold_left (fun acc (n,i) -> 
        match lookup_node i reg_map with
        | None -> acc
        | Some r -> (n,r)::acc
    ) [] colored_vars, var_list)

and ensure_register_consistency (colored_vars:(igraph_node * int) list) (available_regs:Riscv.reg list) : (Riscv.reg list * (int * decision) list) = 
    match colored_vars with
    | [] -> (available_regs, [])
    | (n,i)::xs -> (
        match n with
        | VarNode v -> ensure_register_consistency xs available_regs
        | RegNode r -> 
            let updated_regs = List.filter (fun x -> x <> r) available_regs in
            let (final_regs, assignments) = ensure_register_consistency xs updated_regs in
            (final_regs, (i,Reg r)::assignments)
    )

let rec swap (blocks:Cfg_ast.block list) (temp_to_reg_map:(igraph_node * Riscv.reg) list) : Cfg_ast.func = 
    match blocks with
    | [] -> []
    | x::xs -> (swap_block x temp_to_reg_map)::(swap xs temp_to_reg_map)

and swap_block (insts:Cfg_ast.inst list) (temp_to_reg_map:(igraph_node * Riscv.reg) list) : Cfg_ast.block = 
    match insts with
    | [] -> []
    | i::is -> (swap_inst i temp_to_reg_map)::(swap_block is temp_to_reg_map)

and swap_inst (inst:Cfg_ast.inst) (temp_to_reg_map:(igraph_node * Riscv.reg) list) : Cfg_ast.inst = 
    match inst with
    | Label l -> Label l
    | Jump l -> Jump l
    | Return -> Return
    | Move(o1, o2) -> Move(update_op o1 temp_to_reg_map, update_op o2 temp_to_reg_map)
    | Arith(o1,o2,a,o3) -> Arith(update_op o1 temp_to_reg_map, update_op o2 temp_to_reg_map, a, update_op o3 temp_to_reg_map)
    | Load(o1,o2,i) -> Load(update_op o1 temp_to_reg_map, update_op o2 temp_to_reg_map, i)
    | Store(o1,i,o2) -> Store(update_op o1 temp_to_reg_map, i, update_op o2 temp_to_reg_map)
    | Call(o,i) -> Call(update_op o temp_to_reg_map, i)
    | If(o1,comp,o2,l1,l2) -> If(update_op o1 temp_to_reg_map, comp, update_op o2 temp_to_reg_map, l1, l2)

and update_op (op:Cfg_ast.operand) (temp_to_reg_map:(igraph_node * Riscv.reg) list) : Cfg_ast.operand = 
    match op with
    | Int i -> Int i
    | Lab l -> Lab l
    | Reg r -> Reg r
    | Var v -> 
        let reg = (lookup_node (VarNode v) temp_to_reg_map) in
        match reg with
        | None -> Var v
        | Some r -> Reg r

let rec optimize (blocks:Cfg_ast.block list) : (Cfg_ast.block list) = 
    match blocks with
    | [] -> []
    | b::bs ->
        let (first_pass, initial_map) = optimize_block b [] in
        let (second_pass, _) = optimize_block (List.rev first_pass) initial_map in
        (List.rev second_pass)::(optimize bs)

and optimize_block (insts:Cfg_ast.inst list) (map:(var * Riscv.reg) list) : (Cfg_ast.inst list * (var * Riscv.reg) list) = 
    match insts with
    | [] -> [], map
    | i::is ->
        let (new_inst, new_map) = optimize_inst i map in
        let (remainder, final_map) = optimize_block is new_map in
        new_inst @ remainder, final_map

and optimize_inst (inst:Cfg_ast.inst) (map:(var * Riscv.reg) list) : (Cfg_ast.inst list * (var * Riscv.reg) list) = 
    match inst with
    | Label l -> [Label l], map
    | Jump l -> [Jump l], map
    | Return -> [Return], map
    | Move(o1, o2) -> 
        if o1 = o2 then
            [], map
        else
            (match (o1, o2) with
            | Reg r1, Reg r2 -> [Move(o1,o2)], map
            | Reg r, Var v | Var v, Reg r -> [], (v, r)::map
            | _ -> [Move(o1,o2)], map)
    | Arith(o1,o2,a,o3) -> [Arith(o1,o2,a,o3)], map
    | Load(o1,o2,i) -> (
        match o1 with
        | Reg r -> [Load(o1,o2,i)], map
        | Var v -> (
            match lookup_node v map with
            | None -> [Load(o1,o2,i)], map
            | Some r -> [Load(Reg r,o2,i)], map
        )
        | _ -> [Load(o1,o2,i)], map
    )
    | Store(o1,i,o2) -> (
        match o2 with
        | Reg r -> [Store(o1,i,o2)], map
        | Var v -> (
            match lookup_node v map with
            | None -> [Store(o1,i,o2)], map
            | Some r -> [Store(o1,i,Reg r)], map
        )
        | _ -> [Store(o1,i,o2)], map
    )
    | Call(o,i) -> [Call(o,i)], map
    | If(o1,comp,o2,l1,l2) -> [If(o1,comp,o2,l1,l2)], map

let rec reg_alloc (blocks:Cfg_ast.func) : Cfg_ast.func =
    let igraph : interfere_graph = build_interfere_graph blocks in
    let reg_alloc_stack : igraph_node list = create_reg_alloc_stack igraph in
    let colored_vars : (igraph_node * int) list = color_vars reg_alloc_stack igraph in
    let (assigned_regs, spills) : ((igraph_node * Riscv.reg) list * var list) = assign_registers colored_vars available_regs in
    let spilled_blocks = spill blocks spills in
    let updated_blocks : Cfg_ast.func = swap spilled_blocks assigned_regs in
    optimize updated_blocks

let process_fn (fn:Cish_ast.func) : Cfg_ast.func =
    let curfblocks = (Cfg_ast.fn2blocks fn) in
    reg_alloc curfblocks

let compile (prog:Cish_ast.func list) : Riscv.inst list =
    let blocks : Cfg_ast.func = List.flatten (List.map (fun fn -> process_fn fn) prog) in
    Cfg_compile.cfg_to_riscv blocks
