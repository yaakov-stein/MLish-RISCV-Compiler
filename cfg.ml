open Cfg_ast
exception Implement_Me
exception FatalError
exception NOT_FOUND of string


type igraph_node = RegNode of Riscv.reg | VarNode of var

let string_of_node (n: igraph_node) : string =
  match n with
  | RegNode r -> "$" ^ Riscv.reg2string r
  | VarNode v -> v
;;

module IGraphNode =
  struct
    type t = igraph_node
    let compare = compare
  end

module NodeSet = Set.Make(IGraphNode)                                                   

(* These are the registers that must be generated / killed as part of
   liveness analysis for call instructions to reflect RISC-V calling
   conventions *)

(* Note that for call_gen_list, if the number of arguments n in the
   call is less than 8, then only the first n of these are actually
   used *)
let call_gen_list = ["x10";"x11";"x12";"x13";"x14";"x15";"x16";"x17";]
let call_kill_list = ["x1";"x5";"x6";"x7";"x10";"x11";"x12";"x13";"x14";"x15";"x16";"x17";"x28";"x29";"x30";"x31"]

(* Undirected graphs where nodes are identified by igraph_node type above. Look at
   graph.ml for the interface description.  *)

module IUGraph = Graph.UndirectedGraph(IGraphNode)

(* this is a wrapper to addEdge that prevents adding self edges.
   to do all sorts of other complicated stuff for eg coloring *)
let specialAddEdge u v g =
  if (u = v) then
    g
  else
    IUGraph.addEdge u v g

(* An interference graph is an SUGraph where a node is temp variable
   or a register (to be able to handle pre-colored nodes)

   The adjacency set of variable x should be the set of variables
   y such that x and y are live at the same point in time. *)
type interfere_graph = IUGraph.graph

(* To help you printing an igraph for debugging *)
let string_of_igraph (g: interfere_graph) : string =
  let rec string_of_row (n: IUGraph.node) =
    let ns = IUGraph.adj n g in
    Printf.sprintf "  %s\t: {%s}"
      (string_of_node n)
      (String.concat "," (List.map string_of_node (NodeSet.elements ns)))
  in
  let rows = String.concat "\n" (List.map string_of_row (NodeSet.elements (IUGraph.nodes g))) in
  Printf.sprintf "{\n%s\n}\n" rows


(*******************************************************************)
(* PS7 TODO:  interference graph construction *)

(* given a function (i.e., list of basic blocks), construct the
 * interference graph for that function.  This will require that
 * you build a dataflow analysis for calculating what set of variables
 * are live-in and live-out for each program point. *)
(************** HELPERS **************)
type ('k, 'v) varmap = ('k * 'v) list
let empty_varmap () : ('k, 'v) varmap = []
let rec insert_var equals_f (vm:('k, 'v) varmap) (k:'k) (v:'v) : ('k, 'v) varmap = 
 match vm with
 | [] -> [(k, v)]
 | (key, value)::rest -> 
   if equals_f k key then (k, v)::rest else (key, value)::(insert_var equals_f rest k v)

let rec lookup_var equals_f (vm:('k, 'v) varmap) (k:'k) : 'v = 
  match vm with
  | [] -> raise (NOT_FOUND ("Variable not found"))
  | ((key, value)::xs) -> if equals_f k key then value else lookup_var equals_f xs k

module OpSet = Set.Make(struct
 type t = operand
 let compare = compare
end)

type oset = OpSet.t

let oset2string (s : oset) : string =
 let elems = OpSet.elements s in
 let strings = List.map op2string elems in
 "{" ^ String.concat ", " strings ^ "}"

let analysis2string (analysis:(label * (oset * oset)) list) : string = 
 let entry2string (lbl, (live_in, live_out)) =
   lbl ^ ":\n  LiveIn: " ^ oset2string live_in ^ "\n  LiveOut: " ^ oset2string live_out
 in
 String.concat "\n" (List.map entry2string analysis)

let live_x_equal (a1 : (var * oset) list) (a2 : (var * oset) list) : bool =
 let compare_label (l1, _) (l2, _) = String.compare l1 l2 in
 let sorted1 = List.sort compare_label a1 in
 let sorted2 = List.sort compare_label a2 in
 try
   List.for_all2
     (fun (lbl1, data1) (lbl2, data2) ->
       lbl1 = lbl2 &&
       OpSet.equal data1 data2
     )
     sorted1 sorted2
 with Invalid_argument _ -> false
(************** HELPERS **************)

(**************** MAIN ****************)
let rec build_interfere_graph (f : func) : interfere_graph = 
 process_func f (IUGraph.empty) (liveness_analysis f)

(* 
* How do we build an interference graph?
* 1) We need to create a CFG from the given blocks. ie we need to find each blocks predecessors and successors
* 2) With that knowledge, we need then create a block by block liveness analysis to determine the live-in/live-out for each block
* 3) with that, we can then do a liveness analysis on a instruction level
*)

and process_func (f:func) (igraph:interfere_graph) (liveness:(label * (oset * oset)) list) : interfere_graph =
 match f with
 | [] -> igraph
 | x::xs -> 
   let (_, live_out) = lookup_var (=) liveness (get_block_label x) in
   let initial_graph = add_all_edges live_out live_out igraph in 
   let new_graph = process_block (List.rev x) live_out initial_graph in
   process_func xs new_graph liveness 

and process_block (b:block) (live_out:oset) (igraph:interfere_graph) : interfere_graph =
match b with
| [] -> igraph
| x::xs -> (
  match x with
  | Jump(_) | Return | Label(_) -> process_block xs live_out igraph
  | Move(e1, e2) | Load(e1, e2, _) -> 
    let e1_edges_graph = add_all_edges (OpSet.of_list [e1]) live_out igraph in
    let new_live_out = OpSet.remove e1 (OpSet.add e2 live_out) in
    let new_graph = add_all_edges (OpSet.of_list [e2]) new_live_out e1_edges_graph in
    process_block xs new_live_out new_graph
  | Arith(e1, e2, _, e3) -> 
    let e1_edges_graph = add_all_edges (OpSet.of_list [e1]) live_out igraph in
    let new_live_out = OpSet.remove e1 (OpSet.add e2 (OpSet.add e3 live_out)) in
    let new_graph = add_all_edges (OpSet.of_list [e2; e3]) new_live_out e1_edges_graph in
    process_block xs new_live_out new_graph
  | Store(_, _, e) -> 
    let new_live_out = OpSet.add e live_out in
    let new_graph = add_all_edges (OpSet.of_list [e]) new_live_out igraph in
    process_block xs new_live_out new_graph
  | Call(e, _) -> 
    let new_live_out = OpSet.add (Reg R1) (OpSet.add e live_out) in
    let new_graph = add_all_edges (OpSet.of_list [e; (Reg R1)]) new_live_out igraph in
    process_block xs new_live_out new_graph
  | If(e1, _, e2, _, _) -> 
    let new_live_out = OpSet.add e1 (OpSet.add e2 live_out) in
    let new_graph = add_all_edges (OpSet.of_list [e1; e2]) new_live_out igraph in
    process_block xs new_live_out new_graph
)

and add_all_edges (set_a:oset) (set_b:oset) (igraph:interfere_graph) : interfere_graph =
 let filter_func = function Int _ -> false | Lab _ -> false | _ -> true in
 let filtered_set_a = OpSet.filter filter_func set_a in
 let filtered_set_b = OpSet.filter filter_func set_b in
 OpSet.fold (fun elem acc -> 
   OpSet.fold (fun other acc2 -> 
     specialAddEdge (op_to_igraph_node elem) (op_to_igraph_node other) acc2
     ) filtered_set_b acc
   ) filtered_set_a igraph

and op_to_igraph_node (elem:operand) : igraph_node = 
 match elem with
 | Reg r -> RegNode r
 | Var v -> VarNode v
 | _ -> raise FatalError

and liveness_analysis (blocks:block list) : (label * (oset * oset)) list = 
 let block_map : (label * block) list = List.map (fun x -> get_block_label x, x) blocks in
 let gen_map : (label * oset) list = List.map (fun (l, b) -> l, gen b) block_map in
 let kill_map : (label * oset) list = List.map (fun (l, b) -> l, kill b) block_map in
 let live_in_map : (label * oset) list = List.map (fun (l, gen_of_b) -> l, gen_of_b) gen_map in
 let live_out_map : (label * oset) list = List.map (fun (l, _) -> l, OpSet.empty) block_map in
 liveness_outer_loop block_map gen_map kill_map live_in_map live_out_map

and liveness_outer_loop (blocks:(label * block) list)
                       (gen_map:(label * oset) list)
                       (kill_map:(label * oset) list)
                       (live_in_map:(label * oset) list)
                       (live_out_map:(label * oset) list)
                       : (label * (oset * oset)) list =
 let (new_live_in_map, new_live_out_map) = liveness_inner_loop blocks gen_map kill_map live_in_map live_out_map in
 if (live_x_equal new_live_in_map live_in_map) && (live_x_equal new_live_out_map live_out_map) then
   List.map (fun (l, _) -> (l, ((lookup_var (=) live_in_map l), (lookup_var (=) live_out_map l)))) blocks
 else
   liveness_outer_loop blocks gen_map kill_map new_live_in_map new_live_out_map

and liveness_inner_loop (blocks:(label * block) list)
                 (gen_map:(label * oset) list)
                 (kill_map:(label * oset) list)
                 (live_in_map:(label * oset) list)
                 (live_out_map:(label * oset) list)
                 : ((label * oset) list * (label * oset) list) =
 match blocks with
 | [] -> live_in_map, live_out_map
 | (l, b)::rest -> 
   let fresh_out = (
     match get_fresh_live_out l live_in_map b with
     | None -> lookup_var (=) kill_map l
     | Some data -> data) in
   let old_out = lookup_var (=) live_out_map l in
   if fresh_out = old_out then
     liveness_inner_loop rest gen_map kill_map live_in_map live_out_map
   else 
     let new_live_out_map = insert_var (=) live_out_map l fresh_out in
     let cur_gen = (lookup_var (=) gen_map l) in
     let cur_kill = (lookup_var (=) kill_map l) in
     let new_live_in_map = insert_var (=) live_in_map l (OpSet.union cur_gen (OpSet.diff fresh_out cur_kill)) in
     liveness_inner_loop blocks gen_map kill_map new_live_in_map new_live_out_map


and get_fresh_live_out (l:label) (live_in_map:(label * oset) list) (b:block) : oset option =
 match get_block_succ b with
 | None -> None
 | Some ls -> Some
   (List.fold_left (fun acc x -> OpSet.union acc (lookup_var (=) live_in_map x)) OpSet.empty ls)

and gen (insts:inst list) : oset = 
let rec helper rev_insts acc = 
  match rev_insts with
  | [] -> acc
  | x::xs -> 
    helper xs (
      match x with
      | Label(_) | Return | Jump(_) -> acc
      | Move(e1, e2) | Load(e1, e2, _) -> OpSet.remove e1 (OpSet.add e2 acc)
      | Arith(e1, e2, _, e3) -> OpSet.remove e1 (OpSet.add e2 (OpSet.add e3 acc))
      | Store(_, _, e)  -> OpSet.add e acc
      | Call(e, _) -> OpSet.remove (Reg R1) (OpSet.add e acc)
      | If(e1, _, e2, _, _) -> OpSet.add e2 (OpSet.add e1 acc)
    )
in OpSet.filter (function Int _ -> false | _ -> true) (helper (List.rev insts) OpSet.empty)

and kill (insts:inst list) : oset = 
  match insts with
  | [] -> OpSet.empty
  | x::xs -> 
    OpSet.union (kill xs) (
      match x with
      | Label(_) | Return | Jump(_) | Store(_, _, _) | If(_, _, _, _, _) -> OpSet.empty
      | Move(e, _) | Arith(e, _, _, _) | Load(e, _, _) -> OpSet.add e OpSet.empty
      | Call(_, _) -> OpSet.add (Reg R1) OpSet.empty
    )

and get_block_label (insts:inst list) : label = 
 match insts with
 | x::xs -> (
   match x with
   | Label(l) -> l
   | _ -> raise FatalError
 )
 | _ -> raise FatalError

and get_block_succ (insts:inst list) : label list option = 
 match insts with
 | [x] -> (
   match x with
   | Return -> None
   | If(_, _, _, l1, l2) -> Some (l1::[l2])
   | Jump(l) -> Some [l]
   | _ -> raise FatalError
 )
 | x::xs -> get_block_succ xs
 | _ -> raise FatalError

(**************** MAIN ****************)
