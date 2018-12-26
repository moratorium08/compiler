open Asm

let num = ref 0

let gen_name () = num := (!num + 1);
    "!while!" ^ (string_of_int !num)

let rec judge_loop id body = match body with
  | Sbst _ -> failwith "program error"
  | Ans e -> true
  | Let(_, e, t) ->
    (match e with
      | IfEq(_, _, t1, t2)
      | IfLE(_, _, t1, t2)
      | IfGE(_, _, t1, t2)
      | IfFEq(_, _, t1, t2)
      | IfFLE(_, _, t1, t2) ->
        let a = judge_loop id t1 in
        let b = judge_loop id t2 in
        let c = judge_loop id t in
        a && b && c
      | CallDir(id', _, _) ->
        if id = id' then
          false
        else
          judge_loop id t
      | _ -> judge_loop id t)
  | _ -> failwith "program error (judge_loop)"

let rec trans_t fundef x tail nameop = match x with
  | Ans (CallDir(l, iargs, fargs)) when l = fundef.name->
    let rec loop args = match args with
      | [] -> Continue
      | (target, arg)::args ->
        Sbst((target, Type.Int), Mv(arg), loop args)
    in
    let rec loop2 fargs = match fargs with
      | [] -> loop (List.combine fundef.args iargs )
      | (target, arg)::args ->
        Sbst((target, Type.Float), Mv(arg), loop2 args)
    in
    loop2 (List.combine fundef.fargs fargs)
  | Ans(IfEq(x, y, t1, t2)) ->
    let t1 = trans_t fundef t1 tail nameop in
    let t2 = trans_t fundef t2 tail nameop in
    BIfEq(x, y, t1, t2, Ans(Nop))
  | Ans(IfLE(x, y, t1, t2)) ->
    let t1 = trans_t fundef t1 tail nameop in
    let t2 = trans_t fundef t2 tail nameop in
    BIfLE(x, y, t1, t2, Ans(Nop))
  | Ans(IfGE(x, y, t1, t2)) ->
    let t1 = trans_t fundef t1 tail nameop in
    let t2 = trans_t fundef t2 tail nameop in
    BIfGE(x, y, t1, t2, Ans(Nop))
  | Ans(IfFEq(x, y, t1, t2)) ->
    let t1 = trans_t fundef t1 tail nameop in
    let t2 = trans_t fundef t2 tail nameop in
    BIfFEq(x, y, t1, t2, Ans(Nop))
  | Ans(IfFLE(x, y, t1, t2)) ->
    let t1 = trans_t fundef t1 tail nameop in
    let t2 = trans_t fundef t2 tail nameop in
    BIfFLE(x, y, t1, t2, Ans(Nop))
  | Ans(e) when tail ->
    let x = trans_exp fundef e tail in
    let n = gen_name () in
    let t = fundef.ret in
    Let((n, t), x, Break n)
  | Ans(e) ->
    (match nameop with
    | Some(x) ->  Sbst(x, e, Ans(Nop))
    | None ->  Ans(e))
  | Let(name, IfEq(_) , t)
  | Let(name, IfLE(_) , t)
  | Let(name, IfGE(_) , t)
  | Let(name, IfFEq(_) , t)
  | Let(name, IfFLE(_) , t) ->
    let Let(name, e, t) = x in
    trans_if e name (trans_t fundef t tail nameop) fundef false
  | Let(name, e, t) ->
    Let(name, trans_exp fundef e false , trans_t fundef t tail nameop)
  | _ -> failwith "program error"
and trans_if e name cont fundef tail = match e with
  | IfEq(x, y, t1, t2) ->
    let t1 = trans_t fundef t1 tail (Some(name)) in
    let t2 = trans_t fundef t2 tail (Some(name)) in
    BIfEq(x, y, t1, t2, cont)
  | IfLE(x, y, t1, t2) ->
    let t1 = trans_t fundef t1 tail (Some(name)) in
    let t2 = trans_t fundef t2 tail (Some(name)) in
    BIfLE(x, y, t1, t2, cont)
  | IfGE(x, y, t1, t2) ->
    let t1 = trans_t fundef t1 tail (Some(name)) in
    let t2 = trans_t fundef t2 tail (Some(name)) in
    BIfGE(x, y, t1, t2, cont)
  | IfFEq(x, y, t1, t2) ->
    let t1 = trans_t fundef t1 tail (Some(name)) in
    let t2 = trans_t fundef t2 tail (Some(name)) in
    BIfFEq(x, y, t1, t2, cont)
  | IfFLE(x, y, t1, t2) ->
    let t1 = trans_t fundef t1 tail (Some(name)) in
    let t2 = trans_t fundef t2 tail (Some(name)) in
    BIfFLE(x, y, t1, t2, cont)
  | e -> failwith "program error (trans_if)"
and trans_exp fundef e tail  = match e with
  | x -> x

let rec trans2while fundef =
  let body = trans_t fundef fundef.body true None in
  let rec loop args = match args with
    | [] -> While (body, Ans(Nop))
    | arg::args ->
      Sbst((arg, Type.Int), Mv(arg), loop args)
  in
  let rec loop2 fargs = match fargs with
    | [] -> loop fundef.args
    | arg::args ->
      Sbst((arg, Type.Float), Mv(arg), loop2 args)
  in
  let w = loop2 fundef.fargs in
  {body=w; name=fundef.name; args=fundef.args; fargs=fundef.fargs; ret=fundef.ret}

let rec trans fundef =
  let id = fundef.name in
  let body = fundef.body in
  if judge_loop id body then
    trans2while fundef
  else
    fundef

type node_typ =
  | NIfEq of Id.t * id_or_imm
  | NIfLE  of Id.t * id_or_imm
  | NIfGE  of Id.t * id_or_imm
  | NIfFEq  of Id.t * Id.t
  | NIfFLE  of Id.t * Id.t
  | NWhile | NBreak | NContinue | NNone
type node = {id: int;
             block: t option ref;
             children: node list ref;
             parents: node list ref;
             avails: t list ref;
             kills: t list ref;
             defs: t list ref;
             in_set: t list ref;
             out_set: t list ref;
             typ: node_typ ref
            }

let node_num = ref 0

let new_node typ =
  node_num := !node_num + 1;
  {id = !node_num;
   block=ref None;
   children=ref [];
   parents=ref [];
   typ=ref typ;
   avails=ref [];
   kills=ref [];
   defs=ref [];
   in_set=ref [];
   out_set=ref []}

(* graph, cont *)
let rec cut e = match e with
  | Ans e ->
    (Ans e, None)
  | Let((x, y), e, t) ->
    let (t, cont) = cut t in
    (Let((x, y), e, t), cont)
  | Sbst((x, y), e, t) ->
    let (t, cont) = cut t in
    (Sbst((x, y), e, t), cont)
  | Break _
  | Continue
  | While _
  | BIfEq (_)
  | BIfLE (_)
  | BIfGE (_)
  | BIfFEq (_)
  | BIfFLE(_) ->
    (Ans(Nop), Some(e))

let to_node_typ x = match x with
  | Some(BIfEq(x, y, _, _, _))->
    NIfEq(x, y)
  | Some(BIfLE(x, y, _, _, _))->
    NIfLE(x, y)
  | Some(BIfGE(x, y, _, _, _))->
    NIfGE(x, y)
  | Some(BIfFEq(x, y, _, _, _)) ->
    NIfFEq(x, y)
  | Some(BIfFLE(x, y, _, _, _)) ->
    NIfFLE(x, y)
  | _ -> failwith "program error(to_node_typ)"

(* cur: ref node of current while loop *)
let rec gen_cfg t cur_top cur_next node nodes =
  let (block, cont) = cut t in
  node.block := Some(block);
  match cont with
  | None ->
    node.children := [cur_next];
    cur_next.parents := node :: !(cur_next.parents);
    nodes
  | Some(While(t1, t2)) ->
    let top = new_node NWhile in
    let next = new_node NNone in
    node.children := [top];
    top.parents := node :: !(top.parents);
    let nodes = gen_cfg t1 top next top (top :: next :: nodes) in
    gen_cfg t2 cur_top cur_next next nodes
  | Some(Break (_)) ->
    node.children := [cur_next];
    cur_next.parents := node :: !(cur_next.parents);
    node.typ := NBreak;
    nodes
  | Some(Continue) ->
    node.children := [cur_top];
    cur_top.parents := node :: !(cur_top.parents);
    node.typ := NContinue;
    nodes
  | Some(BIfEq(_, _, t1, t2, t3))
  | Some(BIfLE(_, _, t1, t2, t3))
  | Some(BIfGE(_, _, t1, t2, t3))
  | Some(BIfFEq(_, _, t1, t2, t3))
  | Some(BIfFLE(_, _, t1, t2, t3)) ->
    let n1 = new_node NNone in
    let n2 = new_node NNone in
    let n3 = new_node NNone in
    node.children := [n1; n2];
    n1.parents := node :: !(n1.parents);
    n2.parents := node :: !(n2.parents);
    node.typ := to_node_typ cont;
    let nodes = gen_cfg t1 cur_top n3 n1 (n1 :: n2 :: n3 :: nodes) in
    let nodes = gen_cfg t2 cur_top n3 n2 nodes in
    gen_cfg t3 cur_top cur_next n3 nodes
  | _ -> failwith "program error"

let rec print_cfg e printed =
  let block = !(e.block) in
  let printed =
  (match block with
 | Some(b) ->
   (Printf.printf "node%d[label=\"" e.id;
    (match !(e.typ) with
    | NIfEq(_) -> print_string "ifeq "
    | NIfLE(_)-> print_string "ifle "
    | NIfGE(_)-> print_string "ifge "
    | NIfFEq(_)-> print_string "iffeq "
    | NIfFLE(_)-> print_string "iffle "
    | NWhile-> print_string "while "
    | NBreak-> print_string "break "
    | NContinue-> print_string "continue "
    |_ -> ());
    print_t b;
    Printf.printf "\"];\n";
    e.id :: printed)
  | None -> printed) in
  let rec loop children printed = match children with
    | [] -> printed
    | x::xs ->
      let printed = if List.mem x.id printed then
         printed
      else
        print_cfg x printed
      in
      Printf.printf "node%d -> node%d;\n" e.id x.id;
      loop xs printed
  in
  loop !(e.children) printed

let rec edef env block = match block with
  | Let((x, _), _, t)
  | Sbst((x, _), _, t) ->
    let env = M.add x block env in
    edef env t
  | Ans(_) ->
    env
  | _ -> failwith "program error (def)"

let rec ekill e result envs = match e with
 | Let((x, _), _, t)
 | Sbst((x, _), _, t) ->
   let rec loop envs = match envs with
     | [] -> []
     | env::xs ->
       if M.mem x env then
         (M.find x env) :: (loop xs)
       else
         loop xs
   in
   let result = loop envs in
   ekill t result envs
  | Ans(_) ->
    result
  | _ -> failwith "program error (kill)"

let rec gen_def_kill nodes =
  let rec loop nodes = match nodes with
    | [] -> []
    | node::xs ->
      match !(node.block) with
      |Some(block) ->
        let env = edef M.empty block in
        node.defs := M.fold (fun k x l -> x::l) env [];
        env :: (loop xs)
      | None -> failwith "program error(gen_def_kill"
  in
  let envs = loop nodes in
  let rec loop2 nodes = match nodes with
  | [] -> ()
  | node::xs ->
    match !(node.block) with
    | Some(e) ->
      let kills = ekill e [] envs in
      node.kills := kills
    | None ->
      failwith "program error(gen_def)"
  in
  loop2 nodes

let rec gen_avail top nodes =
  gen_def_kill nodes;

  let rec gen_in_set parents set = match parents

  let rec iter_nodes nodes = match nodes with
    | [] -> ()
    | x::xs ->
      ()
  in


let rec g e =
  let Prog(l, funs, top) = e in
  let rec loop fundefs = match fundefs with
    | [] -> []
    | fundef::xs ->
      let x = trans fundef in
      let dummy1 = new_node NNone in
      let dummy2 = new_node NNone in
      let top = new_node NNone in
      let nodes = gen_cfg x.body dummy1 dummy2 top [] in
      let _ = print_cfg top [] in
      (trans fundef) :: loop xs
  in
  let fundefs = loop funs in
  Prog(l, fundefs, top)

let f e = g e
  (*let Prog(l, funs, top) = g e in
  let rec loop fundefs = match fundefs with
    | [] -> []
    | fundef::xs ->*)

