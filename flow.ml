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

let rec trans_t fundef x = match x with
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
    let t1 = trans_t fundef t1 in
    let t2 = trans_t fundef t2 in
    BIfEq(x, y, t1, t2, Ans(Nop))
  | Ans(IfLE(x, y, t1, t2)) ->
    let t1 = trans_t fundef t1 in
    let t2 = trans_t fundef t2 in
    BIfLE(x, y, t1, t2, Ans(Nop))
  | Ans(IfGE(x, y, t1, t2)) ->
    let t1 = trans_t fundef t1 in
    let t2 = trans_t fundef t2 in
    BIfGE(x, y, t1, t2, Ans(Nop))
  | Ans(IfFEq(x, y, t1, t2)) ->
    let t1 = trans_t fundef t1 in
    let t2 = trans_t fundef t2 in
    BIfFEq(x, y, t1, t2, Ans(Nop))
  | Ans(IfFLE(x, y, t1, t2)) ->
    let t1 = trans_t fundef t1 in
    let t2 = trans_t fundef t2 in
    BIfFLE(x, y, t1, t2, Ans(Nop))
  | Ans(e) ->
    let x = trans_exp fundef e in
    let n = gen_name () in
    let t = fundef.ret in
    Let((n, t), x, Break n)
  | Let(name, IfEq(_) , t)
  | Let(name, IfLE(_) , t)
  | Let(name, IfGE(_) , t)
  | Let(name, IfFEq(_) , t)
  | Let(name, IfFLE(_) , t) ->
    let Let(name, e, t) = x in
    trans_if e name (trans_t fundef t) fundef
  | Let(name, e, t) ->
    Let(name, trans_exp fundef e, trans_t fundef t)
  | _ -> failwith "program error"
and trans_if e name cont fundef = match e with
  | IfEq(x, y, t1, t2) ->
    let t1 = trans_t fundef t1 in
    let t2 = trans_t fundef t2 in
    BIfEq(x, y, t1, t2, cont)
  | IfLE(x, y, t1, t2) ->
    let t1 = trans_t fundef t1 in
    let t2 = trans_t fundef t2 in
    BIfLE(x, y, t1, t2, cont)
  | IfGE(x, y, t1, t2) ->
    let t1 = trans_t fundef t1 in
    let t2 = trans_t fundef t2 in
    BIfGE(x, y, t1, t2, cont)
  | IfFEq(x, y, t1, t2) ->
    let t1 = trans_t fundef t1 in
    let t2 = trans_t fundef t2 in
    BIfFEq(x, y, t1, t2, cont)
  | IfFLE(x, y, t1, t2) ->
    let t1 = trans_t fundef t1 in
    let t2 = trans_t fundef t2 in
    BIfFLE(x, y, t1, t2, cont)
  | e -> failwith "program error (trans_if)"
and trans_exp fundef e = match e with
  | IfEq(x, y, t1, t2) ->
    let t1 = trans_t fundef t1 in
    let t2 = trans_t fundef t2 in
    IfEq(x, y, t1, t2)
  | IfLE(x, y, t1, t2) ->
    let t1 = trans_t fundef t1 in
    let t2 = trans_t fundef t2 in
    IfLE(x, y, t1, t2)
  | IfGE(x, y, t1, t2) ->
    let t1 = trans_t fundef t1 in
    let t2 = trans_t fundef t2 in
    IfGE(x, y, t1, t2)
  | IfFEq(x, y, t1, t2) ->
    let t1 = trans_t fundef t1 in
    let t2 = trans_t fundef t2 in
    IfFEq(x, y, t1, t2)
  | IfFLE(x, y, t1, t2) ->
    let t1 = trans_t fundef t1 in
    let t2 = trans_t fundef t2 in
    IfFLE(x, y, t1, t2)
  (* judgeを先にしておき、以下のCalldirでl = idとなるのは、末尾であることが
   * 保証されている *)
  (*| CallDir(l, iargs, fargs) ->*)
  | x -> x

let rec trans2while fundef =
  let body = trans_t fundef fundef.body in
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

type node = {id: int; block: t option ref; children: node list ref}

let node_num = ref 0

let new_node () =
  node_num := !node_num + 1;
  {id = !node_num; block=ref None; children=ref []}

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

(* cur: ref node of current while loop *)
let rec gen_cfg t cur_top cur_next node =
  let (block, cont) = cut t in
  node.block := Some(block);
  match cont with
  | None ->
    ()
  | Some(While(t1, t2)) ->
    let top = new_node () in
    let next = new_node () in
    node.children := [top];
    gen_cfg t1 top next top;
    gen_cfg t2 cur_top cur_next next
  | Some(Break (_)) ->
    node.children := [cur_next]
  | Some(Continue) ->
    node.children := [cur_top]
  | Some(BIfEq(_, _, t1, t2, t3))
  | Some(BIfLE(_, _, t1, t2, t3))
  | Some(BIfGE(_, _, t1, t2, t3))
  | Some(BIfFEq(_, _, t1, t2, t3))
  | Some(BIfFLE(_, _, t1, t2, t3)) ->
    let n1 = new_node () in
    let n2 = new_node () in
    let n3 = new_node () in
    n1.children := [n3];
    n2.children := [n3];
    node.children := [n1; n2];
    gen_cfg t1 cur_top cur_next n1;
    gen_cfg t2 cur_top cur_next n2;
    gen_cfg t3 cur_top cur_next n3
  | _ -> failwith "program error"

let rec print_cfg e printed =
  let block = !(e.block) in
  let printed =
  (match block with
 | Some(b) ->
   (Printf.printf "node%d[label=\"" e.id;
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

let rec f e =
  let Prog(l, funs, top) = e in
  let rec loop fundefs = match fundefs with
    | [] -> []
    | fundef::xs ->
      let x = trans fundef in
      let dummy1 = new_node () in
      let dummy2 = new_node () in
      let top = new_node () in
      let _ = gen_cfg x.body dummy1 dummy2 top in
      let _ = print_cfg top [] in
      (trans fundef) :: loop xs
  in
  let fundefs = loop funs in
  Prog(l, fundefs, top)
