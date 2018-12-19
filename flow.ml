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
      | [] -> Ans(Continue)
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
    Let((n, t), x, Ans(Break n))
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
    | [] -> Ans(While body)
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

let rec f e =
  let Prog(l, funs, top) = e in
  let rec loop fundefs = match fundefs with
    | [] -> []
    | fundef::xs ->
      (trans fundef) :: loop xs
  in
  let fundefs = loop funs in
  Prog(l, fundefs, top)
