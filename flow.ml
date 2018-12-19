open KNormal

let num = ref 0

let gen_name () = num := (!num + 1);
    "!while!" ^ (string_of_int !num)

let rec not_tail id body = match body with
  | IfEq(x, y, t1, t2)
  | IfLE(x, y, t1, t2) ->
    let a = not_tail id t1 in
    let b = not_tail id t2 in
    a && b
  (* let はalpha 正規系を仮定しているので、not tailな場所に
   * let は存在していないはず *)
  | LetRec(f, y) ->
    let (id', _) = f.name in
    if id = id' then
      true
    else
      not_tail id y
  | App(id', args) ->
    print_string "hoge\n";
    Printf.printf "%s = %s?\n" id' id;
    not (id = id')
  | x -> true

let rec judge_loop id body = match body with
  | IfEq(x, y, t1, t2)
  | IfLE(x, y, t1, t2) ->
    let a = judge_loop id t1 in
    let b = judge_loop id t2 in
    a && b
  (* 実際はrecursively に関数のループを検知する必要がある
   * が、minrtは関数内関数が無いので、とりあえず放置する*)
  | LetRec(f, y) ->
    let (id', _) = f.name in
    if id = id' then
      true
    else
      judge_loop id y
  | Let((id', x), t1, t2) ->
    (* ここクロージャで自分自身が代入される可能性が
     * 否定できない。まぁしかしそこまで考慮すると、しんどいので
     * 関数全体は残し、whileをApp側でinline展開するような
     * 方針にすればいけるかなと
     *)
    let a = not_tail id t1 in
    if (id' = id) then
      a
    else
      let b = judge_loop id t2 in
      a && b
  | x -> true

let rec rec2while fundef body nontail = match body with
  | IfEq(x, y, t1, t2) ->
    let a = rec2while fundef t1 nontail in
    let b = rec2while fundef t2 nontail in
    IfEq(x, y, a, b)
  | IfLE(x, y, t1, t2) ->
    let a = rec2while fundef  t1 nontail in
    let b = rec2while fundef t2 nontail in
    IfLE(x, y, a, b)
  | LetRec(f, y) ->
    let (id, _) = fundef.name in
    let (id', _) = f.name in
    if id = id' then
      LetRec(f, y)
    else
      rec2while fundef y nontail
  | Let((id', x), t1, t2) ->
    let a = rec2while fundef t1 true in
    let b = rec2while fundef t2 nontail in
    Let((id', x), a, b)
  | App(id, args) ->
    let (fname, _) = fundef.name in
    if id = fname then
      (* update args *)
      Continue
    else
      App(id, args)
  | x when nontail ->
    x
  | x ->
    let (_, t) = fundef.name in
    let n = gen_name () in
    let t = Type.return_type t in
    Let((n, t), x, Break n)

let rec trans2while fundef =
  let body = rec2while fundef fundef.body false in
  (* TODO: args *)
  let w = While body in
  {body=w; name=fundef.name; args=fundef.args}

let rec trans fundef =
  let (id, _) = fundef.name in
  let body = fundef.body in
  if judge_loop id body then
    trans2while fundef
  else
    {body=body; name=fundef.name; args=fundef.args}

let rec find_fun x = match x with
  | LetRec(f, y) ->
    LetRec(trans f, y)
  | IfEq(x, y, t1, t2)
  | IfLE(x, y, t1, t2) ->
    let t1 = find_fun t1 in
    let t2 = find_fun t2 in
    IfLE(x, y, t1, t2)
  | Let (x, t1, t2) ->
    let t1 = find_fun t1 in
    let t2 = find_fun t2 in
    Let(x, t1, t2)
  | LetTuple(l, x, t) ->
    let t = find_fun t in
    LetTuple(l, x, t)
  | e -> e

let rec f e =
  find_fun e
