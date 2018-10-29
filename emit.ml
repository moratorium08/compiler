open Asm

let stackset = ref S.empty (* すでにSaveされた変数の集合 (caml2html: emit_stackset) *)
let stackmap = ref [] (* Saveされた変数の、スタックにおける位置 (caml2html: emit_stackmap) *)
let save x =
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    stackmap := !stackmap @ [x]
let savef x =
  stackset := S.add x !stackset;
  if not (List.mem x !stackmap) then
    stackmap := !stackmap @ [x]
let locate x =
  let rec loc = function
    | [] -> []
    | y :: zs when x = y -> 0 :: List.map succ (loc zs)
    | y :: zs -> List.map succ (loc zs) in
  loc !stackmap
let offset x = 4 * List.hd (locate x)
let stacksize () = (List.length !stackmap + 1) * 4

let reg r =
  if is_reg r
  then String.sub r 1 (String.length r - 1)
  else r

(* 関数呼び出しのために引数を並べ替える(register shuffling) (caml2html: emit_shuffle) *)
let rec shuffle sw xys =
  (* remove identical moves *)
  let _, xys = List.partition (fun (x, y) -> x = y) xys in
  (* find acyclic moves *)
  match List.partition (fun (_, y) -> List.mem_assoc y xys) xys with
  | [], [] -> []
  | (x, y) :: xys, [] -> (* no acyclic moves; resolve a cyclic move *)
      (y, sw) :: (x, y) :: shuffle sw (List.map
                                         (function
                                           | (y', z) when y = y' -> (sw, z)
                                           | yz -> yz)
                                         xys)
  | xys, acyc -> acyc @ shuffle sw xys

let rec zip lst1 lst2 = match lst1,lst2 with
  | [],_ -> []
  | _, []-> []
  | (x::xs),(y::ys) -> (x,y) :: (zip xs ys);;

let rec range n m =
  if n = m
    then [n]
    else if n < m then n::(range (n+1) m)
                  else []

type dest = Tail | NonTail of Id.t (* 末尾かどうかを表すデータ型 (caml2html: emit_dest) *)
let rec g buf el = function (* 命令列のアセンブリ生成 (caml2html: emit_g) *)
  | dest, Ans(exp) -> g' buf el (dest, exp)
  | dest, Let((x, t), exp, e) ->
      g' buf el (NonTail(x), exp);
      g buf el (dest, e)
and g' buf el = function (* 各命令のアセンブリ生成 (caml2html: emit_gprime) *)
  (* 末尾でなかったら計算結果をdestにセット (caml2html: emit_nontail) *)
  | NonTail(_), Nop -> Printf.bprintf buf "\tnop\n"
  | NonTail(x), Li(i) -> Printf.bprintf buf "\tli\t%s, %d\n" (reg x) i
  | NonTail(x), FLi(Id.L(l)) ->
      Printf.bprintf buf "\tli\t%s, %s\n" (reg reg_tmp) l;
      Printf.bprintf buf "\tflw\t%s, 0(%s)\n" (reg x) (reg reg_tmp)
  | NonTail(x), SetL(Id.L(y)) ->
      Printf.bprintf buf "\tli\t%s, %s\n" (reg x) y;
  | NonTail(x), Mv(y) when x = y -> ()
  | NonTail(x), Mv(y) -> Printf.bprintf buf "\tmv\t%s, %s\n" (reg x) (reg y)
  | NonTail(x), Neg(y) -> Printf.bprintf buf "\tsub\t%s, zero, %s\n" (reg x) (reg y)
  | NonTail(x), Add(y, V(z)) -> Printf.bprintf buf "\tadd\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | NonTail(x), Add(y, C(z)) -> Printf.bprintf buf "\tadd\t%s, %s, %d\n" (reg x) (reg y) z
  | NonTail(x), Sub(y, V(z)) -> Printf.bprintf buf "\tsub\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | NonTail(x), Sub(y, C(z)) -> Printf.bprintf buf "\tsub\t%s, %s, %d\n" (reg x) (reg y) z
  | NonTail(x), Mul(y, C(z)) ->
      let a = int_of_float (Pervasives.log (Pervasives.float_of_int z) /. Pervasives.log 2.0) in
    Printf.bprintf buf "\tslli\t%s, %s, %d\n" (reg x) (reg y) a
  | NonTail(x), Div(y, C(z)) ->
      let a = int_of_float (Pervasives.log (Pervasives.float_of_int z) /. Pervasives.log 2.0) in
    Printf.bprintf buf "\tsrli\t%s, %s, %d\n" (reg x) (reg y) a
  | NonTail(x), Sll(y, V(z)) -> Printf.bprintf buf "\tsll\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | NonTail(x), Sll(y, C(z)) -> Printf.bprintf buf "\tslli\t%s, %s, %d\n" (reg x) (reg y) z
  | NonTail(x), Lw(y, V(z)) -> Printf.bprintf buf "\tadd\t%s, %s, %s\n\tlw\t%s, 0(%s)\n" (reg reg_tmp) (reg y) (reg z) (reg x) (reg reg_tmp)
  | NonTail(x), Lw(y, C(z)) -> Printf.bprintf buf "\tlw\t%s, %d(%s)\n" (reg x) z (reg y)
  | NonTail(_), Sw(x, y, V(z)) -> Printf.bprintf buf "\tadd\t%s, %s, %s\n\tsw\t%s, 0(%s)\n" (reg reg_tmp) (reg y) (reg z) (reg x) (reg reg_tmp)
  | NonTail(_), Sw(x, y, C(z)) -> Printf.bprintf buf "\tsw\t%s, %d(%s)\n" (reg x) z (reg y)
  | NonTail(x), FMv(y) when x = y -> ()
  | NonTail(x), FMv(y) -> Printf.bprintf buf "\tfmv.s\t%s, %s\n" (reg x) (reg y)
  | NonTail(x), FNeg(y) -> Printf.bprintf buf "\tfneg.s\t%s, %s\n" (reg x) (reg y)
  | NonTail(x), FAdd(y, z) -> Printf.bprintf buf "\tfadd.s\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | NonTail(x), FSub(y, z) -> Printf.bprintf buf "\tfsub.s\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | NonTail(x), FMul(y, z) -> Printf.bprintf buf "\tfmul.s\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | NonTail(x), FDiv(y, z) -> Printf.bprintf buf "\tfdiv.s\t%s, %s, %s\n" (reg x) (reg y) (reg z)
  | NonTail(x), FSqrt(y) -> Printf.bprintf buf "\tfsqrt.s\t%s, %s\n" (reg x) (reg y)
  | NonTail(x), Lfd(y, V(z)) -> Printf.bprintf buf "\tadd\t%s, %s, %s\n\tflw\t%s, 0(%s)\n" (reg reg_tmp) (reg y) (reg z) (reg x) (reg reg_tmp)
  | NonTail(x), Lfd(y, C(z)) -> Printf.bprintf buf "\tflw\t%s, %d(%s)\n" (reg x) z (reg y)
  | NonTail(_), Stfd(x, y, V(z)) -> Printf.bprintf buf "\tadd\t%s, %s, %s\n\tfsw\t%s, 0(%s)\n" (reg reg_tmp) (reg y) (reg z) (reg x) (reg reg_tmp)
  | NonTail(_), Stfd(x, y, C(z)) -> Printf.bprintf buf "\tfsw\t%s, %d(%s)\n" (reg x) z (reg y)
  | NonTail(_), Comment(s) -> Printf.bprintf buf "#\t%s\n" s
  (* 退避の仮想命令の実装 (caml2html: emit_save) *)
  | NonTail(_), Save(x, y) when List.mem x allregs && not (S.mem y !stackset) ->
      save y;
      Printf.bprintf buf "\tsw\t%s, %d(%s)\n" (reg x) (offset y) (reg reg_sp)
  | NonTail(_), Save(x, y) when List.mem x allfregs && not (S.mem y !stackset) ->
      savef y;
      Printf.bprintf buf "\tfsw\t%s, %d(%s)\n" (reg x) (offset y) (reg reg_sp)
  | NonTail(_), Save(x, y) -> assert (S.mem y !stackset); ()
  (* 復帰の仮想命令の実装 (caml2html: emit_restore) *)
  | NonTail(x), Restore(y) when List.mem x allregs ->
      Printf.bprintf buf "\tlw\t%s, %d(%s)\n" (reg x) (offset y) (reg reg_sp)
  | NonTail(x), Restore(y) ->
      assert (List.mem x allfregs);
      Printf.bprintf buf "\tflw\t%s, %d(%s)\n" (reg x) (offset y) (reg reg_sp)
  (* 末尾だったら計算結果を第一レジスタにセットしてリターン (caml2html: emit_tailret) *)
  | Tail, (Nop | Sw _ | Stfd _ | Comment _ | Save _ as exp) ->
      g' buf el (NonTail(Id.gentmp Type.Unit), exp);
      Printf.bprintf buf "\tj\t%s\n" el
  | Tail, (Li _ | SetL _ | Mv _ | Neg _ | Add _ | Sub _ | Mul _ | Div _ | Sll _ | Lw _ as exp) ->
      g' buf el (NonTail(regs.(0)), exp);
      Printf.bprintf buf "\tj\t%s\n" el
  | Tail, (FLi _ | FMv _ | FNeg _ | FAdd _ | FSub _ | FMul _ | FDiv _ | FSqrt _ | Lfd _ as exp) ->
      g' buf el (NonTail(fregs.(0)), exp);
      Printf.bprintf buf "\tj\t%s\n" el
  | Tail, (Restore(x) as exp) ->
      (match locate x with
      | [i] -> g' buf el (NonTail(regs.(0)), exp)
      | [i; j] when i + 1 = j -> g' buf el (NonTail(fregs.(0)), exp)
      | _ -> assert false);
      Printf.bprintf buf "\tj\t%s\n" el;
  | Tail, IfEq(x, V(y), e1, e2) ->
      g'_tail_if buf el e1 e2 "beq" "bne" (reg x) (reg y)
  | Tail, IfEq(x, C(y), e1, e2) ->
      Printf.bprintf buf "\tli\t%s, %d\n" (reg reg_tmp) y;
      g'_tail_if buf el e1 e2 "beq" "bne" (reg x) (reg reg_tmp)
  | Tail, IfLE(x, V(y), e1, e2) ->
      g'_tail_if buf el e1 e2 "ble" "bgt" (reg x) (reg y)
  | Tail, IfLE(x, C(y), e1, e2) ->
      Printf.bprintf buf "\tli\t%s, %d\n" (reg reg_tmp) y;
      g'_tail_if buf el e1 e2 "ble" "bgt" (reg x) (reg reg_tmp)
  | Tail, IfGE(x, V(y), e1, e2) ->
      g'_tail_if buf el e1 e2 "bge" "blt" (reg x) (reg y)
  | Tail, IfGE(x, C(y), e1, e2) ->
      Printf.bprintf buf "\tli\t%s, %d\n" (reg reg_tmp) y;
      g'_tail_if buf el e1 e2 "bge" "blt" (reg x) (reg reg_tmp)
  | Tail, IfFEq(x, y, e1, e2) ->
      g'_tail_if buf el e1 e2 "fne" "feq.s" (reg x) (reg y)
  | Tail, IfFLE(x, y, e1, e2) ->
      g'_tail_if buf el e1 e2 "fgt" "fle.s" (reg x) (reg y)
  | NonTail(z), IfEq(x, V(y), e1, e2) ->
      g'_non_tail_if buf el (NonTail(z)) e1 e2 "beq" "bne" (reg x) (reg y)
  | NonTail(z), IfEq(x, C(y), e1, e2) ->
      Printf.bprintf buf "\tli\t%s, %d\n" (reg reg_tmp) y;
      g'_non_tail_if buf el (NonTail(z)) e1 e2 "beq" "bne" (reg x) (reg reg_tmp)
  | NonTail(z), IfLE(x, V(y), e1, e2) ->
      g'_non_tail_if buf el (NonTail(z)) e1 e2 "ble" "bgt" (reg x) (reg y)
  | NonTail(z), IfLE(x, C(y), e1, e2) ->
      Printf.bprintf buf "\tli\t%s, %d\n" (reg reg_tmp) y;
      g'_non_tail_if buf el (NonTail(z)) e1 e2 "ble" "bgt" (reg x) (reg reg_tmp)
  | NonTail(z), IfGE(x, V(y), e1, e2) ->
      g'_non_tail_if buf el (NonTail(z)) e1 e2 "bge" "blt" (reg x) (reg y)
  | NonTail(z), IfGE(x, C(y), e1, e2) ->
      Printf.bprintf buf "\tli\t%s, %d\n" (reg reg_tmp) y;
      g'_non_tail_if buf el (NonTail(z)) e1 e2 "bge" "blt" (reg x) (reg reg_tmp)
  | NonTail(z), IfFEq(x, y, e1, e2) ->
      g'_non_tail_if buf el (NonTail(z)) e1 e2 "fne" "feq.s" (reg x) (reg y)
  | NonTail(z), IfFLE(x, y, e1, e2) ->
      g'_non_tail_if buf el (NonTail(z)) e1 e2 "fgt" "fle.s" (reg x) (reg y)
  (* 関数呼び出しの仮想命令の実装 (caml2html: emit_call) *)
  | Tail, CallCls(x, ys, zs) -> (* 末尾呼び出し (caml2html: emit_tailcall) *)
      g'_args buf [(x, reg_cl)] ys zs;
      Printf.bprintf buf "\tlw\t%s, 0(%s)\n" (reg reg_tmp) (reg reg_cl);
      Printf.bprintf buf "\tjrl\t%s\n" (reg reg_tmp);
      Printf.bprintf buf "\tj\t%s\n" el;
  | Tail, CallDir(Id.L(x), ys, zs) -> (* 末尾呼び出し *)
      g'_args buf [] ys zs;
      Printf.bprintf buf "\tcall\t%s\n" x;
      Printf.bprintf buf "\tj\t%s\n" el;
  | NonTail(a), CallCls(x, ys, zs) ->
      g'_args buf [(x, reg_cl)] ys zs;
      Printf.bprintf buf "\tlw\t%s, 0(%s)\n" (reg reg_tmp) (reg reg_cl);
      Printf.bprintf buf "\tjrl\t%s\n" (reg reg_tmp);
      if List.mem a allregs && a <> regs.(0) then
        Printf.bprintf buf "\tmv\t%s, %s\n" (reg a) (reg regs.(0))
      else if List.mem a allfregs && a <> fregs.(0) then
        Printf.bprintf buf "\tfmv.s\t%s, %s\n" (reg a) (reg fregs.(0));
  | (NonTail(a), CallDir(Id.L(x), ys, zs)) ->
      g'_args buf [] ys zs;
      Printf.bprintf buf "\tcall\t%s\n" x;
      if List.mem a allregs && a <> regs.(0) then
        Printf.bprintf buf "\tmv\t%s, %s\n" (reg a) (reg regs.(0))
      else if List.mem a allfregs && a <> fregs.(0) then
        Printf.bprintf buf "\tfmv.s\t%s, %s\n" (reg a) (reg fregs.(0));
and g'_tail_if oc el e1 e2 b bn rx ry =
  let b_else = if bn = "fle.s" || bn = "feq.s"
                  then Id.genid (bn ^ "_else") else Id.genid (b ^ "_else") in
  let s = if bn = "fle.s" || bn = "feq.s" then
    (Printf.sprintf "\t%s\t%s, %s, %s\n\tbeq\t%s, zero, %s\n" bn (reg reg_tmp) rx ry (reg reg_tmp) b_else)
          else Printf.sprintf "\t%s\t%s, %s, %s\n" bn rx ry b_else in
  Printf.bprintf oc "%s" s;
  let stackset_back = !stackset in
  g oc el (Tail, e1);
  Printf.bprintf oc "%s:\n" b_else;
  stackset := stackset_back;
  g oc el (Tail, e2)
and g'_non_tail_if oc el dest e1 e2 b bn rx ry =
  let b_else = if bn = "fle.s" || bn = "feq.s"
                  then Id.genid (bn ^ "_else") else Id.genid (b ^ "_else") in
  let b_cont = if bn = "fle.s" || bn = "feq.s"
                  then Id.genid (bn ^ "_cont") else Id.genid (b ^ "_cont") in
  let s = if bn = "fle.s" || bn = "feq.s" then
    (Printf.sprintf "\t%s\t%s, %s, %s\n\tbeq\t%s, zero, %s\n" bn (reg reg_tmp) rx ry (reg reg_tmp) b_else)
          else Printf.sprintf "\t%s\t%s, %s, %s\n" bn rx ry b_else in
  Printf.bprintf oc "%s" s;
  let stackset_back = !stackset in
  g oc el (dest, e1);
  let stackset1 = !stackset in
  Printf.bprintf oc "\tj\t%s\n" b_cont;
  Printf.bprintf oc "%s:\n" b_else;
  stackset := stackset_back;
  g oc el (dest, e2);
  Printf.bprintf oc "%s:\n" b_cont;
  let stackset2 = !stackset in
  stackset := S.inter stackset1 stackset2
and g'_args oc x_reg_cl ys zs =
  let (i, yrs) =
    List.fold_left
      (fun (i, yrs) y -> (i + 1, (y, regs.(i)) :: yrs))
      (0, x_reg_cl)
      ys in
  List.iter
    (fun (y, r) -> Printf.bprintf oc "\tmv\t%s, %s\n" (reg r) (reg y))
    (shuffle reg_tmp yrs);
  let (d, zfrs) =
    List.fold_left
      (fun (d, zfrs) z -> (d + 1, (z, fregs.(d)) :: zfrs))
      (0, [])
      zs in
  List.iter
    (fun (z, fr) -> Printf.bprintf oc "\tfmv.s\t%s, %s\n" (reg fr) (reg z))
    (shuffle reg_fsw zfrs)

let h oc { name = Id.L(x); args = xs; fargs = ys; body = e; ret = _ } =
  Printf.fprintf oc "%s:\n" x;
  let buffer = Buffer.create 128 in
  stackset := S.empty;
  stackmap := [];
  g buffer (x ^ "_end") (Tail, e);
  let n = stacksize () in
  Printf.fprintf oc "\tadd\tsp, sp, %d\n" (-n);
  Printf.fprintf oc "\tsw\tra, %d(sp)\n" (n-4);
  Buffer.output_buffer oc buffer;
  Printf.fprintf oc "%s_end:\n" x;
  Printf.fprintf oc "\tlw\tra, %d(sp)\n" (n-4);
  Printf.fprintf oc "\tadd\tsp, sp, %d\n" n;
  Printf.fprintf oc "\tret\n"

let f oc (Prog(data, fundefs, e)) =
  Format.eprintf "generating assembly...@.";
  if data <> [] then
    (List.iter
       (fun (Id.L(x), d) ->
         Printf.fprintf oc "%s:\t # %f\n" x d;
         Printf.fprintf oc "\t.word\t%d\n" (Int32.to_int (Int32.bits_of_float d)))
       data);
  List.iter (fun fundef -> h oc fundef) fundefs;
  stackset := S.empty;
  stackmap := [];
  let buffer = Buffer.create 128 in
  g buffer "hoge" (NonTail("x0"), e);
  let n = stacksize () in
  Printf.fprintf oc "_min_caml_start: # main entry point\n";
  if n = 4 then ()
  else Printf.fprintf oc "\tadd\tsp, sp, %d\n" (-n+4);
  Buffer.output_buffer oc buffer;
