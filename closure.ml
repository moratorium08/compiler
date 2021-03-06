type closure = { entry : Id.l; actual_fv : Id.t list }
type t = (* クロージャ変換後の式 (caml2html: closure_t) *)
  | Unit
  | Int of int
  | Float of float
  | Neg of Id.t
  | Xor of Id.t * Id.t
  | Add of Id.t * Id.t
  | Sub of Id.t * Id.t
  | Mul of Id.t * Id.t
  | Div of Id.t * Id.t
  | FNeg of Id.t
  | FAdd of Id.t * Id.t
  | FSub of Id.t * Id.t
  | FMul of Id.t * Id.t
  | FDiv of Id.t * Id.t
  | FAddF of Id.t * float (* fadd with famous value *)
  | FSubFL of Id.t * float (* fsub with famous value at left *)
  | FSubFR of Id.t * float (* fsub with famous value at right *)
  | FMulF of Id.t * float
  | FSqrt of Id.t
  | FAbs of Id.t
  | FToI of Id.t
  | IToF of Id.t
  | Fless of Id.t * Id.t
  | IfEq of Id.t * Id.t * t * t
  | IfLE of Id.t * Id.t * t * t
  | Let of (Id.t * Type.t) * t * t
  | Var of Id.t
  | MakeCls of (Id.t * Type.t) * closure * t
  | AppCls of Id.t * Id.t list
  | AppDir of Id.l * Id.t list
  | Tuple of Id.t list
  | LetTuple of (Id.t * Type.t) list * Id.t * t
  | Get of Id.t * Id.t
  | Put of Id.t * Id.t * Id.t
  | GetE of Id.t * Id.t * Type.t
  | PutE of Id.t * Id.t * Id.t * Type.t
  | ExtArray of Id.l * Type.t
  | ExtTuple of Id.l * (Type.t list)
type fundef = { name : Id.l * Type.t;
                args : (Id.t * Type.t) list;
                formal_fv : (Id.t * Type.t) list;
                body : t }
type prog = Prog of fundef list * t

let rec fv = function
  | Unit | Int(_) | Float(_) | ExtArray(_) | ExtTuple(_) -> S.empty
  | Neg(x) | FNeg(x) | FAbs(x)| FSqrt(x) | FToI(x) | IToF(x) | GetE(_, x, _)
  | FAddF(x, _) | FSubFL(x, _) | FSubFR(x, _) | FMulF(x, _) -> S.singleton x
  | Xor(x, y) | Add(x, y) | Sub(x, y) | Mul(x, y) | Div(x, y) | FAdd(x, y) |
    FSub(x, y) | FMul(x, y) | FDiv(x, y) | Get(x, y) | Fless(x, y) | PutE(_, x, y, _) -> S.of_list [x; y]
  | IfEq(x, y, e1, e2)| IfLE(x, y, e1, e2) -> S.add x (S.add y (S.union (fv e1) (fv e2)))
  | Let((x, t), e1, e2) -> S.union (fv e1) (S.remove x (fv e2))
  | Var(x) -> S.singleton x
  | MakeCls((x, t), { entry = l; actual_fv = ys }, e) -> S.remove x (S.union (S.of_list ys) (fv e))
  | AppCls(x, ys) -> S.of_list (x :: ys)
  | AppDir(_, xs) | Tuple(xs) -> S.of_list xs
  | LetTuple(xts, y, e) -> S.add y (S.diff (fv e) (S.of_list (List.map fst xts)))
  | Put(x, y, z) -> S.of_list [x; y; z]

let toplevel : fundef list ref = ref []

let rec g env known = function (* クロージャ変換ルーチン本体 (caml2html: closure_g) *)
  | KNormal.Unit -> Unit
  | KNormal.Int(i) -> Int(i)
  | KNormal.Float(d) -> Float(d)
  | KNormal.Neg(x) -> Neg(x)
  | KNormal.Xor(x, y) -> Xor(x, y)
  | KNormal.Add(x, y) -> Add(x, y)
  | KNormal.Sub(x, y) -> Sub(x, y)
  | KNormal.Mul(x, y) -> Mul(x, y)
  | KNormal.Div(x, y) -> Div(x, y)
  | KNormal.FNeg(x) -> FNeg(x)
  | KNormal.FAdd(x, y) -> FAdd(x, y)
  | KNormal.FSub(x, y) -> FSub(x, y)
  | KNormal.FMul(x, y) -> FMul(x, y)
  | KNormal.FDiv(x, y) -> FDiv(x, y)
  | KNormal.FAddF(x, y) -> FAddF(x, y)
  | KNormal.FSubFL(x, y) -> FSubFL(x, y)
  | KNormal.FSubFR(x, y) -> FSubFR(x, y)
  | KNormal.FMulF(x, y) -> FMulF(x, y)
  | KNormal.IfEq(x, y, e1, e2) -> IfEq(x, y, g env known e1, g env known e2)
  | KNormal.IfLE(x, y, e1, e2) -> IfLE(x, y, g env known e1, g env known e2)
  | KNormal.Let((x, t), e1, e2) -> Let((x, t), g env known e1, g (M.add x t env) known e2)
  | KNormal.Var(x) -> Var(x)
  | KNormal.LetRec({ KNormal.name = (x, t); KNormal.args = yts; KNormal.body = e1 }, e2) -> (* 関数定義の場合 (caml2html: closure_letrec) *)
    (* 関数定義let rec x y1 ... yn = e1 in e2の場合は、
       xに自由変数がない(closureを介さずdirectに呼び出せる)
       と仮定し、knownに追加してe1をクロージャ変換してみる *)
    let toplevel_backup = !toplevel in
    let env' = M.add x t env in
    let known' = S.add x known in
    let e1' = g (M.add_list yts env') known' e1 in
    (* 本当に自由変数がなかったか、変換結果e1'を確認する *)
    (* 注意: e1'にx自身が変数として出現する場合はclosureが必要!
       (thanks to nuevo-namasute and azounoman; test/cls-bug2.ml参照) *)
    let zs = S.diff (fv e1') (S.of_list (List.map fst yts)) in
    let known', e1' =
      if S.is_empty zs then known', e1' else
        (* 駄目だったら状態(toplevelの値)を戻して、クロージャ変換をやり直す *)
        (Format.eprintf "free variable(s) %s found in function %s@." (Id.pp_list (S.elements zs)) x;
         Format.eprintf "function %s cannot be directly applied in fact@." x;
         toplevel := toplevel_backup;
         let e1' = g (M.add_list yts env') known e1 in
         known, e1') in
    let zs = S.elements (S.diff (fv e1') (S.add x (S.of_list (List.map fst yts)))) in (* 自由変数のリスト *)
    let zts = List.map (fun z -> (z, M.find z env')) zs in (* ここで自由変数zの型を引くために引数envが必要 *)
    toplevel := { name = (Id.L(x), t); args = yts; formal_fv = zts; body = e1' } :: !toplevel; (* トップレベル関数を追加 *)
    let e2' = g env' known' e2 in
    if S.mem x (fv e2') then (* xが変数としてe2'に出現するか *)
      MakeCls((x, t), { entry = Id.L(x); actual_fv = zs }, e2') (* 出現していたら削除しない *)
    else
      (Format.eprintf "eliminating closure(s) %s@." x;
       e2') (* 出現しなければMakeClsを削除 *)
  | KNormal.App(x, ys) when S.mem x known -> (* 関数適用の場合 (caml2html: closure_app) *)
    Format.eprintf "directly applying %s@." x;
    AppDir(Id.L(x), ys)
  | KNormal.App(f, xs) -> AppCls(f, xs)
  | KNormal.Tuple(xs) -> Tuple(xs)
  | KNormal.LetTuple(xts, y, e) -> LetTuple(xts, y, g (M.add_list xts env) known e)
  | KNormal.Get(x, y) -> Get(x, y)
  | KNormal.Put(x, y, z) -> Put(x, y, z)
  | KNormal.GetE(x, y, t) -> GetE(x, y, t)
  | KNormal.PutE(x, y, z, t) -> PutE(x, y, z, t)
  | KNormal.ExtArray(x, t) -> ExtArray(Id.L(x), t)
  | KNormal.ExtTuple(x, t) -> ExtTuple(Id.L(x), t)
  | KNormal.ExtFunApp(x, ys) ->
    if x = "int_of_float" then FToI(List.hd ys)
    else if x = "float_of_int" then IToF(List.hd ys)
    else if x = "sqrt" then FSqrt(List.hd ys)
    else if x = "fneg" then FNeg(List.hd ys)
    else if x = "fabs" then FAbs(List.hd ys)
    (* List.hdの順序おかしそう *)
    else if x = "fless" then Fless(List.hd ys, List.hd(List.tl ys))
    else AppDir(Id.L("min_caml_" ^ x), ys)

let f e =
  toplevel := [];
  let e' = g M.empty S.empty e in
  Prog(List.rev !toplevel, e')


let rec print_t = function
  | Unit -> print_string "unit"
  | Int i -> (print_string "int ";
              print_int i)
  | Float x -> (print_string "float ";
                print_float x)
  | Neg s -> print_string ("neg " ^ s ^ " ")
  | Xor (s1, s2) -> print_string ("xor (" ^ s1 ^ " " ^ s2 ^ ") ");
  | Add (s1, s2) -> print_string (s1 ^ " + " ^ s2 ^ " ");
  | Sub (s1, s2) -> print_string (s1 ^ " - " ^ s2 ^ " ");
  | Mul (s1, s2) -> print_string (s1 ^ " * " ^ s2 ^ " ");
  | Div (s1, s2) -> print_string (s1 ^ " / " ^ s2 ^ " ");
  | FNeg s -> print_string ("fneg " ^ s ^ " ")
  | FAdd (s1, s2) -> print_string (s1 ^ " +. " ^ s2 ^ " ");
  | FSub (s1, s2) -> print_string (s1 ^ " -. " ^ s2 ^ " ");
  | FMul (s1, s2) -> print_string (s1 ^ " *. " ^ s2 ^ " ");
  | FDiv (s1, s2) -> print_string (s1 ^ " /. " ^ s2 ^ " ");
  | FAddF (s1, s2) -> Printf.printf ("%s +. %f") s1 s2
  | FSubFL (s1, s2) -> Printf.printf ("%s -. %f") s1 s2
  | FSubFR (s1, s2) -> Printf.printf ("%f -. %s") s2 s1
  | FMulF (s1, s2) -> Printf.printf ("%s *. %f") s1 s2
  | Fless (s1, s2) -> print_string (s1 ^ " < " ^ s2 ^ " ");
  | FSqrt s -> print_string ("fsqrt " ^ s ^ " ");
  | FAbs s -> print_string ("fabs " ^ s ^ " ");
  | FToI s -> print_string ("ftoi " ^ s ^ " ");
  | IToF s -> print_string ("itof " ^ s ^ " ");
  | IfEq (s1, s2, t1, t2) ->
    (print_string ("ifeq " ^ s1 ^  " = "  ^ s2 ^ " then ");
     print_t t1;
     print_string " else ";
     print_t t2;
     print_string " ")
  | IfLE (s1, s2, t1, t2) ->
    (print_string ("ifle " ^ s1 ^  " <= "  ^ s2 ^ " then ");
     print_t t1;
     print_string " else ";
     print_t t2;
     print_string " ")
  | Let ((s, t), t1, t2) -> (print_string ("let " ^ s ^ ": ");
                             Type.print_t t;
                             print_string " = ";
                             print_t t1;
                             print_string " in ";
                             print_t t2;
                             print_string " ")
  | Var s -> print_string ("var " ^ s ^ " ")
  | MakeCls ((s, t), { entry = Id.L(x); actual_fv = xs }, t1) ->
    (print_string ("makecls " ^ s ^ ": ");
     Type.print_t t;
     print_string (" entry = " ^ x ^ ", actual_fv = ");
     List.iter (fun x' -> print_string (x' ^ ", ")) xs;
     print_t t1;
     print_string " "
    )
  | AppCls (s1, ss) -> (print_string ("appcls (" ^ s1 ^ ", ");
                        List.iter (fun s' -> print_string (s' ^ ", ")) ss;
                        print_string ") ")
  | AppDir (L s1, ss) -> (print_string ("appdir (" ^ s1 ^ ", ");
                          List.iter (fun s' -> print_string (s' ^ ", ")) ss;
                          print_string ") ")
  | Tuple (s::ss) -> (print_string ("tuple (" ^ s);
                      List.iter (fun s' -> print_string (", " ^ s')) ss;
                      print_string ") ")
  | LetTuple (s::ss, s1, t) -> (print_string ("lettuple (" ^ (fst s) ^ ": ");
                                Type.print_t (snd s);
                                List.iter (fun (s', t') ->
                                    (print_string (", " ^ s' ^ ": ");
                                     Type.print_t t')) ss;
                                print_string (") = " ^ s1 ^ " in ");
                                print_t t;
                                print_string " ")
  | Get (s1, s2) -> print_string (s1 ^ " . (" ^ s2 ^ " ");
  | Put (s1, s2, s3) -> print_string (s1 ^ " . (" ^ s2 ^ ") <- " ^ s3 ^ " ");
  | GetE (s1, s2, _) -> print_string (s1 ^ " . (" ^ s2 ^ " ");
  | PutE (s1, s2, s3, _) -> print_string (s1 ^ " . (" ^ s2 ^ ") <- " ^ s3 ^ " ");
  | ExtArray (L l, _) -> print_string ("extarray " ^ l)
  | ExtTuple (L l, _) -> print_string ("exttuple " ^ l)

let print_fundef { name = (Id.L(x), t); args = yts; formal_fv = zts; body = e } =
  print_string ("\nname = " ^ x ^ ": ");
  Type.print_t t;
  print_string "\nargs = ";
  List.iter (fun (x', t') ->
      print_string (x' ^ ": ");
      Type.print_t t';
      print_string ", ") yts;
  print_string "\nformal_fv = ";
  List.iter (fun (x', t') ->
      print_string (x' ^ ": ");
      Type.print_t t';
      print_string ", ") zts;
  print_string "\nbody = ";
  print_t e


let print_prog (Prog (fndefs, e)) =
  List.iter (fun fndef -> print_fundef fndef; print_newline ()) fndefs;
  print_t e
