type closure = { entry : Id.l; actual_fv : Id.t list }
type t =
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

val fv : t -> S.t
val f : KNormal.t -> prog

val print_t : t -> unit
val print_prog : prog -> unit
