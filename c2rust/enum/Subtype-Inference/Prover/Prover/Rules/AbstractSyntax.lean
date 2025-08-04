import Mathlib.Data.Set.Basic

def enumVariants : List Nat := [0, 1, 2, 3]

inductive MyType : Type where
| enum : MyType
| int : MyType
| arrow : MyType -> MyType -> MyType
deriving Inhabited, Repr, BEq, DecidableEq

def MyType.ToString : MyType -> String
  | .enum => "enum"
  | .int => "int"
  | .arrow t1 t2 => s!"({MyType.ToString t1} -> {MyType.ToString t2})"

instance : ToString MyType where
  toString := MyType.ToString

inductive Expr : Type where
| const : Nat → Expr
| var : String → Expr
| dec : String → MyType → Expr → Expr → Expr
| binop : Expr → Expr → Expr
| lambda : String → MyType → Expr → Expr
| app : Expr → Expr → Expr
deriving Inhabited, Repr

def Expr.ToString : Expr -> String
  | .const n => s!"{n}"
  | .var x => s!"{x}"
  | .dec x t e1 e2 => s!"let {x} : {MyType.ToString t} = {Expr.ToString e1} in ({Expr.ToString e2})"
  | .binop e1 e2 => s!"({Expr.ToString e1} binop {Expr.ToString e2})"
  | .lambda x t e => s!"(lambda {x} : {MyType.ToString t} -> {Expr.ToString e})"
  | .app e1 e2 => s!"({Expr.ToString e1} {Expr.ToString e2})"

instance : ToString Expr where
  toString := Expr.ToString
