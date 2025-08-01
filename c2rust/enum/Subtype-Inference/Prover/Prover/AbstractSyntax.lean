import Mathlib.Data.Set.Basic

def enumVariants : List Nat := [1, 2, 3]

inductive MyType : Type where
| enum : MyType
| int : MyType
| arrow : MyType -> MyType -> MyType
deriving Inhabited, Repr, BEq, DecidableEq

inductive Expr : Type where
| const : Nat → Expr
| var : String → Expr
| dec : String → MyType → Expr → Expr → Expr
| binop : Expr → Expr → Expr
| lambda : String → MyType → Expr → Expr
| app : Expr → Expr → Expr
deriving Inhabited, Repr
