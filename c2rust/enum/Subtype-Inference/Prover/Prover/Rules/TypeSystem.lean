import Prover.Rules.AbstractSyntax
import Prover.Rules.Utils
set_option linter.hashCommand false

-- Subtype relation for MyType

def isSubType : MyType → MyType → Bool
  | .enum, .int => true
  | .arrow t1 t2, .arrow t3 t4 =>
      isSubType t3 t1 && isSubType t2 t4
  | t1, t2 => t1 = t2
termination_by a b => sizeOf a + sizeOf b

infix:50 " <: " => isSubType

#guard (.enum <: .int) = true
#guard (.int <: .enum) = false
#guard (.arrow .int .enum <: .arrow .int .int) = true
#guard (.arrow .int .enum <: .arrow .int (.arrow .int .int)) = false
#guard (.arrow .int .int <: .arrow .enum .int) = true

-- Type checking for expressions

def typeCheck (tenv : TypeEnv) : Expr -> Option MyType
  | .const n =>
      if enumVariants.contains n then
        .some .enum
      else
        .some .int
  | .var x =>
      match TypeEnv.lookup tenv x with
      | some t => .some t
      | none => .none
  | .dec x t e1 e2 =>
      let tenv' := (x, t) :: tenv
      let r1 := typeCheck tenv e1
      let r2 := typeCheck tenv' e2
      r1.bind fun t' =>
        if t' <: t then r2
        else .none
  | .binop e1 e2 =>
      match typeCheck tenv e1, typeCheck tenv e2 with
      | .some t1, .some t2 =>
          if t1 <: .int && t2 <: .int then .some .int
          else .none
      | _, _ => .none
  | .lambda x t e =>
      let tenv' := (x, t) :: tenv
      let r := typeCheck tenv' e
      r.bind fun retType => .some (.arrow t retType)
  | .app e1 e2 =>
      let r1 := typeCheck tenv e1
      let r2 := typeCheck tenv e2
      r1.bind fun t1 =>
        r2.bind fun t2 =>
          match t1 with
          | .arrow t11 t12 =>
              if t2 <: t11 then .some t12
              else .none
          | _ => .none

#guard (typeCheck [] (.const 42)) = .some .int
#guard (typeCheck [] (.var "x")) = .none
#guard (typeCheck [("x", .int)] (.var "x")) = .some .int
#guard (typeCheck [] (.dec "x" .int (.const 42) (.const 43))) = .some .int
#guard (typeCheck [] (.dec "x" .int (.const 42) (.var "y"))) = .none
#guard (typeCheck [] (.binop (.const 1) (.const 2))) = .some .int
#guard (typeCheck [] (.binop (.const 1) (.var "x"))) = .none
#guard (typeCheck [] (.lambda "x" .int (.const 42))) = .some (.arrow .int .int)
#guard (typeCheck [] (.app (.lambda "x" .int (.const 42)) (.const 43))) = .some .int
