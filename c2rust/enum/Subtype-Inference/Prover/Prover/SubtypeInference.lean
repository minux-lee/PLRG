import Prover.AbstractSyntax
import Prover.TypeSystem
import Prover.Utils
set_option linter.hashCommand false

-- Associated Types

def AssociatedTypeEnv := List (String × MyType)

def AssociatedTypeEnv.lookup (atenv : AssociatedTypeEnv) (x : String) : Option MyType :=
  atenv.find? (fun (y, _) => x = y) |>.map (·.2)

-- Required Types

def isRequiredType : MyType -> Bool
  | .enum => true
  | .int => false
  | .arrow _ t2 => isRequiredType t2

#guard (isRequiredType .enum) = true
#guard (isRequiredType .int) = false
#guard (isRequiredType (.arrow .int .enum)) = true
#guard (isRequiredType (.arrow .int .int)) = false

def forcedRequiredType : MyType -> MyType -> Bool
  | t1, t2 =>
      if isRequiredType t2 then
        t2 <: t1
      else
        false

infix:50 "=>" => forcedRequiredType

#guard (.enum => .int) = false
#guard (.int => .enum) = true
#guard (.arrow .int .int => .arrow .int .enum) = true

-- Check and Require Function

mutual
  def check(tenv : TypeEnv) (e: Expr) : Option (MyType × AssociatedTypeEnv) :=
    .none

  def require(tenv : TypeEnv) : Expr -> MyType -> Option AssociatedTypeEnv
    | e, t => match isRequiredType t with
      | true =>
          match check tenv e with
          | .some (t', atenv) =>
              if t' <: t then
                .some atenv
              else
                .none
          | .none => .none
      | false => .some []
end
