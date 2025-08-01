import Prover.AbstractSyntax

-- Env Utils
def TypeEnv := List (String × MyType)

def TypeEnv.lookup (tenv : TypeEnv) (x : String) : Option MyType :=
  tenv.find? (fun (y, _) => x = y) |>.map (·.2)

-- Type Utils
def Type.eq : MyType → MyType → Bool
  | .int, .int => true
  | .enum, .enum => true
  | .arrow t1 t2, .arrow t3 t4 => Type.eq t1 t3 && Type.eq t2 t4
  | _, _ => false

-- Expression Utils
