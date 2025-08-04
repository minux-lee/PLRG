import Prover.Rules.AbstractSyntax

-- Type Utils
def MyType.sameKind : MyType → MyType → Bool
  | .int, .int => true
  | .int, .enum => true
  | .enum, .int => true
  | .enum, .enum => true
  | .arrow t1 t2, .arrow t3 t4 =>
      MyType.sameKind t1 t3 && MyType.sameKind t2 t4
  | _, _ => false

infix:50 " ~ " => MyType.sameKind

mutual
  def MyType.lowerBound : MyType -> MyType -> Option MyType
    | .enum, .enum => some .enum
    | .int, .int => some .int
    | .enum, .int => some .enum
    | .int, .enum => some .enum
    | .arrow t1 t2, .arrow t3 t4 =>
        match MyType.upperBound t1 t3, MyType.lowerBound t2 t4 with
        | .some t1', .some t2' => some (.arrow t1' t2')
        | _, _ => none
    | _, _ => none

  def MyType.upperBound: MyType -> MyType -> Option MyType
    | .enum, .enum => some .enum
    | .int, .int => some .int
    | .enum, .int => some .int
    | .int, .enum => some .int
    | .arrow t1 t2, .arrow t3 t4 =>
        match MyType.lowerBound t1 t3, MyType.upperBound t2 t4 with
        | .some t1', .some t2' => some (.arrow t1' t2')
        | _, _ => none
    | _, _ => none
end

-- Env Utils
def TypeEnv := List (String × MyType)

instance : ToString TypeEnv where
  toString tenv :=
    "[" ++
    String.intercalate ", "
      (tenv.map (fun (x, t) => s!"({x}, {t.ToString})")) ++
    "]"

def TypeEnv.lookup (tenv : TypeEnv) (x : String) : Option MyType :=
  tenv.find? (fun (y, _) => x = y) |>.map (·.2)

def TypeEnv.sameKind : TypeEnv -> TypeEnv -> Bool
  | [], [] => true
  | (x1, t1) :: rest1, (x2, t2) :: rest2 =>
      x1 = x2 && t1 ~ t2 && TypeEnv.sameKind rest1 rest2
  | _, _ => false

infix:50 " ~ " => TypeEnv.sameKind

-- Expression Utils
