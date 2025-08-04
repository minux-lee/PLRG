import Prover.Rules.AbstractSyntax
import Prover.Rules.TypeSystem
import Prover.Rules.Utils
set_option linter.hashCommand false

-- Associated Types

def AssociatedTypeEnv := List (String × MyType)
deriving Inhabited, Repr, BEq, DecidableEq

instance : ToString AssociatedTypeEnv where
  toString env :=
    "[" ++
    String.intercalate ", "
      (env.map (fun (x, t) =>
        s!"({x}, {t.ToString})"
      )) ++
    "]"

def AssociatedTypeEnv.lookup (atenv : AssociatedTypeEnv) (x : String) : Option MyType :=
  atenv.find? (fun (y, _) => x = y) |>.map (·.2)

def AssociatedTypeEnv.add
  (atenv : AssociatedTypeEnv) (x : String) (t : MyType) : Option AssociatedTypeEnv :=
    match atenv.lookup x with
    | .none => some ((x, t) :: atenv)
    | .some t' =>
      match (MyType.lowerBound t t') with
      | .some t'' => some (atenv.map (fun (y, ty) => if y = x then (y, t'') else (y, ty)))
      | .none => none

def AssociatedTypeEnv.union (env1 env2 : AssociatedTypeEnv) : Option AssociatedTypeEnv :=
  env2.foldl
    (fun accOpt (x, t) =>
      match accOpt with
      | none => none
      | some acc => AssociatedTypeEnv.add acc x t
    )
    (some env1)

infix:50 "⋃" => AssociatedTypeEnv.union

#guard ([("x", .int)] ⋃ [("y", .enum)]) = some [("y", .enum), ("x", .int)]
#guard ([("x", .int)] ⋃ [("x", .enum)]) = some [("x", .enum)]

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

infix:50 "==>" => forcedRequiredType

#guard (.enum ==> .int) = false
#guard (.int ==> .enum) = true
#guard (.arrow .int .int ==> .arrow .int .enum) = true

-- Check and Require Function

mutual
  def check : TypeEnv -> Expr -> Option (MyType × AssociatedTypeEnv) :=
    fun tenv e => match e with
    -- Check-Var
    | .var x =>
      match tenv.lookup x with
      | .none => none
      | .some t => some (t, [])
    | .const n =>
      -- CheckConstEnum
      if enumVariants.contains n then
        some (.enum, [])
      -- CheckConstNonEnum
      else
        some (.int, [])
    -- Check-Binop
    | .binop e1 e2 =>
      match check tenv e1, check tenv e2 with
      | .some (t1, atenv1), .some (t2, atenv2) =>
        if t1 <: .int && t2 <: .int then
          (atenv1 ⋃ atenv2).map (fun atenv => (.int, atenv))
        else
          none
      | _, _ => none
    -- Check-Let
    | .dec x t e1 e2 =>
      (check ((x, t) :: tenv) e2) >>= fun (_, atenv2) =>
        (atenv2.add x t) >>= fun atenv =>
          atenv.lookup x >>= fun t' =>
            require tenv e1 t' >>= fun atenv1 =>
              check ((x, t') :: tenv) e2 >>= fun (t2, atenv2') =>
                (atenv1 ⋃ atenv2').map (fun atenv' => (t2, atenv'))
    -- Check-Lambda
    | .lambda x t e =>
      check ((x, t) :: tenv) e >>= fun (_, atenv1) =>
        (atenv1.add x t) >>= fun atenv =>
          atenv.lookup x >>= fun t' =>
            check ((x, t') :: tenv) e >>= fun (t2, atenv2) =>
              (atenv ⋃ atenv2).map (fun atenv' => (.arrow t' t2, atenv'))
    -- Check-App
    | .app e1 e2 =>
      check tenv e1 >>= fun (t1, atenv1) => match t1 with
      | .arrow t11 t12 =>
          require tenv e2 t11 >>= fun atenv2 =>
            (atenv1 ⋃ atenv2) >>= fun atenv =>
              some (t12, atenv)
      | _ => none

  def require : TypeEnv -> Expr -> MyType -> Option AssociatedTypeEnv :=
    fun tenv e t =>
      if isRequiredType t then
        match e with
        -- Require-Var
        | .var x =>
            some [(x, t)]
        -- Require-ConstEnum
        | .const n =>
            if enumVariants.contains n then
              some []
            else
              none
        -- Require-Binop
        | .binop _ _ => none
        -- Require-Let
        | .dec x t' e1 e2 =>
            require ((x, t') :: tenv) e2 t >>= fun atenv2 =>
              atenv2.add x t >>= fun atenv2' =>
                atenv2'.lookup x >>= fun t'' =>
                  require tenv e1 t'' >>= fun atenv1 =>
                    require ((x, t'') :: tenv) e2 t >>= fun atenv2'' =>
                      atenv1 ⋃ atenv2''
        -- Require-Lambda
        | .lambda x t' e =>
            match t with
            | .arrow t1 t2 =>
                require ((x, t1) :: tenv) e t2 >>= fun atenv1 =>
                  atenv1.add x t' >>= fun atenv2 =>
                    atenv2.lookup x >>= fun t'' =>
                      require ((x, t'') :: tenv) e t2 >>= fun atenv3 =>
                        atenv2 ⋃ atenv3
            | _ => none
        -- Require-App
        | .app e1 e2 =>
            match check tenv e1 with
            | .some (.arrow t1 t2, _) =>
                if t2 ==> t then
                  require tenv e1 (.arrow t1 t) >>= fun atenv1 =>
                    require tenv e2 t1 >>= fun atenv2 =>
                      atenv1 ⋃ atenv2
                else
                  none
            | _ => none
      -- Require-Subsumption
      else
        check tenv e >>= fun (t', atenv) =>
          if t' <: t then
            some atenv
          else
            none
end

-- let x: ℤ = 0 in
--   let y: ε = x in
--     let z: ℤ = 0 in
--       z
#guard check [] (.dec "x" .int (.const 0) (
  .dec "y" .enum (.var "x") (
    .dec "z" .int (.const 0) (.var "z")
  ))) = some (.int, [("x", .enum)])


-- let x: ℤ = 0 in
--   let y: ε = x in
--     let z: ℤ = 0 in
--       x
#guard check [] (.dec "x" .int (.const 0) (
  .dec "y" .enum (.var "x") (
    .dec "z" .int (.const 0) (.var "x")
  ))) = some (.enum, [("x", .enum)])

--  let ctoi: ε -> ℤ = λc: ε = 255 * c in
--    let green: ε = 1 in
--      ctoi(green)
#guard check [] (
  .dec "ctoi" (.arrow .enum .int)
    (.lambda "c" .enum (.binop (.const 255) (.var "c"))) (
      .dec "green" .enum (.const 1) (.app (.var "ctoi") (.var "green"))
    )
) = some (.int, [("green", .enum), ("c", .enum)])

--  let ctoc: ε -> ℤ = λc: ε = c in
--    let green: ε = 1 in
--      let result: ε = ctoc(green) in
--        result
#guard check [] (
  .dec "ctoc" (.arrow .enum .int)
    (.lambda "c" .enum (.var "c")) (
      .dec "green" .enum (.const 1) (
        .dec "result" .enum (.app (.var "ctoc") (.var "green")) (.var "result")))
) = some (.enum, [("green", .enum), ("ctoc", .arrow .enum .enum), ("c", .enum)])
