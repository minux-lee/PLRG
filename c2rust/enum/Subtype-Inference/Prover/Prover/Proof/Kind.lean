import Prover.Rules.Basic

-- Type

lemma sameKind_refl (t : MyType) : t ~ t := by
  induction t with
  | enum => simp [MyType.sameKind]
  | int => simp [MyType.sameKind]
  | arrow a b ihA ihB =>
    simp [MyType.sameKind, ihA, ihB]

lemma sameKind_symm (t1 t2 : MyType) (h : t1 ~ t2) : t2 ~ t1 := by
  revert t2
  induction t1 with
  | enum =>
      intro t2; cases t2 <;> intro h
      · simp [MyType.sameKind]
      · simp [MyType.sameKind]
      · cases (by simp [MyType.sameKind] at h : False)
  | int =>
      intro t2; cases t2 <;> intro h
      · simp [MyType.sameKind]
      · simp [MyType.sameKind]
      · cases (by simp [MyType.sameKind] at h : False)
  | arrow a b ihA ihB =>
    intro t2; cases t2 with
    | enum => intro h; cases (by simp [MyType.sameKind] at h : False)
    | int  => intro h; cases (by simp [MyType.sameKind] at h : False)
    | arrow c d =>
      intro h
      have ⟨ha, hb⟩ :
          (a ~ c) = true ∧ (b ~ d) = true := by
        simpa [MyType.sameKind, Bool.and_eq_true] using h
      simp [MyType.sameKind, ihA, ihB, ha, hb]

theorem sameKindTypesExistBounds {t1 t2 : MyType}
    (h : (t1 ~ t2) = true) :
    ∃ (tℓ tᵤ : MyType),
      MyType.lowerBound t1 t2 = some tℓ ∧
      MyType.upperBound t1 t2 = some tᵤ := by
  revert t2
  induction t1 with
  | enum =>
      intro t2; cases t2 <;> intro h
      · exact ⟨.enum, .enum, rfl, rfl⟩
      · exact ⟨.enum, .int,  rfl, rfl⟩
      · cases (by simp [MyType.sameKind] at h : False)
  | int =>
      intro t2; cases t2 <;> intro h
      · exact ⟨.enum, .int,  rfl, rfl⟩
      · exact ⟨.int,  .int,  rfl, rfl⟩
      · cases (by simp [MyType.sameKind] at h : False)
  | arrow a b ihA ihB =>
    intro t2; cases t2 with
    | enum => intro h; cases (by simp [MyType.sameKind] at h : False)
    | int  => intro h; cases (by simp [MyType.sameKind] at h : False)
    | arrow c d =>
      intro h

      have ⟨ha, hb⟩ :
          (a ~ c) = true ∧ (b ~ d) = true := by
        simpa [MyType.sameKind, Bool.and_eq_true] using h

      obtain ⟨la, ua, hla, hua⟩ := ihA (t2 := c) ha
      obtain ⟨lb, ub, hlb, hub⟩ := ihB (t2 := d) hb

      refine ⟨.arrow ua lb, .arrow la ub, ?_, ?_⟩
      · simp [MyType.lowerBound, hua, hlb]
      · simp [MyType.upperBound, hla, hub]


-- TypeEnv

theorem sameKindTEnvAfterAddingSameKindType
    {Γ1 Γ2 : TypeEnv} {x : String} {t1 t2 : MyType}
    (hΓ : (Γ1 ~ Γ2) = true)
    (ht : (t1 ~ t2) = true) :
    ((x, t1) :: Γ1) ~ ((x, t2) :: Γ2) := by
  simp [TypeEnv.sameKind, hΓ, ht]

-- Check and Require

lemma enumIsRequiredType
    {t : MyType} :
    (t = .enum) -> isRequiredType t := by
  intro h; simp [isRequiredType, h]

lemma checkConstantIsEnumOrInt
    {Γ : TypeEnv} {n : Nat} {t : MyType} {A : AssociatedTypeEnv} :
    (check Γ (.const n) = some (t, A)) ->
    t = .enum ∨ t = .int := by
  intro h
  by_cases hn : n ∈ enumVariants
  · have h1 : t = .enum ∧ A = [] := by
      simpa [check, hn] using h.symm
    simp [h1]
  · have h1 : t = .int ∧ A = [] := by
      simpa [check, hn] using h.symm
    simp [h1]

lemma requireConstantIsEnumOrInt
    {Γ : TypeEnv} {n : Nat} {t : MyType}
    (h : require Γ (.const n) t = some []) :
    t = .enum ∨ t = .int := by
  cases t with
  | enum => simp
  | int => simp
  | arrow l r =>
      by_cases hreq : (isRequiredType (.arrow l r))
      · have h1 : require Γ (.const n) (.arrow l r) = none := by
          simp [require, hreq] at h
        simp [h1] at *
      · by_cases henum : n ∈ enumVariants
        · have h1 : require Γ (.const n) (.arrow l r) = none := by
            simp [require, isSubType, hreq, check, henum] at h
          simp [h1] at *
        · have h1 : require Γ (.const n) (.arrow l r) = none := by
            simp [require, isSubType, hreq, check, henum] at h
          simp [h1] at *

lemma enumOrIntSameKind
    {t1 t2 : MyType}
    (h : t1 = .int ∨ t1 = .enum)
    (h' : t2 = .int ∨ t2 = .enum) :
    t1 ~ t2 := by
  cases h with
  | inl h1 =>
      cases h' with
      | inl h2 => simp [MyType.sameKind, h1, h2]
      | inr h2 => simp [MyType.sameKind, h1, h2]
  | inr h1 =>
      cases h' with
      | inl h2 => simp [MyType.sameKind, h1, h2]
      | inr h2 => simp [MyType.sameKind, h1, h2]

theorem checkOrRequireSameKind
    {Γ1 Γ2 : TypeEnv} {e : Expr} {t1 t2 : MyType}
    (hΓ : (Γ1 ~ Γ2) = true) :
    (((∃A1, check Γ1 e = some (t1, A1)) ∧ (∃A2, check Γ2 e = some (t2, A2))) -> t1 ~ t2)
      ∧ (((∃A1, require Γ1 e t1 = some A1) ∧ (∃A2, require Γ2 e t2 = some A2)) -> t1 ~ t2) := by
  revert Γ1 Γ2 t1 t2
  induction e with
  | const n =>
      intro Γ1 Γ2 t1 t2 hΓ
      constructor
      · intro h
        rcases h with ⟨⟨A1, h1⟩, ⟨A2, h2⟩⟩
        have h1' : t1 = .enum ∨ t1 = .int := checkConstantIsEnumOrInt h1
        have h2' : t2 = .enum ∨ t2 = .int := checkConstantIsEnumOrInt h2
        simp [hΓ, MyType.sameKind, h1', h2']
