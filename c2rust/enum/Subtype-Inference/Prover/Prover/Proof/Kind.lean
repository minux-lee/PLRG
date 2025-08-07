import Prover.Rules.Basic

-- Type

@[simp]
lemma sameKind_refl {t : MyType} : t ~ t := by
  induction t with
  | enum | int => simp [MyType.sameKind]
  | arrow a b ihA ihB =>
    simp [MyType.sameKind, ihA, ihB]

@[simp]
lemma sameKind_symm {t1 t2 : MyType} (h : t1 ~ t2) : t2 ~ t1 := by
  revert t2
  induction t1 with
  | enum | int =>
      intro t2; cases t2 <;> intro h
      · simp [MyType.sameKind]
      · simp [MyType.sameKind]
      · cases (by simp [MyType.sameKind] at h : False)
  | arrow a b ihA ihB =>
    intro t2; cases t2 with
    | enum | int  => intro h; cases (by simp [MyType.sameKind] at h : False)
    | arrow c d =>
      intro h
      have ⟨ha, hb⟩ :
          (a ~ c) = true ∧ (b ~ d) = true := by
        simpa [MyType.sameKind, Bool.and_eq_true] using h
      simp [MyType.sameKind, ihA, ihB, ha, hb]

lemma sameKind_transitive {t1 t2 t3: MyType}
 (h1 : t1 ~ t2) (h2 : t2 ~ t3) : t1 ~ t3 := by
revert t2 t3
induction t1 with
  | enum | int =>
    intro t2 t3 h1 h2
    cases t2 <;> cases t3 <;> simp [MyType.sameKind] at h1 h2 ⊢
  | arrow a b ihA ihB =>
    intro t2 t3 h1 h2
    cases t2 with
    | enum | int => simp [MyType.sameKind] at h1
    | arrow c d =>
      cases t3 with
      | enum | int => simp [MyType.sameKind] at h2
      | arrow e f =>
        have ⟨ha1, hb1⟩ : (a ~ c) = true ∧ (b ~ d) = true := by
          simpa [MyType.sameKind, Bool.and_eq_true] using h1
        have ⟨ha2, hb2⟩ : (c ~ e) = true ∧ (d ~ f) = true := by
          simpa [MyType.sameKind, Bool.and_eq_true] using h2
        simp [MyType.sameKind, ihA ha1 ha2, ihB hb1 hb2]

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
    | enum | int => intro h; cases (by simp [MyType.sameKind] at h : False)
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

lemma subtypeIsSameKind (t1 t2 : MyType) (h : t1 <: t2) : t1 ~ t2 := by
  cases t1 with
  | enum =>
    cases t2 with
    | enum | int => simp [MyType.sameKind]
    | arrow c d => cases (by simp [isSubType] at h : False)
  | int =>
    cases t2 with
    | enum | int => simp [MyType.sameKind]
    | arrow c d => cases (by simp [isSubType] at h : False)
  | arrow a b =>
    cases t2 with
    | enum | int => cases (by simp [isSubType] at h : False)
    | arrow c d =>
      have ⟨h₁, h₂⟩ : c <: a ∧ b <: d := by simpa [isSubType, Bool.and_eq_true] using h
      simp [MyType.sameKind, subtypeIsSameKind c a h₁, subtypeIsSameKind b d h₂]
termination_by sizeOf t1 + sizeOf t2

lemma boundSubType {t1 t2 t3 : MyType} :
  ((MyType.lowerBound t1 t2 = some t3) -> (t3 <: t1) ∧ (t3 <: t2))
  ∧ (MyType.upperBound t1 t2 = some t3 -> (t1 <: t3) ∧ (t2 <: t3)) := by
  revert t2 t3
  induction t1 with
  | enum =>
    intro t2 t3; cases t2 <;> cases t3 <;> simp [MyType.lowerBound, MyType.upperBound, isSubType]
  | int =>
    intro t2 t3; cases t2 <;> cases t3 <;> simp [MyType.lowerBound, MyType.upperBound, isSubType]
  | arrow a b ihA ihB =>
    intro t2 t3;
    constructor
    · intro h
      obtain ⟨c, d, rfl⟩ : ∃ c d, t2 = .arrow c d := by
        cases t2 with
        | enum | int => simp [MyType.lowerBound] at h
        | arrow c d => exact ⟨c, d, rfl⟩
      have ⟨t1', hleft⟩ : ∃ t1', MyType.upperBound a c = some t1' := by
        cases hul : MyType.upperBound a c with
        | none =>
          cases hlr : MyType.lowerBound b d with
          | none | some _ => simp [MyType.lowerBound, hul, hlr] at h
        | some _ => simp
      have ⟨t2', hright⟩ : ∃ t2', MyType.lowerBound b d = some t2' := by
        cases hlr : MyType.lowerBound b d with
        | none =>
          cases hul : MyType.upperBound a c with
          | none | some _ => simp [MyType.lowerBound, hul, hlr] at h
        | some _ => simp
      have hsub : .arrow t1' t2' = t3 := by simpa [MyType.lowerBound, hleft, hright] using h
      rcases ihA with ⟨_, hA2⟩
      rcases ihB with ⟨hB1, _⟩
      have ⟨ha, hc⟩ : (a <: t1') = true ∧ (c <: t1') = true := hA2 hleft
      have ⟨hb, hd⟩ : (t2' <: b) = true ∧ (t2' <: d) = true := hB1 hright
      have hsub1 : .arrow t1' t2' <: a.arrow b := by simp [isSubType, ha, hb]
      have hsub2 : .arrow t1' t2' <: c.arrow d := by simp [isSubType, hc, hd]
      have hsub1' : t3 <: a.arrow b := by simpa [hsub] using hsub1
      have hsub2' : t3 <: c.arrow d := by simpa [hsub] using hsub2
      exact ⟨hsub1', hsub2'⟩
    · intro h
      obtain ⟨c, d, rfl⟩ : ∃ c d, t2 = .arrow c d := by
        cases t2 with
        | enum | int => simp [MyType.upperBound] at h
        | arrow c d => exact ⟨c, d, rfl⟩
      have ⟨t1', hleft⟩ : ∃ t1', MyType.lowerBound a c = some t1' := by
        cases hul : MyType.lowerBound a c with
        | none =>
          cases hlr : MyType.upperBound b d with
          | none | some _ => simp [MyType.upperBound, hul, hlr] at h
        | some _ => simp
      have ⟨t2', hright⟩ : ∃ t2', MyType.upperBound b d = some t2' := by
        cases hlr : MyType.upperBound b d with
        | none =>
          cases hul : MyType.lowerBound a c with
          | none | some _ => simp [MyType.upperBound, hul, hlr] at h
        | some _ => simp
      have hsub : .arrow t1' t2' = t3 := by simpa [MyType.upperBound, hleft, hright] using h
      rcases ihA with ⟨hA1, _⟩
      rcases ihB with ⟨_, hB2⟩
      have ⟨ha, hc⟩ : (t1' <: a) = true ∧ (t1' <: c) = true := hA1 hleft
      have ⟨hb, hd⟩ : (b <: t2') = true ∧ (d <: t2') = true := hB2 hright
      have hsub1 : a.arrow b <: .arrow t1' t2' := by simp [isSubType, ha, hb]
      have hsub2 : c.arrow d <: .arrow t1' t2' := by simp [isSubType, hc, hd]
      have hsub1' : a.arrow b <: t3 := by simpa [hsub] using hsub1
      have hsub2' : c.arrow d <: t3 := by simpa [hsub] using hsub2
      exact ⟨hsub1', hsub2'⟩

-- TypeEnv

lemma sameKindTEnvAfterAddingSameKindType
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
    {Γ : TypeEnv} {n : Nat} {t : MyType} {A : AssociatedTypeEnv}
    (h : require Γ (.const n) t = some A) :
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
    (h : t1 = .enum ∨ t1 = .int)
    (h' : t2 = .enum ∨ t2 = .int) :
    t1 ~ t2 := by
  cases h with
  | inl h1 =>
      cases h' with
      | inl h2 => simp [h1, h2]
      | inr h2 => simp [MyType.sameKind, h1, h2]
  | inr h1 =>
      cases h' with
      | inl h2 => simp [MyType.sameKind, h1, h2]
      | inr h2 => simp [h1, h2]

lemma checkVarLookupIsSome
    {Γ : TypeEnv} {x : String} {t : MyType} {A : AssociatedTypeEnv}
    (h : check Γ (.var x) = some (t, A)) :
    Γ.lookup x = some t := by
  have h' : (match Γ.lookup x with
            | none => none
            | some t => some (t, [])) = some (t, A) := by
    simpa [check] using h
  cases hoption: Γ.lookup x with
  | none => simp [hoption] at h'
  | some t' =>
    have h : t = t' ∧ A = [] := by
      simpa [hoption] using h'.symm
    simp [h]

lemma requireVarLookupIsSomeAndSameKind
    {Γ : TypeEnv} {x : String} {t : MyType} {A : AssociatedTypeEnv}
    (h : require Γ (.var x) t = some A) :
    ∃t' , (Γ.lookup x = some t' ∧ t' ~ t) := by
  by_cases hreq: isRequiredType t
  · have h' : (match Γ.lookup x with
              | some t' => if (t' ~ t) = true then some [(x, t)] else none
              | x => none) =
              some A := by
      simpa [require, hreq] using h
    cases hlookup: Γ.lookup x with
    | none => simp [hlookup] at h'
    | some t' =>
      have hin : (t' ~ t) = true ∧ [(x, t)] = A := by
        simpa [hlookup] using h'
      simp [hin]
  · have ⟨t1, ⟨hCheck, hSub⟩⟩ : ∃t1, (check Γ (.var x) = some (t1, A) ∧ t1 <: t) := by
      have h'' : ((check Γ (.var x)) >>= fun x =>
          if (x.fst <: t) = true then some x.snd else none) = some A := by
        simpa [require, hreq] using h
      cases hcheck : check Γ (.var x) with
      | none => simp [hcheck] at h''
      | some pair => cases hpair: pair with
        | mk t1 A' =>
          have h''': (t1 <: t) = true ∧ A' = A := by
            simpa [hcheck, hpair] using h''
          simp [h''']
    have hlookup : Γ.lookup x = some t1 := checkVarLookupIsSome hCheck
    exists t1
    simp [hlookup, subtypeIsSameKind t1 t hSub]

lemma sameKindEnvironmentProvidesSameKindTypeOnSameVariable
    {Γ1 Γ2 : TypeEnv} {x : String} {t1 t2 : MyType}
    (hΓ : (Γ1 ~ Γ2) = true)
    (ht1 : Γ1.lookup x = some t1)
    (ht2 : Γ2.lookup x = some t2) :
    t1 ~ t2 := by
  revert Γ2 t2 ht2 ht1
  induction Γ1 with
  | nil =>
      intro Γ2 t2 ht2 ht1 hΓ
      simp [TypeEnv.lookup] at ht1
  | cons pair Γ ih =>
    cases pair with
    | mk x' t' =>
      intro Γ2 t2 hΓ ht1 ht2
      cases Γ2 with
      | nil =>
          simp [TypeEnv.sameKind] at hΓ
      | cons pair2 Γ2' =>
        cases pair2 with
        | mk x2 t2h =>
          have hhead :
              (x' = x2 ∧ (t' ~ t2h) = true) ∧ (Γ ~ Γ2') = true := by
            simpa [TypeEnv.sameKind, Bool.and_eq_true] using hΓ
          by_cases hx : x = x'
          · have ht1' : t' = t1 := by
              simpa [TypeEnv.lookup, hx] using ht1
            have hxx2 : x = x2 := by simpa [hx] using hhead.1.left
            have ht2' : t2h = t2 := by
              simpa [TypeEnv.lookup, hxx2] using ht2
            simpa [ht1', ht2'] using hhead.left.right
          · have ht1tail : TypeEnv.lookup Γ x = some t1 := by
              simpa [TypeEnv.lookup, hx] using ht1
            have hx_ne_x2 : x ≠ x2 := by
              intro hxeq
              have : x = x' := by simpa [hhead.1] using hxeq
              exact hx this
            have ht2tail : TypeEnv.lookup Γ2' x = some t2 := by
              simpa [TypeEnv.lookup, hx_ne_x2] using ht2
            exact ih (Γ2 := Γ2') (t2 := t2) hhead.right ht1tail ht2tail

lemma checkBinopIsInt
    {Γ : TypeEnv} {e1 e2 : Expr} {t : MyType} {A : AssociatedTypeEnv}
    (h : check Γ (.binop e1 e2) = some (t, A)) :
    t = .int := by
  cases hcheck1: check Γ e1 with
  | none => simp [check, hcheck1] at h
  | some pair1 =>
    cases hcheck2: check Γ e2 with
    | none => simp [check, hcheck2] at h
    | some pair2 =>
      cases pair1 with
      | mk t1 A1 =>
        cases pair2 with
        | mk t2 A2 =>
          by_cases hint1 : t1 <: .int
          · by_cases hint2 : t2 <: .int
            · have h1 : t = .int := by
                cases hA : (A1⋃A2) with
                | none => simpa [check, hcheck1, hcheck2, hint1, hint2, hA] using h.symm
                | some A' =>
                  have hmore : t = MyType.int ∧ A = A' := by
                    simpa [check, hcheck1, hcheck2, hint1, hint2, hA] using h.symm
                  simp [hmore]
              simp [h1]
            · simp [check, hcheck1, hcheck2, hint1, hint2] at h
          · simp [check, hcheck1, hcheck2, hint1] at h

lemma requireBinopIsInt
    {Γ : TypeEnv} {e1 e2 : Expr} {t : MyType} {A : AssociatedTypeEnv}
    (h : require Γ (.binop e1 e2) t = some A) :
    t = .int := by
  by_cases hreq : isRequiredType t
  · simp [require, hreq] at h
  · have hin1 : ((check Γ (.binop e1 e2)) >>= fun x =>
                  if (x.fst <: t) = true then some x.snd else none) = some A := by
      simpa [require, hreq] using h
    cases hcheck : check Γ (.binop e1 e2) with
    | none => simp [hcheck] at hin1
    | some pair =>
      cases hpair: pair with
      | mk t1 A1 =>
        have hcheck' : check Γ (.binop e1 e2) = (t1, A1) := by
          simp [hcheck, hpair]
        have ht1 : t1 = .int := checkBinopIsInt hcheck'
        cases ht: t with
        | enum => simp [isRequiredType, ht] at *
        | int => simp
        | arrow l r =>
          simp [hcheck', ht1, isSubType, ht] at hin1

lemma replaceAndLookupSame
    {A : AssociatedTypeEnv} {x : String} {t t' : MyType} :
    (h : AssociatedTypeEnv.lookup
      (A.map (fun (y, ty) => if y = x then (y, t) else (y, ty))) x = some t') ->
    t = t' := by
  induction A with
  | nil => intro h; simp [AssociatedTypeEnv.lookup] at h
  | cons pair A' ih =>
    intro h
    cases hpair : pair with
    | mk y ty =>
      by_cases hy : y = x
      · simpa [AssociatedTypeEnv.lookup, hy, hpair] using h
      · have hInductive :
          AssociatedTypeEnv.lookup
            (A'.map (fun (y, ty) => if y = x then (y, t) else (y, ty))) x = some t' := by
          simpa [AssociatedTypeEnv.lookup, hy, hpair] using h
        exact ih hInductive

lemma addAssociatedTypeSameKind
    {A : AssociatedTypeEnv} {x : String} {t t' : MyType}
    (h : ((A.add x t) >>= (fun atenv => (atenv.lookup x)) = some t')) :
    t ~ t' := by
  have ⟨Aadd, hAddSome⟩ : ∃ Aadd, (A.add x t) = some Aadd := by
    cases hadd: (A.add x t) with
    | none => simp [hadd] at h
    | some Aadd => simp
  have ⟨tlook, hLookup⟩ : ∃ tlook, Aadd.lookup x = some tlook := by
    cases hlookup: Aadd.lookup x with
    | none => simp [hlookup, hAddSome] at h
    | some _ => simp
  have hlook : tlook = t' := by
    simpa [hAddSome, hLookup] using h
  cases hlookup : A.lookup x with
  | none =>
    have haddlook : AssociatedTypeEnv.lookup ((x, t) :: A) x = some t := by
      simp [AssociatedTypeEnv.lookup]
    have haddnaive : (x, t) :: A = Aadd := by simpa [hlookup, AssociatedTypeEnv.add] using hAddSome
    have haaddlook : (Aadd.lookup x) = some t := by simpa [haddnaive] using haddlook
    have htlookt : tlook = t := by simpa [hLookup] using haaddlook
    have htt' : t = t' := by simpa [htlookt] using hlook
    simp [htt', sameKind_refl]
  | some tlookup =>
    have ⟨tl, hlowerBoundSome⟩ : ∃ tl, MyType.lowerBound t tlookup = some tl := by
      cases hlower: MyType.lowerBound t tlookup with
      | none => simp [AssociatedTypeEnv.add, hlookup, hlower] at hAddSome
      | some tl => simp
    obtain ⟨hLower, hUpper⟩ := boundSubType
    obtain ⟨hlower, _⟩ := hLower hlowerBoundSome
    have hAddMap : Aadd = A.map (fun (y, ty) => if y = x then (y, tl) else (y, ty)) := by
      simpa [AssociatedTypeEnv.add, hlookup, hlowerBoundSome] using hAddSome.symm
    have hreplaceAndLookup :
      AssociatedTypeEnv.lookup (
        A.map (fun (y, ty) => if y = x then (y, tl) else (y, ty))) x = some t' := by
      simpa [hAddMap, hlook] using hLookup
    obtain hreplace := replaceAndLookupSame hreplaceAndLookup
    have hsub : t' <: t := by simpa [hreplace.symm] using hlower
    obtain hres := subtypeIsSameKind t' t hsub
    exact sameKind_symm hres

lemma checkDecFirstBodySome
    {Γ : TypeEnv} {x : String} {t t' : MyType} {e1 e2 : Expr} {A : AssociatedTypeEnv}
    (h : check Γ (.dec x t e1 e2) = some (t', A)) :
    ∃t1, ∃A1, check ((x, t) :: Γ) e2 = some (t1, A1) := by
  cases hcheck1 : check ((x, t) :: Γ) e2 with
  | none => simp [check, hcheck1] at h
  | some pair1 =>
    cases pair1 with
    | mk t1 A1 => simp

theorem checkOrRequireSameKind
    {Γ1 Γ2 : TypeEnv} {e : Expr} {t1 t2 : MyType}
    (hΓ : (Γ1 ~ Γ2) = true) :
    (((∃A1, check Γ1 e = some (t1, A1)) ∧ (∃A2, check Γ2 e = some (t2, A2))) -> t1 ~ t2)
      ∧ (((isRequiredType t1) ∧ (isRequiredType t2)
        ∧ (∃A1, require Γ1 e t1 = some A1) ∧ (∃A2, require Γ2 e t2 = some A2)) -> t1 ~ t2) := by
  revert Γ1 Γ2 t1 t2
  induction e with
  | const n =>
      intro Γ1 Γ2 t1 t2 hΓ
      constructor
      · intro h
        rcases h with ⟨⟨A1, h1⟩, ⟨A2, h2⟩⟩
        have h1' : t1 = .enum ∨ t1 = .int := checkConstantIsEnumOrInt h1
        have h2' : t2 = .enum ∨ t2 = .int := checkConstantIsEnumOrInt h2
        exact (enumOrIntSameKind h1' h2')
      · intro h
        rcases h with ⟨ht1, ht2, ⟨A1, h1⟩, ⟨A2, h2⟩⟩
        have h1' : t1 = .enum ∨ t1 = .int := requireConstantIsEnumOrInt h1
        have h2' : t2 = .enum ∨ t2 = .int := requireConstantIsEnumOrInt h2
        exact (enumOrIntSameKind h1' h2')
  | var x =>
      intro Γ1 Γ2 t1 t2 hΓ
      constructor
      · intro h
        rcases h with ⟨⟨A1, h1⟩, ⟨A2, h2⟩⟩
        have ht1 : (Γ1.lookup x) = some t1 := checkVarLookupIsSome h1
        have ht2 : (Γ2.lookup x) = some t2 := checkVarLookupIsSome h2
        exact sameKindEnvironmentProvidesSameKindTypeOnSameVariable hΓ ht1 ht2
      · intro h
        rcases h with ⟨ht1, ht2, ⟨A1, h1⟩, ⟨A2, h2⟩⟩
        have ht1 : ∃ t', Γ1.lookup x = some t' ∧ (t' ~ t1) = true :=
          requireVarLookupIsSomeAndSameKind h1
        have ht2 : ∃ t', Γ2.lookup x = some t' ∧ (t' ~ t2) = true :=
          requireVarLookupIsSomeAndSameKind h2
        rcases ht1 with ⟨t1', ⟨hl1, hs1⟩⟩
        rcases ht2 with ⟨t2', ⟨hl2, hs2⟩⟩
        have t1't2' : t1' ~ t2' := sameKindEnvironmentProvidesSameKindTypeOnSameVariable hΓ hl1 hl2
        have t1t1' : t1 ~ t1' := by simp [hs1]
        have t2't2 : t2' ~ t2 := by simp [hs2]
        have t1t2' : t1 ~ t2' := sameKind_transitive t1t1' t1't2'
        exact sameKind_transitive t1t2' t2't2
  | binop e1 e2 =>
      intro Γ1 Γ2 t1 t2 hΓ
      constructor
      · intro h
        rcases h with ⟨⟨A1, h1⟩, ⟨A2, h2⟩⟩
        have ht1 : t1 = .int := checkBinopIsInt h1
        have ht2 : t2 = .int := checkBinopIsInt h2
        simp [ht1, ht2]
      · intro h
        rcases h with ⟨ht1, ht2, ⟨A1, h1⟩, ⟨A2, h2⟩⟩
        have ht1 : t1 = .int := requireBinopIsInt h1
        have ht2 : t2 = .int := requireBinopIsInt h2
        simp [ht1, ht2]
  | dec x t e1 e2 ih1 ih2 =>
      intro Γ1 Γ2 t1 t2 hΓ
      constructor
      · intro h
        rcases h with ⟨⟨A1, h1⟩, ⟨A2, h2⟩⟩
        obtain ⟨t1', A1', hcheck1some⟩ := checkDecFirstBodySome h1
        obtain ⟨t2', A2', hcheck2some⟩ := checkDecFirstBodySome h2
        have ⟨Add1, hadd1some⟩ : ∃ Add1, A1'.add x t = some Add1 := by
          cases hA1 : A1'.add x t with
          | none => simp [check, hcheck1some, hA1] at h1
          | some Add1 => simp
        have ⟨Add2, hadd2some⟩ : ∃ Add2, A2'.add x t = some Add2 := by
          cases hA2 : A2'.add x t with
          | none => simp [check, hcheck2some, hA2] at h2
          | some Add2 => simp
        have ⟨tlook1, hlookup1some⟩ : ∃ tlook1, Add1.lookup x = some tlook1 := by
          cases hlookup1 : Add1.lookup x with
          | none => simp [check, hcheck1some, hadd1some, hlookup1] at h1
          | some tlook1 => simp
        have ⟨tlook2, hlookup2some⟩ : ∃ tlook2, Add2.lookup x = some tlook2 := by
          cases hlookup2 : Add2.lookup x with
          | none => simp [check, hcheck2some, hadd2some, hlookup2] at h2
          | some tlook2 => simp
        have htlooksamekind : tlook1 ~ tlook2 := by
          have hyp1 : ((A1'.add x t) >>= (fun atenv => (atenv.lookup x)) = some tlook1) := by
            simp [hadd1some, hlookup1some]
          have hyp2 : ((A2'.add x t) >>= (fun atenv => (atenv.lookup x)) = some tlook2) := by
            simp [hadd2some, hlookup2some]
          have htt1 : (t ~ tlook1) = true := addAssociatedTypeSameKind hyp1
          have ht1t : (tlook1 ~ t) = true := sameKind_symm htt1
          have htt2 : (t ~ tlook2) = true := addAssociatedTypeSameKind hyp2
          exact sameKind_transitive ht1t htt2
        have ⟨Areq1, hreq1some⟩ : ∃Areq, require Γ1 e1 tlook1 = some Areq := by
          cases hreq1 : require Γ1 e1 tlook1 with
          | none => simp [check, hcheck1some, hadd1some, hlookup1some, hreq1] at h1
          | some Areq => simp
        have ⟨Areq2, hreq2some⟩ : ∃Areq, require Γ2 e1 tlook2 = some Areq := by
          cases hreq2 : require Γ2 e1 tlook2 with
          | none => simp [check, hcheck2some, hadd2some, hlookup2some, hreq2] at h2
          | some Areq => simp
        obtain haddEnvSameKind := sameKindTEnvAfterAddingSameKindType hΓ htlooksamekind
        have ⟨tbody1, Abody1, hbody1some⟩ :
          ∃ tbody1, ∃ Abody1, check ((x, tlook1) :: Γ1) e2 = some (tbody1, Abody1) := by
          cases hcheck1 : check ((x, tlook1) :: Γ1) e2 with
          | none => simp [check, hcheck1some, hadd1some, hlookup1some, hreq1some, hcheck1] at h1
          | some pair =>
            cases pair with
            | mk tbody1 Abody1 => simp
        have ⟨tbody2, Abody2, hbody2some⟩ :
          ∃ tbody2, ∃ Abody2, check ((x, tlook2) :: Γ2) e2 = some (tbody2, Abody2) := by
          cases hcheck2 : check ((x, tlook2) :: Γ2) e2 with
          | none => simp [check, hcheck2some, hadd2some, hlookup2some, hreq2some, hcheck2] at h2
          | some pair =>
            cases pair with
            | mk tbody2 Abody2 => simp
        obtain htbodySameKind := by
          have hbodycombine : (∃A1, check ((x, tlook1) :: Γ1) e2 = some (tbody1, A1))
                            ∧ (∃A2, check ((x, tlook2) :: Γ2) e2 = some (tbody2, A2)) := by
            simp [hbody1some, hbody2some]
          rcases (ih2 haddEnvSameKind) with ⟨hcheckSameKind, hrequireSameKind⟩
          exact hcheckSameKind hbodycombine
        obtain ⟨_, htbody1some⟩ := by simpa [
            check, hcheck1some, hadd1some, hlookup1some, hlookup2some, hreq1some, hbody1some
          ] using h1
        obtain ⟨_, htbody2some⟩ := by simpa [
            check, hcheck2some, hadd2some, hlookup1some, hlookup2some, hreq2some, hbody2some
          ] using h2
        simpa [htbody1some, htbody2some] using htbodySameKind
      · intro h
        rcases h with ⟨ht1, ht2, h1, h2⟩
        have ⟨A1', hrequire1some⟩ : ∃ A1', require ((x, t) :: Γ1) e2 t1 = some A1' := by
          cases hreqFirst1 : require ((x, t) :: Γ1) e2 t1 with
          | none => simp [require, hreqFirst1, ht1] at h1
          | some A1' => simp
        have ⟨A2', hrequire2some⟩ : ∃ A2', require ((x, t) :: Γ2) e2 t2 = some A2' := by
          cases hreqFirst2 : require ((x, t) :: Γ2) e2 t2 with
          | none => simp [require, hreqFirst2, ht2] at h2
          | some A2' => simp
        have ⟨Add1, hadd1some⟩ : ∃ Add1, A1'.add x t = some Add1 := by
          cases hA1 : A1'.add x t with
          | none => simp [require, hrequire1some, hA1, ht1] at h1
          | some Add1 => simp
        have ⟨Add2, hadd2some⟩ : ∃ Add2, A2'.add x t = some Add2 := by
          cases hA2 : A2'.add x t with
          | none => simp [require, hrequire2some, hA2, ht2] at h2
          | some Add2 => simp
        have ⟨tlook1, hlookup1some⟩ : ∃ tlook1, Add1.lookup x = some tlook1 := by
          cases hlookup1 : Add1.lookup x with
          | none => simp [require, ht1, hrequire1some, hadd1some, hlookup1] at h1
          | some tlook1 => simp
        have ⟨tlook2, hlookup2some⟩ : ∃ tlook2, Add2.lookup x = some tlook2 := by
          cases hlookup2 : Add2.lookup x with
          | none => simp [require, ht2, hrequire2some, hadd2some, hlookup2] at h2
          | some tlook2 => simp
        obtain htlooksamekind := by
          obtain hyp1 : ((A1'.add x t) >>= (fun atenv => (atenv.lookup x)) = some tlook1) := by
            simp [hadd1some, hlookup1some]
          have hyp2 : ((A2'.add x t) >>= (fun atenv => (atenv.lookup x)) = some tlook2) := by
            simp [hadd2some, hlookup2some]
          obtain htt1 := addAssociatedTypeSameKind hyp1
          obtain ht1t := sameKind_symm htt1
          obtain htt2 := addAssociatedTypeSameKind hyp2
          exact sameKind_transitive ht1t htt2
        have ⟨Areq1, hreq1some⟩ : ∃Areq, require Γ1 e1 tlook1 = some Areq := by
          cases hreq1 : require Γ1 e1 tlook1 with
          | none => simp [require, ht1, hrequire1some, hadd1some, hlookup1some, hreq1] at h1
          | some Areq => simp
        have ⟨Areq2, hreq2some⟩ : ∃Areq, require Γ2 e1 tlook2 = some Areq := by
          cases hreq2 : require Γ2 e1 tlook2 with
          | none => simp [require, ht2, hrequire2some, hadd2some, hlookup2some, hreq2] at h2
          | some Areq => simp
        obtain haddEnvSameKind := sameKindTEnvAfterAddingSameKindType hΓ htlooksamekind
        have ⟨Abody1, hbody1some⟩ : ∃ Abody1, require ((x, tlook1) :: Γ1) e2 t1 = some Abody1 := by
          cases hcheck1 : require ((x, tlook1) :: Γ1) e2 t1 with
          | none => simp [
              require, ht1, hrequire1some, hadd1some, hlookup1some, hreq1some, hcheck1] at h1
          | some _ => simp
        have ⟨Abody2, hbody2some⟩ : ∃ Abody2, require ((x, tlook2) :: Γ2) e2 t2 = some Abody2 := by
          cases hcheck2 : require ((x, tlook2) :: Γ2) e2 t2 with
          | none => simp [
              require, ht2, hrequire2some, hadd2some, hlookup2some, hreq2some, hcheck2] at h2
          | some _ => simp
        rcases (ih2 haddEnvSameKind) with ⟨_, hrequireSameKind⟩
        have hbodyCombine : (isRequiredType t1) ∧ (isRequiredType t2)
           ∧ ((∃A1, require ((x, tlook1) :: Γ1) e2 t1 = some A1)
           ∧ (∃A2, require ((x, tlook2) :: Γ2) e2 t2 = some A2)) := by
          simp [ht1, ht2, hbody1some, hbody2some]
        exact hrequireSameKind hbodyCombine
    | lambda x t' e ih =>
      intro Γ1 Γ2 t1 t2 hΓ
      constructor
      · intro h
        rcases h with ⟨⟨A1, h1⟩, ⟨A2, h2⟩⟩
        have ⟨tfirst1, Afirst1, hcheckFirst1some⟩ :
          ∃ tfirst1 Afirst1, check ((x, t') :: Γ1) e = some (tfirst1, Afirst1) := by
          cases hcheck1 : check ((x, t') :: Γ1) e with
          | none => simp [check, hcheck1] at h1
          | some pair => cases pair with | mk _ _ => simp
        have ⟨tfirst2, Afirst2, hcheckFirst2some⟩ :
          ∃ tfirst2 Afirst2, check ((x, t') :: Γ2) e = some (tfirst2, Afirst2) := by
          cases hcheck2 : check ((x, t') :: Γ2) e with
          | none => simp [check, hcheck2] at h2
          | some pair => cases pair with | mk _ _ => simp
        have ⟨Add1, hAddSome1⟩ : ∃ Add1, Afirst1.add x t' = some Add1 := by
          cases hA1 : Afirst1.add x t' with
          | none => simp [check, hcheckFirst1some, hA1] at h1
          | some Add1 => simp
        have ⟨Add2, hAddSome2⟩ : ∃ Add2, Afirst2.add x t' = some Add2 := by
          cases hA2 : Afirst2.add x t' with
          | none => simp [check, hcheckFirst2some, hA2] at h2
          | some Add2 => simp
        have ⟨tlook1, hlookup1some⟩ : ∃ tlook1, Add1.lookup x = some tlook1 := by
          cases hlookup1 : Add1.lookup x with
          | none => simp [check, hcheckFirst1some, hAddSome1, hlookup1] at h1
          | some tlook1 => simp
        have ⟨tlook2, hlookup2some⟩ : ∃ tlook2, Add2.lookup x = some tlook2 := by
          cases hlookup2 : Add2.lookup x with
          | none => simp [check, hcheckFirst2some, hAddSome2, hlookup2] at h2
          | some tlook2 => simp
        have htlooksamekind := by
          have hyp1 : ((Afirst1.add x t') >>= (fun atenv => (atenv.lookup x)) = some tlook1) := by
            simp [hAddSome1, hlookup1some]
          have hyp2 : ((Afirst2.add x t') >>= (fun atenv => (atenv.lookup x)) = some tlook2) := by
            simp [hAddSome2, hlookup2some]
          have htt1 := addAssociatedTypeSameKind hyp1
          have ht1t := sameKind_symm htt1
          have htt2 := addAssociatedTypeSameKind hyp2
          exact sameKind_transitive ht1t htt2
        obtain haddEnvSameKind := sameKindTEnvAfterAddingSameKindType hΓ htlooksamekind
        have ⟨tb1, Ab1, hcheck1some⟩ :
          ∃ tb1 Ab1, (check ((x, tlook1) :: Γ1) e) = some (tb1, Ab1) := by
          cases hcheck1 : check ((x, tlook1) :: Γ1) e with
          | none => simp [check, hcheck1, hcheckFirst1some, hAddSome1, hlookup1some] at h1
          | some pair => cases pair with | mk _ _ => simp
        have ⟨tb2, Ab2, hcheck2some⟩ :
          ∃ tb2 Ab2, (check ((x, tlook2) :: Γ2) e) = some (tb2, Ab2) := by
          cases hcheck2 : check ((x, tlook2) :: Γ2) e with
          | none => simp [check, hcheck2, hcheckFirst2some, hAddSome2, hlookup2some] at h2
          | some pair => cases pair with | mk _ _ => simp
        have htbsamekind := by
          have hcheckCombine : (∃A1, check ((x, tlook1) :: Γ1) e = some (tb1, A1))
                            ∧ (∃A2, check ((x, tlook2) :: Γ2) e = some (tb2, A2)) := by
            simp [hcheck1some, hcheck2some]
          rcases (ih haddEnvSameKind) with ⟨hcheckSameKind, _⟩
          exact hcheckSameKind hcheckCombine
        obtain ⟨_, hresult1⟩ := by simpa [
          check, hcheckFirst1some, hAddSome1, hlookup1some, hcheck1some] using h1
        obtain ⟨_, hresult2⟩ := by simpa [
          check, hcheckFirst2some, hAddSome2, hlookup2some, hcheck2some] using h2
        have harrowsamekind : (tlook1.arrow tb1) ~ (tlook2.arrow tb2) := by
          simp [htbsamekind, htlooksamekind, MyType.sameKind]
        simpa [hresult1, hresult2] using harrowsamekind
      · intro h
        rcases h with ⟨ht1, ht2, ⟨A1, h1⟩, ⟨A2, h2⟩⟩
        have ⟨t11, t12, ht1arrow⟩ : ∃ t11 t12, t1 = .arrow t11 t12 := by
          cases ht1c : t1 with
          | enum => simp [require, ht1c, isRequiredType] at h1
          | int => simp [ht1c, isRequiredType] at *
          | arrow _ _ => simp
        have ⟨t21, t22, ht2arrow⟩ : ∃ t21 t22, t2 = .arrow t21 t22 := by
          cases ht2c : t2 with
          | enum => simp [require, ht2c, isRequiredType] at h2
          | int => simp [ht2c, isRequiredType] at *
          | arrow _ _ => simp
        obtain ht1 := by simpa [ht1arrow] using ht1
        obtain ht2 := by simpa [ht2arrow] using ht2
        have ⟨Afirst1, hReqFirst1Some⟩ :
          ∃ Afirst1, require ((x, t') :: Γ1) e t12 = some Afirst1 := by
          cases hcheck1 : require ((x, t') :: Γ1) e t12 with
          | none => simp [require, ht1, hcheck1, ht1arrow] at h1
          | some _ => simp
        have ⟨Afirst2, hReqFirst2Some⟩ :
          ∃ Afirst2, require ((x, t') :: Γ2) e t22 = some Afirst2 := by
          cases hcheck2 : require ((x, t') :: Γ2) e t22 with
          | none => simp [require, ht2, hcheck2, ht2arrow] at h2
          | some _ => simp
        have ⟨Add1, hAddSome1⟩ : ∃ Add1, Afirst1.add x t' = some Add1 := by
          cases hA1 : Afirst1.add x t' with
          | none => simp [require, ht1, ht1arrow, hReqFirst1Some, hA1] at h1
          | some Add1 => simp
        have ⟨Add2, hAddSome2⟩ : ∃ Add2, Afirst2.add x t' = some Add2 := by
          cases hA2 : Afirst2.add x t' with
          | none => simp [require, ht2, ht2arrow, hReqFirst2Some, hA2] at h2
          | some Add2 => simp
        have ⟨tlook1, hlookup1some⟩ : ∃ tlook1, Add1.lookup x = some tlook1 := by
          cases hlookup1 : Add1.lookup x with
          | none => simp [require, ht1, ht1arrow, hReqFirst1Some, hAddSome1, hlookup1] at h1
          | some tlook1 => simp
        have ⟨tlook2, hlookup2some⟩ : ∃ tlook2, Add2.lookup x = some tlook2 := by
          cases hlookup2 : Add2.lookup x with
          | none => simp [require, ht2, ht2arrow, hReqFirst2Some, hAddSome2, hlookup2] at h2
          | some tlook2 => simp
        have htlooksamekind := by
          have hyp1 : ((Afirst1.add x t') >>= (fun atenv => (atenv.lookup x)) = some tlook1) := by
            simp [hAddSome1, hlookup1some]
          have hyp2 : ((Afirst2.add x t') >>= (fun atenv => (atenv.lookup x)) = some tlook2) := by
            simp [hAddSome2, hlookup2some]
          have htt1 := addAssociatedTypeSameKind hyp1
          have ht1t := sameKind_symm htt1
          have htt2 := addAssociatedTypeSameKind hyp2
          exact sameKind_transitive ht1t htt2
        obtain haddEnvSameKind := sameKindTEnvAfterAddingSameKindType hΓ htlooksamekind
        have hsub1 : tlook1 <: t11 := by
          cases hsub1 : tlook1 <: t11 with
          | true => simp
          | false => simp [
            require, ht1, ht1arrow, hsub1, hReqFirst1Some, hAddSome1, hlookup1some] at h1
        have hsub2 : tlook2 <: t21 := by
          cases hsub2 : tlook2 <: t21 with
          | true => simp
          | false => simp [
            require, ht2, ht2arrow, hsub2, hReqFirst2Some, hAddSome2, hlookup2some] at h2
        have ⟨Ab1, hcheck1some⟩ : ∃ Ab1, (require ((x, tlook1) :: Γ1) e t12) = some Ab1 := by
          cases hcheck1 : require ((x, tlook1) :: Γ1) e t12 with
          | none => simp [
            require, ht1, ht1arrow, hsub1, hcheck1, hReqFirst1Some, hAddSome1, hlookup1some] at h1
          | some _ => simp
        have ⟨Ab2, hcheck2some⟩ : ∃ Ab2, (require ((x, tlook2) :: Γ2) e t22) = some Ab2 := by
          cases hcheck2 : require ((x, tlook2) :: Γ2) e t22 with
          | none => simp [
            require, ht2, ht2arrow, hcheck2, hReqFirst2Some, hAddSome2, hlookup2some] at h2
          | some _ => simp
        have htbsamekind := by
          have hreqCombine : (isRequiredType t12) ∧ (isRequiredType t22)
                            ∧ (∃A1, require ((x, tlook1) :: Γ1) e t12 = some A1)
                            ∧ (∃A2, require ((x, tlook2) :: Γ2) e t22 = some A2) := by
            have hreq1 : isRequiredType t12 := by
              by_cases hreq1 : isRequiredType t12
              · exact hreq1
              · simp [isRequiredType, hreq1] at ht1
            have hreq2 : isRequiredType t22 := by
              by_cases hreq2 : isRequiredType t22
              · exact hreq2
              · simp [isRequiredType, hreq2] at ht2
            simp [hreq1, hreq2, hcheck1some, hcheck2some]
          rcases (ih haddEnvSameKind) with ⟨_, hrequireSameKind⟩
          exact hrequireSameKind hreqCombine
        have htpsamekind := by
          have hsub1' := subtypeIsSameKind tlook1 t11 hsub1
          have hsub2' := subtypeIsSameKind tlook2 t21 hsub2
          have hsub1'' := sameKind_symm hsub1'
          have hin := sameKind_transitive hsub1'' htlooksamekind
          exact sameKind_transitive hin hsub2'
        simp [htbsamekind, htpsamekind, MyType.sameKind, ht1arrow, ht2arrow]
    | app e1 e2 ih1 ih2 =>
      intro Γ1 Γ2 t1 t2 hΓ
      constructor
      · intro h
        rcases h with ⟨⟨A1, h1⟩, ⟨A2, h2⟩⟩
        have ⟨tF1, AF1, hCheckF1Some⟩ : ∃ tF AF, check Γ1 e1 = some (tF, AF) := by
          cases hcheck1 : check Γ1 e1 with
          | none => simp [check, hcheck1] at h1
          | some pair => cases pair with | mk _ _ => simp
        have ⟨tF2, AF2, hCheckF2Some⟩ : ∃ tF AF, check Γ2 e1 = some (tF, AF) := by
          cases hcheck2 : check Γ2 e1 with
          | none => simp [check, hcheck2] at h2
          | some pair => cases pair with | mk _ _ => simp
        have ⟨tF11, tF12, htF1Arrow⟩ : ∃ tF11 tF12, tF1 = .arrow tF11 tF12 := by
          cases htF1c : tF1 with
          | enum | int => simp [check, hCheckF1Some, htF1c] at h1
          | arrow _ _ => simp
        have ⟨tF21, tF22, htF2Arrow⟩ : ∃ tF21 tF22, tF2 = .arrow tF21 tF22 := by
          cases htF2c : tF2 with
          | enum | int => simp [check, hCheckF2Some, htF2c] at h2
          | arrow _ _ => simp
        have ⟨Areq1, hReqPSome1⟩ : ∃ Areq1, require Γ1 e2 tF11 = some Areq1 := by
          cases hreq1 : require Γ1 e2 tF11 with
          | none => simp [check, hCheckF1Some, htF1Arrow, hreq1] at h1
          | some _ => simp
        have ⟨Areq2, hReqPSome2⟩ : ∃ Areq2, require Γ2 e2 tF21 = some Areq2 := by
          cases hreq2 : require Γ2 e2 tF21 with
          | none => simp [check, hCheckF2Some, htF2Arrow, hreq2] at h2
          | some _ => simp
        have ⟨Ares1, hAtSome1⟩ : ∃ Ares, (AF1 ⋃ Areq1) = some Ares := by
          cases hAt1 : AF1 ⋃ Areq1 with
          | none => simp [check, hCheckF1Some, htF1Arrow, hReqPSome1, hAt1] at h1
          | some Ares => simp
        have ⟨Ares2, hAtSome2⟩ : ∃ Ares, (AF2 ⋃ Areq2) = some Ares := by
          cases hAt2 : AF2 ⋃ Areq2 with
          | none => simp [check, hCheckF2Some, htF2Arrow, hReqPSome2, hAt2] at h2
          | some Ares => simp
        obtain ⟨ht1, hA1⟩ := by simpa [
          check, hCheckF1Some, htF1Arrow, hReqPSome1, hAtSome1] using h1
        obtain ⟨ht2, hA2⟩ := by simpa [
          check, hCheckF2Some, htF2Arrow, hReqPSome2, hAtSome2] using h2
        have htFSameKind := by
          have hcheckCombine : (∃A1, check Γ1 e1 = some (tF1, A1))
                            ∧ (∃A2, check Γ2 e1 = some (tF2, A2)) := by
            simp [hCheckF1Some, hCheckF2Some]
          rcases (ih1 hΓ) with ⟨hcheckSameKind, _⟩
          exact hcheckSameKind hcheckCombine
        obtain ⟨_, htRetSameKind⟩ := by simpa [
          htF1Arrow, htF2Arrow, MyType.sameKind] using htFSameKind
        simpa [ht1, ht2] using htRetSameKind
      · intro h
        rcases h with ⟨ht1, ht2, ⟨A1, h1⟩, ⟨A2, h2⟩⟩
        have ⟨tF11, tF12, Afirst1, hCheckFSomeArrow1⟩ :
          ∃ tF11 tF22 A_, check Γ1 e1 = some (.arrow tF11 tF22, A_) := by
          cases hcheck1 : check Γ1 e1 with
          | none => simp [require, ht1, hcheck1] at h1
          | some pair => cases hpair : pair with
            | mk ta _ => cases hta : ta with
              | enum | int => simp [require, ht1, hcheck1, hpair, hta] at h1
              | arrow _ _ => simp
        have ⟨tF21, tF22, Afirst2, hCheckFSomeArrow2⟩ :
          ∃ tF21 tF22 A_, check Γ2 e1 = some (.arrow tF21 tF22, A_) := by
          cases hcheck2 : check Γ2 e1 with
          | none => simp [require, ht2, hcheck2] at h2
          | some pair => cases hpair : pair with
            | mk ta _ => cases hta : ta with
              | enum | int => simp [require, ht2, hcheck2, hpair, hta] at h2
              | arrow _ _ => simp
        have hForced1 : tF12 ==> t1 := by
          cases hforced1 : tF12 ==> t1 with
          | true => simp
          | false => simp [require, ht1, hforced1, hCheckFSomeArrow1] at h1
        have hForced2 : tF22 ==> t2 := by
          cases hforced2 : tF22 ==> t2 with
          | true => simp
          | false => simp [require, ht2, hforced2, hCheckFSomeArrow2] at h2
        obtain ⟨_, htx2SameKind⟩ := by
          have hcheckCombine : (∃A1, check Γ1 e1 = some (.arrow tF11 tF12, A1))
                            ∧ (∃A2, check Γ2 e1 = some (.arrow tF21 tF22, A2)) := by
            simp [hCheckFSomeArrow1, hCheckFSomeArrow2]
          rcases (ih1 hΓ) with ⟨hcheckSameKind, _⟩
          simpa [MyType.sameKind] using (hcheckSameKind hcheckCombine)
        have htF12t1sub := by simpa [forcedRequiredType, ht1] using hForced1
        have htF22t2sub := by simpa [forcedRequiredType, ht2] using hForced2
        have htF12t1SameKind : tF12 ~ t1 := by
          simp [htF12t1sub, subtypeIsSameKind]
        have htF22t2SameKind : tF22 ~ t2 := by
          simp [htF22t2sub, subtypeIsSameKind]
        have ht1tF12SameKind : t1 ~ tF12 := by
          simp [htF12t1SameKind, sameKind_symm]
        have hin := sameKind_transitive ht1tF12SameKind htx2SameKind
        exact sameKind_transitive hin htF22t2SameKind
