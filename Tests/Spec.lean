import MeaningDimension

/-!
# Specification tests for Phases 1–2

Each `example` below is transcribed from `docs/spec.md`, not from the implementation. If an
implementation changes its statement, the corresponding `example` stops type-checking.

The second half instantiates the theorems at `𝗜𝚺₁` and `𝗣𝗔` to check that their hypotheses are
satisfiable (the theorems are not vacuous).
-/

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open MeaningDimension MeaningDimension.Godel MeaningDimension.ComplexNumbers

/-! ## P1.1 monotonicity -/

example {L : Language} {T U : Theory L} (h : T ⊆ U) {φ : Sentence L} (hT : T ⊢ φ) : U ⊢ φ :=
  provable_mono h hT

/-! ## P1.2 a refuted sentence cannot be affirmed by a consistent extension -/

example {L : Language} [L.DecidableEq] {T U : Theory L} [T ⪯ U] [Consistent U]
    {φ : Sentence L} (h : T ⊢ ∼φ) : U ⊬ φ :=
  unprovable_of_refuted h

example {L : Language} {T U : Theory L} [T ⪯ U] {M : Type} [Nonempty M] [Tarski.Structure L M]
    [M↓[L] ⊧* U] {φ : Sentence L} (h : T ⊢ ∼φ) : ¬ M↓[L] ⊧ φ :=
  not_models_of_refuted (U := U) h

example {L : Language} {M : Type} [Nonempty M] [Tarski.Structure L M] {φ : Sentence L} :
    ¬ (M↓[L] ⊧ φ ∧ M↓[L] ⊧ ∼φ) :=
  not_models_and_models_neg

/-! ## P1.3 one sentence, two structures -/

example : ∀ x : ℝ, x ^ 2 + 1 ≠ 0 := real_sq_add_one_ne_zero

example : ∃ z : ℂ, z ^ 2 + 1 = 0 := complex_sq_add_one_eq_zero

-- The sentence is literally `∃ x, x * x + 1 = 0` in `ℒₒᵣ` (checked by definitional unfolding).
example : rootSentence = (“∃ x, x * x + 1 = 0” : ArithmeticSentence) := rfl

example : ¬ ℝ↓[ℒₒᵣ] ⊧ rootSentence := real_not_models_rootSentence

open scoped ComplexOrder in
example : ℂ↓[ℒₒᵣ] ⊧ rootSentence := complex_models_rootSentence

open scoped ComplexOrder in
example : ¬ theoryOf ℝ ⊆ theoryOf ℂ := theoryOf_real_not_subset_complex

/-! ## G1 -/

section G1
variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [Consistent T]

example : T ⊬ T.consistent.val := G1_unprovable T
example : T ⪱ T ∪ T.Con := G1_strict T

end G1

/-! ## Stages -/

example (T : ArithmeticTheory) [T.Δ₁] : (ascent T 0).theory = T := rfl

example (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) :
    (ascent T (n + 1)).theory = (ascent T n).theory ∪ (ascent T n).theory.Con := rfl

/-! ## L2.1–L2.3 and G2 -/

section G2
variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]

example : ∀ n, 𝗜𝚺₁ ⪯ (ascent T n).theory := ISigma1_le_ascent T

example (S : Stage) [𝗜𝚺₁ ⪯ S.theory] [S.theory.SoundOnHierarchy 𝚺 1] :
    S.next.theory.SoundOnHierarchy 𝚺 1 :=
  S.sigma1Sound_next

variable [T.SoundOnHierarchy 𝚺 1]

example : ∀ n, Consistent (ascent T n).theory := consistent_ascent T

example : ∀ n, (ascent T n).theory ⊬ (ascent T n).theory.consistent.val := G2_unprovable T

example : ∀ n, (ascent T n).theory ⪱ (ascent T (n + 1)).theory := G2_strict T

example : ∀ m n, m < n → (ascent T m).theory ⪱ (ascent T n).theory :=
  fun _ _ h ↦ G2_strict_of_lt T h

end G2

/-! ## G2-sharp -/

section Sharp
variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [Consistent T]

example : Consistent (T ∪ T.Incon) := consistent_union_incon T
example : Inconsistent ((T ∪ T.Incon) ∪ (T ∪ T.Incon).Con) := inconsistent_next_of_union_incon T
example : ¬ (T ∪ T.Incon).SoundOnHierarchy 𝚺 1 := not_sigma1Sound_union_incon T

end Sharp

/-! ## G3 -/

example (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T] :
    ∃ (U : ArithmeticTheory) (_ : U.Δ₁),
      (∀ σ ∈ U, ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 1 σ) ∧
      (T ∪ T.Conω ≊ T ∪ U) ∧
      (T ∪ U) ⊬ (T ∪ U).consistent.val ∧
      (T ∪ U) ⪱ (T ∪ U) ∪ (T ∪ U).Con ∧
      (T ∪ T.Conω) ⪱ (T ∪ U) ∪ (T ∪ U).Con :=
  G3 T

/-! ## G4 -/

example : ∀ S : Stage, Eligible S → ∃ S' : Stage, ProperExtension S S' ∧ Eligible S' := G4

example (S : Stage) : Eligible S ↔ 𝗜𝚺₁ ⪯ S.theory ∧ S.theory.SoundOnHierarchy 𝚺 1 := Iff.rfl

example (S S' : Stage) : ProperExtension S S' ↔ S.theory ⪱ S'.theory := Iff.rfl

example : ¬ ∃ S : Stage, Eligible S ∧ ∀ σ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ σ → S.theory ⊢ σ :=
  not_exists_eligible_proves_all_truths

/-! ## Non-vacuity: the hypotheses hold for `𝗜𝚺₁` and `𝗣𝗔` -/

example : ∀ n, (ascent 𝗜𝚺₁ n).theory ⊬ (ascent 𝗜𝚺₁ n).theory.consistent.val :=
  G2_unprovable 𝗜𝚺₁

example : ∀ n, (ascent 𝗣𝗔 n).theory ⪱ (ascent 𝗣𝗔 (n + 1)).theory := G2_strict 𝗣𝗔

example : Consistent (𝗣𝗔 ∪ 𝗣𝗔.Incon) := consistent_union_incon 𝗣𝗔

example : Inconsistent ((𝗣𝗔 ∪ 𝗣𝗔.Incon) ∪ (𝗣𝗔 ∪ 𝗣𝗔.Incon).Con) :=
  inconsistent_next_of_union_incon 𝗣𝗔

example : ¬ (𝗣𝗔 ∪ 𝗣𝗔.Incon).SoundOnHierarchy 𝚺 1 := not_sigma1Sound_union_incon 𝗣𝗔

example : ∃ (U : ArithmeticTheory) (_ : U.Δ₁),
      (∀ σ ∈ U, ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 1 σ) ∧
      (𝗣𝗔 ∪ 𝗣𝗔.Conω ≊ 𝗣𝗔 ∪ U) ∧
      (𝗣𝗔 ∪ U) ⊬ (𝗣𝗔 ∪ U).consistent.val ∧
      (𝗣𝗔 ∪ U) ⪱ (𝗣𝗔 ∪ U) ∪ (𝗣𝗔 ∪ U).Con ∧
      (𝗣𝗔 ∪ 𝗣𝗔.Conω) ⪱ (𝗣𝗔 ∪ U) ∪ (𝗣𝗔 ∪ U).Con :=
  G3 𝗣𝗔

example : Eligible ⟨𝗜𝚺₁, inferInstance⟩ := ⟨inferInstance, inferInstance⟩

example : ∀ n, ProperExtension ⟨𝗣𝗔, inferInstance⟩ (Stage.next^[n + 1] ⟨𝗣𝗔, inferInstance⟩) :=
  Eligible.properExtension_iterate_next ⟨inferInstance, inferInstance⟩

/-! ## Phase 3 (preliminary): M1–M5 -/

section Disj
open MeaningDimension.MadeCanonicity FFL.FirstOrder.ProvabilityAbstraction
variable {L : Language} [L.ReferenceableBy L] [L.DecidableEq] {T₀ T : Theory L}
  (𝔅 : Provability T₀ T) (π : Sentence L)

example (σ : Sentence L) : (disjProv 𝔅 π) σ = 𝔅 σ ⋎ π := disj_apply 𝔅 π σ
example [𝔅.HBL2] : (disjProv 𝔅 π).HBL2 := inferInstance
example [𝔅.HBL2] [𝔅.HBL3] : (disjProv 𝔅 π).HBL3 := inferInstance
example : T₀ ⊢ (disjProv 𝔅 π).con 🡘 𝔅.con ⋏ ∼π := disj_con_iff 𝔅 π

end Disj

section DisjArith
open MeaningDimension.MadeCanonicity FFL.FirstOrder.ProvabilityAbstraction
variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

example : standardDisj T =
    disjProv T.standardProvability (T.standardProvability (∼T.standardProvability.con)) := rfl
example : (standardDisj T).HBL := inferInstance
example (σ : ArithmeticSentence) : ℕ↓[ℒₒᵣ] ⊧ (standardDisj T) σ ↔ T ⊢ σ :=
  standard_disj_models_iff T σ
example (σ : ArithmeticSentence) : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 ((standardDisj T) σ) :=
  standard_disj_sigma1 T σ
example : T ⊬ T.standardProvability.con 🡒 (standardDisj T).con := standard_disj_con_not_implied T
example : T ⊢ (standardDisj T).con 🡒 T.standardProvability.con := standard_disj_con_implies T
example : T ⊬ (standardDisj T).con := standard_disj_con_unprovable T

end DisjArith

-- Non-vacuity for M4–M5.
example : 𝗣𝗔 ⊬ 𝗣𝗔.standardProvability.con 🡒 (MeaningDimension.MadeCanonicity.standardDisj 𝗣𝗔).con :=
  MeaningDimension.MadeCanonicity.standard_disj_con_not_implied 𝗣𝗔
