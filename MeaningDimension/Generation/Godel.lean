import MeaningDimension.Generation.Refinement
import MeaningDimension.Godel.EffectiveAscent
import MeaningDimension.Logic.TheoryExtensions

/-!
# The Gödelian ascent: no reversal, the undecided form

Spec: `docs/mdg_spec.md`, §2.3, J5, J8, J9, MDG4, MDG5.

Between theories, a flip (`TheoryFlip`) is a sentence refuted by the earlier theory and proved by
the later one. An extension that keeps every theorem and stays consistent has no flip (MDG4(a),
A8(a)); so no step of the ascent `Tₙ → Tₙ₊₁` of A3 has one (MDG4(b)). Each step is in the
undecided form instead (`Settles`): `Con(Tₙ)` is neither proved nor refuted by `Tₙ` and is proved by
`Tₙ₊₁` (MDG4(c)).

Provable equivalence only grows along an extension (MDG5(a)). In the framework of a theory
(`provFramework`), sameness is provable equivalence (MDG5(b)), so an extension never tells apart
what the earlier theory identified, and the ascent has no step in the refinement form (MDG5(c)(d)).

This depends on reading "distinction" as provable equivalence (J5). In the cumulative framework of
the ascent (`ascentFramework`, J8), whose evaluations are provability in each earlier stage, every
step of the ascent is a step in the refinement form (MDG5(e)): `Con(Tₙ)` and `∼Con(Tₙ)` are
undecided up to `Tₙ` and told apart by `Tₙ₊₁`. In that framework the two forms coincide (MDG5(f)):
a pair is told apart at stage `n + 1` exactly when one of its members is settled there.
-/

namespace MeaningDimension.Generation

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open MeaningDimension.ACSI MeaningDimension.Godel

/-- A sentence refuted by `T` and proved by `T'`. -/
def TheoryFlip (T T' : ArithmeticTheory) (σ : ArithmeticSentence) : Prop := T ⊢ ∼σ ∧ T' ⊢ σ

/-- The undecided form: `T'` extends `T` and proves `σ`, which `T` neither proves nor refutes. -/
def Settles (T T' : ArithmeticTheory) (σ : ArithmeticSentence) : Prop :=
  T ⪯ T' ∧ T ⊬ σ ∧ T ⊬ ∼σ ∧ T' ⊢ σ

/-- The framework of a theory: each sentence `θ` gives the evaluation "provably equivalent to
`θ`" (J5). -/
def provFramework (T : ArithmeticTheory) : Framework ArithmeticSentence :=
  ⟨{P | ∃ θ, P = fun σ ↦ T ⊢ σ 🡘 θ}⟩

/-- The cumulative framework of the ascent at stage `n`: the evaluations "provable in `Tₖ`" for
every `k ≤ n` (J8). -/
def ascentFramework (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) : Framework ArithmeticSentence :=
  ⟨{P | ∃ k ≤ n, P = fun σ ↦ (ascent T k).theory ⊢ σ}⟩

/-! ## MDG4 -/

/-- MDG4(a) (A8(a)). -/
theorem not_theoryFlip {T T' : ArithmeticTheory} [T ⪯ T'] [Consistent T']
    (σ : ArithmeticSentence) : ¬ TheoryFlip T T' σ := fun ⟨h, h'⟩ ↦
  unprovable_of_refuted h h'

section Ascent

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- MDG4(b). -/
theorem ascent_not_theoryFlip (n : ℕ) (σ : ArithmeticSentence) :
    ¬ TheoryFlip (ascent T n).theory (ascent T (n + 1)).theory σ := by
  have : (ascent T n).theory ⪯ (ascent T (n + 1)).theory := (ascent T n).le_next
  have := consistent_ascent T (n + 1)
  exact not_theoryFlip σ

/-- MDG4(c). -/
theorem ascent_settles (n : ℕ) :
    Settles (ascent T n).theory (ascent T (n + 1)).theory
      (ascent T n).theory.consistent.val := by
  have := ISigma1_le_ascent T n
  have := sigma1Sound_ascent T n
  have := consistent_ascent T n
  refine ⟨(ascent T n).le_next, G2_unprovable T n, ?_, ?_⟩
  · exact ProvabilityAbstraction.con_unrefutable (𝔅 := (ascent T n).theory.standardProvability)
  · exact by_axm (Set.mem_union_right _ rfl)

end Ascent

/-! ## MDG5 -/

/-- MDG5(a). -/
theorem provable_iff_mono {T T' : ArithmeticTheory} (h : T ⪯ T') {φ ψ : ArithmeticSentence} :
    T ⊢ φ 🡘 ψ → T' ⊢ φ 🡘 ψ :=
  h.wk

/-- MDG5(b). -/
theorem provFramework_same_iff (T : ArithmeticTheory) (φ ψ : ArithmeticSentence) :
    (provFramework T).Same φ ψ ↔ T ⊢ φ 🡘 ψ := by
  constructor
  · intro h
    have hψ : T ⊢ ψ 🡘 ψ := by cl_prover
    exact (h _ ⟨ψ, rfl⟩).mpr hψ
  · rintro h P ⟨θ, rfl⟩
    constructor
    · intro hφ; cl_prover [h, hφ]
    · intro hψ; cl_prover [h, hψ]

/-- MDG5(c). -/
theorem not_distinctionFlip_provFramework {T T' : ArithmeticTheory} (h : T ⪯ T')
    (φ ψ : ArithmeticSentence) :
    ¬ DistinctionFlip (provFramework T) (provFramework T') φ ψ := fun ⟨hs, hs'⟩ ↦
  hs' ((provFramework_same_iff T' φ ψ).mpr
    (provable_iff_mono h ((provFramework_same_iff T φ ψ).mp hs)))

/-- MDG5(c). -/
theorem not_refineStep_provFramework {T T' : ArithmeticTheory} (h : T ⪯ T') :
    ¬ RefineStep (provFramework T) (provFramework T') := fun ⟨_, φ, ψ, hf⟩ ↦
  not_distinctionFlip_provFramework h φ ψ hf

/-- MDG5(d). -/
theorem ascent_not_refineStep (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) :
    ¬ RefineStep (provFramework (ascent T n).theory) (provFramework (ascent T (n + 1)).theory) :=
  not_refineStep_provFramework (ascent T n).le_next

theorem ascent_le_of_le (T : ArithmeticTheory) [T.Δ₁] {k n : ℕ} (h : k ≤ n) :
    (ascent T k).theory ⪯ (ascent T n).theory := by
  induction n with
  | zero => obtain rfl := Nat.le_zero.mp h; exact WeakerThan.refl _
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · exact WeakerThan.trans (ih (Nat.lt_succ_iff.mp h)) (ascent T n).le_next
    · exact WeakerThan.refl _

theorem ascentFramework_refines (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) :
    Refines (ascentFramework T n) (ascentFramework T (n + 1)) :=
  fun _ ⟨k, hk, hP⟩ ↦ ⟨k, Nat.le_succ_of_le hk, hP⟩

section Cumulative

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- MDG5(f): a sentence settled at stage `n + 1` is told apart from its negation there, and not
before. -/
theorem distinctionFlip_of_settles (n : ℕ) {σ : ArithmeticSentence}
    (h : Settles (ascent T n).theory (ascent T (n + 1)).theory σ) :
    DistinctionFlip (ascentFramework T n) (ascentFramework T (n + 1)) σ (∼σ) := by
  obtain ⟨-, hnp, hnr, hp⟩ := h
  refine ⟨?_, ?_⟩
  · rintro P ⟨k, hk, rfl⟩
    have hle := ascent_le_of_le T hk
    exact ⟨fun h ↦ absurd (hle.wk h) hnp, fun h ↦ absurd (hle.wk h) hnr⟩
  · intro hs
    have := consistent_ascent T (n + 1)
    have hneg : (ascent T (n + 1)).theory ⊢ ∼σ := (hs _ ⟨n + 1, le_rfl, rfl⟩).mp hp
    exact unprovable_of_refuted (T := (ascent T (n + 1)).theory) (by simpa using hneg) hp

/-- MDG5(f): a pair told apart at stage `n + 1` has a member settled there. -/
theorem settles_of_distinctionFlip (n : ℕ) {φ ψ : ArithmeticSentence}
    (h : DistinctionFlip (ascentFramework T n) (ascentFramework T (n + 1)) φ ψ) :
    Settles (ascent T n).theory (ascent T (n + 1)).theory φ ∨
      Settles (ascent T n).theory (ascent T (n + 1)).theory ψ := by
  obtain ⟨hs, hns⟩ := h
  have hn : ((ascent T n).theory ⊢ φ) ↔ ((ascent T n).theory ⊢ ψ) := hs _ ⟨n, le_rfl, rfl⟩
  have hk : ¬ (((ascent T (n + 1)).theory ⊢ φ) ↔ ((ascent T (n + 1)).theory ⊢ ψ)) := by
    intro hiff
    apply hns
    rintro P ⟨k, hk, rfl⟩
    rcases Nat.lt_or_eq_of_le hk with hk | rfl
    · exact hs _ ⟨k, Nat.lt_succ_iff.mp hk, rfl⟩
    · exact hiff
  have := consistent_ascent T (n + 1)
  have hle := (ascent T n).le_next
  have aux : ∀ χ χ', (((ascent T n).theory ⊢ χ) ↔ ((ascent T n).theory ⊢ χ')) →
      (ascent T (n + 1)).theory ⊢ χ → ¬ (ascent T (n + 1)).theory ⊢ χ' →
      Settles (ascent T n).theory (ascent T (n + 1)).theory χ := fun χ χ' hiff hp hnp ↦
    ⟨hle, fun h ↦ hnp (hle.wk (hiff.mp h)),
      fun h ↦ unprovable_of_refuted (T := (ascent T (n + 1)).theory) (hle.wk h) hp, hp⟩
  by_cases hφ : (ascent T (n + 1)).theory ⊢ φ
  · exact .inl (aux φ ψ hn hφ fun hψ ↦ hk ⟨fun _ ↦ hψ, fun _ ↦ hφ⟩)
  · have hψ : (ascent T (n + 1)).theory ⊢ ψ := by
      by_contra hψ
      exact hk ⟨fun h ↦ absurd h hφ, fun h ↦ absurd h hψ⟩
    exact .inr (aux ψ φ hn.symm hψ hφ)

/-- MDG5(f): in the cumulative framework, a step of the ascent is in the refinement form exactly
when it is in the undecided form. -/
theorem ascent_refineStep_iff (n : ℕ) :
    RefineStep (ascentFramework T n) (ascentFramework T (n + 1)) ↔
      ∃ σ, Settles (ascent T n).theory (ascent T (n + 1)).theory σ := by
  constructor
  · rintro ⟨-, φ, ψ, h⟩
    rcases settles_of_distinctionFlip T n h with h | h
    · exact ⟨φ, h⟩
    · exact ⟨ψ, h⟩
  · rintro ⟨σ, h⟩
    exact ⟨ascentFramework_refines T n, σ, ∼σ, distinctionFlip_of_settles T n h⟩

/-- MDG5(e) (J8): in the cumulative framework, each step of the ascent is a step in the refinement
form. `Con(Tₙ)` and `∼Con(Tₙ)` are not told apart by provability in `T₀, …, Tₙ`, and are told
apart by provability in `Tₙ₊₁`. -/
theorem ascent_refineStep (n : ℕ) : RefineStep (ascentFramework T n) (ascentFramework T (n + 1)) :=
  ⟨ascentFramework_refines T n, _, _, distinctionFlip_of_settles T n (ascent_settles T n)⟩

end Cumulative

end MeaningDimension.Generation
