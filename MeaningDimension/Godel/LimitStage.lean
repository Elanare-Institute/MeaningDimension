import MeaningDimension.Godel.EffectiveAscent
import Foundation.FirstOrder.Incompleteness.Reflection.IteratedConsistency

/-!
# Phase 2, G3: the ω-stage

Spec: `docs/spec.md`, G3.

The union of a sequence of theories need not be recursively enumerable, and `Set.iUnion` alone
gives no `Δ₁` presentation. We therefore do **not** apply Gödel II to `⋃ n, (ascent T n).theory`.
Instead we use the ω-stage that Foundation presents uniformly:

* `T.Conω = {¬□_Tⁿ⊥ | n ∈ ℕ}` (`Foundation/FirstOrder/Incompleteness/Reflection/IteratedConsistency.lean`);
* `exists_prenex_axiomatization_turingOmega`: `T ∪ T.Conω ≊ T ∪ U` for a set `U` of prenex Π₁
  sentences with an explicit `Δ₁` presentation (Foundation, known).

We add: soundness in `ℕ` of the ω-stage (from soundness of `T`), hence its consistency, and then
Gödel II for the presentation `T ∪ U`. The consistency statement of the ω-stage is the one built
from Foundation's presentation of `U`; another presentation of the same set could give a
different statement (this is the intensionality the paper is about).

Not proved here (recorded in `docs/open_problems.md`):

* that `⋃ n, (ascent T n).theory` is r.e. (needs computability of `n ↦ ⌜Con(Tₙ)⌝`);
* that `⋃ n, (ascent T n).theory ≊ T ∪ T.Conω` (needs the formalized deduction theorem
  `𝗜𝚺₁ ⊢ □_{T ∪ {φ}} ψ ↔ □_T (φ → ψ)` to identify `Con(Tₙ)` with `¬□_T^{n+1}⊥`);
* the version of G3 assuming only Σ₁-soundness of `T` (needs a compactness argument).
-/

namespace MeaningDimension.Godel

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-! ## Soundness is preserved stage by stage and in the union -/

/-- Every finite stage of the ascent from a theory true in `ℕ` is true in `ℕ`. -/
theorem models_ascent [ℕ↓[ℒₒᵣ] ⊧* T] : ∀ n, ℕ↓[ℒₒᵣ] ⊧* (ascent T n).theory
  | 0 => inferInstanceAs (ℕ↓[ℒₒᵣ] ⊧* T)
  | n + 1 => by
    have : 𝗜𝚺₁ ⪯ (ascent T n).theory := ISigma1_le_ascent T n
    have : ℕ↓[ℒₒᵣ] ⊧* (ascent T n).theory := models_ascent n
    exact (inferInstance : ℕ↓[ℒₒᵣ] ⊧* (ascent T n).theory ∪ (ascent T n).theory.Con)

/-- Soundness in `ℕ` holds uniformly, hence for the set-theoretic union of all finite stages.
(This says nothing about effectiveness of the union.) -/
theorem models_iUnion_ascent [ℕ↓[ℒₒᵣ] ⊧* T] : ℕ↓[ℒₒᵣ] ⊧* ⋃ n, (ascent T n).theory := by
  constructor
  intro σ hσ
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hσ
  exact (models_ascent T n).models_set hn

/-! ## The ω-stage `T ∪ T.Conω` -/

/-- Each iterated consistency statement `¬□_Tⁿ⊥` is true in `ℕ` when `T` is Σ₁-sound. -/
theorem models_conItr [T.SoundOnHierarchy 𝚺 1] (n : ℕ) :
    ℕ↓[ℒₒᵣ] ⊧ T.standardProvability.conItr n := by
  rcases n with _ | k
  · simp [ProvabilityAbstraction.Provability.conItr]
  · have h : ¬ ℕ↓[ℒₒᵣ] ⊧ T.standardProvability^[k + 1] ⊥ :=
      (models_boxBot_iff (T := T) (n := k)).not.mpr (by simp [height_eq_top_of_sigma1_sound])
    change ℕ↓[ℒₒᵣ] ⊧ ∼(T.standardProvability^[k + 1] ⊥)
    exact Semantics.Not.models_not.mpr h

theorem models_Conω [T.SoundOnHierarchy 𝚺 1] : ℕ↓[ℒₒᵣ] ⊧* T.Conω := by
  constructor
  rintro σ ⟨n, rfl⟩
  exact models_conItr T n

theorem models_turingOmega [ℕ↓[ℒₒᵣ] ⊧* T] : ℕ↓[ℒₒᵣ] ⊧* T ∪ T.Conω := by
  have : ℕ↓[ℒₒᵣ] ⊧* T.Conω := models_Conω T
  simp [*]

/-- **G3** (ω-stage). If `T` is true in `ℕ`, then the ω-stage `T ∪ T.Conω` has a uniformly
`Δ₁`-presented Π₁ axiomatization `T ∪ U` (Foundation), that presentation does not prove its own
consistency statement, and adjoining it gives a strictly stronger theory, which is also strictly
stronger than `T ∪ T.Conω`. -/
theorem G3 [ℕ↓[ℒₒᵣ] ⊧* T] :
    ∃ (U : ArithmeticTheory) (_ : U.Δ₁),
      (∀ σ ∈ U, ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 1 σ) ∧
      (T ∪ T.Conω ≊ T ∪ U) ∧
      (T ∪ U) ⊬ (T ∪ U).consistent.val ∧
      (T ∪ U) ⪱ (T ∪ U) ∪ (T ∪ U).Con ∧
      (T ∪ T.Conω) ⪱ (T ∪ U) ∪ (T ∪ U).Con := by
  obtain ⟨U, hU, hPi, heq⟩ := exists_prenex_axiomatization_turingOmega (T := T)
  refine ⟨U, hU, hPi, heq, ?_⟩
  have hISigma : 𝗜𝚺₁ ⪯ T ∪ U :=
    WeakerThan.trans (inferInstance : 𝗜𝚺₁ ⪯ T) (WeakerThan.ofSubset Set.subset_union_left)
  have hconω : Consistent (T ∪ T.Conω) := by
    have : ℕ↓[ℒₒᵣ] ⊧* T ∪ T.Conω := models_turingOmega T
    exact ArithmeticTheory.consistent_of_sound _ (Eq ⊥) rfl
  have hcon : Consistent (T ∪ U) := Consistent.of_le hconω heq.symm.le
  have hunprov : (T ∪ U) ⊬ (T ∪ U).consistent.val := G1_unprovable (T ∪ U)
  have hstrict : (T ∪ U) ⪱ (T ∪ U) ∪ (T ∪ U).Con := G1_strict (T ∪ U)
  refine ⟨hunprov, hstrict, ?_⟩
  have hle : T ∪ T.Conω ⪯ (T ∪ U) ∪ (T ∪ U).Con := WeakerThan.trans heq.le hstrict.weakerThan
  exact StrictlyWeakerThan.of_unprovable_provable (φ := (T ∪ U).consistent.val)
    (fun h ↦ hunprov (heq.le.wk h))
    (by_axm (by simp))

end MeaningDimension.Godel
