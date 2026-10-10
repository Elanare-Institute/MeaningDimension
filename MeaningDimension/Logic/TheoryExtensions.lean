import Foundation.FirstOrder.Incompleteness.Examples

/-!
# Phase 1.1–1.2: theory extensions

Spec: `docs/spec.md`, P1.1 and P1.2.

* `provable_mono` restates Foundation's weakening lemma (known; not a new result).
* `unprovable_of_refuted` and its semantic versions say that an extension which preserves the
  language, the proof system (classical first-order logic) and every theorem of `T` cannot
  affirm a sentence that `T` refutes, unless it is inconsistent. This is elementary.

What these lemmas do *not* say: they say nothing about changing the language or the
interpretation. That case is `MeaningDimension/Examples/ComplexNumbers.lean`, where the same
sentence is evaluated in two different structures.
-/

namespace MeaningDimension

open FFL FFL.FirstOrder FFL.Entailment

variable {L : Language}

/-- P1.1 (monotonicity). Enlarging the axiom set preserves provability. -/
theorem provable_mono {T U : Theory L} (h : T ⊆ U) {φ : Sentence L} : T ⊢ φ → U ⊢ φ :=
  Entailment.weakening (Entailment.WeakerThan.ofSubset h)

/-- P1.2 (syntactic). If `U` keeps every theorem of `T` and is consistent, then `U` cannot prove
a sentence that `T` refutes. `φ` is the same sentence of the same language in both theories. -/
theorem unprovable_of_refuted [L.DecidableEq] {T U : Theory L} [T ⪯ U] [Consistent U]
    {φ : Sentence L} (h : T ⊢ ∼φ) : U ⊬ φ := by
  intro hU
  have h' : U ⊢ ∼φ := WeakerThan.pbl h
  have hbot : U ⊢ ⊥ := by cl_prover [hU, h']
  exact consistent_iff_unprovable_bot.mp inferInstance hbot

/-- P1.2 (single structure). No structure makes both `φ` and `∼φ` true. -/
theorem not_models_and_models_neg {M : Type*} [Nonempty M] [Tarski.Structure L M]
    {φ : Sentence L} : ¬ (M↓[L] ⊧ φ ∧ M↓[L] ⊧ ∼φ) := by
  rintro ⟨h, hn⟩
  exact (Semantics.Not.models_not.mp hn) h

/-- P1.2 (semantic). Under one fixed interpretation `M` that satisfies an extension `U` of `T`,
a sentence refuted by `T` is false. -/
theorem not_models_of_refuted {T U : Theory L} [T ⪯ U] {M : Type*} [Nonempty M]
    [Tarski.Structure L M] [M↓[L] ⊧* U] {φ : Sentence L} (h : T ⊢ ∼φ) : ¬ M↓[L] ⊧ φ := by
  have hU : U ⊢ ∼φ := WeakerThan.pbl h
  have hM : M↓[L] ⊧ ∼φ := models_of_provable inferInstance hU
  exact Semantics.Not.models_not.mp hM

end MeaningDimension
