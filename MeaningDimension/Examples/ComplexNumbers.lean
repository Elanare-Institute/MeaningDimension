import Foundation.FirstOrder.Incompleteness.Examples
import Mathlib.Analysis.Complex.Basic

/-!
# Phase 1.3: one sentence, two structures (ℝ and ℂ)

Spec: `docs/spec.md`, P1.3.

The paper (§2.1, §3.1) says that `x² + 1 = 0` is a contradiction in ℝ that the construction of
ℂ "made true". What can be checked is narrower:

* the first-order sentence `∃ x, x * x + 1 = 0` is *false* in ℝ and *true* in ℂ;
* hence it is a *refutable* sentence of the theory of ℝ, not a true contradiction there;
* the theory of ℂ is not an extension of the theory of ℝ (`Th ℝ ⊄ Th ℂ`): passing to ℂ changes
  the domain of quantification, and the universal sentence `∀ x, x * x + 1 ≠ 0` is lost.

Nothing here shows that a sentence and its negation are both true anywhere
(`MeaningDimension.not_models_and_models_neg` rules that out for every structure).

The language is Foundation's `ℒₒᵣ` (`0, 1, +, *, =, <`). ℂ interprets `<` by Mathlib's partial
order from `ComplexOrder`; `rootSentence` does not mention `<`.
-/

namespace MeaningDimension.ComplexNumbers

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

/-- P1.3(a), meta level (Mathlib): `x² + 1` has no real root. -/
theorem real_sq_add_one_ne_zero : ∀ x : ℝ, x ^ 2 + 1 ≠ 0 := fun x ↦ by positivity

/-- P1.3(b), meta level (Mathlib): `i` is a complex root of `z² + 1`. -/
theorem complex_sq_add_one_eq_zero : ∃ z : ℂ, z ^ 2 + 1 = 0 :=
  ⟨Complex.I, by simp [Complex.I_sq]⟩

/-- The single first-order sentence evaluated in both structures. -/
noncomputable def rootSentence : ArithmeticSentence := “∃ x, x * x + 1 = 0”

/-- P1.3(c): the sentence is false in ℝ. -/
theorem real_not_models_rootSentence : ¬ ℝ↓[ℒₒᵣ] ⊧ rootSentence := by
  simp [rootSentence, models_iff]
  intro x
  nlinarith [sq_nonneg x]

open scoped ComplexOrder in
/-- P1.3(c): the same sentence is true in ℂ. -/
theorem complex_models_rootSentence : ℂ↓[ℒₒᵣ] ⊧ rootSentence := by
  simp [rootSentence, models_iff]
  exact ⟨Complex.I, by simp⟩

/-- The complete first-order theory of a structure in the language `ℒₒᵣ`. -/
def theoryOf (M : Type*) [Nonempty M] [ORingStructure M] : ArithmeticTheory :=
  {σ | M↓[ℒₒᵣ] ⊧ σ}

open scoped ComplexOrder in
/-- P1.3(d): the theory of ℂ does not contain the theory of ℝ. Passing from ℝ to ℂ is a change of
structure, not an extension of the real theory that keeps its theorems. -/
theorem theoryOf_real_not_subset_complex : ¬ theoryOf ℝ ⊆ theoryOf ℂ := by
  intro h
  have hR : (∼rootSentence) ∈ theoryOf ℝ := by
    simpa [theoryOf] using real_not_models_rootSentence
  have hC : ℂ↓[ℒₒᵣ] ⊧ ∼rootSentence := h hR
  exact (Semantics.Not.models_not.mp hC) complex_models_rootSentence

/-- P1.3(e): the embedding `ℝ → ℂ` is an injective ring homomorphism. -/
theorem ofReal_injective : Function.Injective (Complex.ofRealHom : ℝ →+* ℂ) :=
  Complex.ofReal_injective

end MeaningDimension.ComplexNumbers
