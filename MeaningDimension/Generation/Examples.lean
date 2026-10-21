import MeaningDimension.Generation.Embedding
import MeaningDimension.Generation.RingLanguage
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Real.Irrational

/-!
# The examples from the history of mathematics: ℕ → ℤ, ℚ → ℝ, ℝ → ℂ

Spec: `docs/mdg_spec.md`, J2, J4, MDG1(e)(g), MDG2, MDG3.

The language is the language of rings `ℒᵣ` (`0, 1, +, ·, =`), so ℂ carries no order. Each natural
inclusion is an embedding of `ℒᵣ`-structures, and each step flips an existential sentence from
false to true, so each is a `ReversalStep`.

In the other direction, `ℂ → ℝ`, the sentence `∼sentenceC` flips from false to true, but there is
no embedding of ℂ into ℝ: it would carry the true existential sentence `sentenceC` of ℂ to ℝ
(MDG1(b)). So flipping a truth value is not enough for a `ReversalStep` (MDG3).

Along `ℝ → ℂ`, the universal sentence `∼sentenceC` flips from true to false (MDG1(e)): an
embedding keeps quantifier-free and existential facts, not universal ones. Restricted to the old
domain ℝ, `∼sentenceC` stays true in ℂ (MDG1(f)(g)). Both readings hold in ℂ at once: the
restricted sentence is true and the unrestricted one is false.
-/

namespace MeaningDimension.Generation

open FFL FFL.FirstOrder

/-! ## Embeddings of `ℒᵣ`-structures -/

/-- An injective map that preserves `0, 1, +, ·` is an embedding of `ℒᵣ`-structures. -/
def ringEmbedding {M M' : Type*} [Zero M] [One M] [Add M] [Mul M] [Zero M'] [One M'] [Add M']
    [Mul M'] (f : M → M') (hinj : Function.Injective f) (h0 : f 0 = 0) (h1 : f 1 = 1)
    (hadd : ∀ a b, f (a + b) = f a + f b) (hmul : ∀ a b, f (a * b) = f a * f b) :
    M ↪ₛ[ℒᵣ] M' where
  toFun := f
  func' := fun {_} F v ↦ by
    cases F
    · exact h0
    · exact h1
    · exact hadd (v 0) (v 1)
    · exact hmul (v 0) (v 1)
  rel' := fun {_} R v ↦ by
    cases R
    exact fun h ↦ congrArg f h
  rel_inv' := fun {_} R v ↦ by
    cases R
    exact fun h ↦ hinj h
  toFun_inj := hinj

/-- The inclusion `ℕ → ℤ`. -/
def natInt : ℕ ↪ₛ[ℒᵣ] ℤ :=
  ringEmbedding (Nat.cast : ℕ → ℤ) Nat.cast_injective Nat.cast_zero Nat.cast_one Nat.cast_add
    Nat.cast_mul

/-- The inclusion `ℚ → ℝ`. -/
noncomputable def ratReal : ℚ ↪ₛ[ℒᵣ] ℝ :=
  ringEmbedding (Rat.cast : ℚ → ℝ) Rat.cast_injective Rat.cast_zero Rat.cast_one Rat.cast_add
    Rat.cast_mul

/-- The inclusion `ℝ → ℂ`. -/
noncomputable def realComplex : ℝ ↪ₛ[ℒᵣ] ℂ :=
  ringEmbedding (Complex.ofReal : ℝ → ℂ) Complex.ofReal_injective Complex.ofReal_zero
    Complex.ofReal_one Complex.ofReal_add Complex.ofReal_mul

/-! ## The sentences -/

/-- `∃x (x + 5 = 3)`. -/
noncomputable def sentenceZ : Sentence ℒᵣ := “∃ x, x + 5 = 3”

/-- `∃x (x · x = 2)`. -/
noncomputable def sentenceR : Sentence ℒᵣ := “∃ x, x * x = 2”

/-- `∃x (x · x + 1 = 0)`. -/
noncomputable def sentenceC : Sentence ℒᵣ := “∃ x, x * x + 1 = 0”

theorem numeral_eq_cast {M : Type*} [AddMonoidWithOne M] [Mul M] [LT M] :
    ∀ n : ℕ, (ORingStructure.numeral n : M) = n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [ORingStructure.numeral, numeral_eq_cast (n + 1)]
    exact (Nat.cast_succ (n + 1)).symm

theorem sentenceZ_isExistential : IsExistential sentenceZ :=
  .ex (.of_open rfl)

theorem sentenceR_isExistential : IsExistential sentenceR :=
  .ex (.of_open rfl)

theorem sentenceC_isExistential : IsExistential sentenceC :=
  .ex (.of_open rfl)

/-- `∼sentenceC` (`∀x (x · x + 1 ≠ 0)`) is universal. -/
theorem neg_sentenceC_isUniversal : IsUniversal (∼sentenceC) :=
  .all (.of_open rfl)

/-! ## MDG2 -/

theorem nat_not_models_sentenceZ : ¬ ℕ↓[ℒᵣ] ⊧ sentenceZ := by
  simp [sentenceZ, models_iff]

theorem int_models_sentenceZ : ℤ↓[ℒᵣ] ⊧ sentenceZ := by
  simp [sentenceZ, models_iff, numeral_eq_cast]
  exact ⟨-2, by norm_num⟩

theorem rat_not_models_sentenceR : ¬ ℚ↓[ℒᵣ] ⊧ sentenceR := by
  simp [sentenceR, models_iff, numeral_eq_cast]
  intro q hq
  have h2 : (q : ℝ) * q = 2 := by exact_mod_cast hq
  have h3 : Real.sqrt 2 = |(q : ℝ)| := by rw [← h2, Real.sqrt_mul_self_eq_abs]
  exact irrational_sqrt_two ⟨|q|, by rw [Rat.cast_abs, h3]⟩

theorem real_models_sentenceR : ℝ↓[ℒᵣ] ⊧ sentenceR := by
  simp [sentenceR, models_iff, numeral_eq_cast]
  exact ⟨Real.sqrt 2, Real.mul_self_sqrt (by norm_num)⟩

theorem real_not_models_sentenceC : ¬ ℝ↓[ℒᵣ] ⊧ sentenceC := by
  simp [sentenceC, models_iff, numeral_eq_cast]
  intro x h
  nlinarith [mul_self_nonneg x]

theorem complex_models_sentenceC : ℂ↓[ℒᵣ] ⊧ sentenceC := by
  simp [sentenceC, models_iff]
  exact ⟨Complex.I, by simp⟩

/-- MDG2(a). -/
theorem reversalStep_nat_int : ReversalStep ℒᵣ ℕ ℤ :=
  ⟨⟨natInt⟩, sentenceZ, Semantics.Not.models_not.mpr nat_not_models_sentenceZ,
    int_models_sentenceZ⟩

/-- MDG2(b). -/
theorem reversalStep_rat_real : ReversalStep ℒᵣ ℚ ℝ :=
  ⟨⟨ratReal⟩, sentenceR, Semantics.Not.models_not.mpr rat_not_models_sentenceR,
    real_models_sentenceR⟩

/-- MDG2(c). -/
theorem reversalStep_real_complex : ReversalStep ℒᵣ ℝ ℂ :=
  ⟨⟨realComplex⟩, sentenceC, Semantics.Not.models_not.mpr real_not_models_sentenceC,
    complex_models_sentenceC⟩

/-- MDG1(e): along `ℝ → ℂ`, the universal sentence `∼sentenceC` flips from true to false. -/
theorem neg_sentenceC_true_false :
    ℝ↓[ℒᵣ] ⊧ ∼sentenceC ∧ ℂ↓[ℒᵣ] ⊧ ∼(∼sentenceC) :=
  ⟨Semantics.Not.models_not.mpr real_not_models_sentenceC, by
    simpa using complex_models_sentenceC⟩

/-- MDG1(g): in ℂ, `∼sentenceC` restricted to the old domain ℝ is true, and `∼sentenceC` itself
is false. -/
theorem realComplex_restricted_unrestricted :
    EvalOn ℒᵣ (Set.range realComplex) (∼sentenceC) ![] Empty.elim ∧ ℂ↓[ℒᵣ] ⊧ sentenceC :=
  ⟨(models_iff_evalOn realComplex _).mp (Semantics.Not.models_not.mpr real_not_models_sentenceC),
    complex_models_sentenceC⟩

/-! ## MDG3 -/

/-- MDG3: there is no embedding of ℂ into ℝ. -/
theorem isEmpty_complex_real : IsEmpty (ℂ ↪ₛ[ℒᵣ] ℝ) :=
  ⟨fun Θ ↦ real_not_models_sentenceC
    (models_of_isExistential Θ sentenceC_isExistential complex_models_sentenceC)⟩

/-- MDG3: `∼sentenceC` flips from ℂ to ℝ. -/
theorem flips_complex_real : Flips ℒᵣ ℂ ℝ (∼sentenceC) :=
  ⟨by simpa using complex_models_sentenceC,
    Semantics.Not.models_not.mpr real_not_models_sentenceC⟩

/-- MDG3: the step `ℂ → ℝ` is not a `ReversalStep`, although a sentence flips. -/
theorem not_reversalStep_complex_real : ¬ ReversalStep ℒᵣ ℂ ℝ := fun ⟨⟨Θ⟩, _⟩ ↦
  isEmpty_complex_real.false Θ

end MeaningDimension.Generation
