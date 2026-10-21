import MeaningDimension

/-!
# Specification tests for G5 (the next stage depends on the presentation)

Each `example` in the first half is transcribed from `docs/presentation_spec.md` §3, not from the
implementation. If an implementation changes its statement, the corresponding `example` stops
type-checking.

The second half instantiates the theorems at `𝗜𝚺₁` and `𝗣𝗔` to check that their hypotheses are
satisfiable (the theorems are not vacuous).
-/

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open MeaningDimension.Godel

section Spec

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-! ## §2 definitions -/

-- `ρ_T` is `□_α(¬Con_α)`.
example : proofOfIncon T = T.standardProvability (∼T.consistent.val) := rfl

-- `Con_β` is the consistency statement built from `β`.
example : twistedCon T = (@Theory.consistent ℒₒᵣ _ _ T (twisted T)).val := rfl

-- `β`'s defining formula is `α(x) ∨ ghostCh(x)`.
example : (twisted T).ch = T.Δ₁ch ⋎ ghostCh T := twisted_ch T

-- `nextWith T d` is `T ∪ {Con_d}`; for `α` it is Foundation's `T ∪ T.Con`.
example : nextWith T inferInstance = T ∪ T.Con := rfl
example : nextWith T (twisted T) = T ∪ {twistedCon T} := rfl

/-! ## G5.1 -/

noncomputable example : T.Δ₁ := twisted T

-- `β` defines exactly the axioms of `T` in `ℕ`.
example (σ : ArithmeticSentence) :
    (⌜σ⌝ : ℕ) ∈ @Theory.Δ₁Class ℕ _ ℒₒᵣ _ _ T (twisted T) ↔ σ ∈ T :=
  @Bootstrapping.Δ₁Class.mem_iff ℕ _ _ ℒₒᵣ _ _ T (twisted T) σ

/-! ## G5.2 -/

example : 𝗜𝚺₁ ⊢ proofOfIncon T 🡒 twistedProvability T ⊥ := provable_incon_imp_twisted_bot T

/-! ## G5.3 -/

example : 𝗜𝚺₁ ⊢ twistedCon T 🡒 T.consistent.val := twistedCon_imp_con T
example : T ∪ {twistedCon T} ⊢ T.consistent.val := provable_con_of_twistedCon T

/-! ## G5.4 -/

example : T ∪ T.Con ⊬ twistedCon T := not_provable_twistedCon T

/-! ## G5.5 -/

example : T ∪ T.Con ⪱ T ∪ {twistedCon T} := strict_twisted T
example : ¬ (T ∪ T.Con ≊ T ∪ {twistedCon T}) := not_equiv_twisted T

/-! ## G5.6 -/

example : ∃ d₁ d₂ : T.Δ₁, ¬ (nextWith T d₁ ≊ nextWith T d₂) := exists_presentations_not_equiv T
example (F : ArithmeticTheory → ArithmeticTheory) : ¬ ∀ d : T.Δ₁, F T ≊ nextWith T d :=
  not_function_of_theory T F

end Spec

/-! ## Non-vacuity: the hypotheses hold for `𝗜𝚺₁` and `𝗣𝗔` -/

example : 𝗜𝚺₁ ∪ (𝗜𝚺₁ : ArithmeticTheory).Con ⪱ 𝗜𝚺₁ ∪ {twistedCon 𝗜𝚺₁} := strict_twisted 𝗜𝚺₁

example (F : ArithmeticTheory → ArithmeticTheory) :
    ¬ ∀ d : (𝗜𝚺₁ : ArithmeticTheory).Δ₁, F 𝗜𝚺₁ ≊ nextWith 𝗜𝚺₁ d :=
  not_function_of_theory 𝗜𝚺₁ F

example : 𝗣𝗔 ∪ (𝗣𝗔 : ArithmeticTheory).Con ⪱ 𝗣𝗔 ∪ {twistedCon 𝗣𝗔} := strict_twisted 𝗣𝗔

example : 𝗣𝗔 ∪ (𝗣𝗔 : ArithmeticTheory).Con ⊬ twistedCon 𝗣𝗔 := not_provable_twistedCon 𝗣𝗔

example (F : ArithmeticTheory → ArithmeticTheory) :
    ¬ ∀ d : (𝗣𝗔 : ArithmeticTheory).Δ₁, F 𝗣𝗔 ≊ nextWith 𝗣𝗔 d :=
  not_function_of_theory 𝗣𝗔 F
