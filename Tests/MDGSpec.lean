import MeaningDimension

/-!
# Specification tests for MDG (the reversal, undecided and refinement forms)

Each `example` in the first half is transcribed from `docs/mdg_spec.md` §2–§3, not from the
implementation. If an implementation changes its statement, the corresponding `example` stops
type-checking.

The second half instantiates the theorems (ACSI: `singletonMaking : Making ℕ`, the empty self, the
experiences `0`, `1`; Gödel: `𝗜𝚺₁` and `𝗣𝗔`) to check that their hypotheses are satisfiable.
-/

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open MeaningDimension.ACSI MeaningDimension.Godel
open MeaningDimension.Generation

section Spec

/-! ## §2 definitions -/

section Defs

variable (L : Language) (M M' : Type) [Nonempty M] [Nonempty M'] [Tarski.Structure L M]
  [Tarski.Structure L M']

example (σ : Sentence L) : Flips L M M' σ ↔ M↓[L] ⊧ ∼σ ∧ M'↓[L] ⊧ σ := Iff.rfl
example : ReversalStep L M M' ↔ Nonempty (M ↪ₛ[L] M') ∧ ∃ σ, Flips L M M' σ := Iff.rfl

example {ξ : Type} {n : ℕ} (φ : Semiformula L ξ n) (h : φ.Open) : IsExistential φ := .of_open h
example {ξ : Type} {n : ℕ} (φ : Semiformula L ξ (n + 1)) (h : IsExistential φ) :
    IsExistential (∃¹ φ) := .ex h
example {ξ : Type} {n : ℕ} (φ : Semiformula L ξ n) (h : φ.Open) : IsUniversal φ := .of_open h
example {ξ : Type} {n : ℕ} (φ : Semiformula L ξ (n + 1)) (h : IsUniversal φ) :
    IsUniversal (∀¹ φ) := .all h

-- `EvalOn` (J10): `Eval` with every quantifier restricted to `R`.
example {ξ : Type} {n : ℕ} (R : Set M') (b : Fin n → M') (ε : ξ → M') :
    EvalOn L R (⊤ : Semiformula L ξ n) b ε ↔ True := Iff.rfl
example {ξ : Type} {n : ℕ} (R : Set M') (b : Fin n → M') (ε : ξ → M') :
    EvalOn L R (⊥ : Semiformula L ξ n) b ε ↔ False := Iff.rfl
example {ξ : Type} {n k : ℕ} (R : Set M') (r : L.Rel k) (v : Fin k → Semiterm L ξ n)
    (b : Fin n → M') (ε : ξ → M') :
    EvalOn L R (Semiformula.rel r v) b ε ↔ Tarski.Structure.rel r fun i ↦ (v i).val b ε :=
  Iff.rfl
example {ξ : Type} {n k : ℕ} (R : Set M') (r : L.Rel k) (v : Fin k → Semiterm L ξ n)
    (b : Fin n → M') (ε : ξ → M') :
    EvalOn L R (Semiformula.nrel r v) b ε ↔ ¬ Tarski.Structure.rel r fun i ↦ (v i).val b ε :=
  Iff.rfl
example {ξ : Type} {n : ℕ} (R : Set M') (φ ψ : Semiformula L ξ n) (b : Fin n → M')
    (ε : ξ → M') : EvalOn L R (φ ⋏ ψ) b ε ↔ EvalOn L R φ b ε ∧ EvalOn L R ψ b ε := Iff.rfl
example {ξ : Type} {n : ℕ} (R : Set M') (φ ψ : Semiformula L ξ n) (b : Fin n → M')
    (ε : ξ → M') : EvalOn L R (φ ⋎ ψ) b ε ↔ EvalOn L R φ b ε ∨ EvalOn L R ψ b ε := Iff.rfl
example {ξ : Type} {n : ℕ} (R : Set M') (φ : Semiformula L ξ (n + 1)) (b : Fin n → M')
    (ε : ξ → M') : EvalOn L R (∀¹ φ) b ε ↔ ∀ x ∈ R, EvalOn L R φ (x :> b) ε := Iff.rfl
example {ξ : Type} {n : ℕ} (R : Set M') (φ : Semiformula L ξ (n + 1)) (b : Fin n → M')
    (ε : ξ → M') : EvalOn L R (∃¹ φ) b ε ↔ ∃ x ∈ R, EvalOn L R φ (x :> b) ε := Iff.rfl

variable {D : Type} (F F' : Framework D)

example : Refines F F' ↔ F.preds ⊆ F'.preds := Iff.rfl
example (x y : D) : DistinctionFlip F F' x y ↔ F.Same x y ∧ ¬ F'.Same x y := Iff.rfl
example : RefineStep F F' ↔ Refines F F' ∧ ∃ x y, DistinctionFlip F F' x y := Iff.rfl

variable (T T' : ArithmeticTheory) (σ : ArithmeticSentence)

example : TheoryFlip T T' σ ↔ T ⊢ ∼σ ∧ T' ⊢ σ := Iff.rfl
example : Settles T T' σ ↔ T ⪯ T' ∧ T ⊬ σ ∧ T ⊬ ∼σ ∧ T' ⊢ σ := Iff.rfl
example : (provFramework T).preds = {P | ∃ θ, P = fun σ ↦ T ⊢ σ 🡘 θ} := rfl
example [T.Δ₁] (n : ℕ) :
    (ascentFramework T n).preds = {P | ∃ k ≤ n, P = fun σ ↦ (ascent T k).theory ⊢ σ} := rfl

end Defs

-- `ℒᵣ` (J2): `0, 1, +, ·` and `=` only, with the standard structure.
example (k : ℕ) : Language.Func ℒᵣ k = Language.ORing.Func k := rfl
example {k : ℕ} (r : Language.Rel ℒᵣ k) : k = 2 := by cases r; rfl
example (a b : ℂ) : Tarski.Structure.func (L := ℒᵣ) Language.Add.add ![a, b] = a + b := rfl
example (a b : ℂ) : Tarski.Structure.func (L := ℒᵣ) Language.Mul.mul ![a, b] = a * b := rfl
example (v : Fin 0 → ℂ) : Tarski.Structure.func (L := ℒᵣ) Language.Zero.zero v = 0 := rfl
example (v : Fin 0 → ℂ) : Tarski.Structure.func (L := ℒᵣ) Language.One.one v = 1 := rfl
example (a b : ℂ) : Tarski.Structure.rel (L := ℒᵣ) Language.Eq.eq ![a, b] ↔ a = b := Iff.rfl

example : sentenceZ = (“∃ x, x + 5 = 3” : Sentence ℒᵣ) := rfl
example : sentenceR = (“∃ x, x * x = 2” : Sentence ℒᵣ) := rfl
example : sentenceC = (“∃ x, x * x + 1 = 0” : Sentence ℒᵣ) := rfl
example (x : ℕ) : natInt x = (x : ℤ) := rfl
example (x : ℚ) : ratReal x = (x : ℝ) := rfl
example (x : ℝ) : realComplex x = (x : ℂ) := rfl
example (x : Z2) : conj x = star x := rfl
example : ringFramework.preds = {P | ∃ φ, OrderFree φ ∧ P = definable φ} := rfl
example : orderedFramework.preds = {P | ∃ φ, P = definable φ} := rfl
example (φ : Semisentence ℒₒᵣ 1) (x : Z2) : definable φ x ↔ φ.Eval ![x] Empty.elim := Iff.rfl

/-! ## MDG1 -/

section MDG1

variable {L : Language} {M M' : Type} [Nonempty M] [Nonempty M'] [Tarski.Structure L M]
  [Tarski.Structure L M'] (Θ : M ↪ₛ[L] M') {ξ : Type} {n : ℕ} (e : Fin n → M) (ε : ξ → M)

example {φ : Semiformula L ξ n} (h : φ.Open) : φ.Eval e ε ↔ φ.Eval (Θ ∘ e) (Θ ∘ ε) :=
  eval_iff_of_open Θ h e ε
example {φ : Semiformula L ξ n} (h : IsExistential φ) :
    φ.Eval e ε → φ.Eval (Θ ∘ e) (Θ ∘ ε) :=
  eval_of_isExistential Θ h e ε
example {φ : Semiformula L ξ n} (h : IsUniversal φ) :
    φ.Eval (Θ ∘ e) (Θ ∘ ε) → φ.Eval e ε :=
  eval_of_isUniversal Θ h e ε
example {σ : Sentence L} (h : IsExistential σ) : ¬ (M↓[L] ⊧ σ ∧ M'↓[L] ⊧ ∼σ) :=
  not_true_false_of_isExistential Θ h
example {σ : Sentence L} (h : IsUniversal σ) : ¬ Flips L M M' σ :=
  not_flips_of_isUniversal Θ h
-- (f)
example (φ : Semiformula L ξ n) :
    φ.Eval e ε ↔ EvalOn L (Set.range Θ) φ (Θ ∘ e) (Θ ∘ ε) :=
  eval_iff_evalOn Θ φ e ε
example (σ : Sentence L) : M↓[L] ⊧ σ ↔ EvalOn L (Set.range Θ) σ ![] Empty.elim :=
  models_iff_evalOn Θ σ

end MDG1

-- MDG1(e)
example : IsUniversal (∼sentenceC) := neg_sentenceC_isUniversal
example : ℝ↓[ℒᵣ] ⊧ ∼sentenceC ∧ ℂ↓[ℒᵣ] ⊧ ∼(∼sentenceC) := neg_sentenceC_true_false
-- MDG1(g)
example : EvalOn ℒᵣ (Set.range realComplex) (∼sentenceC) ![] Empty.elim ∧ ℂ↓[ℒᵣ] ⊧ sentenceC :=
  realComplex_restricted_unrestricted

/-! ## MDG2 -/

example : ¬ ℕ↓[ℒᵣ] ⊧ sentenceZ := nat_not_models_sentenceZ
example : ℤ↓[ℒᵣ] ⊧ sentenceZ := int_models_sentenceZ
example : ReversalStep ℒᵣ ℕ ℤ := reversalStep_nat_int
example : ¬ ℚ↓[ℒᵣ] ⊧ sentenceR := rat_not_models_sentenceR
example : ℝ↓[ℒᵣ] ⊧ sentenceR := real_models_sentenceR
example : ReversalStep ℒᵣ ℚ ℝ := reversalStep_rat_real
example : ¬ ℝ↓[ℒᵣ] ⊧ sentenceC := real_not_models_sentenceC
example : ℂ↓[ℒᵣ] ⊧ sentenceC := complex_models_sentenceC
example : ReversalStep ℒᵣ ℝ ℂ := reversalStep_real_complex
-- (d)
example : IsExistential sentenceZ := sentenceZ_isExistential
example : IsExistential sentenceR := sentenceR_isExistential
example : IsExistential sentenceC := sentenceC_isExistential

/-! ## MDG3 -/

example : IsEmpty (ℂ ↪ₛ[ℒᵣ] ℝ) := isEmpty_complex_real
example : Flips ℒᵣ ℂ ℝ (∼sentenceC) := flips_complex_real
example : ¬ ReversalStep ℒᵣ ℂ ℝ := not_reversalStep_complex_real

/-! ## MDG4 -/

example {T T' : ArithmeticTheory} [T ⪯ T'] [Consistent T'] (σ : ArithmeticSentence) :
    ¬ TheoryFlip T T' σ :=
  not_theoryFlip σ

section Ascent

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] (n : ℕ)

example (σ : ArithmeticSentence) :
    ¬ TheoryFlip (ascent T n).theory (ascent T (n + 1)).theory σ :=
  ascent_not_theoryFlip T n σ
example : Settles (ascent T n).theory (ascent T (n + 1)).theory
    (ascent T n).theory.consistent.val :=
  ascent_settles T n

end Ascent

/-! ## MDG5 -/

example {T T' : ArithmeticTheory} (h : T ⪯ T') {φ ψ : ArithmeticSentence} :
    T ⊢ φ 🡘 ψ → T' ⊢ φ 🡘 ψ :=
  provable_iff_mono h
example (T : ArithmeticTheory) (φ ψ : ArithmeticSentence) :
    (provFramework T).Same φ ψ ↔ T ⊢ φ 🡘 ψ :=
  provFramework_same_iff T φ ψ
example {T T' : ArithmeticTheory} (h : T ⪯ T') (φ ψ : ArithmeticSentence) :
    ¬ DistinctionFlip (provFramework T) (provFramework T') φ ψ :=
  not_distinctionFlip_provFramework h φ ψ
example {T T' : ArithmeticTheory} (h : T ⪯ T') :
    ¬ RefineStep (provFramework T) (provFramework T') :=
  not_refineStep_provFramework h
example (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) :
    ¬ RefineStep (provFramework (ascent T n).theory) (provFramework (ascent T (n + 1)).theory) :=
  ascent_not_refineStep T n
-- (e)
example (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] (n : ℕ) :
    RefineStep (ascentFramework T n) (ascentFramework T (n + 1)) :=
  ascent_refineStep T n
-- (f)
section MDG5f

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] (n : ℕ)

example {σ : ArithmeticSentence} (h : Settles (ascent T n).theory (ascent T (n + 1)).theory σ) :
    DistinctionFlip (ascentFramework T n) (ascentFramework T (n + 1)) σ (∼σ) :=
  distinctionFlip_of_settles T n h
example {φ ψ : ArithmeticSentence}
    (h : DistinctionFlip (ascentFramework T n) (ascentFramework T (n + 1)) φ ψ) :
    Settles (ascent T n).theory (ascent T (n + 1)).theory φ ∨
      Settles (ascent T n).theory (ascent T (n + 1)).theory ψ :=
  settles_of_distinctionFlip T n h
example : RefineStep (ascentFramework T n) (ascentFramework T (n + 1)) ↔
    ∃ σ, Settles (ascent T n).theory (ascent T (n + 1)).theory σ :=
  ascent_refineStep_iff T n

end MDG5f

/-! ## MDG6 -/

section MDG6

variable {E : Type} (M : Making E) (S : Self E) (e : E)

example {e' : E} (h : S.Classifies e') : (M.incorporate S e).Classifies e' :=
  classifies_incorporate_of_classifies M h e
example : Refines (evaluated S) (evaluated (M.incorporate S e)) :=
  refines_evaluated_incorporate M S e
example {e' : E} (he : S.IsNew e) (he' : S.IsNew e') (hout : e' ∉ M.generate S e) :
    RefineStep (evaluated S) (evaluated (M.incorporate S e)) :=
  refineStep_evaluated_incorporate M he he' hout
example {e' : E} (he : S.IsNew e) (he' : S.IsNew e') (hout : e' ∉ M.generate S e) :
    DistinctionFlip (evaluated S) (evaluated (M.incorporate S e)) (.inr e) (.inr e') :=
  distinctionFlip_evaluated_incorporate M he he' hout
-- (d)
example (x y : Entity E) (h : (evaluated (M.incorporate S e)).Same x y) : (evaluated S).Same x y :=
  same_of_same_evaluated_incorporate M S e h
example (h : List E) : Refines (evaluated S) (evaluated (M.run S h)) :=
  refines_evaluated_run M S h
example (h : List E) (x y : Entity E) (hs : (evaluated (M.run S h)).Same x y) :
    (evaluated S).Same x y :=
  same_of_same_evaluated_run M S h hs

end MDG6

/-! ## MDG7 -/

example {k : ℕ} (f : Language.Func ℒₒᵣ k) (v : Fin k → Z2) :
    conj (Tarski.Structure.func f v) = Tarski.Structure.func f (conj ∘ v) :=
  conj_func f v
example : (0 : Z2) < Zsqrtd.sqrtd ∧ ¬ conj 0 < conj Zsqrtd.sqrtd := conj_not_preserves_lt
example {ξ : Type} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) (h : OrderFree φ) (b : Fin n → Z2)
    (ε : ξ → Z2) : φ.Eval b ε ↔ φ.Eval (conj ∘ b) (conj ∘ ε) :=
  eval_equiv_of_orderFree conj conj_func φ h b ε
example : ringFramework.Same Zsqrtd.sqrtd (-Zsqrtd.sqrtd) := ringFramework_same
example : ¬ orderedFramework.Same Zsqrtd.sqrtd (-Zsqrtd.sqrtd) := orderedFramework_not_same
example : RefineStep ringFramework orderedFramework := refineStep_ring_ordered

end Spec

/-! ## Non-vacuity -/

section NonVacuity

theorem mdg_empty_isNew (e : ℕ) : (Self.empty : Self ℕ).IsNew e :=
  fun ⟨_, hc, _⟩ ↦ List.not_mem_nil hc

-- MDG6(c): incorporation of `0` by `singletonMaking` into the empty self is a step in the
-- refinement form; `0` and `1` are told apart only afterwards.
example : RefineStep (evaluated (Self.empty : Self ℕ))
    (evaluated ((singletonMaking : Making ℕ).incorporate Self.empty 0)) :=
  refineStep_evaluated_incorporate _ (mdg_empty_isNew 0) (mdg_empty_isNew 1)
    (by simp [singletonMaking])

example : DistinctionFlip (evaluated (Self.empty : Self ℕ))
    (evaluated ((singletonMaking : Making ℕ).incorporate Self.empty 0)) (.inr 0) (.inr 1) :=
  distinctionFlip_evaluated_incorporate _ (mdg_empty_isNew 0) (mdg_empty_isNew 1)
    (by simp [singletonMaking])

-- MDG4(b)(c), MDG5(d)(e)(f) at `𝗜𝚺₁` and `𝗣𝗔`.
example (n : ℕ) (σ : ArithmeticSentence) :
    ¬ TheoryFlip (ascent 𝗣𝗔 n).theory (ascent 𝗣𝗔 (n + 1)).theory σ :=
  ascent_not_theoryFlip 𝗣𝗔 n σ
example (n : ℕ) : Settles (ascent 𝗣𝗔 n).theory (ascent 𝗣𝗔 (n + 1)).theory
    (ascent 𝗣𝗔 n).theory.consistent.val :=
  ascent_settles 𝗣𝗔 n
example (n : ℕ) (σ : ArithmeticSentence) :
    ¬ TheoryFlip (ascent 𝗜𝚺₁ n).theory (ascent 𝗜𝚺₁ (n + 1)).theory σ :=
  ascent_not_theoryFlip 𝗜𝚺₁ n σ
example (n : ℕ) : Settles (ascent 𝗜𝚺₁ n).theory (ascent 𝗜𝚺₁ (n + 1)).theory
    (ascent 𝗜𝚺₁ n).theory.consistent.val :=
  ascent_settles 𝗜𝚺₁ n
example (n : ℕ) :
    ¬ RefineStep (provFramework (ascent 𝗣𝗔 n).theory)
      (provFramework (ascent 𝗣𝗔 (n + 1)).theory) :=
  ascent_not_refineStep 𝗣𝗔 n
example (n : ℕ) :
    ¬ RefineStep (provFramework (ascent 𝗜𝚺₁ n).theory)
      (provFramework (ascent 𝗜𝚺₁ (n + 1)).theory) :=
  ascent_not_refineStep 𝗜𝚺₁ n
example (n : ℕ) : RefineStep (ascentFramework 𝗣𝗔 n) (ascentFramework 𝗣𝗔 (n + 1)) :=
  ascent_refineStep 𝗣𝗔 n
example (n : ℕ) : RefineStep (ascentFramework 𝗜𝚺₁ n) (ascentFramework 𝗜𝚺₁ (n + 1)) :=
  ascent_refineStep 𝗜𝚺₁ n
example (n : ℕ) : ∃ σ, Settles (ascent 𝗣𝗔 n).theory (ascent 𝗣𝗔 (n + 1)).theory σ :=
  (ascent_refineStep_iff 𝗣𝗔 n).mp (ascent_refineStep 𝗣𝗔 n)
example (n : ℕ) : ∃ σ, Settles (ascent 𝗜𝚺₁ n).theory (ascent 𝗜𝚺₁ (n + 1)).theory σ :=
  (ascent_refineStep_iff 𝗜𝚺₁ n).mp (ascent_refineStep 𝗜𝚺₁ n)

end NonVacuity

/-! ## MDG8 (spec §7): Kappa's packing -/

section MDG8

open MeaningDimension.Generation.Kappa

/-! ### §7.2 definitions -/

-- `ℒₖ`: `⊕`, `⌜n⌝`, `=`. `ℒ⊕`: `⊕`, `=` (J12).
example : Language.Func ℒₖ 2 = KappaFunc 2 := rfl
example : Language.Func ℒₖ 0 = KappaFunc 0 := rfl
example (n : ℕ) : Language.Func ℒₖ 0 := KappaFunc.num n
example : Language.Func ℒ⊕ 2 = PlusFunc 2 := rfl
example {k : ℕ} (f : Language.Func ℒ⊕ k) : k = 2 := by cases f; rfl
example {k : ℕ} (r : Language.Rel ℒₖ k) : k = 2 := by cases r; rfl
example {k : ℕ} (r : Language.Rel ℒ⊕ k) : k = 2 := by cases r; rfl

-- The structures.
example (a b : ℚ) : addModel.func (KappaFunc.plus : Language.Func ℒₖ 2) ![a, b] = a + b := rfl
example (n : ℕ) (v : Fin 0 → ℚ) : addModel.func (KappaFunc.num n : Language.Func ℒₖ 0) v = n := rfl
example (a b : ℚ) : addModel.rel (RingRel.eq : Language.Rel ℒₖ 2) ![a, b] ↔ a = b := Iff.rfl
example (w a b : ℚ) : (packModel w).func (KappaFunc.plus : Language.Func ℒₖ 2) ![a, b] = a + b + w := rfl
example (w : ℚ) (n : ℕ) (v : Fin 0 → ℚ) :
    (packModel w).func (KappaFunc.num n : Language.Func ℒₖ 0) v = n := rfl
example (w a b : ℚ) : (packModel w).rel (RingRel.eq : Language.Rel ℒₖ 2) ![a, b] ↔ a = b := Iff.rfl
example (a b : ℚ) : addModelP.func (PlusFunc.plus : Language.Func ℒ⊕ 2) ![a, b] = a + b := rfl
example (w a b : ℚ) : (packModelP w).func (PlusFunc.plus : Language.Func ℒ⊕ 2) ![a, b] = a + b + w := rfl
example (w a b : ℚ) : (packModelP w).rel (RingRel.eq : Language.Rel ℒ⊕ 2) ![a, b] ↔ a = b := Iff.rfl
example (w a b : ℚ) : (packRing w).func Language.Add.add ![a, b] = a + b + w := rfl
example (w a b : ℚ) : (packRing w).func Language.Mul.mul ![a, b] = a * b := rfl
example (w : ℚ) (v : Fin 0 → ℚ) : (packRing w).func Language.Zero.zero v = 0 := rfl
example (w : ℚ) (v : Fin 0 → ℚ) : (packRing w).func Language.One.one v = 1 := rfl
example (w a b : ℚ) : (packRing w).rel Language.Eq.eq ![a, b] ↔ a = b := Iff.rfl

-- Instances (J11).
example (w : ℚ) : Pack w = ℚ := rfl
example : (inferInstance : Tarski.Structure ℒₖ ℚ) = addModel := rfl
example : (inferInstance : Tarski.Structure ℒ⊕ ℚ) = addModelP := rfl
example : (inferInstance : Tarski.Structure ℒᵣ ℚ) = ringModel ℚ := rfl
example (w : ℚ) : (inferInstance : Tarski.Structure ℒₖ (Pack w)) = packModel w := rfl
example (w : ℚ) : (inferInstance : Tarski.Structure ℒ⊕ (Pack w)) = packModelP w := rfl
example (w : ℚ) : (inferInstance : Tarski.Structure ℒᵣ (Pack w)) = packRing w := rfl

-- The sentences (J13).
example (n : ℕ) : num n = Semiterm.func (KappaFunc.num n : Language.Func ℒₖ 0) ![] := rfl
example : four = Semiformula.rel (RingRel.eq : Language.Rel ℒₖ 2)
    ![Semiterm.func (KappaFunc.plus : Language.Func ℒₖ 2) ![num 2, num 2], num 4] := rfl
example : five = Semiformula.rel (RingRel.eq : Language.Rel ℒₖ 2)
    ![Semiterm.func (KappaFunc.plus : Language.Func ℒₖ 2) ![num 2, num 2], num 5] := rfl
example : fourR = (“2 + 2 = 4” : Sentence ℒᵣ) := rfl
example : zeroR = (“0 + 0 = 0” : Sentence ℒᵣ) := rfl

/-! ### MDG8 -/

-- (a)
example : ℚ↓[ℒₖ] ⊧ four := rat_models_four
example : ℚ↓[ℒₖ] ⊧ ∼five := rat_models_not_five
example {w : ℚ} (hw : w ≠ 0) : (Pack w)↓[ℒₖ] ⊧ ∼four := pack_models_not_four hw
example : (Pack 1)↓[ℒₖ] ⊧ five := pack_one_models_five

-- (b)
example : packModel 0 = addModel := packModel_zero
example : packModelP 0 = addModelP := packModelP_zero
example : packRing 0 = ringModel ℚ := packRing_zero
example (x : ℚ) : idPack x = x := rfl
example : Function.Surjective idPack := idPack_surjective

-- (c)
section Lemma
variable {L : Language} {M M' : Type} [Nonempty M] [Nonempty M'] [Tarski.Structure L M]
  [Tarski.Structure L M']
example {σ : Sentence L} (hσ : σ.Open) (h : M↓[L] ⊧ σ) (h' : M'↓[L] ⊧ ∼σ) :
    IsEmpty (M ↪ₛ[L] M') := isEmpty_of_open hσ h h'
end Lemma
example {w : ℚ} (hw : w ≠ 0) : IsEmpty (ℚ ↪ₛ[ℒₖ] Pack w) := isEmpty_kappa hw
example {w : ℚ} (hw : w ≠ 0) : Flips ℒₖ ℚ (Pack w) (∼four) := flips_not_four hw
example : Flips ℒₖ ℚ (Pack 1) five := flips_five
example {w : ℚ} (hw : w ≠ 0) : ¬ ReversalStep ℒₖ ℚ (Pack w) := not_reversalStep_kappa hw

-- (d)
example (w x : ℚ) : shift w x = x - w := rfl
example (w : ℚ) : Function.Surjective (shift w) := shift_surjective w
section Lemma
variable {L : Language} {M M' : Type} [Nonempty M] [Nonempty M'] [Tarski.Structure L M]
  [Tarski.Structure L M']
example (Θ : M ↪ₛ[L] M') (hΘ : Function.Surjective Θ) (σ : Sentence L) :
    M↓[L] ⊧ σ ↔ M'↓[L] ⊧ σ := models_iff_of_surjective Θ hΘ σ
end Lemma
example (w : ℚ) (σ : Sentence ℒ⊕) : ℚ↓[ℒ⊕] ⊧ σ ↔ (Pack w)↓[ℒ⊕] ⊧ σ := models_iff_plus w σ
example (w : ℚ) : ¬ ReversalStep ℒ⊕ ℚ (Pack w) := not_reversalStep_plus w

-- (e)
example (w : ℚ) : (Pack w)↓[ℒᵣ] ⊧ fourR := pack_models_fourR w
example : ℚ↓[ℒᵣ] ⊧ fourR := rat_models_fourR
example {w : ℚ} (hw : w ≠ 0) : IsEmpty (ℚ ↪ₛ[ℒᵣ] Pack w) := isEmpty_ring hw
example {w : ℚ} (hw : w ≠ 0) : Flips ℒᵣ ℚ (Pack w) (∼zeroR) := flips_not_zeroR hw
example {w : ℚ} (hw : w ≠ 0) : ¬ ReversalStep ℒᵣ ℚ (Pack w) := not_reversalStep_ring hw

/-! ### Non-vacuity: `w = 1` (Lakatos's numbers) and `w = -1/2` -/

example : (Pack 1)↓[ℒₖ] ⊧ ∼four := pack_models_not_four one_ne_zero
example : IsEmpty (ℚ ↪ₛ[ℒₖ] Pack 1) := isEmpty_kappa one_ne_zero
example : ¬ ReversalStep ℒₖ ℚ (Pack 1) := not_reversalStep_kappa one_ne_zero
example : Nonempty (ℚ ↪ₛ[ℒ⊕] Pack 1) := ⟨shift 1⟩
example : ¬ ReversalStep ℒ⊕ ℚ (Pack 1) := not_reversalStep_plus 1
example : (Pack 1)↓[ℒᵣ] ⊧ fourR := pack_models_fourR 1
example : ¬ ReversalStep ℒᵣ ℚ (Pack 1) := not_reversalStep_ring one_ne_zero

example : (Pack (-1/2))↓[ℒₖ] ⊧ ∼four := pack_models_not_four (by norm_num)
example : IsEmpty (ℚ ↪ₛ[ℒₖ] Pack (-1/2)) := isEmpty_kappa (by norm_num)
example : Flips ℒₖ ℚ (Pack (-1/2)) (∼four) := flips_not_four (by norm_num)
example : ¬ ReversalStep ℒₖ ℚ (Pack (-1/2)) := not_reversalStep_kappa (by norm_num)
example : ¬ ReversalStep ℒ⊕ ℚ (Pack (-1/2)) := not_reversalStep_plus (-1/2)
example : IsEmpty (ℚ ↪ₛ[ℒᵣ] Pack (-1/2)) := isEmpty_ring (by norm_num)
example : Flips ℒᵣ ℚ (Pack (-1/2)) (∼zeroR) := flips_not_zeroR (by norm_num)

end MDG8
