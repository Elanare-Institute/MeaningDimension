import MeaningDimension.Generation.Refinement
import Foundation.FirstOrder.Incompleteness.Examples
import Mathlib.NumberTheory.Zsqrtd.Basic

/-!
# A mathematical example of the refinement form: `√2` and `−√2` in `ℤ√2`

Spec: `docs/mdg_spec.md`, J6, J7, MDG7.

Conjugation `a + b√2 ↦ a − b√2` (Mathlib's `star` on `ℤ√2`) preserves `0, 1, +, ·`, so no formula
without `<` tells `√2` from `−√2` (`eval_equiv_of_orderFree`; the induction is that of Foundation's
`eval_iff_of_equiv`, restricted to formulas without `<`). With the order, `0 < x` tells them
apart. Hence the framework of the ordered ring refines the framework of the ring and tells apart
two elements the latter identified (`refineStep_ring_ordered`).

The frameworks use parameter-free formulas with one free variable (J7). With `√2` as a parameter,
the ring language already tells the two apart.
-/

namespace MeaningDimension.Generation

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic MeaningDimension.ACSI

/-! ## Formulas without `<` -/

/-- The relation symbol is `=`. -/
def IsEqRel : {k : ℕ} → Language.Rel ℒₒᵣ k → Prop
  | _, .eq => True
  | _, .lt => False

/-- No atomic formula of `φ` uses `<` (J6). -/
def OrderFree {ξ : Type*} : {n : ℕ} → Semiformula ℒₒᵣ ξ n → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel r _ => IsEqRel r
  | _, .nrel r _ => IsEqRel r
  | _, .and φ ψ => OrderFree φ ∧ OrderFree ψ
  | _, .or φ ψ => OrderFree φ ∧ OrderFree ψ
  | _, .all φ => OrderFree φ
  | _, .exs φ => OrderFree φ

section Invariance

variable {M M' : Type*} [ORingStructure M] [ORingStructure M'] {ξ : Type*} (I : M ≃ M')
  (hfunc : ∀ {k} (f : Language.Func ℒₒᵣ k) (v : Fin k → M),
    I (Tarski.Structure.func f v) = Tarski.Structure.func f (I ∘ v))
include hfunc

theorem val_equiv {n : ℕ} (b : Fin n → M) (ε : ξ → M) (t : Semiterm ℒₒᵣ ξ n) :
    I (t.val b ε) = t.val (I ∘ b) (I ∘ ε) := by
  induction t <;> simp [*, Function.comp_def]

/-- MDG7(b): a bijection that preserves `0, 1, +, ·` preserves the truth of every formula without
`<`. -/
theorem eval_equiv_of_orderFree : ∀ {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n), OrderFree φ →
    ∀ (b : Fin n → M) (ε : ξ → M), φ.Eval b ε ↔ φ.Eval (I ∘ b) (I ∘ ε)
  | _, .verum, _, _, _ => ⟨fun _ ↦ trivial, fun _ ↦ trivial⟩
  | _, .falsum, _, _, _ => ⟨fun h ↦ (h : False).elim, fun h ↦ (h : False).elim⟩
  | _, .rel r v, h, b, ε => by
    cases r
    · show (v 0).val b ε = (v 1).val b ε ↔ (v 0).val (I ∘ b) (I ∘ ε) = (v 1).val (I ∘ b) (I ∘ ε)
      rw [← val_equiv I hfunc, ← val_equiv I hfunc, I.injective.eq_iff]
    · exact h.elim
  | _, .nrel r v, h, b, ε => by
    cases r
    · show ¬ (v 0).val b ε = (v 1).val b ε ↔
        ¬ (v 0).val (I ∘ b) (I ∘ ε) = (v 1).val (I ∘ b) (I ∘ ε)
      rw [← val_equiv I hfunc, ← val_equiv I hfunc, I.injective.eq_iff]
    · exact h.elim
  | _, .and φ ψ, h, b, ε => by
    have h₁ := eval_equiv_of_orderFree φ h.1 b ε
    have h₂ := eval_equiv_of_orderFree ψ h.2 b ε
    exact and_congr h₁ h₂
  | _, .or φ ψ, h, b, ε => by
    have h₁ := eval_equiv_of_orderFree φ h.1 b ε
    have h₂ := eval_equiv_of_orderFree ψ h.2 b ε
    exact or_congr h₁ h₂
  | _, .all φ, h, b, ε => by
    show (∀ x, φ.Eval (x :> b) ε) ↔ (∀ y, φ.Eval (y :> (I ∘ b)) (I ∘ ε))
    have key : ∀ x, φ.Eval (x :> b) ε ↔ φ.Eval (I x :> (I ∘ b)) (I ∘ ε) := fun x ↦ by
      have e : (I ∘ (x :> b) : Fin _ → M') = I x :> (I ∘ b) := Matrix.comp_vecCons _ _ _
      rw [eval_equiv_of_orderFree φ h (x :> b) ε, e]
    constructor
    · intro hx y
      simpa using (key (I.symm y)).mp (hx _)
    · intro hy x
      exact (key x).mpr (hy _)
  | _, .exs φ, h, b, ε => by
    show (∃ x, φ.Eval (x :> b) ε) ↔ (∃ y, φ.Eval (y :> (I ∘ b)) (I ∘ ε))
    have key : ∀ x, φ.Eval (x :> b) ε ↔ φ.Eval (I x :> (I ∘ b)) (I ∘ ε) := fun x ↦ by
      have e : (I ∘ (x :> b) : Fin _ → M') = I x :> (I ∘ b) := Matrix.comp_vecCons _ _ _
      rw [eval_equiv_of_orderFree φ h (x :> b) ε, e]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨I x, (key x).mp hx⟩
    · rintro ⟨y, hy⟩
      exact ⟨I.symm y, (key _).mpr (by simpa using hy)⟩

end Invariance

/-! ## `ℤ√2` -/

/-- `ℤ√2`, with `2 : ℕ` so that Mathlib's order applies. -/
abbrev Z2 := ℤ√((2 : ℕ) : ℤ)

/-- Conjugation `a + b√2 ↦ a − b√2`. -/
def conj : Z2 ≃ Z2 := ⟨star, star, star_star, star_star⟩

/-- MDG7(a): conjugation preserves `0, 1, +, ·`. -/
theorem conj_func {k : ℕ} (f : Language.Func ℒₒᵣ k) (v : Fin k → Z2) :
    conj (Tarski.Structure.func f v) = Tarski.Structure.func f (conj ∘ v) := by
  cases f
  · exact star_zero _
  · exact star_one _
  · exact star_add (v 0) (v 1)
  · exact star_mul' (v 0) (v 1)

theorem conj_sqrtd : conj Zsqrtd.sqrtd = -Zsqrtd.sqrtd := by
  ext <;> simp [conj, Zsqrtd.re_star, Zsqrtd.im_star, Zsqrtd.re_neg, Zsqrtd.im_neg,
    Zsqrtd.re_sqrtd, Zsqrtd.im_sqrtd]

theorem zero_lt_sqrtd : (0 : Z2) < Zsqrtd.sqrtd := by
  show ¬ (Zsqrtd.sqrtd ≤ 0)
  decide

theorem not_zero_lt_neg_sqrtd : ¬ (0 : Z2) < -Zsqrtd.sqrtd := by
  show ¬ ¬ (-Zsqrtd.sqrtd ≤ 0)
  decide

/-- MDG7(a): conjugation does not preserve `<`. -/
theorem conj_not_preserves_lt :
    (0 : Z2) < Zsqrtd.sqrtd ∧ ¬ conj 0 < conj Zsqrtd.sqrtd := by
  refine ⟨zero_lt_sqrtd, ?_⟩
  rw [conj_sqrtd, show conj 0 = 0 from star_zero _]
  exact not_zero_lt_neg_sqrtd

/-- The predicate on `ℤ√2` defined by a parameter-free formula with one free variable. -/
def definable (φ : Semisentence ℒₒᵣ 1) : Z2 → Prop := fun x ↦ φ.Eval ![x] Empty.elim

/-- The framework of the ring: predicates defined by formulas without `<` (J7). -/
def ringFramework : Framework Z2 := ⟨{P | ∃ φ, OrderFree φ ∧ P = definable φ}⟩

/-- The framework of the ordered ring: predicates defined by any formula of `ℒₒᵣ` (J7). -/
def orderedFramework : Framework Z2 := ⟨{P | ∃ φ, P = definable φ}⟩

/-- MDG7(c): the ring framework does not tell `√2` from `−√2`. -/
theorem ringFramework_same : ringFramework.Same Zsqrtd.sqrtd (-Zsqrtd.sqrtd) := by
  rintro P ⟨φ, hφ, rfl⟩
  have h := eval_equiv_of_orderFree conj conj_func φ hφ ![Zsqrtd.sqrtd] Empty.elim
  have e₁ : (conj ∘ ![Zsqrtd.sqrtd] : Fin 1 → Z2) = ![-Zsqrtd.sqrtd] := by
    funext i
    fin_cases i
    simpa using conj_sqrtd
  have e₂ : (conj ∘ (Empty.elim : Empty → Z2)) = Empty.elim := funext fun x ↦ Empty.elim x
  rw [e₁, e₂] at h
  exact h

/-- The formula `0 < x`. -/
noncomputable def posFormula : Semisentence ℒₒᵣ 1 := “x. 0 < x”

/-- MDG7(d): the ordered framework tells `√2` from `−√2`. -/
theorem orderedFramework_not_same : ¬ orderedFramework.Same Zsqrtd.sqrtd (-Zsqrtd.sqrtd) := by
  intro h
  have := (h (definable posFormula) ⟨_, rfl⟩).mp (by
    simpa [definable, posFormula] using zero_lt_sqrtd)
  exact not_zero_lt_neg_sqrtd (by simpa [definable, posFormula] using this)

/-- MDG7(e). -/
theorem refineStep_ring_ordered : RefineStep ringFramework orderedFramework :=
  ⟨fun _ ⟨φ, _, hP⟩ ↦ ⟨φ, hP⟩, _, _, ringFramework_same, orderedFramework_not_same⟩

end MeaningDimension.Generation
