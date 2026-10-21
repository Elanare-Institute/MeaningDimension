import Foundation.FirstOrder.Incompleteness.Examples

/-!
# The reversal form: embeddings and flipping sentences

Spec: `docs/mdg_spec.md`, §2.1, J9, J10, MDG1(a)–(d), MDG1(f).

A step in the reversal form (`ReversalStep`) is an embedding of the earlier structure into the
later one together with a sentence that is false in the earlier structure and true in the later
one (`Flips`). Neither structure satisfies a sentence and its negation; the reversal is a relation
between the two stages. Embeddings are Foundation's `Tarski.Structure.Embedding`
(`M ↪ₛ[L] M'`): injective maps that preserve the function symbols and preserve and reflect the
relation symbols.

Along an embedding (MDG1):

* quantifier-free formulas keep their truth values, with parameters from the earlier structure
  (Foundation's `Semiformula.eval_hom_iff_of_open`);
* existential formulas true in the earlier structure stay true;
* universal formulas true in the later structure were true in the earlier one.

Hence an existential sentence never flips from true to false, and a universal sentence never flips
from false to true. Universal sentences can flip from true to false (MDG1(e), in
`Generation/Examples.lean`).

That happens only when the old sentence is evaluated over the whole new domain. Evaluated with
every quantifier restricted to the old domain (`EvalOn`, the image of the embedding), every
formula keeps its truth value (MDG1(f)): what was true stays true and what was false stays false.
-/

namespace MeaningDimension.Generation

open FFL FFL.FirstOrder

variable {L : Language} {ξ : Type*}

/-- Existential formulas: a block of `∃` in front of a quantifier-free matrix (J3). -/
inductive IsExistential : {n : ℕ} → Semiformula L ξ n → Prop
  | of_open {n : ℕ} {φ : Semiformula L ξ n} : φ.Open → IsExistential φ
  | ex {n : ℕ} {φ : Semiformula L ξ (n + 1)} : IsExistential φ → IsExistential (∃¹ φ)

/-- Universal formulas: a block of `∀` in front of a quantifier-free matrix (J3). -/
inductive IsUniversal : {n : ℕ} → Semiformula L ξ n → Prop
  | of_open {n : ℕ} {φ : Semiformula L ξ n} : φ.Open → IsUniversal φ
  | all {n : ℕ} {φ : Semiformula L ξ (n + 1)} : IsUniversal φ → IsUniversal (∀¹ φ)

variable (L)

/-- `σ` flips from `M` to `M'`: it is false in `M` and true in `M'`. -/
def Flips (M M' : Type*) [Nonempty M] [Nonempty M'] [Tarski.Structure L M]
    [Tarski.Structure L M'] (σ : Sentence L) : Prop :=
  M↓[L] ⊧ ∼σ ∧ M'↓[L] ⊧ σ

/-- A step in the reversal form: `M` embeds into `M'`, and some sentence flips. -/
def ReversalStep (M M' : Type*) [Nonempty M] [Nonempty M'] [Tarski.Structure L M]
    [Tarski.Structure L M'] : Prop :=
  Nonempty (M ↪ₛ[L] M') ∧ ∃ σ, Flips L M M' σ

variable {L}

section Preservation

variable {M M' : Type*} [Nonempty M] [Nonempty M'] [Tarski.Structure L M]
  [Tarski.Structure L M'] (Θ : M ↪ₛ[L] M')

omit [Nonempty M] [Nonempty M'] in
/-- MDG1(a) (Foundation's `eval_hom_iff_of_open`). -/
theorem eval_iff_of_open {n : ℕ} {φ : Semiformula L ξ n} (hφ : φ.Open) (e : Fin n → M)
    (ε : ξ → M) : φ.Eval e ε ↔ φ.Eval (Θ ∘ e) (Θ ∘ ε) :=
  Semiformula.eval_hom_iff_of_open Θ hφ

omit [Nonempty M] [Nonempty M'] in
/-- MDG1(b). -/
theorem eval_of_isExistential {n : ℕ} {φ : Semiformula L ξ n} (hφ : IsExistential φ) :
    ∀ (e : Fin n → M) (ε : ξ → M), φ.Eval e ε → φ.Eval (Θ ∘ e) (Θ ∘ ε) := by
  induction hφ with
  | of_open h => exact fun e ε ↦ (eval_iff_of_open Θ h e ε).mp
  | ex _ ih =>
    intro e ε h
    obtain ⟨x, hx⟩ := Semiformula.eval_ex.mp h
    refine Semiformula.eval_ex.mpr ⟨Θ x, ?_⟩
    have e' : (Θ ∘ (x :> e) : Fin _ → M') = Θ x :> (Θ ∘ e) := Matrix.comp_vecCons _ _ _
    simpa [e'] using ih (x :> e) ε hx

omit [Nonempty M] [Nonempty M'] in
/-- MDG1(c). -/
theorem eval_of_isUniversal {n : ℕ} {φ : Semiformula L ξ n} (hφ : IsUniversal φ) :
    ∀ (e : Fin n → M) (ε : ξ → M), φ.Eval (Θ ∘ e) (Θ ∘ ε) → φ.Eval e ε := by
  induction hφ with
  | of_open h => exact fun e ε ↦ (eval_iff_of_open Θ h e ε).mpr
  | all _ ih =>
    intro e ε h
    refine Semiformula.eval_all.mpr fun x ↦ ih (x :> e) ε ?_
    have e' : (Θ ∘ (x :> e) : Fin _ → M') = Θ x :> (Θ ∘ e) := Matrix.comp_vecCons _ _ _
    simpa [e'] using Semiformula.eval_all.mp h (Θ x)

omit [Nonempty M] [Nonempty M'] in
theorem comp_finZero (e : Fin 0 → M) : (Θ ∘ e : Fin 0 → M') = ![] :=
  funext fun i ↦ Fin.elim0 i

omit [Nonempty M] [Nonempty M'] in
theorem comp_empty (ε : Empty → M) : (Θ ∘ ε : Empty → M') = Empty.elim :=
  funext fun x ↦ Empty.elim x

include Θ in
/-- Existential sentences true in `M` are true in `M'`. -/
theorem models_of_isExistential {σ : Sentence L} (hσ : IsExistential σ) (h : M↓[L] ⊧ σ) :
    M'↓[L] ⊧ σ := by
  have := eval_of_isExistential Θ hσ ![] Empty.elim h
  rwa [comp_finZero, comp_empty] at this

include Θ in
/-- Universal sentences true in `M'` are true in `M`. -/
theorem models_of_isUniversal {σ : Sentence L} (hσ : IsUniversal σ) (h : M'↓[L] ⊧ σ) :
    M↓[L] ⊧ σ := by
  refine eval_of_isUniversal Θ hσ ![] Empty.elim ?_
  rwa [comp_finZero, comp_empty]

include Θ in
/-- MDG1(d): an existential sentence does not flip from true to false. -/
theorem not_true_false_of_isExistential {σ : Sentence L} (hσ : IsExistential σ) :
    ¬ (M↓[L] ⊧ σ ∧ M'↓[L] ⊧ ∼σ) := fun ⟨h, h'⟩ ↦
  (Semantics.Not.models_not.mp h') (models_of_isExistential Θ hσ h)

include Θ in
/-- MDG1(d): a universal sentence does not flip from false to true. -/
theorem not_flips_of_isUniversal {σ : Sentence L} (hσ : IsUniversal σ) : ¬ Flips L M M' σ :=
  fun ⟨h, h'⟩ ↦ (Semantics.Not.models_not.mp h) (models_of_isUniversal Θ hσ h')

end Preservation

/-! ## Restriction to the old domain -/

variable (L) in
/-- Truth in `M'` with every quantifier restricted to `R` (J10): the truth condition of the
formula relativized to a predicate for `R`, in `M'` expanded by that predicate. -/
def EvalOn {M' : Type*} [Tarski.Structure L M'] (R : Set M') :
    {n : ℕ} → Semiformula L ξ n → (Fin n → M') → (ξ → M') → Prop
  | _, .verum, _, _ => True
  | _, .falsum, _, _ => False
  | _, .rel r v, b, ε => Tarski.Structure.rel r fun i ↦ (v i).val b ε
  | _, .nrel r v, b, ε => ¬ Tarski.Structure.rel r fun i ↦ (v i).val b ε
  | _, .and φ ψ, b, ε => EvalOn R φ b ε ∧ EvalOn R ψ b ε
  | _, .or φ ψ, b, ε => EvalOn R φ b ε ∨ EvalOn R ψ b ε
  | _, .all φ, b, ε => ∀ x ∈ R, EvalOn R φ (x :> b) ε
  | _, .exs φ, b, ε => ∃ x ∈ R, EvalOn R φ (x :> b) ε

section Restriction

variable {M M' : Type*} [Tarski.Structure L M] [Tarski.Structure L M'] (Θ : M ↪ₛ[L] M')

/-- MDG1(f): restricted to the image of the embedding, every formula keeps its truth value. -/
theorem eval_iff_evalOn : ∀ {n : ℕ} (φ : Semiformula L ξ n) (b : Fin n → M) (ε : ξ → M),
    φ.Eval b ε ↔ EvalOn L (Set.range Θ) φ (Θ ∘ b) (Θ ∘ ε)
  | _, .verum, _, _ => ⟨fun _ ↦ trivial, fun _ ↦ trivial⟩
  | _, .falsum, _, _ => ⟨fun h ↦ (h : False).elim, fun h ↦ (h : False).elim⟩
  | _, .rel r v, b, ε => by
    show Tarski.Structure.rel r (fun i ↦ (v i).val b ε) ↔
      Tarski.Structure.rel r fun i ↦ (v i).val (Θ ∘ b) (Θ ∘ ε)
    simp only [← Tarski.Structure.HomClass.val_term Θ]
    exact (Tarski.Structure.EmbeddingClass.rel Θ r _).symm
  | _, .nrel r v, b, ε => by
    show ¬ Tarski.Structure.rel r (fun i ↦ (v i).val b ε) ↔
      ¬ Tarski.Structure.rel r fun i ↦ (v i).val (Θ ∘ b) (Θ ∘ ε)
    simp only [← Tarski.Structure.HomClass.val_term Θ]
    exact not_congr (Tarski.Structure.EmbeddingClass.rel Θ r _).symm
  | _, .and φ ψ, b, ε => and_congr (eval_iff_evalOn φ b ε) (eval_iff_evalOn ψ b ε)
  | _, .or φ ψ, b, ε => or_congr (eval_iff_evalOn φ b ε) (eval_iff_evalOn ψ b ε)
  | _, .all φ, b, ε => by
    show (∀ x, φ.Eval (x :> b) ε) ↔ ∀ y ∈ Set.range Θ, EvalOn L _ φ (y :> (Θ ∘ b)) (Θ ∘ ε)
    have key : ∀ x, φ.Eval (x :> b) ε ↔ EvalOn L (Set.range Θ) φ (Θ x :> (Θ ∘ b)) (Θ ∘ ε) :=
      fun x ↦ by
        have e : (Θ ∘ (x :> b) : Fin _ → M') = Θ x :> (Θ ∘ b) := Matrix.comp_vecCons _ _ _
        rw [eval_iff_evalOn φ (x :> b) ε, e]
    constructor
    · rintro h _ ⟨x, rfl⟩
      exact (key x).mp (h x)
    · exact fun h x ↦ (key x).mpr (h _ ⟨x, rfl⟩)
  | _, .exs φ, b, ε => by
    show (∃ x, φ.Eval (x :> b) ε) ↔ ∃ y ∈ Set.range Θ, EvalOn L _ φ (y :> (Θ ∘ b)) (Θ ∘ ε)
    have key : ∀ x, φ.Eval (x :> b) ε ↔ EvalOn L (Set.range Θ) φ (Θ x :> (Θ ∘ b)) (Θ ∘ ε) :=
      fun x ↦ by
        have e : (Θ ∘ (x :> b) : Fin _ → M') = Θ x :> (Θ ∘ b) := Matrix.comp_vecCons _ _ _
        rw [eval_iff_evalOn φ (x :> b) ε, e]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨Θ x, ⟨x, rfl⟩, (key x).mp hx⟩
    · rintro ⟨_, ⟨x, rfl⟩, h⟩
      exact ⟨x, (key x).mpr h⟩

/-- MDG1(f), for sentences: restricted to the old domain, a sentence true in `M` stays true in
`M'`, and a sentence false in `M` stays false. -/
theorem models_iff_evalOn [Nonempty M] (σ : Sentence L) :
    M↓[L] ⊧ σ ↔ EvalOn L (Set.range Θ) σ ![] Empty.elim := by
  have h := eval_iff_evalOn Θ σ ![] Empty.elim
  rwa [comp_finZero, comp_empty] at h

end Restriction

end MeaningDimension.Generation
