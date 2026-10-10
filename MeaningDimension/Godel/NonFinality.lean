import MeaningDimension.Godel.EffectiveAscent

/-!
# Phase 2, G4: conditional non-finality

Spec: `docs/spec.md`, G4.

`Eligible S` says that the stage `S` contains `𝗜𝚺₁` and is Σ₁-sound. It mentions no extension
of `S`. `ProperExtension S S'` is Foundation's strict strength order `⪱`, not a notion defined
here. The theorem `G4` is therefore not true by definition: its content is G1 (Gödel II) plus
L2.2 (propagation of Σ₁-soundness), which together make the property iterable.

`G4` is the formal counterpart of condition (iv) of the paper's generative schema (§3.4) **for
effectively presented arithmetic theories only**. It is not a proof of the paper's axiom that
meaning-dimension generation is infinitely possible (§2.3).

The last theorem contrasts two quantifier orders from §3.3: no eligible stage proves every
sentence true in `ℕ` ("one stage for all questions" fails), while every eligible stage has a
strictly stronger eligible successor.
-/

namespace MeaningDimension.Godel

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

/-- A stage to which Gödel II applies and from which the ascent can continue. -/
def Eligible (S : Stage) : Prop :=
  𝗜𝚺₁ ⪯ S.theory ∧ S.theory.SoundOnHierarchy 𝚺 1

/-- `S'` proves everything `S` proves, and something `S` does not prove. -/
def ProperExtension (S S' : Stage) : Prop :=
  S.theory ⪱ S'.theory

/-- One step of `G4` with the canonical witness `S.next`. -/
theorem Eligible.next {S : Stage} (hS : Eligible S) :
    ProperExtension S S.next ∧ Eligible S.next := by
  obtain ⟨hI, hs⟩ := hS
  have : Consistent S.theory := inferInstance
  exact ⟨G1_strict S.theory, WeakerThan.trans hI S.le_next, S.sigma1Sound_next⟩

/-- **G4** Every eligible stage has a proper extension that is again eligible. The witness is
`S.next = S ∪ {Con(S)}`. -/
theorem G4 : ∀ S : Stage, Eligible S → ∃ S' : Stage, ProperExtension S S' ∧ Eligible S' :=
  fun S hS ↦ ⟨S.next, hS.next⟩

/-- **G4, iterated.** Iterating `Stage.next` from an eligible stage stays eligible. -/
theorem Eligible.iterate_next {S : Stage} (hS : Eligible S) :
    ∀ n, Eligible (Stage.next^[n] S)
  | 0 => hS
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact (hS.iterate_next n).next.2

/-- **G4, iterated.** Every iterate `Stage.next^[n+1] S` properly extends `S`. -/
theorem Eligible.properExtension_iterate_next {S : Stage} (hS : Eligible S) :
    ∀ n, ProperExtension S (Stage.next^[n + 1] S)
  | 0 => hS.next.1
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact StrictlyWeakerThan.trans (hS.properExtension_iterate_next n)
      (hS.iterate_next (n + 1)).next.1

/-- **§3.3, "one stage for all questions" fails.** No eligible stage proves every sentence true in
`ℕ`: its own consistency statement is true and unprovable. -/
theorem not_exists_eligible_proves_all_truths :
    ¬ ∃ S : Stage, Eligible S ∧ ∀ σ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ σ → S.theory ⊢ σ := by
  rintro ⟨S, ⟨hI, hs⟩, hall⟩
  have : Consistent S.theory := inferInstance
  exact G1_unprovable S.theory (hall _ (models_consistent S.theory))

/-- **§3.3, "for each question of this family, some later stage".** Each consistency statement
`Con(Tₙ)` of the ascent is proved at stage `n + 1`. (This is the trivial, effective case; the
paper's claim for *all* true sentences concerns transfinite progressions and is not formalized.) -/
theorem consistency_proved_later (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) :
    (ascent T (n + 1)).theory ⊢ (ascent T n).theory.consistent.val :=
  by_axm (by simp [ascent_succ, Stage.next])

end MeaningDimension.Godel
