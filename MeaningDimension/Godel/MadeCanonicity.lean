import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Height

/-!
# Phase 3 (preliminary): what the derivability conditions do not determine

Analysis and context: `docs/made_canonicity_audit.md`.

The paper proposes *made-canonicity* as a criterion that selects "the" consistency statement of a
theory, and says that the Hilbert–Bernays–Löb conditions D1–D3 follow from it. This file does
**not** formalize made-canonicity: its condition (ii) has no formal definition yet. It proves an
abstract fact that constrains any such criterion.

**Disjunctive variant.** For a provability predicate `□` and any sentence `π`, put
`□'σ := □σ ∨ π`.

* `disj_HBL`: if `□` satisfies D1–D3, so does `□'`, whatever `π` is.
* `disj_con_iff`: `Con' ↔ Con ∧ ¬π` provably in the base theory.

**Arithmetic instance** (`T` Σ₁-sound, `□` = Foundation's standard provability of `T`,
`π := □(¬Con_T)`):

* `standard_disj_models_iff`: `□'` is extensionally correct: `ℕ ⊧ □'σ ↔ T ⊢ σ`.
* `standard_disj_con_not_implied`: `T ⊬ Con_T → Con'`. So two provability predicates for the same
  theory, both satisfying D1–D3, both correct in `ℕ`, both Σ₁ in form (a disjunction of Σ₁
  formulas), have consistency statements that `T` does not prove equivalent.
* `standard_disj_con_unprovable`: Gödel II still holds for `□'` (it satisfies D1–D3).

Informally (not formalized), `□'` is the provability predicate of the Σ₁ presentation
`α'(x) := α(x) ∨ (x = ⌜0=1⌝ ∧ Pr_α(⌜¬Con_α⌝))`, which contains no Π₁ clause asserting the
non-existence of a proof. Whether `α'` "embeds information about the provability relation" in the
sense of condition (ii) is exactly what the condition leaves undefined.

Mathematical status: elementary consequences of standard facts (Löb's theorem; see
`formalized_unprovable_not_con` in Foundation). We do not claim mathematical novelty; we have
not found this particular construction stated in the sources we checked.
-/

namespace MeaningDimension.MadeCanonicity

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment FFL.FirstOrder.ProvabilityAbstraction

section Abstract

variable {L : Language} [L.ReferenceableBy L] [L.DecidableEq] {T₀ T : Theory L}

/-- The disjunctive variant `disjProv 𝔅 π`, with `(disjProv 𝔅 π) σ = 𝔅 σ ⋎ π` (`disj_apply`).
D1 for the variant follows from D1 for `𝔅`. -/
def disjProv (𝔅 : Provability T₀ T) (π : Sentence L) : Provability T₀ T where
  prov := “x. !𝔅.prov x ∨ !π”
  bew_def := fun {σ} h ↦ by
    have h₁ : T₀ ⊢ 𝔅 σ := 𝔅.D1 h
    have e : (“x. !𝔅.prov x ∨ !π” : Semisentence L 1)/[⌜σ⌝] = 𝔅 σ ⋎ π := by
      simp [Provability.pr, Rewriting.subst, ← TransitiveRewriting.comp_app, Rew.subst_comp_subst]
    rw [e]
    cl_prover [h₁]

variable (𝔅 : Provability T₀ T) (π : Sentence L)

omit [L.DecidableEq] in
@[simp] lemma disj_apply (σ : Sentence L) : (disjProv 𝔅 π) σ = 𝔅 σ ⋎ π := by
  simp [disjProv, Provability.pr, Rewriting.subst, ← TransitiveRewriting.comp_app,
    Rew.subst_comp_subst]

/-- D2 is preserved. -/
instance disj_HBL2 [𝔅.HBL2] : (disjProv 𝔅 π).HBL2 := ⟨fun {σ τ} ↦ by
  have h : T₀ ⊢ 𝔅 (σ 🡒 τ) 🡒 𝔅 σ 🡒 𝔅 τ := 𝔅.D2
  simp only [disj_apply]
  cl_prover [h]⟩

/-- D3 is preserved. -/
instance disj_HBL3 [𝔅.HBL2] [𝔅.HBL3] : (disjProv 𝔅 π).HBL3 := ⟨fun {σ} ↦ by
  have h₁ : T₀ ⊢ 𝔅 σ 🡒 𝔅 (𝔅 σ) := 𝔅.D3
  have h₂ : T₀ ⊢ 𝔅 (𝔅 σ) 🡒 𝔅 (𝔅 σ ⋎ π) := 𝔅.mono (by cl_prover)
  simp only [disj_apply]
  cl_prover [h₁, h₂]⟩

/-- D1–D3 are preserved by `□ ↦ □ ∨ π`, for every sentence `π`. -/
instance disj_HBL [𝔅.HBL] : (disjProv 𝔅 π).HBL where

-- `cl_prover` needs `[L.DecidableEq]` while elaborating, though the proof term does not use it.
set_option linter.unusedSectionVars false in
/-- The consistency statement of the variant is `Con ∧ ¬π`. -/
lemma disj_con_iff : T₀ ⊢ (disjProv 𝔅 π).con 🡘 𝔅.con ⋏ ∼π := by
  simp only [Provability.con, disj_apply]
  cl_prover

end Abstract

section Arithmetic

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- `π := □_T(¬Con_T)`, "T proves its own inconsistency". -/
noncomputable abbrev selfRefutation : ArithmeticSentence :=
  T.standardProvability (∼T.standardProvability.con)

/-- The variant `□'σ := □_T σ ∨ □_T(¬Con_T)`. -/
noncomputable abbrev standardDisj : Provability 𝗜𝚺₁ T :=
  disjProv T.standardProvability (selfRefutation T)

/-- `□'` satisfies D1–D3. -/
example : (standardDisj T).HBL := inferInstance

omit [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] in
/-- `□'σ` is a Σ₁ sentence (a disjunction of two Σ₁ sentences), like `□σ`. -/
theorem standard_disj_sigma1 (σ : ArithmeticSentence) :
    ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 ((standardDisj T) σ) := by
  simp [standardDisj, selfRefutation, Arithmetic.standardProvability_def]

/-- `□'` is extensionally correct in the standard model: it holds of exactly the theorems of `T`.
(External truth in `ℕ`, not internal provability.) -/
theorem standard_disj_models_iff (σ : ArithmeticSentence) :
    ℕ↓[ℒₒᵣ] ⊧ (standardDisj T) σ ↔ T ⊢ σ := by
  have hπ : ¬ ℕ↓[ℒₒᵣ] ⊧ selfRefutation T := by
    rw [models_standardProvability_iff]
    exact con_unrefutable (𝔅 := T.standardProvability)
  simp [standardDisj, hπ, models_standardProvability_iff]

/-- The two consistency statements are not `T`-provably equivalent: `T ⊬ Con → Con'`. -/
theorem standard_disj_con_not_implied :
    T ⊬ T.standardProvability.con 🡒 (standardDisj T).con := by
  intro h
  have hiff : T ⊢ (standardDisj T).con 🡘 T.standardProvability.con ⋏ ∼selfRefutation T :=
    WeakerThan.pbl (disj_con_iff _ _)
  have : T ⊢ T.standardProvability.con 🡒 ∼T.standardProvability (∼T.standardProvability.con) :=
    C_trans (C_trans h (K_left hiff)) and₂
  exact formalized_unprovable_not_con (𝔅 := T.standardProvability) this

omit [T.SoundOnHierarchy 𝚺 1] in
/-- The converse direction does hold: `Con'` implies `Con`. -/
theorem standard_disj_con_implies : T ⊢ (standardDisj T).con 🡒 T.standardProvability.con := by
  have hiff : T ⊢ (standardDisj T).con 🡘 T.standardProvability.con ⋏ ∼selfRefutation T :=
    WeakerThan.pbl (disj_con_iff _ _)
  exact C_trans (K_left hiff) and₁

/-- Gödel II holds for `□'` as well. -/
theorem standard_disj_con_unprovable : T ⊬ (standardDisj T).con :=
  con_unprovable (𝔅 := standardDisj T)

end Arithmetic

end MeaningDimension.MadeCanonicity
