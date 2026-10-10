import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Height

/-!
# Phase 2: the Gödelian ascent `T₀, T₁ = T₀ + Con(T₀), T₂ = T₁ + Con(T₁), …`

Spec: `docs/spec.md` (G1, L2.1–L2.3, G2, G2-sharp).

Provenance of each result:

* **G1** (`G1_unprovable`, `G1_strict`) is Foundation's second incompleteness theorem
  (`FFL.FirstOrder.Arithmetic.consistent_unprovable` and the instance `T ⪱ T ∪ T.Con` in
  `Foundation/FirstOrder/Incompleteness/Second.lean`). We only give it a name. Known result.
* **L2.2** (`Stage.sigma1Sound_next`, propagation of Σ₁-soundness) is proved here. The
  mathematics is standard (it is the argument of footnote 18 of the earlier draft *Which
  Consistency Statement?*); the Lean proof is new to this project.
* **G2** (`G2_unprovable`, `G2_strict`, `G2_strict_of_lt`) is G1 applied at every stage, with
  the hypotheses of G1 discharged by L2.1–L2.3. Known corollary.
* **G2-sharp** (`consistent_union_incon`, `inconsistent_next_of_union_incon`,
  `not_sigma1Sound_union_incon`) shows that consistency alone does not carry the ascent past
  `PA + ¬Con(PA)` (Portrait 3 of the paper). It uses Foundation's
  `height_union_incon_eq_one`. Known.

The consistency statement `S.theory.consistent` is built from the `Δ₁` *presentation* stored in
the stage (`Stage.presentation`), not from the set of axioms alone. Each stage of `ascent` uses
the presentation `ch_{Tₙ} ∨ (x = ⌜Con(Tₙ)⌝)` that Foundation's `Theory.Δ₁.add` assigns to a union.
-/

namespace MeaningDimension.Godel

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

/-! ## G1: one step (Foundation, known) -/

section G1

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [Consistent T]

/-- **G1(a)** (Foundation's Gödel II). A consistent theory containing `𝗜𝚺₁`, given by a
`Δ₁` presentation, does not prove the consistency statement built from that presentation. -/
theorem G1_unprovable : T ⊬ T.consistent.val :=
  consistent_unprovable T

/-- **G1(b)** (Foundation). Adjoining the consistency statement gives a strictly stronger
theory. -/
theorem G1_strict : T ⪱ T ∪ T.Con :=
  inferInstance

end G1

/-! ## Stages -/

/-- A stage of the ascent: a theory together with a chosen `Δ₁` presentation of its axioms.
The presentation is data: different presentations of the same set give different consistency
statements. -/
structure Stage where
  theory : ArithmeticTheory
  presentation : theory.Δ₁

attribute [instance] Stage.presentation

/-- The next stage `S ∪ {Con(S)}`, presented by Foundation's union presentation. -/
noncomputable def Stage.next (S : Stage) : Stage where
  theory := S.theory ∪ S.theory.Con
  presentation := inferInstance

/-- The finite ascent `T₀ = T`, `Tₙ₊₁ = Tₙ ∪ {Con(Tₙ)}`. -/
noncomputable def ascent (T : ArithmeticTheory) [T.Δ₁] : ℕ → Stage
  | 0 => ⟨T, inferInstance⟩
  | n + 1 => (ascent T n).next

@[simp] lemma ascent_zero_theory (T : ArithmeticTheory) [T.Δ₁] : (ascent T 0).theory = T := rfl

lemma ascent_succ (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) :
    ascent T (n + 1) = (ascent T n).next := rfl

lemma Stage.subset_next (S : Stage) : S.theory ⊆ S.next.theory := Set.subset_union_left

lemma Stage.le_next (S : Stage) : S.theory ⪯ S.next.theory :=
  WeakerThan.ofSubset S.subset_next

/-! ## L2.1: every stage contains `𝗜𝚺₁` -/

/-- **L2.1** -/
theorem ISigma1_le_ascent (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] :
    ∀ n, 𝗜𝚺₁ ⪯ (ascent T n).theory
  | 0 => inferInstanceAs (𝗜𝚺₁ ⪯ T)
  | n + 1 => WeakerThan.trans (ISigma1_le_ascent T n) (ascent T n).le_next

/-! ## L2.2: Σ₁-soundness propagates -/

/-- The consistency statement of a consistent theory is true in the standard model. This is a
fact about external truth (`ℕ ⊧ …`), distinct from internal provability. -/
lemma models_consistent (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [Consistent T] :
    ℕ↓[ℒₒᵣ] ⊧ T.consistent.val := by
  have : 𝗥₀ ⪯ T := WeakerThan.trans (inferInstance : 𝗥₀ ⪯ 𝗜𝚺₁) inferInstance
  simp [models_iff, Bootstrapping.standard_consistent, *]

/-- **L2.2** (propagation of Σ₁-soundness). If `S` is Σ₁-sound then so is `S ∪ {Con(S)}`.

Proof: if `S ∪ {Con(S)} ⊢ σ` with `σ` a Σ₁ sentence, the deduction theorem gives
`S ⊢ Con(S) → σ`. This sentence is Σ₁ (its antecedent is Π₁), so it is true by Σ₁-soundness of
`S`; `Con(S)` is true because `S` is consistent; hence `σ` is true. -/
theorem Stage.sigma1Sound_next (S : Stage) [𝗜𝚺₁ ⪯ S.theory] [S.theory.SoundOnHierarchy 𝚺 1] :
    S.next.theory.SoundOnHierarchy 𝚺 1 := by
  constructor
  intro σ hσ hsig
  have hadj : S.theory.consistent.val ∷ S.theory ⊢ σ := by
    have e : S.next.theory = S.theory.consistent.val ∷ S.theory := by
      simp [Stage.next, Theory.Con, Set.union_singleton]; rfl
    simpa [e] using hσ
  have himp : S.theory ⊢ S.theory.consistent.val 🡒 σ := deduction_iff.mp hadj
  have hsigimp : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 (S.theory.consistent.val 🡒 σ) := by
    simp [hsig]
  have htrue : ℕ↓[ℒₒᵣ] ⊧ S.theory.consistent.val 🡒 σ :=
    S.theory.soundOnHierarchy 𝚺 1 himp hsigimp
  exact Semantics.Imp.models_imply.mp htrue (models_consistent S.theory)

/-- **L2.2**, iterated: every stage of the ascent from a Σ₁-sound theory is Σ₁-sound. -/
theorem sigma1Sound_ascent (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] : ∀ n, (ascent T n).theory.SoundOnHierarchy 𝚺 1
  | 0 => inferInstanceAs (T.SoundOnHierarchy 𝚺 1)
  | n + 1 => by
    have := ISigma1_le_ascent T n
    have := sigma1Sound_ascent T n
    exact (ascent T n).sigma1Sound_next

/-- **L2.3** Every stage of the ascent from a Σ₁-sound theory is consistent. -/
theorem consistent_ascent (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] (n : ℕ) : Consistent (ascent T n).theory := by
  have := sigma1Sound_ascent T n
  infer_instance

/-! ## G2: no finite stage is final -/

section G2

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- **G2(a)** No stage proves its own consistency statement. -/
theorem G2_unprovable (n : ℕ) : (ascent T n).theory ⊬ (ascent T n).theory.consistent.val := by
  have := ISigma1_le_ascent T n
  have := consistent_ascent T n
  exact G1_unprovable _

/-- **G2(b)** Each stage is strictly weaker than the next. -/
theorem G2_strict (n : ℕ) : (ascent T n).theory ⪱ (ascent T (n + 1)).theory := by
  have := ISigma1_le_ascent T n
  have := consistent_ascent T n
  exact G1_strict (ascent T n).theory

/-- **G2(c)** Earlier stages are strictly weaker than later ones. -/
theorem G2_strict_of_lt {m n : ℕ} (h : m < n) : (ascent T m).theory ⪱ (ascent T n).theory := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · exact StrictlyWeakerThan.trans (ih h') (G2_strict T n)
    · exact G2_strict T m

end G2

/-! ## G2-sharp: consistency alone does not carry the ascent (Portrait 3) -/

section Sharp

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [Consistent T]

/-- `T + ¬Con(T)` is consistent (by Gödel II for `T`). -/
theorem consistent_union_incon : Consistent (T ∪ T.Incon) := by
  have h := unprovable_iff_consistent_adjoin.mp (G1_unprovable T)
  have e : T ∪ T.Incon = (∼T.consistent.val) ∷ T := by
    simp [Theory.Incon, Set.union_singleton]; rfl
  rw [e]
  exact h

/-- `T' = T + ¬Con(T)` proves its own inconsistency, so the next stage `T' + Con(T')` is
inconsistent. Uses Foundation's `height_union_incon_eq_one`. -/
theorem inconsistent_next_of_union_incon :
    Inconsistent ((T ∪ T.Incon) ∪ (T ∪ T.Incon).Con) := by
  have : 𝗜𝚺₁ ⪯ T ∪ T.Incon :=
    WeakerThan.trans (inferInstance : 𝗜𝚺₁ ⪯ T) (WeakerThan.ofSubset Set.subset_union_left)
  have hheight : (T ∪ T.Incon).height = 1 := height_union_incon_eq_one
  have hbox : T ∪ T.Incon ⊢ (T ∪ T.Incon).standardProvability ⊥ := by
    have := (ProvabilityAbstraction.Provability.height_le_iff_boxBot (n := 1)
      (𝔅 := (T ∪ T.Incon).standardProvability)).mp (by
        exact le_of_eq (hheight.trans rfl))
    simpa using this
  have h₁ : (T ∪ T.Incon) ∪ (T ∪ T.Incon).Con ⊢ (T ∪ T.Incon).standardProvability ⊥ :=
    WeakerThan.pbl (𝓢 := T ∪ T.Incon) hbox
  have h₂ : (T ∪ T.Incon) ∪ (T ∪ T.Incon).Con ⊢ (T ∪ T.Incon).consistent.val :=
    by_axm (by simp)
  have h₂' : (T ∪ T.Incon) ∪ (T ∪ T.Incon).Con ⊢ ∼(T ∪ T.Incon).standardProvability ⊥ := by
    simpa [Bootstrapping.consistent_eq, ProvabilityAbstraction.Provability.con] using h₂
  exact inconsistent_iff_provable_bot.mpr (by cl_prover [h₁, h₂'])

/-- `T + ¬Con(T)` is not Σ₁-sound: otherwise L2.2 would make its successor Σ₁-sound and hence
consistent. So the Σ₁-soundness hypothesis of G2 cannot be weakened to consistency. -/
theorem not_sigma1Sound_union_incon : ¬ (T ∪ T.Incon).SoundOnHierarchy 𝚺 1 := by
  intro hs
  have : 𝗜𝚺₁ ⪯ T ∪ T.Incon :=
    WeakerThan.trans (inferInstance : 𝗜𝚺₁ ⪯ T) (WeakerThan.ofSubset Set.subset_union_left)
  let S : Stage := ⟨T ∪ T.Incon, inferInstance⟩
  have : S.theory.SoundOnHierarchy 𝚺 1 := hs
  have : 𝗜𝚺₁ ⪯ S.theory := inferInstanceAs (𝗜𝚺₁ ⪯ T ∪ T.Incon)
  have : S.next.theory.SoundOnHierarchy 𝚺 1 := S.sigma1Sound_next
  have hcon : Consistent S.next.theory := inferInstance
  exact not_consistent_iff_inconsistent.mpr (inconsistent_next_of_union_incon T) hcon

end Sharp

end MeaningDimension.Godel
