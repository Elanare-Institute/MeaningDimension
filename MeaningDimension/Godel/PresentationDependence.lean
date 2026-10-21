import Foundation.FirstOrder.Incompleteness.Examples
import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.CraigTrick

/-!
# G5: the next stage depends on the presentation, not on the theory alone

Spec: `docs/presentation_spec.md`.

For a Σ₁-sound theory `T ⊇ 𝗜𝚺₁` with a `Δ₁` presentation `α`, we build a second `Δ₁`
presentation `β = twisted T` of the *same* set of axioms such that

  `T ∪ {Con_α} ⪱ T ∪ {Con_β}`.

So the step `T ↦ T ∪ {Con(T)}` is not a function of the set of axioms: it depends on the
presentation (`exists_presentations_not_equiv`, `not_function_of_theory`).

The presentation `β` adds "ghost axioms": once a proof of `¬Con_α` from `α` is found, the padded
falsum `⊥ ⋏ ⊤ ⋏ ⋯ ⋏ ⊤` becomes an axiom. In `ℕ` there is no such proof (Σ₁-soundness), so `β`
defines exactly the axioms of `T`; but `𝗜𝚺₁` cannot prove this, and internally
`□_α(¬Con_α) → □_β ⊥` (`provable_incon_imp_twisted_bot`). The padding keeps the search for the
proof bounded, so `β` is `Δ₁`; the construction follows Craig's trick in Foundation
(`Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/CraigTrick.lean`).

The step `T ∪ {Con_α} ⊬ Con_β` uses Foundation's `formalized_unprovable_not_con` (a consequence
of Löb's theorem), not a formalized deduction theorem.

Known mathematics (dependence of the consistency statement on the presentation, Feferman 1960).
-/

namespace MeaningDimension.Godel

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable (T : ArithmeticTheory) [T.Δ₁]

/-! ## The ghost axioms -/

/-- `ρ_T`: the Σ₁ sentence "`T` proves `¬Con(T)`". -/
noncomputable def proofOfIncon : ArithmeticSentence := T.standardProvability (∼T.consistent.val)

lemma proofOfIncon_sigma1 : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 (proofOfIncon T) := by
  simp [proofOfIncon, standardProvability_def]

/-- A `Δ₀` matrix of `ρ_T`: `𝗜𝚺₁ ⊢ ρ_T ↔ ∃ s, θ(s)`. -/
noncomputable def inconWitness : 𝚺ᴬ₀.Semisentence 1 :=
  .mkSigma (ISigma1.exists_matrix_provable (n := 0) (proofOfIncon_sigma1 T)).choose.val

lemma inconWitness_spec (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    V↓[ℒₒᵣ] ⊧ proofOfIncon T ↔ ∃ s : V, V ⊧/![s] (inconWitness T).val := by
  have := models_iff_of_provable_iff
    (ISigma1.exists_matrix_provable (n := 0) (proofOfIncon_sigma1 T)).choose_spec V ![]
  simpa [models_iff, inconWitness, Matrix.constant_eq_singleton] using this

/-- `x` is a ghost axiom: the code of `⊥ ⋏ ⊤ ⋏ ⋯ ⋏ ⊤` padded by a witness `s` of `ρ_T`. -/
def IsGhost (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (x : V) : Prop :=
  ∃ s : V, x = ^⊥ ^⋏ qqVerums s ∧ V ⊧/![s] (inconWitness T).val

/-- The `Δ₁` definition of the ghost axioms (bounded, as in Craig's trick). -/
noncomputable def ghostCh : 𝚫ᴬ₁.Semisentence 1 := .mkDelta
  (.mkSigma “x. ∃ s < x, ∃ v < x, ∃ f < x,
    !qqFalsumDef f ∧ !qqVerumsGraph v s ∧ !qqAndDef x f v ∧ !(inconWitness T).val s”)
  (.mkPi “x. ∃ s < x, ∃ v < x, ∃ f < x,
    !qqFalsumDef f ∧ (∀ v', !qqVerumsGraph v' s → v' = v) ∧ !qqAndDef x f v ∧
      !(inconWitness T).val s”)

variable {T} in
lemma IsGhost.lt_aux {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (s : V) :
    s < ^⊥ ^⋏ qqVerums s ∧ qqVerums s < ^⊥ ^⋏ qqVerums s ∧ (^⊥ : V) < ^⊥ ^⋏ qqVerums s :=
  ⟨lt_of_le_of_lt (le_qqVerums s) (lt_K!_right _ _), lt_K!_right _ _, lt_K!_left _ _⟩

instance IsGhost.defined {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚫ᴬ₁-Predicate[V] (IsGhost T V) via ghostCh T := .mk <| by
  constructor
  · intro v; simp [ghostCh]
  · intro v
    simp only [ghostCh, IsGhost]
    simp
    constructor
    · rintro ⟨s, _, _, _, hx, hs⟩
      exact ⟨s, hx, hs⟩
    · rintro ⟨s, hx, hs⟩
      obtain ⟨h₁, h₂, h₃⟩ := IsGhost.lt_aux s
      exact ⟨s, by rw [hx]; exact h₁, by rw [hx]; exact h₂, by rw [hx]; exact h₃, hx, hs⟩

/-- If a padded falsum `⊥ ⋏ ⊤ ⋏ ⋯ ⋏ ⊤` is an axiom of `U` (inside a model of `𝗜𝚺₁`), then `U`
proves `⊥` there. -/
lemma provable_bot_of_mem_padded_falsum {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (U : ArithmeticTheory) [U.Δ₁] {s : V} (h : (^⊥ ^⋏ qqVerums s : V) ∈ U.Δ₁Class) :
    Provable U (⌜(⊥ : ArithmeticSentence)⌝ : V) := by
  let φ : Formula V ℒₒᵣ := ⊥ ⋏ verums s
  have h₁ : U.internalize V ⊢ φ := ⟨TProof.byAxm h⟩
  have h₂ : U.internalize V ⊢ (⊥ : Formula V ℒₒᵣ) := K_left h₁
  exact tprovable_iff_provable.mp h₂

section Twisted

variable [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- In `ℕ` there is no ghost axiom: `T ⊬ ¬Con(T)` by Σ₁-soundness. -/
lemma not_isGhost_nat (x : ℕ) : ¬ IsGhost T ℕ x := by
  rintro ⟨s, -, hs⟩
  have hρ : ℕ↓[ℒₒᵣ] ⊧ proofOfIncon T := (inconWitness_spec T ℕ).mpr ⟨s, hs⟩
  have hT : T ⊢ ∼T.consistent.val := models_standardProvability_iff.mp hρ
  exact ProvabilityAbstraction.con_unrefutable (𝔅 := T.standardProvability) hT

/-- The ghost axioms as a `Δ₁` presentation of the empty theory. -/
@[instance_reducible]
noncomputable def ghostPresentation : (∅ : ArithmeticTheory).Δ₁ where
  ch := ghostCh T
  mem_iff φ := by
    simp only [Set.mem_empty_iff_false, false_and, exists_false, iff_false]
    exact fun h ↦ not_isGhost_nat T _ ((IsGhost.defined (T := T) (V := ℕ)).iff.mp h)
  isDelta1 := Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _
    fun V _ _ ↦ (IsGhost.defined (T := T) (V := V)).proper

/-- **G5.1** The second presentation `β` of `T`: the axioms of `α` or a ghost axiom. -/
@[instance_reducible]
noncomputable def twisted : T.Δ₁ :=
  (Theory.Δ₁.add inferInstance (ghostPresentation T)).ofEq (Set.union_empty T)

lemma mem_twisted_Δ₁Class {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {x : V} :
    x ∈ @Theory.Δ₁Class V _ ℒₒᵣ _ _ T (twisted T) ↔ x ∈ T.Δ₁Class ∨ IsGhost T V x :=
  (@Theory.Δ₁Class.mem_union ℒₒᵣ _ _ T ∅ V _ _ (ghostPresentation T) x).trans
    (or_congr Iff.rfl (IsGhost.defined (T := T) (V := V)).iff)

/-- Inside any model of `𝗜𝚺₁`, a ghost axiom makes `β` prove `⊥`. -/
lemma provable_twisted_bot_of_isGhost {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {s : V}
    (hs : V ⊧/![s] (inconWitness T).val) :
    @Provable V _ _ ℒₒᵣ _ _ T (twisted T) (⌜(⊥ : ArithmeticSentence)⌝ : V) :=
  @provable_bot_of_mem_padded_falsum V _ _ T (twisted T) s
    ((mem_twisted_Δ₁Class T).mpr (Or.inr ⟨s, rfl, hs⟩))

/-- `□_β`: the standard provability predicate built from `β`. -/
noncomputable abbrev twistedProvability : ProvabilityAbstraction.Provability 𝗜𝚺₁ T :=
  @Theory.standardProvability ℒₒᵣ _ _ T (twisted T)

/-- **G5.2** `𝗜𝚺₁ ⊢ □_α(¬Con_α) → □_β ⊥`. -/
theorem provable_incon_imp_twisted_bot :
    𝗜𝚺₁ ⊢ proofOfIncon T 🡒 twistedProvability T ⊥ :=
  complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦ by
    apply Semantics.Imp.models_imply.mpr
    intro hρ
    obtain ⟨s, hs⟩ := (inconWitness_spec T V).mp hρ
    simpa [models_iff, standardProvability_def] using provable_twisted_bot_of_isGhost T hs

/-- `Con_β`: the consistency statement built from `β`. -/
noncomputable abbrev twistedCon : ArithmeticSentence :=
  (@Theory.consistent ℒₒᵣ _ _ T (twisted T)).val

lemma twistedCon_eq : twistedCon T = (twistedProvability T).con :=
  @Bootstrapping.consistent_eq T (twisted T)

/-- **G5.3** `𝗜𝚺₁ ⊢ Con_β → Con_α`: every axiom of `α` is an axiom of `β`. -/
theorem twistedCon_imp_con : 𝗜𝚺₁ ⊢ twistedCon T 🡒 T.consistent.val := by
  have hsub : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (p : V),
      p ∈ T.Δ₁Class → p ∈ @Theory.Δ₁Class V _ ℒₒᵣ _ _ T (twisted T) :=
    fun _ _ _ _ hp ↦ (mem_twisted_Δ₁Class T).mpr (Or.inl hp)
  have h : 𝗜𝚺₁ ⊢ T.standardProvability ⊥ 🡒 twistedProvability T ⊥ :=
    @provable_standardProvability_imp_of_Δ₁Class_subset T T _ (twisted T) hsub ⊥
  rw [twistedCon_eq, Bootstrapping.consistent_eq]
  exact contra h

/-- **G5.4** `T ∪ {Con_α} ⊬ Con_β`. If it were provable, `T ⊢ Con_α → ¬□_α(¬Con_α)` would follow
from G5.2, against `formalized_unprovable_not_con` (Löb's theorem). -/
theorem not_provable_twistedCon : T ∪ T.Con ⊬ twistedCon T := by
  intro h
  have e : T ∪ T.Con = T.consistent.val ∷ T := by simp [Theory.Con, Set.union_singleton]; rfl
  rw [e] at h
  have h₁ : T ⊢ T.consistent.val 🡒 twistedCon T := deduction_iff.mp h
  rw [twistedCon_eq, Bootstrapping.consistent_eq] at h₁
  have h₂ : T ⊢ proofOfIncon T 🡒 twistedProvability T ⊥ :=
    WeakerThan.pbl (provable_incon_imp_twisted_bot T)
  have h₃ : T ⊢ T.standardProvability.con 🡒 ∼proofOfIncon T := C_trans h₁ (contra h₂)
  exact ProvabilityAbstraction.formalized_unprovable_not_con (𝔅 := T.standardProvability) h₃

/-- The defining formula of `β` is that of `α` or that of the ghost axioms. -/
lemma twisted_ch : (twisted T).ch = T.Δ₁ch ⋎ ghostCh T := rfl

instance : 𝗜𝚺₁ ⪯ T ∪ {twistedCon T} :=
  WeakerThan.trans inferInstance (WeakerThan.ofSubset Set.subset_union_left)

/-- **G5.3** `T ∪ {Con_β} ⊢ Con_α`. -/
theorem provable_con_of_twistedCon : T ∪ {twistedCon T} ⊢ T.consistent.val :=
  (WeakerThan.pbl (twistedCon_imp_con T) : T ∪ {twistedCon T} ⊢ twistedCon T 🡒 _) ⨀
    by_axm (Set.mem_union_right _ rfl)

/-- **G5.5** The next stage built from `β` is strictly stronger than the one built from `α`. -/
theorem strict_twisted : T ∪ T.Con ⪱ T ∪ {twistedCon T} := by
  have : T ∪ T.Con ⪯ T ∪ {twistedCon T} := WeakerThan.ofAxm! <| by
    rintro σ (hσ | hσ)
    · exact by_axm (Set.mem_union_left _ hσ)
    · rw [Set.mem_singleton_iff.mp hσ]
      exact provable_con_of_twistedCon T
  exact StrictlyWeakerThan.of_unprovable_provable (not_provable_twistedCon T)
    (by_axm (Set.mem_union_right _ rfl))

/-- **G5.5** -/
theorem not_equiv_twisted : ¬ (T ∪ T.Con ≊ T ∪ {twistedCon T}) := fun e ↦
  (strict_twisted T).notWT (Equiv.antisymm_iff.mp e).2

end Twisted

/-! ## G5.6: the next stage is not a function of the theory -/

omit [T.Δ₁] in
/-- The next stage `T ∪ {Con_d}` built from the presentation `d`. -/
abbrev nextWith (d : T.Δ₁) : ArithmeticTheory := T ∪ {(@Theory.consistent ℒₒᵣ _ _ T d).val}

section NotFunction

variable [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- **G5.6(a)** Two presentations of the same axioms give inequivalent next stages. -/
theorem exists_presentations_not_equiv : ∃ d₁ d₂ : T.Δ₁, ¬ (nextWith T d₁ ≊ nextWith T d₂) :=
  ⟨inferInstance, twisted T, not_equiv_twisted T⟩

/-- **G5.6(b)** No function of the theory (the set of axioms) gives the next stage for every
presentation. -/
theorem not_function_of_theory (F : ArithmeticTheory → ArithmeticTheory) :
    ¬ ∀ d : T.Δ₁, F T ≊ nextWith T d := fun hF ↦
  not_equiv_twisted T ((hF inferInstance).symm.trans (hF (twisted T)))

end NotFunction

end MeaningDimension.Godel
