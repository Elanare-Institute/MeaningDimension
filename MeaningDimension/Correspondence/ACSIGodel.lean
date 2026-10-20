import MeaningDimension.Correspondence.Growth
import MeaningDimension.ACSI.Incorporation
import MeaningDimension.Godel.EffectiveAscent
import MeaningDimension.Godel.PresentationDependence

/-!
# The traces of ACSI and of the Gödelian ascent are isomorphic

Spec: `docs/correspondence_spec.md`, N2, N3, N6, CR0, CR4–CR6.

* `acsiGrowth M`: stages are selves, items are experiences, an item holds when the self classifies
  it, and the step is incorporation by the making `M`.
* `godelGrowth`: stages are theories, items are sentences, an item holds when the theory proves
  it, and the step adjoins the sentence.

The Gödelian past `conPast T n` lists the consistency statements `Con(T₀), …, Con(Tₙ₋₁)` of the
ascent of `EffectiveAscent.lean`; it is fresh by Gödel II at each stage (`G2_unprovable`). Every
fresh past of experiences has a trace isomorphic to the trace of the Gödelian past of the same
length (`acsiGodelIso`): the self at stage `k` goes to `Tₖ` and the `j`-th experience to
`Con(Tⱼ)`.

The common form of AC9 and G5.6(b) (`Growth.not_predetermined`) is instantiated on both sides
with different offers: every totally new experience on the ACSI side, the consistency statement of
some presentation on the Gödel side. It is not part of the isomorphism.
-/

namespace MeaningDimension.Correspondence

open MeaningDimension.ACSI

/-! ## The ACSI side -/

section ACSI

universe u

variable {E : Type u}

/-- The ACSI growth system of the making `M` (N2). Its two axioms are AC5(b)(c). -/
abbrev acsiGrowth (M : Making E) : Growth.{u, u} where
  Stage := Self E
  Item := E
  Holds := Self.Classifies
  step := M.incorporate
  holds_step_self := Making.classifies_incorporate
  holds_step_of_holds x h := Making.classifies_incorporate_of_classifies h x

/-- CR0(a). -/
theorem acsiGrowth_run (M : Making E) : (acsiGrowth M).run = M.run := rfl

/-- A past of experiences is fresh when each experience is totally new for the self that takes it
in. -/
theorem acsiGrowth_fresh_iff (M : Making E) (S₀ : Self E) (h : List E) :
    (acsiGrowth M).Fresh S₀ h ↔ ∀ k (hk : k < h.length), (M.run S₀ (h.take k)).IsNew h[k] :=
  Iff.rfl

theorem Making.reachable_foldl (M : Making E) {S₀ : Self E} :
    ∀ (h : List E) {S : Self E}, M.Reachable S₀ S → M.Reachable S₀ (h.foldl M.incorporate S)
  | [], _, hS => hS
  | e :: h, _, hS => Making.reachable_foldl M h (hS.step e)

/-- CR4(b): under openness, there are fresh pasts of every length. -/
theorem exists_fresh_of_isOpen {M : Making E} {S₀ : Self E} (hM : M.IsOpen S₀) :
    ∀ n, ∃ h : List E, h.length = n ∧ (acsiGrowth M).Fresh S₀ h
  | 0 => ⟨[], rfl, fun _ hk ↦ absurd hk (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨h, hl, hf⟩ := exists_fresh_of_isOpen hM n
    obtain ⟨e, he⟩ := hM (M.run S₀ h) (Making.reachable_foldl M h .base)
    refine ⟨h ++ [e], by simp [hl], fun k hk ↦ ?_⟩
    rcases Nat.lt_or_ge k h.length with hk' | hk'
    · have := hf k hk'
      simpa [List.take_append_of_le_length hk'.le, List.getElem_append_left hk'] using this
    · have hkl : k = h.length := by simp at hk; omega
      subst hkl
      simpa [Self.IsNew, acsiGrowth_run] using he

/-- CR6(b): with `singletonMaking`, two different experiences, the first new for `S`, are taken
into selves that classify different experiences. -/
theorem acsi_not_equivalent (S : Self E) {e e' : E} (he : S.IsNew e) (hne : e ≠ e') :
    ¬ (acsiGrowth singletonMaking).Equivalent (singletonMaking.incorporate S e)
      (singletonMaking.incorporate S e') := fun hequiv ↦ by
  obtain ⟨c, hc, hec⟩ := (hequiv e).mp (Making.classifies_incorporate S e)
  rcases List.mem_cons.mp hc with rfl | hc
  · exact hne (Set.mem_singleton_iff.mp hec)
  · exact he ⟨c, hc, hec⟩

end ACSI

/-! ## The Gödel side -/

section Godel

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open MeaningDimension.Godel

/-- The Gödelian growth system (N3). -/
noncomputable abbrev godelGrowth : Growth.{0, 0} where
  Stage := ArithmeticTheory
  Item := ArithmeticSentence
  Holds T σ := T ⊢ σ
  step T σ := T ∪ {σ}
  holds_step_self _ _ := by_axm (Set.mem_union_right _ rfl)
  holds_step_of_holds _ h := (WeakerThan.ofSubset Set.subset_union_left).wk h

/-- CR0(b). -/
theorem godelGrowth_le_iff (T U : ArithmeticTheory) : godelGrowth.Le T U ↔ T ⪯ U :=
  ⟨fun h ↦ weakerThan_iff.mpr fun hx ↦ h _ hx, fun h _ hx ↦ h.wk hx⟩

/-- CR0(b). -/
theorem godelGrowth_equivalent_iff (T U : ArithmeticTheory) :
    godelGrowth.Equivalent T U ↔ T ≊ U := by
  rw [Entailment.Equiv.antisymm_iff, ← godelGrowth_le_iff, ← godelGrowth_le_iff]
  exact ⟨fun h ↦ ⟨fun x ↦ (h x).mp, fun x ↦ (h x).mpr⟩, fun h x ↦ ⟨h.1 x, h.2 x⟩⟩

/-- `σ` is the consistency statement of `U` built from some presentation of `U` (CR6(c)). -/
def conOffer (U : ArithmeticTheory) (σ : ArithmeticSentence) : Prop :=
  ∃ d : U.Δ₁, σ = (@Theory.consistent ℒₒᵣ _ _ U d).val

variable (T : ArithmeticTheory) [T.Δ₁]

/-- The Gödelian past `[Con(T₀), …, Con(Tₙ₋₁)]` (N6). -/
noncomputable def conPast (n : ℕ) : List ArithmeticSentence :=
  (List.range n).map fun k ↦ (ascent T k).theory.consistent.val

@[simp] theorem conPast_length (n : ℕ) : (conPast T n).length = n := by
  simp [conPast]

@[simp] theorem conPast_getElem {n k : ℕ} (hk : k < (conPast T n).length) :
    getElem (conPast T n) k hk = (ascent T k).theory.consistent.val := by
  simp only [conPast, List.getElem_map]
  rw [List.getElem_range]

theorem conPast_take {n k : ℕ} (hkn : k ≤ n) : (conPast T n).take k = conPast T k := by
  rw [conPast, conPast, ← List.map_take, List.take_range, min_eq_left hkn]

/-- CR4(a): the stage after the first `k` consistency statements is `Tₖ`. -/
theorem run_conPast : ∀ k, godelGrowth.run T (conPast T k) = (ascent T k).theory
  | 0 => rfl
  | k + 1 => by
    have e : conPast T (k + 1) = conPast T k ++ [(ascent T k).theory.consistent.val] := by
      simp [conPast, List.range_succ]
    have ih := run_conPast k
    simp only [Growth.run] at ih ⊢
    rw [e, List.foldl_append, ih]
    rfl

/-- CR4(a): the Gödelian past is fresh (Gödel II at each stage). -/
theorem conPast_fresh [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] (n : ℕ) :
    godelGrowth.Fresh T (conPast T n) := fun k hk ↦ by
  have hkn : k ≤ n := by simp at hk; omega
  simp only [conPast_take T hkn, run_conPast, conPast_getElem]
  exact G2_unprovable T k

theorem conOffer_con : conOffer T T.consistent.val := ⟨inferInstance, rfl⟩

section Twisted

variable [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

theorem conOffer_twistedCon : conOffer T (twistedCon T) := ⟨twisted T, rfl⟩

/-- CR6(c): the two offered consistency statements lead to non-equivalent stages (G5.5). -/
theorem godel_not_equivalent :
    ¬ godelGrowth.Equivalent (T ∪ {T.consistent.val}) (T ∪ {twistedCon T}) := fun h ↦
  not_equiv_twisted T ((godelGrowth_equivalent_iff _ _).mp h)

end Twisted

end Godel

/-! ## CR5: the isomorphism -/

section Iso

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open MeaningDimension.Godel

universe u

variable {E : Type u} (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- CR5(a): the trace of a fresh past of experiences is isomorphic to the trace of the Gödelian
past of the same length. -/
noncomputable def acsiGodelIso {M : Making E} {S₀ : Self E} {h : List E}
    (hf : (acsiGrowth M).Fresh S₀ h) :
    ((acsiGrowth M).trace S₀ h).Iso (godelGrowth.trace T (conPast T h.length)) :=
  Growth.traceIso hf (conPast_fresh T h.length) (conPast_length T h.length).symm

/-- CR5(a): the self at stage `k` goes to `Tₖ`. -/
theorem acsiGodelIso_stage {M : Making E} {S₀ : Self E} {h : List E}
    (hf : (acsiGrowth M).Fresh S₀ h) (k : Fin (h.length + 1)) :
    ((acsiGodelIso T hf).stage ⟨M.run S₀ (h.take k), k, rfl⟩ : ArithmeticTheory) =
      (ascent T k).theory := by
  refine (Growth.traceIso_stage hf (conPast_fresh T h.length)
    (conPast_length T h.length).symm k).trans ?_
  rw [conPast_take T (Nat.lt_succ_iff.mp k.2), run_conPast]

/-- CR5(a): the `j`-th experience goes to `Con(Tⱼ)`. -/
theorem acsiGodelIso_item {M : Making E} {S₀ : Self E} {h : List E}
    (hf : (acsiGrowth M).Fresh S₀ h) (j : Fin h.length) :
    ((acsiGodelIso T hf).item ⟨h[(j : ℕ)], j, rfl⟩ : ArithmeticSentence) =
      (ascent T j).theory.consistent.val := by
  exact (Growth.traceIso_item hf (conPast_fresh T h.length)
    (conPast_length T h.length).symm j).trans (conPast_getElem T _)

/-- CR5(b): under openness, for every length there is a fresh past of experiences whose trace is
isomorphic to the trace of the Gödelian past. -/
theorem exists_acsiGodelIso {M : Making E} {S₀ : Self E} (hM : M.IsOpen S₀) (n : ℕ) :
    ∃ h : List E, h.length = n ∧ (acsiGrowth M).Fresh S₀ h ∧
      Nonempty (((acsiGrowth M).trace S₀ h).Iso (godelGrowth.trace T (conPast T n))) := by
  obtain ⟨h, rfl, hf⟩ := exists_fresh_of_isOpen hM n
  exact ⟨h, rfl, hf, ⟨acsiGodelIso T hf⟩⟩

end Iso

end MeaningDimension.Correspondence
