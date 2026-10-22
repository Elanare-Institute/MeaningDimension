import MeaningDimension.Correspondence.Process
import MeaningDimension.Correspondence.ACSIGodel
import MeaningDimension.Generation.Godel
import MeaningDimension.Godel.NonFinality

/-!
# Extending the ACSI–Gödel isomorphism: processes, offers, and taking-in

Spec: `docs/correspondence_spec.md` §6, E1–E5, N8–N10, CR7(d)(e), CR8(b)–(e), CR9(c), CR10(c)–(f).

* CR7: the isomorphism `acsiGodelIso` of a longer past extends that of its prefix, and both sides
  can always be extended by one item (the ACSI side by openness, the Gödel side in one determined
  way).
* CR8: the Gödel side is read as a growth system on presented theories (`godelStageGrowth`) whose
  offer at a stage is the consistency statement of its own presentation (`ownCon`, E1). It is
  open from a Σ₁-sound theory, its offer is unique, and the offered step is `Stage.next`. On the
  ACSI side the offer (every totally new experience) branches, and no function of the self gives
  the next self (`singleton_not_predetermined`). This is where (iv) stays outside the isomorphism.
* CR9: the finite-stock form of AC10(c) on items, on both sides.
* CR10: the structural difference is that the Gödel side's input is fixed in advance and the ACSI
  side's is not (E1, E5). On the Gödel side the trace follows the max rule:
  `Tₖ ∪ {Con(Tⱼ)} ≊ T_{max(k, j+1)}`, because `Con(Tⱼ)` is built from `Tⱼ` and carries the earlier
  consistency statements (`union_con_proves_con`). On the ACSI side every reachable self can take
  in every experience, and an experience of a past taken in at another stage may start a new branch
  off that past. With `singletonMaking` the trace of a fresh
  past of length at least two is not closed under taking-in, so it is not isomorphic to the
  Gödelian trace with taking-in (`singleton_not_stepIso`). `iicMaking`, which fixes a linear order
  on experiences in advance, is kept only as a contrast: it reproduces the Gödelian line
  (`iicGodelStepIso`). It is not an ACSI correspondence.
-/

namespace MeaningDimension.Correspondence

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open MeaningDimension.ACSI MeaningDimension.Godel MeaningDimension.Generation

universe u

/-! ## CR7(d)(e) -/

section CR7

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
  {E : Type u} {M : Making E} {S₀ : Self E} {h h₂ : List E}

/-- CR7(d), stages. -/
theorem acsiGodelIso_stage_extends (hf : (acsiGrowth M).Fresh S₀ (h ++ h₂))
    (k : Fin (h.length + 1)) :
    ((acsiGodelIso T hf).stage
        ⟨M.run S₀ ((h ++ h₂).take (Fin.castLE (Growth.succ_length_le_append h h₂) k)), _, rfl⟩ :
        ArithmeticTheory) =
      ((acsiGodelIso T hf.of_append).stage ⟨M.run S₀ (h.take k), k, rfl⟩ : ArithmeticTheory) := by
  rw [acsiGodelIso_stage, acsiGodelIso_stage]
  rfl

/-- CR7(d), items. -/
theorem acsiGodelIso_item_extends (hf : (acsiGrowth M).Fresh S₀ (h ++ h₂)) (j : Fin h.length) :
    ((acsiGodelIso T hf).item
        ⟨(h ++ h₂).get (Fin.castLE (Growth.length_le_append h h₂) j), _, rfl⟩ :
        ArithmeticSentence) =
      ((acsiGodelIso T hf.of_append).item ⟨h[(j : ℕ)], j, rfl⟩ : ArithmeticSentence) :=
  (acsiGodelIso_item T hf (Fin.castLE (Growth.length_le_append h h₂) j)).trans
    (acsiGodelIso_item T hf.of_append j).symm

/-- CR7(e), the ACSI side: under openness every fresh past extends by one experience. -/
theorem exists_fresh_append_of_isOpen (hM : M.IsOpen S₀) (hf : (acsiGrowth M).Fresh S₀ h) :
    ∃ e, (acsiGrowth M).Fresh S₀ (h ++ [e]) :=
  let ⟨e, he⟩ := hM (M.run S₀ h) (Making.reachable_foldl M h .base)
  ⟨e, hf.append_singleton he⟩

end CR7

/-- CR7(e), the Gödel side: the Gödelian past extends in one determined way. -/
theorem conPast_succ (T : ArithmeticTheory) [T.Δ₁] (n : ℕ) :
    conPast T (n + 1) = conPast T n ++ [(ascent T n).theory.consistent.val] := by
  simp [conPast, List.range_succ]

/-! ## CR8: offers and openness -/

section CR8

/-- CR8(b): ACSI openness is openness for the offer "totally new". -/
theorem acsi_openFor_of_isOpen {E : Type u} {M : Making E} {S₀ : Self E} (hM : M.IsOpen S₀) :
    (acsiGrowth M).OpenFor (fun S e ↦ S.IsNew e) S₀ := fun h _ _ ↦
  let ⟨e, he⟩ := hM (M.run S₀ h) (Making.reachable_foldl M h .base)
  ⟨e, he, he⟩

/-- The Gödelian growth system on presented theories (N9). -/
noncomputable abbrev godelStageGrowth : Growth.{0, 0} where
  Stage := Godel.Stage
  Item := ArithmeticSentence
  Holds S σ := S.theory ⊢ σ
  step S σ := ⟨S.theory ∪ {σ}, Theory.Δ₁.add S.presentation (Theory.Δ₁.singleton σ)⟩
  holds_step_self _ _ := by_axm (Set.mem_union_right _ rfl)
  holds_step_of_holds _ h := (WeakerThan.ofSubset Set.subset_union_left).wk h

/-- The offer of the Gödel side: the consistency statement of the stage's own presentation
(N9, E1). -/
def ownCon (S : Godel.Stage) (σ : ArithmeticSentence) : Prop := σ = S.theory.consistent.val

/-- CR8(c): taking the offered item in is one step of the ascent. -/
theorem godelStageGrowth_step_con (S : Godel.Stage) :
    godelStageGrowth.step S S.theory.consistent.val = S.next :=
  rfl

/-- CR8(d): the offer is unique. -/
theorem ownCon_unique {S : Godel.Stage} {σ σ' : ArithmeticSentence} (h : ownCon S σ)
    (h' : ownCon S σ') : σ = σ' :=
  h.trans h'.symm

/-- CR8(d): the next stage given by the offer is a function of the stage. -/
theorem step_of_ownCon {S : Godel.Stage} {σ : ArithmeticSentence} (h : ownCon S σ) :
    godelStageGrowth.step S σ = S.next := by
  rw [h]
  rfl

section Godel

variable (T : ArithmeticTheory) [T.Δ₁]

theorem offered_ownCon_aux :
    ∀ n (h : List ArithmeticSentence), h.length = n →
      godelStageGrowth.Offered ownCon (ascent T 0) h →
        h = conPast T n ∧ godelStageGrowth.run (ascent T 0) h = ascent T n
  | 0, h, hl, _ => by
    obtain rfl := List.length_eq_zero_iff.mp hl
    exact ⟨rfl, rfl⟩
  | n + 1, h, hl, ho => by
    have hn : n < h.length := by omega
    have e : h = h.take n ++ [h[n]] := by
      rw [← List.take_succ_eq_append_getElem hn, ← hl, List.take_length]
    have ho' : godelStageGrowth.Offered ownCon (ascent T 0) (h.take n) :=
      (e ▸ ho : godelStageGrowth.Offered ownCon (ascent T 0) _).of_append
    obtain ⟨ih₁, ih₂⟩ := offered_ownCon_aux n (h.take n) (by simp; omega) ho'
    have hx : h[n] = (ascent T n).theory.consistent.val := by
      have := ho n hn
      rwa [ih₂] at this
    constructor
    · rw [e, ih₁, hx, conPast_succ]
    · rw [← List.take_length (l := h), hl, Growth.run_take_succ _ _ hn, ih₂, hx]
      rfl

/-- CR8(c): an offered past from `T₀` is the Gödelian past. -/
theorem offered_ownCon_eq {h : List ArithmeticSentence}
    (ho : godelStageGrowth.Offered ownCon (ascent T 0) h) : h = conPast T h.length :=
  (offered_ownCon_aux T h.length h rfl ho).1

/-- CR8(c): the stage after an offered past is the stage of the ascent of the same length. -/
theorem run_offered_ownCon {h : List ArithmeticSentence}
    (ho : godelStageGrowth.Offered ownCon (ascent T 0) h) :
    godelStageGrowth.run (ascent T 0) h = ascent T h.length :=
  (offered_ownCon_aux T h.length h rfl ho).2

/-- CR8(c): the Gödel side is open from a Σ₁-sound theory containing `𝗜𝚺₁`. -/
theorem godel_openFor [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    godelStageGrowth.OpenFor ownCon (ascent T 0) := fun h ho _ ↦ by
  rw [run_offered_ownCon T ho]
  exact ⟨_, rfl, G2_unprovable T h.length⟩

end Godel

/-- CR8(e): with infinitely many possible experiences, the offer of `singletonMaking` branches at
every self reachable from the empty self, so no function of the self gives the next self. -/
theorem singleton_not_predetermined {E : Type u} [Infinite E] {S : Self E}
    (hS : (singletonMaking : Making E).Reachable Self.empty S) (F : Self E → Self E) :
    ¬ ∀ e, S.IsNew e →
      (acsiGrowth singletonMaking).Equivalent (singletonMaking.incorporate S e) (F S) := by
  classical
  have hnew : ∀ e, e ∉ S.experiences → S.IsNew e := by
    rintro e he ⟨c, hc, hec⟩
    rw [Making.reachable_singletonMaking_categories hS] at hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    rw [Set.mem_singleton_iff.mp hec] at he
    exact he ha
  obtain ⟨e, he⟩ := Infinite.exists_notMem_finset S.experiences.toFinset
  obtain ⟨e', he'⟩ := Infinite.exists_notMem_finset (insert e S.experiences.toFinset)
  have hne : e ≠ e' := fun h ↦ he' (h ▸ Finset.mem_insert_self e _)
  have he₁ : S.IsNew e := hnew e (fun h ↦ he (List.mem_toFinset.mpr h))
  have he₂ : S.IsNew e' :=
    hnew e' (fun h ↦ he' (Finset.mem_insert_of_mem (List.mem_toFinset.mpr h)))
  exact Growth.not_predetermined (acsiGrowth singletonMaking) (fun S e ↦ S.IsNew e) he₁ he₂
    (acsi_not_equivalent S he₁ hne) F

end CR8

/-! ## CR9(c) -/

section CR9

/-- CR9(c), the ACSI side. -/
theorem acsi_exists_new_notMem {E : Type u} {M : Making E} {S₀ : Self E} (hM : M.IsOpen S₀)
    (C : Finset E) : ∃ h : List E, (acsiGrowth M).Fresh S₀ h ∧ ∃ e, (M.run S₀ h).IsNew e ∧ e ∉ C := by
  by_contra hne
  refine Growth.not_openFor_of_finite C (fun h _ hf x hx ↦ ?_) (acsi_openFor_of_isOpen hM)
  by_contra hxC
  exact hne ⟨h, hf, x, hx, hxC⟩

/-- CR9(c), the Gödel side. -/
theorem godel_exists_con_notMem (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] (C : Finset ArithmeticSentence) :
    ∃ n, (ascent T n).theory.consistent.val ∉ C := by
  by_contra hne
  refine Growth.not_openFor_of_finite C (fun h ho _ x hx ↦ ?_) (godel_openFor T)
  rw [run_offered_ownCon T ho] at hx
  have hx' : x = (ascent T h.length).theory.consistent.val := hx
  rw [hx']
  by_contra hxC
  exact hne ⟨h.length, hxC⟩

end CR9

/-! ## CR10: taking-in -/

section CR10Godel

variable (T : ArithmeticTheory) [T.Δ₁]

theorem con_succ_imp (i : ℕ) :
    𝗜𝚺₁ ⊢ (ascent T (i + 1)).theory.consistent.val 🡒 (ascent T i).theory.consistent.val := by
  have hsub : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (p : V),
      p ∈ (ascent T i).theory.Δ₁Class → p ∈ (ascent T (i + 1)).theory.Δ₁Class :=
    fun _ _ _ _ hp ↦ Theory.Δ₁Class.mem_union.mpr (Or.inl hp)
  have h := @provable_standardProvability_imp_of_Δ₁Class_subset
    (ascent T i).theory (ascent T (i + 1)).theory _ _ hsub ⊥
  rw [Bootstrapping.consistent_eq, Bootstrapping.consistent_eq]
  exact contra h

/-- CR10(c): a later consistency statement of the ascent implies an earlier one. -/
theorem con_imp_of_le {i j : ℕ} (hij : i ≤ j) :
    𝗜𝚺₁ ⊢ (ascent T j).theory.consistent.val 🡒 (ascent T i).theory.consistent.val := by
  induction j, hij using Nat.le_induction with
  | base => exact C_id
  | succ j _ ih => exact C_trans (con_succ_imp T j) ih

theorem le_union_singleton (U : ArithmeticTheory) (σ : ArithmeticSentence) : U ⪯ U ∪ {σ} :=
  WeakerThan.ofSubset Set.subset_union_left

/-- If `U ⪯ V` and `V ⊢ σ`, then `U ∪ {σ} ⪯ V`. -/
theorem union_singleton_le {U V : ArithmeticTheory} {σ : ArithmeticSentence} (hUV : U ⪯ V)
    (hσ : V ⊢ σ) : U ∪ {σ} ⪯ V := by
  rw [← godelGrowth_le_iff]
  intro x hx
  have e : U ∪ {σ} = σ ∷ U := by simp [Set.union_singleton]; rfl
  have hx' : σ ∷ U ⊢ x := by simpa [e] using hx
  exact hUV.wk (deduction_iff.mp hx') ⨀ hσ

/-- CR10(c): the ascent follows the max rule. -/
theorem ascent_union_con_equiv [𝗜𝚺₁ ⪯ T] (k j : ℕ) :
    (ascent T k).theory ∪ {(ascent T j).theory.consistent.val} ≊
      (ascent T (max k (j + 1))).theory := by
  rcases Nat.lt_or_ge j k with hjk | hjk
  · rw [max_eq_left (by omega)]
    have hprov : (ascent T k).theory ⊢ (ascent T j).theory.consistent.val :=
      (ascent_le_of_le T (by omega : j + 1 ≤ k)).wk (consistency_proved_later T j)
    exact Entailment.Equiv.antisymm_iff.mpr
      ⟨union_singleton_le (WeakerThan.refl _) hprov, le_union_singleton _ _⟩
  · rw [max_eq_right (by omega)]
    set U := (ascent T k).theory ∪ {(ascent T j).theory.consistent.val}
    have hISigma : 𝗜𝚺₁ ⪯ U :=
      WeakerThan.trans (ISigma1_le_ascent T k) (le_union_singleton _ _)
    have hconj : U ⊢ (ascent T j).theory.consistent.val := by_axm (Set.mem_union_right _ rfl)
    have key : ∀ i ≤ j + 1, (ascent T i).theory ⪯ U := by
      intro i hi
      induction i with
      | zero =>
        exact WeakerThan.trans (ascent_le_of_le T (Nat.zero_le k)) (le_union_singleton _ _)
      | succ i ih =>
        rcases Nat.lt_or_ge (i + 1) (k + 1) with hik | hik
        · exact WeakerThan.trans (ascent_le_of_le T (by omega)) (le_union_singleton _ _)
        · have hci : U ⊢ (ascent T i).theory.consistent.val :=
            hISigma.wk (con_imp_of_le T (by omega : i ≤ j)) ⨀ hconj
          rw [ascent_succ]
          exact union_singleton_le (ih (by omega)) hci
    refine Entailment.Equiv.antisymm_iff.mpr ⟨?_, key (j + 1) le_rfl⟩
    exact union_singleton_le (ascent_le_of_le T (by omega)) (consistency_proved_later T j)

/-- CR10(c): the Gödelian past follows the max rule. -/
theorem conPast_maxRule [𝗜𝚺₁ ⪯ T] (n : ℕ) : godelGrowth.MaxRule T (conPast T n) := by
  intro k j hk hj
  simp only [conPast_length] at hk hj
  have hm : max k (j + 1) ≤ n := max_le hk hj
  simp only [conPast_take T hk, conPast_take T hm, run_conPast, conPast_getElem]
  exact (godelGrowth_equivalent_iff _ _).mpr (ascent_union_con_equiv T k j)

/-- CR10(d), the Gödel side: `Con(Tⱼ)` carries every earlier consistency statement. -/
theorem union_con_proves_con [𝗜𝚺₁ ⪯ T] {i j : ℕ} (hij : i ≤ j) :
    T ∪ {(ascent T j).theory.consistent.val} ⊢ (ascent T i).theory.consistent.val := by
  have hI : 𝗜𝚺₁ ⪯ T ∪ {(ascent T j).theory.consistent.val} :=
    WeakerThan.trans (inferInstanceAs (𝗜𝚺₁ ⪯ T)) (le_union_singleton _ _)
  exact hI.wk (con_imp_of_le T hij) ⨀ by_axm (Set.mem_union_right _ rfl)

end CR10Godel

section CR10ACSI

variable {E : Type u}

/-- The contrast making (N10): experiences carry a linear order fixed in advance, and an
experience generates the category of what lies below it. Not an ACSI correspondence (E5). -/
def iicMaking [LinearOrder E] : Making E := ⟨fun _ e ↦ Set.Iic e, fun _ e ↦ le_refl e⟩

theorem classifies_incorporate_iff (M : Making E) (S : Self E) (e x : E) :
    (M.incorporate S e).Classifies x ↔ x ∈ M.generate S e ∨ S.Classifies x := by
  constructor
  · rintro ⟨c, hc, hxc⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · exact .inl hxc
    · exact .inr ⟨c, hc, hxc⟩
  · rintro (hx | hx)
    · exact ⟨_, List.mem_cons_self, hx⟩
    · exact Making.classifies_incorporate_of_classifies hx e

variable [LinearOrder E]

/-- CR10(f): what the self after the first `k` experiences classifies. -/
theorem iicMaking_classifies_run (h : List E) (k : ℕ) (hk : k ≤ h.length) (x : E) :
    (iicMaking.run Self.empty (h.take k)).Classifies x ↔
      ∃ i, ∃ hi : i < k, x ≤ h[i]'(lt_of_lt_of_le hi hk) := by
  induction k with
  | zero => simp [Making.run, Self.Classifies, Self.empty]
  | succ k ih =>
    have e := (acsiGrowth (iicMaking : Making E)).run_take_succ Self.empty h (k := k) (by omega)
    simp only [acsiGrowth_run] at e
    rw [e, classifies_incorporate_iff, ih (by omega)]
    constructor
    · rintro (hx | ⟨i, hi, hx⟩)
      · exact ⟨k, by omega, hx⟩
      · exact ⟨i, by omega, hx⟩
    · rintro ⟨i, hi, hx⟩
      rcases Nat.lt_or_ge i k with hik | hik
      · exact .inr ⟨i, hik, hx⟩
      · have : i = k := by omega
        subst this
        exact .inl hx

/-- A fresh past of `iicMaking` from the empty self is strictly increasing. -/
theorem iicMaking_lt_of_fresh {h : List E} (hf : (acsiGrowth iicMaking).Fresh Self.empty h)
    {i k : ℕ} (hik : i < k) (hk : k < h.length) : h[i] < h[k] := by
  refine lt_of_not_ge fun hle ↦ hf k hk ?_
  exact (iicMaking_classifies_run h k hk.le h[k]).mpr ⟨i, hik, hle⟩

/-- CR10(f): fresh pasts of `iicMaking` from the empty self follow the max rule. -/
theorem iicMaking_maxRule {h : List E} (hf : (acsiGrowth iicMaking).Fresh Self.empty h) :
    (acsiGrowth iicMaking).MaxRule Self.empty h := by
  intro k j hk hj x
  have hm : max k (j + 1) ≤ h.length := max_le hk hj
  show (iicMaking.incorporate (iicMaking.run Self.empty (h.take k)) h[j]).Classifies x ↔
    (iicMaking.run Self.empty (h.take (max k (j + 1)))).Classifies x
  rw [classifies_incorporate_iff, iicMaking_classifies_run h k hk,
    iicMaking_classifies_run h _ hm]
  constructor
  · rintro (hx | ⟨i, hi, hx⟩)
    · exact ⟨j, by omega, hx⟩
    · exact ⟨i, by omega, hx⟩
  · rintro ⟨i, hi, hx⟩
    rcases Nat.lt_or_ge i k with hik | hik
    · exact .inr ⟨i, hik, hx⟩
    · have hij : i ≤ j := by omega
      refine .inl (le_trans hx ?_)
      rcases Nat.lt_or_eq_of_le hij with hij | rfl
      · exact (iicMaking_lt_of_fresh hf hij hj).le
      · exact le_rfl

/-- CR10(f): `iicMaking` on `ℕ` is open from the empty self. -/
theorem iicMaking_isOpen : (iicMaking : Making ℕ).IsOpen Self.empty := by
  intro S hS
  have hcat : S.categories = S.experiences.map fun a ↦ Set.Iic a := by
    induction hS with
    | base => rfl
    | step e _ ih => simp [Making.incorporate, iicMaking, ih]
  refine ⟨S.experiences.sum + 1, ?_⟩
  rintro ⟨c, hc, hxc⟩
  rw [hcat] at hc
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
  have : a ≤ S.experiences.sum := List.le_sum_of_mem ha
  have : S.experiences.sum + 1 ≤ a := hxc
  omega

end CR10ACSI

section CR10Iso

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- CR10(f): with the contrast making `iicMaking`, which fixes the order of experiences in
advance, the trace is isomorphic to the Gödelian one even with taking-in. -/
noncomputable def iicGodelStepIso {E : Type u} [LinearOrder E] {h : List E}
    (hf : (acsiGrowth iicMaking).Fresh Self.empty h) :
    ((acsiGrowth iicMaking).stepTrace Self.empty h).Iso
      (godelGrowth.stepTrace T (conPast T h.length)) :=
  Growth.stepTraceIso hf (iicMaking_maxRule hf) (conPast_fresh T h.length)
    (conPast_maxRule T h.length) (conPast_length T h.length).symm

/-- CR10(f): the self at stage `k` goes to `Tₖ`. -/
theorem iicGodelStepIso_stage {E : Type u} [LinearOrder E] {h : List E}
    (hf : (acsiGrowth iicMaking).Fresh Self.empty h) (k : Fin (h.length + 1)) :
    ((iicGodelStepIso T hf).stage ⟨iicMaking.run Self.empty (h.take k), k, rfl⟩ :
      ArithmeticTheory) = (ascent T k).theory :=
  acsiGodelIso_stage T hf k

/-- CR10(f): the `j`-th experience goes to `Con(Tⱼ)`. -/
theorem iicGodelStepIso_item {E : Type u} [LinearOrder E] {h : List E}
    (hf : (acsiGrowth iicMaking).Fresh Self.empty h) (j : Fin h.length) :
    ((iicGodelStepIso T hf).item ⟨h[(j : ℕ)], j, rfl⟩ : ArithmeticSentence) =
      (ascent T j).theory.consistent.val :=
  acsiGodelIso_item T hf j

/-- CR10(e): with `singletonMaking`, the trace of a fresh past of length at least two is not
closed under taking-in: the second experience taken in at the first stage gives a self that
classifies it but not the first experience, which lies off the past. -/
theorem singleton_stepTrace_not_closed {E : Type u} {S₀ : Self E} {h : List E}
    (hf : (acsiGrowth singletonMaking).Fresh S₀ h) (h2 : 2 ≤ h.length) :
    ¬ ((acsiGrowth singletonMaking).stepTrace S₀ h).Closed := by
  intro hc
  have h0 : 0 < h.length := by omega
  have h1 : 1 < h.length := by omega
  obtain ⟨⟨s', m, rfl⟩, hs'⟩ := hc ⟨_, ⟨0, by omega⟩, rfl⟩ ⟨_, ⟨1, h1⟩, rfl⟩
  have e : (acsiGrowth singletonMaking).Equivalent
      (singletonMaking.incorporate S₀ h[1]) ((acsiGrowth singletonMaking).run S₀ (h.take m)) :=
    hs'
  have hm : (m : ℕ) ≤ h.length := Nat.lt_succ_iff.mp m.2
  -- the stage `m` classifies `h[1]`, so `1 < m`
  have hm1 : 1 < (m : ℕ) :=
    (hf.holds_iff h1).mp ((e h[1]).mp (Making.classifies_incorporate S₀ h[1]))
  -- it then classifies `h[0]`, which the stepped self does not
  have hc0 := (e h[0]).mpr ((hf.holds_iff h0).mpr (by omega))
  rcases (classifies_incorporate_iff singletonMaking S₀ h[1] h[0]).mp hc0 with h01 | hS₀
  · have e01 : h.get ⟨0, h0⟩ = h.get ⟨1, h1⟩ := h01
    exact absurd (congrArg Fin.val (hf.get_injective e01)) (by simp)
  · exact hf 0 h0 hS₀

/-- CR10(e): hence there is no isomorphism with taking-in between such a trace and the Gödelian
trace. -/
theorem singleton_not_stepIso {E : Type u} {S₀ : Self E} {h : List E}
    (hf : (acsiGrowth singletonMaking).Fresh S₀ h) (h2 : 2 ≤ h.length) :
    IsEmpty (((acsiGrowth singletonMaking).stepTrace S₀ h).Iso
      (godelGrowth.stepTrace T (conPast T h.length))) :=
  ⟨fun e ↦ singleton_stepTrace_not_closed hf h2
    (e.closed_iff.mpr ((conPast_fresh T h.length).closed (conPast_maxRule T h.length)))⟩

end CR10Iso

end MeaningDimension.Correspondence
