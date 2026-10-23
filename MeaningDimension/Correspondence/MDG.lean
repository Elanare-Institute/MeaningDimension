import MeaningDimension.Correspondence.Extension
import MeaningDimension.Generation.Examples

/-!
# Meaning-dimension generation as a model with input, and its maps to ACSI and the Gödel side

Spec: `docs/correspondence_spec.md` §7, N13–N17, CR11–CR13.

Until now, MDG described only the relation between two structures after generation (an embedding
and a flipping sentence). Here generation gets an input: a stage is a structure (`Struc`), a demand
may come to a stage when it does not hold there and holds in some structure into which the stage
embeds (`mdgOffer`), and the making (`MDGMaking`) is a black box that takes a stage and a demand that
may come to it and returns a new stage into which the old one embeds and where the demand holds. It
is treated like ACSI's making: its contents are not specified, only that it exists.

Everything compared here is compared by isomorphisms constructed in Lean:

* CR12: a past of existential demands (`MDGPast`) has a trace isomorphic to the standard structure
  of its length, hence to the traces of ACSI and of the Gödelian ascent of the same length. This is
  an isomorphism of histories, not of models.
* CR13: the input structure at a stage (the stage and the inputs that may come there,
  `OfferIncidence`). The standard input structure with `n` inputs is isomorphic to a part of the
  input structure of ACSI (at the empty self) and of MDG (at ℝ) for every `n`, and for `n = 2` to no
  part of the Gödel side, whose offer is unique. No isomorphism between whole models is constructed.
-/

namespace MeaningDimension.Correspondence

open FFL FFL.FirstOrder
open MeaningDimension.ACSI MeaningDimension.Godel MeaningDimension.Generation

universe u v u' v'

/-! ## CR11: the input model of MDG -/

/-- A structure of the language `L`, bundled (N13). -/
structure Struc (L : Language) where
  carrier : Type
  [str : Tarski.Structure L carrier]
  [ne : Nonempty carrier]

attribute [instance] Struc.str Struc.ne

variable {L : Language}

/-- The sentence `σ` holds in the structure `M`. -/
def Struc.Holds (M : Struc L) (σ : Sentence L) : Prop := M.carrier↓[L] ⊧ σ

/-- The demand `σ` may come to `M` (N14): it does not hold in `M` and holds in some structure into
which `M` embeds. -/
def mdgOffer (M : Struc L) (σ : Sentence L) : Prop :=
  ¬ M.Holds σ ∧ ∃ M' : Struc L, Nonempty (M.carrier ↪ₛ[L] M'.carrier) ∧ M'.Holds σ

noncomputable instance (M : Struc L) (σ : Sentence L) : Decidable (mdgOffer M σ) :=
  Classical.propDecidable _

/-- The making of MDG (N15): a black box. From a stage and a demand that may come to it, it returns
a new stage into which the old one embeds and where the demand holds. -/
structure MDGMaking (L : Language) where
  gen : (M : Struc L) → (σ : Sentence L) → mdgOffer M σ → Struc L
  emb : ∀ M σ h, Nonempty (M.carrier ↪ₛ[L] (gen M σ h).carrier)
  holds_gen : ∀ M σ h, (gen M σ h).Holds σ

namespace MDGMaking

/-- CR11(a): a making exists. Its contents are not specified. -/
theorem nonempty (L : Language) : Nonempty (MDGMaking L) :=
  ⟨⟨fun _ _ h ↦ Classical.choose h.2, fun _ _ h ↦ (Classical.choose_spec h.2).1,
    fun _ _ h ↦ (Classical.choose_spec h.2).2⟩⟩

variable (G : MDGMaking L)

/-- Taking a demand in; a demand that may not come leaves the stage as it is. -/
noncomputable def step (M : Struc L) (σ : Sentence L) : Struc L :=
  if h : mdgOffer M σ then G.gen M σ h else M

/-- The stage after the demands `h` (in temporal order), starting from `M₀`. -/
noncomputable def run (M₀ : Struc L) (h : List (Sentence L)) : Struc L := h.foldl G.step M₀

/-- Each demand of `h` may come to the stage that takes it in. -/
def Offered (M₀ : Struc L) (h : List (Sentence L)) : Prop :=
  ∀ k (hk : k < h.length), mdgOffer (G.run M₀ (h.take k)) h[k]

variable {G}

/-- CR11(b). -/
theorem step_of_offer {M : Struc L} {σ : Sentence L} (h : mdgOffer M σ) :
    G.step M σ = G.gen M σ h := by
  simp [step, h]

/-- CR11(c): existential sentences that held before still hold after generation. -/
theorem holds_gen_of_isExistential {M : Struc L} {σ : Sentence L} (h : mdgOffer M σ)
    {τ : Sentence L} (hτ : IsExistential τ) (hM : M.Holds τ) : (G.gen M σ h).Holds τ :=
  let ⟨Θ⟩ := G.emb M σ h
  models_of_isExistential Θ hτ hM

variable (G)

theorem run_take_succ (M₀ : Struc L) (h : List (Sentence L)) {k : ℕ} (hk : k < h.length) :
    G.run M₀ (h.take (k + 1)) = G.step (G.run M₀ (h.take k)) h[k] := by
  rw [run, run, List.take_succ_eq_append_getElem hk, List.foldl_append]
  rfl

end MDGMaking

/-! ## CR12: pasts of MDG and their traces -/

/-- A past of MDG (N16): stages, an embedding of each stage into the next, and existential demands,
each failing at its stage and holding at the next. -/
structure MDGPast (L : Language) (n : ℕ) where
  stage : Fin (n + 1) → Struc L
  emb : ∀ k : Fin n, Nonempty ((stage k.castSucc).carrier ↪ₛ[L] (stage k.succ).carrier)
  demand : Fin n → Sentence L
  existential : ∀ k, IsExistential (demand k)
  not_holds : ∀ k : Fin n, ¬ (stage k.castSucc).Holds (demand k)
  holds : ∀ k : Fin n, (stage k.succ).Holds (demand k)

namespace MDGPast

variable {n : ℕ} (c : MDGPast L n)

/-- Existential demands, once they hold, keep holding along the past. -/
theorem holds_mono (j : Fin n) {k m : ℕ} (hkm : k ≤ m) (hm : m ≤ n)
    (h : (c.stage ⟨k, by omega⟩).Holds (c.demand j)) :
    (c.stage ⟨m, by omega⟩).Holds (c.demand j) := by
  induction m, hkm using Nat.le_induction with
  | base => exact h
  | succ m _ ih =>
    obtain ⟨Θ⟩ := c.emb ⟨m, by omega⟩
    exact models_of_isExistential Θ (c.existential j) (ih (by omega) h)

/-- CR12(a): the `j`-th demand holds at the `k`-th stage exactly when `j < k`. -/
theorem holds_iff (k : Fin (n + 1)) (j : Fin n) :
    (c.stage k).Holds (c.demand j) ↔ (j : ℕ) < k := by
  constructor
  · intro h
    by_contra hjk
    have hkj : (k : ℕ) ≤ j := Nat.le_of_not_lt hjk
    exact c.not_holds j (c.holds_mono j (k := k) (m := j) hkj (by omega) h)
  · intro hjk
    have h₀ : (c.stage ⟨(j : ℕ) + 1, by omega⟩).Holds (c.demand j) := c.holds j
    exact c.holds_mono j (k := (j : ℕ) + 1) (m := k) hjk (by omega) h₀

/-- CR12(a). -/
theorem stage_injective : Function.Injective c.stage := by
  have key : ∀ k m : Fin (n + 1), (k : ℕ) < m → c.stage k ≠ c.stage m := fun k m hkm e ↦ by
    have hk : (k : ℕ) < n := by omega
    have h := (c.holds_iff m ⟨k, hk⟩).mpr hkm
    rw [← e, c.holds_iff] at h
    exact lt_irrefl _ h
  intro k m e
  rcases lt_trichotomy (k : ℕ) m with h | h | h
  · exact absurd e (key k m h)
  · exact Fin.ext h
  · exact absurd e.symm (key m k h)

/-- CR12(a). -/
theorem demand_injective : Function.Injective c.demand := by
  have key : ∀ i j : Fin n, (i : ℕ) < j → c.demand i ≠ c.demand j := fun i j hij e ↦ by
    have h := (c.holds_iff ⟨(i : ℕ) + 1, by omega⟩ i).mpr (Nat.lt_succ_self _)
    rw [e, c.holds_iff] at h
    exact absurd h (by simp; omega)
  intro i j e
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · exact absurd e (key i j h)
  · exact Fin.ext h
  · exact absurd e.symm (key j i h)

/-- The trace of the past (§7.2). -/
abbrev trace : Incidence where
  Stage := Set.range c.stage
  Item := Set.range c.demand
  Holds s x := (s : Struc L).Holds x
  Next s x s' := ∃ k : Fin n, (s : Struc L) = c.stage k.castSucc ∧ (x : Sentence L) = c.demand k ∧
    (s' : Struc L) = c.stage k.succ

/-- CR12(b): the trace is isomorphic to the standard structure of its length. -/
noncomputable def ofStd : (Incidence.std n).Iso c.trace where
  stage := Equiv.ofInjective _ c.stage_injective
  item := Equiv.ofInjective _ c.demand_injective
  holds_iff k j := (c.holds_iff k j).symm
  next_iff k j k' := by
    simp only [Equiv.ofInjective_apply]
    constructor
    · rintro ⟨hj, hk'⟩
      have e₁ : k = j.castSucc := Fin.ext hj.symm
      have e₂ : k' = j.succ := Fin.ext (by simp [hk', hj])
      exact ⟨j, by rw [e₁], rfl, by rw [e₂]⟩
    · rintro ⟨m, e₁, e₂, e₃⟩
      have hk : k = m.castSucc := c.stage_injective e₁
      have hj : j = m := c.demand_injective e₂
      have hk' : k' = m.succ := c.stage_injective e₃
      subst hk hj hk'
      exact ⟨rfl, rfl⟩

theorem ofStd_stage (k : Fin (n + 1)) : (c.ofStd.stage k : Struc L) = c.stage k := rfl

theorem ofStd_item (j : Fin n) : (c.ofStd.item j : Sentence L) = c.demand j := rfl

end MDGPast

namespace MDGMaking

variable (G : MDGMaking L)

/-- CR12(c): a past followed by the making, with existential demands, is an `MDGPast`. -/
noncomputable def toPast (M₀ : Struc L) (h : List (Sentence L)) (ho : G.Offered M₀ h)
    (hex : ∀ σ ∈ h, IsExistential σ) : MDGPast L h.length where
  stage k := G.run M₀ (h.take k)
  demand j := h[(j : ℕ)]
  emb k := by
    show Nonempty ((G.run M₀ (h.take k)).carrier ↪ₛ[L] (G.run M₀ (h.take (k + 1))).carrier)
    rw [G.run_take_succ M₀ h k.2, step_of_offer (ho k k.2)]
    exact G.emb _ _ _
  existential j := hex _ (List.getElem_mem _)
  not_holds k := (ho k k.2).1
  holds k := by
    show (G.run M₀ (h.take (k + 1))).Holds h[(k : ℕ)]
    rw [G.run_take_succ M₀ h k.2, step_of_offer (ho k k.2)]
    exact G.holds_gen _ _ _

theorem toPast_stage (M₀ : Struc L) (h : List (Sentence L)) (ho : G.Offered M₀ h)
    (hex : ∀ σ ∈ h, IsExistential σ) (k : Fin (h.length + 1)) :
    (G.toPast M₀ h ho hex).stage k = G.run M₀ (h.take k) :=
  rfl

theorem toPast_demand (M₀ : Struc L) (h : List (Sentence L)) (ho : G.Offered M₀ h)
    (hex : ∀ σ ∈ h, IsExistential σ) (j : Fin h.length) :
    (G.toPast M₀ h ho hex).demand j = h[(j : ℕ)] :=
  rfl

end MDGMaking

/-! ### CR12(d): the three traces -/

section Three

variable {E : Type u} {M : Making E} {S₀ : Self E} {h : List E}

/-- CR12(d): the trace of an MDG past is isomorphic to the trace of a fresh ACSI past of the same
length. -/
noncomputable def mdgAcsiIso (c : MDGPast L h.length) (hf : (acsiGrowth M).Fresh S₀ h) :
    c.trace.Iso ((acsiGrowth M).trace S₀ h) :=
  c.ofStd.symm.trans hf.ofStd

/-- CR12(d): the `k`-th stage goes to the self at stage `k`. -/
theorem mdgAcsiIso_stage (c : MDGPast L h.length) (hf : (acsiGrowth M).Fresh S₀ h)
    (k : Fin (h.length + 1)) :
    ((mdgAcsiIso c hf).stage ⟨c.stage k, k, rfl⟩ : Self E) = M.run S₀ (h.take k) := by
  have e : c.ofStd.symm.stage ⟨c.stage k, k, rfl⟩ = k :=
    Equiv.ofInjective_symm_apply c.stage_injective k
  show (hf.ofStd.stage (c.ofStd.symm.stage _) : Self E) = _
  rw [e]
  rfl

/-- CR12(d): the `j`-th demand goes to the `j`-th experience. -/
theorem mdgAcsiIso_item (c : MDGPast L h.length) (hf : (acsiGrowth M).Fresh S₀ h)
    (j : Fin h.length) :
    ((mdgAcsiIso c hf).item ⟨c.demand j, j, rfl⟩ : E) = h[(j : ℕ)] := by
  have e : c.ofStd.symm.item ⟨c.demand j, j, rfl⟩ = j :=
    Equiv.ofInjective_symm_apply c.demand_injective j
  show (hf.ofStd.item (c.ofStd.symm.item _) : E) = _
  rw [e]
  rfl

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/-- CR12(d): the trace of an MDG past is isomorphic to the Gödelian trace of the same length. -/
noncomputable def mdgGodelIso {n : ℕ} (c : MDGPast L n) :
    c.trace.Iso (godelGrowth.trace T (conPast T n)) :=
  c.ofStd.symm.trans ((Incidence.Iso.stdCast (conPast_length T n).symm).trans
    (conPast_fresh T n).ofStd)

/-- CR12(d): the `k`-th stage goes to `Tₖ`. -/
theorem mdgGodelIso_stage {n : ℕ} (c : MDGPast L n) (k : Fin (n + 1)) :
    ((mdgGodelIso T c).stage ⟨c.stage k, k, rfl⟩ : ArithmeticTheory) = (ascent T k).theory := by
  have e : c.ofStd.symm.stage ⟨c.stage k, k, rfl⟩ = k :=
    Equiv.ofInjective_symm_apply c.stage_injective k
  show ((conPast_fresh T n).ofStd.stage
    ((Incidence.Iso.stdCast (conPast_length T n).symm).stage (c.ofStd.symm.stage _)) :
      ArithmeticTheory) = _
  rw [e]
  show godelGrowth.run T ((conPast T n).take k) = _
  rw [conPast_take T (Nat.lt_succ_iff.mp k.2), run_conPast]

/-- CR12(d): the `j`-th demand goes to `Con(Tⱼ)`. -/
theorem mdgGodelIso_item {n : ℕ} (c : MDGPast L n) (j : Fin n) :
    ((mdgGodelIso T c).item ⟨c.demand j, j, rfl⟩ : ArithmeticSentence) =
      (ascent T j).theory.consistent.val := by
  have e : c.ofStd.symm.item ⟨c.demand j, j, rfl⟩ = j :=
    Equiv.ofInjective_symm_apply c.demand_injective j
  show ((conPast_fresh T n).ofStd.item
    ((Incidence.Iso.stdCast (conPast_length T n).symm).item (c.ofStd.symm.item _)) :
      ArithmeticSentence) = _
  rw [e]
  exact conPast_getElem T _

end Three

/-! ### CR12(e): the history ℕ → ℤ → ℚ → ℝ → ℂ -/

section History

/-- The inclusion `ℤ → ℚ`. -/
def intRat : ℤ ↪ₛ[ℒᵣ] ℚ :=
  ringEmbedding (Int.cast : ℤ → ℚ) Int.cast_injective Int.cast_zero Int.cast_one Int.cast_add
    Int.cast_mul

/-- `∃x (x + x = 1)`. -/
noncomputable def sentenceQ : Sentence ℒᵣ := “∃ x, x + x = 1”

theorem sentenceQ_isExistential : IsExistential sentenceQ := .ex (.of_open rfl)

theorem int_not_models_sentenceQ : ¬ ℤ↓[ℒᵣ] ⊧ sentenceQ := by
  simp [sentenceQ, models_iff]
  intro x h
  omega

theorem rat_models_sentenceQ : ℚ↓[ℒᵣ] ⊧ sentenceQ := by
  simp [sentenceQ, models_iff]
  exact ⟨1 / 2, by norm_num⟩

def natS : Struc ℒᵣ := ⟨ℕ⟩
def intS : Struc ℒᵣ := ⟨ℤ⟩
def ratS : Struc ℒᵣ := ⟨ℚ⟩
def realS : Struc ℒᵣ := ⟨ℝ⟩
def complexS : Struc ℒᵣ := ⟨ℂ⟩

/-- CR12(e): the history ℕ → ℤ → ℚ → ℝ → ℂ as a past of MDG. -/
noncomputable def historyPast : MDGPast ℒᵣ 4 where
  stage := ![natS, intS, ratS, realS, complexS]
  demand := ![sentenceZ, sentenceQ, sentenceR, sentenceC]
  emb k := by
    fin_cases k
    exacts [⟨natInt⟩, ⟨intRat⟩, ⟨ratReal⟩, ⟨realComplex⟩]
  existential k := by
    fin_cases k
    exacts [sentenceZ_isExistential, sentenceQ_isExistential, sentenceR_isExistential,
      sentenceC_isExistential]
  not_holds k := by
    fin_cases k
    exacts [nat_not_models_sentenceZ, int_not_models_sentenceQ, rat_not_models_sentenceR,
      real_not_models_sentenceC]
  holds k := by
    fin_cases k
    exacts [int_models_sentenceZ, rat_models_sentenceQ, real_models_sentenceR,
      complex_models_sentenceC]

end History

/-! ## CR13: input structures -/

/-- A stage-and-input structure (N17): stages, items, which items hold at which stages, and which
items may come to which stages. -/
structure OfferIncidence where
  Stage : Type u
  Item : Type v
  Holds : Stage → Item → Prop
  Offer : Stage → Item → Prop

namespace OfferIncidence

/-- An isomorphism: bijections on stages and on items that preserve and reflect `Holds` and
`Offer`. -/
structure Iso (A : OfferIncidence.{u, v}) (B : OfferIncidence.{u', v'}) where
  stage : A.Stage ≃ B.Stage
  item : A.Item ≃ B.Item
  holds_iff : ∀ s x, A.Holds s x ↔ B.Holds (stage s) (item x)
  offer_iff : ∀ s x, A.Offer s x ↔ B.Offer (stage s) (item x)

/-- The standard input structure: one stage and `n` items, each of which may come and none of which
holds. -/
abbrev std (n : ℕ) : OfferIncidence.{0, 0} where
  Stage := Unit
  Item := Fin n
  Holds _ _ := False
  Offer _ _ := True

end OfferIncidence

/-- The part of an input structure made of the stage `s` and the items `xs`. -/
abbrev offerAt {S : Type u} {I : Type v} (Holds Offer : S → I → Prop) (s : S) {n : ℕ}
    (xs : Fin n ↪ I) : OfferIncidence.{u, v} where
  Stage := {t // t = s}
  Item := Set.range xs
  Holds t x := Holds t x
  Offer t x := Offer t x

section OfferAt

variable {S : Type u} {I : Type v} {Holds Offer : S → I → Prop} {s : S} {n : ℕ}
  {xs : Fin n ↪ I} (hxs : ∀ i, Offer s (xs i)) (hnew : ∀ x, Offer s x → ¬ Holds s x)

/-- CR13(a): `n` different inputs that may come to `s`, none of which holds at `s`, form a copy of
the standard input structure. The isomorphism sends the only stage to `s` and the `i`-th item to
`xs i`. -/
noncomputable def offerAtIso : (OfferIncidence.std n).Iso (offerAt Holds Offer s xs) where
  stage :=
    { toFun := fun _ ↦ ⟨s, rfl⟩
      invFun := fun _ ↦ ()
      left_inv := fun _ ↦ rfl
      right_inv := fun ⟨_, ht⟩ ↦ by subst ht; rfl }
  item := Equiv.ofInjective xs xs.injective
  holds_iff := fun _ i ↦ ⟨False.elim, fun h ↦ hnew _ (hxs i) h⟩
  offer_iff := fun _ i ↦ ⟨fun _ ↦ hxs i, fun _ ↦ trivial⟩

/-- CR13(a): the only stage goes to `s`. -/
theorem offerAtIso_stage (u : Unit) : ((offerAtIso hxs hnew).stage u : S) = s := rfl

/-- CR13(a): the `i`-th item goes to `xs i`. -/
theorem offerAtIso_item (i : Fin n) : ((offerAtIso hxs hnew).item i : I) = xs i := rfl

include hxs hnew in
/-- CR13(a), as an existence statement. -/
theorem offerAt_iso : Nonempty ((OfferIncidence.std n).Iso (offerAt Holds Offer s xs)) :=
  ⟨offerAtIso hxs hnew⟩

end OfferAt

theorem isNew_empty {E : Type u} (e : E) : (Self.empty : Self E).IsNew e :=
  fun ⟨_, hc, _⟩ ↦ List.not_mem_nil hc

/-- CR13(b): with infinitely many possible experiences, every standard input structure has a copy
at the empty self, whatever the making. -/
theorem acsi_offerIso {E : Type u} [Infinite E] (M : Making E) (n : ℕ) :
    ∃ xs : Fin n ↪ E, Nonempty ((OfferIncidence.std n).Iso
      (offerAt (acsiGrowth M).Holds (fun S e ↦ S.IsNew e) Self.empty xs)) :=
  ⟨Fin.valEmbedding.trans (Infinite.natEmbedding E),
    offerAt_iso (fun _ ↦ isNew_empty _) (fun _ h ↦ h)⟩

/-- Different demands, each equivalent to `sentenceC`. -/
noncomputable def padC : ℕ → Sentence ℒᵣ
  | 0 => sentenceC
  | k + 1 => padC k ⋏ padC k

theorem complexity_padC : ∀ k, (padC k).complexity = sentenceC.complexity + k
  | 0 => rfl
  | k + 1 => by simp [padC, complexity_padC k]; omega

theorem padC_injective : Function.Injective padC := fun k m h ↦ by
  have := congrArg Semiformula.complexity h
  rw [complexity_padC, complexity_padC] at this
  omega

theorem models_padC_iff {M : Type} [Nonempty M] [Tarski.Structure ℒᵣ M] :
    ∀ k, M↓[ℒᵣ] ⊧ padC k ↔ M↓[ℒᵣ] ⊧ sentenceC
  | 0 => Iff.rfl
  | k + 1 => by rw [padC, Semantics.And.models_and, models_padC_iff k, and_self]

/-- Each `padC k` may come to ℝ. -/
theorem mdgOffer_real_padC (k : ℕ) : mdgOffer realS (padC k) :=
  ⟨fun h ↦ real_not_models_sentenceC ((models_padC_iff k).mp h),
    complexS, ⟨realComplex⟩, (models_padC_iff k).mpr complex_models_sentenceC⟩

/-- CR13(c): every standard input structure has a copy at ℝ, whatever the making. -/
theorem mdg_offerIso (n : ℕ) :
    ∃ xs : Fin n ↪ Sentence ℒᵣ,
      Nonempty ((OfferIncidence.std n).Iso (offerAt Struc.Holds mdgOffer realS xs)) :=
  ⟨⟨fun i ↦ padC i, fun _ _ h ↦ Fin.ext (padC_injective h)⟩,
    offerAt_iso (fun i ↦ mdgOffer_real_padC i) (fun _ h ↦ h.1)⟩

/-- CR13(d): on the Gödel side the standard input structure with two inputs has no copy, since the
offer is unique. -/
theorem godel_not_offerIso (S : Godel.Stage) (xs : Fin 2 ↪ ArithmeticSentence) :
    IsEmpty ((OfferIncidence.std 2).Iso (offerAt godelStageGrowth.Holds ownCon S xs)) :=
  ⟨fun e ↦ by
    have h₀ := (e.offer_iff () 0).mp trivial
    have h₁ := (e.offer_iff () 1).mp trivial
    have : ((e.item 0 : Set.range xs) : ArithmeticSentence) = (e.item 1 : Set.range xs) :=
      ownCon_unique h₀ h₁
    exact absurd (e.item.injective (Subtype.ext this)) (by decide)⟩

end MeaningDimension.Correspondence
