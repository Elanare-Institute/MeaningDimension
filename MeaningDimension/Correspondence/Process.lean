import MeaningDimension.Correspondence.Growth
import Mathlib.Data.Finset.Card

/-!
# Growth processes: offers, openness, extension, and taking items in along a trace

Spec: `docs/correspondence_spec.md` §6, N7, N11, N12, CR7(a)–(c), CR8(a), CR9(a)(b),
CR10(a)(b)(d).

An *offer* says which items a stage may take in. A past is *offered* when each item is offered at
the stage that takes it in, and a growth system is *open* for an offer when every stage after an
offered fresh past is offered an item that does not hold there.

The isomorphism of processes is stated in the form of potential infinity (N12): the isomorphism of
a longer trace extends that of its prefix (`traceIso_stage_extends`, `traceIso_item_extends`), and
under openness every offered fresh past can be extended by one item (`Fresh.append_singleton`,
`OpenFor.exists_offered_fresh`). No isomorphism between infinite sequences is stated.

`StepTo s x s'` says that taking `x` in at `s` gives a stage at which the same items hold as at
`s'` (N11). A past follows the *max rule* when taking its `j`-th item in at its `k`-th stage gives
its `max k (j + 1)`-th stage in this sense: the trace is closed under taking-in, and the item
fixes where it leads. In such a fresh past each item carries all earlier ones
(`MaxRule.holds_step_start`). Fresh max-rule traces with `StepTo` are isomorphic to a standard
structure of their length (`Fresh.ofStdStep`), hence to each other (`stepTraceIso`).
-/

namespace MeaningDimension.Correspondence

universe u v u' v' u'' v''

lemma Growth.length_le_append {α : Type*} (h h₂ : List α) : h.length ≤ (h ++ h₂).length := by
  simp

lemma Growth.succ_length_le_append {α : Type*} (h h₂ : List α) :
    h.length + 1 ≤ (h ++ h₂).length + 1 :=
  Nat.succ_le_succ (Growth.length_le_append h h₂)

namespace Growth

variable (G : Growth.{u, v})

/-- Each item of `h` is offered at the stage that takes it in (N7). -/
def Offered (Offer : G.Stage → G.Item → Prop) (s₀ : G.Stage) (h : List G.Item) : Prop :=
  ∀ k (hk : k < h.length), Offer (G.run s₀ (h.take k)) h[k]

/-- Openness for an offer: every stage after an offered fresh past is offered an item that does
not hold there (N7). -/
def OpenFor (Offer : G.Stage → G.Item → Prop) (s₀ : G.Stage) : Prop :=
  ∀ h, G.Offered Offer s₀ h → G.Fresh s₀ h → ∃ x, Offer (G.run s₀ h) x ∧ ¬ G.Holds (G.run s₀ h) x

/-- Taking `x` in at `s` gives a stage at which the same items hold as at `s'` (N11). -/
def StepTo (s : G.Stage) (x : G.Item) (s' : G.Stage) : Prop := G.Equivalent (G.step s x) s'

/-- The max rule: taking the `j`-th item in at the `k`-th stage gives the `max k (j + 1)`-th stage,
up to equivalence. -/
def MaxRule (s₀ : G.Stage) (h : List G.Item) : Prop :=
  ∀ k j, k ≤ h.length → (hj : j < h.length) →
    G.StepTo (G.run s₀ (h.take k)) h[j] (G.run s₀ (h.take (max k (j + 1))))

variable {G}

theorem Equivalent.refl (s : G.Stage) : G.Equivalent s s := fun _ ↦ Iff.rfl

theorem Equivalent.symm {s s' : G.Stage} (e : G.Equivalent s s') : G.Equivalent s' s :=
  fun x ↦ (e x).symm

theorem Equivalent.trans {s s' s'' : G.Stage} (e : G.Equivalent s s') (e' : G.Equivalent s' s'') :
    G.Equivalent s s'' :=
  fun x ↦ (e x).trans (e' x)

theorem Equivalent.le {s s' : G.Stage} (e : G.Equivalent s s') : G.Le s s' := fun x ↦ (e x).mp

/-! ## CR7(a)(b): prefixes and one-item extensions -/

variable {Offer : G.Stage → G.Item → Prop} {s₀ : G.Stage} {h h₂ : List G.Item}

/-- CR7(a). -/
theorem Fresh.of_append (hf : G.Fresh s₀ (h ++ h₂)) : G.Fresh s₀ h := fun k hk ↦ by
  have := hf k (by simp; omega)
  rwa [List.take_append_of_le_length hk.le, List.getElem_append_left hk] at this

/-- CR7(a). -/
theorem Offered.of_append (ho : G.Offered Offer s₀ (h ++ h₂)) : G.Offered Offer s₀ h :=
  fun k hk ↦ by
    have := ho k (by simp; omega)
    rwa [List.take_append_of_le_length hk.le, List.getElem_append_left hk] at this

/-- CR7(b). -/
theorem Fresh.append_singleton {x : G.Item} (hf : G.Fresh s₀ h)
    (hx : ¬ G.Holds (G.run s₀ h) x) : G.Fresh s₀ (h ++ [x]) := fun k hk ↦ by
  rcases Nat.lt_or_ge k h.length with hk' | hk'
  · rw [List.take_append_of_le_length hk'.le, List.getElem_append_left hk']
    exact hf k hk'
  · have hkl : k = h.length := by simp at hk; omega
    subst hkl
    simpa using hx

/-- CR7(b). -/
theorem Offered.append_singleton {x : G.Item} (ho : G.Offered Offer s₀ h)
    (hx : Offer (G.run s₀ h) x) : G.Offered Offer s₀ (h ++ [x]) := fun k hk ↦ by
  rcases Nat.lt_or_ge k h.length with hk' | hk'
  · rw [List.take_append_of_le_length hk'.le, List.getElem_append_left hk']
    exact ho k hk'
  · have hkl : k = h.length := by simp at hk; omega
    subst hkl
    simpa using hx

/-! ## CR7(c): the isomorphism of a longer trace extends that of its prefix -/

section Extends

variable {G' : Growth.{u', v'}} {s₀' : G'.Stage} {h' h₂' : List G'.Item}

/-- CR7(c), stages. -/
theorem traceIso_stage_extends (hf : G.Fresh s₀ (h ++ h₂)) (hf' : G'.Fresh s₀' (h' ++ h₂'))
    (hl : h.length = h'.length) (hl₂ : (h ++ h₂).length = (h' ++ h₂').length)
    (k : Fin (h.length + 1)) :
    ((traceIso hf hf' hl₂).stage
        ⟨G.stages s₀ (h ++ h₂) (Fin.castLE (succ_length_le_append h h₂) k), _, rfl⟩ :
        G'.Stage) =
      ((traceIso hf.of_append hf'.of_append hl).stage ⟨G.stages s₀ h k, k, rfl⟩ : G'.Stage) := by
  rw [traceIso_stage, traceIso_stage]
  have hk : (k : ℕ) ≤ h'.length := hl ▸ Nat.lt_succ_iff.mp k.2
  simp [List.take_append_of_le_length hk]

/-- CR7(c), items. -/
theorem traceIso_item_extends (hf : G.Fresh s₀ (h ++ h₂)) (hf' : G'.Fresh s₀' (h' ++ h₂'))
    (hl : h.length = h'.length) (hl₂ : (h ++ h₂).length = (h' ++ h₂').length)
    (j : Fin h.length) :
    ((traceIso hf hf' hl₂).item ⟨(h ++ h₂).get (Fin.castLE (length_le_append h h₂) j), _, rfl⟩ :
        G'.Item) =
      ((traceIso hf.of_append hf'.of_append hl).item ⟨h.get j, j, rfl⟩ : G'.Item) := by
  rw [traceIso_item, traceIso_item]
  have hj : (j : ℕ) < h'.length := hl ▸ j.2
  simp [List.getElem_append_left hj]

end Extends

/-! ## CR8(a), CR9(a)(b): consequences of openness -/

/-- CR8(a): under openness there are offered fresh pasts of every length. -/
theorem OpenFor.exists_offered_fresh (hO : G.OpenFor Offer s₀) :
    ∀ n, ∃ h : List G.Item, h.length = n ∧ G.Offered Offer s₀ h ∧ G.Fresh s₀ h
  | 0 => ⟨[], rfl, fun _ hk ↦ absurd hk (Nat.not_lt_zero _),
      fun _ hk ↦ absurd hk (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨h, hl, ho, hf⟩ := hO.exists_offered_fresh n
    obtain ⟨x, hxo, hxh⟩ := hO h ho hf
    exact ⟨h ++ [x], by simp [hl], ho.append_singleton hxo, hf.append_singleton hxh⟩

/-- CR9(a): no stage after an offered fresh past makes every item hold. -/
theorem OpenFor.not_all_holds (hO : G.OpenFor Offer s₀) (ho : G.Offered Offer s₀ h)
    (hf : G.Fresh s₀ h) : ¬ ∀ x, G.Holds (G.run s₀ h) x := fun hall ↦
  let ⟨x, _, hx⟩ := hO h ho hf
  hx (hall x)

/-- CR9(b): if every offered item lies in a finite stock fixed in advance, openness fails. -/
theorem not_openFor_of_finite (C : Finset G.Item)
    (hC : ∀ h, G.Offered Offer s₀ h → G.Fresh s₀ h → ∀ x, Offer (G.run s₀ h) x → x ∈ C) :
    ¬ G.OpenFor Offer s₀ := by
  classical
  intro hO
  obtain ⟨h, hl, ho, hf⟩ := hO.exists_offered_fresh (C.card + 1)
  have hsub : h.toFinset ⊆ C := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hx)
    have e : h = h.take k ++ h.drop k := (List.take_append_drop k h).symm
    have ho' : G.Offered Offer s₀ (h.take k) := (e ▸ ho : G.Offered Offer s₀ _).of_append
    have hf' : G.Fresh s₀ (h.take k) := (e ▸ hf : G.Fresh s₀ _).of_append
    have hx' : Offer (G.run s₀ (h.take k)) h[k] := ho k hk
    exact hC _ ho' hf' _ hx'
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hf.nodup, hl] at hcard
  omega

end Growth

/-! ## CR10(a)(b): incidence structures with taking-in -/

/-- An incidence structure together with the relation "taking this item in at this stage gives
that stage" (N11). -/
structure StepIncidence extends Incidence.{u, v} where
  StepTo : Stage → Item → Stage → Prop

namespace StepIncidence

/-- An isomorphism of incidence structures that also preserves and reflects `StepTo`. -/
structure Iso (A : StepIncidence.{u, v}) (B : StepIncidence.{u', v'}) extends
    A.toIncidence.Iso B.toIncidence where
  stepTo_iff : ∀ s x s', A.StepTo s x s' ↔ B.StepTo (stage s) (item x) (stage s')

/-- Taking any item of the structure in at any of its stages gives one of its stages. -/
def Closed (A : StepIncidence.{u, v}) : Prop := ∀ s x, ∃ s', A.StepTo s x s'

namespace Iso

/-- The inverse isomorphism. -/
def symm {A : StepIncidence.{u, v}} {B : StepIncidence.{u', v'}} (e : A.Iso B) : B.Iso A where
  toIso := e.toIso.symm
  stepTo_iff s x s' := by
    show B.StepTo s x s' ↔ A.StepTo (e.stage.symm s) (e.item.symm x) (e.stage.symm s')
    simpa using (e.stepTo_iff (e.stage.symm s) (e.item.symm x) (e.stage.symm s')).symm

/-- The composite isomorphism. -/
def trans {A : StepIncidence.{u, v}} {B : StepIncidence.{u', v'}} {C : StepIncidence.{u'', v''}}
    (e : A.Iso B) (f : B.Iso C) : A.Iso C where
  toIso := e.toIso.trans f.toIso
  stepTo_iff s x s' := (e.stepTo_iff s x s').trans (f.stepTo_iff _ _ _)

/-- CR10(b): isomorphisms preserve closedness. -/
theorem closed_iff {A : StepIncidence.{u, v}} {B : StepIncidence.{u', v'}} (e : A.Iso B) :
    A.Closed ↔ B.Closed := by
  constructor
  · intro hA s x
    obtain ⟨s', hs'⟩ := hA (e.stage.symm s) (e.item.symm x)
    exact ⟨e.stage s', by simpa using (e.stepTo_iff _ _ _).mp hs'⟩
  · intro hB s x
    obtain ⟨s', hs'⟩ := hB (e.stage s) (e.item x)
    refine ⟨e.stage.symm s', (e.stepTo_iff _ _ _).mpr ?_⟩
    simpa using hs'

end Iso

/-- The standard structure of length `n` with taking-in: the `k`-th stage takes the `j`-th item in
to become the `max k (j + 1)`-th stage. -/
abbrev std (n : ℕ) : StepIncidence.{0, 0} where
  toIncidence := Incidence.std n
  StepTo k j k' := (k' : ℕ) = max (k : ℕ) (j + 1)

/-- Standard structures of equal lengths are isomorphic. -/
def Iso.stdCast {n m : ℕ} (e : n = m) : (std n).Iso (std m) where
  toIso := Incidence.Iso.stdCast e
  stepTo_iff _ _ _ := Iff.rfl

end StepIncidence

namespace Growth

variable (G : Growth.{u, v})

/-- The trace of `h` from `s₀` with taking-in (N11). -/
abbrev stepTrace (s₀ : G.Stage) (h : List G.Item) : StepIncidence.{u, v} where
  toIncidence := G.trace s₀ h
  StepTo s x s' := G.StepTo s x s'

variable {G} {s₀ : G.Stage} {h : List G.Item}

/-- CR10(a): a fresh max-rule trace with taking-in is isomorphic to the standard structure of
its length. -/
noncomputable def Fresh.ofStdStep (hf : G.Fresh s₀ h) (hc : G.MaxRule s₀ h) :
    (StepIncidence.std h.length).Iso (G.stepTrace s₀ h) where
  toIso := hf.ofStd
  stepTo_iff k j k' := by
    show (k' : ℕ) = max (k : ℕ) (j + 1) ↔
      G.StepTo (G.run s₀ (h.take k)) h[(j : ℕ)] (G.run s₀ (h.take k'))
    have hk : (k : ℕ) ≤ h.length := Nat.lt_succ_iff.mp k.2
    have hk' : (k' : ℕ) ≤ h.length := Nat.lt_succ_iff.mp k'.2
    have hm : max (k : ℕ) (j + 1) ≤ h.length := max_le hk j.2
    have hstep := hc k j hk j.2
    constructor
    · intro e
      rw [e]
      exact hstep
    · intro h'
      have e : G.Equivalent (G.run s₀ (h.take k')) (G.run s₀ (h.take (max (k : ℕ) (j + 1)))) :=
        h'.symm.trans hstep
      exact le_antisymm ((hf.le_iff hk').mp e.le) ((hf.le_iff hm).mp e.symm.le)

/-- CR10(a): fresh max-rule traces of equal lengths are isomorphic with taking-in. -/
noncomputable def stepTraceIso {G' : Growth.{u', v'}} {s₀' : G'.Stage} {h' : List G'.Item}
    (hf : G.Fresh s₀ h) (hc : G.MaxRule s₀ h) (hf' : G'.Fresh s₀' h')
    (hc' : G'.MaxRule s₀' h') (hl : h.length = h'.length) :
    (G.stepTrace s₀ h).Iso (G'.stepTrace s₀' h') :=
  (hf.ofStdStep hc).symm.trans ((StepIncidence.Iso.stdCast hl).trans (hf'.ofStdStep hc'))

/-- `stepTraceIso` extends `traceIso`. -/
theorem stepTraceIso_toIso {G' : Growth.{u', v'}} {s₀' : G'.Stage} {h' : List G'.Item}
    (hf : G.Fresh s₀ h) (hc : G.MaxRule s₀ h) (hf' : G'.Fresh s₀' h')
    (hc' : G'.MaxRule s₀' h') (hl : h.length = h'.length) :
    (stepTraceIso hf hc hf' hc' hl).toIso = traceIso hf hf' hl :=
  rfl

/-- CR10(b): a fresh max-rule trace is closed under taking-in. -/
theorem Fresh.closed (_hf : G.Fresh s₀ h) (hc : G.MaxRule s₀ h) : (G.stepTrace s₀ h).Closed := by
  rintro ⟨s, k, rfl⟩ ⟨x, j, rfl⟩
  have hk : (k : ℕ) ≤ h.length := Nat.lt_succ_iff.mp k.2
  have hm : max (k : ℕ) (j + 1) < h.length + 1 := Nat.lt_succ_of_le (max_le hk j.2)
  exact ⟨⟨G.stages s₀ h ⟨_, hm⟩, ⟨_, hm⟩, rfl⟩, hc k j hk j.2⟩

/-- CR10(d): in a fresh max-rule past, taking the `j`-th item in at the start already makes every
item up to the `j`-th hold: each item carries the earlier ones. -/
theorem MaxRule.holds_step_start (hs : G.MaxRule s₀ h) (hf : G.Fresh s₀ h) {i j : ℕ} (hij : i ≤ j)
    (hj : j < h.length) : G.Holds (G.step s₀ h[j]) (h[i]'(lt_of_le_of_lt hij hj)) := by
  have e := hs 0 j (Nat.zero_le _) hj
  rw [Nat.zero_max] at e
  exact (e _).mpr ((hf.holds_iff (lt_of_le_of_lt hij hj)).mpr (Nat.lt_succ_of_le hij))

end Growth

end MeaningDimension.Correspondence
