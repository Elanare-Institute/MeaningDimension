import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.Nodup

/-!
# Growth systems and the traces of fresh pasts

Spec: `docs/correspondence_spec.md`, N1, N4, N5, CR1–CR3, CR6(a).

A growth system has stages, items, a relation "the item holds at the stage", and a step that takes
an item in. Taking an item in makes it hold, and what held keeps holding. A past (a finite list of
items) is *fresh* when no item holds at the stage that takes it in.

The trace of a past records the stages it passes through, the items it takes in, which of these
items hold at which of these stages, and the succession along the past. A fresh trace is
isomorphic to the standard structure of its length (`Fresh.ofStd`): the `j`-th item holds at the
`k`-th stage exactly when `j < k` (`Fresh.holds_iff`). Hence any two fresh traces of the same
length are isomorphic (`traceIso`), whatever the two growth systems are.

`not_predetermined` is the common form of ACSI's AC9 and of G5.6(b). It is not part of the
isomorphism.
-/

namespace MeaningDimension.Correspondence

universe u v u' v' u'' v''

/-- A growth system (N1). -/
structure Growth where
  Stage : Type u
  Item : Type v
  Holds : Stage → Item → Prop
  step : Stage → Item → Stage
  holds_step_self : ∀ s x, Holds (step s x) x
  holds_step_of_holds : ∀ {s y} (x), Holds s y → Holds (step s x) y

namespace Growth

variable (G : Growth.{u, v})

/-- The stage after the past `h` (in temporal order), starting from `s₀`. -/
def run (s₀ : G.Stage) (h : List G.Item) : G.Stage := h.foldl G.step s₀

/-- The stages that the past `h` passes through: the `k`-th one is the stage after the first `k`
items. -/
def stages (s₀ : G.Stage) (h : List G.Item) (k : Fin (h.length + 1)) : G.Stage :=
  G.run s₀ (h.take k)

/-- The past `h` from `s₀` is fresh: no item holds at the stage that takes it in (N4). -/
def Fresh (s₀ : G.Stage) (h : List G.Item) : Prop :=
  ∀ k (hk : k < h.length), ¬ G.Holds (G.run s₀ (h.take k)) h[k]

/-- Whatever holds at `s` holds at `s'`. -/
def Le (s s' : G.Stage) : Prop := ∀ x, G.Holds s x → G.Holds s' x

/-- The same items hold at `s` and `s'`. -/
def Equivalent (s s' : G.Stage) : Prop := ∀ x, G.Holds s x ↔ G.Holds s' x

variable {G}

theorem run_take_succ (s₀ : G.Stage) (h : List G.Item) {k : ℕ} (hk : k < h.length) :
    G.run s₀ (h.take (k + 1)) = G.step (G.run s₀ (h.take k)) h[k] := by
  rw [run, run, List.take_succ_eq_append_getElem hk, List.foldl_append]
  rfl

theorem le_foldl : ∀ (l : List G.Item) (s : G.Stage), G.Le s (l.foldl G.step s)
  | [], _ => fun _ hx ↦ hx
  | x :: l, s => fun y hy ↦ le_foldl l (G.step s x) y (G.holds_step_of_holds x hy)

theorem le_run_take (s₀ : G.Stage) (h : List G.Item) {k m : ℕ} (hkm : k ≤ m) :
    G.Le (G.run s₀ (h.take k)) (G.run s₀ (h.take m)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  rw [run, run, List.take_add, List.foldl_append]
  exact le_foldl _ _

theorem holds_run_take_succ (s₀ : G.Stage) (h : List G.Item) {k : ℕ} (hk : k < h.length) :
    G.Holds (G.run s₀ (h.take (k + 1))) h[k] := by
  rw [run_take_succ s₀ h hk]
  exact G.holds_step_self _ _

/-! ## CR1: the standard form of a fresh past -/

namespace Fresh

variable {s₀ : G.Stage} {h : List G.Item} (hf : G.Fresh s₀ h)
include hf

/-- CR1(a): the `j`-th item holds at the `k`-th stage exactly when `j < k`. -/
theorem holds_iff {k j : ℕ} (hj : j < h.length) :
    G.Holds (G.run s₀ (h.take k)) h[j] ↔ j < k := by
  constructor
  · intro hk
    by_contra hjk
    exact hf j hj (le_run_take s₀ h (not_lt.mp hjk) _ hk)
  · intro hjk
    exact le_run_take s₀ h (Nat.succ_le_of_lt hjk) _ (holds_run_take_succ s₀ h hj)

/-- CR1(b): the stages grow strictly along the past. -/
theorem le_iff {k m : ℕ} (hk : k ≤ h.length) :
    G.Le (G.run s₀ (h.take k)) (G.run s₀ (h.take m)) ↔ k ≤ m := by
  refine ⟨fun hle ↦ ?_, le_run_take s₀ h⟩
  by_contra hmk
  have hmk : m < k := not_le.mp hmk
  have hm : m < h.length := lt_of_lt_of_le hmk hk
  exact lt_irrefl m ((hf.holds_iff hm).mp (hle _ ((hf.holds_iff hm).mpr hmk)))

/-- CR1(c), as injectivity. -/
theorem get_injective : Function.Injective h.get := by
  have key : ∀ i j : Fin h.length, i < j → h.get i ≠ h.get j := fun i j hij e ↦ by
    have e' : h[(i : ℕ)] = h[(j : ℕ)] := by simpa using e
    exact hf j j.2 (e' ▸ (hf.holds_iff (k := j) i.2).mpr hij)
  intro i j e
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd e (key i j hij)
  · exact hij
  · exact absurd e.symm (key j i hij)

/-- CR1(c). -/
theorem nodup : h.Nodup := List.nodup_iff_injective_get.mpr hf.get_injective

/-- CR1(d). -/
theorem stages_injective : Function.Injective (G.stages s₀ h) := by
  intro k m e
  simp only [stages] at e
  have hk : (k : ℕ) ≤ h.length := Nat.lt_succ_iff.mp k.2
  have hm : (m : ℕ) ≤ h.length := Nat.lt_succ_iff.mp m.2
  exact Fin.ext <| le_antisymm ((hf.le_iff hk).mp fun x hx ↦ e ▸ hx)
    ((hf.le_iff hm).mp fun x hx ↦ e ▸ hx)

end Fresh

/-- CR6(a): the common form of AC9 and G5.6(b). If two items offered at `s` lead to stages at
which different items hold, no function of the stage gives the next stage for every offered
item. -/
theorem not_predetermined (G : Growth.{u, v}) (Offer : G.Stage → G.Item → Prop) {s : G.Stage}
    {x x' : G.Item} (hx : Offer s x) (hx' : Offer s x')
    (hne : ¬ G.Equivalent (G.step s x) (G.step s x')) (F : G.Stage → G.Stage) :
    ¬ ∀ y, Offer s y → G.Equivalent (G.step s y) (F s) := fun hall ↦
  hne fun z ↦ (hall x hx z).trans (hall x' hx' z).symm

end Growth

/-! ## Incidence structures and their isomorphisms -/

/-- Stages, items, which items hold at which stages, and which stage follows which by taking in
which item (N5). -/
structure Incidence where
  Stage : Type u
  Item : Type v
  Holds : Stage → Item → Prop
  Next : Stage → Item → Stage → Prop

namespace Incidence

/-- An isomorphism: bijections on stages and on items that preserve and reflect `Holds` and
`Next`. -/
structure Iso (A : Incidence.{u, v}) (B : Incidence.{u', v'}) where
  stage : A.Stage ≃ B.Stage
  item : A.Item ≃ B.Item
  holds_iff : ∀ s x, A.Holds s x ↔ B.Holds (stage s) (item x)
  next_iff : ∀ s x s', A.Next s x s' ↔ B.Next (stage s) (item x) (stage s')

namespace Iso

/-- The identity isomorphism. -/
def refl (A : Incidence.{u, v}) : A.Iso A :=
  ⟨Equiv.refl _, Equiv.refl _, fun _ _ ↦ Iff.rfl, fun _ _ _ ↦ Iff.rfl⟩

/-- The inverse isomorphism. -/
def symm {A : Incidence.{u, v}} {B : Incidence.{u', v'}} (e : A.Iso B) : B.Iso A where
  stage := e.stage.symm
  item := e.item.symm
  holds_iff s x := by simpa using (e.holds_iff (e.stage.symm s) (e.item.symm x)).symm
  next_iff s x s' := by
    simpa using (e.next_iff (e.stage.symm s) (e.item.symm x) (e.stage.symm s')).symm

/-- The composite isomorphism. -/
def trans {A : Incidence.{u, v}} {B : Incidence.{u', v'}} {C : Incidence.{u'', v''}}
    (e : A.Iso B) (f : B.Iso C) : A.Iso C where
  stage := e.stage.trans f.stage
  item := e.item.trans f.item
  holds_iff s x := (e.holds_iff s x).trans (f.holds_iff _ _)
  next_iff s x s' := (e.next_iff s x s').trans (f.next_iff _ _ _)

end Iso

/-- The standard structure of length `n`: the `j`-th item holds at the `k`-th stage exactly when
`j < k`, and the `k`-th stage takes in the `k`-th item to become the `(k+1)`-th stage. -/
abbrev std (n : ℕ) : Incidence.{0, 0} where
  Stage := Fin (n + 1)
  Item := Fin n
  Holds k j := (j : ℕ) < k
  Next k j k' := (j : ℕ) = k ∧ (k' : ℕ) = k + 1

/-- Standard structures of equal lengths are isomorphic. -/
def Iso.stdCast {n m : ℕ} (e : n = m) : (std n).Iso (std m) where
  stage := finCongr (congrArg (· + 1) e)
  item := finCongr e
  holds_iff _ _ := Iff.rfl
  next_iff _ _ _ := Iff.rfl

end Incidence

namespace Growth

variable (G : Growth.{u, v})

/-- The trace of the past `h` from `s₀` (N5). -/
abbrev trace (s₀ : G.Stage) (h : List G.Item) : Incidence.{u, v} where
  Stage := Set.range (G.stages s₀ h)
  Item := Set.range h.get
  Holds s x := G.Holds s x
  Next s x s' := ∃ k, ∃ hk : k < h.length, (s : G.Stage) = G.run s₀ (h.take k) ∧
    (x : G.Item) = h[k] ∧ (s' : G.Stage) = G.run s₀ (h.take (k + 1))

variable {G}

/-- CR2: a fresh trace is isomorphic to the standard structure of its length. The isomorphism
sends `k` to the `k`-th stage and `j` to the `j`-th item. -/
noncomputable def Fresh.ofStd {s₀ : G.Stage} {h : List G.Item} (hf : G.Fresh s₀ h) :
    (Incidence.std h.length).Iso (G.trace s₀ h) where
  stage := Equiv.ofInjective _ hf.stages_injective
  item := Equiv.ofInjective _ hf.get_injective
  holds_iff k j := (hf.holds_iff (k := k) j.2).symm
  next_iff k j k' := by
    simp only [Equiv.ofInjective_apply, stages, List.get_eq_getElem]
    constructor
    · rintro ⟨hj, hk'⟩
      exact ⟨j, j.2, by rw [hj], rfl, by rw [hk', hj]⟩
    · rintro ⟨m, hm, e₁, e₂, e₃⟩
      have hkm : k = ⟨m, by omega⟩ := hf.stages_injective e₁
      have hjm : j = ⟨m, hm⟩ := hf.get_injective e₂
      have hkm' : k' = ⟨m + 1, by omega⟩ := hf.stages_injective e₃
      subst hkm hjm hkm'
      exact ⟨rfl, rfl⟩

theorem Fresh.ofStd_stage {s₀ : G.Stage} {h : List G.Item} (hf : G.Fresh s₀ h)
    (k : Fin (h.length + 1)) : (hf.ofStd.stage k : G.Stage) = G.run s₀ (h.take k) :=
  rfl

theorem Fresh.ofStd_item {s₀ : G.Stage} {h : List G.Item} (hf : G.Fresh s₀ h)
    (j : Fin h.length) : (hf.ofStd.item j : G.Item) = h[(j : ℕ)] :=
  rfl

variable {G' : Growth.{u', v'}} {s₀ : G.Stage} {h : List G.Item} {s₀' : G'.Stage}
  {h' : List G'.Item}

/-- CR3: fresh traces of equal lengths are isomorphic, whatever the two growth systems are. -/
noncomputable def traceIso (hf : G.Fresh s₀ h) (hf' : G'.Fresh s₀' h')
    (hl : h.length = h'.length) : (G.trace s₀ h).Iso (G'.trace s₀' h') :=
  hf.ofStd.symm.trans ((Incidence.Iso.stdCast hl).trans hf'.ofStd)

/-- CR3: `traceIso` sends the `k`-th stage to the `k`-th stage. -/
theorem traceIso_stage (hf : G.Fresh s₀ h) (hf' : G'.Fresh s₀' h') (hl : h.length = h'.length)
    (k : Fin (h.length + 1)) :
    ((traceIso hf hf' hl).stage ⟨G.stages s₀ h k, k, rfl⟩ : G'.Stage) =
      G'.run s₀' (h'.take k) := by
  have e : hf.ofStd.symm.stage ⟨G.stages s₀ h k, k, rfl⟩ = k :=
    Equiv.ofInjective_symm_apply hf.stages_injective k
  show (hf'.ofStd.stage ((Incidence.Iso.stdCast hl).stage (hf.ofStd.symm.stage _)) : G'.Stage) = _
  rw [e]
  rfl

/-- CR3: `traceIso` sends the `j`-th item to the `j`-th item. -/
theorem traceIso_item (hf : G.Fresh s₀ h) (hf' : G'.Fresh s₀' h') (hl : h.length = h'.length)
    (j : Fin h.length) :
    ((traceIso hf hf' hl).item ⟨h.get j, j, rfl⟩ : G'.Item) = h'[(j : ℕ)]'(hl ▸ j.2) := by
  have e : hf.ofStd.symm.item ⟨h.get j, j, rfl⟩ = j :=
    Equiv.ofInjective_symm_apply hf.get_injective j
  show (hf'.ofStd.item ((Incidence.Iso.stdCast hl).item (hf.ofStd.symm.item _)) : G'.Item) = _
  rw [e]
  rfl

end Growth

end MeaningDimension.Correspondence
