import MeaningDimension

/-!
# Specification tests for CR (a partial structural isomorphism between ACSI and the Gödelian ascent)

Each `example` in the first half is transcribed from `docs/correspondence_spec.md` §2–§3, not from
the implementation. If an implementation changes its statement, the corresponding `example` stops
type-checking.

The second half instantiates the theorems at `singletonMaking : Making ℕ`, the empty self, `𝗜𝚺₁`
and `𝗣𝗔` to check that their hypotheses are satisfiable (the theorems are not vacuous).
-/

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open MeaningDimension.Godel MeaningDimension.ACSI MeaningDimension.Correspondence

section Spec

/-! ## §2 definitions -/

section Defs

variable (G : Growth) (s₀ : G.Stage) (h : List G.Item)

example : G.run s₀ h = h.foldl G.step s₀ := rfl
example (k : Fin (h.length + 1)) : G.stages s₀ h k = G.run s₀ (h.take k) := rfl
example : G.Fresh s₀ h ↔ ∀ k (hk : k < h.length), ¬ G.Holds (G.run s₀ (h.take k)) h[k] :=
  Iff.rfl
example (s s' : G.Stage) : G.Le s s' ↔ ∀ x, G.Holds s x → G.Holds s' x := Iff.rfl
example (s s' : G.Stage) : G.Equivalent s s' ↔ ∀ x, G.Holds s x ↔ G.Holds s' x := Iff.rfl

example (n : ℕ) (k : Fin (n + 1)) (j : Fin n) :
    (Incidence.std n).Holds k j ↔ (j : ℕ) < k := Iff.rfl
example (n : ℕ) (k k' : Fin (n + 1)) (j : Fin n) :
    (Incidence.std n).Next k j k' ↔ (j : ℕ) = k ∧ (k' : ℕ) = k + 1 := Iff.rfl

example : (G.trace s₀ h).Stage = Set.range (G.stages s₀ h) := rfl
example : (G.trace s₀ h).Item = Set.range h.get := rfl
example (s : (G.trace s₀ h).Stage) (x : (G.trace s₀ h).Item) :
    (G.trace s₀ h).Holds s x ↔ G.Holds s x := Iff.rfl
example (s s' : (G.trace s₀ h).Stage) (x : (G.trace s₀ h).Item) :
    (G.trace s₀ h).Next s x s' ↔ ∃ k, ∃ hk : k < h.length, (s : G.Stage) = G.run s₀ (h.take k) ∧
      (x : G.Item) = h[k] ∧ (s' : G.Stage) = G.run s₀ (h.take (k + 1)) := Iff.rfl

end Defs

section DefsInstances

variable {E : Type} (M : Making E) (T : ArithmeticTheory) [T.Δ₁]

example : (acsiGrowth M).Stage = Self E := rfl
example : (acsiGrowth M).Item = E := rfl
example : (acsiGrowth M).Holds = Self.Classifies := rfl
example : (acsiGrowth M).step = M.incorporate := rfl

example : godelGrowth.Stage = ArithmeticTheory := rfl
example : godelGrowth.Item = ArithmeticSentence := rfl
example (U : ArithmeticTheory) (σ : ArithmeticSentence) : godelGrowth.Holds U σ ↔ U ⊢ σ :=
  Iff.rfl
example (U : ArithmeticTheory) (σ : ArithmeticSentence) : godelGrowth.step U σ = U ∪ {σ} := rfl

example (n : ℕ) :
    conPast T n = (List.range n).map fun k ↦ (ascent T k).theory.consistent.val := rfl
example (U : ArithmeticTheory) (σ : ArithmeticSentence) :
    conOffer U σ ↔ ∃ d : U.Δ₁, σ = (@Theory.consistent ℒₒᵣ _ _ U d).val := Iff.rfl

end DefsInstances

/-! ## CR0 -/

section CR0

variable {E : Type} (M : Making E)

-- (a): the two axioms are AC5(b)(c).
example (S : Self E) (e : E) : (M.incorporate S e).Classifies e :=
  (acsiGrowth M).holds_step_self S e
example {S : Self E} {e' : E} (h : S.Classifies e') (e : E) :
    (M.incorporate S e).Classifies e' :=
  (acsiGrowth M).holds_step_of_holds e h
example : (acsiGrowth M).run = M.run := acsiGrowth_run M

-- (b)
example (T U : ArithmeticTheory) : godelGrowth.Le T U ↔ T ⪯ U := godelGrowth_le_iff T U
example (T U : ArithmeticTheory) : godelGrowth.Equivalent T U ↔ T ≊ U :=
  godelGrowth_equivalent_iff T U

end CR0

/-! ## CR1–CR3 -/

section CR123

variable {G : Growth} {s₀ : G.Stage} {h : List G.Item} (hf : G.Fresh s₀ h)

-- CR1
example {k j : ℕ} (hj : j < h.length) : G.Holds (G.run s₀ (h.take k)) h[j] ↔ j < k :=
  hf.holds_iff hj
example {k m : ℕ} (hk : k ≤ h.length) :
    G.Le (G.run s₀ (h.take k)) (G.run s₀ (h.take m)) ↔ k ≤ m :=
  hf.le_iff hk
example : h.Nodup := hf.nodup
example : Function.Injective (G.stages s₀ h) := hf.stages_injective

-- CR2
noncomputable example : (Incidence.std h.length).Iso (G.trace s₀ h) := hf.ofStd
example (k : Fin (h.length + 1)) : (hf.ofStd.stage k : G.Stage) = G.run s₀ (h.take k) :=
  hf.ofStd_stage k
example (j : Fin h.length) : (hf.ofStd.item j : G.Item) = h[(j : ℕ)] := hf.ofStd_item j

-- CR3
variable {G' : Growth} {s₀' : G'.Stage} {h' : List G'.Item} (hf' : G'.Fresh s₀' h')
  (hl : h.length = h'.length)

noncomputable example : (G.trace s₀ h).Iso (G'.trace s₀' h') := Growth.traceIso hf hf' hl
example (k : Fin (h.length + 1)) :
    ((Growth.traceIso hf hf' hl).stage ⟨G.stages s₀ h k, k, rfl⟩ : G'.Stage) =
      G'.run s₀' (h'.take k) :=
  Growth.traceIso_stage hf hf' hl k
example (j : Fin h.length) :
    ((Growth.traceIso hf hf' hl).item ⟨h.get j, j, rfl⟩ : G'.Item) = h'[(j : ℕ)]'(hl ▸ j.2) :=
  Growth.traceIso_item hf hf' hl j

end CR123

/-! ## CR4–CR5 -/

section CR45

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

-- CR4(a)
example (k : ℕ) : godelGrowth.run T (conPast T k) = (ascent T k).theory := run_conPast T k
example (n : ℕ) : (conPast T n).length = n := conPast_length T n
example {n k : ℕ} (hk : k < (conPast T n).length) :
    getElem (conPast T n) k hk = (ascent T k).theory.consistent.val :=
  conPast_getElem T hk
example (n : ℕ) : godelGrowth.Fresh T (conPast T n) := conPast_fresh T n

variable {E : Type} {M : Making E} {S₀ : Self E}

-- CR4(b)
example (hM : M.IsOpen S₀) (n : ℕ) : ∃ h : List E, h.length = n ∧ (acsiGrowth M).Fresh S₀ h :=
  exists_fresh_of_isOpen hM n

-- CR5(a)
variable {h : List E} (hf : (acsiGrowth M).Fresh S₀ h)

noncomputable example :
    ((acsiGrowth M).trace S₀ h).Iso (godelGrowth.trace T (conPast T h.length)) :=
  acsiGodelIso T hf
example (k : Fin (h.length + 1)) :
    ((acsiGodelIso T hf).stage ⟨M.run S₀ (h.take k), k, rfl⟩ : ArithmeticTheory) =
      (ascent T k).theory :=
  acsiGodelIso_stage T hf k
example (j : Fin h.length) :
    ((acsiGodelIso T hf).item ⟨h[(j : ℕ)], j, rfl⟩ : ArithmeticSentence) =
      (ascent T j).theory.consistent.val :=
  acsiGodelIso_item T hf j

-- CR5(b)
example (hM : M.IsOpen S₀) (n : ℕ) :
    ∃ h : List E, h.length = n ∧ (acsiGrowth M).Fresh S₀ h ∧
      Nonempty (((acsiGrowth M).trace S₀ h).Iso (godelGrowth.trace T (conPast T n))) :=
  exists_acsiGodelIso T hM n

end CR45

/-! ## CR6 -/

section CR6

-- (a)
example (G : Growth) (Offer : G.Stage → G.Item → Prop) {s : G.Stage} {x x' : G.Item}
    (hx : Offer s x) (hx' : Offer s x') (hne : ¬ G.Equivalent (G.step s x) (G.step s x'))
    (F : G.Stage → G.Stage) : ¬ ∀ y, Offer s y → G.Equivalent (G.step s y) (F s) :=
  Growth.not_predetermined G Offer hx hx' hne F

-- (b)
example {E : Type} (S : Self E) {e e' : E} (he : S.IsNew e) (hne : e ≠ e') :
    ¬ (acsiGrowth singletonMaking).Equivalent (singletonMaking.incorporate S e)
      (singletonMaking.incorporate S e') :=
  acsi_not_equivalent S he hne

-- (c)
variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

example : conOffer T T.consistent.val := conOffer_con T
example : conOffer T (twistedCon T) := conOffer_twistedCon T
example : ¬ godelGrowth.Equivalent (T ∪ {T.consistent.val}) (T ∪ {twistedCon T}) :=
  godel_not_equivalent T

end CR6

end Spec

/-! ## Non-vacuity -/

section NonVacuity

theorem empty_isNew' {E : Type} (e : E) : (Self.empty : Self E).IsNew e :=
  fun ⟨_, hc, _⟩ ↦ List.not_mem_nil hc

/-- The past `[0, 1]` is fresh for `singletonMaking` from the empty self. -/
theorem fresh_01 : (acsiGrowth (singletonMaking : Making ℕ)).Fresh Self.empty [0, 1] := by
  intro k hk
  match k, hk with
  | 0, _ => exact empty_isNew' 0
  | 1, _ =>
    rintro ⟨c, hc, h1⟩
    simp [Growth.run, Making.incorporate, singletonMaking, Self.empty] at hc
    subst hc
    simp at h1
  | k + 2, hk => simp at hk

-- CR4(b), CR5(b): openness holds for `singletonMaking` on `ℕ` from the empty self.
example (n : ℕ) : ∃ h : List ℕ, h.length = n ∧
    (acsiGrowth (singletonMaking : Making ℕ)).Fresh Self.empty h :=
  exists_fresh_of_isOpen Making.singletonMaking_isOpen n

example (n : ℕ) : ∃ h : List ℕ, h.length = n ∧
    (acsiGrowth (singletonMaking : Making ℕ)).Fresh Self.empty h ∧
      Nonempty (((acsiGrowth singletonMaking).trace Self.empty h).Iso
        (godelGrowth.trace 𝗣𝗔 (conPast 𝗣𝗔 n))) :=
  exists_acsiGodelIso 𝗣𝗔 Making.singletonMaking_isOpen n

example (n : ℕ) : ∃ h : List ℕ, h.length = n ∧
    (acsiGrowth (singletonMaking : Making ℕ)).Fresh Self.empty h ∧
      Nonempty (((acsiGrowth singletonMaking).trace Self.empty h).Iso
        (godelGrowth.trace 𝗜𝚺₁ (conPast 𝗜𝚺₁ n))) :=
  exists_acsiGodelIso 𝗜𝚺₁ Making.singletonMaking_isOpen n

-- CR4(a) at `𝗣𝗔` and `𝗜𝚺₁`.
example (n : ℕ) : godelGrowth.Fresh 𝗣𝗔 (conPast 𝗣𝗔 n) := conPast_fresh 𝗣𝗔 n
example (n : ℕ) : godelGrowth.Fresh 𝗜𝚺₁ (conPast 𝗜𝚺₁ n) := conPast_fresh 𝗜𝚺₁ n

-- CR5(a) for the concrete past `[0, 1]` and `𝗣𝗔`: the self after `[0, 1]` goes to `T₂`, and the
-- experience `1` goes to `Con(T₁)`.
noncomputable example : ((acsiGrowth singletonMaking).trace Self.empty [0, 1]).Iso
    (godelGrowth.trace 𝗣𝗔 (conPast 𝗣𝗔 2)) :=
  acsiGodelIso 𝗣𝗔 fresh_01

example : ((acsiGodelIso 𝗣𝗔 fresh_01).stage
    ⟨singletonMaking.run Self.empty ([0, 1].take 2), 2, rfl⟩ : ArithmeticTheory) =
      (ascent 𝗣𝗔 2).theory :=
  acsiGodelIso_stage 𝗣𝗔 fresh_01 2

example : ((acsiGodelIso 𝗣𝗔 fresh_01).item ⟨[0, 1][1], 1, rfl⟩ : ArithmeticSentence) =
      (ascent 𝗣𝗔 1).theory.consistent.val :=
  acsiGodelIso_item 𝗣𝗔 fresh_01 1

-- CR6(b) at the empty self and the experiences `0`, `1`.
example (F : Self ℕ → Self ℕ) :
    ¬ ∀ y, (Self.empty : Self ℕ).IsNew y →
      (acsiGrowth singletonMaking).Equivalent (singletonMaking.incorporate Self.empty y)
        (F Self.empty) :=
  Growth.not_predetermined (acsiGrowth singletonMaking) (fun S e ↦ S.IsNew e)
    (empty_isNew' 0) (empty_isNew' 1) (acsi_not_equivalent _ (empty_isNew' 0) (by decide)) F

-- CR6(c) at `𝗣𝗔`.
example (F : ArithmeticTheory → ArithmeticTheory) :
    ¬ ∀ σ, conOffer 𝗣𝗔 σ → godelGrowth.Equivalent (𝗣𝗔 ∪ {σ}) (F 𝗣𝗔) :=
  Growth.not_predetermined godelGrowth conOffer (conOffer_con 𝗣𝗔)
    (conOffer_twistedCon 𝗣𝗔) (godel_not_equivalent 𝗣𝗔) F

end NonVacuity

/-! # §6: CR7–CR10 (2026-10-22)

Transcribed from `docs/correspondence_spec.md` §6.2–§6.3, then instantiated at
`singletonMaking : Making ℕ`, `iicMaking : Making ℕ`, the empty self and `𝗣𝗔`. -/

section SpecExtension

/-! ## §6.2 definitions -/

section Defs

variable (G : Growth) (Offer : G.Stage → G.Item → Prop) (s₀ : G.Stage) (h : List G.Item)

example : G.Offered Offer s₀ h ↔ ∀ k (hk : k < h.length), Offer (G.run s₀ (h.take k)) h[k] :=
  Iff.rfl
example : G.OpenFor Offer s₀ ↔ ∀ h, G.Offered Offer s₀ h → G.Fresh s₀ h →
    ∃ x, Offer (G.run s₀ h) x ∧ ¬ G.Holds (G.run s₀ h) x :=
  Iff.rfl
example (s s' : G.Stage) (x : G.Item) : G.StepTo s x s' ↔ G.Equivalent (G.step s x) s' :=
  Iff.rfl
example : G.MaxRule s₀ h ↔ ∀ k j, k ≤ h.length → (hj : j < h.length) →
    G.StepTo (G.run s₀ (h.take k)) h[j] (G.run s₀ (h.take (max k (j + 1)))) :=
  Iff.rfl

example (A : StepIncidence) : A.Closed ↔ ∀ s x, ∃ s', A.StepTo s x s' := Iff.rfl
example (n : ℕ) : (StepIncidence.std n).toIncidence = Incidence.std n := rfl
example (n : ℕ) (k k' : Fin (n + 1)) (j : Fin n) :
    (StepIncidence.std n).StepTo k j k' ↔ (k' : ℕ) = max (k : ℕ) (j + 1) := Iff.rfl
example : (G.stepTrace s₀ h).toIncidence = G.trace s₀ h := rfl
example (s s' : (G.stepTrace s₀ h).Stage) (x : (G.stepTrace s₀ h).Item) :
    (G.stepTrace s₀ h).StepTo s x s' ↔ G.StepTo s x s' := Iff.rfl

example {A B : StepIncidence} (e : A.Iso B) (s : A.Stage) (x : A.Item) (s' : A.Stage) :
    A.StepTo s x s' ↔ B.StepTo (e.stage s) (e.item x) (e.stage s') :=
  e.stepTo_iff s x s'

example : godelStageGrowth.Stage = MeaningDimension.Godel.Stage := rfl
example : godelStageGrowth.Item = ArithmeticSentence := rfl
example (S : MeaningDimension.Godel.Stage) (σ : ArithmeticSentence) : godelStageGrowth.Holds S σ ↔ S.theory ⊢ σ :=
  Iff.rfl
example (S : MeaningDimension.Godel.Stage) (σ : ArithmeticSentence) :
    godelStageGrowth.step S σ =
      ⟨S.theory ∪ {σ}, Theory.Δ₁.add S.presentation (Theory.Δ₁.singleton σ)⟩ := rfl
example (S : MeaningDimension.Godel.Stage) (σ : ArithmeticSentence) : ownCon S σ ↔ σ = S.theory.consistent.val :=
  Iff.rfl

example {E : Type} [LinearOrder E] (S : Self E) (e : E) :
    (iicMaking : Making E).generate S e = Set.Iic e := rfl

end Defs

/-! ## CR7 -/

section CR7

variable {G : Growth} {Offer : G.Stage → G.Item → Prop} {s₀ : G.Stage} {h h₂ : List G.Item}

-- (a)
example (hf : G.Fresh s₀ (h ++ h₂)) : G.Fresh s₀ h := hf.of_append
example (ho : G.Offered Offer s₀ (h ++ h₂)) : G.Offered Offer s₀ h := ho.of_append

-- (b)
example {x : G.Item} (hf : G.Fresh s₀ h) (hx : ¬ G.Holds (G.run s₀ h) x) :
    G.Fresh s₀ (h ++ [x]) :=
  hf.append_singleton hx
example {x : G.Item} (ho : G.Offered Offer s₀ h) (hx : Offer (G.run s₀ h) x) :
    G.Offered Offer s₀ (h ++ [x]) :=
  ho.append_singleton hx

-- (c)
variable {G' : Growth} {s₀' : G'.Stage} {h' h₂' : List G'.Item}
  (hf : G.Fresh s₀ (h ++ h₂)) (hf' : G'.Fresh s₀' (h' ++ h₂')) (hl : h.length = h'.length)
  (hl₂ : (h ++ h₂).length = (h' ++ h₂').length)

example (k : Fin (h.length + 1)) :
    ((Growth.traceIso hf hf' hl₂).stage
        ⟨G.stages s₀ (h ++ h₂) (Fin.castLE (Growth.succ_length_le_append h h₂) k), _, rfl⟩ :
        G'.Stage) =
      ((Growth.traceIso hf.of_append hf'.of_append hl).stage ⟨G.stages s₀ h k, k, rfl⟩ :
        G'.Stage) :=
  Growth.traceIso_stage_extends hf hf' hl hl₂ k
example (j : Fin h.length) :
    ((Growth.traceIso hf hf' hl₂).item
        ⟨(h ++ h₂).get (Fin.castLE (Growth.length_le_append h h₂) j), _, rfl⟩ : G'.Item) =
      ((Growth.traceIso hf.of_append hf'.of_append hl).item ⟨h.get j, j, rfl⟩ : G'.Item) :=
  Growth.traceIso_item_extends hf hf' hl hl₂ j

end CR7

section CR7Instances

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
  {E : Type} {M : Making E} {S₀ : Self E} {h h₂ : List E}

-- (d)
example (hf : (acsiGrowth M).Fresh S₀ (h ++ h₂)) (k : Fin (h.length + 1)) :
    ((acsiGodelIso T hf).stage
        ⟨M.run S₀ ((h ++ h₂).take (Fin.castLE (Growth.succ_length_le_append h h₂) k)), _, rfl⟩ :
        ArithmeticTheory) =
      ((acsiGodelIso T hf.of_append).stage ⟨M.run S₀ (h.take k), k, rfl⟩ : ArithmeticTheory) :=
  acsiGodelIso_stage_extends T hf k
example (hf : (acsiGrowth M).Fresh S₀ (h ++ h₂)) (j : Fin h.length) :
    ((acsiGodelIso T hf).item
        ⟨(h ++ h₂).get (Fin.castLE (Growth.length_le_append h h₂) j), _, rfl⟩ :
        ArithmeticSentence) =
      ((acsiGodelIso T hf.of_append).item ⟨h[(j : ℕ)], j, rfl⟩ : ArithmeticSentence) :=
  acsiGodelIso_item_extends T hf j

-- (e)
example (hM : M.IsOpen S₀) (hf : (acsiGrowth M).Fresh S₀ h) :
    ∃ e, (acsiGrowth M).Fresh S₀ (h ++ [e]) :=
  exists_fresh_append_of_isOpen hM hf
example (n : ℕ) :
    conPast T (n + 1) = conPast T n ++ [(ascent T n).theory.consistent.val] :=
  conPast_succ T n

end CR7Instances

/-! ## CR8 -/

section CR8

-- (a)
example {G : Growth} {Offer : G.Stage → G.Item → Prop} {s₀ : G.Stage} (hO : G.OpenFor Offer s₀)
    (n : ℕ) : ∃ h : List G.Item, h.length = n ∧ G.Offered Offer s₀ h ∧ G.Fresh s₀ h :=
  hO.exists_offered_fresh n

-- (b)
example {E : Type} {M : Making E} {S₀ : Self E} (hM : M.IsOpen S₀) :
    (acsiGrowth M).OpenFor (fun S e ↦ S.IsNew e) S₀ :=
  acsi_openFor_of_isOpen hM

-- (c)
example (S : MeaningDimension.Godel.Stage) : godelStageGrowth.step S S.theory.consistent.val = S.next :=
  godelStageGrowth_step_con S

section Godel

variable (T : ArithmeticTheory) [T.Δ₁]

example {h : List ArithmeticSentence} (ho : godelStageGrowth.Offered ownCon (ascent T 0) h) :
    h = conPast T h.length :=
  offered_ownCon_eq T ho
example {h : List ArithmeticSentence} (ho : godelStageGrowth.Offered ownCon (ascent T 0) h) :
    godelStageGrowth.run (ascent T 0) h = ascent T h.length :=
  run_offered_ownCon T ho
example [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1] : godelStageGrowth.OpenFor ownCon (ascent T 0) :=
  godel_openFor T

end Godel

-- (d)
example {S : MeaningDimension.Godel.Stage} {σ σ' : ArithmeticSentence} (h : ownCon S σ) (h' : ownCon S σ') :
    σ = σ' :=
  ownCon_unique h h'
example {S : MeaningDimension.Godel.Stage} {σ : ArithmeticSentence} (h : ownCon S σ) :
    godelStageGrowth.step S σ = S.next :=
  step_of_ownCon h

-- (e)
example {E : Type} [Infinite E] {S : Self E}
    (hS : (singletonMaking : Making E).Reachable Self.empty S) (F : Self E → Self E) :
    ¬ ∀ e, S.IsNew e →
      (acsiGrowth singletonMaking).Equivalent (singletonMaking.incorporate S e) (F S) :=
  singleton_not_predetermined hS F

end CR8

/-! ## CR9 -/

section CR9

variable {G : Growth} {Offer : G.Stage → G.Item → Prop} {s₀ : G.Stage}

-- (a)
example (hO : G.OpenFor Offer s₀) {h : List G.Item} (ho : G.Offered Offer s₀ h)
    (hf : G.Fresh s₀ h) : ¬ ∀ x, G.Holds (G.run s₀ h) x :=
  hO.not_all_holds ho hf

-- (b)
example (C : Finset G.Item)
    (hC : ∀ h, G.Offered Offer s₀ h → G.Fresh s₀ h → ∀ x, Offer (G.run s₀ h) x → x ∈ C) :
    ¬ G.OpenFor Offer s₀ :=
  Growth.not_openFor_of_finite C hC

-- (c)
example {E : Type} {M : Making E} {S₀ : Self E} (hM : M.IsOpen S₀) (C : Finset E) :
    ∃ h : List E, (acsiGrowth M).Fresh S₀ h ∧ ∃ e, (M.run S₀ h).IsNew e ∧ e ∉ C :=
  acsi_exists_new_notMem hM C
example (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    (C : Finset ArithmeticSentence) : ∃ n, (ascent T n).theory.consistent.val ∉ C :=
  godel_exists_con_notMem T C

end CR9

/-! ## CR10 -/

section CR10

variable {G : Growth} {s₀ : G.Stage} {h : List G.Item} (hf : G.Fresh s₀ h) (hs : G.MaxRule s₀ h)

-- (a)
noncomputable example : (StepIncidence.std h.length).Iso (G.stepTrace s₀ h) := hf.ofStdStep hs
example (k : Fin (h.length + 1)) :
    ((hf.ofStdStep hs).stage k : G.Stage) = G.run s₀ (h.take k) := rfl
example (j : Fin h.length) : ((hf.ofStdStep hs).item j : G.Item) = h[(j : ℕ)] := rfl

variable {G' : Growth} {s₀' : G'.Stage} {h' : List G'.Item} (hf' : G'.Fresh s₀' h')
  (hs' : G'.MaxRule s₀' h') (hl : h.length = h'.length)

noncomputable example : (G.stepTrace s₀ h).Iso (G'.stepTrace s₀' h') :=
  Growth.stepTraceIso hf hs hf' hs' hl

-- (b)
example {A B : StepIncidence} (e : A.Iso B) : A.Closed ↔ B.Closed := e.closed_iff
example : (G.stepTrace s₀ h).Closed := hf.closed hs

-- (d), the abstract form
example {i j : ℕ} (hij : i ≤ j) (hj : j < h.length) :
    G.Holds (G.step s₀ h[j]) (h[i]'(lt_of_le_of_lt hij hj)) :=
  hs.holds_step_start hf hij hj

-- (c), (d): the Gödel side
section Godel

variable (T : ArithmeticTheory) [T.Δ₁]

example {i j : ℕ} (hij : i ≤ j) :
    𝗜𝚺₁ ⊢ (ascent T j).theory.consistent.val 🡒 (ascent T i).theory.consistent.val :=
  con_imp_of_le T hij
example [𝗜𝚺₁ ⪯ T] (k j : ℕ) :
    (ascent T k).theory ∪ {(ascent T j).theory.consistent.val} ≊
      (ascent T (max k (j + 1))).theory :=
  ascent_union_con_equiv T k j
example [𝗜𝚺₁ ⪯ T] (n : ℕ) : godelGrowth.MaxRule T (conPast T n) := conPast_maxRule T n
example [𝗜𝚺₁ ⪯ T] {i j : ℕ} (hij : i ≤ j) :
    T ∪ {(ascent T j).theory.consistent.val} ⊢ (ascent T i).theory.consistent.val :=
  union_con_proves_con T hij

end Godel

-- (e)
example {E : Type} {M : Making E} {S₀ S : Self E} (hS : M.Reachable S₀ S) (e : E) :
    M.Reachable S₀ (M.incorporate S e) :=
  hS.step e
example {E : Type} {S₀ : Self E} {h : List E}
    (hf : (acsiGrowth singletonMaking).Fresh S₀ h) (h2 : 2 ≤ h.length) :
    ¬ ((acsiGrowth singletonMaking).stepTrace S₀ h).Closed :=
  singleton_stepTrace_not_closed hf h2
example (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
    {E : Type} {S₀ : Self E} {h : List E}
    (hf : (acsiGrowth singletonMaking).Fresh S₀ h) (h2 : 2 ≤ h.length) :
    IsEmpty (((acsiGrowth singletonMaking).stepTrace S₀ h).Iso
      (godelGrowth.stepTrace T (conPast T h.length))) :=
  singleton_not_stepIso T hf h2

-- (f): the contrast example `iicMaking` (not an ACSI correspondence, E5)
example {E : Type} [LinearOrder E] (h : List E) (k : ℕ) (hk : k ≤ h.length) (x : E) :
    (iicMaking.run Self.empty (h.take k)).Classifies x ↔
      ∃ i, ∃ hi : i < k, x ≤ h[i]'(lt_of_lt_of_le hi hk) :=
  iicMaking_classifies_run h k hk x
example {E : Type} [LinearOrder E] {h : List E}
    (hf : (acsiGrowth iicMaking).Fresh Self.empty h) :
    (acsiGrowth iicMaking).MaxRule Self.empty h :=
  iicMaking_maxRule hf

section IicGodel

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]
  {E : Type} [LinearOrder E] {h : List E} (hf : (acsiGrowth iicMaking).Fresh Self.empty h)

noncomputable example : ((acsiGrowth iicMaking).stepTrace Self.empty h).Iso
    (godelGrowth.stepTrace T (conPast T h.length)) :=
  iicGodelStepIso T hf
example (k : Fin (h.length + 1)) :
    ((iicGodelStepIso T hf).stage ⟨iicMaking.run Self.empty (h.take k), k, rfl⟩ :
      ArithmeticTheory) = (ascent T k).theory :=
  iicGodelStepIso_stage T hf k
example (j : Fin h.length) :
    ((iicGodelStepIso T hf).item ⟨h[(j : ℕ)], j, rfl⟩ : ArithmeticSentence) =
      (ascent T j).theory.consistent.val :=
  iicGodelStepIso_item T hf j

end IicGodel

example : (iicMaking : Making ℕ).IsOpen Self.empty := iicMaking_isOpen

end CR10

end SpecExtension

/-! ## Non-vacuity (CR7–CR10) -/

section NonVacuityExtension

-- CR7(e), CR8(b): `singletonMaking` on `ℕ` from the empty self.
example : ∃ e, (acsiGrowth (singletonMaking : Making ℕ)).Fresh Self.empty ([0, 1] ++ [e]) :=
  exists_fresh_append_of_isOpen Making.singletonMaking_isOpen fresh_01
example : (acsiGrowth (singletonMaking : Making ℕ)).OpenFor (fun S e ↦ S.IsNew e) Self.empty :=
  acsi_openFor_of_isOpen Making.singletonMaking_isOpen

/-- The past `[0] ++ [1]` (that is, `[0, 1]`) is fresh for `singletonMaking`. -/
theorem fresh_0_1 : (acsiGrowth (singletonMaking : Making ℕ)).Fresh Self.empty ([0] ++ [1]) :=
  fresh_01

-- CR7(d) at `[0] ++ [1]` and `𝗣𝗔`.
example : True := by
  have := acsiGodelIso_stage_extends 𝗣𝗔 fresh_0_1 1
  trivial
example : True := by
  have := acsiGodelIso_item_extends 𝗣𝗔 fresh_0_1 0
  trivial

-- CR8(c), CR9(c) at `𝗣𝗔`.
example : godelStageGrowth.OpenFor ownCon (ascent 𝗣𝗔 0) := godel_openFor 𝗣𝗔
example (C : Finset ArithmeticSentence) : ∃ n, (ascent 𝗣𝗔 n).theory.consistent.val ∉ C :=
  godel_exists_con_notMem 𝗣𝗔 C

-- CR8(e) at `ℕ` and the empty self.
example (F : Self ℕ → Self ℕ) :
    ¬ ∀ e, (Self.empty : Self ℕ).IsNew e →
      (acsiGrowth singletonMaking).Equivalent (singletonMaking.incorporate Self.empty e)
        (F Self.empty) :=
  singleton_not_predetermined .base F

/-- The past `[0, 1]` is fresh for `iicMaking` from the empty self. -/
theorem iic_fresh_01 : (acsiGrowth (iicMaking : Making ℕ)).Fresh Self.empty [0, 1] := by
  intro k hk
  match k, hk with
  | 0, _ => exact empty_isNew' 0
  | 1, _ =>
    intro hc
    obtain ⟨i, hi, hle⟩ := (iicMaking_classifies_run [0, 1] 1 (by decide) 1).mp hc
    have : i = 0 := by omega
    subst this
    simp at hle
  | k + 2, hk => simp at hk

-- CR10(f) at `[0, 1]` and `𝗣𝗔`: the self after `[0, 1]` goes to `T₂`.
noncomputable example : ((acsiGrowth iicMaking).stepTrace Self.empty [0, 1]).Iso
    (godelGrowth.stepTrace 𝗣𝗔 (conPast 𝗣𝗔 2)) :=
  iicGodelStepIso 𝗣𝗔 iic_fresh_01
example : ((iicGodelStepIso 𝗣𝗔 iic_fresh_01).stage
    ⟨iicMaking.run Self.empty ([0, 1].take 2), 2, rfl⟩ : ArithmeticTheory) =
      (ascent 𝗣𝗔 2).theory :=
  iicGodelStepIso_stage 𝗣𝗔 iic_fresh_01 2

-- CR10(d) at `𝗣𝗔`: `𝗣𝗔 ∪ {Con(T₂)}` proves `Con(T₀)`.
example : 𝗣𝗔 ∪ {(ascent 𝗣𝗔 2).theory.consistent.val} ⊢ (ascent 𝗣𝗔 0).theory.consistent.val :=
  union_con_proves_con 𝗣𝗔 (by decide)

-- CR10(e) at `[0, 1]` and `𝗣𝗔`.
example : IsEmpty (((acsiGrowth singletonMaking).stepTrace Self.empty [0, 1]).Iso
    (godelGrowth.stepTrace 𝗣𝗔 (conPast 𝗣𝗔 2))) :=
  singleton_not_stepIso 𝗣𝗔 fresh_01 (by decide)

end NonVacuityExtension

/-! # §7: CR11–CR13 (2026-10-22)

Transcribed from `docs/correspondence_spec.md` §7.2–§7.3, then instantiated at `ℒᵣ`, the history
ℕ → ℤ → ℚ → ℝ → ℂ, `singletonMaking : Making ℕ`, ℝ, and `𝗣𝗔`. -/

section SpecMDG

open MeaningDimension.Generation

/-! ## §7.2 definitions -/

section Defs

variable {L : Language} (M : Struc L) (σ : Sentence L)

example : M.Holds σ ↔ M.carrier↓[L] ⊧ σ := Iff.rfl
example : mdgOffer M σ ↔
    ¬ M.Holds σ ∧ ∃ M' : Struc L, Nonempty (M.carrier ↪ₛ[L] M'.carrier) ∧ M'.Holds σ :=
  Iff.rfl

variable (G : MDGMaking L)

example (h : mdgOffer M σ) : Nonempty (M.carrier ↪ₛ[L] (G.gen M σ h).carrier) := G.emb M σ h
example (h : mdgOffer M σ) : (G.gen M σ h).Holds σ := G.holds_gen M σ h
example : G.step M σ = if h : mdgOffer M σ then G.gen M σ h else M := rfl
example (M₀ : Struc L) (h : List (Sentence L)) : G.run M₀ h = h.foldl G.step M₀ := rfl
example (M₀ : Struc L) (h : List (Sentence L)) :
    G.Offered M₀ h ↔ ∀ k (hk : k < h.length), mdgOffer (G.run M₀ (h.take k)) h[k] :=
  Iff.rfl

variable {n : ℕ} (c : MDGPast L n)

example (k : Fin n) : Nonempty ((c.stage k.castSucc).carrier ↪ₛ[L] (c.stage k.succ).carrier) :=
  c.emb k
example (k : Fin n) : IsExistential (c.demand k) := c.existential k
example (k : Fin n) : ¬ (c.stage k.castSucc).Holds (c.demand k) := c.not_holds k
example (k : Fin n) : (c.stage k.succ).Holds (c.demand k) := c.holds k
example : c.trace.Stage = Set.range c.stage := rfl
example : c.trace.Item = Set.range c.demand := rfl
example (s : c.trace.Stage) (x : c.trace.Item) : c.trace.Holds s x ↔ (s : Struc L).Holds x :=
  Iff.rfl
example (s s' : c.trace.Stage) (x : c.trace.Item) :
    c.trace.Next s x s' ↔ ∃ k : Fin n, (s : Struc L) = c.stage k.castSucc ∧
      (x : Sentence L) = c.demand k ∧ (s' : Struc L) = c.stage k.succ :=
  Iff.rfl

example (m : ℕ) : (OfferIncidence.std m).Stage = Unit := rfl
example (m : ℕ) : (OfferIncidence.std m).Item = Fin m := rfl
example (m : ℕ) (s : Unit) (x : Fin m) : (OfferIncidence.std m).Holds s x ↔ False := Iff.rfl
example (m : ℕ) (s : Unit) (x : Fin m) : (OfferIncidence.std m).Offer s x ↔ True := Iff.rfl
example {A B : OfferIncidence} (e : A.Iso B) (s : A.Stage) (x : A.Item) :
    A.Holds s x ↔ B.Holds (e.stage s) (e.item x) :=
  e.holds_iff s x
example {A B : OfferIncidence} (e : A.Iso B) (s : A.Stage) (x : A.Item) :
    A.Offer s x ↔ B.Offer (e.stage s) (e.item x) :=
  e.offer_iff s x
example {S I : Type} (Holds Offer : S → I → Prop) (s : S) {m : ℕ} (xs : Fin m ↪ I) :
    (offerAt Holds Offer s xs).Stage = {t // t = s} := rfl
example {S I : Type} (Holds Offer : S → I → Prop) (s : S) {m : ℕ} (xs : Fin m ↪ I) :
    (offerAt Holds Offer s xs).Item = Set.range xs := rfl

example : sentenceQ = “∃ x, x + x = 1” := rfl
example : padC 0 = sentenceC := rfl
example (k : ℕ) : padC (k + 1) = padC k ⋏ padC k := rfl

end Defs

/-! ## CR11 -/

section CR11

variable {L : Language}

-- (a)
example : Nonempty (MDGMaking L) := MDGMaking.nonempty L

variable (G : MDGMaking L) {M : Struc L} {σ : Sentence L} (h : mdgOffer M σ)

-- (b)
example : G.step M σ = G.gen M σ h := G.step_of_offer h

-- (c)
example {τ : Sentence L} (hτ : IsExistential τ) (hM : M.Holds τ) : (G.gen M σ h).Holds τ :=
  G.holds_gen_of_isExistential h hτ hM

end CR11

/-! ## CR12 -/

section CR12

variable {L : Language} {n : ℕ} (c : MDGPast L n)

-- (a)
example (k : Fin (n + 1)) (j : Fin n) : (c.stage k).Holds (c.demand j) ↔ (j : ℕ) < k :=
  c.holds_iff k j
example : Function.Injective c.stage := c.stage_injective
example : Function.Injective c.demand := c.demand_injective

-- (b)
noncomputable example : (Incidence.std n).Iso c.trace := c.ofStd
example (k : Fin (n + 1)) : (c.ofStd.stage k : Struc L) = c.stage k := c.ofStd_stage k
example (j : Fin n) : (c.ofStd.item j : Sentence L) = c.demand j := c.ofStd_item j

-- (c)
example (G : MDGMaking L) (M₀ : Struc L) (h : List (Sentence L)) (ho : G.Offered M₀ h)
    (hex : ∀ σ ∈ h, IsExistential σ) (k : Fin (h.length + 1)) :
    (G.toPast M₀ h ho hex).stage k = G.run M₀ (h.take k) :=
  G.toPast_stage M₀ h ho hex k
example (G : MDGMaking L) (M₀ : Struc L) (h : List (Sentence L)) (ho : G.Offered M₀ h)
    (hex : ∀ σ ∈ h, IsExistential σ) (j : Fin h.length) :
    (G.toPast M₀ h ho hex).demand j = h[(j : ℕ)] :=
  G.toPast_demand M₀ h ho hex j

-- (d)
section Three

variable {E : Type} {M : Making E} {S₀ : Self E} {h : List E}
  (hf : (acsiGrowth M).Fresh S₀ h) (c' : MDGPast L h.length)

noncomputable example : c'.trace.Iso ((acsiGrowth M).trace S₀ h) := mdgAcsiIso c' hf
example (k : Fin (h.length + 1)) :
    ((mdgAcsiIso c' hf).stage ⟨c'.stage k, k, rfl⟩ : Self E) = M.run S₀ (h.take k) :=
  mdgAcsiIso_stage c' hf k
example (j : Fin h.length) :
    ((mdgAcsiIso c' hf).item ⟨c'.demand j, j, rfl⟩ : E) = h[(j : ℕ)] :=
  mdgAcsiIso_item c' hf j

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

noncomputable example : c.trace.Iso (godelGrowth.trace T (conPast T n)) := mdgGodelIso T c
example (k : Fin (n + 1)) :
    ((mdgGodelIso T c).stage ⟨c.stage k, k, rfl⟩ : ArithmeticTheory) = (ascent T k).theory :=
  mdgGodelIso_stage T c k
example (j : Fin n) :
    ((mdgGodelIso T c).item ⟨c.demand j, j, rfl⟩ : ArithmeticSentence) =
      (ascent T j).theory.consistent.val :=
  mdgGodelIso_item T c j

end Three

-- (e)
example : historyPast.stage = ![natS, intS, ratS, realS, complexS] := rfl
example : historyPast.demand = ![sentenceZ, sentenceQ, sentenceR, sentenceC] := rfl

end CR12

/-! ## CR13 -/

section CR13

-- (a)
section A

variable {S I : Type} {Holds Offer : S → I → Prop} {s : S} {m : ℕ} {xs : Fin m ↪ I}
  (hxs : ∀ i, Offer s (xs i)) (hnew : ∀ x, Offer s x → ¬ Holds s x)

noncomputable example : (OfferIncidence.std m).Iso (offerAt Holds Offer s xs) :=
  offerAtIso hxs hnew
example (u : Unit) : ((offerAtIso hxs hnew).stage u : S) = s := offerAtIso_stage hxs hnew u
example (i : Fin m) : ((offerAtIso hxs hnew).item i : I) = xs i := offerAtIso_item hxs hnew i
example : Nonempty ((OfferIncidence.std m).Iso (offerAt Holds Offer s xs)) :=
  offerAt_iso hxs hnew

end A

-- (b)
example {E : Type} [Infinite E] (M : Making E) (m : ℕ) :
    ∃ xs : Fin m ↪ E, Nonempty ((OfferIncidence.std m).Iso
      (offerAt (acsiGrowth M).Holds (fun S e ↦ S.IsNew e) Self.empty xs)) :=
  acsi_offerIso M m

-- (c)
example (m : ℕ) : ∃ xs : Fin m ↪ Sentence ℒᵣ,
    Nonempty ((OfferIncidence.std m).Iso (offerAt Struc.Holds mdgOffer realS xs)) :=
  mdg_offerIso m

-- (d)
example (S : MeaningDimension.Godel.Stage) (xs : Fin 2 ↪ ArithmeticSentence) :
    IsEmpty ((OfferIncidence.std 2).Iso (offerAt godelStageGrowth.Holds ownCon S xs)) :=
  godel_not_offerIso S xs

end CR13

end SpecMDG

/-! ## Non-vacuity (CR11–CR13) -/

section NonVacuityMDG

open MeaningDimension.Generation

-- CR11(a) at `ℒᵣ`.
example : Nonempty (MDGMaking ℒᵣ) := MDGMaking.nonempty ℒᵣ

-- CR12(e): the history ℕ → ℤ → ℚ → ℝ → ℂ, with ACSI and with `𝗣𝗔`.
noncomputable example : historyPast.trace.Iso (godelGrowth.trace 𝗣𝗔 (conPast 𝗣𝗔 4)) :=
  mdgGodelIso 𝗣𝗔 historyPast
example : ((mdgGodelIso 𝗣𝗔 historyPast).stage ⟨complexS, 4, rfl⟩ : ArithmeticTheory) =
    (ascent 𝗣𝗔 4).theory :=
  mdgGodelIso_stage 𝗣𝗔 historyPast 4
example : ((mdgGodelIso 𝗣𝗔 historyPast).item ⟨sentenceC, 3, rfl⟩ : ArithmeticSentence) =
    (ascent 𝗣𝗔 3).theory.consistent.val :=
  mdgGodelIso_item 𝗣𝗔 historyPast 3
theorem singleton_classifies_foldl {E : Type} (x : E) :
    ∀ (l : List E) (S : Self E),
      (l.foldl (singletonMaking : Making E).incorporate S).Classifies x ↔ S.Classifies x ∨ x ∈ l
  | [], S => by simp
  | a :: l, S => by
    rw [List.foldl_cons, singleton_classifies_foldl x l, classifies_incorporate_iff]
    simp only [singletonMaking, Set.mem_singleton_iff, List.mem_cons]
    tauto

/-- The past `[0, 1, 2, 3]` is fresh for `singletonMaking` from the empty self. -/
theorem fresh_0123 : (acsiGrowth (singletonMaking : Making ℕ)).Fresh Self.empty [0, 1, 2, 3] := by
  intro k hk
  show ¬ (([0, 1, 2, 3].take k).foldl singletonMaking.incorporate Self.empty).Classifies _
  rw [singleton_classifies_foldl]
  have hS : ∀ x, ¬ (Self.empty : Self ℕ).Classifies x := fun x ↦ empty_isNew' x
  simp only [List.length_cons, List.length_nil] at hk
  interval_cases k <;> simp [hS]

noncomputable example : historyPast.trace.Iso
    ((acsiGrowth singletonMaking).trace Self.empty [0, 1, 2, 3]) :=
  mdgAcsiIso historyPast fresh_0123

-- CR13(b) at `ℕ`, (c), (d) at `𝗣𝗔`.
example (m : ℕ) : ∃ xs : Fin m ↪ ℕ, Nonempty ((OfferIncidence.std m).Iso
    (offerAt (acsiGrowth (singletonMaking : Making ℕ)).Holds (fun S e ↦ S.IsNew e)
      Self.empty xs)) :=
  acsi_offerIso singletonMaking m
example (xs : Fin 2 ↪ ArithmeticSentence) :
    IsEmpty ((OfferIncidence.std 2).Iso (offerAt godelStageGrowth.Holds ownCon (ascent 𝗣𝗔 0) xs)) :=
  godel_not_offerIso (ascent 𝗣𝗔 0) xs

end NonVacuityMDG
