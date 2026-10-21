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
