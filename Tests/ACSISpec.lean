import MeaningDimension

/-!
# Specification tests for the formalization of absolute contradictory self-identity

Each `example` in the first half is transcribed from `docs/acsi_spec.md` §3, not from the
implementation. If an implementation changes its statement, the corresponding `example` stops
type-checking.

The second half instantiates the hypotheses (`E = ℕ` or `Bool`, `singletonMaking`, the empty self,
the past `[0, 1]`) to check that the theorems are not vacuous.
-/

open MeaningDimension.ACSI MeaningDimension.ACSI.Framework MeaningDimension.ACSI.Making

section Spec

variable {D E : Type} (F : Framework D) (M : Making E) (S S₀ : Self E) (e e' : E)

/-! ## AC1 -/

example (x y : D) : (pure : Framework D).Same x y := pure_same x y
example : (pure : Framework (Entity E)).Same (.inl S) (.inr e) := pure_same_subject_object S e
example : Subsingleton (pure : Framework D).Obj := inferInstance

/-! ## AC2 -/

example : ¬ (evaluated S).Same (.inl S) (.inr e) := evaluated_not_same_subject_object S e

/-! ## AC3 -/

example : (pure : Framework (Entity E)).Same (.inl S) (.inr e) ∧
    ¬ (evaluated S).Same (.inl S) (.inr e) :=
  subjectObject_frameworkRelative S e
example (x y : D) : ¬ (F.Same x y ∧ ¬ F.Same x y) := F.not_same_and_not_same x y

/-! ## AC4 -/

example : S.IsNew e ↔ S.eval e = ∅ := Self.isNew_iff_eval_eq_empty
example (he : S.IsNew e) (he' : S.IsNew e') : (evaluated S).Same (.inr e) (.inr e') :=
  evaluated_same_of_isNew he he'

/-! ## AC5 -/

example : e ∈ (M.incorporate S e).experiences := mem_incorporate_experiences S e
example : ∀ x ∈ S.experiences, x ∈ (M.incorporate S e).experiences :=
  experiences_subset_incorporate S e
example : (M.incorporate S e).Classifies e := classifies_incorporate S e
example (h : S.Classifies e') : (M.incorporate S e).Classifies e' :=
  classifies_incorporate_of_classifies h e
example (he : S.IsNew e) : M.generate S e ∉ S.categories := generate_notMem_of_isNew he
example (he' : e' ∉ M.generate S e) :
    ¬ (evaluated (M.incorporate S e)).Same (.inr e) (.inr e') :=
  evaluated_incorporate_not_same he'

/-! ## AC6 -/

example (inc : Self E → E → Self E) (h : FactorsThroughEval inc) (he : S.IsNew e)
    (he' : S.IsNew e') : inc S e = inc S e' :=
  h.eq_of_isNew he he'
example (he : S.IsNew e) (he' : S.IsNew e') (hne : M.generate S e ≠ M.generate S e') :
    ¬ FactorsThroughEval M.incorporate :=
  M.not_factorsThroughEval he he' hne
example (hne : e ≠ e') :
    (singletonMaking : Making E).generate S e ≠ singletonMaking.generate S e' :=
  singletonMaking_generate_ne S hne

/-! ## AC7 -/

section AC7
variable (h : List E)

example {k : ℕ} (hk : k < h.length) :
    M.run S₀ (h.take (k + 1)) = M.incorporate (M.run S₀ (h.take k)) h[k] :=
  run_take_succ M S₀ h hk
example {k : ℕ} (hk : k < h.length) : h[k] ∈ (M.run S₀ (h.take (k + 1))).experiences :=
  getElem_mem_run_take_succ M S₀ h hk
example (x : Node) : ¬ Prec h x x := prec_irrefl h x
example (x y : Node) (hxy : Prec h x y) : ¬ Prec h y x := prec_asymm hxy
example (x y : Node) : ¬ stageFramework.Mutual (Prec h) x y := stageFramework_not_mutual h x y
example (k m : ℕ) : selfIdentity.Same (.self k) (.self m) := selfIdentity_same_self k m
example (k m : ℕ) : ¬ selfIdentity.Same (.self k) (.exp m) := selfIdentity_not_same_self_exp k m
example (k m : ℕ) (hkm : k ≠ m) : ¬ selfIdentity.Same (.exp k) (.exp m) :=
  selfIdentity_not_same_exp_exp hkm
example {k : ℕ} (hk : k < h.length) : selfIdentity.Mutual (Base h) (.self 0) (.exp k) :=
  selfIdentity_mutual hk
example (hn : 0 < h.length) :
    selfIdentity.Lift (Prec h) (selfIdentity.obj (.self 0)) (selfIdentity.obj (.self 0)) :=
  selfIdentity_self_precedes_self hn
example {α : Type} (R : α → α → Prop) (hR : ∀ a b, R a b → ¬ R b a) (a b : α) :
    ¬ (R a b ∧ R b a) :=
  not_mutual_of_asymm hR a b

end AC7

/-! ## AC8 -/

example (hM : M.IsOpen S₀) (hS : M.Reachable S₀ S) :
    ∃ e, M.Reachable S₀ (M.incorporate S e) ∧ S.IsNew e ∧ (M.incorporate S e).Classifies e ∧
      M.generate S e ∉ S.categories :=
  hM.exists_next hS
example (hM : M.IsOpen S₀) : ¬ ∃ S, M.Reachable S₀ S ∧ ∀ e, S.Classifies e :=
  hM.not_exists_final
example [Infinite E] : (singletonMaking : Making E).IsOpen Self.empty := singletonMaking_isOpen

/-! ## AC9 -/

example (he : S.IsNew e) (he' : S.IsNew e') (hne : M.incorporate S e ≠ M.incorporate S e')
    (F : Self E → Self E) : ¬ ∀ x, S.IsNew x → M.incorporate S x = F S :=
  not_predetermined M he he' hne F

/-! ## AC10 -/

example : (pure : Framework (Entity E)).Same (.inl S) (.inl (M.incorporate S e)) :=
  pure_same_incorporate M S e
example (C : Finset (Set E)) (hC : ∀ S, M.Reachable S₀ S → ∀ e, M.generate S e ∈ C) :
    ¬ M.IsOpen S₀ :=
  not_isOpen_of_finite C hC

end Spec

/-! ## Non-vacuity -/

section NonVacuity

/-- The empty self classifies nothing. -/
theorem empty_isNew {E : Type} (e : E) : (Self.empty : Self E).IsNew e :=
  fun ⟨_, hc, _⟩ ↦ List.not_mem_nil hc

-- AC5(e), AC6(b): `singletonMaking` takes in two new experiences as different experiences, so it
-- does not factor through evaluation.
example :
    ¬ (evaluated ((singletonMaking : Making ℕ).incorporate Self.empty 0)).Same (.inr 0) (.inr 1) :=
  evaluated_incorporate_not_same (by simp [singletonMaking])

example : ¬ FactorsThroughEval (singletonMaking : Making ℕ).incorporate :=
  singletonMaking.not_factorsThroughEval (empty_isNew 0) (empty_isNew 1)
    (singletonMaking_generate_ne _ (by decide))

-- AC8: openness holds for `ℕ`, so no reachable self is final.
example : (singletonMaking : Making ℕ).IsOpen Self.empty := singletonMaking_isOpen

example : ¬ ∃ S, (singletonMaking : Making ℕ).Reachable Self.empty S ∧ ∀ e, S.Classifies e :=
  singletonMaking_isOpen.not_exists_final

-- AC9: the hypothesis holds for `singletonMaking` at the empty self.
example (F : Self ℕ → Self ℕ) :
    ¬ ∀ x, (Self.empty : Self ℕ).IsNew x →
      singletonMaking.incorporate Self.empty x = F Self.empty :=
  not_predetermined _ (empty_isNew 0) (empty_isNew 1) (by simp [incorporate, singletonMaking]) F

-- AC7(e)(f) for the past `[0, 1]`.
example : selfIdentity.Mutual (Base [0, 1]) (.self 0) (.exp 1) := selfIdentity_mutual (by decide)

example : selfIdentity.Lift (Prec [0, 1]) (selfIdentity.obj (.self 0))
    (selfIdentity.obj (.self 0)) :=
  selfIdentity_self_precedes_self (by decide)

-- AC10(c): the hypothesis holds for `Bool` (every generated category lies in `{{true}, {false}}`),
-- and openness fails.
example : ¬ (singletonMaking : Making Bool).IsOpen Self.empty :=
  not_isOpen_of_finite {{true}, {false}} fun _ _ e ↦ by cases e <;> simp [singletonMaking]

end NonVacuity
