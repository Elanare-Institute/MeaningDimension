import MeaningDimension.ACSI.SubjectObject
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Incorporation: the self as made and as making

Spec: `docs/acsi_spec.md`, M5, M7, AC5, AC6, AC8, AC9, AC10.

A making (作る働き) generates, from a self and an experience, a category that contains the
experience. Incorporation stores the experience and adds the generated category to the cognitive
system. The self is *made* (作られたもの): it is built from the experiences it stores. It is also
*making* (作るもの): through incorporation it remakes its own cognitive system, and the category
it generates may depend on what it has become.

* AC5: incorporation stores the experience and makes it classifiable; a totally new experience
  yields a category that the cognitive system did not have.
* AC6: an incorporation that sees only the evaluated experience (`Self.eval`) takes in all totally
  new experiences alike. Taking them in as different experiences requires the experience before
  evaluation.
* AC8: if every reachable self meets a totally new experience (`Making.IsOpen`), no reachable self
  is final.
* AC9: incorporation is not a `next : Self E → Self E` fixed in advance.
* AC10: staying in one framework stops generation; so does a finite stock of possible categories
  fixed in advance.

The future is not given as an infinite stream of experiences (M7): statements about what comes
next have the form "for every reachable self there is an experience".
-/

namespace MeaningDimension.ACSI

universe u

variable {E : Type u}

/-- A making: generates, from a self and an experience, a category containing the experience
(M5). -/
structure Making (E : Type u) where
  generate : Self E → E → Set E
  mem_generate : ∀ S e, e ∈ generate S e

namespace Making

variable (M : Making E)

/-- Incorporation: store `e` and add the generated category to the cognitive system. -/
def incorporate (S : Self E) (e : E) : Self E :=
  ⟨e :: S.experiences, M.generate S e :: S.categories⟩

/-- The self after the past `h` (in temporal order), starting from `S₀`. -/
def run (S₀ : Self E) (h : List E) : Self E := h.foldl M.incorporate S₀

/-- `S` is reached from `S₀` by finitely many incorporations. -/
inductive Reachable (S₀ : Self E) : Self E → Prop
  | base : Reachable S₀ S₀
  | step {S : Self E} (e : E) : Reachable S₀ S → Reachable S₀ (M.incorporate S e)

/-- Openness: every self reachable from `S₀` meets an experience that is totally new for it. -/
def IsOpen (S₀ : Self E) : Prop := ∀ S, M.Reachable S₀ S → ∃ e, S.IsNew e

/-! ## AC5: the self as made -/

variable {M}

/-- AC5(a). -/
theorem mem_incorporate_experiences (S : Self E) (e : E) :
    e ∈ (M.incorporate S e).experiences :=
  List.mem_cons_self

/-- AC5(a): earlier experiences are kept. -/
theorem experiences_subset_incorporate (S : Self E) (e : E) :
    ∀ x ∈ S.experiences, x ∈ (M.incorporate S e).experiences :=
  fun _ hx ↦ List.mem_cons_of_mem _ hx

/-- AC5(b). -/
theorem classifies_incorporate (S : Self E) (e : E) : (M.incorporate S e).Classifies e :=
  ⟨M.generate S e, List.mem_cons_self, M.mem_generate S e⟩

/-- AC5(c). -/
theorem classifies_incorporate_of_classifies {S : Self E} {e' : E} (h : S.Classifies e')
    (e : E) : (M.incorporate S e).Classifies e' :=
  let ⟨c, hc, hc'⟩ := h
  ⟨c, List.mem_cons_of_mem _ hc, hc'⟩

/-- AC5(d): the category generated from a totally new experience is new to the cognitive
system. -/
theorem generate_notMem_of_isNew {S : Self E} {e : E} (he : S.IsNew e) :
    M.generate S e ∉ S.categories :=
  fun h ↦ he ⟨_, h, M.mem_generate S e⟩

/-- AC5(e): after incorporation, the framework tells `e` apart from experiences outside the
generated category. -/
theorem evaluated_incorporate_not_same {S : Self E} {e e' : E} (he' : e' ∉ M.generate S e) :
    ¬ (evaluated (M.incorporate S e)).Same (.inr e) (.inr e') := fun h ↦
  he' ((h _ (inCategory_mem_evaluated (List.mem_cons_self (a := M.generate S e)))).mp
    (M.mem_generate S e))

end Making

/-! ## AC6: through the experience before evaluation -/

/-- The incorporation `inc` depends only on the evaluated experience, not on the experience
itself. -/
def FactorsThroughEval (inc : Self E → E → Self E) : Prop :=
  ∃ g : Self E → Set (Set E) → Self E, ∀ S e, inc S e = g S (S.eval e)

/-- AC6(a): an incorporation that sees only the evaluated experience takes in all totally new
experiences alike. -/
theorem FactorsThroughEval.eq_of_isNew {inc : Self E → E → Self E} (h : FactorsThroughEval inc)
    {S : Self E} {e e' : E} (he : S.IsNew e) (he' : S.IsNew e') : inc S e = inc S e' := by
  obtain ⟨g, hg⟩ := h
  rw [hg, hg, Self.isNew_iff_eval_eq_empty.mp he, Self.isNew_iff_eval_eq_empty.mp he']

/-- AC6(b): a making that generates different categories from two totally new experiences does
not factor through evaluation. -/
theorem Making.not_factorsThroughEval (M : Making E) {S : Self E} {e e' : E} (he : S.IsNew e)
    (he' : S.IsNew e') (hne : M.generate S e ≠ M.generate S e') :
    ¬ FactorsThroughEval M.incorporate := fun h ↦ by
  have := h.eq_of_isNew he he'
  simp only [Making.incorporate, Self.mk.injEq, List.cons.injEq] at this
  exact hne this.2.1

/-- The making that generates, from an experience, the category consisting of it alone. -/
def singletonMaking : Making E := ⟨fun _ e ↦ {e}, fun _ _ ↦ rfl⟩

/-- AC6(c). -/
theorem singletonMaking_generate_ne (S : Self E) {e e' : E} (hne : e ≠ e') :
    (singletonMaking : Making E).generate S e ≠ singletonMaking.generate S e' :=
  fun h ↦ hne (Set.singleton_eq_singleton_iff.mp h)

/-! ## AC8: non-finality -/

namespace Making

variable {M : Making E} {S₀ : Self E}

/-- AC8(a). -/
theorem IsOpen.exists_next (hM : M.IsOpen S₀) {S : Self E} (hS : M.Reachable S₀ S) :
    ∃ e, M.Reachable S₀ (M.incorporate S e) ∧ S.IsNew e ∧ (M.incorporate S e).Classifies e ∧
      M.generate S e ∉ S.categories :=
  let ⟨e, he⟩ := hM S hS
  ⟨e, hS.step e, he, classifies_incorporate S e, generate_notMem_of_isNew he⟩

/-- AC8(b): no reachable self classifies every experience. -/
theorem IsOpen.not_exists_final (hM : M.IsOpen S₀) :
    ¬ ∃ S, M.Reachable S₀ S ∧ ∀ e, S.Classifies e := fun ⟨S, hS, hall⟩ ↦
  let ⟨e, he⟩ := hM S hS
  he (hall e)

theorem reachable_singletonMaking_categories {S : Self E}
    (hS : (singletonMaking : Making E).Reachable Self.empty S) :
    S.categories = S.experiences.map fun a ↦ {a} := by
  induction hS with
  | base => rfl
  | step e _ ih => simp [incorporate, singletonMaking, ih]

/-- AC8(c): for infinitely many possible experiences, `singletonMaking` is open from the empty
self (the hypothesis of AC8 is satisfiable). -/
theorem singletonMaking_isOpen [Infinite E] :
    (singletonMaking : Making E).IsOpen Self.empty := by
  classical
  intro S hS
  obtain ⟨e, he⟩ := Infinite.exists_notMem_finset S.experiences.toFinset
  refine ⟨e, ?_⟩
  rintro ⟨c, hc, hec⟩
  rw [reachable_singletonMaking_categories hS] at hc
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
  rw [Set.mem_singleton_iff.mp hec] at he
  exact he (List.mem_toFinset.mpr ha)

/-! ## AC9: not a `next` fixed in advance -/

/-- AC9. -/
theorem not_predetermined (M : Making E) {S : Self E} {e e' : E} (he : S.IsNew e)
    (he' : S.IsNew e') (hne : M.incorporate S e ≠ M.incorporate S e') (F : Self E → Self E) :
    ¬ ∀ x, S.IsNew x → M.incorporate S x = F S := fun hall ↦
  hne ((hall e he).trans (hall e' he').symm)

/-! ## AC10: staying in one framework, or a finite stock of categories, stops generation -/

/-- AC10(a): in the pure framework, the self after incorporation is the same as before. -/
theorem pure_same_incorporate (M : Making E) (S : Self E) (e : E) :
    (Framework.pure : Framework (Entity E)).Same (.inl S) (.inl (M.incorporate S e)) :=
  Framework.pure_same _ _

open Classical in
/-- AC10(c): if every category that can be generated lies in a finite set fixed in advance,
openness fails. -/
theorem not_isOpen_of_finite (C : Finset (Set E))
    (hC : ∀ S, M.Reachable S₀ S → ∀ e, M.generate S e ∈ C) : ¬ M.IsOpen S₀ := by
  intro hM
  have key : ∀ n, ∃ S, M.Reachable S₀ S ∧ n ≤ (C.filter (· ∈ S.categories)).card := by
    intro n
    induction n with
    | zero => exact ⟨S₀, .base, Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨S, hS, hn⟩ := ih
      obtain ⟨e, he⟩ := hM S hS
      have hcC : M.generate S e ∈ C := hC S hS e
      have hcS : M.generate S e ∉ C.filter (· ∈ S.categories) := by
        simpa using fun _ ↦ generate_notMem_of_isNew he
      have hsub : insert (M.generate S e) (C.filter (· ∈ S.categories)) ⊆
          C.filter (· ∈ (M.incorporate S e).categories) := by
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_filter, incorporate, List.mem_cons] at hc ⊢
        rcases hc with rfl | ⟨hc, hc'⟩
        · exact ⟨hcC, .inl rfl⟩
        · exact ⟨hc, .inr hc'⟩
      refine ⟨_, hS.step e, ?_⟩
      calc n + 1 ≤ (C.filter (· ∈ S.categories)).card + 1 := by omega
        _ = (insert (M.generate S e) (C.filter (· ∈ S.categories))).card :=
          (Finset.card_insert_of_notMem hcS).symm
        _ ≤ _ := Finset.card_le_card hsub
  obtain ⟨S, _, hS⟩ := key (C.card + 1)
  have := Finset.card_filter_le C (· ∈ S.categories)
  omega

end Making

end MeaningDimension.ACSI
