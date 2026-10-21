import MeaningDimension.ACSI.Framework
import Mathlib.Data.Set.Insert

/-!
# The self, evaluation, and the subject–object division

Spec: `docs/acsi_spec.md`, M3–M4, AC1(a), AC2, AC3(a), AC4.

A self (自己) consists of the experiences it has stored and its cognitive system (認識体系), a
list of categories (sets of experiences). An experience is *totally new* (全く新しい) for a self
when none of its categories contains it.

The framework `evaluated S` is the ordinary framework after evaluation by `S`: it tells apart the
side that evaluates (主) from what is evaluated (客), and sorts experiences by the categories of
`S`. The same sentence "the self is the experience" is true in the pure framework and false in
`evaluated S` (`subjectObject_frameworkRelative`).
-/

namespace MeaningDimension.ACSI

universe u

/-- A self: the experiences it has stored and its categories (M4). -/
structure Self (E : Type u) where
  experiences : List E
  categories : List (Set E)

namespace Self

variable {E : Type u}

/-- The self that has stored nothing and has no category. -/
def empty : Self E := ⟨[], []⟩

/-- The self `S` can classify `e`: some category of `S` contains `e`. -/
def Classifies (S : Self E) (e : E) : Prop := ∃ c ∈ S.categories, e ∈ c

/-- `e` is totally new for `S`: no category of `S` contains it. -/
def IsNew (S : Self E) (e : E) : Prop := ¬ S.Classifies e

/-- The evaluation of `e` by `S`: the categories of `S` that contain `e`. -/
def eval (S : Self E) (e : E) : Set (Set E) := {c | c ∈ S.categories ∧ e ∈ c}

/-- AC4(a). -/
theorem isNew_iff_eval_eq_empty {S : Self E} {e : E} : S.IsNew e ↔ S.eval e = ∅ := by
  simp [IsNew, Classifies, eval, Set.eq_empty_iff_forall_notMem]

end Self

/-- The two sides of an experience: the self (`inl`, 主) and the experience (`inr`, 客). -/
abbrev Entity (E : Type u) := Self E ⊕ E

variable {E : Type u}

/-- Being the side that evaluates (主). -/
def isSubject : Entity E → Prop
  | .inl _ => True
  | .inr _ => False

/-- Being an experience that falls under the category `c`. -/
def inCategory (c : Set E) : Entity E → Prop
  | .inl _ => False
  | .inr x => x ∈ c

/-- The ordinary framework after evaluation by `S` (M3). -/
def evaluated (S : Self E) : Framework (Entity E) :=
  ⟨insert isSubject {P | ∃ c ∈ S.categories, P = inCategory c}⟩

theorem isSubject_mem_evaluated (S : Self E) : isSubject ∈ (evaluated S).preds :=
  Set.mem_insert _ _

theorem inCategory_mem_evaluated {S : Self E} {c : Set E} (hc : c ∈ S.categories) :
    inCategory c ∈ (evaluated S).preds :=
  Set.mem_insert_of_mem _ ⟨c, hc, rfl⟩

/-- AC1(a), instance: before evaluation, the self and the experience are the same
(主客未分). -/
theorem pure_same_subject_object (S : Self E) (e : E) :
    (Framework.pure : Framework (Entity E)).Same (.inl S) (.inr e) :=
  Framework.pure_same _ _

/-- AC2: after evaluation, the self and the experience are told apart. -/
theorem evaluated_not_same_subject_object (S : Self E) (e : E) :
    ¬ (evaluated S).Same (.inl S) (.inr e) := fun h ↦
  ((h isSubject (isSubject_mem_evaluated S)).mp trivial : isSubject (Sum.inr e : Entity E))

/-- AC3(a): the sentence "the self is the experience" is true in the pure framework and false in
the framework after evaluation, for the same self and experience. -/
theorem subjectObject_frameworkRelative (S : Self E) (e : E) :
    (Framework.pure : Framework (Entity E)).Same (.inl S) (.inr e) ∧
      ¬ (evaluated S).Same (.inl S) (.inr e) :=
  ⟨pure_same_subject_object S e, evaluated_not_same_subject_object S e⟩

/-- AC4(b): in the framework after evaluation by `S`, two experiences that are totally new for
`S` are not told apart. -/
theorem evaluated_same_of_isNew {S : Self E} {e e' : E} (he : S.IsNew e) (he' : S.IsNew e') :
    (evaluated S).Same (.inr e) (.inr e') := by
  rintro P (rfl | ⟨c, hc, rfl⟩)
  · exact Iff.rfl
  · exact ⟨fun h ↦ absurd ⟨c, hc, h⟩ he, fun h ↦ absurd ⟨c, hc, h⟩ he'⟩

end MeaningDimension.ACSI
