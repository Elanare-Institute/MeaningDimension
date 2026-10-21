import MeaningDimension.ACSI.Incorporation

/-!
# The refinement form of generation, and ACSI's incorporation

Spec: `docs/mdg_spec.md`, §2.2, MDG6.

A framework (ACSI's `Framework`) refines another when it keeps all of its evaluation predicates.
A step in the refinement form (`RefineStep`) is a refinement in which two things that were the same
become distinguished (D2; J9 for the name).

MDG6(b) asks whether incorporation refines the evaluated framework. It does, for every making
(`refines_evaluated_incorporate`): incorporation only adds a category, so every evaluation
predicate of `evaluated S` is an evaluation predicate of `evaluated (M.incorporate S e)`. With
AC4(b) and AC5(e), two totally new experiences that the earlier framework does not tell apart are
told apart afterwards when the second is outside the generated category
(`refineStep_evaluated_incorporate`). The definitions `evaluated` and `incorporate` are those of
`ACSI/`, unchanged.

This shows that incorporation is also a step in the refinement form; ACSI is not identified with
that form (D8). Growth by selection, which identifies what was told apart, is not represented
(D9): incorporation, and so every past, never identifies what was told apart (MDG6(d)).
-/

namespace MeaningDimension.Generation

open MeaningDimension.ACSI

universe u

variable {D : Type u}

/-- `F'` refines `F`: it keeps every evaluation predicate of `F`. -/
def Refines (F F' : Framework D) : Prop := F.preds ⊆ F'.preds

/-- `x` and `y` are the same in `F` and told apart in `F'`. -/
def DistinctionFlip (F F' : Framework D) (x y : D) : Prop := F.Same x y ∧ ¬ F'.Same x y

/-- A step in the refinement form. -/
def RefineStep (F F' : Framework D) : Prop :=
  Refines F F' ∧ ∃ x y, DistinctionFlip F F' x y

/-- A refinement identifies no more than the earlier framework. -/
theorem Refines.same {F F' : Framework D} (h : Refines F F') {x y : D} (hxy : F'.Same x y) :
    F.Same x y := fun P hP ↦ hxy P (h hP)

theorem Refines.refl (F : Framework D) : Refines F F := Set.Subset.rfl

theorem Refines.trans {F F' F'' : Framework D} (h : Refines F F') (h' : Refines F' F'') :
    Refines F F'' :=
  Set.Subset.trans h h'

/-! ## MDG6 -/

variable {E : Type u}

/-- MDG6(a) (AC5(c)): classification does not flip from true to false. -/
theorem classifies_incorporate_of_classifies (M : Making E) {S : Self E} {e' : E}
    (h : S.Classifies e') (e : E) : (M.incorporate S e).Classifies e' :=
  Making.classifies_incorporate_of_classifies h e

/-- MDG6(b): incorporation keeps every evaluation predicate. -/
theorem refines_evaluated_incorporate (M : Making E) (S : Self E) (e : E) :
    Refines (evaluated S) (evaluated (M.incorporate S e)) := by
  rintro P (rfl | ⟨c, hc, rfl⟩)
  · exact isSubject_mem_evaluated _
  · exact inCategory_mem_evaluated (List.mem_cons_of_mem _ hc)

/-- MDG6(b): two totally new experiences, the second outside the category generated from the
first, are told apart only after incorporation. -/
theorem distinctionFlip_evaluated_incorporate (M : Making E) {S : Self E} {e e' : E}
    (he : S.IsNew e) (he' : S.IsNew e') (hout : e' ∉ M.generate S e) :
    DistinctionFlip (evaluated S) (evaluated (M.incorporate S e)) (.inr e) (.inr e') :=
  ⟨evaluated_same_of_isNew he he', Making.evaluated_incorporate_not_same hout⟩

/-- MDG6(b). -/
theorem refineStep_evaluated_incorporate (M : Making E) {S : Self E} {e e' : E}
    (he : S.IsNew e) (he' : S.IsNew e') (hout : e' ∉ M.generate S e) :
    RefineStep (evaluated S) (evaluated (M.incorporate S e)) :=
  ⟨refines_evaluated_incorporate M S e, _, _,
    distinctionFlip_evaluated_incorporate M he he' hout⟩

/-- MDG6(d): incorporation does not identify what was told apart. -/
theorem same_of_same_evaluated_incorporate (M : Making E) (S : Self E) (e : E) {x y : Entity E}
    (h : (evaluated (M.incorporate S e)).Same x y) : (evaluated S).Same x y :=
  (refines_evaluated_incorporate M S e).same h

/-- MDG6(d): every past keeps every evaluation predicate. -/
theorem refines_evaluated_run (M : Making E) (S : Self E) (h : List E) :
    Refines (evaluated S) (evaluated (M.run S h)) := by
  induction h generalizing S with
  | nil => exact Refines.refl _
  | cons e h ih => exact (refines_evaluated_incorporate M S e).trans (ih (M.incorporate S e))

/-- MDG6(d): no past identifies what was told apart. -/
theorem same_of_same_evaluated_run (M : Making E) (S : Self E) (h : List E) {x y : Entity E}
    (hs : (evaluated (M.run S h)).Same x y) : (evaluated S).Same x y :=
  (refines_evaluated_run M S h).same hs

end MeaningDimension.Generation
