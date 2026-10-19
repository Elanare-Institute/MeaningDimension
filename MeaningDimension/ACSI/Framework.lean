import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation

/-!
# Frameworks and framework-relative identity

Spec: `docs/acsi_spec.md`, M1–M2, AC1, AC3(b), AC7(g).

A *framework* (枠組み) is a set of evaluation predicates on a domain. Two things are the same in a
framework when no predicate of the framework tells them apart; the objects of the framework are
the classes of this equivalence. The *pure* framework has no evaluation predicate at all: it is
the formal counterpart of pure experience (純粋経験) as "the state before experience is cognized
and evaluated" in the author's formulation.

Contradictory sentences are evaluated framework by framework, as the author chose
("枠組みによる"): a sentence may hold in one framework and fail in another, but no framework
contains a sentence together with its negation (`not_same_and_not_same`). No paraconsistent logic
is used.
-/

namespace MeaningDimension.ACSI

universe u

/-- A framework: a set of evaluation predicates on the domain `D`. -/
structure Framework (D : Type u) where
  preds : Set (D → Prop)

namespace Framework

variable {D : Type u} (F : Framework D)

/-- `x` and `y` are the same in the framework `F`: no evaluation predicate of `F` tells them
apart. -/
def Same (x y : D) : Prop := ∀ P ∈ F.preds, (P x ↔ P y)

theorem same_refl (x : D) : F.Same x x := fun _ _ ↦ Iff.rfl

variable {F} in
theorem same_symm {x y : D} (h : F.Same x y) : F.Same y x := fun P hP ↦ (h P hP).symm

variable {F} in
theorem same_trans {x y z : D} (h₁ : F.Same x y) (h₂ : F.Same y z) : F.Same x z :=
  fun P hP ↦ (h₁ P hP).trans (h₂ P hP)

/-- Sameness in `F` as a setoid. -/
def setoid : Setoid D := ⟨F.Same, ⟨F.same_refl, same_symm, same_trans⟩⟩

/-- The objects of the framework `F`. -/
def Obj : Type u := Quotient F.setoid

/-- `x` seen as an object of the framework `F`. -/
def obj (x : D) : F.Obj := Quotient.mk F.setoid x

theorem obj_eq_iff {x y : D} : F.obj x = F.obj y ↔ F.Same x y := Quotient.eq (r := F.setoid)

/-- AC3(b): inside one framework, sameness and its negation never hold together. -/
theorem not_same_and_not_same (x y : D) : ¬ (F.Same x y ∧ ¬ F.Same x y) := fun h ↦ h.2 h.1

/-- The pure framework (M2): no evaluation predicate. -/
def pure : Framework D := ⟨∅⟩

/-- AC1(a): in the pure framework, everything is the same. -/
theorem pure_same (x y : D) : (pure : Framework D).Same x y :=
  fun _ hP ↦ absurd hP (Set.notMem_empty _)

/-- AC1(b): the pure framework has at most one object. -/
instance : Subsingleton (pure : Framework D).Obj :=
  ⟨fun a b ↦ Quotient.inductionOn₂ (s₁ := pure.setoid) (s₂ := pure.setoid) a b
    fun x y ↦ (obj_eq_iff _).mpr (pure_same x y)⟩

/-- The framework that tells everything apart. -/
def discrete : Framework D := ⟨Set.range fun x ↦ (· = x)⟩

theorem discrete_same_iff {x y : D} : (discrete : Framework D).Same x y ↔ x = y := by
  constructor
  · intro h
    exact (h (· = y) ⟨y, rfl⟩).mpr rfl
  · rintro rfl
    exact same_refl _ x

/-- A relation `R` on `D`, carried over to the objects of the framework `F`. -/
def Lift (R : D → D → Prop) (a b : F.Obj) : Prop :=
  ∃ x y, F.obj x = a ∧ F.obj y = b ∧ R x y

/-- In the framework `F`, `x` and `y` precede each other with respect to `R`. -/
def Mutual (R : D → D → Prop) (x y : D) : Prop :=
  F.Lift R (F.obj x) (F.obj y) ∧ F.Lift R (F.obj y) (F.obj x)

theorem lift_discrete_iff {R : D → D → Prop} {x y : D} :
    (discrete : Framework D).Lift R (discrete.obj x) (discrete.obj y) ↔ R x y := by
  constructor
  · rintro ⟨x', y', hx, hy, h⟩
    rw [obj_eq_iff, discrete_same_iff] at hx hy
    exact hx ▸ hy ▸ h
  · intro h
    exact ⟨x, y, rfl, rfl, h⟩

end Framework

/-- AC7(g): for an asymmetric relation (precedence in the ordinary sense), two things never
precede each other. -/
theorem not_mutual_of_asymm {α : Type u} {R : α → α → Prop} (hR : ∀ a b, R a b → ¬ R b a)
    (a b : α) : ¬ (R a b ∧ R b a) :=
  fun h ↦ hR a b h.1 h.2

end MeaningDimension.ACSI
