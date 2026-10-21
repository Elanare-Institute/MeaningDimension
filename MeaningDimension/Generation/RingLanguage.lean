import Foundation.FirstOrder.Incompleteness.Examples

/-!
# The language of rings, without `<`

Spec: `docs/mdg_spec.md`, J2, §2.4.

Foundation has the language of ordered rings `ℒₒᵣ` (`0, 1, +, ·, =, <`) but no language of rings.
`ℒᵣ` has the function symbols of `ℒₒᵣ` and `=` as its only relation symbol. A type with `0, 1, +, ·`
carries the standard `ℒᵣ`-structure (`ringModel`), so ℂ needs no order.
-/

namespace MeaningDimension.Generation

open FFL FFL.FirstOrder

/-- The only relation symbol of `ℒᵣ`. -/
inductive RingRel : ℕ → Type
  | eq : RingRel 2

/-- The language of rings: `0, 1, +, ·, =`. -/
def ringLang : Language where
  Func := Language.ORing.Func
  Rel := RingRel

notation "ℒᵣ" => ringLang

instance : Language.Eq ℒᵣ := ⟨RingRel.eq⟩
instance : Language.Zero ℒᵣ := ⟨Language.ORing.Func.zero⟩
instance : Language.One ℒᵣ := ⟨Language.ORing.Func.one⟩
instance : Language.Add ℒᵣ := ⟨Language.ORing.Func.add⟩
instance : Language.Mul ℒᵣ := ⟨Language.ORing.Func.mul⟩

section Model

variable (M : Type*) [Zero M] [One M] [Add M] [Mul M]

/-- The standard `ℒᵣ`-structure. -/
instance ringModel : Tarski.Structure ℒᵣ M where
  func := fun _ f ↦
    match f with
    | Language.ORing.Func.zero => fun _ ↦ 0
    | Language.ORing.Func.one => fun _ ↦ 1
    | Language.ORing.Func.add => fun v ↦ v 0 + v 1
    | Language.ORing.Func.mul => fun v ↦ v 0 * v 1
  rel := fun _ r ↦
    match r with
    | RingRel.eq => fun v ↦ v 0 = v 1

instance : Tarski.Structure.Zero ℒᵣ M := ⟨rfl⟩
instance : Tarski.Structure.One ℒᵣ M := ⟨rfl⟩
instance : Tarski.Structure.Add ℒᵣ M := ⟨fun _ _ ↦ rfl⟩
instance : Tarski.Structure.Mul ℒᵣ M := ⟨fun _ _ ↦ rfl⟩
instance : Tarski.Structure.Eq ℒᵣ M := ⟨fun _ _ ↦ iff_of_eq rfl⟩

end Model

/-- The numeral `z` denotes `z`. -/
@[simp] theorem val_numeral {M : Type*} [AddMonoidWithOne M] [Mul M] :
    (z : ℕ) → (Semiterm.Operator.numeral ℒᵣ z).val ![] = (z : M)
  | 0 => by simp [Semiterm.Operator.numeral_zero]
  | 1 => by simp [Semiterm.Operator.numeral_one]
  | z + 2 => by
    simp [Semiterm.Operator.numeral_add_two, Semiterm.Operator.val_comp, Matrix.fun_eq_vec_two,
      val_numeral (z + 1)]
    rw [add_assoc, one_add_one_eq_two]

end MeaningDimension.Generation
