import MeaningDimension.Generation.Embedding
import MeaningDimension.Generation.RingLanguage
import MeaningDimension.Generation.Examples
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Kappa's "2 + 2 = 5" and the embedding condition (MDG8)

Spec: `docs/mdg_spec.md`, §7, J11–J16.

Lakatos's Kappa (*Proofs and Refutations*, pp. 101–102): two items of 2 lb each, received in a
box of 1 lb, weigh 5 lb together. Packing with a wrapper of weight `w` reads the binary symbol `⊕`
as `a + b + w`; plain addition is the packing with `w = 0` (MDG8(b)).

Whether this move is a `ReversalStep` depends on the language, that is, on which symbols keep a
fixed meaning:

* `ℒₖ` (`⊕` and a constant `⌜n⌝` for every `n`): `⌜2⌝ ⊕ ⌜2⌝ = ⌜4⌝` is quantifier-free, true for
  plain addition and false for every `w ≠ 0`, so there is no embedding (MDG8(c)).
* `ℒ⊕` (`⊕` only): `x ↦ x - w` is a surjective embedding, so no sentence flips (MDG8(d)).
* `ℒᵣ` (`0, 1, +, ·`, numerals built from `1` and `+`): `2 + 2 = 4` stays true, and `0 + 0 = 0`
  rules out an embedding for `w ≠ 0` (MDG8(e)).

Every structure here lives on ℚ. Instances on ℚ are the plain ones; the packed ones sit on the
type synonym `Pack w` (J11).
-/

namespace MeaningDimension.Generation

open FFL FFL.FirstOrder

/-! ## General lemmas (J14, J15) -/

section General

variable {L : Language} {M M' : Type*} [Nonempty M] [Nonempty M'] [Tarski.Structure L M]
  [Tarski.Structure L M']

/-- J14: a quantifier-free sentence true in `M` and false in `M'` rules out an embedding. -/
theorem isEmpty_of_open {σ : Sentence L} (hσ : σ.Open) (h : M↓[L] ⊧ σ) (h' : M'↓[L] ⊧ ∼σ) :
    IsEmpty (M ↪ₛ[L] M') :=
  ⟨fun Θ ↦ not_true_false_of_isExistential Θ (.of_open hσ) ⟨h, h'⟩⟩

omit [Nonempty M'] in
/-- Restricted to the whole domain, `EvalOn` is `Eval`. -/
theorem evalOn_univ {ξ : Type*} : ∀ {n : ℕ} (φ : Semiformula L ξ n) (b : Fin n → M')
    (ε : ξ → M'), EvalOn L Set.univ φ b ε ↔ φ.Eval b ε
  | _, .verum, _, _ => Iff.rfl
  | _, .falsum, _, _ => Iff.rfl
  | _, .rel _ _, _, _ => Iff.rfl
  | _, .nrel _ _, _, _ => Iff.rfl
  | _, .and φ ψ, b, ε => and_congr (evalOn_univ φ b ε) (evalOn_univ ψ b ε)
  | _, .or φ ψ, b, ε => or_congr (evalOn_univ φ b ε) (evalOn_univ ψ b ε)
  | _, .all φ, b, ε => by
    show (∀ x ∈ Set.univ, EvalOn L _ φ (x :> b) ε) ↔ ∀ x, φ.Eval (x :> b) ε
    simp only [Set.mem_univ, true_implies, evalOn_univ φ]
  | _, .exs φ, b, ε => by
    show (∃ x ∈ Set.univ, EvalOn L _ φ (x :> b) ε) ↔ ∃ x, φ.Eval (x :> b) ε
    simp only [Set.mem_univ, true_and, evalOn_univ φ]

/-- J15: along a surjective embedding every sentence keeps its truth value (MDG1(f) with the
image equal to the whole domain). -/
theorem models_iff_of_surjective (Θ : M ↪ₛ[L] M') (hΘ : Function.Surjective Θ)
    (σ : Sentence L) : M↓[L] ⊧ σ ↔ M'↓[L] ⊧ σ := by
  rw [models_iff_evalOn Θ σ, Set.range_eq_univ.mpr hΘ, evalOn_univ]
  rfl

/-- Along a surjective embedding no sentence flips. -/
theorem not_flips_of_surjective (Θ : M ↪ₛ[L] M') (hΘ : Function.Surjective Θ)
    (σ : Sentence L) : ¬ Flips L M M' σ := fun ⟨h, h'⟩ ↦
  (Semantics.Not.models_not.mp h) ((models_iff_of_surjective Θ hΘ σ).mpr h')

end General

namespace Kappa

/-! ## The languages (J12) -/

/-- Function symbols of `ℒₖ`: `⊕` and a constant `⌜n⌝` for every `n`. -/
inductive KappaFunc : ℕ → Type
  | plus : KappaFunc 2
  | num : ℕ → KappaFunc 0

/-- Function symbols of `ℒ⊕`: `⊕` only. -/
inductive PlusFunc : ℕ → Type
  | plus : PlusFunc 2

/-- `ℒₖ`: `⊕`, `⌜n⌝` (n : ℕ), `=`. -/
abbrev kappaLang : Language where
  Func := KappaFunc
  Rel := RingRel

/-- `ℒ⊕`: `⊕`, `=`. -/
abbrev plusLang : Language where
  Func := PlusFunc
  Rel := RingRel

notation "ℒₖ" => kappaLang
notation "ℒ⊕" => plusLang

/-! ## The structures (J11) -/

/-- Plain addition: `⊕` is `a + b`, `⌜n⌝` is `n`. -/
@[instance_reducible] def addModel : Tarski.Structure ℒₖ ℚ where
  func := fun _ f ↦
    match f with
    | KappaFunc.plus => fun v ↦ v 0 + v 1
    | KappaFunc.num n => fun _ ↦ n
  rel := fun _ r ↦
    match r with
    | RingRel.eq => fun v ↦ v 0 = v 1

/-- Packing with a wrapper of weight `w`: `⊕` is `a + b + w`, `⌜n⌝` is `n`. -/
@[instance_reducible] def packModel (w : ℚ) : Tarski.Structure ℒₖ ℚ where
  func := fun _ f ↦
    match f with
    | KappaFunc.plus => fun v ↦ v 0 + v 1 + w
    | KappaFunc.num n => fun _ ↦ n
  rel := fun _ r ↦
    match r with
    | RingRel.eq => fun v ↦ v 0 = v 1

/-- Plain addition in `ℒ⊕`. -/
@[instance_reducible] def addModelP : Tarski.Structure ℒ⊕ ℚ where
  func := fun _ f ↦
    match f with
    | PlusFunc.plus => fun v ↦ v 0 + v 1
  rel := fun _ r ↦
    match r with
    | RingRel.eq => fun v ↦ v 0 = v 1

/-- Packing in `ℒ⊕`. -/
@[instance_reducible] def packModelP (w : ℚ) : Tarski.Structure ℒ⊕ ℚ where
  func := fun _ f ↦
    match f with
    | PlusFunc.plus => fun v ↦ v 0 + v 1 + w
  rel := fun _ r ↦
    match r with
    | RingRel.eq => fun v ↦ v 0 = v 1

/-- Packing in `ℒᵣ`: only `+` changes. -/
@[instance_reducible] def packRing (w : ℚ) : Tarski.Structure ℒᵣ ℚ where
  func := fun _ f ↦
    match f with
    | Language.ORing.Func.zero => fun _ ↦ 0
    | Language.ORing.Func.one => fun _ ↦ 1
    | Language.ORing.Func.add => fun v ↦ v 0 + v 1 + w
    | Language.ORing.Func.mul => fun v ↦ v 0 * v 1
  rel := fun _ r ↦
    match r with
    | RingRel.eq => fun v ↦ v 0 = v 1

/-- The domain of the packed structures: a synonym of ℚ (J11). -/
def Pack (_ : ℚ) : Type := ℚ

instance : Tarski.Structure ℒₖ ℚ := addModel
instance : Tarski.Structure ℒ⊕ ℚ := addModelP
instance (w : ℚ) : Nonempty (Pack w) := ⟨(0 : ℚ)⟩
instance (w : ℚ) : Tarski.Structure ℒₖ (Pack w) := packModel w
instance (w : ℚ) : Tarski.Structure ℒ⊕ (Pack w) := packModelP w
instance (w : ℚ) : Tarski.Structure ℒᵣ (Pack w) := packRing w

/-! ## The sentences (J13) -/

/-- The constant `⌜n⌝`. -/
def num (n : ℕ) : Semiterm ℒₖ Empty 0 := .func (KappaFunc.num n : Language.Func ℒₖ 0) ![]

/-- `⌜2⌝ ⊕ ⌜2⌝`. -/
def twoPlusTwo : Semiterm ℒₖ Empty 0 :=
  .func (KappaFunc.plus : Language.Func ℒₖ 2) ![num 2, num 2]

/-- `⌜2⌝ ⊕ ⌜2⌝ = ⌜4⌝`. -/
def four : Sentence ℒₖ := .rel (RingRel.eq : Language.Rel ℒₖ 2) ![twoPlusTwo, num 4]

/-- `⌜2⌝ ⊕ ⌜2⌝ = ⌜5⌝`. -/
def five : Sentence ℒₖ := .rel (RingRel.eq : Language.Rel ℒₖ 2) ![twoPlusTwo, num 5]

/-- `2 + 2 = 4` in `ℒᵣ`, with Foundation's numerals. -/
noncomputable def fourR : Sentence ℒᵣ := “2 + 2 = 4”

/-- `0 + 0 = 0` in `ℒᵣ`. -/
noncomputable def zeroR : Sentence ℒᵣ := “0 + 0 = 0”

/-! ## MDG8(a): truth values -/

/-- In packing with `w`, `⌜2⌝ ⊕ ⌜2⌝ = ⌜n⌝` holds iff `2 + 2 + w = n` (`w = 0` is plain
addition). -/
theorem eval_eq_num_iff (s : Tarski.Structure ℒₖ ℚ) (w : ℚ)
    (hplus : ∀ a b, s.func (KappaFunc.plus : Language.Func ℒₖ 2) ![a, b] = a + b + w)
    (hnum : ∀ (n : ℕ) v, s.func (KappaFunc.num n : Language.Func ℒₖ 0) v = n)
    (heq : ∀ a b, s.rel (RingRel.eq : Language.Rel ℒₖ 2) ![a, b] ↔ a = b) (n : ℕ) :
    Semiformula.Eval (s := s) ![] Empty.elim
        (.rel (RingRel.eq : Language.Rel ℒₖ 2) ![twoPlusTwo, num n]) ↔
      (2 + 2 + w : ℚ) = n := by
  have hv : ∀ k : ℕ, Semiterm.val (s := s) ![] Empty.elim (num k) = k := fun k ↦ by
    rw [num, Semiterm.val_func']; exact hnum k _
  have h2 : Semiterm.val (s := s) ![] Empty.elim twoPlusTwo = 2 + 2 + w := by
    rw [twoPlusTwo, Semiterm.val_func']
    have : (fun i ↦ Semiterm.val (s := s) ![] Empty.elim (![num 2, num 2] i)) =
        ![((2 : ℕ) : ℚ), ((2 : ℕ) : ℚ)] := by
      funext i; fin_cases i <;> simp [hv]
    rw [this, hplus]; norm_num
  rw [Semiformula.eval_rel']
  have : (fun i ↦ Semiterm.val (s := s) ![] Empty.elim (![twoPlusTwo, num n] i)) =
      ![2 + 2 + w, (n : ℚ)] := by
    funext i; fin_cases i <;> simp [h2, hv]
  rw [this, heq]

theorem models_eq_num_iff_add (n : ℕ) :
    ℚ↓[ℒₖ] ⊧ (.rel (RingRel.eq : Language.Rel ℒₖ 2) ![twoPlusTwo, num n]) ↔
      (2 + 2 : ℚ) = n := by
  rw [models_iff, ← add_zero (2 + 2 : ℚ)]
  exact eval_eq_num_iff addModel 0 (fun a b ↦ (add_zero _).symm) (fun _ _ ↦ rfl)
    (fun _ _ ↦ Iff.rfl) n

theorem models_eq_num_iff_pack (w : ℚ) (n : ℕ) :
    (Pack w)↓[ℒₖ] ⊧ (.rel (RingRel.eq : Language.Rel ℒₖ 2) ![twoPlusTwo, num n]) ↔
      (2 + 2 + w : ℚ) = n := by
  rw [models_iff]
  exact eval_eq_num_iff (packModel w) w (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ Iff.rfl) n

theorem rat_models_four : ℚ↓[ℒₖ] ⊧ four :=
  (models_eq_num_iff_add 4).mpr (by norm_num)

theorem rat_models_not_five : ℚ↓[ℒₖ] ⊧ ∼five := by
  rw [Semantics.Not.models_not, five, models_eq_num_iff_add]
  norm_num

theorem pack_models_not_four {w : ℚ} (hw : w ≠ 0) : (Pack w)↓[ℒₖ] ⊧ ∼four := by
  rw [Semantics.Not.models_not, four, models_eq_num_iff_pack]
  intro h
  exact hw (by push_cast at h; linarith)

/-- Lakatos's numbers: two items of 2 lb in a box of 1 lb weigh 5 lb. -/
theorem pack_one_models_five : (Pack 1)↓[ℒₖ] ⊧ five :=
  (models_eq_num_iff_pack 1 5).mpr (by norm_num)

/-! ## MDG8(b): plain addition is the packing with `w = 0` -/

theorem packModel_zero : packModel 0 = addModel := by
  ext k f v
  · cases f <;> first | rfl | exact add_zero _
  · rfl

theorem packModelP_zero : packModelP 0 = addModelP := by
  ext k f v
  · cases f; exact add_zero _
  · rfl

theorem packRing_zero : packRing 0 = ringModel ℚ := by
  ext k f v
  · cases f <;> first | rfl | exact add_zero _
  · rfl

/-- The identity `ℚ → Pack 0` is an `ℒₖ`-embedding. -/
def idPack : ℚ ↪ₛ[ℒₖ] Pack 0 where
  toFun := fun x ↦ x
  func' := fun {_} f v ↦ by
    cases f
    · show v 0 + v 1 = v 0 + v 1 + 0
      exact (add_zero _).symm
    · rfl
  rel' := fun {_} r _ h ↦ by cases r; exact h
  rel_inv' := fun {_} r _ h ↦ by cases r; exact h
  toFun_inj := fun _ _ h ↦ h

theorem idPack_surjective : Function.Surjective idPack := fun x ↦ ⟨x, rfl⟩

/-! ## MDG8(c): with the numbers fixed there is no embedding -/

theorem isEmpty_kappa {w : ℚ} (hw : w ≠ 0) : IsEmpty (ℚ ↪ₛ[ℒₖ] Pack w) :=
  isEmpty_of_open (σ := four) rfl rat_models_four (pack_models_not_four hw)

theorem flips_not_four {w : ℚ} (hw : w ≠ 0) : Flips ℒₖ ℚ (Pack w) (∼four) :=
  ⟨by simpa using rat_models_four, pack_models_not_four hw⟩

theorem flips_five : Flips ℒₖ ℚ (Pack 1) five :=
  ⟨rat_models_not_five, pack_one_models_five⟩

theorem not_reversalStep_kappa {w : ℚ} (hw : w ≠ 0) : ¬ ReversalStep ℒₖ ℚ (Pack w) :=
  fun ⟨⟨Θ⟩, _⟩ ↦ (isEmpty_kappa hw).false Θ

/-! ## MDG8(d): without number symbols, `x ↦ x - w` is an isomorphism -/

/-- `x ↦ x - w`, an `ℒ⊕`-embedding of plain addition into packing. -/
def shift (w : ℚ) : ℚ ↪ₛ[ℒ⊕] Pack w where
  toFun := fun x ↦ x - w
  func' := fun {_} f v ↦ by
    cases f
    show v 0 + v 1 - w = (v 0 - w) + (v 1 - w) + w
    ring
  rel' := fun {_} r v h ↦ by
    cases r
    show v 0 - w = v 1 - w
    rw [show v 0 = v 1 from h]
  rel_inv' := fun {_} r v h ↦ by
    cases r
    exact sub_left_inj.mp (h : v 0 - w = v 1 - w)
  toFun_inj := fun _ _ h ↦ sub_left_inj.mp h

theorem shift_surjective (w : ℚ) : Function.Surjective (shift w) :=
  fun y ↦ ⟨(show ℚ from y) + w, add_sub_cancel_right (show ℚ from y) w⟩

theorem models_iff_plus (w : ℚ) (σ : Sentence ℒ⊕) : ℚ↓[ℒ⊕] ⊧ σ ↔ (Pack w)↓[ℒ⊕] ⊧ σ :=
  models_iff_of_surjective (shift w) (shift_surjective w) σ

theorem not_reversalStep_plus (w : ℚ) : ¬ ReversalStep ℒ⊕ ℚ (Pack w) :=
  fun ⟨_, σ, h⟩ ↦ not_flips_of_surjective (shift w) (shift_surjective w) σ h

/-! ## MDG8(e): numbers built from `1` and `+` -/

section PackRing

variable (w : ℚ)

theorem pack_val_add (a b : ℚ) :
    (Semiterm.Operator.Add.add : Semiterm.Operator ℒᵣ 2).val (s := packRing w) ![a, b] =
      a + b + w := by
  simp [Semiterm.Operator.val, Semiterm.Operator.Add.term_eq]
  rfl

theorem pack_val_zero :
    (Semiterm.Operator.Zero.zero : Semiterm.Operator ℒᵣ 0).val (s := packRing w) ![] = 0 := by
  simp [Semiterm.Operator.val, Semiterm.Operator.Zero.term_eq]
  rfl

theorem pack_val_one :
    (Semiterm.Operator.One.one : Semiterm.Operator ℒᵣ 0).val (s := packRing w) ![] = 1 := by
  simp [Semiterm.Operator.val, Semiterm.Operator.One.term_eq]
  rfl

/-- In `Pack w`, the numeral `n + 1` (built from `1` and `+`) denotes `(n + 1) + n · w`. -/
theorem pack_val_numeral : ∀ n : ℕ,
    (Semiterm.Operator.numeral ℒᵣ (n + 1)).val (s := packRing w) ![] = (n + 1 : ℚ) + n * w
  | 0 => by
    rw [Semiterm.Operator.numeral_one, pack_val_one]; simp
  | n + 1 => by
    rw [Semiterm.Operator.numeral_add_two, Semiterm.Operator.val_comp]
    have : (Semiterm.Operator.val (s := packRing w) ![] ∘
        ![Semiterm.Operator.numeral ℒᵣ (n + 1), Semiterm.Operator.One.one]) =
        ![(n + 1 : ℚ) + n * w, 1] := by
      funext i; fin_cases i
      · exact pack_val_numeral n
      · exact pack_val_one w
    rw [this, pack_val_add]
    push_cast; ring

theorem pack_val_eq (a b : ℚ) :
    (Semiformula.Operator.Eq.eq : Semiformula.Operator ℒᵣ 2).val (s := packRing w) ![a, b] ↔
      a = b := by
  simp [Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]
  rfl

/-- `2 + 2 = 4` holds in `Pack w`: both sides denote `4 + 3w`. -/
theorem pack_models_fourR : (Pack w)↓[ℒᵣ] ⊧ fourR := by
  simp [models_iff, fourR]
  refine (pack_val_eq w _ _).mpr ?_
  show (Semiterm.Operator.Add.add : Semiterm.Operator ℒᵣ 2).val (s := packRing w)
      ![(Semiterm.Operator.numeral ℒᵣ (1 + 1)).val (s := packRing w) ![],
        (Semiterm.Operator.numeral ℒᵣ (1 + 1)).val (s := packRing w) ![]] =
    (Semiterm.Operator.numeral ℒᵣ (3 + 1)).val (s := packRing w) ![]
  rw [pack_val_numeral, pack_val_numeral, pack_val_add]
  push_cast; ring

theorem rat_models_fourR : ℚ↓[ℒᵣ] ⊧ fourR := by
  simp [models_iff, fourR, numeral_eq_cast]
  norm_num

/-- `0 + 0 = 0` fails in `Pack w` for `w ≠ 0`. -/
theorem pack_models_not_zeroR {w : ℚ} (hw : w ≠ 0) : (Pack w)↓[ℒᵣ] ⊧ ∼zeroR := by
  rw [Semantics.Not.models_not]
  simp [models_iff, zeroR]
  intro h
  have h' : (0 : ℚ) + 0 + w = 0 :=
    calc (0 : ℚ) + 0 + w
        = (Semiterm.Operator.Add.add : Semiterm.Operator ℒᵣ 2).val (s := packRing w)
          ![(Semiterm.Operator.Zero.zero : Semiterm.Operator ℒᵣ 0).val (s := packRing w) ![],
            (Semiterm.Operator.Zero.zero : Semiterm.Operator ℒᵣ 0).val (s := packRing w) ![]] := by
          rw [pack_val_zero, pack_val_add]
      _ = (Semiterm.Operator.Zero.zero : Semiterm.Operator ℒᵣ 0).val (s := packRing w) ![] :=
          (pack_val_eq w _ _).mp h
      _ = 0 := pack_val_zero w
  exact hw (by simpa using h')

theorem rat_models_zeroR : ℚ↓[ℒᵣ] ⊧ zeroR := by
  simp [models_iff, zeroR]

theorem isEmpty_ring {w : ℚ} (hw : w ≠ 0) : IsEmpty (ℚ ↪ₛ[ℒᵣ] Pack w) :=
  isEmpty_of_open (σ := zeroR) rfl rat_models_zeroR (pack_models_not_zeroR hw)

theorem flips_not_zeroR {w : ℚ} (hw : w ≠ 0) : Flips ℒᵣ ℚ (Pack w) (∼zeroR) :=
  ⟨by simpa using rat_models_zeroR, pack_models_not_zeroR hw⟩

theorem not_reversalStep_ring {w : ℚ} (hw : w ≠ 0) : ¬ ReversalStep ℒᵣ ℚ (Pack w) :=
  fun ⟨⟨Θ⟩, _⟩ ↦ (isEmpty_ring hw).false Θ

end PackRing

end Kappa

end MeaningDimension.Generation
