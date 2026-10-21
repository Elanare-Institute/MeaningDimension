import MeaningDimension.ACSI.Incorporation

/-!
# Self and experience precede each other

Spec: `docs/acsi_spec.md`, M6, AC7.

The author's second contradiction: experience precedes the self as its ground (土台), and the
self precedes experience as the subject that has it ("互いに先立つ"). Following the author's
choice for the subject–object contradiction, it is read framework by framework:

* unfolding a past `h` in time gives the nodes `self k` and `exp k`; `self k` precedes `exp k`
  (the self at stage `k` takes in `h[k]`) and `exp k` precedes `self (k+1)` (`h[k]` is stored in
  the self at stage `k+1`). This precedence is strict (`prec_irrefl`, `prec_asymm`), and in the
  framework that tells all stages apart nothing precedes and is preceded by the same thing
  (`stageFramework_not_mutual`);
* in the framework of self-identity, which does not tell the stages of the self apart, the self
  and each experience precede each other (`selfIdentity_mutual`), and the self precedes itself
  (`selfIdentity_self_precedes_self`).

`Base h` is defined from the stages (`h.length`). Its correspondence with incorporation is
`run_take_succ` and `getElem_mem_run_take_succ`.
-/

namespace MeaningDimension.ACSI

universe u

variable {E : Type u}

/-- The nodes of a past unfolded in time. -/
inductive Node
  | self (k : ℕ)
  | exp (k : ℕ)

namespace Node

/-- Position in time: `self 0, exp 0, self 1, exp 1, …`. -/
def rank : Node → ℕ
  | self k => 2 * k
  | exp k => 2 * k + 1

/-- Being a stage of the self. -/
def isSelf : Node → Prop
  | self _ => True
  | exp _ => False

end Node

/-- Direct precedence in the past `h` (M6). -/
inductive Base (h : List E) : Node → Node → Prop
  /-- The self at stage `k` precedes `h[k]` as the subject that takes it in. -/
  | subject (k : ℕ) (hk : k < h.length) : Base h (.self k) (.exp k)
  /-- `h[k]` precedes the self at stage `k+1` as its ground. -/
  | ground (k : ℕ) (hk : k < h.length) : Base h (.exp k) (.self (k + 1))

/-- Precedence in the past `h`. -/
def Prec (h : List E) : Node → Node → Prop := Relation.TransGen (Base h)

/-- The framework of the past unfolded in time: it tells all nodes apart. -/
def stageFramework : Framework Node := Framework.discrete

/-- The framework of self-identity: it tells selves from experiences and experiences from one
another, but not one stage of the self from another. -/
def selfIdentity : Framework Node :=
  ⟨insert Node.isSelf (Set.range fun k ↦ (· = Node.exp k))⟩

/-! ## AC7(a): correspondence with incorporation -/

/-- AC7(a): the self at stage `k+1` is the self at stage `k` after taking in `h[k]`. -/
theorem run_take_succ (M : Making E) (S₀ : Self E) (h : List E) {k : ℕ} (hk : k < h.length) :
    M.run S₀ (h.take (k + 1)) = M.incorporate (M.run S₀ (h.take k)) h[k] := by
  rw [Making.run, Making.run, List.take_succ_eq_append_getElem hk, List.foldl_append]
  rfl

/-- AC7(a): `h[k]` is stored in the self at stage `k+1`. -/
theorem getElem_mem_run_take_succ (M : Making E) (S₀ : Self E) (h : List E) {k : ℕ}
    (hk : k < h.length) : h[k] ∈ (M.run S₀ (h.take (k + 1))).experiences := by
  rw [run_take_succ M S₀ h hk]
  exact Making.mem_incorporate_experiences _ _

/-! ## AC7(b)(c): unfolded in time, precedence is strict -/

theorem Base.rank_lt {h : List E} {x y : Node} (hxy : Base h x y) : x.rank < y.rank := by
  cases hxy
  · simp only [Node.rank]; omega
  · simp only [Node.rank]; omega

theorem Prec.rank_lt {h : List E} {x y : Node} (hxy : Prec h x y) : x.rank < y.rank := by
  induction hxy with
  | single hb => exact hb.rank_lt
  | tail _ hb ih => exact ih.trans hb.rank_lt

/-- AC7(b). -/
theorem prec_irrefl (h : List E) (x : Node) : ¬ Prec h x x := fun hx ↦
  lt_irrefl _ hx.rank_lt

/-- AC7(b). -/
theorem prec_asymm {h : List E} {x y : Node} (hxy : Prec h x y) : ¬ Prec h y x := fun hyx ↦
  lt_asymm hxy.rank_lt hyx.rank_lt

/-- AC7(c): in the framework of the past unfolded in time, nothing precedes and is preceded by
the same thing. -/
theorem stageFramework_not_mutual (h : List E) (x y : Node) :
    ¬ stageFramework.Mutual (Prec h) x y := fun ⟨hxy, hyx⟩ ↦
  prec_asymm (Framework.lift_discrete_iff.mp hxy) (Framework.lift_discrete_iff.mp hyx)

/-! ## AC7(d)–(f): in the framework of self-identity -/

/-- AC7(d). -/
theorem selfIdentity_same_self (k m : ℕ) : selfIdentity.Same (.self k) (.self m) := by
  rintro P (rfl | ⟨j, rfl⟩) <;> simp [Node.isSelf]

/-- AC7(d). -/
theorem selfIdentity_not_same_self_exp (k m : ℕ) : ¬ selfIdentity.Same (.self k) (.exp m) :=
  fun hs ↦ ((hs Node.isSelf (Set.mem_insert _ _)).mp trivial : Node.isSelf (.exp m))

/-- AC7(d). -/
theorem selfIdentity_not_same_exp_exp {k m : ℕ} (hkm : k ≠ m) :
    ¬ selfIdentity.Same (.exp k) (.exp m) := fun hs ↦ by
  have := (hs (· = Node.exp m) (Set.mem_insert_of_mem _ ⟨m, rfl⟩)).mpr rfl
  exact hkm (Node.exp.inj this)

theorem selfIdentity_obj_self (k : ℕ) :
    selfIdentity.obj (.self k) = selfIdentity.obj (.self 0) :=
  (Framework.obj_eq_iff _).mpr (selfIdentity_same_self k 0)

/-- AC7(e): in the framework of self-identity, the self and each experience precede each
other. -/
theorem selfIdentity_mutual {h : List E} {k : ℕ} (hk : k < h.length) :
    selfIdentity.Mutual (Base h) (.self 0) (.exp k) :=
  ⟨⟨.self k, .exp k, selfIdentity_obj_self k, rfl, .subject k hk⟩,
    ⟨.exp k, .self (k + 1), rfl, selfIdentity_obj_self (k + 1), .ground k hk⟩⟩

/-- AC7(f): in the framework of self-identity, the self precedes itself. -/
theorem selfIdentity_self_precedes_self {h : List E} (hn : 0 < h.length) :
    selfIdentity.Lift (Prec h) (selfIdentity.obj (.self 0)) (selfIdentity.obj (.self 0)) :=
  ⟨.self 0, .self 1, rfl, selfIdentity_obj_self 1,
    .tail (.single (.subject 0 hn)) (.ground 0 hn)⟩

end MeaningDimension.ACSI
