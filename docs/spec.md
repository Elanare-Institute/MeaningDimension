# 仕様: Phase 1–2（実装前に固定）

この文書は実装より先に書いた。`MeaningDimension/Tests/Spec.lean` のテストは**この文書の文言**から書き起こし、実装の都合で変えない。仕様を変えるときは、まずこの文書を改訂し、テストも改訂する。

記号: `T ⊢ φ`（Foundation の証明可能性、メタレベルの `Prop`）、`ℕ ⊧ φ`（標準モデルでの真理）、`T ⪯ U`（T の定理はすべて U の定理）、`T ⪱ U`（`T ⪯ U` かつ U が T の証明しない文を証明する）。`T.Con = {T.consistent}` は `T` の **Δ₁ 表示**から作る Π₁ 文 `¬□_T ⊥` である。

内部の証明可能性（`T ⊢ φ`、`□_T`）と外部の真理（`ℕ ⊧ φ`）は別の述語として扱い、混同しない。

## Phase 1: 論理構造の基礎

**P1.1 単調性**（分類 B: Foundation の既存補題の言い換え）
任意の言語 `L`、理論 `T U : Theory L` について、`T ⊆ U` かつ `T ⊢ φ` なら `U ⊢ φ`。

**P1.2 反証済み命題の保存不能性**（分類 A。数学的には自明）
`T ⪯ U`（U が T の全定理を保存）、U が無矛盾、`T ⊢ ∼φ` なら `U ⊬ φ`。
- φ は**同じ言語の同じ文**。U は**同じ証明体系**（古典一階論理）。
- 意味論版: 構造 `M` が `M ⊧* U` を満たし、`T ⪯ U`、`T ⊢ ∼φ` なら `M ⊭ φ`。（同一の解釈 M のもとで φ は真にならない。）
- 単一構造版: どの構造 `M` でも `M ⊧ φ` と `M ⊧ ∼φ` は両立しない。

**P1.3 解釈変更の具体例**（分類 A）
- (a) メタレベル（mathlib）: `∀ x : ℝ, x^2 + 1 ≠ 0`。
- (b) メタレベル（mathlib）: `∃ z : ℂ, z^2 + 1 = 0`。
- (c) 対象レベル（Foundation）: 一階の文 `rootSentence := “∃ x, x * x + 1 = 0”`（言語 ℒₒᵣ）について `ℝ ⊭ rootSentence` かつ `ℂ ⊧ rootSentence`。**同一の構文的対象**を二つの構造で評価した結果が異なる。ℂ の `<` は mathlib の `ComplexOrder`（部分順序）で解釈するが、`rootSentence` は `<` を含まないので結論に影響しない。
- (d) `Th(ℝ) ⊄ Th(ℂ)`。ここで `Th(M) := {σ | M ⊧ σ}`。ℂ の理論は ℝ の理論の**拡張ではない**。
- (e) 埋め込み `ℝ → ℂ` は単射な環準同型であり、存在文 `rootSentence` の真理は ℂ で成立する一方、全称文 `∼rootSentence` の真理は保存されない（(c) から従う）。
- コメントに「複素数が実数内の矛盾を真にした」と書かない。

**P1.4**（外延的同値から無矛盾性文の内部同値は出ない）は Phase 3 に送る（`docs/made_canonicity_audit.md`）。

## Phase 2: Gödelian ascent

以下、`T : ArithmeticTheory` は Δ₁ 表示 `[T.Δ₁]` を持ち、`[𝗜𝚺₁ ⪯ T]` を満たすとする。

**G1 単段階の strict ascent**（分類 B: Foundation の Gödel II の直接再利用。**新定理ではない**）
`[Consistent T]` のもとで
- `T ⊬ T.consistent`
- `T ⪱ T ∪ T.Con`

**段階の型**: `Stage` = 算術理論とその Δ₁ 表示の組。`Stage.next S := S ∪ S.Con`（和集合の表示は Foundation の `Theory.Δ₁.add`）。
`ascent T 0 = T`、`ascent T (n+1) = (ascent T n).next`。

**L2.1 IΣ₁ 包含の伝播**: `∀ n, 𝗜𝚺₁ ⪯ (ascent T n)`。

**L2.2 Σ₁ 健全性の伝播**（分類 A: Foundation 上の新規 Lean 証明。数学的には既知）
`S` が Σ₁ 健全（`SoundOnHierarchy 𝚺 1`）かつ `𝗜𝚺₁ ⪯ S` なら、`S.next` も Σ₁ 健全。
証明の要点（論文 前稿 脚注18 と同じ）: `S ∪ {Con_S} ⊢ σ`（σ ∈ Σ₁）なら演繹定理で `S ⊢ Con_S → σ`。この文は Σ₁（Π₁ → Σ₁）なので S の Σ₁ 健全性から ℕ で真。`Con_S` は ℕ で真（S は無矛盾）。よって σ は ℕ で真。

**L2.3 段階の無矛盾性**: T が Σ₁ 健全なら `∀ n, Consistent (ascent T n)`。

**G2 有限段階の非完結性**（分類 A/B: G1 を各段に適用。L2.2 が新規の Lean 部分）
T が Σ₁ 健全なら、すべての n について
- `(ascent T n) ⊬ (ascent T n).consistent`
- `(ascent T n) ⪱ (ascent T (n+1))`
- `m < n → (ascent T m) ⪱ (ascent T n)`

**G2-sharp 仮定の必要性**（分類 A: Foundation の `height_union_incon_eq_one` を使う。論文 Portrait 3 の形式版）
T が無矛盾（`[Consistent T]`）なら、`T' := T ∪ T.Incon`（= T + ¬Con_T）について
- `Consistent T'`
- `Inconsistent (T' ∪ T'.Con)`（次の段は矛盾する）
- `¬ T'.SoundOnHierarchy 𝚺 1`（ただし `𝗥₀ ⪯ T` のもとで）

つまり G2 の仮定を「無矛盾性」に弱めると、一段目で上昇が止まる。

**G3 ω 段階**（分類 B/A: Foundation の `exists_prenex_axiomatization_turingOmega` を再利用し、ℕ 健全性から無矛盾性を導いて G1 を適用）
`T_ω := T ∪ T.Conω`（`T.Conω = {¬□_Tⁿ⊥ | n ∈ ℕ}`）とする。`ℕ ⊧* T` のもとで、ある Π₁ 文の集合 U とその Δ₁ 表示があって
- `T ∪ T.Conω ≊ T ∪ U`
- `(T ∪ U) ⊬ (T ∪ U).consistent`（**U の Δ₁ 表示から作った**無矛盾性文）
- `(T ∪ U) ⪱ (T ∪ U) ∪ (T ∪ U).Con`
- `T ∪ T.Conω` は `T ∪ T.Conω ⪱ (T ∪ U) ∪ (T ∪ U).Con` を満たす

注意: (1) 「任意の理論列の合併は r.e.」は偽であり、ここでは Foundation が**明示的に構成した一様 Δ₁ 表示**を使う。(2) `Con(T_ω)` は選んだ表示に依存する。(3) `T_ω` と `⋃ₙ ascent T n` の同値性（形式化された演繹定理 `Con(T_n) ↔ ¬□_T^{n+1}⊥` が必要）は**本仕様の対象外**とし、`docs/open_problems.md` に記録する。

**G4 条件付き non-finality**（分類 A: G1 と L2.2 からの系）
- `Eligible S :≡ 𝗜𝚺₁ ⪯ S ∧ S.SoundOnHierarchy 𝚺 1`（S は Δ₁ 表示つき）
- `ProperExtension S S' :≡ S ⪱ S'`（Foundation の `⪱` をそのまま使う。独自定義しない）
- 定理: `∀ S, Eligible S → ∃ S', ProperExtension S S' ∧ Eligible S'`
- 量化順序の対比: `¬ ∃ S, Eligible S ∧ ∀ σ, ℕ ⊧ σ → S ⊢ σ`（どの適格な段階も全真理を証明しない。Foundation の Gödel I から）

自明化の検査: `Eligible` は拡張について何も述べず、`ProperExtension` は Foundation の定義である。結論 `∃ S'` は仮定に埋め込まれていない。

## 監査要件（全定理）

- `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` を使わない。
- 各定理の `#print axioms` が `[propext, Classical.choice, Quot.sound]` の部分集合であること。

## Phase 3（予備）: D1–D3 が決めないもの

（2026-10-10 追記。実装前に `docs/made_canonicity_audit.md` §4 の紙上の議論に基づいて固定。）

抽象 provability（Foundation の `Provability T₀ T`、言語 L は自己参照可能、`[L.DecidableEq]`）について:

**M1** 任意の provability `𝔅` と任意の文 `π` に対し、`disjProv 𝔅 π` は `(disjProv 𝔅 π) σ = 𝔅 σ ⋎ π` を満たす provability である（D1 は 𝔅 の D1 から従う）。

**M2** `𝔅` が D2 を満たせば `disjProv 𝔅 π` も D2 を、`𝔅` が D2 と D3 を満たせば `disjProv 𝔅 π` も D3 を満たす。`π` に条件はない。

**M3** `T₀ ⊢ (disjProv 𝔅 π).con 🡘 𝔅.con ⋏ ∼π`。

算術（`T` は Δ₁ 表示、`𝗜𝚺₁ ⪯ T`、Σ₁ 健全）、`𝔅 = T.standardProvability`、`π = 𝔅(∼𝔅.con)`、`𝔅' = disjProv 𝔅 π` について:

**M4** 外延的正しさ: すべての文 σ について `ℕ ⊧ 𝔅' σ ↔ T ⊢ σ`。また `𝔅' σ` は Σ₁ 文（`ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1`）である（2026-10-10 追記、M4′）。

**M5** `T ⊬ 𝔅.con 🡒 𝔅'.con`、`T ⊢ 𝔅'.con 🡒 𝔅.con`（Σ₁ 健全性不要）、`T ⊬ 𝔅'.con`。

M4–M5 の意味: 同じ理論について D1–D3 を満たし ℕ で正しい二つの provability が、T で同値でない無矛盾性文を持つ。made-canonicity が「その」無矛盾性文を D1–D3 経由で選ぶという主張に対する制約である。made-canonicity 自体（特に条件 (ii)）は形式化しない。
