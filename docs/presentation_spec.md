# 仕様: 次段階の表示依存性（G5、修正案 B。実装前に固定）

この文書は実装より先に書いた。`Tests/PresentationSpec.lean` のテストは**この文書の文言**から書き起こし、実装の都合で変えない。仕様を変えるときは、まずこの文書を改訂し、テストも改訂する。

## 0. 背景

`math_verification_report.md` §F。ACSI の AC9（作る働きは、段階だけから前もって決まった `next` ではない）には、ゲーデル側の有限段の Con 上昇の中に対応物がない（上昇 `T ↦ T ∪ {Con_T}` は段階から計算で決まる）。G5 は、ゲーデル側で AC9 にもっとも近い形の命題を証明する: **次の段階 `T ∪ {Con}` は、理論（公理集合）だけからは決まらず、表示に依存する。**

表示の選択を ACSI の「外から来る経験」と同じように扱ってよいかは、著者が結果を見て判断する（著者の表明、2026-10-20）。この文書と実装はその判断をしない。

## 1. 前提と記法

- `T : ArithmeticTheory`、与えられた Δ₁ 表示 `α := [T.Δ₁]`、`[𝗜𝚺₁ ⪯ T]`、`[T.SoundOnHierarchy 𝚺 1]`（Σ₁ 健全）。
- 表示 `d : T.Δ₁` について、`□_d` は Foundation の標準的な可証性述語、`Con_d := ¬□_d ⊥`（Foundation の `Theory.consistent`）、`T ∪ {Con_d}` は Foundation の `T ∪ T.Con`（表示 `d` から作る）。
- `⊥ ⋏ ⊤ˢ` は `⊥` を `⊤` の `s` 個の連言で水増しした文（Foundation の `Semiformula.padding`、Craig の構成と同じ）。

## 2. 定義（Lean 名。名前空間 `MeaningDimension.Godel`）

- `ρ_T`: Σ₁ 文 `□_α(¬Con_α)`（「T は自分の無矛盾性文の否定を証明する」）。
- `inconWitness T : 𝚺ᴬ₀.Semisentence 1`: `ρ_T` の Δ₀ 母式 θ。`𝗜𝚺₁ ⊢ ρ_T ↔ ∃s θ(s)` を満たすものを Foundation の `ISigma1.exists_matrix_provable_of_sentence` で選ぶ。
- `ghostCh T : 𝚫ᴬ₁.Semisentence 1`（幽霊公理の定義式）: 「`x = ⌜⊥ ⋏ ⊤ˢ⌝` かつ `θ(s)` を満たす `s < x` がある」。
- `ghostPresentation T : (∅ : ArithmeticTheory).Δ₁`: 定義式は `ghostCh T`。Σ₁ 健全性により、ℕ では何も定めない。
- `twisted T : T.Δ₁`（以下 β）: α と `ghostPresentation T` の和の表示（Foundation の `Theory.Δ₁.add`）を、`T ∪ ∅ = T` で T に移したもの。定義式は `α(x) ∨ ghostCh(x)`。

## 3. 命題

**G5.1（β は T の Δ₁ 表示である）** `twisted T : T.Δ₁` が構成できる。すなわち、その定義式は ℕ でちょうど T の公理を定め、かつ 𝗜𝚺₁ で証明可能に Δ₁ である（`Theory.Δ₁` の型が要求する条件）。

**G5.2（鍵の補題）** `𝗜𝚺₁ ⊢ □_α(¬Con_α) → □_β ⊥`。

**G5.3** `𝗜𝚺₁ ⊢ Con_β → Con_α`。したがって `T ∪ {Con_β} ⊢ Con_α`。

**G5.4** `T ∪ {Con_α} ⊬ Con_β`。

**G5.5（次の段階は真に異なる）** `T ∪ {Con_α} ⪱ T ∪ {Con_β}`。特に `¬ (T ∪ {Con_α} ≊ T ∪ {Con_β})`。

**G5.6（次の段階は理論だけからは決まらない）**
(a) 表示 `d₁ d₂ : T.Δ₁` で、`¬ (T ∪ {Con_{d₁}} ≊ T ∪ {Con_{d₂}})` となるものがある。
(b) 任意の `F : ArithmeticTheory → ArithmeticTheory` について、`¬ ∀ d : T.Δ₁, F T ≊ T ∪ {Con_d}`。

**非空虚性** G5.4–G5.6 を `𝗜𝚺₁` と `𝗣𝗔` に実例化する。

## 4. 証明の見通し

- G5.1: ℕ での定義性は、Σ₁ 健全性から `T ⊬ ¬Con_α`（Foundation `con_unrefutable`）を得て、`ρ_T` が ℕ で偽であることから従う。Δ₁ 性は、Craig の構成（Foundation `CraigTrick.lean`）と同じく、有界量化子と Δ₀ 母式による。
- G5.2: 𝗜𝚺₁ の任意のモデル V で、`ρ_T` の証人 `s` から `⌜⊥ ⋏ ⊤ˢ⌝` が β の公理になり、内部の連言除去で `□_β ⊥`。
- G5.3: α の公理は β の公理（Foundation `provable_standardProvability_imp_of_Δ₁Class_subset`）。
- G5.4: もし `T ∪ {Con_α} ⊢ Con_β` なら、G5.2 と合わせて `T ⊢ Con_α → ¬□_α(¬Con_α)`。これは Foundation の `formalized_unprovable_not_con`（Löb の定理から従う）に反する。形式化された演繹定理（報告 B の T2）は使わない。

## 5. 新規性と、言えないこと

- **新規性: なし。** 無矛盾性文が公理集合ではなく表示に依存すること（Feferman 1960）の、Δ₁ 表示による一例である。
- β は人工的な表示である（「T が ¬Con_α を証明したら、⊥ を公理に加える」）。ℕ では α と同じ公理集合を定めるが、𝗜𝚺₁ はそのことを証明できない。
- 表示を固定すれば、次の段階は前もって決まる。G5 が示すのは「理論（公理集合）だけからは決まらない」ことであり、「何によっても前もって決まっていない」ことではない。
- `T ∪ {Con_β}` が `T ∪ {Con_α} ∪ {Con(T ∪ {Con_α})}` と同値であることは示さない（形式化された演繹定理が必要）。
