# Dependency audit（Phase 0）

## 1. 固定したバージョン

| 項目 | 値 |
|---|---|
| Lean | `leanprover/lean4:v4.34.0`（commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`） |
| Foundation | <https://github.com/FormalizedFormalLogic/Foundation> commit **`dfaa003d0c4533c89ca72ae513d9c055fd3fe7bf`**（2026-10-10T08:39:40Z, "add(FirstOrder/Arithmetic): `Δ` induction `𝗜𝚫` (#1039)"） |
| mathlib4 | `5ed2965256430c3649e86755f9576b54eca72435`（inputRev `v4.34.0`、Foundation の manifest に従う） |
| その他の推移的依存 | `lake-manifest.json` に全 SHA を記録（batteries `f2effa3d`, aesop `355695d5`, Qq `6a489d9a`, proofwidgets `106ff4fa`, plausible `118aa17e`, Forgive `727e3a36`, doc-gen4 `a6521b2d` ほか） |

`lakefile.toml` は Foundation を `rev = "dfaa003d…"`（ブランチ名ではなく SHA）で固定している。`master` には追従しない。

## 2. ライセンスと出典

- Foundation: Apache-2.0。著者（CITATION.cff）Shogo Saitou, Mashu Noguchi。主要開発者は README による。本プロジェクトは Foundation の定理を `import` して呼び出すだけで、ソースのコピーや改変はしていない。
- mathlib4: Apache-2.0。

## 3. ビルド手順（再現用）

```bash
cd MeaningDimension
lake update                      # lake-manifest.json の SHA を使う
lake exe cache get               # mathlib のビルド済みキャッシュ
LAKE_CONFIG=lake-cache.toml lake cache get --service ffl \
  --repo FormalizedFormalLogic/Foundation --package Foundation   # Foundation のキャッシュ
lake build
scripts/check_proofs.sh
```

Foundation のキャッシュ（`cache.formalizedformallogic.org`）がない場合は Foundation を手元でビルドすることになり、数時間かかる。

## 4. 確認した既存宣言（`#check` で取得した正確な型）

名前空間は `FFL.FirstOrder.Arithmetic`（指示書の `LO.FirstOrder.Arithmetic` は**古い**。現在は `FFL.`）。また指示書の `T ∪ T.Con` という表記は正しいが、旧版の `T + T.Con` ではない。

```text
consistent_unprovable : ∀ (T : ArithmeticTheory) [inst : Theory.Δ₁ T] [𝗜𝚺₁ ⪯ T] [Entailment.Consistent T],
  T ⊬ ↑(Theory.consistent T)
inconsistent_unprovable : ∀ (T : ArithmeticTheory) [inst : Theory.Δ₁ T] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1],
  T ⊬ ∼↑(Theory.consistent T)
instance [Consistent T] : T ⪱ T ∪ T.Con                    -- Second.lean（無名インスタンス）
instance [T.SoundOnHierarchy 𝚺 1] : T ⪱ T ∪ T.Incon        -- Second.lean
Theory.consistent : (T : Theory L) → [T.Δ₁] → 𝚷₁.Sentence    -- := .mkPi (∼provabilityPred T ⊥)
Theory.Con : (T : Theory L) → [T.Δ₁] → ArithmeticTheory     -- := {T.consistent.val}
Theory.Δ₁ : Theory L → Type                                  -- ★ Prop ではなくデータ
StrictlyWeakerThan.of_unprovable_provable : [𝓢 ⪯ 𝓣] → 𝓢 ⊬ φ → 𝓣 ⊢ φ → 𝓢 ⪱ 𝓣
exists_prenex_axiomatization_turingOmega : ∀ {T} [T.Δ₁] [𝗜𝚺₁ ⪯ T],
  ∃ U x, (∀ σ ∈ U, ℬ[<, ℒₒᵣ].PrenexHierarchy 𝚷 1 σ) ∧ T ∪ Theory.Conω T ≊ T ∪ U
Theory.Conω T := Set.range T.standardProvability.conItr      -- {¬□ⁿ⊥ | n}
ProvabilityAbstraction.con_unprovable : [Diagonalization T₀] [𝔅.HBL] [T₀ ⪯ T] [Consistent T], T ⊬ 𝔅.con
height_union_incon_eq_one : [Consistent T] → (T ∪ T.Incon).height = 1
ArithmeticTheory.SoundOnHierarchy T Γ k := T.SoundOn (ℬ[<, ℒₒᵣ].Hierarchy Γ k)
```

### 4.1 `Theory.Δ₁` は「表示」である（論文にとって重要）

```lean
class Δ₁ (T : Theory L) where
  ch : 𝚫ᴬ₁.Semisentence 1                       -- 公理を定義する Δ₁ 論理式
  mem_iff : ∀ φ, ℕ ⊧/![⌜φ⌝] ch.val ↔ ∃ σ ∈ T, φ = σ   -- 標準モデルで公理集合をちょうど定義
  isDelta1 : ch.ProvablyProperOn 𝗜𝚺₁             -- Σ形と Π形の同値が IΣ₁ で証明可能
```

- `T.consistent` は集合 `T` ではなく**このインスタンスの `ch`** から作られる。論文の `α`（表示）は Foundation では `Theory.Δ₁` インスタンスに当たる。
- Foundation の Gödel II は「**IΣ₁ で証明可能に Δ₁**」な表示に対する定理である。これは made-canonicity の条件 (i)（Σ₁）**より強い**仮定である。
- Feferman の α*（Σ₁ ∧ Π₁）はこの型の値として書けない。したがって Foundation の G2 を α* に「適用」することはできず、Feferman 現象は抽象 provability 層（`ProvabilityAbstraction.Provability T₀ T`、D1 だけを要求）で扱うことになる。
- 同じ集合 `T` に複数の `Δ₁` インスタンスがありうる。`T.Con` はインスタンスの選び方に依存する。

## 5. 公理監査

- Foundation の `Foundation/` 以下に `axiom` 宣言は**ない**（`grep -rnE "^(private |protected )?axiom "` で0件）。
- `sorry` の出現は2ファイル。いずれも**コメント内**（`Arithmetic/PeanoMinus/Q.lean:54` は `--` 行、`Syntax/Classical/BinderNotation.lean:1039–1056` は `/- … -/` ブロック内）。
- `#print axioms` の結果（このコミット、`logs/` に保存）:

```text
consistent_unprovable                      : [propext, Classical.choice, Quot.sound]
inconsistent_unprovable                    : [propext, Classical.choice, Quot.sound]
𝗜𝚺₁ ⪱ 𝗜𝚺₁ ∪ 𝗜𝚺₁.Con（inferInstance）       : [propext, Classical.choice, Quot.sound]
𝗣𝗔 ⪱ 𝗣𝗔 ∪ 𝗣𝗔.Con（inferInstance）           : [propext, Classical.choice, Quot.sound]
exists_prenex_axiomatization_turingOmega   : [propext, Classical.choice, Quot.sound]
height_union_incon_eq_one                  : [propext, Classical.choice, Quot.sound]
```

- **前作との違い**: companion repo（`nishida-mathematics`）が使った Foundation `c28942b7` では `ISigma1_delta1Definable : 𝗜𝚺₁.Δ₁` が `axiom` だった。現行 `dfaa003d` では `𝗣𝗔⁻` の Δ₁ 性（`PeanoMinus.delta1`）と帰納法図式の Δ₁ 性（`Incompleteness/Definability.lean`）が**証明**されており、`#synth 𝗜𝚺₁.Δ₁` は `Theory.Δ₁.instUnion` で解決される。追加の数学的公理はない。

## 6. mathlib だけで足りるか

足りない。mathlib には一階算術の構文の算術化、provability predicate、Gödel II はない（2026-10 時点の mathlib `v4.34.0` を `grep` した範囲。網羅的調査ではない）。ℝ/ℂ の事実（Phase 1.3）には mathlib を直接使う。

## 7. 指示書と現行 Foundation の不一致

| 指示書の記述 | 現行（`dfaa003d`） |
|---|---|
| `LO.FirstOrder.Arithmetic` | `FFL.FirstOrder.Arithmetic` |
| `T ⪱ T ∪ T.Con` | 同じ（無名 `instance`。名前付き定理ではない） |
| `ProvabilityAbstraction`, `RosserProvability` | 存在（`Incompleteness/ProvabilityAbstraction/*.lean`, `Incompleteness/RosserProvability.lean`） |
| `lake new MeaningDimension math` | 使わない。Foundation 互換の `lakefile.toml` を手書きし、mathlib は Foundation 経由で固定 |
