# Lean 宣言の再監査（Phase A）

作成日: 2026-10-11。監査対象: Lean ソース commit `54dc740`（`54dc740..d65b6b0` 間で `.lean` の差分なし、`git diff --stat` で確認）。ブランチ `reorientation` 上で再実行。

## 0. 起点の確認

| 項目 | 結果 |
|---|---|
| 報告済みソース commit `54dc740` | 存在する。完全ハッシュ `54dc740172dcd7bff08f270eac559750d70ac25d`（2026-10-10 21:59 +0900） |
| 報告済み検証ログ commit `d65b6b0` | 存在する。完全ハッシュ `d65b6b033183d6ce926c550a47e55964ba7fb8f2`。`main` の HEAD |
| 作業ツリー | 再監査前はクリーン。新ブランチ `reorientation` を作成 |
| 旧ログの保存 | `logs/archive/d65b6b0/`（`build.log`, `axioms.log`, `env.txt`）に複製してから再実行 |
| 依存版 | Lean 4.34.0（`lean-toolchain`）、Foundation `dfaa003d0c4533c89ca72ae513d9c055fd3fe7bf`、mathlib `5ed2965256430c3649e86755f9576b54eca72435`（`lake-manifest.json`、`logs/env.txt`） |
| `scripts/check_proofs.sh` 再実行 | **ALL CHECKS PASSED**（2026-10-10T19:48:08Z = 2026-10-11 04:48 JST）。禁止構文なし、`lake build` 成功（2085 jobs）、公理監査 OK、Tests/Spec.lean の `example` 48件がビルドで検査済み |

## 1. 「81宣言」の内訳（宣言数と独自定理数の区別）

`Tests/AxiomAudit.lean` の「81 declarations」は、`MeaningDimension.*` モジュールに属する **theorem / def 定数の数**である。これには、コンパイラが自動生成した補助定数が含まれる。`scratchpad` の監査スクリプト（`findDeclarationRanges?` と名前の規則で判定）で分類した結果:

| 区分 | 数 |
|---|---|
| 公理監査が数える定数（theorem + def） | **81** |
| └ 手書きの theorem（instance 3件を含む） | 49 |
| └ 手書きの def（構造体の射影 `Stage.theory`, `Stage.presentation` を含む） | 11 |
| └ 自動生成（`.eq_1` 方程式補題、`match_` 補助関数、構造体の `noConfusion` / `casesOn` / `recOn` / `mk.inj` / `mk.injEq` / `mk.sizeOf_spec` / `ctorIdx` / `noConfusionType`） | 21 |
| 公理監査が数えない手書き宣言（`structure Stage`） | 1 |
| **手書き宣言の合計** | **61**（theorem 49、def 11、structure 1） |

注意:

- 自動生成の `FFL.FirstOrder.ProvabilityAbstraction.Provability.con.eq_1` は Foundation 名前空間の方程式補題で、`EffectiveAscent` と `MadeCanonicity` の**両方のモジュールで生成され、2回数えられている**。81 の中の相異なる名前は 80。
- 自動生成定数の公理も監査済み（すべて標準3公理の部分集合）。
- **数学的に新しい定理の数: 0。** 手書きの theorem 49件はすべて、既知の定理（Gödel II、Hilbert–Bernays–Löb、Feferman など）か、その初等的な系である。「本プロジェクトで新たに書いた Lean の証明」と「数学的に新しい定理」を混同しない。

証明の性格による内訳（手書き theorem 49件 + D1 の証明を含む def `disjProv`）:

| 記号 | 意味 | 件数 |
|---|---|---|
| R | 既存ライブラリの一つの事実をほぼそのまま再掲（`inferInstance`, `rfl`, 1行の適用） | 13 |
| S | 既存の補題を数個組み合わせた短い導出 | 29 |
| M | 数段の論証（演繹定理・Σ₁ 健全性・高さ・Löb などを組み合わせる。数学的には既知） | 7 |
| def | 定義（`disjProv` は D1 の証明を含む） | 12 |

M の7件: `Stage.sigma1Sound_next`（L2.2）、`inconsistent_next_of_union_incon`（G2s2）、`not_sigma1Sound_union_incon`（G2s3）、`G3`、`disj_HBL2`、`disj_HBL3`、`standard_disj_con_not_implied`。

## 2. 手書き宣言の全件表

「型クラス仮定」は、コンパイル済み環境で各定数の型を pretty-print し、`[...]` の束縛を機械的に抜き出したもの。明示引数の仮定（例: `Eligible S`、`T ⊆ U`）は含まない。公理列の `std3` は `[propext, Classical.choice, Quot.sound]`。

| # | ファイル:行 | 宣言 | 種別 | 台帳 ID | 証明の性格 | 数学的位置 | 公理 | 型クラス仮定（Lean の型から抽出） |
|---|---|---|---|---|---|---|---|---|
| 1 | `ComplexNumbers.lean:28` | `ComplexNumbers.real_sq_add_one_ne_zero` | theorem | P1.3a | S | known | std3 | — |
| 2 | `ComplexNumbers.lean:31` | `ComplexNumbers.complex_sq_add_one_eq_zero` | theorem | P1.3b | R | known | std3 | — |
| 3 | `ComplexNumbers.lean:35` | `ComplexNumbers.rootSentence` | def | P1.3c | def | — | [propext] | — |
| 4 | `ComplexNumbers.lean:38` | `ComplexNumbers.real_not_models_rootSentence` | theorem | P1.3c | S | known | std3 | — |
| 5 | `ComplexNumbers.lean:45` | `ComplexNumbers.complex_models_rootSentence` | theorem | P1.3c | S | known | std3 | — |
| 6 | `ComplexNumbers.lean:50` | `ComplexNumbers.theoryOf` | def | P1.3d | def | — | std3 | `[Nonempty M]`, `[FFL.ORingStructure M]` |
| 7 | `ComplexNumbers.lean:55` | `ComplexNumbers.theoryOf_real_not_subset_complex` | theorem | P1.3d | S | known | std3 | — |
| 8 | `ComplexNumbers.lean:64` | `ComplexNumbers.ofReal_injective` | theorem | (台帳外) | R | known | std3 | — |
| 9 | `EffectiveAscent.lean:38` | `Godel.G1_unprovable` | theorem | G1a | R | known (Gödel II) | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[Consistent T]` |
| 10 | `EffectiveAscent.lean:43` | `Godel.G1_strict` | theorem | G1b | R | known | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[Consistent T]` |
| 11 | `EffectiveAscent.lean:52` | `Godel.Stage` | inductive | (台帳外) | def | — | std3 | — |
| 12 | `EffectiveAscent.lean:56` | `Godel.Stage.theory` | def | (台帳外) | def | — | std3 | — |
| 13 | `EffectiveAscent.lean:57` | `Godel.Stage.presentation` | def instance | (台帳外) | def | — | std3 | — |
| 14 | `EffectiveAscent.lean:61` | `Godel.Stage.next` | def | (台帳外) | def | — | std3 | — |
| 15 | `EffectiveAscent.lean:66` | `Godel.ascent` | def | (台帳外) | def | — | std3 | `[T.Δ₁]` |
| 16 | `EffectiveAscent.lean:71` | `Godel.ascent_zero_theory` | theorem | (台帳外) | R | trivial (rfl) | std3 | `[T.Δ₁]` |
| 17 | `EffectiveAscent.lean:73` | `Godel.ascent_succ` | theorem | (台帳外) | R | trivial (rfl) | std3 | `[T.Δ₁]` |
| 18 | `EffectiveAscent.lean:76` | `Godel.Stage.subset_next` | theorem | (台帳外) | R | trivial | std3 | — |
| 19 | `EffectiveAscent.lean:78` | `Godel.Stage.le_next` | theorem | (台帳外) | R | trivial | std3 | — |
| 20 | `EffectiveAscent.lean:83` | `Godel.ISigma1_le_ascent` | theorem | L2.1 | S | known (trivial) | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]` |
| 21 | `EffectiveAscent.lean:91` | `Godel.models_consistent` | theorem | (台帳外; L2.2 の補題) | S | known | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[Consistent T]` |
| 22 | `EffectiveAscent.lean:98` | `Godel.Stage.sigma1Sound_next` | theorem | L2.2 | M | known corollary | std3 | `[𝗜𝚺₁ ⪯ S.theory]`, `[S.theory.SoundOnHierarchy 𝚺 1]` |
| 23 | `EffectiveAscent.lean:118` | `Godel.sigma1Sound_ascent` | theorem | L2.3 | S | known corollary | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[T.SoundOnHierarchy 𝚺 1]` |
| 24 | `EffectiveAscent.lean:127` | `Godel.consistent_ascent` | theorem | L2.3 | S | known corollary | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[T.SoundOnHierarchy 𝚺 1]` |
| 25 | `EffectiveAscent.lean:139` | `Godel.G2_unprovable` | theorem | G2a | S | known corollary | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[T.SoundOnHierarchy 𝚺 1]` |
| 26 | `EffectiveAscent.lean:145` | `Godel.G2_strict` | theorem | G2b | S | known corollary | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[T.SoundOnHierarchy 𝚺 1]` |
| 27 | `EffectiveAscent.lean:151` | `Godel.G2_strict_of_lt` | theorem | G2c | S | known corollary | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[T.SoundOnHierarchy 𝚺 1]` |
| 28 | `EffectiveAscent.lean:168` | `Godel.consistent_union_incon` | theorem | G2s1 | S | known | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[Consistent T]` |
| 29 | `EffectiveAscent.lean:176` | `Godel.inconsistent_next_of_union_incon` | theorem | G2s2 | M | known | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[Consistent T]` |
| 30 | `EffectiveAscent.lean:196` | `Godel.not_sigma1Sound_union_incon` | theorem | G2s3 | M | known | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[Consistent T]` |
| 31 | `LimitStage.lean:38` | `Godel.models_ascent` | theorem | G3a | S | known (trivial) | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[ℕ↓[ℒₒᵣ] ⊧* T]` |
| 32 | `LimitStage.lean:46` | `Godel.models_iUnion_ascent` | theorem | G3a | S | known (trivial) | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[ℕ↓[ℒₒᵣ] ⊧* T]` |
| 33 | `LimitStage.lean:56` | `Godel.models_conItr` | theorem | G3b | S | known | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[T.SoundOnHierarchy 𝚺 1]` |
| 34 | `LimitStage.lean:66` | `Godel.models_Conω` | theorem | G3b | S | known | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[T.SoundOnHierarchy 𝚺 1]` |
| 35 | `LimitStage.lean:71` | `Godel.models_turingOmega` | theorem | (台帳外; G3 の補題) | S | known | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[ℕ↓[ℒₒᵣ] ⊧* T]` |
| 36 | `LimitStage.lean:75` | `Godel.G3` | theorem | G3 | M | known corollary | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[ℕ↓[ℒₒᵣ] ⊧* T]` |
| 37 | `MadeCanonicity.lean:46` | `MadeCanonicity.disjProv` | def | M1–M2 | def(D1 証明込み) | elementary | std3 | `[L.ReferenceableBy L]` |
| 38 | `MadeCanonicity.lean:60` | `MadeCanonicity.disj_apply` | theorem | (台帳外) | S | elementary | std3 | `[L.ReferenceableBy L]` |
| 39 | `MadeCanonicity.lean:64` | `MadeCanonicity.disj_HBL2` | theorem instance | M1–M2 | M | elementary | std3 | `[L.ReferenceableBy L]`, `[𝔅.HBL2]` |
| 40 | `MadeCanonicity.lean:70` | `MadeCanonicity.disj_HBL3` | theorem instance | M1–M2 | M | elementary | std3 | `[L.ReferenceableBy L]`, `[𝔅.HBL2]`, `[𝔅.HBL3]` |
| 41 | `MadeCanonicity.lean:77` | `MadeCanonicity.disj_HBL` | theorem instance | M1–M2 | R | elementary | std3 | `[L.ReferenceableBy L]`, `[𝔅.HBL]` |
| 42 | `MadeCanonicity.lean:82` | `MadeCanonicity.disj_con_iff` | theorem | M3 | S | elementary | std3 | `[L.ReferenceableBy L]`, `[L.DecidableEq]` |
| 43 | `MadeCanonicity.lean:93` | `MadeCanonicity.selfRefutation` | def | M4 | def | — | std3 | `[T.Δ₁]` |
| 44 | `MadeCanonicity.lean:97` | `MadeCanonicity.standardDisj` | def | M4 | def | — | std3 | `[T.Δ₁]` |
| 45 | `MadeCanonicity.lean:105` | `MadeCanonicity.standard_disj_sigma1` | theorem | M4 | S | elementary | std3 | `[T.Δ₁]` |
| 46 | `MadeCanonicity.lean:110` | `MadeCanonicity.standard_disj_models_iff` | theorem | M4 | S | elementary | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[T.SoundOnHierarchy 𝚺 1]` |
| 47 | `MadeCanonicity.lean:119` | `MadeCanonicity.standard_disj_con_not_implied` | theorem | M5 | M | elementary (Löb) | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[T.SoundOnHierarchy 𝚺 1]` |
| 48 | `MadeCanonicity.lean:130` | `MadeCanonicity.standard_disj_con_implies` | theorem | M5 | S | elementary | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]` |
| 49 | `MadeCanonicity.lean:136` | `MadeCanonicity.standard_disj_con_unprovable` | theorem | M5 | R | known (G2 for HBL predicates) | std3 | `[T.Δ₁]`, `[𝗜𝚺₁ ⪯ T]`, `[T.SoundOnHierarchy 𝚺 1]` |
| 50 | `NonFinality.lean:26` | `Godel.Eligible` | def | G4 | def | — | std3 | — |
| 51 | `NonFinality.lean:30` | `Godel.ProperExtension` | def | G4 | def | — | std3 | — |
| 52 | `NonFinality.lean:34` | `Godel.Eligible.next` | theorem | G4 | S | known content | std3 | — |
| 53 | `NonFinality.lean:41` | `Godel.G4` | theorem | G4 | S | known content | std3 | — |
| 54 | `NonFinality.lean:46` | `Godel.Eligible.iterate_next` | theorem | G4i | S | known corollary | std3 | — |
| 55 | `NonFinality.lean:54` | `Godel.Eligible.properExtension_iterate_next` | theorem | G4i | S | known corollary | std3 | — |
| 56 | `NonFinality.lean:63` | `Godel.not_exists_eligible_proves_all_truths` | theorem | Q1 | S | known corollary | std3 | — |
| 57 | `NonFinality.lean:71` | `Godel.consistency_proved_later` | theorem | Q2 | R | trivial | std3 | `[T.Δ₁]` |
| 58 | `TheoryExtensions.lean:24` | `provable_mono` | theorem | P1.1 | R | known | std3 | — |
| 59 | `TheoryExtensions.lean:28` | `unprovable_of_refuted` | theorem | P1.2a | S | known (elementary) | std3 | `[L.DecidableEq]`, `[T ⪯ U]`, `[Consistent U]` |
| 60 | `TheoryExtensions.lean:37` | `not_models_and_models_neg` | theorem | P1.2c | R | known | std3 | `[Nonempty M]`, `[Tarski.Structure L M]` |
| 61 | `TheoryExtensions.lean:43` | `not_models_of_refuted` | theorem | P1.2b | S | known (elementary) | std3 | `[T ⪯ U]`, `[Nonempty M]`, `[Tarski.Structure L M]`, `[M↓[L] ⊧* U]` |

## 3. `theorem_ledger.md` との突き合わせ

| # | 照合項目 | 結果 |
|---|---|---|
| L1 | 台帳の各行の Lean 名が実在するか | **全件実在**する |
| L2 | 台帳の前提条件と実際の型 | 台帳の前提は実際以上に強いか同じ。弱く書かれた行はない。差異: `standard_disj_sigma1` の実際の仮定は `[T.Δ₁]` のみ（台帳 M4 は Σ₁ 健全性まで列挙）。`standard_disj_con_implies` は Σ₁ 健全性を要しない（台帳 M5 は列挙）。どちらも台帳の記述が安全側 |
| L3 | 台帳にない手書き宣言 | 補題: `ascent_zero_theory`, `ascent_succ`, `Stage.subset_next`, `Stage.le_next`, `models_consistent`, `models_turingOmega`, `ComplexNumbers.ofReal_injective`, `MadeCanonicity.disj_apply`。定義: `Stage`, `Stage.theory`, `Stage.presentation`, `Stage.next`, `ascent`。どれも補助的なもので、論文向けの主張はない |
| L4 | 台帳の「Originality」欄 | 「new theorem はない」という記述は正しい。G4 の「new conditional (interface)」は、本プロジェクトで定義した `Eligible` / `ProperExtension` 上の命題という意味で、数学的な新規性ではない |
| L5 | 公理 | 81件すべて `[propext, Classical.choice, Quot.sound]` の部分集合（`rootSentence` は `[propext]` のみ、`match_` 補助関数は `[]`）。`sorryAx` やプロジェクト独自・依存先の `axiom` は使っていない |
| L6 | 台帳の「Build」欄 | 2026-10-11 の再実行で再確認した |

## 4. 前作（companion repository）の Lean との関係（再監査）

論文 §5 末尾と GC 論文 §9・注46・注50 は「Lean 4 で IΣ₁ の上昇を **10段階** 検証した」と書いている。2026-10-11 に `~/src/nishida-mathematics` を再確認した。HEAD は `fdb3b7381966a78ab23b184ebf3622195e7f3b24`（2026-06-15）。

- Lean ファイルは `experiments/wp6/lean/S7Wp6LeanInstantiation.lean`（73行）の **1件のみ**。
- 定理は `wp6_ec2_stage1_ISigma1 : 𝗜𝚺₁ ⪱ 𝗜𝚺₁ + 𝗜𝚺₁.Con := inferInstance`（**第1段階のみ**）。同じファイルのコメントによれば、当時の Foundation は `ISigma1_delta1Definable` を `axiom` として持っていた。
- **「10段階を Lean で検証」は、ローカルのリポジトリでは確認できない。** Zenodo アーカイブ（DOI 10.5281/zenodo.20687363）の中身は今回は見ていない（`unknown`）。
- 本プロジェクトの `G2_strict` は、Σ₁ 健全な T について**すべての有限段階 n** で `Tₙ ⪱ Tₙ₊₁` を示す。Foundation `dfaa003d` 上で、追加の `axiom` はない。論文の記述を直すなら、この結果に差し替えるのが正確（`claims_matrix.md` 参照）。
