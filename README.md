# MeaningDimension

*Meaning-Dimension Generation and the Intensionality of Gödel's Second Incompleteness Theorem* の数学的に形式化できる部分を、Lean 4 と [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation)（commit `dfaa003d`）で検証するプロジェクト。

## 検証

```bash
lake exe cache get
LAKE_CONFIG=lake-cache.toml lake cache get --service ffl --repo FormalizedFormalLogic/Foundation --package Foundation
scripts/check_proofs.sh      # 禁止構文の検査 / lake build（仕様テスト込み）/ 公理監査 / 環境記録
```

## 構成

| パス | 内容 |
|---|---|
| `MeaningDimension/Logic/TheoryExtensions.lean` | Phase 1.1–1.2: 単調性、反証済み命題の保存不能性 |
| `MeaningDimension/Examples/ComplexNumbers.lean` | Phase 1.3: 同一の一階文を ℝ と ℂ で評価 |
| `MeaningDimension/Godel/EffectiveAscent.lean` | G1, Σ₁ 健全性の伝播, G2, G2-sharp（PA + ¬Con(PA)） |
| `MeaningDimension/Godel/LimitStage.lean` | G3: ω 段階 |
| `MeaningDimension/Godel/NonFinality.lean` | G4: 条件付き non-finality、量化順序 |
| `MeaningDimension/Godel/MadeCanonicity.lean` | Phase 3（予備）: D1–D3 は無矛盾性文を決めない |
| `Tests/Spec.lean` | `docs/spec.md` から書き起こした仕様テスト（非空虚性の確認を含む） |
| `Tests/AxiomAudit.lean` | 全宣言の公理監査 |
| `docs/` | source map, dependency audit, spec, theorem ledger, dependency graph, scope, open problems, made-canonicity audit, paper insert（英語） |

**本プロジェクトの Lean 定理に、数学的に新しい定理はない**（`docs/theorem_ledger.md`）。論文の哲学的主張は形式化していない（`docs/philosophical_scope.md`）。

## 方針転換（2026-10-11、ブランチ `reorientation`）

新しい指示書 `~/src/godelex/CLAUDE_CODE_PHILMATH_REORIENTATION.md` に従い、made-canonicity を論文の中心から撤回し、著者の哲学的立場を記述し直したうえで、Gödel との対応範囲を監査した。Lean コードは変更していない。旧方針の成果物（`paper_insert.md`、`made_canonicity_audit.md` など）は保存してあり、論文本体には適用しない。

| 文書 | 内容 |
|---|---|
| `docs/strategy_delta.md` | 旧指示書からの方針変更点 |
| `docs/source_reading_audit.md` | 入力資料ごとの読了状況、最新稿 `PhilMath2.tex` と旧稿の差分、西田原典の照合、投稿上の事実 |
| `docs/lean_inventory_audit.md` | 公理監査の「81宣言」の内訳（手書き60、自動生成21。ほかに手書きの構造体1）と台帳との突き合わせ |
| `docs/retired_made_canonicity.md` | made-canonicity の来歴・反例・撤回理由、残る数学的結果 |
| `docs/author_position_jp.md` / `docs/author_position_en.md` | 著者の哲学的テーゼ一覧（日・英）。西田本文の照合結果 |
| `docs/claims_matrix.md` | 最新稿の全主張の分類（retain / reinterpret / remove / investigate）と訂正案 |
| `docs/godel_boundary.md` | Gödel・Feferman・Lean 成果と著者の存在論の境界 |
| `docs/restructure_options.md` | 論文再構成の二案と推薦（**著者の承認待ち**） |

## 役割変更（2026-10-11、最優先）

論文原稿は著者と ChatGPT が作成する。Claude Code の担当は、Lean 4 による数学的な形式化・証明・反例探索と、その検証報告だけである。報告は `docs/math_verification_report.md`。論文の構成・内容に関わる文書（`revised_outline.md`、`restructure_options.md`、`claims_matrix.md`、`author_position_*.md` など）は記録として保存し、以後は更新しない。新しい命題は、著者と ChatGPT から具体的な仕様を受け取ってから実装する。
