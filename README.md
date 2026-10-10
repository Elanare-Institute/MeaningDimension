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
