# Strategy delta：旧指示書 → 新指示書

作成日: 2026-10-11。ブランチ `reorientation`（`main` の `d65b6b0` から分岐）。

- 旧: `~/src/godelex/CLAUDE_CODE_LEAN4_PHILMATH_INSTRUCTIONS.md`（2026-10-10 21:23、26.6KB）
- 新: `~/src/godelex/CLAUDE_CODE_PHILMATH_REORIENTATION.md`（2026-10-11 04:41、20.9KB）

**優先順位**: 新指示書は旧指示書より新しい。両者が矛盾するときは、新指示書の「哲学的主張・撤回事項・停止条件」を優先する。旧実装と旧検証成果は削除しないが、旧方針は自動では引き継がない。

## 1. 撤回・変更された方針

| # | 旧指示書 | 新指示書 | 本プロジェクトでの扱い |
|---|---|---|---|
| S1 | 論文に忠実な語彙として `made-canonicity` を保持し、Phase 3 で D1–D3 との関係を監査する（旧 §0, §3 Phase 3） | made-canonicity は**以前 Claude が技術的動機から提案した概念**で、著者は自身の西田理解に対応しないと明示した。論文の中心から撤去する方向で改稿案を作る（新 §2） | `docs/retired_made_canonicity.md` に来歴・反例・撤回理由を保存する。Lean コード（`MadeCanonicity.lean`）は削除しない。**修復・再導入の研究は、著者の別途の承認があるまで始めない。** |
| S2 | `made-to-making asymmetry` を論文の語彙として保持する | 語句は捨てない。ただし「作られたものと作る働きが**不可分である**」という含意を優先して再検討する。公理表示と証明可能性関係への静的な一対一対応を西田哲学とはしない | `author_position_*.md` と `claims_matrix.md` で、旧 §3.5 の「never in reverse」「公理 = made、証明可能性 = making」を reinterpret / remove 候補にする |
| S3 | 目的は Lean 4 による形式化。Phase 0 → 1 → 2 → 3（→ 4–6 任意） | Lean の証明を増やすことは第一目的ではない。まず著者の哲学的主張を確定し、Gödel との数学的な対応範囲を監査する。Phase A → B → C で**停止**し、著者の承認を求める | Lean の新規実装はしない（Phase D は承認後）。既存81宣言は再監査のみ |
| S4 | 成果物の中心は `paper_insert.md`（検証済み命題を原稿に挿入する形） | 成果物の中心は著者の立場の文書化（`author_position_jp/en.md`）、主張の分類（`claims_matrix.md`）、境界（`godel_boundary.md`）、構成二案（`restructure_options.md`） | `paper_insert.md` は旧方針の成果物として保存する。論文本体には適用しない。Phase D で個別に再照合する |
| S5 | 論文の主張を A（Lean で証明可能）/ B（既存定理の系）/ C（条件付き）/ D（哲学的主張・予想）に分類 | 加えて、哲学側を `original author claim / source-verified Nishida / heuristic analogy / mathematical result` に区別する。Gödel との対応を `is a special case / structural analogy / philosophical extension / unsupported` に分類する | 両方の分類軸を併用する |
| S6 | 西田は論文の背景（[3] 生成的矛盾論文に委譲） | 西田本人に帰属させる記述は、原典の該当箇所を照合したものに限る。`著者による解釈 / 西田本文に帰属可能な記述 / 比較研究上の仮説` を区別する | 原典照合は青空文庫の本文で行い、照合できなかったものは `not verified` と記録する（`source_reading_audit.md` §4） |
| S7 | 意味次元生成は Phase 5 の抽象インターフェース（探索）として扱う | 著者の時間論（いま・過去の再構成・未来の非存在・行為的直観）と、意味の遡及的再解釈を明示的な研究対象にする。ただし `next : Stage → Stage` の機械的反復と同一視しない | `godel_boundary.md` で、`ascent` が「完全に事前決定された列」である点を境界として明記する |
| S8 | 作業は main ブランチで commit | 作業は新ブランチで行い、編集は別稿ファイルで行う | ブランチ `reorientation` を作成した。原稿 `PhilMath2.tex` には手を触れない |
| S9 | （規定なし） | **著者の考えを西田より上位に置く**（著者の追加指示、2026-10-11） | 著者のテーゼが哲学的な基準。西田は従属する資源・比較対象。食い違いがあっても著者の定式化は直さず、西田への帰属だけを直す（`author_position_jp.md` 優先順位の原則） |

## 2. 引き継ぐもの（両指示書で一致）

- Lean のガードレール: `sorry` / `admit` / 空虚な `axiom` / `native_decide` / ゴールを仮定に埋め込む形式化を禁止。`#print axioms` 相当の監査、ソース・テスト・commit SHA を提示する（`scripts/check_proofs.sh`）。
- 哲学的テーゼを Lean の `axiom` に置かない。帰結を証明して「哲学を証明した」と書かない。
- 既知の結果（Feferman 1960, 1962, Turing 1939 など）を新発見と呼ばない。
- 数学的に誤っている箇所は、原文を残した対比表と訂正案で示す。原稿を上書きしない。
- 知らないことは創作しない。曖昧な箇所は `unknown` と記録する。

## 3. 新たに加わった禁止事項（新 §3.1, §7）

- Gödel II が、未来の存在論的な未成立、行為的直観、意味次元一般の可能無限、あらゆる矛盾の将来的成立、意識・記憶、LLM の原理的不可能性を証明した、と書かない。
- `T_{n+1} = T_n + Con(T_n)` を「未だ存在しない未来そのものの生成」の完全モデルとしない。これは**限定的な数学的対応例**にとどまる。
- 単調拡張 `T ⊆ T'` だけで新しい意味次元をすべて表せるとしない。
- 「未来はまだ存在しない」を「未来についての数学的推測は不可能」と読み替えない。
- 「過去は現在のナラティブとして現れる」を「客観的な出来事は起きていなかった」と読み替えない。
- 著者の時間論を McTaggart、現象学、西田原典などの一般理論へ、勝手に翻訳したり同一視したりしない。

## 4. 停止条件

Phase C（`docs/restructure_options.md`）で二案を提出したら停止する。著者の選択なしに論文本体の大規模な書き換え（Phase D）を始めない。
