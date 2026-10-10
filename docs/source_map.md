# Source map（Phase 0）

作成日: 2026-10-10。対象論文: *Meaning-Dimension Generation and the Intensionality of Gödel's Second Incompleteness Theorem*。

## 0. 入力資料の所在と読了状況

| # | 指示書上の名前 | 実際に見つかったファイル | 状態 |
|---|---|---|---|
| 1 | `PhilMath2.pdf`（最新稿、LaTeX ソースのテキスト印刷） | **見つからない**。探索範囲: `~/Downloads`, `~/Documents`, `~/Desktop`, `~/src`（深さ4）, Spotlight 全体, Google Drive（`title contains 'PhilMath'` / `fullText contains 'made-canonicity'`）。原本 `.tex` も見つからない。 | **未入手**。最新稿との差分確認は**実施不能**。 |
| 2 | `paper_draft.pdf`（旧稿、27頁） | `~/Downloads/paper_draft.pdf`（pdfTeX, 作成 2026-10-09 13:28Z, 27頁） | **全文読了**（pypdf で抽出）。抽出時の欠落は合字（fi/ff/fl）とダッシュのみ。本文・付録・参考文献 [1]–[59] すべて揃っている。 |
| 3 | `paper draft.md`（旧稿の Markdown 版） | `~/Downloads/paper_draft.md`（2026-06-15、同一内容のコピー `paper_draft (1).md` あり）と旧版 `~/Downloads/files - 2026-06-15T210006.698/paper_draft.md` | **全文読了**（新しい方）。ただし**これは #2 の Markdown 版ではない**。別論文 *Generative Contradiction: Reading Gödel with Nishida Kitarō*（Philosophy East and West 向け、論文 #2 の参考文献 [3]）である。旧版の md は見出し構造のみ照合した（同一構成・約1,150語少ない）。 |
| 4 | `appendix_catalog.md` | `~/Downloads/appendix_catalog.md`（2026-10-09） | **全文読了**。#2 の付録 A と実質同一（正規化した語列の一致率 0.96。残りの差は数式組版と引用形式「著者 年」/「[番号]」だけ）。 |
| 5 | `Which_Consistency_Statement_final.pdf`（前稿） | `~/Downloads/files - 2026-09-14T115720.870/Which_Consistency_Statement_final.pdf`（31頁） | **全文読了**。同名の別版（`Which_Consistency_Statement.pdf` 9/23、`_zenodo*.pdf` 9/21・9/30）は**未読**。 |

補足: `~/src/nishida-mathematics`（論文が言及する companion repository、Zenodo DOI 10.5281/zenodo.20687363）も確認した。

**以下の「新稿」は #2 `paper_draft.pdf`（10月9日）を指す。** `PhilMath2.pdf` と同一である保証はない。PhilMath2 が入手できたら本表の差分欄を再点検する必要がある。

## 1. 稿間の差分（前稿 → 新稿）。数学的に重要なもの

| ID | 箇所 | 前稿（Which Consistency Statement, 9月） | 新稿（paper_draft.pdf, 10月） | 評価 |
|---|---|---|---|---|
| Δ1 | Feferman の α* の定義 | `α*(x) = α(x) ∧ ¬∃y<x Prf_α(y, ⌜0=1⌝)`（**有界**量化子） | `α*(x) = α(x) ∧ ¬∃y Prf_{α↾x}(y, ⌜0=1⌝)`（**非有界**、x 以下の公理に制限） | 前稿版は Δ₀ 連言なので α* は Σ₁ のまま。Feferman の定理（Σ₁ 数え上げなら Con は証明不能）がそのまま適用され、**Feferman の反例にならない**。新稿で正しく修正されている。前稿の脚注2「Π₁ claim」も有界なら誤り。 |
| Δ2 | D2 の根拠 | 「D2 は Prf が Σ₁（決定可能）であることに依存」 | 「D2 は任意の数え上げ α で成り立つ（α* でも）」 | 新稿の方が正確（Feferman 1960）。 |
| Δ3 | D3 の導出（§4.2） | 脚注49: `PA ⊢ σ → Prov(⌜σ⌝)`（**内部の含意**） | 表示式: `T ⊢ φ ⇒ T ⊢ Prov(⌜φ⌝)` for Σ₁ φ（**メタレベルの推論規則**） | **新稿で後退**。D3 に必要なのは形式化された Σ₁ 完全性 `T ⊢ σ → Prov(⌜σ⌝)`（内部含意）であり、新稿の表示式は D1 の Σ₁ 制限にすぎない。散文の「provable Σ₁-completeness」は正しい。表示式の修正を提案する（`docs/paper_insert.md` §6）。 |
| Δ4 | 逆向き（D1–D3 ⇒ made-canonicity?） | 「真に Σ₂ で D1–D3 を満たす述語の存在は未解決」 | 「Σ₁ より複雑で D1–D3 を全部満たす述語は示されていない」 | 構文的な読みでは反例が容易に作れる（`docs/made_canonicity_audit.md` §3）。 |
| Δ5 | 「矛盾」の地位 | （別論文 [3] 6月版）「西田の矛盾は真矛盾ではない」「生成に矛盾は不要」 | §3.1「現行体系の規則のもとで φ と ¬φ が両方成り立つ」（generative dialetheism） | **立場が変化**。さらに新稿の §3.2/表1 は「古典的 T では最後の行は T が矛盾することを意味する」とし、矛盾の door を「T ⊢ ¬φ かつ実践が φ を要求、T+φ が両方を導く」と読み替えている。§3.1 と §3.2 の間に緊張がある。形式化できるのは §3.2 の読みだけ。 |
| Δ6 | Lean 検証の記述（§5 末） | 「IΣ₁ ≺ IΣ₁+Con(IΣ₁) ≺ … を **10段階まで** Lean で検証」 | 同じ記述 + DOI | **事実と不一致**。companion repo の Lean は第1段階（`wp6_ec2_stage1_ISigma1 : 𝗜𝚺₁ ⪱ 𝗜𝚺₁ + 𝗜𝚺₁.Con := inferInstance`）のみ。10段階は Python の GL prover による反例モデル（Claim 3）。6月版 [3] の脚注26も「第1段階」と書いている。さらに当時の Foundation（`c28942b7`）は `ISigma1_delta1Definable` を `axiom` として持っていた。 |
| Δ7 | 構成 | 西田テクスト（§2）、潜在主義（§6）、Auerbach、系譜（§9）を詳述 | 意味次元生成（§2）、生成的真矛盾主義（§3）、doors（§3.2）、someday-for-each（§3.3）、反プラトン主義・反潜在主義（§6）、LLM（§7.2）、付録カタログを追加。西田部分は [3] へ移動 | 構成上の変更。 |
| Δ8 | Kurahashi 引用 | 「Rosser 述語は D2 と D3 を同時に満たさない [Kurahashi, Cor 3.3]」＋「Löb から従う」 | 同じ（脚注なし） | 主張自体は正しい（D1 は Rosser 述語で成立し、Con^R が証明可能なので Löb の議論から D2∧D3 は不可）。**Cor 3.3 という位置は未確認**。 |

## 2. 論文の主張と形式化候補（新稿基準）

分類: **A** = 明示された体系の下で Lean で証明可能 / **B** = 既存定理の再利用・系 / **C** = 追加定義の下での条件付き命題 / **D** = 哲学的主張・予想。

| 節 | 原文の主張（要約・原文語彙を保持） | 形式化候補 | 分類 | 依存仮定 | 判断保留・注記 |
|---|---|---|---|---|---|
| §1 | Feferman の α*: T が無矛盾なら α* は α と同じ公理を数え上げるが、Con_{α*} は PA で証明可能 | Foundation の `Theory.Δ₁` は「IΣ₁ で証明可能に Δ₁」な表示しか許さないため、α*（Σ₁∧Π₁）は**表現不能**。抽象 provability 層でなら扱える | B（既知: Feferman 1960） | T ⊇ IΣ₁, T 無矛盾 | Phase 3 |
| §2.3 | **Axiom**: meaning-dimension generation is infinitely possible（potential infinite） | 形式化しない。Phase 5 でインターフェース化した場合も「仮定」としてのみ置く | **D**（哲学的公理） | — | Lean の `axiom` にはしない |
| §2.4, §6.1 | 発見ではなく生成。C 構成前に `i² = −1` は真理値を持たない | 形式化対象外 | D | — | 反プラトン主義 |
| §3.1 | 任意の矛盾について、それを真にする意味次元が**いつか**生成されうる（「次の段階で」ではない） | 形式化しない。ただし反例的な no-go を証明: 同じ言語・同じ解釈・古典的無矛盾性を保ったまま、反証済みの文を真にはできない | D（主張本体）/ A（no-go） | 古典論理 | 「made true」は**解釈の変更**としてしか形式化できない（§3.2 の読み） |
| §3.1, §2.1 | `x²+1=0` は R における矛盾で、C の構成がそれを真にした | ℝ ⊨ ¬∃x(x·x+1=0)、ℂ ⊨ ∃x(x·x+1=0)。**同一の一階文**を**異なる構造**で評価。Th(ℝ) ⊄ Th(ℂ) | A | mathlib, Foundation の意味論 | **指示書の警告どおり**: これは「反証可能な文」であって ℝ における真矛盾ではない。ℂ への移行は量化領域の変更 |
| §3.2 | 四つの door: contradiction / undecidability / limits of available means / open problems。表1の論理的四状態とは別 | 表1（provable / refutable / undecidable / contradictory）は T 相対で定義可能。door は形式化しない | A（表1）/ D（door 分類） | 古典的 T では「contradictory」は T の矛盾と同値 | |
| §3.2 | Gödel I（Rosser 形）: 無矛盾で実効的に公理化された十分強い体系は決定不能文を持つ | Foundation `incomplete_GR` 等 | B | `[T.Δ₁] [𝗜𝚺₁ ⪯ T] [Consistent T]` | 再利用のみ |
| §3.3 | `for each question, some later stage` と `one stage for all questions` の区別。後者は不完全性定理で否定 | 量化順序の違いを具体モデルで示す（Phase 5）。G2/G3 から「どの実効段階も全問を処理しない」は形式化可能 | A（G2/G3 の系）/ D（「各問がいつか handled」） | G2 の仮定 | 前者を Gödel II から導けると主張しない |
| §3.3 | Turing 1939: 真の Π₁ 文はすべて反映進行のある段階で証明可能。Feferman 1962: uniform reflection で全算術文 | Foundation に超限進行の形式化はない（`Reflection/` は有限反復と ω のみ） | B（既知だが未形式化） | 順序数記法、実効性 | Phase 6。大型案件 |
| §3.4 (i) | Self-specification: 対角化補題が Gödel 文を固定する | Foundation `Diagonalization`, `gödel_spec` | B | — | |
| §3.4 (ii) | Excess: Gödel 文は真だが証明不能 | `unprovable_gödel`、G1 | B | Consistent T | |
| §3.4 (iii) | Incorporation: 無矛盾性文の追加で真に強い理論 | **G1**: `T ⪱ T ∪ T.Con` | B | `[T.Δ₁] [𝗜𝚺₁ ⪯ T] [Consistent T]` | 既知の帰結 |
| §3.4 (iv) | Non-completion: 「Σ₁-soundness propagates, and the process iterates」 | **G2**: Σ₁ 健全性の伝播補題 ＋ 全段階での G1 | A（Foundation 上の新規 Lean 証明、数学的には既知） | `[T₀.Δ₁] [𝗜𝚺₁ ⪯ T₀] [T₀.SoundOnHierarchy 𝚺 1]` | 無矛盾性だけでは不足（PA+¬Con(PA)、Portrait 3）。Lean で反例も示す |
| §3.4 | 有限段階の後 ω 段階（Turing–Feferman） | **G3**: T_ω = T ∪ {¬□ⁿ⊥} の Δ₁ Π₁ 公理化に G1 を適用 | A/B | 同上 ＋ 一様 Δ₁ 表示 | Con(T_ω) は**選んだ表示に依存**（made-canonicity の論点そのもの） |
| §3.5 | made-to-making asymmetry: 公理 = made、証明可能性 = making。多くの公理化が同じ帰結集合を生成 | 「同じ帰結集合 ≠ 同じ表示」は Foundation で `T ≊ U` と `Δ₁` データの区別として表現できる | C | — | 非対称性の哲学的解釈は D |
| §4.1 | **Definition 1 (made-canonicity)**: (i) α は Σ₁、(ii) α は自分の証明可能性関係の情報を埋め込まない（Π₁ の非存在節を含まない） | (i) は形式化可能（Foundation は Δ₁ を要求）。(ii) は構文的十分条件 / 意味的不変条件 / 規範的条件に分けて検討 | C（(i)）/ **未定義**（(ii)） | — | `docs/made_canonicity_audit.md` |
| §4.2 | D1–D3 は made-canonicity から**帰結**する | D1–D3 の導出に使われているのは (i) だけで、(ii) は使われていない（論文自身の議論でも） | B（(i) から D1–D3: Hilbert–Bernays–Löb, Feferman 1960） | T ⊇ IΣ₁、α が T で数え上げ | (ii) は導出に寄与しない |
| §4.2 | 逆向きは未解決 | 構文的な読みでは反例あり。証明可能同値を法とする読みでも反例候補あり | C/A | — | `made_canonicity_audit.md` §3–4 |
| §5 P1 | Gödel 文: generative | G1/G2 | B | | |
| §5 P2 | Henkin 文: 証明可能（Löb）、inert | Foundation `Löb.lean` | B | | Phase 4 |
| §5 P3 | PA + ¬Con(PA): 無矛盾だが Σ₁ 非健全、¬Con(T) を証明、Con(T) は反証可能、halting | Foundation `height_union_incon_eq_one` を使い、**T ∪ T.Con が矛盾する**ことを Lean で示す | A | Consistent T（T = PA 等） | G2 の仮定が必要であることの反例として Phase 2 で実施 |
| §5 P4 | 透明な真理述語 / Liar: 古典では explosion、LP では quarantine | Foundation `Tarski.lean`。LP は Foundation の範囲外 | B / 範囲外 | | Phase 4 |
| §5 P5 | α*・Prov^R: vacuous | Rosser は Foundation `RosserProvability.lean`。α* は抽象層で | B / C | | Phase 3–4 |
| §5 表2 | generative/inert/halting/explosive/vacuous は「予測的」 | **哲学的分類ラベル**。Lean が予言・証明したとは書かない | D | | |
| §6.3 | 生成的上昇の技術的署名は Σ₁ 健全性（無矛盾性より強い） | G2 の仮定と反例（PA+¬Con）で裏付けられる部分のみ | A（部分） | | |
| §7.2 | LLM は意味次元生成ができない（構造的理由） | 形式化しない | **D** | — | Gödel II から導いたと主張しない |
| 付録 | 34事例 | 形式化対象として抽出するのは 3（ℂ）、9（Gödel）、14（Gentzen は既知・未形式化）、17（Goodstein は範囲外）だけ。実際に Lean 化するのは 3 と 9 | A（3, 9）/ 範囲外 | | 他は歴史的・解釈的 |

## 3. 原文の意味を変更する必要がある箇所（コード前の提案）

1. **「矛盾を真にする」の形式的読み**。§3.1 の文字どおりの読み（「現行体系の規則のもとで φ と ¬φ が両方成り立つ」）は、古典的で無矛盾な体系では形式化できない（体系が矛盾してしまう）。形式化では §3.2 の読み、すなわち「T ⊢ ¬φ、かつ T とは**別の解釈・別の言語・別の量化領域**で φ が充足される」を採用する。これは原文の主張を弱めた読みであり、**生成的真矛盾主義そのものの形式化ではない**と明記する。
2. **made-canonicity 条件 (ii)**。「Π₁ 節を含まない」という構文的定義は、論理的同値な書き換えで判定が変わる（`made_canonicity_audit.md`）。Lean では (ii) を定義せず、(ii) の候補を三層（構文的・意味的・規範的）に分けて監査に留める。
3. **Non-completion の数学的版**。原文 §3.4(iv) は「Σ₁ 健全性が伝播し過程が反復する」。Lean では「T₀ が Σ₁ 健全なら、すべての有限段階 T_n が Σ₁ 健全で G1 の仮定を満たす」と、ω 段階 T_ω の別定理に分ける。**超限段階**（Turing–Feferman）は対象外。
