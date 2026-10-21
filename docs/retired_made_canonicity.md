# Retired: made-canonicity（来歴・反例・撤回理由の保存）

作成日: 2026-10-11。根拠: `CLAUDE_CODE_PHILMATH_REORIENTATION.md` §2。

## 0. 判定

- **made-canonicity は論文本体に適用しない。** 中心概念から撤去する方向で改稿案を作る（`restructure_options.md`）。
- 関連する Lean コード（`MeaningDimension/Godel/MadeCanonicity.lean`）と旧監査（`docs/made_canonicity_audit.md`、`docs/paper_insert.md` §2 Prop. 6–7）は**削除せず保存する**。
- **made-canonicity を修復・再導入する研究は、著者の別途の明示的承認があるまで始めない。**
- 以下の反例が対象にしているのは、made-canonicity という**技術的な規範化**（Definition 1 の条件 (i)(ii) と、そこから D1–D3 を導く論証）である。著者の哲学（意味次元生成、可能無限、行為的直観、時間論）を反証したものではない。そう読んではいけない。

## 1. 来歴

| 時点 | 資料 | made-canonicity の扱い | 確認方法 |
|---|---|---|---|
| 2026-09-14 以前 | `Which_Consistency_Statement_final.pdf`（31頁、`~/Downloads/files - 2026-09-14T115720.870/`） | 題名が *Which Consistency Statement? Made-Canonicity and the Intensionality of Gödel's Second Incompleteness Theorem*。要旨は made-canonicity を「Nishida Kitarō's "from the made to the making" を通じて articulated された、作られたものとそれを超える作る働きの非対称性」に基礎づけている | 10/10 に全文読了。10/11 に要旨と α* の箇所を再照合（抽出テキスト 1–30行、597行、1012行付近） |
| 2026-10-09 | `paper_draft.pdf`（27頁） | §3.5 made-to-making asymmetry、§4 Definition 1 と D1–D3、§5 五類型、要旨・結論 | 10/10 に全文読了。原本は 10/11 時点で `~/Downloads` から消えている。前回セッションの抽出テキストで照合（`source_reading_audit.md`） |
| 2026-10-11 | `PhilMath2.tex`（560行） | 同上。要旨（28行）、§1（45行）、§3.5（195–199行）、§4（201–243行）、§5（245–286行）、結論（342, 346行） | 10/11 に全文読了 |
| 2026-10-11 | 著者の申告（ユーザーのメッセージ） | 「従来の made-canonicity は AI が提案した概念であり、著者の西田理解と対応しないため、論文の中心から撤回します」 | 申告として記録する。提案の経緯（どのセッションで誰が提案したか）は、本プロジェクトの資料からは検証していない（`unknown`）。`~/Downloads` には投稿時の AI 開示文書らしい PDF（`Philosofical mathematica AI開示 - Submission_ _Which Consistency Statement_ ...pdf`）があるが、**未読** |

## 2. 撤回する推論とその理由

| ID | 原稿の推論（PhilMath2.tex） | 撤回理由 | 種別 |
|---|---|---|---|
| R1 | made-to-making asymmetry: 公理 = made（固定・所与）、証明可能性関係 = making、運動は made から making へで「never in reverse」（195–197行）。ゆえに正準的な表示は made だけを記述し、making を折り込まない（199行） | 撤回の根拠は**著者自身の立場**である（著者の考えを西田より上位に置く）。著者は、作られたものと作る働きの**不可分な動的関係**を重視する。公理表示と証明可能性関係への静的な一対一対応や「逆向きはない」という一方向性は、著者の西田理解ではない（新指示書 §1.3, §2）。「作られたものに作る働きを混ぜるべきではない」という規則も西田からは導かない | 哲学的（著者の立場との不一致） |
| R2 | 条件 (i)(ii) は made-to-making asymmetry の「consequences」（215行） | R1 による。加えて、(ii) の「証明可能性関係の情報を埋め込まない」は形式的に未定義で、構文的な読みは論理的同値な書き換えに対して不変でない（`made_canonicity_audit.md` §3, C1–C3） | 哲学的 + 数学的 |
| R3 | D1–D3 は made-canonicity から帰結する（45, 227, 342行） | D1・D3 の導出に使われているのは (i)（Σ₁ 性）だけで、D2 は任意の数え上げで成り立つ（原稿 229–237行自身の議論）。(ii) はどこにも使われていない。(i) から D1–D3 が出ることは Hilbert–Bernays–Löb と Feferman 1960 による**既知**の結果 | 数学的（既知の結果の再ラベル） |
| R4 | made-canonicity が「哲学的に正当化された」無矛盾性文を選ぶ（28行、要旨） | D1–D3、Σ₁ 形、ℕ での外延的正しさの三つを満たしても、無矛盾性文は T 上の証明可能同値を除いても一意に決まらない（**Lean**: §3 の M1–M5）。対応する表示 α' は (ii) の構文的な読みを満たす（紙上、未形式化） | 数学的（反例） |
| R5 | α* は Π₁ 連言のせいで D3 を「precisely」破る（239行） | α* の Con が PA で証明可能なのは正しい。しかし「どの条件が破れるか」は T に依存する。T ⊇ PA なら（本質的反射性により）D1・D2 が成り立つので D3 が破れる。有限公理化された T では D1 が破れうる。さらに、Π₁ 節が構文的にあるかどうかでは振る舞いは決まらない（C1: 無害な Π₁ 節を持つ表示、前稿の有界版 α* は Σ₁ のまま G2 が成り立つ） | 数学的（条件の不足） |
| R6 | Rosser 述語も同じ理由（making の折り込み）で deviant（199, 241行） | Kurahashi の結果（Rosser 述語は D2 と D3 を同時に満たさない）自体は正しい（前回 arXiv:1902.06863 で Cor 3.3 を確認。今回の書誌確認は `source_reading_audit.md`）。しかし「making の折り込み」による分類は導出ではなく、ラベル付けにとどまる | 解釈（導出ではない） |
| R7 | 逆向きは未解決。Σ₁ より複雑で D1–D3 を満たす述語は示されていない（243行） | 構文的な読みでは自明な反例（C3）。証明可能同値を法とする読みでは、`Pr ∨ ¬RFN_Σ₁(T)` が D1–D3 を満たし、T 上でどの Σ₁ 論理式とも同値でない（C4、紙上の証明。非 Σ₁ 性の部分は未形式化）。初等的な議論なので既知の可能性が高く、新規性は主張しない | 数学的（紙上の反例） |
| R8 | 五類型の分類は made/making の立場から「predictive」（284行） | 各類型の数学的事実（Gödel 文、Henkin 文、PA+¬Con(PA)、Tarski/LP、α*/Rosser）は既知の定理で決まる。made/making のラベルから結果を予測したわけではない。降格（`claims_matrix.md`） | 解釈（過大な主張） |

## 3. 前回報告5点の再監査（報告だけを検証済みとして扱わない）

| # | 前回の報告 | 今回照合した根拠 | 判定 |
|---|---|---|---|
| A1 | 条件 (ii) は D1–D3 の証明に使われていない | PhilMath2.tex 229–237行（D1 は「(i) が保証」、D3 は「condition (i)」、D2 は「any numeration whatsoever」）。Lean では (ii) が**定義されていない**ので、Lean の証明が (ii) を使っていないことは自明。Foundation の D1–D3 は `Theory.Δ₁`（IΣ₁ で証明可能に Δ₁ な表示）を仮定しており、(i) より強い | **確認**。ただし主張の範囲は「原稿の論証で (ii) が使われていない」こと。「(ii) が何の役にも立たない」とまでは言っていない |
| A2 | `□'φ := □φ ∨ π` は D1–D3 を保存し、正準性・無矛盾性表示の一意性は導かれない | `MadeCanonicity.lean`: `disjProv`（D1、46–55行）、`disj_HBL2`（64行）、`disj_HBL3`（70行、□ の D2・D3 を仮定）、`disj_HBL`（77行）、`disj_con_iff`（82行）。算術版: `standard_disj_sigma1`（105行、仮定は `[T.Δ₁]` のみ）、`standard_disj_models_iff`（110行）、`standard_disj_con_not_implied`（119行、仮定は `[T.Δ₁] [𝗜𝚺₁ ⪯ T] [T Σ₁-sound]`）。2026-10-11 に再ビルドと公理監査（標準3公理のみ）を確認 | **確認**（Lean）。言えるのは「T ⊬ Con → Con'」まで。「Con' ↔ Con ∧ ¬□(¬Con)」も Lean で確認済み |
| A3 | 対応する公理表示 `α'` の厳密な算術化は未形式化 | `MadeCanonicity.lean` 28–31行のドキュメントで「Informally (not formalized)」と明記。`α'` を `Theory.Δ₁` として構成するコードはない。Foundation は Δ₁ 表示の組合せ（和集合など）を持つが、`Pr_α(⌜¬Con⌝)` を含む表示の `isDelta1` 証明は書いていない | **確認**（未形式化のまま） |
| A4 | 原稿の D3 で推論規則と内部含意が混同されている | PhilMath2.tex 231–235行: 表示式は `T ⊢ φ ⇒ T ⊢ Prov(⌜φ⌝)`（Σ₁ φ についてのメタレベルの推論規則）。D3 に必要なのは形式化された Σ₁ 完全性 `T ⊢ φ → Prov(⌜φ⌝)`（内部含意）。本文の「provable Σ₁-completeness」という語は正しいが、表示式がそれと合っていない。D3 の定義（224行）自体は正しく内部含意で書かれている | **確認**（最新稿でも未修正） |
| A5 | 旧版の Feferman α* で有界量化子を使った誤記 | `Which_Consistency_Statement_final.pdf` の抽出テキスト: 29行（§1）、597行（Portrait 5）、1012行（§5 の分類）がいずれも `α(x) ∧ ¬∃y<x Prf_α(y, ⌜0=1⌝)`。1014行で「The conjunct is Π₁」、1016行で「Con_{α*} is provable in PA」としている。有界版では連言は Δ₀ なので α* は Σ₁ のまま、Feferman 1960 により Con は証明できない。**両方の主張が有界版では誤り**。PhilMath2.tex 37行は非有界・`α↾x` 版で、正しい Feferman の構成 | **確認**（前稿の誤り。最新稿では修正済み） |

## 4. made-canonicity を外しても残る有効な数学的結果

made-canonicity に依存しない形で、次は引き続き使える。どれも**既知の結果か初等的な系**であり、論文の新規性の主役にはしない。

1. **Feferman の内包性**（既知、Feferman 1960）: 外延的に同じ公理集合でも、表示によって Gödel II の判定が変わる（α* の Con は PA で証明可能、標準的な Σ₁ 表示の Con は証明不能）。PhilMath2.tex 35–39行の記述は正しい。
2. **D1–D3 は無矛盾性文を一意に定めない**（Lean、M1–M5。初等的）: Σ₁ 形・ℕ で正しい・D1–D3 を満たす、という三条件をすべて満たしても、T ⊬ Con → Con' となる述語がある。Halbach–Visser や Visser の「どの選択が正準か決めない」という観察と整合する（文献照合は `source_reading_audit.md`）。
3. **Rosser 述語の D2/D3**（既知、Kurahashi）。
4. **Gödel II は Foundation では「IΣ₁ で証明可能に Δ₁ な表示」を前提にしている**（`dependency_audit.md` §4.1）。表示はデータであり、`Stage` 構造体は表示を明示的に持つ。

これらは、案 B（`restructure_options.md`）で「内包性の問題は残すが、正準表示を一意に選ぶとは約束しない」形で使える。

## 5. 撤回後に論証構造をどう組み直すか（新指示書 §8-3）

旧構造:

```
意味次元生成（§2）→ 生成的真矛盾主義（§3.1–3.4）→ made-to-making asymmetry（§3.5）
  → made-canonicity（§4.1）→ D1–D3 が帰結（§4.2）→ 五類型の「予測的」分類（§5）
```

撤去すると、§3.5 → §4 → §5 の連鎖が切れる。§1 で立てた問い「どの無矛盾性文か」に、哲学的原理で答えるという論文の看板が外れる。残る構造は二通りある（詳細は `restructure_options.md`）:

- **案 A**: 意味次元生成と可能無限を主題とし、Gödel・Feferman を**限定的な数学的対応例**として位置づける。§1 の Feferman 問題は導入の主題から外し、「形式的生成の非完結性」の章で、表示依存性という事実として扱う。
- **案 B**: Gödelian non-closure（Σ₁ 健全性の伝播、ω 段階、表示依存性）を主題とし、その哲学的解釈として著者の生成論を論じる。内包性は「正準表示を選ぶ原理」ではなく、「非完結性の語り方そのものが表示に依存する」という論点として残す。

どちらの案でも、§3.5 の「made-to-making」は、作られたものと作る働きの不可分な関係として再記述する候補とし、公理と証明可能性への対応づけは外す。
