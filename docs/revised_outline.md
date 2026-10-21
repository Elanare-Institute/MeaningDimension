# 改訂版の詳細アウトラインと中心命題の定義案

> **2026-10-11 役割変更**: 論文原稿は著者と ChatGPT が作成し、Claude Code の担当は Lean 4 による数学的形式化・証明・反例探索のみになった。この文書は論文の構成・内容に関わるため Claude Code の担当外であり、**記録として保存し、以後は更新しない**。論文への適用は著者と ChatGPT が判断する。

作成日: 2026-10-11。案 A の条件付き承認を受けた最初の提出物。**本文の改稿はまだ行っていない。** 本文は承認後に別ファイルで書く。made-canonicity は復活させない。

## 0. 承認条件とその反映

| # | 著者の条件（2026-10-11） | この文書での反映 |
|---|---|---|
| 1 | 意味次元生成と生成的可能無限を中心に置き、Gödelian Non-Closure は限定的な数学的対応例とする | §1 主論証、§3 アウトライン（Gödel は §7 の一節） |
| 2 | 「いま」による未来の創発は哲学的基盤なので削除しない。本稿は数学哲学の範囲に限定する | 定義 D4、アウトライン §5 |
| 3 | 非単調性は意味次元生成の必要条件としない | 定義 D2 の注。`godel_boundary.md` B1・B3、`author_position_en.md` の用語表を修正済み |
| 4 | modal potentialism との違いは関連文献の原文を精査する。既存理論が完成済みの可能性空間を前提とすると、検証なしに断定しない | §4 に精査結果を記載（原文の照合は実施中。結果を受けて確定） |
| 5 | J4 直観主義に非コミット、J5 発見方法論を短く収録、J6 P vs NP を主論証から除外、J9 T14 を短い比較論点に | 定義 D10・D11、アウトライン §4.4、§6.5、§9、付録 |
| 6 | J2・J3 は著者未決定として保持。生成的真矛盾主義の定義や普遍的主張を AI の判断で変更しない | 定義 D6 は原稿の文言のまま。選択肢は §2 に並記するだけで、確定しない。`claims_matrix.md` の関連行は hold にした |
| 7 | AI 利用の開示と旧稿の審査状況を確認する。過去の原稿・Lean 成果・監査記録は維持する | §6。過去の資料はすべて保存済み |
| 8 | 西田の原典と先行研究の照合状況を維持し、未読・抄録のみ・全文確認済みを区別する | §5（各節が依拠する文献とその照合状態） |

**デスクリジェクトの理由への応答**: 前稿は「著者の真に独創的な哲学的議論を書くことに失敗している」という趣旨の理由でデスクリジェクトされた（著者の要約）。改訂版は、**著者の独自の議論を主論証として一本に通し**、先行研究と Gödel をその論証に仕える位置に置く。

## 1. 主論証の流れ（著者の独自の議論）

1. 数学は、意味の次元を生成しながら進む（意味次元生成）。カタログの34事例は、それが反復して起きてきたことを示す。
2. この生成は無限に可能である。しかもその可能性は、あらかじめ与えられたものから選ばれるのではなく、生成の行為のなかで生まれる（生成的可能無限。著者の公理）。
3. 生成は「いま」の行為として起きる。未来の意味次元はまだ存在せず、現在のどの枠組みもその全体を先取りできない（著者の哲学的基盤。本稿では数学に限って述べる）。
4. 生成は、既存の体系にすでにある限界、つまり四つの door（矛盾・決定不能性・手段の限界・未解決問題）を通って起きる。矛盾の door についての著者のテーゼが生成的真矛盾主義である。
5. したがって、各問いはいつか扱われうるが、すべての問いが一度に扱われる段階はない（量化の順序）。
6. Gödel の非完結性は、このことの厳密だが限定された数学的対応例である。それは、事前に決まった手続きでさえ閉じないことを示す。ただし、可能性そのものの生成までは表さない。
7. この立場は、数学的プラトン主義（完成した真理の全体）とも、標準的真矛盾主義（最終的な矛盾）とも、modal potentialism とも異なる。違いの要点は閉包にある（潜在主義との違いは原文の精査に基づいて述べる、§4）。

## 2. 中心命題の定義案

英文は論文に入れる形の案。日本語の注は著者向け。**D6 は著者の原文のまま**で、J2・J3 の選択肢は並記するだけで確定しない。

**D1（意味次元）** *A meaning dimension of a practice is a rule, or a system of rules, that fixes what counts as an object of the practice, what counts as a question within it, and what can be proved, evaluated, or chosen within it.*
- 典拠: 著者の言葉（新指示書 §1.2「何が対象か／何が問いか／何を証明・評価・選択できるか」）。原稿には意味次元そのものの定義文はない。

**D2（意味次元生成）** 原稿の定義（行61）を保持する: *the creation of a new dimension of meaning that extends the rules of an existing system.* 補足（行107）: *the operation starts from an existing system, requires human agency, and produces a new dimension of meaning that extends the system's rules.*
- 注（承認条件3）: 事例には、同じ言語で新しい公理や証明原理を加える単調な場合（例: 原稿 行155 の反映進行、Gentzen の超限帰納）と、旧体系の定理の一部が新体系で成り立たない非単調な場合（ℝ → ℂ）の両方がある。どちらの性質も定義の条件にはしない。

**D3（生成的可能無限。著者の公理）** 原稿の公理（行82）と様相の説明（行97）を保持する: *Axiom. Meaning-dimension generation is infinitely possible.* — *for any meaning dimension that has been generated, a further one can be generated. It does not mean that all meaning dimensions exist simultaneously or that the process is completed.* 生成的であることの規定（行107, 127）: *the possibilities themselves are created by the act of generation; a meaning dimension does not exist, even as a possibility, until it is generated.*
- 注: modal potentialism との違いの言い方は、§4 の原文精査の結果に基づいて確定する（承認条件4）。

**D4（いまによる生成。著者の哲学的基盤、本稿では数学に限定）** *Generation takes place in the present. What will be generated does not yet exist; no description available now reads off, as a completed whole, the meaning dimensions that may yet be generated.* 本稿では、これを数学の実践についてだけ主張する: *No present mathematical framework fixes in advance the totality of meaning dimensions that mathematics may yet generate.*
- 典拠: 著者のテーゼ T1・T3（`author_position_jp.md`）。
- 主張しないこと: 予測や数学的推測が不可能であること。因果法則の否定。

**D5（意味の遡及。数学に限定）** *A later meaning dimension can change the meaning of earlier mathematical work — what it was a case of, what it demanded, what it achieved — without altering the historical record and without attributing the later meaning to the historical agents.* 事例: ℂ 以後の Cardano・Bombelli の計算、Robinson 以後の Leibniz の無限小、Dedekind 以後の Eudoxus（付録の事例1, 3, 5, 11）。
- 典拠: 著者のテーゼ T5。事例の選択は原稿の付録による。

**D6（生成的真矛盾主義。原稿の文言を保持。J2・J3 は著者未決定）**
- 定義（行119）: *A contradiction — a formal φ ∧ ¬φ, or a case in which practice demands what the system's rules formally exclude, thereby yielding a formal contradiction — is neither an error to be excluded nor a permanent truth to be accepted. It is a transition point: a signal that the current system's rules are insufficient, and that a new meaning dimension can be generated in which the contradiction is made true. … The contradiction is true at its level — within the rules of the current system, both φ and ¬φ hold — but it is not final.*
- 普遍的主張（行28, 123）: *for each contradiction a meaning dimension that makes it true can someday be generated.* / *Every contradiction … is penultimate.*

J2・J3 の選択肢（**並記のみ。確定しない**）:

| | J3: 「その水準で真」をどう読むか | 帰結（本文のどこに影響するか） |
|---|---|---|
| J3-a | **原稿の文言のまま**: 現行体系の規則のもとで φ と ¬φ が両方成り立つ | 表1の注記（古典的 T では T の矛盾）・行151（T + φ が両方を導く）との関係を本文で説明する必要がある |
| J3-b | **要求と規則の衝突として読む**: 体系は φ を反証し、実践は φ を要求する。要求を加えた体系 T + φ が φ と ¬φ を導く（行151 の定式） | 体系そのものは古典的に無矛盾のまま。Lean の no-go（同じ解釈では反証済みの文を真にできない）と両立する |
| J3-c | **水準に添字づけた真理として読む**: 「真」はつねにある水準（場所）で語られ、水準を持たない「端的な真」はない（著者の GC 論文 §6 の議論） | 標準的真矛盾主義との違いを「final でない」ことと「水準を持たない真理の否定」に置く。§8 の閉包の議論と直結する |
| J3-d | **その水準の論理を矛盾許容的とする** | 標準的真矛盾主義との違いは「final でない」ことだけになる。§8 の論じ方が変わる |

| | J2: 「真にする」に制約を課すか | 帰結 |
|---|---|---|
| J2-a | **原稿の文言のまま**（制約を明示しない） | 「任意の再解釈で何でも真にできる」という自明化の反論に、本文の別の箇所で応答する必要がある |
| J2-b | 矛盾を生んだ**要求が新しい次元で満たされる**ことを「真にする」の内容とする | 事例8–11の書き方（真になったのは要求や形式）と一致する |
| J2-c | 要求の充足に加えて、**旧体系の成果が新しい次元から説明できる**ことを課す | 自明化の反論に最も強いが、普遍的主張の範囲が狭まる可能性がある |
| J2-d | 制約は課さず、普遍的主張を**開いた図式**（Russell の any）として述べ、反論には「完成した全体への量化ではない」と応答する | §8 の revenge への応答（原稿 行308）と同じ論法 |

**D7（四つの door）** 原稿 §3.2 を保持: contradiction / undecidability / limits of available means / open problems。*A door is not a cause that compels the next step. It is where the next step can be taken.*（行163）

**D8（いつか、各問いについて）** 原稿 §3.3 を保持: *for each question there is some later stage at which it is handled, not … some stage at which every question is handled.* 「扱う」の二つの意味（解決 / 問いの再構成）。

**D9（Gödelian non-closure。数学的結果、限定的対応例）** *For every theory T that contains IΣ₁, is effectively (Δ₁-)presented and Σ₁-sound, adjoining T's consistency statement yields a strictly stronger theory that is again Σ₁-sound; hence the ascent T, T + Con(T), … never reaches a final stage. Consistency alone does not suffice: T + ¬Con(T) is consistent, but its successor is inconsistent.* 既知の結果（本プロジェクトの Lean で検証済み。数学的新規性はない）。

**D10（発見方法論。短く収録、J5）** *Using potential infinity deliberately, one can work backwards from conditions that a future meaning dimension would have to satisfy, and so arrive at new conjectures and research questions.* アブダクションとの関係は短く触れるだけで、独創性の証明とはしない。典拠: 著者のテーゼ T10。

**D11（T14。短い比較論点、J9）** *Absolute contradictory self-identity is contradictory within the term itself; its realization presupposes generative dialetheism and generative potential infinity, which Nishida did not develop.* 本稿では §9 の短い比較として置く。

## 3. 詳細アウトライン

各節の「素材」は PhilMath2.tex の行番号。「依拠文献」の照合状態は §5。

### §1 Introduction（序論）
- 1.1 問い: 数学が開かれているとはどういうことか。限界としての不完全性の読みと、生成としての読み。
- 1.2 本稿の独自の主張（§1 の主論証 1–7 を要約）。
- 1.3 主張しないこと: Gödel の定理が著者の哲学を証明するとは言わない。D4 は数学の実践に限って述べる。
- 1.4 構成。
- 素材: 新規執筆（現 §1 の Feferman の内包性問題は導入の主題から外す）。

### §2 Meaning-Dimension Generation（意味次元生成）
- 2.1 操作と三つの例（ℂ、Shannon、パーフェクトイド空間）。素材: 行53–61。
- 2.2 既存の語との関係: domain extension、Hilbert の理想元、Lakatos の concept stretching、Wittgenstein の concept formation、**概念工学と open texture**（新規。Tanswell 2018、Shapiro。原文の精読が必要）。素材: 行63–75。
- 2.3 何でないか: 発見・発明・創造ではなく生成。素材: 行99–107（「発明」の定義は典拠を付けるか定義として明示する。C2.15）。
- 2.4 単調な事例と非単調な事例（D2 の注）。
- 削除: 語数の経験的主張（行87、C2.8）。

### §3 The Axiom of Generative Potential Infinity（生成的可能無限）
- 3.1 公理と様相（D3）。根拠 (1)–(5)（行85–95。(1) の語数の主張は除く）。
- 3.2 any と all（Russell）。「いつか、各問いについて」（D8）。素材: 行165–175、308。
- 3.3 Wrigley 2022 への応答。素材: 行173（語の修正: recursive-ordinal recognition ability、「持つと信じる十分な理由がない」。B-14）。
- 3.4 直観主義論理にはコミットしない（J4）。Cook 2026 が、潜在無限なら直観主義論理という Dummett の見方に反論していることに触れる（抄録のみ確認。原文の精読が必要）。

### §4 Modal Potentialism and Generative Potentialism（潜在主義との違い）
- **原文精査の結果を受けて書く（承認条件4）。** 現時点の照合済み事実: Linnebo–Shapiro 2019 は liberal / strict を区別し（p.169）、strict は直観主義論理に導く（pp.181–182）、liberal は古典論理（p.183）。それ以外の論点（可能性の空間が与えられているか、拡張の行為者、意味の変化）は精査中。
- 4.1 liberal / strict の区別（原文に即して）。
- 4.2 可能性は与えられているか（原文に即して。断定しない）。
- 4.3 行為者の開放性（原稿 行314、GC §8）と、解釈・措定の様相（Studd、Fine）との関係。
- 4.4 意味の変化: 「潜在主義の段階は意味を固定して領域を広げる」（行314）が既存理論にどこまで当てはまるか（精査結果に従う）。

### §5 Generation in the Present（いまの生成と意味の遡及。数学に限定）
- 5.1 D4: 未来の意味次元はまだ存在しない。現在の枠組みは全体を先取りできない。
- 5.2 D5: 数学史における意味の遡及（ℂ と Bombelli、Robinson と Leibniz、Dedekind と Eudoxus）。当事者への帰属をしない（付録冒頭 行354 の限定）。
- 5.3 発見方法論（D10、短く）。
- 素材: 新規執筆。著者の時間論の一般形（イデオロギー、ナラティブ、歴史解釈）は別稿に回すと注記する。

### §6 Generative Dialetheism and the Doors（生成的真矛盾主義と四つの door）
- 6.1 矛盾の三つの読み。D6（著者の原文のまま。J2・J3 の決定に応じて書き方を確定）。素材: 行111–127。
- 6.2 表1と四状態。素材: 行129–151。
- 6.3 他の三つの door。素材: 行153–163（P vs NP の再定式化への言及 行159 は本文から外す。J6）。
- 6.4 無限小の歴史（Berkeley → Weierstrass → Robinson）。素材: 行125。
- 6.5 標準的真矛盾主義者への帰属（行121）は削除するか、Priest の照合後に限定する（B-3）。

### §7 Gödelian Non-Closure as a Limited Mathematical Counterpart（限定的な数学的対応例）
- 7.1 D9 の数学（Σ₁ 健全性の伝播、PA + ¬Con(PA)、ω 段階、実効的な合併の不完全性）。素材: 行177–193 の数学部分、行276、316。
- 7.2 Turing と Feferman の進行（Turing の基礎体系は Gödel の P、Π₁ について。B-12）。経路の選択は実効的でない（Feferman–Spector）。
- 7.3 表示依存性: 非完結性はどの Σ₁ 表示についても成り立ち、付け加わる文は表示に依存する（Feferman 1960 は一次未照合）。
- 7.4 示さないこと: 事前決定された手続き、固定した言語と標準模型。可能性そのものの生成は表さない（`godel_boundary.md` B2, §4）。
- 7.5 Lean による検証の位置づけ（既知の結果の機械検証。新規性は主張しない。「10段階」の記述は訂正、B-6）。

### §8 Against Platonism, Standard Dialetheism, and Closure（閉包をめぐって）
- 8.1 反プラトン主義（素材: 行290–298。C6.3 の議論の飛躍に注意）。
- 8.2 標準的真矛盾主義との違いは閉包にある。Inclosure Schema と Domain Principle（Hallett 1984 p.25 の定式化に直す。B-7）。意味の次元は同一性規準を持たない。素材: 行300–308。
- 8.3 Zermelo 1930 の引用は原典で照合してから使う（C6.6）。

### §9 Nishida（短い比較、J9）
- 9.1 著者の考えが基準であり、西田は資源である（優先順位の原則）。
- 9.2 D11（T14）。照合済みの本文（永遠の今・絶対現在、過去と未来の同時存在）と、反対材料（「無限の過程」）への応答。
- 素材: `author_position_en.md` §3–4、`author_position_jp.md` T14。

### §10 Conclusion

### 付録
- A: 事例カタログ（34事例。`claims_matrix.md` 付録の判定に従う。事例34は本文の論証から外したうえで、カタログにだけ置くか削除するかを決める。J6）。
- B: Lean 検証の要約（1段落とリポジトリ）。
- 謝辞: AI 利用の開示（§6、J7）。

### 削除するもの
made-canonicity（現 §3.5 の静的対応、§4 全体）、五類型の「予測的」分類（Portrait 1・3 は §7 の数学例として使う）、LLM の節（現 §7.2）、「10段階を Lean で検証」、語数の経験的主張、Detlefsen 1979 への誤った帰属（B-11）。

## 4. modal potentialism の原文精査

（未実施。原文の精査は 2026-10-11 の役割変更により中止した。Linnebo–Shapiro 2019 の全文照合済み事項は `source_reading_audit.md` L9 を参照）

## 5. 照合状態の維持（承認条件8）

各節が依拠する文献と照合状態。全文 = 該当頁を読んだ / 抄録 = 抄録のみ / 書誌 = 書誌のみ / 二次 = 二次資料経由 / 未 = 未照合。詳細は `source_reading_audit.md` §4–5。

| 節 | 文献 | 状態 | 執筆前に必要なこと |
|---|---|---|---|
| §2.2 | Lakatos 1976、Wittgenstein 1956、Hilbert 1926 | 未 | 該当箇所の照合 |
| §2.2 | Tanswell 2018 / Cappelen 2018 / Shapiro（open texture） | 抄録 / 抄録 / 書誌 | 精読 |
| §3.2 | Russell 1908（any / all） | 未 | 照合 |
| §3.3 | Wrigley 2022 | 抄録＋部分（WebFetch） | 全文の照合 |
| §3.4 | Cook 2026 | 抄録 | 精読（§4 の精査で対応中） |
| §4 | Linnebo–Shapiro 2019 | 全文（pp.169, 175–184） | 精査中 |
| §4 | Linnebo–Shapiro 2026、Hamkins 2026、Linnebo 2013、Studd 2019、Fine 2006 | 抄録 | 精査中 |
| §6 | Priest 2006、1995/2002 | 未 | 照合 |
| §6.4 | Berkeley 1734、Robinson 1966 | 未 | 照合 |
| §7 | Gödel 1931 注14 | 全文（Meltzer 訳） | — |
| §7.2 | Turing 1939 | 全文（pp.161–228 の該当部） | — |
| §7.2 | Feferman 1962、Feferman–Spector 1962 | 書誌・二次 | 一次照合 |
| §7.3 | Feferman 1960 | 書誌・二次 | 一次照合 |
| §7 | Kurahashi 2021（使う場合） | 全文（arXiv v2 p.7） | — |
| §8.2 | Hallett 1984 p.25、Priest（Domain Principle） | 二次 | 一次照合 |
| §8.3 | Zermelo 1930 | 二次（p.47） | 原典・Ewald 訳で照合 |
| §9 | 西田「絶対矛盾的自己同一」「デカルト哲学について」『善の研究』 | 全文（青空文庫・新字新仮名、頁なし） | 『全集』版で頁を照合 |
| §9 | 西田「行為的直観」「論理と生命」 | 未（青空文庫で未公開） | 『全集』で照合 |
| §9 | Lotman–Urai 2023、Deguchi–Fujikawa 2021 | 未 | 照合 |
| 付録 | 34事例の各典拠 | 大半は未 | Phase E の引用監査 |

## 6. AI 利用の開示と旧稿の審査状況（承認条件7）

| 項目 | 確認結果 | 根拠 |
|---|---|---|
| 旧稿の投稿と審査 | 2026-09-21 投稿、9/24 担当編集者に割り当て。**デスクリジェクト**。理由は著者の要約で「著者の真に独創的な哲学的議論を書くことに失敗している」という趣旨 | 投稿時の往復書簡（10/4 印刷の PDF、全文読了）と、著者からの聞き取り（10/11）。却下通知の原文は未見（連携 Gmail にはない） |
| 投稿区分 | 改訂版は**新規投稿** | 上記 |
| 旧稿の AI 開示（9/23） | 謝辞: "Claude (Anthropic, Claude Opus 4.6) was used for literature search, citation verification, English-language drafting from the author's Japanese-language direction, and editorial formatting. All intellectual content — the made-canonicity criterion, the generative schema, the five-portrait classification, and the philosophical arguments — is the author's own. …" | `Which_Consistency_Statement.pdf`（9/23 版）の謝辞で照合済み。往復書簡の9/23 のメールと一致 |
| 編集長への回答（10/1） | 「The central concept is my own, although the expression "made-canonicity" was proposed by the AI」。会話履歴の提供を申し出ている | 往復書簡 |
| 投稿規定 | 誌の頁に AI 方針の記載はない。旧稿の投稿時に、編集部は OUP の AI 開示方針への準拠確認と、謝辞での開示を求めた | `source_reading_audit.md` §5.3 |
| 改訂版の開示文 | **著者の判断事項（J7）**。今回の作業での AI の役割（本プロジェクトの監査・照合・Lean 検証・構成案）と、made-canonicity を撤回した経緯をどう書くかは、著者が決める | — |
