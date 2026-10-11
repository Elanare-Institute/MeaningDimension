# Source reading audit（入力資料の読了状況）

作成日: 2026-10-11。新指示書 §4 により最初に作成する文書。未知の文章を旧稿で補って「最新版を読んだ」ことにはしない。

読了の区分: **全文読了**（最初から最後まで読んだ）/ **部分**（範囲を明記）/ **照合のみ**（特定箇所を確認）/ **未読** / **未入手**。

## 1. 原稿

| # | 資料 | 所在・版 | 状態 | 根拠・注記 |
|---|---|---|---|---|
| 1 | **`PhilMath2.tex`（最新稿）** | `~/src/godelex/PhilMath2.tex`、92,392 bytes、560行、更新 2026-10-11 04:44、md5 `b09d7e9ab806ab6c6a083a8a6c359bae` | **全文読了**（1–560行。本文・付録 A の34事例・参考文献60件） | `\end{document}` まであり、欠落はない。題名 *Meaning-Dimension Generation and the Intensionality of Gödel's Second Incompleteness Theorem*、著者 `[Author]`（匿名化済み）。**最新の `.tex` は入手済みなので、改稿判断に欠落はない** |
| 2 | `PhilMath2.pdf` | 見つからない（`mdfind -name PhilMath2` は `.tex` のみ） | 未入手 | 新指示書によれば、行末が切れた LaTeX ソースの印刷。`.tex` があるので不要と判断する |
| 3 | `paper_draft.pdf`（旧稿、27頁） | 2026-10-10 には `~/Downloads/paper_draft.pdf` にあった。**2026-10-11 時点で見つからない**（`~/Downloads`、`mdfind`、`~` の深さ5まで、ゴミ箱） | 全文読了（10/10）。原本は現在**所在不明** | 10/10 に抽出したテキスト（1,163行）が scratchpad に残っており、§2 の差分はこれで取った。scratchpad はセッション用の一時領域なので、恒久的な保存が必要なら原本の再配置を著者に依頼する |
| 4 | `appendix_catalog.md` | 2026-10-10 には `~/Downloads/appendix_catalog.md` にあった。**10/11 時点で見つからない** | 全文読了（10/10）。現在所在不明 | 10/10 の照合で #3 の付録 A と実質同一（正規化した語列の一致率 0.96）。最新稿の付録 A は #3 からさらに改訂されている（§2 Δ'7–Δ'10）ので、**付録の監査は最新稿の付録 A で行った**（`claims_matrix.md` 付録 A） |
| 5 | `Which_Consistency_Statement_final.pdf`（前稿、31頁） | `~/Downloads/files - 2026-09-14T115720.870/` | 全文読了（10/10）。10/11 に α* の箇所と要旨を再照合 | `retired_made_canonicity.md` §1, §3 A5 |
| 6 | `Which_Consistency_Statement.pdf`（9/23）、`_zenodo.pdf`（9/21）、`_zenodo (1).pdf`（9/30、9/21 版と同サイズ） | `~/Downloads/` | 未読 | #5 の別版。9/23 版は投稿時に謝辞（AI 開示）を加えた版の可能性がある（#9 の往復書簡による）。内容差は未確認 |

## 2. 最新稿 PhilMath2.tex と旧稿 paper_draft.pdf の差分

方法: 両者を文に分割して正規化し（LaTeX 命令・引用番号・合字の欠落を除去）、相手側で最も近い文との類似度が 0.80 未満の文を抽出した（scratchpad の `diff.py`）。見出しの結合や組版の違いによる偽陽性は手で除いた。

| ID | 箇所 | 旧稿（10/9） | 最新稿（10/11） | 評価 |
|---|---|---|---|---|
| Δ'1 | 要旨 | 長い版。「LLM が意味次元生成を**できない**理由」で締める | 短い版。LLM への言及なし | 主張の弱化 |
| Δ'2 | §3.1 矛盾の定義 | 「A contradiction is neither an error … nor a permanent truth」 | 「A contradiction — a formal φ ∧ ¬φ, **or a case in which practice demands what the system's rules formally exclude, thereby yielding a formal contradiction** — is …」。さらに「生成的真矛盾主義は矛盾についてのテーゼで、他の door は矛盾ではない」の文を追加 | 前回の監査（`source_map.md` Δ5）の緊張に部分的に対応。ただし「both φ and ¬φ hold」（行119）は残る（`claims_matrix.md` B-2） |
| Δ'3 | §3.1 ℝ の例 | 「it asserts the existence of something the system's rules forbid」 | 「is formally refuted by the ordered-field axioms」 | 正確になった |
| Δ'4 | §3.2 表1 と行151 | 表の位置以外は同じ | 同じ | — |
| Δ'5 | §3.3 | Wrigley の段落なし | **Wrigley 2022 の段落を追加**（RORA、認識的な絶対的決定不能性、静寂主義との両立） | 新しい先行研究への応答。照合が必要（`claims_matrix.md` C3.28） |
| Δ'6 | §7.2 LLM | 「something they cannot do」「The reason is structural, not a limitation of current training techniques」 | 「structurally different」「The hypothesis rests on …」「Whether future architectures could perform it is an open question」 | 断定から仮説へ弱化 |
| Δ'7 | 付録8 Russell | 「the collection the paradox demands is not a set at the stage where it is defined and is a set at the next」 | 「This is not the unrestricted Russell set coming into existence: {x ∈ V_α : x ∉ x} … is a well-defined set at V_{α+1}」 | 正確になった |
| Δ'8 | 付録9 Gödel | 「In the dimension so generated, the Liar's form is made true」 | 「What is made true is not the original Liar sentence but its structural pattern in a new dimension」 | 正確になった |
| Δ'9 | 付録10 Tarski | 「In that hierarchy the Liar's form is made true」 | 「As with entry 9, what is made true is the Liar's form in a new dimension, not the original sentence」 | 正確になった |
| Δ'10 | 付録11 超準解析 | （限定なし） | 「What is made true is not the original contradiction as Berkeley stated it … but the demand that drove it」「The rules of *ℝ are not those of ℝ」 | 正確になった |
| Δ'11 | 脚注 | 「DOI: 10.5281/zenodo.20687363」 | 「DOI: [removed for blind review]」 | 匿名化 |
| Δ'12 | 参考文献 | 59件（番号式 [1]–[59]） | 60件（natbib の著者–年式）。Wrigley 2022 を追加 | — |

**変わっていない箇所**（10/10 の監査で指摘し、最新稿でも残るもの）: D3 の表示式（行231–235）、「10段階を Lean で検証」（行286）、made-canonicity の定義と D1–D3 の帰結の主張（§4）、五類型の「予測的」（行284）、Kurahashi Cor 3.3 の引用（行241）。

## 3. 著者の関連論文・資料

| # | 資料 | 所在・版 | 状態 | 根拠・注記 |
|---|---|---|---|---|
| 7 | *Generative Contradiction: Reading Gödel with Nishida Kitarō*（生成的真矛盾主義の独立論文。最新稿の参考文献 `gc_paper`） | `~/Downloads/generative_contradiction_preprint.md`（ファイル更新 8/15、本文の日付「Preprint · 27 July 2026」、282行） | **全文読了**（10/11、1–282行、注 1–50 を含む） | 同じ日付の PDF（`generative_contradiction_preprint.pdf`、27頁、7/27。`~/src/asi/` に同一ハッシュのコピー）は1頁目だけ照合し、題名・日付が一致することを確認した。全文の一致は未確認 |
| 8 | 同論文の旧版 | `Generative_Contradiction_Nishida_Godel.pdf`（6/16）、`Generative_Contradiction_Zenodo.pdf`（6/26、`(1)` は同一ハッシュ）、`~/src/asi/Generative_Contradiction_PEW_blind.pdf`（7/24）、`~/Downloads/paper_draft.md`（6/15、10/10 に全文読了） | 6/15 版のみ全文読了。他は**未読** | 6/15 版から 7/27 版で、西田の矛盾の位置づけが「真矛盾ではない」から「その水準で真だが final でない」に変わっている（`source_map.md` Δ5 の記録と、7/27 版 §2, §6 の照合による） |
| 9 | 投稿時の往復書簡（`Philosofical mathematica AI開示 - Submission_ … .pdf`、7頁） | `~/Downloads/`（印刷日 2026-10-04） | **全文読了**（10/11） | *Which Consistency Statement?* の投稿（9/21）から編集部とのやりとり（〜10/2）。投稿先との関係で重要な事実を含む（§6） |
| 10 | 著者の行為的直観論「行為者にとって純粋経験はすでに行為的である——デザイン実践からの西田哲学再検討」（5頁） | `~/Downloads/nishida_paper.pdf`（2025-12-24） | **全文読了**（10/11） | 著者の西田理解の一次資料として `author_position_jp.md` T4 で参照。英語版 `nishida_paper_en.pdf`（4頁）は1頁目の要旨だけ照合 |
| 11 | P vs NP の companion paper（`da_paper`） | 候補: `~/Downloads/Computational_Directional_Asymmetry_v2.pdf`, `directional-asymmetry-preprint.pdf`, `directional-asymmetry-rev1.pdf` | **未読** | 最新稿の付録34と §3.2 が依存する。今回は読んでいない（`claims_matrix.md` 付録34 は investigate） |
| 12 | companion repository `~/src/nishida-mathematics` | HEAD `fdb3b738`（2026-06-15） | Lean 部分を照合（10/11） | Lean は第1段階のみ（`lean_inventory_audit.md` §4）。Zenodo アーカイブの中身は未確認 |

## 4. 西田の一次テキスト

原典照合はサブエージェントに委託し、結果のうち10件を私が独立に再照合した。

| 項目 | 結果 |
|---|---|
| 取得元 | 青空文庫（作家別作品リスト No.182）。公開中の14作品の全文を `curl` で生のまま取得し、Shift_JIS から復号した。WebFetch（要約が入る）は使っていない |
| 照合した引用 | 60件が取得テキストの完全一致部分文字列であることをスクリプトで確認（サブエージェント）。うち10件を 2026-10-11 に再確認（すべて一致） |
| 主要テキスト | 「絶対矛盾的自己同一」（『思想』202号、1939.3。青空文庫 card 1755、底本: 岩波文庫『西田幾多郎哲学論集Ⅲ』1989、親本: 『西田幾多郎全集』第9巻 1979）。『善の研究』（card 946）。「デカルト哲学について」（card 3216） |
| 限界 | (1) 主要テキストは**新字新仮名**の文庫版で、西田の原表記ではない。(2) 青空文庫には**頁番号がない**ので、『全集』の頁による引用は印刷版で別に確認する必要がある。(3) 「**行為的直観**」（1937）、「**論理と生命**」、「場所」、「弁証法的一般者としての世界」は青空文庫で作業中・未公開（図書カード 404）。これらの論文に依拠する主張は**未照合**。(4) 「世界新秩序の原理」の「永遠の今」は皇室を論じる文脈にある |
| 主な所見 | 「作られたものから作るものへ」は「絶対矛盾的自己同一」にのみ（74回）。同論文は、作られたものが作るものから「離れない」ことを**動物・生物の段階**の特徴とし、「故に作られたものから作るものへではない」と明言する。行為と直観は「矛盾的自己同一」で「何処までも相反する」とされる。詳細は `author_position_en.md` §3 |
| 未発見 | 逐語の「我々は行為によって物を見る」。過去が現在から作り直される・再解釈されるという明言。著者の2025年論文が引く「作ることによって見、見ることによって作る」の逐語形（近い表現は「見ることによって働き、働くことによって見る」） |

## 5. 先行研究（書誌と内容の帰属）

2026-10-11 にサブエージェントが照合した結果（ウェブ検索、公開 PDF のローカル抽出）。**アクセス水準**は、全文 = 該当頁を読んだ / 抄録 = 抄録のみ / 書誌 = 書誌レコードのみ / 二次 = 二次資料経由。WebFetch 経由の抽出（要約モデルを通る）は、その旨を注記した。ペイウォールやアンチボットは回避していない。**この表は Phase E の引用監査の代わりにはならない。**

### 5.1 原稿が引く文献と、原稿が帰属させている内容

| # | 文献 | 書誌 | アクセス | 原稿の帰属内容の照合結果 | 判定 |
|---|---|---|---|---|---|
| L1 | Detlefsen 1979, *J. Phil. Logic* 8: 297–313 | 一致 | 全文（pp.297, 309–310, 313） | **原稿の帰属を支持しない。** 中心論点は、有限主義的な量化子の解釈により Con(T) が Hilbert の計画に関わる意味での無矛盾性を「表現」しないこと（p.309）。注25（p.313）は、Feferman 1960 の仕事で G2 を覆せるという見方を明示的に退けている | **要修正**（C1.3）。代替候補 Detlefsen 2001, *Phil. Math.* 9: 37–71（抄録のみ） |
| L2 | Feferman 1960, *Fund. Math.* 49: 35–92 | 一致（IMPAN の記録） | 書誌。内容は二次（Feferman の回顧 "My route to arithmetization"、Halbach–Visser I p.680） | α* の趣旨（P ⊢ Con_α* となる binumeration）と extensional / intensional の区別は二次資料で確認。原稿の定義式の正確な形と "natural / unnatural presentations" の語が 1960 年論文にあるかは**一次資料で未確認** | 要一次照合 |
| L3 | Feferman 1962, *JSL* 27: 259–316 | 一致 | 書誌。内容は二次（Wrigley 2022 経由、WebFetch） | 全算術真理がある経路で到達可能という趣旨は二次資料で確認。uniform reflection の限定は未確認 | 要一次照合。Feferman–Spector 1962（*JSL* 27: 383–390）の併記を推奨 |
| L4 | Turing 1939, *Proc. LMS* (2) 45: 161–228 | 一致 | 全文（pp.161, 168, 198–212） | **「over PA」は不正確。** 基礎体系は Gödel の体系 P。完全性が証明されているのは「θ(x) vanishes identically」（θ は原始再帰的）の形、つまり Π₁ 文について（p.209–210） | **要修正**（C3.24） |
| L5 | Halbach–Visser 2014 I, II, *RSL* 7: 671–691, 692–712 | 一致 | I は全文、II は抄録と冒頭 | 「three dimensions of intensionality」は I p.680 で確認。ただし三つ目は原文では "the method of obtaining presumed self-reference"（原稿は "fixed-point method"） | 表現を合わせる（C1.5） |
| L6 | Visser 2016（*Gödel's Disjunction*） | **頁は pp.67–90**（原稿は 67–91） | 抄録のみ | 未照合 | 頁の修正 |
| L7 | Visser 2020, *RSL* 13: 269–295 | 一致 | 全文（pp.269–273 精読、全文検索） | "Feferman format"（固定した証明述語と、変化する公理表示）は p.269, 271 で確認。**「G2 は無矛盾性の概念に対して頑健でない」「選択基準を控える」は 2020 年論文では見つからない**（2016 年の章にあるなら頁を特定する必要） | 要修正（C1.6） |
| L8 | Kurahashi 2021（arXiv:1902.06863 v2） | 出版版は *Advances in Mathematical Logic* pp.77–97, doi:10.1007/978-981-16-4173-2_4 | 全文（arXiv v2 p.7） | Corollary 3.3「There exists no Rosser provability predicate of T satisfying both D2 and D3」で一致。出版版の番号は未確認 | 確認（C4.10） |
| L9 | Linnebo–Shapiro 2019, *Noûs* 53: 160–191 | 一致 | 全文（pp.169, 175–184） | liberal / strict の定義（p.169）、strict は直観主義論理（p.181–182）、liberal は古典論理（p.183）で一致。ただし古典論理の結論は様相論理が十分強いという条件付きで、一階論理についての話 | 確認（C6.10） |
| L10 | Linnebo–Shapiro 2026, *Phil. Math.* 34: 100–136 | 一致（doi:10.1093/philmat/nkae020、オンライン 2024-11-12） | 抄録 | 「semi-intuitionistic: set-sized domain は古典的、全集合・全クラスの領域は直観主義的」で一致 | 確認（C6.10） |
| L11 | Wrigley 2022, *Phil. Math.* 30: 306–342 | 一致 | 抄録と部分的な全文（WebFetch、頁番号なし） | 名称は "recursive-ordinal recognition ability"（strong / weak の二種）。主張は「その能力を持つと信じる十分な理由がない」で、原稿の「lack」より弱い。**略号 "RORA" は確認できず**。静寂主義の文は確認 | 表現の調整（C3.28） |
| L12 | Domain Principle（Priest 1995/2002, Hallett 1984） | — | 原典は未閲覧。二次（Linnebo の arXiv 論文、学位論文、プレプリント）は全文 | Hallett 1984 p.25（Cantor 1886 の英訳）: "Each potential infinite, if it is rigorously applicable mathematically, presupposes an actual infinite." **原稿の「every property determines a set」は Domain Principle の正確な記述ではない**（素朴内包に近い） | **要修正**（C6.7, B-7） |
| L13 | Zermelo 1930, *Fund. Math.* 16: 29–47 | 一致 | 原典・Ewald 訳は未閲覧。二次（Maddy–Väänänen arXiv:2204.13754）は全文 | 趣旨（見かけの矛盾は集合論とその個々のモデルの混同による。あるモデルで集合でないものが次のモデルで集合）は二次資料で支持。ただし二次資料は原誌 **p.47** とし、原稿の pp.46–47 とずれる。原稿の英文 "a perfectly good, valid set" は未確認 | 要一次照合（C6.6） |
| L14 | Gödel 1931 注14 | — | 全文（Meltzer 訳） | 番号・文言とも一致。使用した英訳を明記することを推奨 | 確認（C3.38） |
| L15 | Solovay 1976, *Israel J. Math.* 25: 287–304 | doi:10.1007/BF02757006 | 書誌。内容は二次（arXiv:1704.07677） | GLS（GL + 反射、必然化なし）は算術的真理の様相論理（Solovay の第二定理）。⊥ は ℕ で偽なので GLS は無矛盾。必然化で閉じると矛盾する（推論はサブエージェントによる。資料の記述ではない） | **要修正**（C5.9, B-5）。原稿の参考文献に追加が必要 |

### 5.2 査読者が期待しそうな先行文献（書誌確認と抄録）

| 文献 | 書誌 | アクセス | 関連（抄録の範囲） |
|---|---|---|---|
| Franzén 2004, *Inexhaustibility* | ASL Lecture Notes in Logic 16 | 抄録 | Turing–Feferman の超限進行に基づく数学の汲み尽くせなさ |
| Franzén 2004, *BSL* 10: 367–389 | 一致 | 冒頭のみ | 超限進行の完全性の意義 |
| Beklemishev 2003, *Arch. Math. Logic* 42: 515–552 | 一致 | 書誌 | 評価不能 |
| Feferman–Spector 1962, *JSL* 27: 383–390 | 一致 | 書誌 | 経路に沿った不完全性 |
| Shapiro 2006（open texture）ほか | 一致 | 書誌 | 評価不能 |
| Tanswell 2018, *Inquiry* 61: 881–913 | 一致 | 抄録 | open texture と Lakatos から、数学概念の概念工学へ |
| Cappelen 2018, *Fixing Language* | 一致 | 抄録 | 概念の改良の過程と限界 |
| Linnebo 2013, *RSL* 6: 205–228 / Linnebo 2018, *Thin Objects* | 一致 | 抄録 | 潜在的階層の様相集合論 / 動的抽象 |
| Studd 2019, *Everything, More or Less* | 一致 | 抄録 | generality relativism |
| Dummett 1993, "What Is Mathematics About?" | 一致 | 抄録 | 抄録では不定拡張性を確認できず |
| Fine 2006, "Relatively Unrestricted Quantification" | 一致 | 抄録 | 不定拡張可能性を懐疑の根拠に挙げる |
| **Cook 2026**, "The Logic of Potential Infinity", *Phil. Math.* 34: 63–99 | 一致 | 抄録 | 潜在無限なら直観主義論理という Dummett の見方に反論し、それより強い論理を支持する。著者の U3（構成主義）と原稿 C6.10 に直接関わる |
| **Hamkins 2026**, "The Modal Logic of Arithmetic Potentialism and the Universal Algorithm", *Phil. Math.* 34: 137–182 | 一致 | 抄録 | 算術の潜在主義の様相的コミットメント。案 A・B の両方に関わる |
| *Phil. Math.* 34(1) の潜在主義特集の他の論文 | Hellman–Linnebo–Shapiro（序）、Sutto、Berry | 書誌（目次） | 案 A の §3 で参照候補 |
| Maraldo, SEP "Nishida Kitarō"（2024-02-21 改訂） | 一致 | 全文 | §3.2 で、公理系は Gödel の定理により自己説明的でない、という類比が述べられている（西田自身ではなく Maraldo の類比）。GC 論文 §7 の「唯一の先行の痕跡」に当たる |
| Krummel 2015 | 一致 | 抄録 | 評価のみ |
| Feferman 1991, "Reflecting on incompleteness", *JSL* 56: 1–49 | 一致 | 抄録 | 反射原理と schematic theory の reflective closure |
| Gödel 1951（Gibbs 講演）, *Collected Works* III | 一致 | 書誌 | 選言とプラトン主義の内容は未閲覧 |
| **Akiyoshi–Arana 2019**, 『哲学論叢』46: 1–17 | 一致 | 全文 | 竹内外史による西田の語（active intuition, self-reflection）の使用。Takeuti 1972「our finite mind is the so-called potential infinity … because our mind has the ability of self-reflection」（p.12）。**西田と不完全性定理を直接結ぶ記述はない**（Gödel への言及は2点のみ） |

### 5.3 Philosophia Mathematica の投稿規定（2026-10-11 取得。WebFetch 経由の抽出）

| 項目 | 内容 |
|---|---|
| 範囲 | "new work in philosophy of mathematics, the application of mathematics, and computing"。論文は「問題の歴史的背景と明示的に関係する立場を示すか、ある問題を新しい光の下で示す」こと。最重要の基準は "intellectual value and interest, preferably to more than one of its constituencies"（About、General Instructions） |
| 要旨 | **最大100語**（最新稿の要旨は約99語） |
| 引用形式 | 「Jones [1991]」形式を推奨。文献表はアルファベット順。最新稿の natbib 著者–年式「Author (Year)」からの変換が必要 |
| 組版 | TeX で再現可能（natbib）。PDF に頁番号 |
| 匿名化 | double-anonymised peer review |
| 語数上限 | 記載なし |
| AI 方針 | 誌の頁には記載なし。ただし前稿の投稿時に、編集部は "Policy on AI Use & Disclosure for Oxford Journals Authors" への準拠確認と、謝辞での開示を求めた（資料 #9） |

前回セッション（10/10）に照合済みのもの: Cheng, arXiv:2009.04887（Feferman 1960 の Σ₁ 数え上げの要約、`made_canonicity_audit.md` §2）。

## 6. 投稿先との関係で記録すべき事実（資料 #9 より）

著者の個人情報には触れず、論文の改稿に関わる事実だけを記録する。

1. 前稿 *Which Consistency Statement?* は 2026-09-21 に Philosophia Mathematica に投稿され、9/24 に担当編集者に割り当てられた。
2. 9/23 の AI 開示文は「All intellectual content — the made-canonicity criterion, the generative schema, the five-portrait classification, and the philosophical arguments — is the author's own」と述べている。
3. 9/30 に共同編集長から、投稿論文が著者の AI ワークフローの産物かどうかの照会があった。10/1 の著者の回答は「The central concept is my own, although the expression "made-canonicity" was proposed by the AI during that process and I decided to adopt it」と述べ、会話履歴の提供も申し出ている。10/2 の編集長の返信は「I am now going to think about how to proceed」。それ以降の経過はこの資料にはない（`unknown`）。
3a. **審査の結果（著者からの聞き取り、2026-10-11）**: 前稿は**デスクリジェクト**された。理由は、著者の要約によれば「著者の真に独創的な哲学的議論を書くことに失敗している」という趣旨。却下通知の原文は本プロジェクトでは見ていない（連携している Gmail には該当のやりとりがない）。したがって今回の改稿版は**新規投稿**として扱う。
4. 今回（10/11）の著者の申告は「made-canonicity は AI が提案した概念であり、著者の西田理解と対応しない」である。**10/1 の回答（概念は著者のもの、語だけが AI の提案）との関係を、改稿版の AI 開示でどう説明するかは著者の判断事項**であり、`restructure_options.md` §4 で投稿上のリスクとして挙げる。
