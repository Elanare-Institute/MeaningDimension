# Claims matrix — PhilMath2.tex の全主張

作成日: 2026-10-11。Phase B。対象: `~/src/godelex/PhilMath2.tex`（560行、md5 `b09d7e9ab806ab6c6a083a8a6c359bae`）。「行」は同ファイルの行番号。

## 凡例

- **判定**: `retain`（そのまま残す）/ `reinterpret`（意味を明確にして言い直す。原文と訂正案の対比を §B に置く）/ `remove`（論文から外す。別稿に移す場合を含む）/ `investigate`（典拠・事実の確認が終わるまで判定を保留）。
- **種別**: OAC = 著者独自の哲学的主張 / MR = 数学的結果（既知） / HA = 発見的類推 / HIST = 史実 / LIT = 先行研究の内容の帰属 / EMP = 経験的主張。
- **Lean**: 本プロジェクトの Lean で検証済みのもの（名前）/ `Foundation` = 既存ライブラリにある / `—` = 形式化の対象外 / `未` = 形式化可能だが未実施。
- **典拠の状態**: 先行研究の照合結果は `source_reading_audit.md` §5。ここで「要照合」とあるものは、Phase E の引用監査まで未確認。
- 判定は**提案**であり、確定は著者の承認による。原稿は変更していない。
- 西田に関わる行は、**著者の考えを西田より上位に置く**原則（著者の指示、2026-10-11）で判定した。西田本文との違いは、著者の主張を直す理由ではなく、西田への帰属を直す理由としてだけ扱う。

## A. 主張の一覧

### 要旨（行28）

| ID | 行 | 主張（原文の語を保持して要約） | 種別 | 判定 | 理由 | 必要な典拠 | Lean |
|---|---|---|---|---|---|---|---|
| C0.1 | 28 | G2 is intensional: its verdict depends on how axioms are presented | MR/LIT | retain | Feferman 1960 の既知の事実 | Feferman 1960; Halbach–Visser 2014 | — |
| C0.2 | 28 | MDG grounds generative dialetheism: for each contradiction a meaning dimension that makes it true can someday be generated | OAC | retain（「makes it true」は C3.3 に合わせて言い直す） | 著者の中心テーゼ T7, T8 | — | — |
| C0.3 | 28 | made-canonicity が導かれ、D1–D3 がその帰結として従う | OAC+MR | **remove** | 撤回（`retired_made_canonicity.md` R3, R4） | — | M1–M5 は反例側 |
| C0.4 | 28 | Five self-referential patterns are classified | OAC | reinterpret | 分類は既知の数学で決まる。made/making による「予測」は外す（C5.8） | — | 部分（G2s） |
| C0.5 | 28 | argues against Platonism and standard dialetheism | OAC | retain | 著者の立場。ただし Gödel はこの点で中立（`godel_boundary.md` §2-7） | Priest; Linnebo–Shapiro | — |

### §1 Introduction（行33–47）

| ID | 行 | 主張 | 種別 | 判定 | 理由 | 必要な典拠 | Lean |
|---|---|---|---|---|---|---|---|
| C1.1 | 33 | G2: no consistent, sufficiently strong formal system can prove its own consistency | MR | reinterpret | 「実効的に公理化」「標準的な無矛盾性文に対して」を明記する | Gödel 1931 | `G1_unprovable` |
| C1.2 | 35–39 | Feferman の α*: α と同じ公理を数え上げる（T が無矛盾なら）。Con_{α*} は PA で証明可能、Con_α は証明不能 | MR | retain | 正しい（非有界・`α↾x` 版）。前稿の有界版の誤りは修正済み | Feferman 1960（定理番号・頁の照合） | 未（Foundation の `Theory.Δ₁` では α* を表現できない） |
| C1.3 | 41 | Detlefsen 1979: 内包性は G2 から Hilbert 的意義を奪う | LIT | **reinterpret（典拠の差し替え）** | 照合の結果、Detlefsen 1979 はこの帰属を支持しない。中心論点は有限主義的な量化子の解釈で（p.309）、注25（p.313）は Feferman 1960 で G2 を覆せるという見方を明示的に退けている（`source_reading_audit.md` L1） | Detlefsen 1979 の正確な論点、または Detlefsen 2001（*Phil. Math.* 9、未読） | — |
| C1.4 | 41 | Feferman は natural / unnatural を区別したが、基準は非形式的なまま | LIT | investigate | 同上 | Feferman 1960 | — |
| C1.5 | 41 | Halbach–Visser: D1–D3 の下で Löb により G2。内包性の三つの次元（coding, expressing formula, fixed-point method） | LIT | reinterpret（語の修正） | 三つの次元は I p.680 で確認。三つ目の原文は "the method of obtaining presumed self-reference"（L5）。「D1–D3 に限定せよ」という帰属は未照合 | Halbach–Visser 2014 I p.680 | — |
| C1.6 | 41 | Visser 2016/2020: G2 は無矛盾性の概念に対して頑健でない。Feferman format。選択基準は示さない | LIT | **reinterpret（典拠の特定）** | "Feferman format" は Visser 2020 pp.269, 271 で確認。「頑健でない」「選択基準を控える」は 2020 年論文に見つからない。2016 年の章（**頁は 67–90**）は抄録のみで未照合（L6, L7） | Visser 2016 の該当頁 | — |
| C1.7 | 43 | None closes it. 欠けているのは、なぜある表示が正準かを説明する哲学的原理 | OAC | **remove**（案 B では reinterpret） | made-canonicity を前提にした問題設定。撤回後は論文の問いを立て直す（`restructure_options.md`） | — | — |
| C1.8 | 45 | MDG は無限に可能。意味の構造そのものに基づく公理 | OAC | retain | T7 | — | — |
| C1.9 | 45 | made-canonicity を導き、D1–D3 がその帰結 | OAC+MR | **remove** | R3 | — | — |
| C1.10 | 47 | LLM の限界についての注記 | OAC | remove（または別稿へ） | C7.3 | — | — |

### §2 Meaning-Dimension Generation（行49–107）

| ID | 行 | 主張 | 種別 | 判定 | 理由 | 必要な典拠 | Lean |
|---|---|---|---|---|---|---|---|
| C2.1a | 55 | 実数の規則（全順序を含む）は −1 の平方根を許さない | MR | retain | 順序体では x² ≥ 0 | 教科書的事実 | `real_sq_add_one_ne_zero` |
| C2.1b | 55 | i の創造は新しい意味の次元（複素平面）を生んだ | OAC | retain | T6 | — | — |
| C2.1c | 55 | 「矛盾」x² = −1 は除去されたのではなく、**規則を拡張することで真にされた** | OAC+MR | **reinterpret** | ℂ は ℝ の順序体の規則を拡張していない。順序を捨て、構造を取り替えている（Th(ℝ) ⊄ Th(ℂ)）。真になったのは同じ文の ℂ での充足（§B-1） | — | `complex_models_rootSentence`, `theoryOf_real_not_subset_complex` |
| C2.2 | 57 | Shannon 以前には、統計的構造をもつ情報源のメッセージがどれだけの情報を担うかについて「事実がなかった」 | OAC/HIST | reinterpret | 反実在論的な強い主張。査読で反論されやすい（統計力学のエントロピーなど先行概念との関係）。「測る概念がなかった」と「事実がなかった」を区別する | Hartley 1928; Shannon 1948 | — |
| C2.3 | 59 | Scholze のパーフェクトイド空間は標数 0 と p を橋渡しした | HIST | retain | 付録32と整合 | Scholze 2012 | — |
| C2.4 | 61 | 三つの事例は一つの操作（MDG）の例 | OAC | retain | T6 | — | — |
| C2.5 | 67–73 | domain extension / Hilbert の理想元 / Lakatos の concept stretching / Wittgenstein の concept formation は、同じ操作の別の側面 | OAC/LIT | investigate | Lakatos の concept stretching の説明（多面体の例）と Wittgenstein の静寂主義への言及は照合が必要。概念工学（conceptual engineering）、開かれた組織（open texture）の文献に触れていない（`restructure_options.md` の査読反論） | Lakatos 1976; Wittgenstein 1956; Hilbert 1926 | — |
| C2.6 | 75 | MDG はこれら四つを統合する上位概念 | OAC | retain | ただし「何を加えるか」の論証を強める必要 | — | — |
| C2.7 | 79–83 | **Axiom.** Meaning-dimension generation is infinitely possible | OAC | retain | T7。Gödel から導かないことを明記 | — | —（Lean の `axiom` にしない） |
| C2.8 | 87 | (1) Words increase。持続的な人類の活動で、使用語数が純減した時代はない | EMP | **remove**（または典拠つきで弱める） | 典拠のない経験的主張。言語消滅などの反例が考えられ、査読で突かれる | 言語学の統計（未調査） | — |
| C2.9 | 89 | (2) 意味は語を超える（多義性、非言語的意味） | OAC/EMP | retain（表現を弱める） | 「always exceeds」は数えられない量の比較 | — | — |
| C2.10 | 91 | (3) 意味に保存則はない | OAC | retain | — | — | — |
| C2.11 | 93 | (4) Shannon の限界は通信についての制約で、意味についての制約ではない | OAC/LIT | retain | Shannon 1948 冒頭の、意味的側面を工学的問題から外す趣旨の一文で裏づけられる見込み（要照合） | Shannon 1948 | — |
| C2.12 | 95 | (5) 意味だけでなく意味の次元が生成される（マルクス主義、フェミニズム）。数学の domain extension はその最も厳密な形 | OAC | retain | T6。ただし「most rigorous form」は B3 に照らして言い直す（ℂ は規則の取り替え） | — | — |
| C2.13 | 97 | 様相は可能無限。究極の限界を証明した者はいない。証明責任は限界を主張する側にある | OAC | retain | 証明責任の議論は査読で反論されやすい（`restructure_options.md`） | — | — |
| C2.14 | 101 | 発見ではない。ℂ の構成以前、「i² = −1」は真理値を持たなかった | OAC | retain | T11。付録3（Bombelli 1572 の計算）との時系列の整合（「構成」とは何時点か）を明記する必要 | — | — |
| C2.15 | 103 | 発明は自然法則の利用を要する（標準的な意味で） | OAC | reinterpret | 「自然法則を利用した」は特許法上の発明の定義に近い。「標準的な意味」とするなら典拠を示し、そうでなければ定義として明示する | 典拠未確認 | — |
| C2.16 | 105 | 創造（ex nihilo）ではない。既存体系の矛盾から始まる生成 | OAC | retain | 括弧書きで他の door にも言及済み | — | — |
| C2.17 | 107 | 立場は potentialist ではなく generative | OAC | retain | T7, T12 | Linnebo–Shapiro 2019 | — |

### §3.1 A third concept of contradiction（行111–127）

| ID | 行 | 主張 | 種別 | 判定 | 理由 | 必要な典拠 | Lean |
|---|---|---|---|---|---|---|---|
| C3.1 | 115 | 古典論理では φ ∧ ¬φ は爆発する | MR | retain | — | — | `not_models_and_models_neg` |
| C3.2 | 117 | 標準的真矛盾主義: ある矛盾は真で、永続的な特徴として受け入れられる | LIT | investigate | Priest の立場の要約として照合 | Priest 2006 | — |
| C3.3 | 119 | 生成的真矛盾主義の定義。矛盾は「at its level で真: 現行体系の規則のもとで φ と ¬φ が両方成り立つ」が final ではない | OAC | **reinterpret** | 同じ原稿の表1の注記（古典的 T では T の矛盾を意味する）、行151（T + φ が両方を導く）と緊張する。著者の確認が必要（`author_position_jp.md` U5）。§B-2 | — | `unprovable_of_refuted`, `not_models_of_refuted`（字義どおりの読みへの no-go） |
| C3.4 | 121 | ℝ で ∃x(x²+1=0) は順序体の公理で反証される | MR | retain | — | — | `real_not_models_rootSentence` |
| C3.5 | 121 | 標準的真矛盾主義者はそれを真矛盾として受け入れ、矛盾許容的実解析で作業するだろう | LIT | **remove**（または仮定法に） | 真矛盾主義者の実際の主張への帰属に根拠がない。藁人形と読まれる | Priest（反例の確認） | — |
| C3.6 | 121 | ℂ の構成がその矛盾を真にする生成 | OAC | reinterpret | C2.1c と同じ。§B-1 | — | 同上 |
| C3.7 | 123 | どの矛盾も penultimate。「解消」ではなく「充足」。ℝ は根を持たないまま | OAC/MR | retain（言い直し） | ℝ と ℂ の二つの構造の話として正確に書く | — | `theoryOf_real_not_subset_complex` |
| C3.8 | 125 | 無限小: Berkeley 1734 → Weierstrass の ε-δ による除去 → Robinson 1966 による実現。次の段階ではなかった | HIST/OAC | retain | 付録11の慎重な言い方（真になったのは要求）に揃える | Berkeley 1734; Robinson 1966 | — |
| C3.9 | 127 | 保証は「いつか」で、意味次元は生成されるまで可能性としても存在しない | OAC | retain | T7 | — | — |

### §3.2 Doors to generation（行129–163）

| ID | 行 | 主張 | 種別 | 判定 | 理由 | 必要な典拠 | Lean |
|---|---|---|---|---|---|---|---|
| C3.10 | 131–147 | 表1: 文の四状態（provable / refutable / undecidable / contradictory）。古典的 T では最後は T の矛盾 | MR | retain | 正確 | — | 未（定義は容易） |
| C3.11 | 149 | Gödel–Rosser: 無矛盾で実効的に公理化された十分強い体系は決定不能文を持つ | MR | retain | — | Gödel 1931; Rosser 1936 | Foundation（再利用のみ） |
| C3.12 | 151 | 矛盾の door の形: 実践が要求するものと、それを排除する規則を合わせると、T + φ が φ と ¬φ を導く | OAC/MR | retain | 形式化できる読み（C3.3 の訂正案の基礎） | — | `unprovable_of_refuted` |
| C3.13 | 155 | 決定不能性の例（平行線公準、ZFC の CH、PA の Goodstein・Paris–Harrington・Con(PA)）。前提を明記している | MR | retain | 正確 | Gödel 1940; Cohen 1963; Goodstein 1944; Kirby–Paris 1982; Paris–Harrington 1977 | — |
| C3.14 | 155 | 生成の形: Gentzen の ε₀ までの超限帰納、ε₀ 未満の順序数、T + Con(T)、巨大基数（Martin–Steel; CH は決めない: Lévy–Solovay）、モデル構成、逆数学 | MR/HIST | retain | 正確 | 各典拠 | `G1_strict`（T + Con(T) のみ） |
| C3.15 | 157 | 手段の限界（作図、五次方程式、停止問題、Hilbert 第10問題、Tarski、鳩の巣原理の証明長、P vs NP の障壁） | MR | retain | 正確（障壁の定式化は原文どおりで妥当） | Wantzel; Abel; Turing; Matiyasevich; Tarski; Haken; Buss; BGS; Aaronson–Wigderson; Razborov–Rudich | — |
| C3.16 | 159 | 未解決問題の door（Weil, FLT, Poincaré, Kepler, Entscheidungsproblem, H10）。companion paper の P vs NP 再定式化 | MR/HIST | retain（da_paper は investigate） | 著者の未査読論文への依存 | da_paper（未読） | — |
| C3.17 | 161 | 生成の形の一覧。door と形は独立の分類。どちらも閉じていない | OAC | retain | — | — | — |
| C3.18 | 163 | door は次の一歩を強制する原因ではなく、一歩を踏み出せる場所 | OAC | retain | — | — | — |

### §3.3 Someday, for each（行165–175）

| ID | 行 | 主張 | 種別 | 判定 | 理由 | 必要な典拠 | Lean |
|---|---|---|---|---|---|---|---|
| C3.19 | 167 | 生成的真矛盾主義は、§2.3 の公理が矛盾の door でとる形 | OAC | retain | — | — | — |
| C3.20 | 167 | 現在の体系の限界を、今後生成されうるすべての意味体系に投影することを否定 | OAC | retain | T9 | — | — |
| C3.21 | 169 | 「扱う」の二つの意味（解決 / 問いの再構成） | OAC | retain | — | — | — |
| C3.22 | 171 | ある体系で証明不能と示されても、すべての体系で決着不能とは示されない | MR | retain | 正確 | — | — |
| C3.23 | 171 | 量化の順序: ∀q∃n と ∃n∀q。不完全性定理は後者を否定する | MR | retain | 正確（前者を導くとは言っていない） | — | `not_exists_eligible_proves_all_truths`（適格な段階について） |
| C3.24 | 171 | Turing 1939: 真の Π₁ 文はすべて反映原理の超限進行のある段階で証明可能。Feferman 1962: uniform reflection で全算術真理 | MR/LIT | **reinterpret** | Turing の基礎体系は PA ではなく Gödel の体系 P。完全性が証明されているのは「θ(x) vanishes identically」の形（Π₁）について（Turing 1939 pp.209–210、L4）。Feferman 1962 は二次資料でのみ確認（L3） | Turing 1939 pp.209–210; Feferman 1962（一次照合）; Feferman–Spector 1962 | 未（Foundation に超限進行なし） |
| C3.25 | 171 | どの段階かは記法に依存し、正しい記法を見つけるには実質的にその文の真を知っている必要がある | MR/LIT | retain（典拠を付ける） | 既知の論点 | Feferman 1962; Franzén 2004 | — |
| C3.26 | 171 | 「Each sentence can be reached; no fixed procedure reaches them all」 | MR | retain | M-R（`godel_boundary.md`）の正確な述べ方 | — | 部分（`G3`） |
| C3.27 | 171 | これが量化の順序として述べた可能無限。Russell の any / all | OAC/LIT | retain | Russell 1908 の照合 | Russell 1908 | — |
| C3.28 | 173 | Wrigley 2022: RORA を欠くので絶対的決定不能な算術命題がある。認識的な意味で、for each someday と両立 | LIT | reinterpret | 名称は "recursive-ordinal recognition ability"（strong / weak の二種）。主張は「その能力を持つと信じる十分な理由がない」で、「欠く」より弱い。略号 RORA は確認できず（L11） | Wrigley 2022 の頁（全文での照合） | — |
| C3.29 | 175 | 「いつか」は「いま」ではない | OAC | retain | — | — | — |

### §3.4 The generative schema（行177–193）

| ID | 行 | 主張 | 種別 | 判定 | 理由 | 必要な典拠 | Lean |
|---|---|---|---|---|---|---|---|
| C3.30 | 179 | 詳細は gc_paper | — | retain | 匿名化の扱いに注意 | 著者の preprint | — |
| C3.31 | 181 | **西田の哲学的構造と Gödel の数学的構造の両方が**四条件を実現する | HA | **reinterpret** | 図式は著者のものとして提示する（著者の考えが上位）。**著者の T14 と食い違う**: 西田の絶対矛盾的自己同一は、生成的真矛盾主義と可能無限を前提にしてはじめて実現され、西田はそこまで至らなかった。したがって「西田の構造がこの図式を実現する」とは書かず、「西田の概念はこの図式（とくに (iv) と可能無限）を要求するが、西田自身はそれを展開しなかった」と書き直す。Gödel との対応は図式レベルの類推（HA） | 西田原典（`author_position_en.md` §3） | — |
| C3.32 | 184 | (i) Self-specification: 対角化補題が Gödel 文を固定する。哲学的には自己限定としての相互限定 | MR + HA | retain（MR）/ reinterpret（HA） | MR 部分は正確（証明可能同値を除いて） | — | Foundation |
| C3.33 | 186 | (ii) Excess: Gödel 文は真だが証明不能 | MR | retain | 前提（無矛盾性、ℕ での真）を明記 | — | Foundation |
| C3.34 | 188 | (iii) Incorporation: 無矛盾性文の付加で真に強い理論。哲学的には「作られたものから作るものへ」 | MR + HA | retain（MR）/ reinterpret（HA） | 句を**著者の用法**として定義して使うか、西田の句として引くかを区別する。西田の句として引くなら、本文（N1–N4）では運動は相互否定的で、作られたものが作るものを作る関係である。いずれにせよ無矛盾性文の付加に当てるのは類推 | 西田「絶対矛盾的自己同一」 | `G1_strict` |
| C3.35 | 190 | (iv) Non-completion: Σ₁ 健全性が伝播し、過程は反復する。哲学的には自己は完成した全体に閉じない | MR + HA | retain（MR）/ reinterpret（HA） | MR は Lean で検証済み（既知の系） | — | `Stage.sigma1Sound_next`, `G2_strict`, `G4` |
| C3.36 | 193 | 西田の設定では door は矛盾。絶対矛盾的自己同一が明示的な出発点 | HA/OAC | retain（T14 に沿って） | 語そのものが矛盾を含むという著者の読み（T14）と整合する。出発点としての定式は照合済み（「故に私は現実の世界は絶対矛盾的自己同一というのである」、§一 第1段落） | 西田「絶対矛盾的自己同一」 | — |
| C3.37 | 193 | Gödel の設定では door は決定不能性（ω 無矛盾なら Gödel 文、無矛盾なら Rosser 文） | MR | retain | 正確 | — | Foundation |
| C3.38 | 193 | この決定不能性は矛盾の上に築かれた。Gödel 注14「すべての認識論的アンチノミーは同様の決定不能性証明に使える」 | HIST | retain | 注番号・文言は Meltzer 訳で一致（L14）。使用した英訳を明記する | Gödel 1931（Meltzer 訳） | — |
| C3.39 | 193 | 証明可能性を真理から分けることは意味次元生成であり、その次元で嘘つきの形式が真になる | PE | reinterpret | `godel_boundary.md` B7。「形式」の意味を明示し、嘘つき文自体が真になったのではないと書く（付録9は既にそう書いている） | — | — |
| C3.40 | 193 | Gödel 文は標準模型で真で、証明不能 | MR | retain | 正確 | — | — |
| C3.41 | 193 | 決定不能性が次の段階 T + Con(T) への door になる | MR + HA | retain | — | — | `G1_strict` |

### §3.5 The made-to-making asymmetry（行195–199）

| ID | 行 | 主張 | 種別 | 判定 | 理由 | 必要な典拠 | Lean |
|---|---|---|---|---|---|---|---|
| C3.42 | 197 | 運動は made から making へで、逆はない。公理 = made、証明可能性関係 = making | OAC | **remove** | `retired_made_canonicity.md` R1。撤去の根拠は著者の立場（作られたものと作る働きの不可分で動的な関係）である。西田本文との整合は根拠にしない（参考までに、西田本文でも関係は相互否定的: N4） | — | — |
| C3.43 | 197 | 証明可能性関係は公理を一般には決定しない（同じ帰結集合を生む公理化は多い） | MR | retain（made/making の語を外して、Feferman の議論の中で使う） | 正確 | — | 未（`T ≊ U` と表示データの区別は Foundation で表現できる） |
| C3.44 | 199 | この非対称性こそ内包性問題に欠けていた哲学的原理 | OAC | **remove** | R1, R2 | — | — |
| C3.45 | 199 | α* と Rosser 述語は making を折り込むので deviant。Rosser 述語の定義 | OAC + MR | remove（ラベル）/ retain（定義） | 定義は正確 | — | — |

### §4 Made-Canonicity as Criterion（行201–243）

| ID | 行 | 主張 | 種別 | 判定 | 理由 | 必要な典拠 | Lean |
|---|---|---|---|---|---|---|---|
| C4.1 | 205–211 | Definition 1（made-canonicity） | OAC | **remove** | 撤回 | — | 反例側 M1–M5 |
| C4.2 | 213–215 | 二条件は made-to-making asymmetry の帰結 | OAC | **remove** | R2 | — | — |
| C4.3 | 221–225 | D1–D3 の定義 | MR | retain（内包性を論じる場合） | 定義は正確（D3 は内部含意で書かれている） | Hilbert–Bernays; Löb 1955 | Foundation `HBL` |
| C4.4 | 227 | 三条件とも made-canonicity から従う | OAC+MR | **remove** | R3 | — | — |
| C4.5 | 229 | D1 は自動的。Prf が Σ₁ であることだけを要する（(i) が保証） | MR | reinterpret | D1 に必要なのは、α が T の公理を T 内で数え上げること（Σ₁ で ℕ で正しければ Σ₁ 完全性から従う）。言い方の精密化 | Feferman 1960 | — |
| C4.6 | 231–235 | D3 は Σ₁ 完全性の例。表示式 `T ⊢ φ ⇒ T ⊢ Prov(⌜φ⌝)`（Σ₁ φ について） | MR | **reinterpret** | 表示式はメタレベルの推論規則で、D3 に必要な内部含意 `T ⊢ φ → Prov(⌜φ⌝)` になっていない（§B-4） | Hájek–Pudlák 1993 など | Foundation（形式化された Σ₁ 完全性） |
| C4.7 | 237 | D2 は任意の数え上げで成り立つ（α* でも） | MR | retain | Feferman 1960 | Feferman 1960 | — |
| C4.8 | 239 | α* は (ii) に違反し、Π₁ 連言のせいで「precisely」D3 を破る | OAC+MR | **remove**（made-canonicity 部分）/ reinterpret（数学部分） | T ⊇ PA なら D3 が破れる。有限公理化された T では D1 が破れうる（R5） | Feferman 1960 | — |
| C4.9 | 239 | α* はもはや Σ₁ ではない | MR | retain | Σ₁ ∧ Π₁ | — | — |
| C4.10 | 241 | Rosser 述語は D2 と D3 を同時に満たさない [Kurahashi, Cor 3.3] | MR/LIT | retain | arXiv v2 p.7 の Corollary 3.3 で一致（L8）。出版版は pp.77–97、番号は未確認 | Kurahashi 2021 | — |
| C4.11 | 243 | 逆向きは未解決 | MR | **remove** | 撤回により論点が消える。残す場合も C3/C4 の反例を示す必要（R7） | — | 紙上 |

### §5 Five Portraits（行245–286）

| ID | 行 | 主張 | 種別 | 判定 | 理由 | 必要な典拠 | Lean |
|---|---|---|---|---|---|---|---|
| C5.1 | 247 | made-to-making asymmetry が自己言及の類型を生む | OAC | **remove** | R8 | — | — |
| C5.2 | 251–270 | 表2（Made/making stance 列を含む） | OAC + MR | reinterpret | 「Made/making stance」列を外し、数学的事実と結果のラベル（generative / inert / halting / explosive / vacuous）を記述的に残す | — | — |
| C5.3 | 272 | Portrait 1: G ↔ ¬Prov(G)。真だが証明不能。G（同値に Con(T)）の付加で真に強い体系。「made-canonical」 | MR + OAC | retain（MR）/ remove（made-canonical） | G と Con(T) の T 上の同値は標準的な述語で成り立つ | — | `G1_strict`（Con の付加） |
| C5.4 | 274 | Portrait 2: Henkin 文は Löb により証明可能。GL では ⊤ に解ける | MR | retain（「made = making」は外す） | 正確 | Löb 1955; Boolos 1993 | Foundation `Löb` |
| C5.5 | 276 | Portrait 3: PA + ¬Con(PA) は無矛盾だが Σ₁ 非健全。¬Con(T) を証明し、Con(T) は反証可能。上昇は止まる | MR | retain | 正確。Lean で検証済み（既知） | Smoryński 1977 など | `consistent_union_incon`, `inconsistent_next_of_union_incon`, `not_sigma1Sound_union_incon` |
| C5.6 | 278 | Portrait 4: 透明な真理述語は古典論理で爆発、LP では隔離 | MR | retain（made/making の語は外す） | 正確 | Tarski 1935; Priest 1979 | Foundation `Tarski`（古典側のみ） |
| C5.7 | 280 | Portrait 5: α*・Rosser の無矛盾性文は PA で証明可能（vacuous）。made-canonicity は (ii) で破れる | MR + OAC | retain（MR）/ remove（(ii)） | — | Feferman 1960; Kurahashi | — |
| C5.8 | 284 | 分類は記述的でなく**予測的**。結果は made-to-making asymmetry との位置で決まる | OAC | **remove** | R8。結果は既知の定理で決まり、ラベルからの予測ではない | — | — |
| C5.9 | 286 | GL prover: ¬□⊥ は GL の定理でない。Henkin 不動点は ⊤。**GL は反映図式 □φ → φ を無矛盾には含みえない** | MR | reinterpret | 必然化で閉じた正規様相論理としてなら正しい。必然化で閉じない GLS（GL + 反映、MP のみ）は無矛盾で、算術的真理の様相論理（Solovay の第二定理。二次資料で確認、L15）。§B-5 | Boolos 1993; Solovay 1976（*Israel J. Math.* 25: 287–304。原稿の参考文献に未収録） | — |
| C5.10 | 286 | Lean 4 で IΣ₁ < IΣ₁ + Con(IΣ₁) < … を**10段階**検証 | MR（事実の主張） | **reinterpret（訂正）** | companion repo の Lean は第1段階のみで、当時は `axiom` に依存（`lean_inventory_audit.md` §4）。本プロジェクトの `G2_strict` が全有限段階を示すので、それに差し替える（§B-6） | — | `G2_strict`, `G2_strict_of_lt` |

### §6 Against Platonism, Against Standard Dialetheism（行288–316）

| ID | 行 | 主張 | 種別 | 判定 | 理由 | 必要な典拠 | Lean |
|---|---|---|---|---|---|---|---|
| C6.1 | 292 | プラトン主義の定義 | LIT | retain | — | — | — |
| C6.2 | 294 | ℂ 以前、i² = −1 は真理値を持たなかった | OAC | retain | T11 | — | — |
| C6.3 | 296 | プラトン主義は数学的真理の全体があらかじめ固定され、すべての意味次元がすでに存在することを含意する。そうなら §2.3 の公理は不要。全体の独立存在を確立する議論はない。可能無限が最強の正当化された様相 | OAC | reinterpret | 「数学的対象の独立存在」から「すべての意味次元の既存」への移行は議論を要する（藁人形と読まれる危険）。「最強の正当化された様相」は強すぎる | プラトン主義の標準的文献（未定） | — |
| C6.4 | 298 | 潜在主義者は既存の可能性の実現、生成的見方は可能性そのものの創造 | OAC/LIT | retain（潜在主義の要約は照合） | T7, T12 | Linnebo–Shapiro 2019 | — |
| C6.5 | 302 | 標準的真矛盾主義: 矛盾は真で final、さらなる解決は不要 | LIT | investigate | Priest の立場の要約として照合 | Priest 1995/2002, 2006 | — |
| C6.6 | 304 | Priest の二つの範例はどちらもこのように応じられた。Liar → Gödel・Tarski、Russell → 累積的階層（Zermelo 1930「in the succeeding model, a perfectly good, valid set」pp. 46–47） | PE/HIST | reinterpret + investigate | 付録8の慎重な言い方（無制限の Russell 集合が存在するようになったのではない）に揃える。Zermelo の趣旨は二次資料で支持されるが、二次資料は原誌 p.47 とし、原稿の英文 "a perfectly good, valid set" は未確認（L13） | Zermelo 1930; Ewald 1996 の英訳 | — |
| C6.7 | 306 | 対立は矛盾ではなく閉包について。Inclosure Schema は完成した全体に適用される。**Domain Principle = 「すべての性質は集合を定める」という Cantor の原理** | OAC/LIT | **reinterpret** | 著者自身の GC 論文 §6 は Priest の Domain Principle を「whenever there are things of a certain kind, there are all of those things」と引いており、本稿の記述と食い違う。Hallett 1984 p.25 の定式化（二次資料で確認）は「Each potential infinite, if it is rigorously applicable mathematically, presupposes an actual infinite」で、「すべての性質は集合を定める」（素朴内包に近い）ではない（L12、§B-7） | Hallett 1984 p.25; Priest 1995/2002 の該当頁（一次照合） | — |
| C6.8 | 306 | 意味の次元は同一性規準を持たないので、Inclosure の適用条件を満たさない | OAC | retain | GC §6 の議論 | — | — |
| C6.9 | 308 | 一般化は開いた図式（Russell の any）で、完成した全体の量化ではない | OAC/LIT | retain | — | Russell 1908 | — |
| C6.10 | 312 | liberal は古典論理、strict は直観主義論理（L&S 2019）、全集合の不定領域上では半直観主義（L&S 2026） | LIT | retain | L&S 2019 pp.169, 181–183、L&S 2026 の抄録で一致（L9, L10）。古典論理の結論は様相論理が十分強いという条件付きで、一階論理についての話であることを注記する。潜在無限なら直観主義論理という見方に反論する Cook 2026（*Phil. Math.* 34: 63–99）にも触れる必要 | Linnebo–Shapiro 2019, 2026; Cook 2026 | — |
| C6.11 | 314 | L&S は拡張がどんな行為で誰が行うかを未決にしている。生成的見方では、新しい意味次元は可能性として存在しない。行為者の開放性。潜在主義の段階は固定された意味のもとで領域を拡張し、MDG は意味を拡張する | OAC/LIT | retain（L&S への帰属は照合） | T7, T12。B3 と整合する重要な区別 | Linnebo–Shapiro 2019 | — |
| C6.12 | 316 | 生成的上昇の技術的署名は Σ₁ 健全性。無矛盾性より強く、**strict potentialism より弱い** | MR + OAC | reinterpret | 前半は Lean で検証済み（既知）。「strict potentialism より弱い」は理論の性質と論理の選択を同じ尺度で比べており、比較が成り立たない（§B-8） | — | `Stage.sigma1Sound_next`, `not_sigma1Sound_union_incon` |
| C6.13 | 316 | 生成的枠組みは、存在主張が「honest」であることを要求する | OAC/HA | retain | ラベルとして | — | — |

### §7 Discussion（行318–338）

| ID | 行 | 主張 | 種別 | 判定 | 理由 | 必要な典拠 | Lean |
|---|---|---|---|---|---|---|---|
| C7.1 | 322 | MDG が無限に可能なら、数学は最終状態に近づいていない | OAC | retain | 条件文として | — | — |
| C7.2 | 322 | 構成された任意の形式体系について、自身の限界の取り込みでさらに体系が生成できる。各段階は真に強く、最終段階はない | MR | reinterpret | 前提（実効的、IΣ₁ を含む、無矛盾。反復には Σ₁ 健全性）を明記。無矛盾性だけでは2段目で止まる（Portrait 3） | — | `G1_strict`, `G2_strict`, `G4`, `inconsistent_next_of_union_incon` |
| C7.3 | 324 | MDG は無矛盾性文の反復に還元できない新しい構造を作る | OAC | retain | B3 と整合 | — | — |
| C7.4 | 328–334 | LLM は統計的規則性の内部で動く。新しい次元の創造は形式体系の限界との関わりを要する。1545年以前の数学で訓練した LLM は ℂ を生まないだろう。過度の依存は停滞のリスク | OAC/EMP | **remove**（別稿へ） | 新指示書 §6 の撤去候補。反実仮想に根拠がない。Gödel とも Lean とも無関係（B14）。最新稿は「hypothesis」と弱めているが、PhilMath の主題からも外れる | — | — |
| C7.5 | 338 | 生成図式は Gödel と独立に西田の哲学で実現される。言語哲学・制度論・科学革命への応用可能性 | HA/OAC | reinterpret | 図式は著者のものとして述べる。T14 により、西田の哲学は図式を「実現する」のではなく、図式を要求しつつ完成させなかったものとして位置づける。西田に帰属させる部分は照合済みの本文に限る。独立性は史実の主張（GC §7） | 西田; GC | — |

### §8 Conclusion（行340–348）

| ID | 行 | 主張 | 種別 | 判定 | 理由 | Lean |
|---|---|---|---|---|---|---|
| C8.1 | 342 | made-canonicity が内包性を解決し、D1–D3 が従う | OAC | **remove** | R3, R4 | — |
| C8.2 | 344 | MDG は domain extension の基礎にある哲学的に基本的な操作。生成的真矛盾主義。door。for each someday | OAC | retain | — | — |
| C8.3 | 346 | 五類型の分類、プラトン主義と真矛盾主義への反対、LLM の構造的理由 | OAC | reinterpret / remove（LLM） | C5.8, C7.4 | — |
| C8.4 | 348 | 形式体系の矛盾と決定不能文は、それが止まる場所ではなく、通り抜ける door である | OAC | retain | — | — |

### 付録 A: 34事例（行350–434）

付録冒頭（行354）の「rational reconstructions。door は本枠組みの立場からの同定で、歴史上の当事者に帰属させない」は **retain**（適切な限定）。各事例の判定:

| # | 事例 | door | 数学的・史実の正確さ | 「真にする」の言い方 | 判定 | 典拠 |
|---|---|---|---|---|---|---|
| 1 | 通約不能量 | 矛盾 | Eudoxus（『原論』第5巻）、Dedekind 1872 は妥当。ピタゴラス派の「共通尺度」の信念は史学上の再構成 | — | retain（史実は要照合） | 史学文献 |
| 2 | ゼロと負数 | 矛盾 | Brahmagupta 628 は妥当。ℕ で 3−5 は答えを持たない | 「減法が全域になった」で正確 | retain | — |
| 3 | 複素数 | 矛盾 | Cardano 1545、Bombelli 1572、x³ = 15x + 4 が √−121 を経由して根 4 に至る（立方根は 2 ± i）は正確 | 「x² + 1 = 0 が根を持つ領域」と書いており正確 | retain | — / Lean: M-ℂ |
| 4 | 無限遠点 | 矛盾 | Desargues 1639 は妥当 | — | retain | — |
| 5 | 微積分 | 矛盾 | 妥当。実現は11へ送る | — | retain | Berkeley 1734 |
| 6 | 超限数 | 矛盾 | Galileo 1638、Dedekind 1888、Cantor は妥当 | 「部分が全体に等しい」が真になったのは、「等しい」が対等（全単射）の意味に変わったから。意味の変化として明記すると MDG の好例になる | reinterpret（語の意味の変化を明記） | — |
| 7 | Hilbert の理想元 | 矛盾 | Hilbert 1926 の例（無限遠点、虚数、Kummer の理想数）は妥当（要照合） | — | retain | Hilbert 1926 |
| 8 | Russell の逆理と集合の階層 | 矛盾 | 最新稿で「無制限の Russell 集合が存在するようになったのではない」と修正済み。{x ∈ V_α : x ∉ x} が V_{α+1} の集合であることは正しい（基礎の公理の下ではそれは V_α 自身）。Zermelo 1930 の引用は要照合 | 「要求が段階ごとに満たされる」 | retain（引用照合後） | Zermelo 1930 |
| 9 | Gödel の不完全性定理 | 矛盾 | 最新稿で「嘘つき文そのものではなく、その構造的パターン」と修正済み。正確 | 正確 | retain | Gödel 1931 注14 |
| 10 | Tarski の真理定義不可能性 | 矛盾 | 「L₀ で真でないと自らについて言う文は L₀ の文でない。だから L₀ で真でなく、L₁ で真」は妥当 | 最新稿で「元の文ではなく形式」と修正済み。末尾の「making を made の一段上に保つ」は made/making の語を外す | reinterpret（語のみ） | Tarski 1935 |
| 11 | 超準解析 | 矛盾 | 最新稿で「Berkeley が述べた矛盾そのものではなく、それを駆動した要求」と修正済み。正確 | 正確 | retain | Robinson 1966 |
| 12 | ホモトピー型理論 | 矛盾 | 一価性公理の説明は妥当 | 実践（同型を同一視）と基礎（区別）の不一致は、形式的矛盾でも「規則による排除」でもない。矛盾の door への分類は §3.2 の定義から外れる | investigate（door の分類） | Univalent Foundations 2013 |
| 13 | 非ユークリッド幾何 | 決定不能 | 妥当（相対無矛盾性による独立性） | — | retain | — |
| 14 | Gentzen | 決定不能 | 妥当 | — | retain | Gentzen 1936 |
| 15 | 連続体仮説 | 決定不能 | 妥当（ZFC の無矛盾性に相対的と明記） | — | retain | Gödel 1940; Cohen 1963 |
| 16 | Paris–Harrington | 決定不能 | 妥当 | — | retain | — |
| 17 | Goodstein | 決定不能 | 妥当 | — | retain | — |
| 18 | 巨大基数 | 決定不能 | 「無限個の Woodin 基数があれば射影集合はすべて決定的、ゆえに Lebesgue 可測」（Martin–Steel）、CH は決めない（Lévy–Solovay）は妥当 | — | retain | — |
| 19 | 逆数学 | 決定不能 | 「多くの定理が基礎体系で証明可能か、四つの強い部分体系のどれかと同値」は妥当 | — | retain | Simpson 2009 |
| 20 | 角の三等分 | 手段の限界 | 8x³ − 6x − 1 = 0、作図可能な長さの次数が2の冪は正確 | — | retain | Wantzel 1837 |
| 21 | 五次方程式と Galois | 手段の限界 | 妥当 | — | retain | — |
| 22 | Lebesgue 積分 | 手段の限界 | 妥当 | — | retain | — |
| 23 | 直観主義論理 | 手段の限界 | 妥当 | — | retain | Brouwer 1908; Heyting 1930 |
| 24 | 圏論 | 手段の限界 | 妥当（有限次元での二重双対の自然性） | — | retain | — |
| 25 | 情報エントロピー | 手段の限界 | 妥当（Hartley は等確率の特殊例） | — | retain | — |
| 26 | 証明複雑性 | 手段の限界 | 妥当 | — | retain | — |
| 27 | Entscheidungsproblem と停止問題 | 未解決問題 | 妥当 | — | retain | — |
| 28 | Hilbert 第10問題 | 未解決問題 | 妥当 | — | retain | — |
| 29 | Weil 予想とスキーム | 未解決問題 | 妥当 | — | retain | — |
| 30 | Fermat の最終定理 | 未解決問題 | 妥当 | — | retain | — |
| 31 | Poincaré 予想 | 未解決問題 | 妥当 | — | retain | — |
| 32 | パーフェクトイド空間 | 未解決問題 | 妥当（射影的滑らかなトーリック多様体の完全交叉で証明） | — | retain | Scholze 2012 |
| 33 | Kepler 予想 | 未解決問題 | 妥当 | — | retain | Hales 2005, 2017 |
| 34 | P vs NP と directional asymmetry | 未解決問題 | 著者の未査読論文の結果（「P = NP ⇔ すべての NP 関係が最悪 O(log n) の非対称性の解法を持つ」など）に依存。本プロジェクトでは**未読・未検証** | 「解消されたのは古典的な問いで、形式的命題ではない」と明記している点は正確 | investigate（PhilMath 論文から外すことも検討。自己引用と匿名化の問題もある） | da_paper |

付録末尾（行434）: 「Contradictions have been made true (entries 1–12)」→ **reinterpret**。最新稿の各事例自身が、真になったのは矛盾そのものではなく「要求」や「形式」だと書いている（8–11）。まとめの文をそれに揃える。

## B. 原文と訂正案の対比（数学的に不正確・緊張のある箇所）

原文は変更していない。訂正案は提案であり、著者の承認を要する。

| # | 箇所 | 原文 | 問題 | 訂正案 |
|---|---|---|---|---|
| B-1 | 行55, 121 | "The 'contradiction' x² = −1 was not eliminated; it was made true by extending the rules." / "The construction of ℂ is the meaning-dimension generation that makes the contradiction true." | ℂ は ℝ の順序体の規則を拡張していない（順序が両立しない）。Th(ℝ) ⊄ Th(ℂ)。「真になった」のは文 ∃x(x²+1=0) の ℂ での充足で、矛盾 φ ∧ ¬φ ではない | "What ℝ refutes, ℂ satisfies: the sentence ∃x(x²+1=0) is false in ℝ and true in ℂ. ℂ is not obtained by adding rules to those of ℝ; the ordering is given up and the domain and operations are changed. The 'contradiction' is the clash between this demand and the rules of ℝ; what generation makes true is the demanded sentence, in a new structure." |
| B-2 | 行119 | "The contradiction is true at its level — within the rules of the current system, both φ and ¬φ hold — but it is not final." | 同じ原稿の表1の注記（古典的 T では「両方証明可能」は T の矛盾）と行151（T + φ が両方を導く）と緊張する | 著者に二択を問う（`author_position_jp.md` U5）。(a) 古典的読み: "Within the current system, φ is refuted while practice demands it; the system extended by the demand derives both φ and ¬φ." (b) 文字どおりの真矛盾を「その水準で」認める読み: その場合、その水準の論理が矛盾許容的であることを明示し、§6.2 の標準的真矛盾主義との差を「final かどうか」だけに置く |
| B-3 | 行121 | "The standard dialetheist would accept it as a true contradiction and work within a paraconsistent real analysis." | 真矛盾主義者の実際の主張に根拠のない帰属 | 削除するか、"A dialetheist need not, and Priest does not, take this case as a dialetheia; the contrast is with the general attitude to contradictions." のように限定する（Priest の照合後） |
| B-4 | 行231–235 | "T ⊢ φ ⇒ T ⊢ Prov(⌜φ⌝) for Σ₁ sentences φ" | メタレベルの推論規則で、D3 に必要な内部含意ではない | "T ⊢ φ → Prov(⌜φ⌝) for every Σ₁ sentence φ (formalized Σ₁-completeness, provable in IΣ₁)." 撤回後に §4 を残す場合のみ |
| B-5 | 行286 | "GL cannot consistently contain the reflection schema □φ → φ" | 必然化で閉じた正規様相論理としてなら正しい。必然化を課さない拡張 GLS は無矛盾（二次資料で確認、`source_reading_audit.md` L15） | "No normal modal logic extending GL (closed under necessitation) contains the reflection schema □φ → φ consistently; Solovay's system GLS, which adds the schema without closing under necessitation, is consistent (it is the modal logic of arithmetical truth)." |
| B-6 | 行286 | "A Lean 4 formalization verifies the strict hierarchy IΣ₁ < IΣ₁ + Con(IΣ₁) < ⋯ through ten stages." | ローカルの companion repo では第1段階のみ（`axiom` 依存） | "A Lean 4 formalization (on the Foundation library, with no additional axioms) verifies, for every Σ₁-sound theory T containing IΣ₁ with a Δ₁ presentation, that every finite stage Tₙ of the ascent is Σ₁-sound and that Tₙ ⊊ Tₙ₊₁ for all n." （本プロジェクトの `G2_strict` 等。数学的には既知であることも併記） |
| B-7 | 行306 | "the Domain Principle — Cantor's principle that every property determines a set" | 著者自身の GC 論文 §6 は Priest の Domain Principle を "whenever there are things of a certain kind, there are all of those things" として引く。「すべての性質は集合を定める」は素朴内包に近い | Hallett 1984 p.25 の定式化（"Each potential infinite, if it is rigorously applicable mathematically, presupposes an actual infinite"、二次資料で確認）か、GC 論文の定式化に揃え、Priest の該当頁を一次照合する |
| B-8 | 行316 | "It is stronger than consistency, and weaker than strict potentialism, which requires each truth to be made true at a stage and changes the logic" | Σ₁ 健全性（理論の性質）と strict potentialism（哲学的立場・論理の選択）は同じ尺度にない | "It is stronger than consistency. Unlike strict potentialism, it does not change the logic: Σ₁-soundness is a classical property of a theory, requiring that its existential theorems of the simplest kind be witnessed." |
| B-9 | 行434 | "Contradictions have been made true (entries 1–12)" | 事例8–11の本文自身が、真になったのは矛盾ではなく要求・形式だと書く | "In entries 1–12, what a contradiction demanded has been met in a new structure — sometimes centuries after the contradiction was named." |
| B-10 | 行87 | "No period of sustained human activity has seen a net decrease in the number of words in use." | 典拠のない経験的主張 | 削除するか、典拠を付けて限定する |
| B-11 | 行41 | "Detlefsen (1979) argued that the intensionality strips G2 of its Hilbertian significance" | Detlefsen 1979 の論点は有限主義的な量化子の解釈で、注25は Feferman 型の内包性で G2 を覆す見方を退けている（L1） | Detlefsen 1979 の実際の論点（Con(T) は Hilbert の計画に関わる意味での無矛盾性を表現しない）に即して書き直すか、内包性の論者として別の典拠を探す |
| B-12 | 行171 | "Turing (1939) showed that every true Π₁ sentence is provable at some stage of a transfinite progression of reflection principles over PA" | 基礎体系は Gödel の体系 P。Turing の進行は無矛盾性文の付加による序数論理（L4） | "Turing (1939) showed, for his ordinal logic over Gödel's system P, that every true Π₁ sentence ('θ(x) vanishes identically', θ primitive recursive) is provable at some stage of a transfinite progression of consistency extensions." |
| B-13 | 行41 | "coding, expressing formula, fixed-point method" | 原文の三つ目は "the method of obtaining presumed self-reference"（Halbach–Visser I p.680） | 原文の語に合わせる |
| B-14 | 行173 | "because we lack recursive ordinal recognition ability (RORA)" | 名称は "recursive-ordinal recognition ability"。Wrigley の主張は「持つと信じる十分な理由がない」（L11） | "because there is no good reason to believe that we possess the recursive-ordinal recognition ability …" |
| B-15 | 行41, 542 | Visser 2016, pp.67–91 / 「not robust」「refrained from offering a selection criterion」の典拠 | 頁は 67–90。後者の二つは Visser 2020 では見つからない（L6, L7） | 頁を直し、該当箇所を 2016 年の章で特定するか、主張を "Feferman format" に限る |

## C. 集計

表 A の行を機械的に数えた（判定欄の先頭の語で分類。MR 部分は retain、OAC 部分は remove のように併記した行は、先頭の語で数えた）。

| 判定 | 本文（C0.1–C8.4、122行） | 付録（34事例） |
|---|---|---|
| retain | 73 | 30 |
| reinterpret | 26 | 2（6, 10） |
| remove | 18 | 0 |
| investigate | 5 | 2（12, 34） |

付録の冒頭（行354）は retain、末尾（行434）は reinterpret。判定はすべて提案で、承認後に確定する。
