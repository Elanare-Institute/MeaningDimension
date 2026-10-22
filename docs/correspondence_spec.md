# 仕様: ACSI とゲーデルの上昇の、部分的な構造同型（CR。実装前に固定）

この文書は実装より先に書いた。`Tests/CorrespondenceSpec.lean` のテストは**この文書の文言**から書き起こし、実装の都合で変えない。仕様を変えるときは、まずこの文書を改訂し、テストも改訂する。

## 0. 背景

- `math_verification_report.md` §F3.3 は、対応表 (i)–(v) の「構造的同型」という語に形式的な裏づけがないと記録した。二つの側のあいだに、構造を保つ写像を定義していないからである。
- 著者の問い（2026-10-20）:「ゲーデルとの構造的同型を部分的にでも示せる？」
- CR は、(i)(ii)(iii)(v) の行について、構造を保つ全単射を定義して、それが同型であることを証明する。(iv) は同型に含めない。共通の形（CR6）として別に述べる。
- 表示の選び方を「外から来る経験」と同じように扱ってよいかは、著者が判断する（§G7）。この文書と実装はその判断をしない。**（追記 2026-10-22: 著者が判断した。外から来る入力とみなさない。§6.0 の E1。）**

## 1. モデル化上の選択（Claude による）

| ID | 内容 |
|---|---|
| N1 | 共通の構造を**成長系**とする。成長系は、段階、項目、「段階で項目が成り立つ」（`Holds`）、項目の取り込み（`step`）からなる。公理は二つ。取り込んだ項目は成り立つ。それまで成り立っていた項目は成り立ち続ける |
| N2 | ACSI 側: 段階は自己、項目は経験、成り立つは「分類できる」、取り込みは `incorporate`（作る働き M を固定する）。(i) の Domain(S) を「S が分類できるもの」と読む（§F3 修正案 A の 1） |
| N3 | ゲーデル側: 段階は理論（公理集合）、項目は文、成り立つは「証明できる」、取り込みは `T ↦ T ∪ {σ}` |
| N4 | 過去は、有限の項目の列とする（ACSI の M7）。過去が**新鮮**とは、各項目が、それを取り込む段階で成り立たないことをいう。(i) にあたる |
| N5 | 過去の**痕跡**は次の四つからなる。過去が通る段階、過去が取り込む項目、そのあいだの `Holds`、過去に沿った継起 `Next`（段階 k が項目 k を取り込んで段階 k+1 になる）。**同型**は、段階どうしの全単射と項目どうしの全単射の組で、`Holds` と `Next` を保ち、かつ反映するもの |
| N6 | ゲーデル側の過去は、A3 の上昇の無矛盾性文の列 `[Con(T₀), …, Con(Tₙ₋₁)]` とする。各段の表示は A3 と同じ |

## 2. 定義（Lean 名。名前空間 `MeaningDimension.Correspondence`）

- `Growth`: フィールドは `Stage`、`Item`、`Holds : Stage → Item → Prop`、`step : Stage → Item → Stage`、`holds_step_self : ∀ s x, Holds (step s x) x`、`holds_step_of_holds : ∀ {s y} x, Holds s y → Holds (step s x) y`。
- `G.run s₀ h := h.foldl G.step s₀`。
- `G.stages s₀ h : Fin (h.length + 1) → G.Stage`。k を `G.run s₀ (h.take k)` に送る。
- `G.Fresh s₀ h :⇔ ∀ k (hk : k < h.length), ¬ G.Holds (G.run s₀ (h.take k)) h[k]`。
- `G.Le s s' :⇔ ∀ x, G.Holds s x → G.Holds s' x`。
- `G.Equivalent s s' :⇔ ∀ x, G.Holds s x ↔ G.Holds s' x`。
- `Incidence`: フィールドは `Stage`、`Item`、`Holds : Stage → Item → Prop`、`Next : Stage → Item → Stage → Prop`。
- `Incidence.Iso A B`: フィールドは次の四つ。`refl`、`symm`、`trans` をもつ。
  - `stage : A.Stage ≃ B.Stage`
  - `item : A.Item ≃ B.Item`
  - `holds_iff : ∀ s x, A.Holds s x ↔ B.Holds (stage s) (item x)`
  - `next_iff : ∀ s x s', A.Next s x s' ↔ B.Next (stage s) (item x) (stage s')`
- `Incidence.std n`: 段階は `Fin (n + 1)`、項目は `Fin n`。`Holds k j :⇔ j < k`、`Next k j k' :⇔ j = k ∧ k' = k + 1`（いずれも ℕ の値で比べる）。
- `G.trace s₀ h : Incidence`: 定義は次のとおり。
  - 段階: `Set.range (G.stages s₀ h)`
  - 項目: `Set.range (fun j : Fin h.length ↦ h[j])`
  - `Holds`: `G.Holds` の制限
  - `Next s x s' :⇔ ∃ k (hk : k < h.length), s = G.run s₀ (h.take k) ∧ x = h[k] ∧ s' = G.run s₀ (h.take (k + 1))`
- `acsiGrowth M : Growth`: ACSI 側（N2）。`E` と作る働き `M : Making E` から作る。
- `godelGrowth : Growth`: ゲーデル側（N3）。
- `conPast T n : List ArithmeticSentence`: `[Con(T₀), …, Con(Tₙ₋₁)]`。`Tₖ` は A3 の `ascent T k`、`Con(Tₖ)` はその表示から作った無矛盾性文。
- `conOffer U σ :⇔ ∃ d : U.Δ₁, σ = (d から作った U の無矛盾性文)`（理論と文の関係。U の表示を固定しない）。

## 3. 命題

**CR0（二つの成長系）**
- (a) `acsiGrowth M` の二つの公理は AC5(b)(c) である。`(acsiGrowth M).run = M.run`。
- (b) `godelGrowth` の二つの公理は、公理の証明と弱化である。さらに `godelGrowth.Le T U ↔ T ⪯ U`、`godelGrowth.Equivalent T U ↔ T ≊ U`。

**CR1（新鮮な過去の標準形）** 任意の成長系 G と、s₀ からの新鮮な過去 h について、次が成り立つ。
- (a) `j < h.length` なら `G.Holds (G.run s₀ (h.take k)) h[j] ↔ j < k`。
- (b) `k ≤ h.length` なら `G.Le (G.run s₀ (h.take k)) (G.run s₀ (h.take m)) ↔ k ≤ m`。
- (c) `h.Nodup`。
- (d) `G.stages s₀ h` は単射。

**CR2（痕跡は標準の構造と同型）** 同型 `G.ofStd : (Incidence.std h.length).Iso (G.trace s₀ h)` がある。これは k を k 番目の段階に、j を `h[j]` に送る。

**CR3（同じ長さの新鮮な痕跡は同型）** 任意の成長系 G、G'（異なってよい）を考える。s₀ からの新鮮な過去 h と、s₀' からの新鮮な過去 h' が、同じ長さをもつとする。このとき同型 `traceIso : (G.trace s₀ h).Iso (G'.trace s₀' h')` がある。これは k 番目の段階を k 番目の段階に、`h[j]` を `h'[j]` に送る。

**CR4（両側の新鮮な過去）**
- (a) ゲーデル側。仮定は `[T.Δ₁]`、`𝗜𝚺₁ ⪯ T`、Σ₁ 健全。このとき次が成り立つ。
  - `godelGrowth.run T (conPast T k) = (ascent T k).theory`
  - `(conPast T n).length = n`
  - `(conPast T n)[k] = Con(Tₖ)`
  - `conPast T n` は T からの新鮮な過去である（A3 の `G2_unprovable` による）
- (b) ACSI 側。`M.IsOpen S₀` なら、任意の n について、S₀ からの新鮮な過去で長さ n のものがある。

**CR5（ACSI とゲーデルの痕跡の同型）**
- (a) 任意の作る働き M、自己 S₀、S₀ からの新鮮な経験の過去 h について、同型 `((acsiGrowth M).trace S₀ h).Iso (godelGrowth.trace T (conPast T h.length))` がある。これは k 段階の自己を `Tₖ` に、経験 `h[j]` を `Con(Tⱼ)` に送る。
- (b) `M.IsOpen S₀` なら、任意の n について、長さ n の新鮮な過去 h と、(a) の同型がある。

**CR6（(iv) の共通の形。同型には含めない）**
- (a) 抽象形。任意の成長系 G と「段階 s で差し出される項目」`Offer` を考える。s で差し出される x、x' について、`¬ G.Equivalent (G.step s x) (G.step s x')` とする。このとき、任意の `F : G.Stage → G.Stage` について `¬ ∀ y, Offer s y → G.Equivalent (G.step s y) (F s)`。
- (b) ACSI 側。`Offer := IsNew`。`singletonMaking` では、S にとって新しい e ≠ e' について `¬ Equivalent (incorporate S e) (incorporate S e')`。
- (c) ゲーデル側。`Offer := conOffer`。G5 の仮定のもとで、`T.consistent.val` と `twistedCon T` はともに T で差し出され、`¬ Equivalent (T ∪ {Con_α}) (T ∪ {Con_β})` である（G5.5）。

**非空虚性**
- ACSI 側: `singletonMaking : Making ℕ`、空の自己（開放的。AC8(c)）。
- ゲーデル側: `𝗜𝚺₁` と `𝗣𝗔`。
- CR5(b) を `ℕ`・`singletonMaking`・空の自己と `𝗣𝗔` で実例化する。
- CR6(b) を空の自己と経験 0、1 で、CR6(c) を `𝗣𝗔` で実例化する。

## 4. 証明の見通し

- CR1(a): j < k なら、`h[j]` は段階 j+1 で成り立つ（取り込み）。単調性で段階 k でも成り立つ。k ≤ j なら、段階 k で成り立てば単調性で段階 j でも成り立ち、新鮮さに反する。
- CR1(b)(c)(d) は (a) から従う。
- CR2: 段階と項目の対応は、(c)(d) により単射。`Holds` の保存は (a)。`Next` の保存は (c)(d)。
- CR3 は CR2 の合成である。
- CR4(a): 段階 k の理論は `ascent T k`。新鮮さは各段の Gödel II（A3 の `G2_unprovable`）。
- CR4(b): 長さについての帰納法。新鮮な過去の後の自己は到達可能なので、開放性から新しい経験を得て、末尾に加える。

## 5. 新規性と、言えないこと

**2026-10-22 の分類し直し。** 下の各項目（CR0–CR6 の時点の記録）を、§6.0 の方針に従って次のように分類する。分類は、理論的限界（定理・反例・数学的事実で裏づけたもの）、著者の決定、撤回（未実装だったもの）の三つである。下の本文は記録として残す。

| 項目 | 分類 | 根拠 |
|---|---|---|
| 同型はゲーデルに固有の内容を区別しない | 事実（構造の選び方の帰結） | 痕跡の構造が「成り立つ」と継起だけだからである。CR10 で取り込みを加えると、入力が事前に決まっているかどうかが同型で区別される（ゲーデルの痕跡は max 規則をみたし、ACSI の過去の痕跡とは同型にならない。CR10(e)） |
| (iv) は同型に含まれない | 著者の決定（E1）のもとで証明できる違い | ゲーデル側の差し出しは一つで、次の段は段階の関数（CR8(d)）。ACSI 側は枝分かれし、段階の関数でない（CR8(e)） |
| 保つのは継起だけで、取り込み一般は保たない | **撤回** | この項目の例は、段階を等号で比べていた。「段階が何であるかは捨てる」という同じ節の方針に従い、成り立つもの（`Equivalent`）で比べると、成り立っている項目の取り込み直しは両側で何も変えない。取り込み一般は CR10 で扱う |
| 捨てているもの: AC1–AC4、AC7 | 著者の決定（E2） | 著者の存在論の概念なので、ゲーデル側に持ち込まない |
| 捨てているもの: AC6 | 著者の決定（E1）の帰結 | AC6 は、差し出された複数の新しい経験の扱いを述べる。ゲーデル側の差し出しは一つなので、対応物がない |
| 捨てているもの: AC8、AC10(c) | **撤回**（未実装だった） | AC8(b) の形は CR9(a)。項目の在庫が有限なら止まることは CR9(b)。範疇の在庫（AC10(c) そのもの）は ACSI の概念なので、ゲーデル側に持ち込まない（E2） |
| 捨てているもの: 枠組みの細分 | 証明できる違い | ゲーデル自身の区別（証明可能な同値。MDG5 の J5）では、上昇で区別は生まれない（`ascent_not_refineStep`）。ACSI では生まれる（MDG6）。J8 の累積の枠組みは ACSI に形を合わせた評価なので、対応に数えない（E2） |
| 続く仮定は異なる | 事実と著者の決定 | ACSI 側は開放性を仮定し、ゲーデル側は Σ₁ 健全性から開放性を証明する（CR8(c)）。ACSI 側の過去は前もって与えられず、ゲーデル側の過去は出発時のデータで決まる（E1） |
| 有限の痕跡だけを扱う | **撤回**（未実装だった） | 可能無限の過程の同型は CR7 で述べる（N12、E4） |
| (i) の「記述不能」は表していない | 理論的限界（ゲーデル側の事実） | Con(T) は ℒₒᵣ の文で、上昇は言語を変えない。ACSI 側は、段階ごとに台を生成するモデルにすれば表せる（型が前もって固定されているのはモデル化の選択）が、ゲーデル側に対応物がないので同型には入らない |

以下、CR0–CR6 の時点の記録。

- **新規性: なし。** 数学的には初等的である。形式的な内容は、§F3.3 が欠けていると記録した「構造を保つ写像」を定義し、それが同型であることを証明した点にある。
- **同型は、ゲーデルに固有の内容を区別しない。** CR2 により、新鮮な痕跡の同型類は長さだけで決まる。したがって同型は、同じ長さの新鮮な過去のどの二つのあいだにも成り立つ。二つの ACSI の過去のあいだにも、Con ではない独立な文を加えていくゲーデル側の過去とのあいだにも成り立つ。Con(T) が T 自身の指定する文であることと、それが証明できないこと（Gödel II）は、ゲーデル側の過去が新鮮であること（CR4(a)）にだけ入っている。
- **(iv) は同型に含まれない。** CR6 は共通の形であって、同型ではない。差し出される項目 `Offer` は両側で異なる。ACSI 側は全く新しい経験のすべてである。ゲーデル側は、ある表示から作った無矛盾性文である。両者が対応するかは、著者の判断による。
- **保つのは、過去に沿った継起 `Next` だけである。** 取り込み `step` 一般は保たない。たとえば j < k のとき、ゲーデル側では `Tₖ ∪ {Con(Tⱼ)} = Tₖ` となる（取り込み直しても何も変わらない）。ACSI 側の `incorporate` は、つねに経験を一つ多くもつ新しい自己を作る。この例は Lean では述べていない。
- **捨てているもの。** 段階と項目が何であるか（範疇をもつ自己か、公理集合か）を捨てている。AC1–AC4、AC6、AC7、AC10（枠組み、主客未分、互いに先立つこと）も捨てている。AC7 の先行関係 `Base h` は過去の長さだけから定義されるので、同じ長さのどの痕跡にも共通する。これを対応とは主張しない。
- **続く仮定は異なる。** ACSI 側は開放性、ゲーデル側は Σ₁ 健全性を仮定する（§F1 (v)）。ACSI 側の過去はあらかじめ与えられていない（∀n∃h。M7）。ゲーデル側の過去 `conPast T n` は、T と n の関数である。
- **有限の痕跡だけを扱う。** 無限の過程どうしの同型は述べない。
- **(i) の「記述不能」は表していない。** `Holds` は「分類できる」と「証明できる」である。

## 6. 拡張（CR7–CR10。2026-10-22 追加、実装前に固定）

### 6.0 方針と著者の決定（変えないこと）

- 著者の方針（2026-10-22）: 部分的同型は、なるべく広く取る。実装の手抜きやモデル化の選択を、理論的限界と呼ばない。

| ID | 著者の決定 |
|---|---|
| E1 | （§G7 の判断）ゲーデルの上昇で使う表示の選び方は、外から来る入力とみなさない。上昇は、出発時のデータ（T とその表示）で決定論的に決まる。理由は `godel_boundary.md` の B2 と §4 にある。論文でのゲーデルの役割は「完全に事前に決まった手続きでも閉じない」ことであり、著者の存在論の「まだ決まっていない」（T3、T7）と区別しておく |
| E2 | ゲーデル側は、ゲーデル自身の概念（証明可能性、証明可能な同値、決まった上昇）だけで読む。著者の存在論や、ACSI の概念に形を合わせた評価（AC7 の自己同一の枠組み、MDG5 の J8 の累積の枠組み）は、ゲーデル側に持ち込まない。それらは意味次元の側で扱う。したがって AC7 と J8 は対応に数えない |
| E3 | ~~範疇が累積する作る働きを、ACSI の例として加えてよい~~ **（同日改訂）** この承認は、「累積」をふつうの意味（生成したものが失われず、段階が大きくなる）で読んだうえでのものだった。ふつうの意味の累積は、どの作る働きでも成り立つ（AC5(c)、CR1(b)、MDG6(d)）。CR10 が使う性質は、これとは別の「max 規則」で、入力が事前に決まっていることの現れである。E5 により ACSI の対応には数えない。`iicMaking` は対比の例としてだけ残す |
| E5 | ACSI と意味次元生成では、入力（渡される経験）が事前に決まっていない。どの段階の自己も、どの経験でも取り込める（人間は何歳のときにどんな経験をしても対応できる。これは反実仮想ではない）。ゲーデル側は入力が事前に決まっている（E1）。構造の上での違いはこの一点であり、(iv) の差し出しの違い（CR8(d)(e)）と、取り込みの振る舞いの違い（CR10）は、どちらもその観察である。ゲーデル側の事前に決まった構造を、ACSI 側に持ち込まない（E2 の逆向き）。（同日の訂正: いったん違いを「飛び越し」という性質として括ったが、撤回した。構造的同型は構造を観察して判定するものであり、違いは「入力が事前に決まっているか」で述べる。） |
| E4 | 可能無限は、有限の値と ∀／∃ だけで述べる。極限や完成した無限の全体（無限の和、すべての段の合併、ω 段階）は使わない |

- E1 により、CR6(c)（G5 の二つの表示）は事実として残すが、(iv) の対応物とは読まない。G5 が示すのは、次の段が公理集合だけでは決まらず、出発時に決めた表示で決まることである。

### 6.1 モデル化上の選択（Claude による）

| ID | 内容 |
|---|---|
| N7 | **差し出し**は、段階と項目の関係 `Offer` とする。過去が**差し出された**過去であるとは、各項目が、それを取り込む段階で差し出されていることをいう。差し出しについての**開放性**とは、s₀ からの差し出された新鮮な過去のあとの段階に、差し出された項目で、そこで成り立たないものがあることをいう |
| N8 | ACSI 側の差し出しは「全く新しい」（`IsNew`）とする |
| N9 | ゲーデル側に、段階を表示つきの理論（A3 の `Stage`）とする成長系を加える。取り込みは `S ↦ S ∪ {σ}` で、表示は Foundation の和集合の表示（S の表示と、{σ} の一点の表示）である。差し出しは「S 自身の表示から作った S の無矛盾性文」とする（E1）。既存の `godelGrowth`（段階は公理集合）は変えない |
| N10 | 経験に前もって線形順序を入れた作る働き `iicMaking`。経験 e から範疇 `{x | x ≤ e}` を生成する。ACSI の例ではない。ゲーデル側の前もって決まった構造を ACSI 側に入れた場合の対比の例である（E3、E5） |
| N11 | 段階 s で項目 x を取り込んだ段階を、成り立つものが同じ（`Equivalent`）段階 s' と同一視する。§5 の「段階が何であるかは捨てる」と同じ方針である |
| N12 | 可能無限の過程の同型は、(1) 過去を延ばしても前の同型がそのまま延長されることと、(2) 両側で過去を一つ延ばせること（∀∃）の組で述べる。無限の列の全体のあいだの同型は述べない。これは E4 による選択であり、限界ではない |

### 6.2 定義（Lean 名。名前空間 `MeaningDimension.Correspondence`）

- `G.Offered Offer s₀ h :⇔ ∀ k (hk : k < h.length), Offer (G.run s₀ (h.take k)) h[k]`。
- `G.OpenFor Offer s₀ :⇔ ∀ h, G.Offered Offer s₀ h → G.Fresh s₀ h → ∃ x, Offer (G.run s₀ h) x ∧ ¬ G.Holds (G.run s₀ h) x`。
- `G.StepTo s x s' :⇔ G.Equivalent (G.step s x) s'`。
- `G.MaxRule s₀ h :⇔ ∀ k j, k ≤ h.length → (hj : j < h.length) → G.StepTo (G.run s₀ (h.take k)) h[j] (G.run s₀ (h.take (max k (j + 1))))`。**max 規則**: k 番目の段階で j 番目の項目を取り込むと、`max(k, j+1)` 番目の段階と同値になる。痕跡が取り込みで閉じ、行き先が項目の番号で決まる、という観察である。
- `StepIncidence`: `Incidence` に `StepTo : Stage → Item → Stage → Prop` を加えたもの。
- `StepIncidence.Iso A B`: `Incidence.Iso` に `stepTo_iff : ∀ s x s', A.StepTo s x s' ↔ B.StepTo (stage s) (item x) (stage s')` を加えたもの。
- `StepIncidence.Closed A :⇔ ∀ s x, ∃ s', A.StepTo s x s'`。
- `StepIncidence.std n`: `Incidence.std n` に `StepTo k j k' :⇔ (k' : ℕ) = max (k : ℕ) (j + 1)` を加えたもの。
- `G.stepTrace s₀ h : StepIncidence`: `G.trace s₀ h` に `StepTo s x s' :⇔ G.StepTo s x s'` を加えたもの。
- `godelStageGrowth : Growth`（N9）: 段階は `Godel.Stage`、項目は文、`Holds S σ :⇔ S.theory ⊢ σ`、`step S σ := ⟨S.theory ∪ {σ}, Theory.Δ₁.add S.presentation (Theory.Δ₁.singleton σ)⟩`。
- `ownCon S σ :⇔ σ = S.theory.consistent.val`（S の表示から作った無矛盾性文）。
- `iicMaking : Making E`（`[LinearOrder E]`。N10）: `generate S e = Set.Iic e`。

### 6.3 命題

**CR7（可能無限の過程の同型）**
- (a) 前の部分: `G.Fresh s₀ (h ++ h₂) → G.Fresh s₀ h`。`G.Offered Offer s₀ (h ++ h₂) → G.Offered Offer s₀ h`。
- (b) 一つ延ばす: `G.Fresh s₀ h → ¬ G.Holds (G.run s₀ h) x → G.Fresh s₀ (h ++ [x])`。`G.Offered Offer s₀ h → Offer (G.run s₀ h) x → G.Offered Offer s₀ (h ++ [x])`。
- (c) 同型の延長: 任意の成長系 G、G' を考える。s₀ からの新鮮な過去 `h ++ h₂` と、s₀' からの新鮮な過去 `h' ++ h₂'` があり、`h.length = h'.length`、`(h ++ h₂).length = (h' ++ h₂').length` とする。このとき長い過去の痕跡の同型 `traceIso` は、`k ≤ h.length` の k 番目の段階と `j < h.length` の j 番目の項目を、短い過去 h、h' の痕跡の同型 `traceIso` と同じところに送る。
- (d) ACSI とゲーデル: 新鮮な経験の過去 `h ++ h₂` について、その `acsiGodelIso` は、`k ≤ h.length` の k 番目の段階と `j < h.length` の j 番目の経験を、h の `acsiGodelIso` と同じところ（`Tₖ` と `Con(Tⱼ)`）に送る。
- (e) 両側で延ばせる。
  - ACSI 側: `M.IsOpen S₀` のもとで、S₀ からの新鮮な過去 h に対して、`h ++ [e]` が新鮮になる経験 e がある。
  - ゲーデル側: `conPast T (n + 1) = conPast T n ++ [Con(Tₙ)]`。延長は一通りに決まる（E1）。

**CR8（差し出しと開放性。(iv) の違いの位置）**
- (a) 抽象形: `G.OpenFor Offer s₀` なら、任意の n について、長さ n の差し出された新鮮な過去がある（CR4(b) の一般形）。
- (b) ACSI 側: `M.IsOpen S₀ → (acsiGrowth M).OpenFor (fun S e ↦ S.IsNew e) S₀`。
- (c) ゲーデル側。
  - `godelStageGrowth.step S S.theory.consistent.val = S.next`（差し出された項目の取り込みは、A3 の一歩である）。
  - `[T.Δ₁]` のもとで、`ascent T 0` からの差し出された過去 h について、`h = conPast T h.length` であり、`godelStageGrowth.run (ascent T 0) h = ascent T h.length`。
  - さらに `𝗜𝚺₁ ⪯ T`、Σ₁ 健全なら、`godelStageGrowth.OpenFor ownCon (ascent T 0)`。
- (d) ゲーデル側の差し出しは一つ: `ownCon S σ → ownCon S σ' → σ = σ'`。差し出された項目による次の段階は段階の関数である: `ownCon S σ → godelStageGrowth.step S σ = S.next`。
- (e) ACSI 側の差し出しは枝分かれする: E が無限なら、`singletonMaking` で空の自己から到達できるどの自己 S についても、任意の `F : Self E → Self E` について `¬ ∀ e, S.IsNew e → (acsiGrowth singletonMaking).Equivalent (singletonMaking.incorporate S e) (F S)`。
- (iv) の違いは (d) と (e) の対比に定まる。ゲーデル側では次の段を与える段階の関数（`Stage.next`）があり、ACSI 側ではない。

**CR9（開放性の帰結。AC8・AC10(c) の成長系の形）**
- (a) すべてが成り立つ段階はない: `G.OpenFor Offer s₀` で、h が s₀ からの差し出された新鮮な過去なら、`¬ ∀ x, G.Holds (G.run s₀ h) x`。
- (b) 項目の在庫が有限なら止まる: 有限集合 `C : Finset G.Item` について、s₀ からのどの差し出された新鮮な過去 h についても、`G.run s₀ h` で差し出される項目がすべて C に入るなら、`¬ G.OpenFor Offer s₀`。
- (c) 実例。
  - ACSI 側: `M.IsOpen S₀` なら、どの有限集合 `C : Finset E` についても、S₀ からの新鮮な過去 h と、`M.run S₀ h` にとって全く新しい経験 e で、`e ∉ C` となるものがある。
  - ゲーデル側: A3 の仮定（`[T.Δ₁]`、`𝗜𝚺₁ ⪯ T`、Σ₁ 健全）のもとで、どの有限集合 `C : Finset ArithmeticSentence` についても、`Con(Tₙ) ∉ C` となる n がある。
- 範疇の在庫（AC10(c) そのもの）は ACSI の概念なので、ゲーデル側には持ち込まない（E2）。

**CR10（取り込みの振る舞い。入力が事前に決まっているかの観察）**
- (a) 抽象形: s₀ からmax 規則をみたす新鮮な過去 h について、同型 `(StepIncidence.std h.length).Iso (G.stepTrace s₀ h)` がある。これは k を k 番目の段階に、j を `h[j]` に送る。したがって、任意の成長系 G、G' で、同じ長さの、max 規則をみたす新鮮な過去の `stepTrace` は同型である。
- (b) 閉じていること。
  - 同型は閉じていることを保つ: `A.Iso B → (A.Closed ↔ B.Closed)`。
  - max 規則をみたす新鮮な過去の `stepTrace` は閉じている。
- (c) ゲーデル側の痕跡は max 規則をみたす。
  - `[T.Δ₁]` のもとで、i ≤ j なら `𝗜𝚺₁ ⊢ Con(Tⱼ) → Con(Tᵢ)`。
  - さらに `𝗜𝚺₁ ⪯ T` なら、任意の k、j について `Tₖ ∪ {Con(Tⱼ)} ≊ T_{max(k, j+1)}`。
  - したがって `conPast T n` は T から max 規則をみたす。
- (d) 項目が来歴を含む。
  - 抽象形: s₀ からmax 規則をみたす新鮮な過去 h では、j 番目の項目を s₀ で取り込むだけで、i ≤ j のすべての項目が成り立つ: `G.Holds (G.step s₀ h[j]) h[i]`。
  - ゲーデル側: `[T.Δ₁]`、`𝗜𝚺₁ ⪯ T` のもとで、i ≤ j なら `T ∪ {Con(Tⱼ)} ⊢ Con(Tᵢ)`。Con(Tⱼ) は Tⱼ から作る文なので、来歴を含む。
- (e) ACSI 側の閉じ方。
  - 到達可能な自己の全体は、どの経験の取り込みでも閉じている（`Making.Reachable.step`）。どの段階の自己も、どの経験でも取り込める（E5）。
  - ある過去の経験を別の段階で取り込むと、その過去の上にない新しい枝になりうる。`singletonMaking` では、任意の自己 S₀ からの長さ 2 以上の新鮮な過去 h について、`(acsiGrowth singletonMaking).stepTrace S₀ h` は閉じていない。
  - したがって A3 の仮定のもとで、`godelGrowth.stepTrace T (conPast T h.length)` との `StepIncidence.Iso` はない。
- (f) 対比の例（ACSI の対応ではない。E5）。経験に前もって線形順序を入れた `iicMaking` について、次が成り立つ。
  - 空の自己から過去 h の最初の k 個を取り込んだ自己が分類できるのは、ちょうど、ある `i < k` について `x ≤ h[i]` となる x である（`k ≤ h.length`）。
  - 空の自己からの新鮮な過去は、max 規則をみたす。
  - A3 の仮定のもとで、空の自己からの新鮮な過去 h について、同型 `((acsiGrowth iicMaking).stepTrace Self.empty h).Iso (godelGrowth.stepTrace T (conPast T h.length))` がある。これは k 段の自己を `Tₖ` に、`h[j]` を `Con(Tⱼ)` に送る。
  - `iicMaking : Making ℕ` は、空の自己から開放的である。
  - 前もって順序を固定すると、ゲーデルと同じ一本の列の構造になる。この例が示すのは、その構造が順序の事前の固定から来ることである。

**非空虚性（CR7–CR10）**
- CR7(d)(e)、CR8(b)(e): `singletonMaking : Making ℕ`、空の自己。
- CR8(c)、CR9(c)、CR10(d) のゲーデル側: `𝗣𝗔`。
- CR10(e): `singletonMaking : Making ℕ`、空の自己、過去 `[0, 1]`、`𝗣𝗔`。
- CR10(f): `iicMaking : Making ℕ`、空の自己、過去 `[0, 1]`、`𝗣𝗔`。

### 6.4 証明の見通し

- CR7(a)(b): `take` と `++` の計算。(b) は、長さ |h| の取り込みの段階が `G.run s₀ h` であることによる。
- CR7(c)(d): 両方の同型の像を CR3（`traceIso_stage`、`traceIso_item`）と CR5（`acsiGodelIso_stage`、`acsiGodelIso_item`）で計算し、`take` と `getElem` を前の部分に戻す。
- CR7(e): ACSI 側は CR4(b) の帰納法の一歩。ゲーデル側は `List.range` の計算。
- CR8(a): 長さについての帰納法と CR7(b)。(b) は、過去のあとの自己が到達可能であること。
- CR8(c): 一つ目は定義上の等号。二つ目は過去の長さについての帰納法。三つ目は A3 の `G2_unprovable`。
- CR8(d) は定義から従う。(e) は、到達可能な自己の範疇が有限個の一点集合であること（AC8(c) と同じ）から、全く新しい経験を二つ取り、CR6(a)(b) を使う。
- CR9(a): 差し出された項目は成り立たない。(b): 長さ |C| + 1 の差し出された新鮮な過去を CR8(a) でとる。その項目はどれも、前の部分（CR7(a)）のあとで差し出されているので C に入る。重複がない（CR1(c)）ので、個数が |C| を超え、矛盾する。
- CR10(a): CR2 の同型に `stepTo_iff` を加える。⇐ は max 規則。⇒ は、`Equivalent` が同値関係であることと、新鮮な過去の段階がどの二つも `Equivalent` でないこと（CR1(b)）から、`k' = max(k, j+1)` が出る。
- CR10(b): 同型で移す。max 規則をみたす過去では `max(k, j+1)` 番目の段階がとれる。
- CR10(c): 一つ目は、`Tᵢ` の表示が `Tᵢ₊₁` の表示に含まれること（`provable_standardProvability_imp_of_Δ₁Class_subset`）を、i について繰り返す。
  - j < k なら、`Con(Tⱼ)` は `Tₖ` で証明できるので、加えても同値。
  - j ≥ k なら、`Tₖ ∪ {Con(Tⱼ)} ⪯ T_{j+1}` は弱化と `Con(Tⱼ) ∈ T_{j+1}` から出る。逆向きは、i ≤ j+1 についての帰納法で `Tᵢ ⪯ Tₖ ∪ {Con(Tⱼ)}` を示す（i > k のときは一つ目を使う）。
- CR10(d): 抽象形は、max 規則で `G.step s₀ h[j]` が `j+1` 番目の段階と同値になることと、CR1(a)。ゲーデル側は (c) の一つ目と、`𝗜𝚺₁ ⪯ T`。
- CR10(e): 二番目の項目を最初の段階で取り込んだ自己は、一番目の項目を分類しない（一点集合であり、h に重複がない）。一方、1 番目以降の段階は一番目の項目を分類する。0 番目の段階は二番目の項目を分類しない。よって、どの痕跡の段階とも `Equivalent` でない。あとは (b) による。
- CR10(f): 分類の公式は k についての帰納法。新鮮さから、線形順序のもとで h は狭義単調増加になり、`max` の式が出る。同型は (a)(c) から従う。開放性: 到達可能な自己の範疇は経験の数の `Iic` で、経験の和に 1 を足した数は全く新しい。

### 6.5 新規性と、言えないこと（CR7–CR10）

- **新規性: なし。** どれも初等的である。CR10(c) の一つ目は標準的な事実（表示の包含から無矛盾性文の含意）である。
- **取り込みまで含めた同型は、ACSI の対応ではない。** 構造の違いは、入力が事前に決まっているかの一点である（E1、E5）。ゲーデル側では入力が決まっているので、項目（無矛盾性文）が来歴を含み、痕跡は max 規則で取り込みに閉じる（CR10(c)(d)）。ACSI 側では入力が決まっていないので、どの段階の自己もどの経験でも取り込め、到達可能な自己の木が取り込みで閉じる。ある過去の経験を別の段階で取り込むと、その過去の外の新しい枝になりうる（CR10(e)）。(iv) の違い（CR8(d)(e)）も、同じ一点の観察である。
- **`singletonMaking` と `iicMaking` は玩具の例である。** 人間の作る働き（ブラックボックス）が何であるかは言わない。ACSI の定理は、どれも任意の作る働きについて述べている。
- **(iv) は同型の外に残る。** これは E1 のもとで証明できる違いである（CR8(d)(e)）。
- **CR9(c) のゲーデル側は軽い。** `Con(Tₙ)` がどれも異なることから、ほぼ直ちに従う。
- **CR7 は、可能無限の形の同型である（N12、E4）。** 無限の列の全体のあいだの同型は述べない。

## 7. 写像で示す、意味次元生成（MDG）とゲーデル・ACSI の対応（CR11–CR13。2026-10-22 追加、実装前に固定）

### 7.0 方針

- 著者の方針（2026-10-22）: 構造的同型は Lean で証明する。証明していないことを、観察だけで言わない。同型写像（と、標準の構造を写す同型）で示せることを示す。
- 入力が来る前の段階で、入力やその否定を評価することは、ACSI と MDG のモデルの構造ではない（言語や型を前もって固定した形式化の産物）。入力については「いまの段階で成り立たない」だけを使う。
- **MDG の入力のモデル。** これまで MDG は、生成が起きた後の二つの構造の関係（埋め込みと反転文）だけを扱っていた（MDG の指示書 §6）。生成の働きを、中身を指定しないブラックボックスとして置けば、人間の意思を形式化せずに「入力から新しい段ができる」形を表せる。ACSI の作る働きと同じ扱いである。
- **同型の水準を書き分ける。**
  - 痕跡の同型（CR12）は、モデルがたどった履歴のあいだの同型であり、モデルどうしの同型ではない。
  - 入力の構造の同型（CR13）は、ある段階と、そこに来うる入力からなる構造のあいだの同型である。
  - モデル全体のあいだの同型写像は作らない。段階や項目の集まりが違うので作れない。

### 7.1 モデル化上の選択（Claude による）

| ID | 内容 |
|---|---|
| N13 | MDG の段階は、言語 L の構造（台は `Type`）を束ねたもの `Struc L` とする。成り立つ = その構造で文が真 |
| N14 | MDG の入力は要求とし、文で書き表す。要求が段階 M に**来うる**とは、M で成り立たず、M を埋め込んだある構造で成り立つことをいう（D1）。文は入力の書き表し方の一つで、前の段での否定を構造として使わない |
| N15 | MDG の生成の働き `MDGMaking L`（ブラックボックス）。段階 M と、M に来うる要求 σ から、新しい段階を返す。M はそこに埋め込まれ、σ はそこで成り立つ。中身は指定しない |
| N16 | MDG の過去 `MDGPast L n`。n+1 個の段階、各段から次の段への埋め込み、n 個の要求からなる。各要求は存在文で、その段で成り立たず、次の段で成り立つ。生成の働きでたどった過去は MDGPast になる（CR12(c)）。要求を存在文に限るのは、存在文が埋め込みに沿って真のまま残ることが MDG1(b) で証明されているからである。存在文でない要求（∀∃ の形など）では痕跡の標準形が成り立つとは限らず、これは調べていない |
| N17 | 入力の構造 `OfferIncidence` は、段階・項目・成り立つ・来うる、からなる。同型は、段階どうし・項目どうしの全単射の組で、成り立つと来うるを保ち、かつ反映するもの。標準の入力の構造 `OfferIncidence.std n` は、段階が一つ、項目が n 個で、どの項目も来うるが、どの項目も成り立たない。`offerAt Holds Offer s xs` は、段階 s と、異なる n 個の項目 xs からなる部分構造 |

### 7.2 定義（Lean 名。名前空間 `MeaningDimension.Correspondence`）

- `Struc L`: フィールドは `carrier : Type`、`[Tarski.Structure L carrier]`、`[Nonempty carrier]`。`M.Holds σ :⇔ M.carrier↓[L] ⊧ σ`。
- `mdgOffer M σ :⇔ ¬ M.Holds σ ∧ ∃ M' : Struc L, Nonempty (M.carrier ↪ₛ[L] M'.carrier) ∧ M'.Holds σ`。
- `MDGMaking L`: フィールドは次の三つ。
  - `gen : (M : Struc L) → (σ : Sentence L) → mdgOffer M σ → Struc L`
  - `emb : ∀ M σ h, Nonempty (M.carrier ↪ₛ[L] (gen M σ h).carrier)`
  - `holds_gen : ∀ M σ h, (gen M σ h).Holds σ`
- `G.step M σ := if h : mdgOffer M σ then G.gen M σ h else M`、`G.run M₀ h := h.foldl G.step M₀`、`G.Offered M₀ h :⇔ ∀ k (hk : k < h.length), mdgOffer (G.run M₀ (h.take k)) h[k]`。
- `MDGPast L n`: フィールドは次の六つ。
  - `stage : Fin (n + 1) → Struc L`
  - `emb : ∀ k : Fin n, Nonempty ((stage k.castSucc).carrier ↪ₛ[L] (stage k.succ).carrier)`
  - `demand : Fin n → Sentence L`
  - `existential : ∀ k, IsExistential (demand k)`
  - `not_holds : ∀ k : Fin n, ¬ (stage k.castSucc).Holds (demand k)`
  - `holds : ∀ k : Fin n, (stage k.succ).Holds (demand k)`
- `c.trace : Incidence`: 段階は `Set.range c.stage`、項目は `Set.range c.demand`、成り立つは `Struc.Holds` の制限、`Next s x s' :⇔ ∃ k : Fin n, (s : Struc L) = c.stage k.castSucc ∧ (x : Sentence L) = c.demand k ∧ (s' : Struc L) = c.stage k.succ`。
- `OfferIncidence`: フィールドは `Stage`、`Item`、`Holds : Stage → Item → Prop`、`Offer : Stage → Item → Prop`。
- `OfferIncidence.Iso A B`: フィールドは `stage : A.Stage ≃ B.Stage`、`item : A.Item ≃ B.Item`、`holds_iff : ∀ s x, A.Holds s x ↔ B.Holds (stage s) (item x)`、`offer_iff : ∀ s x, A.Offer s x ↔ B.Offer (stage s) (item x)`。
- `OfferIncidence.std n`: 段階は `Unit`、項目は `Fin n`、`Holds := False`、`Offer := True`。
- `offerAt Holds Offer s xs`（`xs : Fin n ↪ I`）: 段階は `{t // t = s}`、項目は `Set.range xs`、成り立つと来うるは制限。
- 例: `sentenceQ := ∃x (x + x = 1)`、`intRat : ℤ ↪ₛ[ℒᵣ] ℚ`（自然な包含）、`padC k`（`padC 0 = sentenceC`、`padC (k + 1) = padC k ⋏ padC k`）、`natS`、`intS`、`ratS`、`realS`、`complexS : Struc ℒᵣ`、`historyPast : MDGPast ℒᵣ 4`（段階 ℕ, ℤ, ℚ, ℝ, ℂ、要求 sentenceZ, sentenceQ, sentenceR, sentenceC）。

### 7.3 命題

**CR11（MDG の入力のモデル）**
- (a) 生成の働きは存在する: `Nonempty (MDGMaking L)`。中身は指定せず、存在だけを示す。
- (b) 来うる要求については、`G.step M σ = G.gen M σ h`。
- (c) 生成のあとも、前の段階で成り立っていた存在文は成り立つ: `mdgOffer M σ` のもとで、`IsExistential τ → M.Holds τ → (G.gen M σ h).Holds τ`。

**CR12（三者の痕跡の同型）**
- (a) MDGPast の標準形: `(c.stage k).Holds (c.demand j) ↔ (j : ℕ) < k`。`c.stage` と `c.demand` は単射。
- (b) 同型 `c.ofStd : (Incidence.std n).Iso c.trace` がある。これは k を k 番目の段階に、j を j 番目の要求に送る。
- (c) 生成の働きでたどった過去: 任意の G、M₀ と、存在文だけからなる、来うる要求の過去 h（`G.Offered M₀ h`）について、MDGPast `G.toPast M₀ h ho hex : MDGPast L h.length` がある。その k 番目の段階は `G.run M₀ (h.take k)`、j 番目の要求は `h[j]`。
- (d) 三者。
  - MDGPast `c : MDGPast L h.length` と、ACSI の新鮮な過去 h について、同型 `c.trace.Iso ((acsiGrowth M).trace S₀ h)` がある。k 番目の段階を k 段の自己に、j 番目の要求を `h[j]` に送る。
  - A3 の仮定のもとで、MDGPast `c : MDGPast L n` について、同型 `c.trace.Iso (godelGrowth.trace T (conPast T n))` がある。k 番目の段階を `Tₖ` に、j 番目の要求を `Con(Tⱼ)` に送る。
- (e) 数学史の過去: `historyPast`（ℕ→ℤ→ℚ→ℝ→ℂ）は `MDGPast ℒᵣ 4` である。その痕跡は、長さ 4 の ACSI の新鮮な過去（`singletonMaking`、空の自己）の痕跡と、`conPast 𝗣𝗔 4` の痕跡に同型である。

**CR13（入力の構造）**
- (a) 抽象形: 段階 s に来うる異なる n 個の項目 xs があり、s に来うる項目が s で成り立たないなら、同型 `(OfferIncidence.std n).Iso (offerAt Holds Offer s xs)` がある。
- (b) ACSI: E が無限なら、どの n についても、空の自己に来うる（全く新しい）異なる n 個の経験 xs と、`(OfferIncidence.std n).Iso (offerAt (acsiGrowth M).Holds (fun S e ↦ S.IsNew e) Self.empty xs)` がある。作る働き M によらない。
- (c) MDG: どの n についても、ℝ に来うる異なる n 個の要求（`padC 0, …, padC (n − 1)`）と、`(OfferIncidence.std n).Iso (offerAt Struc.Holds mdgOffer realS xs)` がある。生成の働きによらない。
- (d) ゲーデル: 表示つきの理論のどの段階 S と、どの 2 個の文 `xs : Fin 2 ↪ ArithmeticSentence` についても、`(OfferIncidence.std 2).Iso (offerAt godelStageGrowth.Holds ownCon S xs)` はない。差し出しが一つだからである（CR8(d)）。
- 入力の構造では、ACSI と MDG は標準の構造を任意の大きさで含む（どの n についても。可能無限の形）。ゲーデルは大きさ 2 の標準の構造を含まない。これは「入力が事前に決まっているか」（E1、E5）を写像で表したものである。

**非空虚性（CR11–CR13）**
- CR11(a) は `ℒᵣ` で。
- CR12(e) そのもの。
- CR13(b) は `E = ℕ` で、(c) はそのまま、(d) は `𝗣𝗔` の `ascent 𝗣𝗔 0` で実例化する。

### 7.4 証明の見通し

- CR11(a): 来うる要求の定義にある構造を、選択で取る。(c): MDG1(b)。
- CR12(a): j < k なら、`stage (j+1)` で成り立ち、存在文なので埋め込みに沿って `stage k` まで残る。k ≤ j なら、`stage k` で成り立つと `stage j` まで残り、`not_holds` に反する。単射は (a) から。
- CR12(b): CR2 と同じ。(c): 来うる要求なので `step` は `gen` に一致し、`emb`・`holds_gen`・来うることの定義から MDGPast の各条件が出る。(d): (b) と CR2 を合成する（CR3 と同じ）。(e): `intRat` と `sentenceQ`（ℤ では x + x が偶数、ℚ では x = 1/2）を加え、MDG2 の事実を並べる。
- CR13(a): 段階は一点どうし、項目は `Equiv.ofInjective`。(b): 空の自己にはどの経験も全く新しい。`Infinite.natEmbedding`。(c): `padC k` はどれも `sentenceC` と同値なので ℝ で偽、ℂ で真。`complexity` が k とともに増えるので単射。(d): 同型なら標準の構造の二つの項目がどちらも来うるので、像の二つの文はどちらも `Con(S)` に等しく、項目の全単射に反する。

### 7.5 新規性と、言えないこと（CR11–CR13）

- **新規性: なし。** どれも初等的である。
- **痕跡の同型は履歴の同型であり、モデルの同型ではない。**
- **CR12 の MDG 側は、要求が存在文の場合だけである**（N16）。
- **CR13 は入力の構造（段階と、そこに来うる入力）だけを扱う。** 生成のあとの段階どうしの関係（ある入力の取り込みが別の入力を成り立たせるか）は含まない。それは生成の働き（ブラックボックス）に依存するからである。
- **モデル全体のあいだの同型写像は作らない。**
