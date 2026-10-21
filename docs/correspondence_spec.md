# 仕様: ACSI とゲーデルの上昇の、部分的な構造同型（CR。実装前に固定）

この文書は実装より先に書いた。`Tests/CorrespondenceSpec.lean` のテストは**この文書の文言**から書き起こし、実装の都合で変えない。仕様を変えるときは、まずこの文書を改訂し、テストも改訂する。

## 0. 背景

- `math_verification_report.md` §F3.3 は、対応表 (i)–(v) の「構造的同型」という語に形式的な裏づけがないと記録した。二つの側のあいだに、構造を保つ写像を定義していないからである。
- 著者の問い（2026-10-20）:「ゲーデルとの構造的同型を部分的にでも示せる？」
- CR は、(i)(ii)(iii)(v) の行について、構造を保つ全単射を定義して、それが同型であることを証明する。(iv) は同型に含めない。共通の形（CR6）として別に述べる。
- 表示の選び方を「外から来る経験」と同じように扱ってよいかは、著者が判断する（§G7）。この文書と実装はその判断をしない。

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

- **新規性: なし。** 数学的には初等的である。形式的な内容は、§F3.3 が欠けていると記録した「構造を保つ写像」を定義し、それが同型であることを証明した点にある。
- **同型は、ゲーデルに固有の内容を区別しない。** CR2 により、新鮮な痕跡の同型類は長さだけで決まる。したがって同型は、同じ長さの新鮮な過去のどの二つのあいだにも成り立つ。二つの ACSI の過去のあいだにも、Con ではない独立な文を加えていくゲーデル側の過去とのあいだにも成り立つ。Con(T) が T 自身の指定する文であることと、それが証明できないこと（Gödel II）は、ゲーデル側の過去が新鮮であること（CR4(a)）にだけ入っている。
- **(iv) は同型に含まれない。** CR6 は共通の形であって、同型ではない。差し出される項目 `Offer` は両側で異なる。ACSI 側は全く新しい経験のすべてである。ゲーデル側は、ある表示から作った無矛盾性文である。両者が対応するかは、著者の判断による。
- **保つのは、過去に沿った継起 `Next` だけである。** 取り込み `step` 一般は保たない。たとえば j < k のとき、ゲーデル側では `Tₖ ∪ {Con(Tⱼ)} = Tₖ` となる（取り込み直しても何も変わらない）。ACSI 側の `incorporate` は、つねに経験を一つ多くもつ新しい自己を作る。この例は Lean では述べていない。
- **捨てているもの。** 段階と項目が何であるか（範疇をもつ自己か、公理集合か）を捨てている。AC1–AC4、AC6、AC7、AC10（枠組み、主客未分、互いに先立つこと）も捨てている。AC7 の先行関係 `Base h` は過去の長さだけから定義されるので、同じ長さのどの痕跡にも共通する。これを対応とは主張しない。
- **続く仮定は異なる。** ACSI 側は開放性、ゲーデル側は Σ₁ 健全性を仮定する（§F1 (v)）。ACSI 側の過去はあらかじめ与えられていない（∀n∃h。M7）。ゲーデル側の過去 `conPast T n` は、T と n の関数である。
- **有限の痕跡だけを扱う。** 無限の過程どうしの同型は述べない。
- **(i) の「記述不能」は表していない。** `Holds` は「分類できる」と「証明できる」である。
