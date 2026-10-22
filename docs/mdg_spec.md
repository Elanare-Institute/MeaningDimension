# 仕様: 意味次元生成の三つの形（反転形・未決定形・細分形）の形式化と、ACSI・ゲーデルの上昇との三者比較（MDG。実装前に固定）

この文書は実装より先に書いた。`Tests/MDGSpec.lean` のテストは**この文書の文言**から書き起こし、実装の都合で変えない。仕様を変えるときは、まずこの文書を改訂し、テストも改訂する。

典拠: 著者の指示書 `../CLAUDE_CODE_MDG_INSTRUCTIONS.md`（2026-10-20）。著者の決定 D1–D7 はそのまま従う。初版の実装後、著者側の FB（2026-10-20）で改訂した（§6）。その後、著者が次の二つを決めた（2026-10-20）。これにも従う。

- **D8**: ACSI を細分形と同一視しない。細分は ACSI の成長の一つの型である。
- **D9**: 選択（重要でない区別を同一視する）型の成長は、現在のモデルでは表していない。

追加指示書 `CLAUDE_CODE_MDG8_KAPPA_INSTRUCTIONS.md`（2026-10-21）により、§7（MDG8、調整 J11–J16）を加えた。

## 0. 背景

- `math_verification_report.md` §H の同型（CR）は、痕跡の長さだけで決まり、ACSI とゲーデルの上昇を区別しない。
- MDG は、著者の概念である意味次元生成の一つの形を形式化する。その形とは、**前の段を特殊な場合として含む矛盾の解消**（D1）である。
- そのうえで、次の三つがこの形を満たすかを Lean で判定する。
  - 数学史上の例（ℕ→ℤ、ℚ→ℝ、ℝ→ℂ）
  - ゲーデルの有限段の上昇（A3）
  - ACSI の取り込み（§E）

## 1. 指示書からの調整（Claude による）

| ID | 指示書 | この仕様での扱い |
|---|---|---|
| J1 | 埋め込み `M ↪ M'`（§2.1） | Foundation の `Tarski.Structure.Embedding`（記法 `M ↪ₛ[L] M'`）をそのまま使う。単射で、関数記号を保存し、関係記号を保存かつ反映する写像である。新しく定義しない |
| J2 | 順序 `<` を言語に含めるか | （§6 で改訂）MDG1(e)(g)・MDG2・MDG3 の例は、`<` を含まない**環の言語** `ℒᵣ`（`0, 1, +, ·, =`）で扱う。Foundation に環の言語はないので、このプロジェクトで定義する（記号は `ℒₒᵣ` から `<` を除いたもの）。ℂ には順序を入れない。`<` を使うのは MDG7（`ℤ√2`、`ℒₒᵣ`）だけである |
| J3 | 存在文・全称文（MDG1(b)(c)） | 冠頭の量化子がすべて ∃（または ∀）で、母式が量化子をもたない論理式とする。帰納的に定義する（`IsExistential`、`IsUniversal`）。Foundation の `Hierarchy 𝚺 1` は母式に有界量化子を許すので使わない |
| J4 | MDG2 の文 | 指示書のとおり。ℕ→ℤ は `∃x (x + 5 = 3)`、ℚ→ℝ は `∃x (x · x = 2)`、ℝ→ℂ は `∃x (x · x + 1 = 0)`。いずれも `ℒᵣ` の文である（J2）。ℝ→ℂ の文は A7 の `rootSentence`（`ℒₒᵣ` の文）と同じ形だが、別の文 `sentenceC` として置く。数字は Foundation の数字項 |
| J5 | MDG5 の「区別」を枠組みで述べる | ACSI の `Framework` を使う。理論 T の枠組み `provFramework T` は、各文 θ について「T で θ と証明可能に同値である」を評価述語とする。このとき、枠組みでの同一は「T で証明可能に同値」と一致する（MDG5(b)） |
| J6 | MDG7 の ℚ(√2) | Mathlib の `ℤ√2`（`Zsqrtd`、d = 2 : ℕ）を使う。体ではなく環だが、現象は同じである（共役 a + b√2 ↦ a − b√2 は環の自己同型で、√2 と −√2 を入れ替える）。「体の言語」は、`<` を使わない ℒₒᵣ の論理式（`OrderFree`）とする |
| J7 | MDG7 の枠組み | 二つの枠組みの評価述語は、どちらも、パラメータなしの、自由変数を一つもつ ℒₒᵣ の論理式が定める述語とする。`ringFramework` は `<` を使わない論理式だけ、`orderedFramework` はすべての論理式である |
| J8 | MDG5 の結論が J5 の読みに依存するか（指示書にない。Claude による追加。反例探索） | 別の読みとして、上昇の段 n の**累積の枠組み** `ascentFramework T n` を置く。評価述語は「k ≤ n の各段 Tₖ で証明できる」である。ACSI の `evaluated S` が範疇を累積するのと同じ形である。この読みのもとで MDG5(e)(f) を調べる |
| J9 | 名前（§6 で追加） | 三つの形を**反転形**（偽→真）、**未決定形**（未決定→決定）、**細分形**（区別されない→区別される）と呼ぶ。Lean 名は `ReversalStep`（旧 `GenStep`）、`Settles`（旧 `UndecidedDoor`）、`RefineStep`。三つのそれぞれを意味次元生成に含めるかは著者が決める（§5）。英語の説明文では "contradiction" を形の名前に使わない。どの形でも、一つの体系の中で φ ∧ ¬φ が成り立つわけではないからである（A8、AC3(b)） |
| J10 | 古い領域に制限した評価（§6 で追加） | `EvalOn L R φ b ε` を、量化子をすべて集合 R に制限した評価として、論理式についての再帰で定義する。これは、M' に R を表す述語を加えた構造での、R に相対化した論理式 φᴿ の真理条件である。相対化した論理式そのもの（構文）は作らない |

## 2. 定義（Lean 名。名前空間 `MeaningDimension.Generation`）

### 2.1 反転形（構造のあいだ）

言語 L、構造 M、M'（`Nonempty`、`Tarski.Structure L`）について次のように定める。

- `Flips L M M' σ :⇔ M ⊧ ∼σ ∧ M' ⊧ σ`（反転文）。
- `ReversalStep L M M' :⇔ Nonempty (M ↪ₛ[L] M') ∧ ∃ σ, Flips L M M' σ`（反転形の一歩）。
- `IsExistential φ`: 帰納的に定める。量化子のない φ（Foundation の `φ.Open`）は存在的である。存在的な φ について、`∃¹ φ` も存在的である。
- `IsUniversal φ`: 同様に、量化子のない φ と、全称的な φ についての `∀¹ φ` とする。
- `EvalOn L R φ b ε`（R : Set M'）: 次の再帰で定める（J10）。原子論理式・⊤・⊥・∧・∨ は `Eval` と同じ。`∀¹ φ` は「R のすべての x について `EvalOn L R φ (x :> b) ε`」、`∃¹ φ` は「R のある x について `EvalOn L R φ (x :> b) ε`」。

### 2.2 細分（枠組みのあいだ。ACSI の `Framework`）

- `Refines F F' :⇔ F.preds ⊆ F'.preds`（細分）。
- `DistinctionFlip F F' x y :⇔ F.Same x y ∧ ¬ F'.Same x y`（区別の反転）。
- `RefineStep F F' :⇔ Refines F F' ∧ ∃ x y, DistinctionFlip F F' x y`（細分形の一歩）。

### 2.3 理論のあいだ（未決定形）

- `TheoryFlip T T' σ :⇔ T ⊢ ∼σ ∧ T' ⊢ σ`（理論の反転: 反証されていた文が証明される）。
- `Settles T T' σ :⇔ T ⪯ T' ∧ T ⊬ σ ∧ T ⊬ ∼σ ∧ T' ⊢ σ`（未決定形: T で未決定の σ を T' が決める）。
- `provFramework T : Framework ArithmeticSentence`: 評価述語は `{(fun σ ↦ T ⊢ σ 🡘 θ) | θ}`。
- `ascentFramework T n : Framework ArithmeticSentence`: 評価述語は `{(fun σ ↦ Tₖ ⊢ σ) | k ≤ n}`（J8）。

### 2.4 例

- `ℒᵣ`: 環の言語（J2）。関数記号は `0, 1, +, ·`、関係記号は `=` だけ。`Zero`、`One`、`Add`、`Mul` をもつ型には標準の `ℒᵣ` 構造を入れる。
- `sentenceZ := ∃x (x + 5 = 3)`、`sentenceR := ∃x (x · x = 2)`、`sentenceC := ∃x (x · x + 1 = 0)`（すべて `Sentence ℒᵣ`）。
- 埋め込み `natInt : ℕ ↪ₛ[ℒᵣ] ℤ`、`ratReal : ℚ ↪ₛ[ℒᵣ] ℝ`、`realComplex : ℝ ↪ₛ[ℒᵣ] ℂ`（自然な包含）。
- `OrderFree φ`: φ の原子論理式が `<` を使わない。
- `ringFramework`、`orderedFramework : Framework ℤ√2`（J7）。
- `conj : ℤ√2 ≃ ℤ√2`: 共役（Mathlib の `star`）。

## 3. 命題

**MDG1（前の段を壊さない）** 埋め込み `Θ : M ↪ₛ[L] M'`、束縛変数の値 e、自由変数の値（パラメータ）ε について、次が成り立つ。
- (a) 量化子のない φ について、`φ.Eval e ε ↔ φ.Eval (Θ ∘ e) (Θ ∘ ε)`。
- (b) 存在的な φ について、`φ.Eval e ε → φ.Eval (Θ ∘ e) (Θ ∘ ε)`。
- (c) 全称的な φ について、`φ.Eval (Θ ∘ e) (Θ ∘ ε) → φ.Eval e ε`。
- (d) 文について、次の二つが成り立つ。
  - 存在文 σ は真から偽に反転しない: `¬ (M ⊧ σ ∧ M' ⊧ ∼σ)`。
  - 全称文 σ は偽から真に反転しない: `¬ Flips L M M' σ`。
- (e) 全称文は真から偽に反転しうる。ℝ→ℂ で、全称文 `∼sentenceC` は ℝ で真、ℂ で偽である。
- (f) （§6 で追加）古い領域に制限すれば、すべての論理式の真理値が保たれる: どの φ についても `φ.Eval e ε ↔ EvalOn L (Set.range Θ) φ (Θ ∘ e) (Θ ∘ ε)`。文については `M ⊧ σ ↔ EvalOn L (Set.range Θ) σ ![] Empty.elim`。前の段で真の文は真のまま、偽の文は偽のまま残る。
- (g) （§6 で追加）ℝ→ℂ で、ℂ において次の二つが同時に成り立つ。
  - 古い領域に制限した `∼sentenceC`（∀x ∈ ℝ, x · x + 1 ≠ 0）は真（狭い読み）。
  - 制限しない `∼sentenceC` は偽、つまり `ℂ ⊧ sentenceC`（広い読み）。

**MDG2（数学の例は反転形の一歩である）**
- (a) ℕ→ℤ: `sentenceZ` は ℕ で偽、ℤ で真。`ReversalStep ℒᵣ ℕ ℤ`。
- (b) ℚ→ℝ: `sentenceR` は ℚ で偽、ℝ で真。`ReversalStep ℒᵣ ℚ ℝ`。
- (c) ℝ→ℂ: `sentenceC` は ℝ で偽、ℂ で真。`ReversalStep ℒᵣ ℝ ℂ`。
- (d) 三つの反転文はいずれも存在文である（MDG1(d) と整合する）。

**MDG3（埋め込みの条件は必要である）**
- ℂ から ℝ への埋め込みはない: `IsEmpty (ℂ ↪ₛ[ℒᵣ] ℝ)`。理由は MDG1(b) で、存在文 `sentenceC` が ℂ で真、ℝ で偽だからである。
- ℂ→ℝ にも反転文はある。`∼sentenceC` は ℂ で偽、ℝ で真である。
- それでも `¬ ReversalStep ℒᵣ ℂ ℝ` である。

**MDG4（ゲーデルの上昇は反転形を通らず、未決定形を通る）**
- (a) `T ⪯ T'` で T' が無矛盾なら、どの σ についても `¬ TheoryFlip T T' σ`（A8(a) の再掲）。
- (b) A3 の上昇（T は `[T.Δ₁]`、`𝗜𝚺₁ ⪯ T`、Σ₁ 健全）のどの段についても、`¬ TheoryFlip Tₙ Tₙ₊₁ σ`。
- (c) 同じ仮定のもとで、`Settles Tₙ Tₙ₊₁ Con(Tₙ)`。反証できないこと（`Tₙ ⊬ ∼Con(Tₙ)`）には、Tₙ の Σ₁ 健全性（A2）を使う。

**MDG5（ゲーデルの上昇と細分形。読みによる）**
- (a) `T ⪯ T'` なら、`T ⊢ φ 🡘 ψ → T' ⊢ φ 🡘 ψ`。
- (b) `(provFramework T).Same φ ψ ↔ T ⊢ φ 🡘 ψ`。
- (c) `T ⪯ T'` なら、どの φ、ψ についても `¬ DistinctionFlip (provFramework T) (provFramework T') φ ψ`。したがって `¬ RefineStep (provFramework T) (provFramework T')`。
- (d) A3 の上昇のどの段についても `¬ RefineStep (provFramework Tₙ) (provFramework Tₙ₊₁)`。
- (e) （J8。読みへの依存の確認）A3 の仮定のもとで、どの段についても `RefineStep (ascentFramework T n) (ascentFramework T (n + 1))`。反転する対は `(Con(Tₙ), ∼Con(Tₙ))` である。Tₙ 以前の段ではどちらも証明できず、Tₙ₊₁ では一方だけが証明できる。
- (f) （§6 で追加。J8 での細分形と未決定形の関係）A3 の仮定のもとで、どの段 n についても次が成り立つ。
  - `Settles Tₙ Tₙ₊₁ σ` なら `DistinctionFlip (ascentFramework T n) (ascentFramework T (n + 1)) σ (∼σ)`。
  - 逆に、`DistinctionFlip (ascentFramework T n) (ascentFramework T (n + 1)) φ ψ` なら、`Settles Tₙ Tₙ₊₁ φ` または `Settles Tₙ Tₙ₊₁ ψ`。
  - したがって `RefineStep (ascentFramework T n) (ascentFramework T (n + 1)) ↔ ∃ σ, Settles Tₙ Tₙ₊₁ σ`。J8 の読みでは、上昇の細分形の一歩は未決定形の一歩と同じものである。

**MDG6（ACSI の取り込み）**
- (a) 分類は真から偽に反転しない: `S.Classifies e' → (M.incorporate S e).Classifies e'`（AC5(c) の再掲）。
- (b) **判定する命題。** 任意の M、S、e について `Refines (evaluated S) (evaluated (M.incorporate S e))` が成り立つかを判定する。成り立てば、`S.IsNew e`、`S.IsNew e'`、`e' ∉ M.generate S e` のもとで `RefineStep (evaluated S) (evaluated (M.incorporate S e))` が成り立つ。反転する対は `(.inr e, .inr e')` である（AC4(b)、AC5(e)）。
  - 成り立たない場合は、どの述語が保たれないかを報告する。
  - 結果を見越して定義を変えない。既存の `evaluated`、`incorporate` をそのまま使う。
- (c) `singletonMaking : Making ℕ`、空の自己、経験 0、1 で (b) を実例化する。
- (d) （D9 の裏づけ）取り込みは、区別されていたものを同一視しない。
  - 一回の取り込み: `(evaluated (M.incorporate S e)).Same x y → (evaluated S).Same x y`。
  - 任意の過去 h: `Refines (evaluated S) (evaluated (M.run S h))`。したがって `(evaluated (M.run S h)).Same x y → (evaluated S).Same x y`。

**MDG7（細分形の数学の例）**
- (a) `conj` は ℒₒᵣ の関数記号（`0, 1, +, ·`）を保存する。`<` は保存しない。
- (b) `<` を使わない論理式は `conj` で真理値を変えない（パラメータなし）。
- (c) `ringFramework.Same √2 (−√2)`。
- (d) `¬ orderedFramework.Same √2 (−√2)`。区別するのは `0 < x` である。
- (e) `RefineStep ringFramework orderedFramework`。

**非空虚性**
- MDG2・MDG3 は具体例そのものである。
- MDG1(f) は (g)（ℝ→ℂ）で実例化する。
- MDG4・MDG5(d)(e)(f) は 𝗜𝚺₁ と 𝗣𝗔 で実例化する。
- MDG6(c)。

## 4. 証明の見通し

- MDG1(a) は Foundation の `Semiformula.eval_hom_iff_of_open`。(b)(c) は IsExistential・IsUniversal についての帰納法で、∃ の証人を Θ で送る。(d) は (b)(c) の文の場合。
- MDG2: 埋め込みは Mathlib の `Nat.cast`、`Rat.cast`、`Complex.ofReal`。ℚ で偽なのは √2 の無理性（`irrational_sqrt_two`）による。
- MDG1(f): 論理式についての再帰。∀・∃ の場合は、R = Θ の像の元が Θ x の形であることを使う。項の値は Foundation の `HomClass.val_term`、関係記号は `EmbeddingClass.rel`。
- MDG3: もし埋め込みがあれば、MDG1(b) により `sentenceC` が ℝ で真になり、ℝ で x · x + 1 ≠ 0 であることに反する。
- MDG4: (a) は A8(a)。(b) は A3（各段の無矛盾性）と (a)。(c) は A3 の `G2_unprovable`、Foundation の `con_unrefutable`、公理の証明。
- MDG5: 弱化と、命題論理の同値の推移性。(e) は、k ≤ n なら `Tₖ ⪯ Tₙ` であることと、MDG4(c)、Tₙ₊₁ の無矛盾性による。(f) の逆向きは、区別が k ≤ n の段では起きないので k = n + 1 の段で起きること、Tₙ で証明できる側があればもう一方も証明できること、Tₙ で反証される側が Tₙ₊₁ で証明されれば Tₙ₊₁ が矛盾することによる。
- MDG6(b): `incorporate` は範疇の列の先頭に一つ加えるだけなので、評価述語は保たれる見込み。(d) は (b) と、細分が同一を逆向きに保つこと（`Refines.same`）、過去についての帰納法による。
- MDG7: Foundation の `eval_iff_of_equiv` と同じ帰納法を、`<` を使わない論理式に制限して行う。

## 5. 新規性と、言えないこと

- **新規性: なし。** すべて既知の事実（埋め込みと存在文の保存、Gödel II、共役による識別不能性）か、その初等的な系である。
- 意味次元生成に伴う人間の意思、生成が発見ではないこと、可能無限であることは形式化しない。
- MDG2 の例は、意味次元生成が**起きた後の**構造の関係を述べるだけで、生成の過程は表さない。
- 型があらかじめ固定されているので、「まだ存在しない構造」は表せない（ACSI の M7 と同じ限界）。
- 「前の段を壊さない」（MDG1）は、制限せずに評価すると、量化子のない事実と存在文についてだけ成り立つ。全称文は取り消されうる（MDG1(e)、A7）。古い領域に制限すれば、すべての文が保たれる（MDG1(f)）。
- MDG1(f) の R は埋め込み Θ の像であり、Θ の選び方による。埋め込みの一意性は扱わない。`EvalOn` は相対化した論理式の真理条件を直接与えたもので、R を記号として加えた言語や、相対化した論理式（構文）は作らない（J10）。
- MDG1(f) はどの埋め込みでも成り立つ。反転形の一歩に特有の性質ではない。
- 構造のあいだの反転（`Flips`）と理論のあいだの反転（`TheoryFlip`）は、別の定義である。三者比較の表では、この違いを明記する。
- MDG5(c)(d) の「細分なし」は、J5 の読み（区別 = 証明可能な同値）での結果である。MDG5(e) は、別の読みでは結論が変わることを示す。MDG5(f) により、J8 の読みでは上昇の細分形は未決定形と同じものになる。J5 の読みでは三つの形は別々に保たれる。どちらの読みが著者の「区別の細かさ」に合うかは、著者が判断する。**（2026-10-22: 著者は J5 を採った。J8 の累積の枠組みは ACSI の範疇の累積に形を合わせた評価関数で、ゲーデル自身の区別ではないので、ゲーデル側に持ち込まない。`correspondence_spec.md` §6.0 の E2。MDG5(e)(f) は、取り替えた評価関数についての定理として残す。）**
- 三つの形のそれぞれを意味次元生成に含めるかは、著者が判断する（J9）。
- MDG6(b) は、ACSI の取り込みが細分形の一歩でもあることを示すだけである。ACSI を細分形と同一視しない（D8）。
- 選択型の成長（区別されていたものを同一視する移行）は表さない（D9）。MDG6(d) により、現在のモデルの成長（取り込み）はこの型をとらない。モデルには区別の粗い枠組み（純粋経験の枠組み `Framework.pure`、自己同一の枠組み `selfIdentity`）もあるが、取り込みがそこへ移ることはない。
- MDG7 は ℤ√2 についての主張であり、ℚ(√2) そのものについては述べない。

## 6. 改訂（2026-10-20、著者側の FB による）

初版の実装（MDG1–MDG7）の後、次のとおり改訂した。テストもこの改訂に合わせて改訂する。

- **名前（J9）**: 「矛盾の扉」「未決定性の扉」をやめ、反転形・未決定形・細分形と呼ぶ。`GenStep` → `ReversalStep`、`UndecidedDoor` → `Settles`。定義の中身は変えない。
- **言語（J2・J4）**: ℝ→ℂ の例で ℂ に部分順序 `ComplexOrder` を入れるのをやめる。MDG1(e)・MDG2・MDG3 を環の言語 `ℒᵣ` で述べ直す。`<` は MDG7 だけで使う。旧版の `ℒₒᵣ` での例（`ComplexOrder` を使うもの）は廃止する。A7（`Examples/ComplexNumbers.lean`）は変えない。
- **追加（J10・MDG1(f)(g)）**: 古い領域に制限した文の保存。全称文が取り消されるのは制限せずに評価したときであり、古い領域に制限すれば前の段の文はすべて保たれることを示す。
- **追加（MDG5(f)）**: J8 の読みでの、細分形と未決定形の一致。
- **著者の決定 D8・D9**: 冒頭に記録した。D9 の裏づけとして MDG6(d) を加える。

## 7. MDG8: Kappa の「2+2=5」と埋め込みの条件（2026-10-21 追加）

典拠: 著者の追加指示書 `CLAUDE_CODE_MDG8_KAPPA_INSTRUCTIONS.md`（2026-10-21）。D1–D9 はそのまま従う（とくに D4: 「含む」は構造の埋め込みで読む）。Lakatos の読解が正しいかは検証の対象外とし、指示書 §0 の要約（2 ポンドの品物二つを 1 ポンドの箱で受け取ると「2 と 2 で 5 ポンド」）を前提に使う。名前空間は `MeaningDimension.Generation.Kappa`、ファイルは `MeaningDimension/Generation/Packing.lean`。

### 7.1 指示書からの調整（Claude による）

| ID | 指示書 | この仕様での扱い |
|---|---|---|
| J11 | 構造 `addModel`、`packModel w`（台はどちらも ℚ） | Lean の `Tarski.Structure` は型クラスなので、同じ型 ℚ に二つの構造を同時に入れられない。構造そのものは定義 `addModel`、`packModel w : Tarski.Structure ℒₖ ℚ` として置く。インスタンスとしては、ℚ に `addModel` を、型の別名 `Pack w := ℚ` に `packModel w` を入れる。指示書の `addModel ↪ₛ[ℒₖ] packModel w` は `ℚ ↪ₛ[ℒₖ] Pack w` と書く。`ℒ⊕` の構造（`addModelP`、`packModelP w`）と `ℒᵣ` の構造 `packRing w` も同じようにする。ℚ の `ℒᵣ` 構造は既存の `ringModel` である |
| J12 | 言語 `ℒₖ`、`ℒ⊕` | 関数記号を帰納型で定める。`ℒₖ` は ⊕（2 項）と、各 n : ℕ の定数記号 ⌜n⌝。`ℒ⊕` は ⊕ だけ。関係記号はどちらも `=` だけで、`ℒᵣ` の `RingRel` を流用する。Lean 名は `kappaLang`（記法 `ℒₖ`）、`plusLang`（記法 `ℒ⊕`） |
| J13 | 文 `four`、`five` | Foundation の “…” 記法は ⌜n⌝ を数字項に読むので使わず、原子論理式 `rel (=) ![⌜2⌝ ⊕ ⌜2⌝, ⌜4⌝]` として直接つくる |
| J14 | (c)・(e) の「埋め込みはない」 | 二つを一つの補題から出す。量化子のない文 σ が M で真、M' で偽なら、M から M' への埋め込みはない（MDG1(a)）。(c) は σ = `four`、(e) は σ = `zeroR := “0 + 0 = 0”`（`ℒᵣ`）に使う |
| J15 | (d) の系「どの `ℒ⊕` の文も真理値が同じ」 | 全射の埋め込みについての一般の補題として示す。MDG1(f) で、像が台全体になる場合である（全体に制限した評価は、制限しない評価と同じ） |
| J16 | 追加（指示書にない。Claude による） | (c) を一般の w ≠ 0 でも反転文つきで述べる（`∼four` が反転する）。(e) に、MDG3 と同じ形の系（`Flips ℒᵣ ℚ (Pack w) (∼zeroR)` と `¬ ReversalStep ℒᵣ ℚ (Pack w)`）を加える。(b) を `ℒ⊕`・`ℒᵣ` でも述べる |

### 7.2 定義（名前空間 `MeaningDimension.Generation.Kappa`）

- `ℒₖ`: 関数記号は `plus`（2 項、⊕）と `num n`（0 項、⌜n⌝、n : ℕ）。関係記号は `=` だけ。
- `ℒ⊕`: 関数記号は `plus`（2 項、⊕）だけ。関係記号は `=` だけ。
- `addModel : Tarski.Structure ℒₖ ℚ`: ⊕ を a + b、⌜n⌝ を (n : ℚ)、`=` を等号と解釈する。
- `packModel w : Tarski.Structure ℒₖ ℚ`（w : ℚ）: ⊕ を a + b + w、⌜n⌝ を (n : ℚ)、`=` を等号と解釈する。
- `addModelP`、`packModelP w : Tarski.Structure ℒ⊕ ℚ`: 同じく、⊕ を a + b、a + b + w と解釈する。
- `packRing w : Tarski.Structure ℒᵣ ℚ`: + を a + b + w と解釈し、0、1、·、`=` は通常どおり。
- `Pack w := ℚ`（型の別名）。インスタンス: ℚ には `addModel`（`ℒₖ`）、`addModelP`（`ℒ⊕`）、既存の `ringModel`（`ℒᵣ`）。`Pack w` には `packModel w`、`packModelP w`、`packRing w`（J11）。
- `four := ⌜2⌝ ⊕ ⌜2⌝ = ⌜4⌝`、`five := ⌜2⌝ ⊕ ⌜2⌝ = ⌜5⌝`（`Sentence ℒₖ`、J13）。
- `fourR := “2 + 2 = 4”`、`zeroR := “0 + 0 = 0”`（`Sentence ℒᵣ`。数字は Foundation の数字項）。

### 7.3 命題

**MDG8（Kappa の梱包）**

- (a) 真理値。
  - `ℚ ⊧ four`、`ℚ ⊧ ∼five`（`ℒₖ`、`addModel`）。
  - w ≠ 0 なら `Pack w ⊧ ∼four`。
  - `Pack 1 ⊧ five`（Lakatos の数値）。
- (b) 特殊な場合はパラメータの値である。
  - 構造として等しい: `packModel 0 = addModel`、`packModelP 0 = addModelP`、`packRing 0 = ringModel ℚ`。
  - 恒等写像は `ℒₖ` の埋め込み `ℚ ↪ₛ[ℒₖ] Pack 0` で、全射である。
- (c) 数を固定すると埋め込みはない。
  - 一般の補題（J14）: σ が量化子をもたず、`M ⊧ σ`、`M' ⊧ ∼σ` なら `IsEmpty (M ↪ₛ[L] M')`。
  - w ≠ 0 なら `IsEmpty (ℚ ↪ₛ[ℒₖ] Pack w)`。
  - w ≠ 0 なら `Flips ℒₖ ℚ (Pack w) (∼four)`（J16）。
  - `Flips ℒₖ ℚ (Pack 1) five`。
  - w ≠ 0 なら `¬ ReversalStep ℒₖ ℚ (Pack w)`。とくに `¬ ReversalStep ℒₖ ℚ (Pack 1)`。
- (d) 数の記号がなければ同型になる。
  - どの w についても、x ↦ x − w は `ℒ⊕` の埋め込み `shift w : ℚ ↪ₛ[ℒ⊕] Pack w` で、全射である。
  - 一般の補題（J15）: 埋め込み Θ が全射なら、どの文 σ についても `M ⊧ σ ↔ M' ⊧ σ`。
  - 系: どの w、どの `ℒ⊕` の文 σ についても `ℚ ⊧ σ ↔ Pack w ⊧ σ`。
  - したがって、どの w についても `¬ ReversalStep ℒ⊕ ℚ (Pack w)`（埋め込みはあるが、反転文がない）。とくに w = 1。
- (e) 数を加法で作る言語 `ℒᵣ`。
  - どの w についても `Pack w ⊧ fourR`。`ℚ ⊧ fourR`。
  - w ≠ 0 なら `IsEmpty (ℚ ↪ₛ[ℒᵣ] Pack w)`（J14。`zeroR` は ℚ で真、`Pack w` で偽）。
  - w ≠ 0 なら `Flips ℒᵣ ℚ (Pack w) (∼zeroR)`、`¬ ReversalStep ℒᵣ ℚ (Pack w)`（J16）。
- (f) まとめの表（報告 §I11）。行は `ℒₖ`・`ℒ⊕`・`ℒᵣ`、列は「埋め込みがあるか」「Kappa の文の真理値」「`ReversalStep` か」。

**非空虚性**: (a)–(e) は具体例そのものである。w = 1（Lakatos の数値）と、一般の w ≠ 0 の両方で述べる。テストでは w = 1 と w = −1/2 で実例化する。

### 7.4 証明の見通し

- (a) は有理数の計算。(b) は構造の外延性（関数記号ごとに `add_zero`）。
- (c) の補題は MDG1(b)（量化子のない文は存在的）。`four` は `addModel` で真、`packModel w` では 2 + 2 + w = 4 から w = 0 になるので偽。
- (d) (a − w) + (b − w) + w = (a + b) − w。全射の補題は MDG1(f) と、全体に制限した評価が `Eval` と一致すること（論理式についての帰納法）。
- (e) 数字項は 1 と + から作られる（`numeral (n + 2) = numeral (n + 1) + 1`）。`Pack w` での値は (n + 1) + n·w になり、2 + 2 と 4 はどちらも 4 + 3w。`zeroR` は `Pack w` で 0 + 0 + w = 0、つまり w = 0 になるので偽。

### 7.5 言えないこと

- (b) の「特殊な場合」は、パラメータ w を 0 にすることである。MDG1(f) の「古い領域への制限」（埋め込みの像への制限）とは別の操作である。どちらが著者の「前の段を特殊な場合として含む」に当たるかは判断しない（§5 と同じく著者が決める）。
- 言語の選択（どの記号の意味を固定するか）を Lean は決めない。MDG8 は、選んだ言語ごとの帰結を並べるだけである。
- 梱包が「概念の拡張」として正当かどうか、Lakatos の Kappa・Gamma・Theta のどの立場が正しいかは扱わない。
- ここでの構造はどれも同じ台 ℚ の上にある。「重さのない加法」から「梱包」への移行は、台を広げる移行ではない。
- 新規性: なし。初等的な計算である。

## 8. 注記（2026-10-22。入力が来る前の評価について）

- **D1(b) の「前の段で偽」の読み。** これは古い言語での事実（例: x² + 1 = 0 は実数の解をもたない。「解けなかった」）であり、まだ生まれていない新しい概念（複素数）の否定ではない（著者の指摘、2026-10-22）。Lean の `Flips`（`M ⊧ ∼σ`）は、言語 `ℒᵣ` を前もって固定しているので評価できる。これを「新しい概念の否定が成り立っていた」と読まない。
- **MDG4 の反転形と未決定形の対比。** ゲーデルの入力 Con(T) は事前に決まっていて、T の言語で書ける。そのため、前の段での状態（未決定）がゲーデルのモデルの構造に入る。MDG と ACSI では入力が事前に決まっておらず、入力が来る前の段階で入力やその否定を評価することはモデルの構造ではない。したがって、この対比はゲーデルの入力が事前に決まっていることの別の面であり、MDG とゲーデルのモデルの構造の違いとして独立に数えない。Lean の定理（MDG4 など）は数学の事実としてそのまま残る。
- **§5 の「生成の過程は表さない」について。** 生成の働きを中身を指定しないブラックボックスとして置けば、入力から新しい段ができる形を表せる。`correspondence_spec.md` §7 の CR11（`MDGMaking`）でそうした。人間の意思そのものは、引き続き形式化しない。
