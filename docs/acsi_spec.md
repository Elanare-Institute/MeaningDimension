# 仕様: 絶対矛盾的自己同一（著者の定式化）の形式化（実装前に固定）

この文書は実装より先に書いた。`Tests/ACSISpec.lean` のテストは**この文書の文言**から書き起こし、実装の都合で変えない。仕様を変えるときは、まずこの文書を改訂し、テストも改訂する。

Gödel 関係の形式化（`docs/spec.md`）とは独立である。Lean のコードは `MeaningDimension/ACSI/` に置き、Gödel 側の定義に依存しない。

## 0. 典拠と範囲

著者の定式化（2026-10-19、会話）。西田本文に帰属させるのではなく、**著者が西田から抽出した定式化**として扱う。

> 絶対矛盾的自己同一は、純粋経験からスタートする。純粋経験とは経験を認識して評価する前の状態のことを指している。純粋経験は評価する前なので主客未分である。そして全く新しいものを体験しても人間はそれを経験として自己の認識体系に取り込めるわけだから、作られたものだけではなく、作るものである。これを絶対矛盾的自己同一という。
> このとき主客未分も矛盾であり、経験は自己の土台になるものであるということも矛盾が存在する。
> 主客未分の純粋経験のなかでは経験と自己が同一化しているという、通常の私たちの感覚ではありえないが確かにある状態を経由して自己が作られ経験も蓄えられていく

著者の選択（2026-10-19）:

- **主客未分の矛盾は「枠組みによる」。** 評価後の通常の枠組みでは「自己＝経験」は偽、純粋経験の枠組みでは真。一つの枠組みの中に φ ∧ ¬φ は現れない（ℝ と ℂ の例 P1.3 と同じ型）。
- **「経験は自己の土台」の矛盾は「互いに先立つ」。** 経験は自己の土台として自己に先立ち、自己は経験する主体として経験に先立つ。

後者も前者と同じく、枠組みに相対的な矛盾として扱う（モデル化上の選択 M6）。矛盾許容論理は使わない。

## 1. モデル化上の選択（Claude による。著者の記述そのものではない）

| ID | 著者の記述 | 形式化 |
|---|---|---|
| M1 | 枠組み | 領域 `D` 上の評価述語の集合。二つのものは、その枠組みのどの評価述語でも区別されないとき、その枠組みで同一とする（識別不可能なものの同一を、枠組みに相対化したもの）。枠組みで見た対象は、この同値関係による商 |
| M2 | 純粋経験＝認識して評価する前の状態 | 評価述語を一つももたない枠組み `pure` |
| M3 | 評価した後の通常の枠組み | 自己 `S` の枠組み `evaluated S`。述語は「評価する側（主）である」と、`S` の各範疇 `c` についての「`c` に入る経験である」 |
| M4 | 自己、認識体系、経験が蓄えられる | 自己 = 蓄えた経験の列と、範疇（経験の集合）の列。どれかの範疇に入る経験を、自己が「分類できる」経験とする |
| M5 | 全く新しいもの、取り込む、作るもの | 新しい = 自己のどの範疇にも入らない。作る働き = 自己と経験から範疇を生成する関数で、生成された範疇はその経験を含む。生成は自己（作られたもの）に依存してよい。取り込み = 経験を蓄え、生成した範疇を認識体系に加える |
| M6 | 互いに先立つ | 過去の経験の列 `h`（時間順）を展開した節点 `self k`, `exp k` の上の直接の先行。`self k` は `exp k` に先立つ（`k` 段階の自己が `h[k]` を取り込む主体である）。`exp k` は `self (k+1)` に先立つ（`h[k]` は `k+1` 段階の自己が蓄えた経験である）。自己同一の枠組みは、すべての `self k` を区別しない枠組み |
| M7 | 未来はまだ存在しない（T3） | 経験の無限列をあらかじめ与えない。過去は有限の列とし、これからの経験については「どの自己にも、ある経験がある」（∀∃）の形でだけ述べる |

## 2. 定義（Lean 名。すべて名前空間 `MeaningDimension.ACSI`）

- `Framework D`: フィールド `preds : Set (D → Prop)`。
- `F.Same x y :⇔ ∀ P ∈ F.preds, (P x ↔ P y)`。同値関係。`F.Obj` はその商、`F.obj x` は `x` の同値類。
- `Framework.pure : Framework D`: `preds = ∅`。
- `Framework.discrete : Framework D`: `preds = {(· = x) | x : D}`（すべてを区別する枠組み）。
- `F.Lift R a b :⇔ ∃ x y, F.obj x = a ∧ F.obj y = b ∧ R x y`（関係 `R` を枠組み `F` の対象に移したもの）。
- `F.Mutual R x y :⇔ F.Lift R (F.obj x) (F.obj y) ∧ F.Lift R (F.obj y) (F.obj x)`（枠組み `F` で `x` と `y` が互いに `R` で先立つ）。
- `Self E`: フィールド `experiences : List E`、`categories : List (Set E)`。`Self.empty` は両方とも空。
- `S.Classifies e :⇔ ∃ c ∈ S.categories, e ∈ c`、`S.IsNew e :⇔ ¬ S.Classifies e`。
- `S.eval e : Set (Set E) := {c | c ∈ S.categories ∧ e ∈ c}`（評価された経験）。
- `Entity E := Self E ⊕ E`（`inl` が主の側、`inr` が客の側）。
- `evaluated S : Framework (Entity E)`: `preds = {isSubject} ∪ {inCategory c | c ∈ S.categories}`。`isSubject` は `inl` で真・`inr` で偽。`inCategory c` は `inl` で偽、`inr x` で `x ∈ c`。
- `Making E`: フィールド `generate : Self E → E → Set E`、`mem_generate : ∀ S e, e ∈ generate S e`。
- `M.incorporate S e := ⟨e :: S.experiences, M.generate S e :: S.categories⟩`。
- `M.run S₀ h := h.foldl M.incorporate S₀`（`h` は時間順の過去）。
- `M.Reachable S₀ S`: `S₀` から取り込みを有限回繰り返して `S` に至る（帰納的定義）。
- `M.IsOpen S₀ :⇔ ∀ S, M.Reachable S₀ S → ∃ e, S.IsNew e`（開放性: 到達しうるどの自己にも、その自己にとって全く新しい経験がある）。
- `FactorsThroughEval inc :⇔ ∃ g, ∀ S e, inc S e = g S (S.eval e)`（経験そのものではなく、評価された結果だけに依存する取り込み）。
- `singletonMaking : Making E`: `generate S e = {e}`。
- `Node`: `self (k : ℕ)` と `exp (k : ℕ)`。
- `Base h`: 構成子 `subject k : k < h.length → Base h (self k) (exp k)` と `ground k : k < h.length → Base h (exp k) (self (k+1))`。`Prec h := Relation.TransGen (Base h)`。
- `selfIdentity : Framework Node`: `preds = {isSelf} ∪ {(· = exp k) | k : ℕ}`。
- `stageFramework : Framework Node := Framework.discrete`（時間的に展開した枠組み）。

## 3. 命題

**AC1 純粋経験の主客未分**
(a) 任意の `x y : D` について `pure.Same x y`。特に `pure.Same (inl S) (inr e)`。
(b) `pure.Obj` は高々一点（`Subsingleton`）。

**AC2 評価による主客の分化**
任意の `S`, `e` について `¬ (evaluated S).Same (inl S) (inr e)`。

**AC3 枠組み相対性**
(a) 同じ `S`, `e` について `pure.Same (inl S) (inr e) ∧ ¬ (evaluated S).Same (inl S) (inr e)`。
(b) どの枠組み `F` の中でも `¬ (F.Same x y ∧ ¬ F.Same x y)`。

**AC4 全く新しいもの**
(a) `S.IsNew e ↔ S.eval e = ∅`。
(b) `S.IsNew e → S.IsNew e' → (evaluated S).Same (inr e) (inr e')`。評価後の枠組みでは、全く新しい経験どうしは区別されない。

**AC5 取り込み（作られたもの）**
(a) `e ∈ (M.incorporate S e).experiences`。`S.experiences` の要素はすべて `(M.incorporate S e).experiences` に残る。
(b) `(M.incorporate S e).Classifies e`。
(c) `S.Classifies e' → (M.incorporate S e).Classifies e'`。
(d) `S.IsNew e → M.generate S e ∉ S.categories`（生成された範疇は、それまでの認識体系にない）。
(e) `e' ∉ M.generate S e → ¬ (evaluated (M.incorporate S e)).Same (inr e) (inr e')`（取り込み後の枠組みは、`e` を、生成された範疇に入らない経験から区別する）。

**AC6 評価済みの情報だけでは、新しいものを取り込み分けられない（純粋経験を経由する）**
(a) `FactorsThroughEval inc → S.IsNew e → S.IsNew e' → inc S e = inc S e'`。
(b) `S.IsNew e → S.IsNew e' → M.generate S e ≠ M.generate S e' → ¬ FactorsThroughEval M.incorporate`。
(c) `e ≠ e' → singletonMaking.generate S e ≠ singletonMaking.generate S e'`（(b) の仮定を満たす作る働きがある）。

**AC7 互いに先立つ（枠組み相対）**
`h : List E` を過去、`n = h.length` とする。
(a) 根拠: `k < n` のとき `M.run S₀ (h.take (k+1)) = M.incorporate (M.run S₀ (h.take k)) h[k]`、かつ `h[k] ∈ (M.run S₀ (h.take (k+1))).experiences`。
(b) 時間的展開では、先行は厳密である: `¬ Prec h x x`、`Prec h x y → ¬ Prec h y x`。
(c) 時間的に展開した枠組みでは、互いに先立つことはない: 任意の `x y` で `¬ stageFramework.Mutual (Prec h) x y`。
(d) 自己同一の枠組みが同一視するのは自己どうしだけである: `selfIdentity.Same (self k) (self m)`、`¬ selfIdentity.Same (self k) (exp m)`、`k ≠ m → ¬ selfIdentity.Same (exp k) (exp m)`。
(e) 自己同一の枠組みでは、自己と経験は互いに先立つ: `k < n → selfIdentity.Mutual (Base h) (self 0) (exp k)`。
(f) 自己同一の枠組みでは、自己は自己に先立つ: `0 < n → selfIdentity.Lift (Prec h) (selfIdentity.obj (self 0)) (selfIdentity.obj (self 0))`。
(g) 通常の先行関係（非対称な関係 `R`）では、互いに先立つことはない: `(∀ a b, R a b → ¬ R b a) → ¬ (R a b ∧ R b a)`。

**AC8 非完結性**
`M.IsOpen S₀` のとき:
(a) `M.Reachable S₀ S` なら、ある `e` について `M.Reachable S₀ (M.incorporate S e)`、`S.IsNew e`、`(M.incorporate S e).Classifies e`、`M.generate S e ∉ S.categories`。
(b) すべての経験を分類する到達可能な自己はない: `¬ ∃ S, M.Reachable S₀ S ∧ ∀ e, S.Classifies e`。
(c) 非空虚性: `E` が無限なら `singletonMaking.IsOpen Self.empty`。

**AC9 作る働きは、あらかじめ固定した `next` ではない**
`S.IsNew e`、`S.IsNew e'`、`M.incorporate S e ≠ M.incorporate S e'` なら、任意の `F : Self E → Self E` について `¬ ∀ x, S.IsNew x → M.incorporate S x = F S`。

**AC10 一つの枠組みにとどまると、生成は止まる（T14 との対応）**
(a) 純粋経験の枠組みにとどまる場合: `pure.Same (inl S) (inl (M.incorporate S e))`。作られた自己と、その前の自己は区別されない（AC1(b) により、この枠組みでは全体が一つである）。
(b) 評価後の枠組みにとどまる場合: AC6(a)。
(c) 可能な範疇があらかじめ有限: 有限集合 `C : Finset (Set E)` について `∀ S, M.Reachable S₀ S → ∀ e, M.generate S e ∈ C` なら `¬ M.IsOpen S₀`。

## 4. T14 の論証との対応（記録）

| T14 の段階（`author_position_jp.md`） | 本形式化での対応 |
|---|---|
| 2. 古典論理で読むと、矛盾は爆発する | AC3(b)、AC7(g): 一つの枠組みの中では、同一とその否定、互いに先立つことは成り立たない |
| 3. 矛盾を final とすると、自己同一は固定し、生成が止まる | AC10(a): 純粋経験の枠組みにとどまると、全体が一つになり、作られた自己を区別できない |
| 4. 矛盾はその水準で真だが final でない | AC3(a)、AC7(c)(e): 矛盾した文は一つの枠組みで真、別の枠組みで偽。生成は枠組みの間の移行（AC5、AC6）として表される |
| 5. つねに次の水準が生成されうる（可能無限） | AC8、AC10(c) |

## 5. 言えないこと

- 純粋経験が実在すること、人間の自己が実際にこのように作られることは示さない。示すのは、著者の記述を M1–M7 で読んだとき、それらが一つのモデルで同時に成り立つこと、そして一つの枠組みにとどまる読みでは何が成り立たなくなるかである。
- M1（識別できないものを同一とする）はモデル化上の選択である。AC1 はこの定義からほぼ直接に従う。内容は AC1–AC10 の組み合わせにある。
- Lean では型があらかじめ固定される。「まだ存在しない可能性の生成」は、外から来る経験への依存と ∀∃ の形（M7）でしか表していない。AC10(c) が排除するのは有限の固定された可能性空間だけで、無限の固定された可能性空間と可能無限は区別できない。
- AC7 の `Base h` は、段階の構造（`h.length`）から定義した。動力学（`run`）との対応は AC7(a) で確認するが、先行関係そのものは定義による。
- 数学的に新しい定理はない。すべて初等的である。
