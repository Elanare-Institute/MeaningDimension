# 数学的検証報告（Lean 4）

作成日: 2026-10-11。役割変更（`strategy_delta.md` S10）後の最初の報告。**論文用の文章ではない。** 著者と ChatGPT が論文に取り込むかどうかを判断するための、数学的な検証の記録である。

## 0. 共通事項

| 項目 | 内容 |
|---|---|
| Lean ソース | `MeaningDimension/`。最終変更 commit `54dc740`（以後 `.lean` の変更なし） |
| 検証 | `scripts/check_proofs.sh`（禁止構文の検査、`lake build`、`Tests/Spec.lean` の48件の仕様テスト、全宣言の公理監査、環境記録）。2026-10-11 に再実行し **ALL CHECKS PASSED** |
| 依存公理 | 監査対象の81定数すべてが `[propext, Classical.choice, Quot.sound]` の部分集合（Lean 標準）。`sorry`・独自の `axiom`・`native_decide` なし |
| 外部ライブラリ | FormalizedFormalLogic/Foundation `dfaa003d0c4533c89ca72ae513d9c055fd3fe7bf`、Mathlib `5ed2965256430c3649e86755f9576b54eca72435`、Lean 4.34.0 |
| 記法 | `T.Δ₁`: T の公理集合の、IΣ₁ で証明可能に Δ₁ な表示（データ）。`Con_T`（Lean: `T.consistent`）: その表示から作った無矛盾性文。`T.Con = {Con_T}`、`T.Incon = {¬Con_T}`。`T ⪯ U`: T の定理はすべて U の定理。`T ⪱ U`: `T ⪯ U` かつ `U ⪯ T` でない。`T ≊ U`: 相互に ⪯。Σ₁ 健全（`SoundOnHierarchy 𝚺 1`）: 証明できる Σ₁ 文はすべて ℕ で真。`ℕ ⊧* T`: T の公理はすべて ℕ で真 |
| 新規性の総括 | **以下の証明済み命題に、数学的に新しい定理はない。** すべて既知の定理、その系、または初等的事実である（`lean_inventory_audit.md`） |

## A. 証明済みの命題

### A1. 一段の非完結性（Gödel II）
1. **命題**: T が `[T.Δ₁]`、`𝗜𝚺₁ ⪯ T`、無矛盾のとき、(a) `T ⊬ Con_T`、(b) `T ⪱ T ∪ {Con_T}`。
2. **Lean**: `MeaningDimension.Godel.G1_unprovable`, `G1_strict`（`MeaningDimension/Godel/EffectiveAscent.lean`）。
3. **状態**: 証明済み（Foundation の定理の再掲）。
4. **依存**: 標準3公理。Foundation `consistent_unprovable` と、`T ⪱ T + T.Con` のインスタンス。
5. **新規性**: なし（Gödel の第二不完全性定理）。
6. **言えないこと**: `Con_T` は選んだ Δ₁ 表示に依存する。他の表示の無矛盾性文や、Σ₁ だが IΣ₁ で証明可能に Δ₁ でない表示（Feferman の α* など）については何も言わない。

### A2. Σ₁ 健全性の伝播
1. **命題**: 段階 S（理論と Δ₁ 表示の組）が `𝗜𝚺₁ ⪯ S` かつ Σ₁ 健全なら、`S ∪ {Con_S}` も Σ₁ 健全。
2. **Lean**: `Godel.Stage.sigma1Sound_next`（`EffectiveAscent.lean`）。証明: 演繹定理で `S ⊢ Con_S → σ`、これは Σ₁ 文なので ℕ で真、`Con_S` も ℕ で真（S は無矛盾）。
3. **状態**: 証明済み。
4. **依存**: 標準3公理。Foundation `deduction_iff`, `standard_consistent`, 健全性。
5. **新規性**: なし（標準的な事実）。
6. **言えないこと**: 無矛盾性だけでは伝播しない（A4）。Σ₁ 健全性が上昇の継続に**必要**かどうかは示していない（C1）。

### A3. 有限上昇の非完結性
1. **命題**: `T₀ = T`、`Tₙ₊₁ = Tₙ ∪ {Con(Tₙ)}`（各段階の表示は Foundation の和集合表示）。T が `[T.Δ₁]`、`𝗜𝚺₁ ⪯ T`、Σ₁ 健全なら、すべての n で: `𝗜𝚺₁ ⪯ Tₙ`、Tₙ は Σ₁ 健全かつ無矛盾、`Tₙ ⊬ Con(Tₙ)`、`Tₙ ⪱ Tₙ₊₁`。さらに `m < n → Tₘ ⪱ Tₙ`。
2. **Lean**: `Godel.ascent`, `ISigma1_le_ascent`, `sigma1Sound_ascent`, `consistent_ascent`, `G2_unprovable`, `G2_strict`, `G2_strict_of_lt`（`EffectiveAscent.lean`）。仕様テストで IΣ₁ と PA に実例化。
3. **状態**: 証明済み。
4. **依存**: 標準3公理。Foundation。
5. **新規性**: なし（既知の系）。
6. **言えないこと**: 列 `ascent T : ℕ → Stage` は T から**全段階が事前に定まる**関数であり、各段階の表示も固定されている。ω 段階以降、超限の進行については何も言わない（A5 は別定理）。

### A4. 無矛盾性だけでは上昇が続かない（反例）
1. **命題**: T が `[T.Δ₁]`、`𝗜𝚺₁ ⪯ T`、無矛盾のとき、(a) `T ∪ {¬Con_T}` は無矛盾、(b) その次の段階 `(T ∪ {¬Con_T}) ∪ {Con(T ∪ {¬Con_T})}` は矛盾、(c) `T ∪ {¬Con_T}` は Σ₁ 健全でない。
2. **Lean**: `Godel.consistent_union_incon`, `inconsistent_next_of_union_incon`, `not_sigma1Sound_union_incon`（`EffectiveAscent.lean`）。
3. **状態**: 証明済み。「無矛盾性があれば上昇は2段続く」の**反例**。
4. **依存**: 標準3公理。Foundation `height_union_incon_eq_one`。
5. **新規性**: なし（既知、PA + ¬Con(PA) の古典的な例）。
6. **言えないこと**: 無矛盾だが Σ₁ 健全でない理論の**すべて**で上昇が止まるとは言わない（C1）。

### A5. ω 段階
1. **命題**: T が `[T.Δ₁]`、`𝗜𝚺₁ ⪯ T`、`ℕ ⊧* T` のとき、`T.Conω = {¬□_Tⁿ⊥ | n}` について、Δ₁ 表示をもつ Π₁（冠頭）文の集合 U が存在して、`T ∪ T.Conω ≊ T ∪ U`、`T ∪ U ⊬ Con(T ∪ U)`、`T ∪ U ⪱ (T ∪ U) ∪ {Con(T ∪ U)}`、`T ∪ T.Conω ⪱ (T ∪ U) ∪ {Con(T ∪ U)}`。補題: Σ₁ 健全なら `ℕ ⊧ ¬□_Tⁿ⊥`（全 n）。`ℕ ⊧* T` なら全段階と `⋃ₙ Tₙ` も ℕ で真。
2. **Lean**: `Godel.G3`, `models_conItr`, `models_Conω`, `models_turingOmega`, `models_ascent`, `models_iUnion_ascent`（`MeaningDimension/Godel/LimitStage.lean`）。
3. **状態**: 証明済み。
4. **依存**: 標準3公理。Foundation `exists_prenex_axiomatization_turingOmega`, `models_boxBot_iff`, `height_eq_top_of_sigma1_sound`。
5. **新規性**: なし（既知の系）。
6. **言えないこと**: 仮定 `ℕ ⊧* T` は Σ₁ 健全性より強く、過剰な可能性がある（B1）。`T ∪ T.Conω` と有限段階の合併 `⋃ₙ Tₙ` の同一視は**未証明**（B2）。`Con(T ∪ U)` は Foundation が構成した U の表示に依存する。

### A6. 適格な段階に最終段階はない
1. **命題**: `Eligible S :⇔ 𝗜𝚺₁ ⪯ S ∧ S は Σ₁ 健全`、`ProperExtension S S' :⇔ S ⪱ S'`（本プロジェクトの定義）。(a) 適格な S には、適格な真の拡張 S' がある（`S' = S ∪ {Con_S}`）。(b) 反復も適格で、S を真に拡張する。(c) ℕ で真な文をすべて証明する適格な段階はない。(d) `Con(Tₙ)` は段階 n+1 で証明される。
2. **Lean**: `Godel.G4`, `Eligible.next`, `Eligible.iterate_next`, `Eligible.properExtension_iterate_next`, `not_exists_eligible_proves_all_truths`, `consistency_proved_later`（`MeaningDimension/Godel/NonFinality.lean`）。
3. **状態**: 証明済み。
4. **依存**: 標準3公理。A1, A2。
5. **新規性**: 定義は本プロジェクトのもの。内容は既知。
6. **言えないこと**: (c) は「ある一段階ですべて」の否定にとどまる。「各真文について、いつかの段階で証明される」（Turing–Feferman）は形式化していない（B7）。証人 S' は S から計算で決まる。

### A7. 同じ一階文が二つの構造で異なる真理値をとる
1. **命題**: ℒₒᵣ の文 `∃x (x·x + 1 = 0)` は ℝ で偽、ℂ で真。`Th(ℝ) ⊄ Th(ℂ)`（Th は ℒₒᵣ 文の集合）。
2. **Lean**: `ComplexNumbers.real_not_models_rootSentence`, `complex_models_rootSentence`, `theoryOf_real_not_subset_complex`（`MeaningDimension/Examples/ComplexNumbers.lean`）。
3. **状態**: 証明済み。
4. **依存**: 標準3公理。Mathlib（ℝ, ℂ）、Foundation の意味論。ℂ の順序は Mathlib の `ComplexOrder`（文は順序を使わない）。
5. **新規性**: なし。
6. **言えないこと**: ある構造で φ と ¬φ が同時に成り立つことは示さない（A8 により不可能）。ℝ から ℂ への移行は、同じ文を別の構造で評価することであり、理論の単調な拡張ではない。

### A8. 同じ解釈のもとでの不可能性（no-go）
1. **命題**: (a) `T ⪯ U`、U が無矛盾、`T ⊢ ¬φ` なら `U ⊬ φ`。(b) `T ⪯ U`、`M ⊧* U`、`T ⊢ ¬φ` なら `M ⊭ φ`。(c) どの構造も φ と ¬φ を同時には充足しない。
2. **Lean**: `unprovable_of_refuted`, `not_models_of_refuted`, `not_models_and_models_neg`（`MeaningDimension/Logic/TheoryExtensions.lean`）。
3. **状態**: 証明済み。
4. **依存**: 標準3公理。Foundation。
5. **新規性**: なし（初等的）。
6. **言えないこと**: 古典論理・同じ言語・同じ解釈の範囲の結果。矛盾許容論理、言語や解釈の変更については何も言わない。

### A9. 理論の単調性
1. **命題**: `T ⊆ U` かつ `T ⊢ φ` なら `U ⊢ φ`。
2. **Lean**: `provable_mono`（`TheoryExtensions.lean`）、`Stage.subset_next`, `Stage.le_next`（`EffectiveAscent.lean`）。
3. **状態**: 証明済み。
4. **依存**: 標準3公理。Foundation。
5. **新規性**: なし。
6. **言えないこと**: —

### A10. 撤回済みの研究: D1–D3 は無矛盾性文を決めない（made-canonicity は再導入しない）
1. **命題**: 抽象的な provability 述語 □ が D1–D3（Foundation の `HBL`）を満たすなら、任意の文 π について `□'σ := □σ ∨ π` も D1–D3 を満たし、`Con' ↔ Con ∧ ¬π`。算術版（T が `[T.Δ₁]`、`𝗜𝚺₁ ⪯ T`、Σ₁ 健全、`π := □_T(¬Con_T)`）: `□'σ` は Σ₁ 文、ℕ で `□'σ ↔ T ⊢ σ`、`T ⊬ Con → Con'`、`T ⊢ Con' → Con`、`T ⊬ Con'`。
2. **Lean**: `MadeCanonicity.disjProv`, `disj_HBL2`, `disj_HBL3`, `disj_HBL`, `disj_con_iff`, `standard_disj_sigma1`, `standard_disj_models_iff`, `standard_disj_con_not_implied`, `standard_disj_con_implies`, `standard_disj_con_unprovable`（`MeaningDimension/Godel/MadeCanonicity.lean`）。
3. **状態**: 証明済み。撤回済みの研究として保存（`retired_made_canonicity.md`）。
4. **依存**: 標準3公理。Foundation `formalized_unprovable_not_con`（Löb）、`con_unprovable`。
5. **新規性**: 初等的。新規性は主張しない。
6. **言えないこと**: 対応する公理表示 α' の算術化は未形式化（B4）。

## B. 未解決（Lean で未証明）

| ID | 命題 | 状態 | ブロッカー |
|---|---|---|---|
| B1 | A5（ω 段階）を、`ℕ ⊧* T` ではなく Σ₁ 健全性の仮定で証明する。方針: Σ₁ 健全な T に真の Π₁ 文を有限個加えても Σ₁ 健全（A2 と同じ議論）なので、コンパクト性で `T ∪ T.Conω` が Σ₁ 健全、ゆえに無矛盾 | 未解決 | 有限部分の扱い（`Compact`）。見積り小〜中 |
| B2 | `⋃ₙ Tₙ ≊ T ∪ T.Conω` | 未解決 | 形式化された演繹定理 `𝗜𝚺₁ ⊢ □_{T∪{φ}}ψ ↔ □_T(φ → ψ)`。見積り中 |
| B3 | `⋃ₙ Tₙ` が実効的（Δ₁ 表示をもつ）こと、および実効的な合併の不完全性 | 未解決 | `n ↦ ⌜Con(Tₙ)⌝` の計算可能性。見積り大 |
| B4 | 撤回済み研究の残り: 表示 α' の算術化 | 未解決（優先度低） | Σ₁ 表示の provability の形式化 |
| B5 | 撤回済み研究の残り: `Pr ∨ ¬RFN_Σ₁(T)` が T 上で Σ₁ と同値でないこと | 未解決（紙上の証明のみ。優先度低） | 一様 Σ₁ 反映の形式化 |
| B6 | Feferman の α*（非有界版） | 未解決 | Foundation の `Theory.Δ₁` では表現できない。抽象層での形式化が必要 |
| B7 | Turing–Feferman の超限進行（各真文が、ある経路のある段階で証明される） | 未着手 | 順序数記法と反映原理の形式化。別プロジェクト規模 |

## C. 追加検証の候補（意味次元生成と Gödelian non-closure の形式的対応に関わるもの）

**いずれも未実装。** 実装は、著者と ChatGPT から具体的な仕様を受け取ってから行う。ここでは数学的な内容と、検証したときに言えること・言えないことだけを書く。

### C1. 上昇が止まらないための最小の仮定（A3 の仮定の過剰性の検討）
- **命題（候補）**: 無矛盾な T について、すべての有限段階 Tₙ が無矛盾であることは、ω 段階 `T ∪ T.Conω` が無矛盾であることと同値（コンパクト性と B2 による）。Σ₁ 健全性はこの十分条件だが、**必要条件ではない可能性が高い**。
- **反例候補（未検証）**: 例えば `T = PA + ¬Con(ZFC)` は（ZFC が無矛盾なら）Σ₁ 健全でない。紙上の推論では、少なくとも `T + Con(T)` は（ZFC が無矛盾なら）無矛盾になる。全段階が無矛盾かどうかは未検証。
- **状態**: 未着手。前半は B2 に依存する。
- **新規性**: 既知と思われる。
- **言えないこと**: どの性質が上昇の継続に「本質的」かという哲学的な判断は含まない。

### C2. 表示に依存しない非完結性と、表示に依存する内容
- **命題（候補）**: (a) T のどの Δ₁ 表示 p についても `T ⪱ T ∪ {Con_p}`。(b) 同じ T の二つの Δ₁ 表示 p, q で、`T ⊬ Con_p ↔ Con_q` となるものがある。
- **状態**: (a) は A1 の `G1_strict` が任意の表示インスタンスについて述べられているので、**実質的に証明済み**。明示的な定理として述べ直すのは容易。(b) は表示のレベルでは未証明（provability 述語のレベルでは A10 が類似の事実を示す）。
- **新規性**: (a) は既知。(b) は既知の現象（Feferman 1960）の Δ₁ 版。
- **言えないこと**: どの表示が「正しい」かは何も言わない。

### C3. 「無限に拡張可能」と「すべての問いにいつか到達」の非同値
- **命題（候補）**: (a) 抽象版: 真に増大する集合の列で、合併にも入らない元があるもの（自明）。(b) 算術版: どの有限段階 Tₙ も、ω 段階の無矛盾性文 `Con(T ∪ U)` を証明しない（A5 と B2 から従う）。
- **状態**: 未着手。(b) は B2 に依存する。
- **新規性**: なし。
- **言えないこと**: 事前に決まった一つの列についての結果であり、生成一般についての主張ではない。

### C4. 単調な拡張と、構造の取り替え
- **既存の結果**: 単調な例は `Stage.subset_next`（A3、A9）。構造を取り替える例は `theoryOf_real_not_subset_complex`（A7）。
- **候補**: 両者を区別する一般的な形式的定義（例えば「`T ⪯ T'`」と「`Th(M) ⊄ Th(M')`」）。
- **状態**: 一般的な定義は未着手。仕様が必要。
- **言えないこと**: Lean には「意味次元生成」の定義はない。どちらの例が意味次元生成に当たるかは、著者の哲学による判断である（著者は非単調性を必要条件にしないと決めている）。

### C5. 文の四状態（原稿の表1）
- **命題（候補）**: T に対して provable / refutable / undecidable / contradictory を定義すると、四つは互いに排反で網羅的。古典的な T では「contradictory な文がある」⇔「T が矛盾」。
- **状態**: 未着手（初等的）。
- **言えないこと**: door の分類（哲学的分類）は形式化しない。

### C6. 要求を加えた理論の矛盾
- **命題（候補）**: 古典論理では `T ∪ {φ}` が矛盾 ⇔ `T ⊢ ¬φ`。
- **状態**: Foundation に同等の定理がある（再掲は容易）。
- **言えないこと**: 生成的真矛盾主義の定義の読み方（J2・J3）は著者と ChatGPT が決める。この命題はどの読みを採るかを決めない。

### C7. 解釈の更新の玩具モデル
- **候補**: 出来事の時点・解釈の時点・解釈の枠組みをもつ型と、解釈の更新を（関数ではなく）関係として与えるモデル。
- **状態**: 未着手。仕様が必要。
- **言えないこと**: 作れるのはモデルであり、過去の再構成についての著者の哲学を証明するものではない。

### C8. Turing–Feferman の超限進行
- B7 と同じ。別プロジェクト規模。

## D. 証明結果からは言えないこと（全体）

1. 意味次元生成、生成的可能無限、生成的真矛盾主義、いまによる未来の創発、意味の遡及は、どれも Lean では定義も証明もしていない。
2. A3・A6 の上昇は、固定した言語・固定した標準模型での、事前に定まった単調な手続きである。
3. Lean の結果は Foundation の枠組み（IΣ₁ で証明可能に Δ₁ な表示）の範囲のものである。
4. 数学的に新しい定理はない。
