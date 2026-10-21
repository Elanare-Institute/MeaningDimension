# 数学的検証報告（Lean 4）

作成日: 2026-10-11。役割変更（`strategy_delta.md` S10）後の最初の報告。**論文用の文章ではない。** 著者と ChatGPT が論文に取り込むかどうかを判断するための、数学的な検証の記録である。

## 0. 共通事項

| 項目 | 内容 |
|---|---|
| Lean ソース | `MeaningDimension/`。§A–D の対象は commit `54dc740` 以後変更なし。2026-10-19 に `MeaningDimension/ACSI/` を追加（§E）。2026-10-20 に `MeaningDimension/Godel/PresentationDependence.lean`（§G）、`MeaningDimension/Correspondence/`（§H）、`MeaningDimension/Generation/`（§I）を追加 |
| 検証 | `scripts/check_proofs.sh`（禁止構文の検査、`lake build`、`Tests/Spec.lean` の48件の仕様テスト、全宣言の公理監査、環境記録）。2026-10-11 に再実行し **ALL CHECKS PASSED**。2026-10-19 に `Tests/ACSISpec.lean` を加えて再実行し **ALL CHECKS PASSED**。2026-10-20 に `Tests/PresentationSpec.lean` を加えて再実行し **ALL CHECKS PASSED**（公理監査 259 定数）。同日 `Tests/CorrespondenceSpec.lean` を加えて再実行し **ALL CHECKS PASSED**（公理監査 357 定数）。同日 `Tests/MDGSpec.lean` を加えて再実行し **ALL CHECKS PASSED**（公理監査 455 定数）。同日、著者側の FB で §I を改訂して再実行し **ALL CHECKS PASSED**（公理監査 492 定数）。著者の決定 D8・D9 と MDG6(d) を加えて再実行し **ALL CHECKS PASSED**（公理監査 497 定数） |
| 依存公理 | 監査対象の81定数（2026-10-19 の監査では ACSI を含め226定数。自動生成の補助定数を含む）すべてが `[propext, Classical.choice, Quot.sound]` の部分集合（Lean 標準）。`sorry`・独自の `axiom`・`native_decide` なし |
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

## E. 絶対矛盾的自己同一（著者の定式化）の形式化（2026-10-19 追加）

Gödel 関係の形式化とは独立。仕様は `docs/acsi_spec.md`（実装前に固定）。対象は、著者が西田から抽出した定式化（2026-10-19）であり、西田本文への帰属ではない。

### E0. 共通事項

| 項目 | 内容 |
|---|---|
| 著者の選択 | 主客未分の矛盾は**枠組みによる**（一つの枠組みの中に φ ∧ ¬φ は現れない）。「経験は自己の土台」の矛盾は**互いに先立つ**。後者も枠組み相対で扱う（`acsi_spec.md` M6） |
| モデル化上の選択 | `acsi_spec.md` §1 の M1–M7（Claude による）。とくに M1: 枠組み = 評価述語の集合、枠組みでの同一 = どの述語でも区別されないこと |
| Lean | `MeaningDimension/ACSI/Framework.lean`、`SubjectObject.lean`、`Incorporation.lean`、`MutualPrecedence.lean` |
| 仕様テスト | `Tests/ACSISpec.lean`（AC1–AC10 の文言の書き起こしと、`ℕ`・`Bool`・`singletonMaking`・空の自己・過去 `[0, 1]` での非空虚性の確認） |
| 依存 | Mathlib のみ（Foundation は使わない）。公理は標準3公理の部分集合。`Classical.choice` を使うのは `not_isOpen_of_finite` と `singletonMaking_isOpen` だけで、ほかは `propext`・`Quot.sound` 以下、または公理なし |
| 矛盾許容論理 | 使わない |
| 新規性 | **なし。** すべて初等的 |

### E1. 証明済みの命題

| ID | 命題（要約） | Lean 名 | 状態 |
|---|---|---|---|
| AC1 | 評価述語のない枠組み（純粋経験）では、すべてが同一。自己と経験も同一（主客未分）。対象は高々一点 | `Framework.pure_same`, `pure_same_subject_object`, `Framework.instSubsingletonObjPure` | 証明済み |
| AC2 | 自己 S が評価した後の枠組みでは、自己と経験は区別される | `evaluated_not_same_subject_object` | 証明済み |
| AC3 | (a) 同じ自己と経験について、「自己＝経験」は純粋経験の枠組みで真、評価後の枠組みで偽。(b) 一つの枠組みの中では、同一とその否定は両立しない | `subjectObject_frameworkRelative`, `Framework.not_same_and_not_same` | 証明済み |
| AC4 | (a) 全く新しい ⇔ 評価が空。(b) 評価後の枠組みでは、全く新しい経験どうしは区別されない | `Self.isNew_iff_eval_eq_empty`, `evaluated_same_of_isNew` | 証明済み |
| AC5 | 取り込みで経験が蓄えられ、分類できるようになり、既存の分類は失われない。全く新しい経験から生成された範疇は、それまでの認識体系にない。取り込み後の枠組みは、その経験を、生成された範疇の外の経験から区別する | `Making.mem_incorporate_experiences`, `experiences_subset_incorporate`, `classifies_incorporate`, `classifies_incorporate_of_classifies`, `generate_notMem_of_isNew`, `evaluated_incorporate_not_same` | 証明済み |
| AC6 | 評価された結果だけに依存する取り込みは、全く新しい経験をすべて同じように取り込む。二つの新しい経験から異なる範疇を作る働きは、評価だけには依存しない。そのような働き（`singletonMaking`）はある | `FactorsThroughEval.eq_of_isNew`, `Making.not_factorsThroughEval`, `singletonMaking_generate_ne` | 証明済み |
| AC7 | 時間的に展開した過去では、先行は厳密（非反射・非対称）で、互いに先立つことはない。自己同一の枠組み（自己の段階を区別しない）では、自己と各経験は互いに先立ち、自己は自己に先立つ。この枠組みが同一視するのは自己どうしだけ。先行と取り込みの対応（`run`） | `prec_irrefl`, `prec_asymm`, `stageFramework_not_mutual`, `selfIdentity_mutual`, `selfIdentity_self_precedes_self`, `selfIdentity_same_self`, `selfIdentity_not_same_self_exp`, `selfIdentity_not_same_exp_exp`, `run_take_succ`, `getElem_mem_run_take_succ`, `not_mutual_of_asymm` | 証明済み |
| AC8 | 開放性（到達しうるどの自己にも全く新しい経験がある）のもとで、どの自己にも真に新しい範疇を生む次の取り込みがあり、すべてを分類する自己はない。経験が無限なら `singletonMaking` は開放的 | `IsOpen.exists_next`, `IsOpen.not_exists_final`, `singletonMaking_isOpen` | 証明済み |
| AC9 | 二つの新しい経験を異なる自己に取り込むなら、どんな `F : Self → Self` もその取り込みを事前に決めていない | `Making.not_predetermined` | 証明済み |
| AC10 | (a) 純粋経験の枠組みでは、作られた自己とその前の自己は区別されない。(b) 評価後の枠組みにとどまると AC6(a)。(c) 生成されうる範疇があらかじめ有限集合に収まるなら、開放性は成り立たない | `Making.pure_same_incorporate`, `Making.not_isOpen_of_finite` | 証明済み。(c) の仮定は `Bool` で充足を確認 |

### E2. T14 の論証との対応

`acsi_spec.md` §4 の表のとおり。T14 の 2（古典論理では爆発）は AC3(b)・AC7(g)、3（矛盾を final にすると生成が止まる）は AC10(a)、4（その水準で真だが final でない）は AC3(a)・AC7(c)(e) と AC5・AC6、5（可能無限）は AC8・AC10(c) に対応する。

### E3. 言えないこと

1. 純粋経験の実在や、人間の自己が実際にこう作られることは示さない。示したのは、著者の記述を M1–M7 で読んだとき、それらが一つのモデルで矛盾なく同時に成り立つこと、そして一つの枠組みにとどまる読みでは何が成り立たなくなるかである。
2. M1 はモデル化上の選択であり、AC1 はこの定義からほぼ直接に従う。AC9 も、仮定から一行で従う。
3. Lean では型があらかじめ固定される。「まだ存在しない可能性の生成」は、外から来る経験への依存と ∀∃ の形（M7）でしか表していない。AC10(c) が排除するのは有限の固定された可能性空間だけで、無限の固定された可能性空間と可能無限は区別できない。
4. AC7 の先行関係 `Base h` は、段階の構造から定義した。取り込みの動力学との対応は AC7(a) で確認したが、先行関係そのものは定義による。
5. 生成的真矛盾主義そのもの（§D.1）は、この形式化でも定義していない。著者の選択（枠組みによる）に従い、矛盾した文が枠組みごとに異なる真理値をとることと、枠組みの間の移行を形式化しただけである。

### E4. 先行研究の調査（2026-10-20）

著者の方針により、京都学派は調査対象から外した。対象は京都学派以外の研究と、京都学派以後の研究である。調べたのは英語・日本語の公開ウェブ情報（Web 検索と、公開されている抄録・本文）。

- **結論**: 絶対矛盾的自己同一（純粋経験から主客未分を経て自己が作られる構造を含む）を、形式体系上のモデルとして定式化した研究も、証明支援系で検証した研究も、見つからなかった。
- **もっとも近いもの**: Deguchi & Fujikawa, "Dialetheism in the Work of Nishida Kitarō," in Deguchi, Garfield, Priest & Sharf, *What Can't Be Said* (OUP, 2021), ch. 7。西田を真矛盾主義者として読む解釈で、自己は世界とも自己自身とも同一であり、かつ同一でない、とする。抄録とキーワードからは哲学的な解釈と判断されるが、本文は未確認なので、形式的な記法やモデルを使っているかは**未確定**。著者の GC 論文の注21で引用済み。この解釈は矛盾を一つの枠組みの中の真矛盾として扱っており、著者が選んだ読み（枠組みによる）とは異なる。**著者は、この真矛盾主義的な解釈を誤りとみなしている**（2026-10-20）。
- **形式化ではないもの**: Sawada & Takagi, *Open Philosophy* 8 (2025)（出口の Self-as-We との比較。本文は未確認）。Kozyra, *Japan Review* 20 (2008) など（形式論理による分析は誤りだと論じている）。西尾泰和のメモ（2017、不連続関数の片側極限による非形式的なアナロジー）。Lotman & Urai, *EJJP* 8 (2023)（無限と矛盾についての哲学的分析）。
- **隣接する前例**: Lawvere による、ヘーゲルの対立物の統一の圏論的な定式化（随伴）。対象は西田ではない（GC 論文の注45）。
- **調査の限界**: 有料の本文（OUP の章、Open Philosophy）は読めていない。CiNii・J-STAGE・PhilPapers を直接検索しておらず、日本語の書籍は確認できていない。見つからなかったことは、存在しないことの証明ではない。

## F. 対応表（(i)–(v)、別のチャットで作成）の検証（2026-10-20）

対象: 著者と ChatGPT が別のチャットで作った対応表（西田／generative schema／ゲーデルの5条件 (i)–(v)）。外部から受けた指摘（「(iv) の行は、ACSI の形式化のもとでは意味のある形で成り立たない」）とあわせて、本報告の命題に照らして検証した。論文用の文章ではない。

### F1. 行ごとの判定

| 条件 | ACSI の形式化（§E） | 表のゲーデル側 | 判定 |
|---|---|---|---|
| (i) e は S で記述不能 | AC4: e はどの範疇にも入らない | Con(T) は T で証明不能 | **要修正**。Con(T) は T の言語で記述**できる**（T 自身が指定する文）。「記述不能」と「証明不能」は別の性質である。Domain(S) を「S が証明・分類できるもの」と読めば一致する（A1(a)）が、その場合は (iv) と同じ事実になる |
| (ii) e を記述できる S' が生成可能 | AC5(b) | T' = T + Con(T) が構成可能 | 成り立つ（A1(b)、A3） |
| (iii) S ⊂ S' | AC5(a)(c)(d) | T ⊂ T' | 成り立つ（A1(b): `T ⪱ T ∪ {Con_T}`） |
| (iv) S → S' の移行は S 内で導出不能 | AC9（移行は段階だけから前もって決まらない）、AC6 | T ⊬ Con(T) | **成り立たない**（F2） |
| (v) 停止しない | AC8 | 同じ構造が再帰 | 成り立つ（A3、A6）。ただし前提が違う。AC8 は開放性の仮定、A3・A6 は Σ₁ 健全性の仮定のもとでの結果 |

### F2. (iv) が成り立たない理由

- 指摘のとおり、`T ↦ T ∪ {Con_T}` は T から計算で決まる移行である（A3、A6、D2）。どの文を加えるかは T の表示から計算でき、T の内部でも表現できる。T にできないのは、加える文 Con(T) を**証明すること**、つまり移行を T の内部で**正当化すること**である。
- 一方、ACSI の形式化で (iv) にあたるのは、移行が段階だけから**前もって決まっていない**こと（AC9）である。表の説明文「S の中にいる限り、S' がどうあるべきかは決まらない」も、この意味である。
- したがって (iv) は、どちらの意味で読んでも、片側に対応物がない。
  - 「前もって決まっていない」と読む場合: ACSI 側は AC9。ゲーデル側の有限段の Con 上昇には対応物がない。上昇は、AC9 が作る働きについて否定した `next` の一例である。
  - 「S の内部で正当化できない」と読む場合: ゲーデル側は A1（`T ⊬ Con_T`）。ACSI の形式化は正当化を扱っておらず、対応物がない。
- また、表のゲーデル側では (i) と (iv) が同じ事実（Con(T) の証明不能性）を指している。

### F3. 修正案 A（新しい証明は不要）

1. (i) を「S の中では得られない（証明・分類できない）」と読み、ゲーデル側を A1(a) とする。「記述不能」はゲーデル側には当てはまらない（言語は固定されている。D2）。
2. (iv) のゲーデル側を外し、「非予定性（AC9）には、ゲーデルの有限段の上昇の中に対応物がない」と明記する。`godel_boundary.md` B2 の「決定的な非類似」と同じ内容である。
3. 「構造的同型」という語には、形式的な裏づけがない。二つの側の間に、構造を保つ写像を定義していないからである。GC 論文 §4 も、同型ではないと明言している。**（追記 2026-10-20: (i)(ii)(iii)(v) の行に限って、構造を保つ写像を定義し、同型であることを §H で証明した。(iv) は同型に含まれない。）**

### F4. 修正案 B（Gödel 側に非予定性の対応物をつくる。**§G で証明済み**）

- **候補命題**: T が `[T.Δ₁]`（表示 α）、`𝗜𝚺₁ ⪯ T`、Σ₁ 健全のとき、**同じ公理集合 T** の別の Δ₁ 表示 β があって、`T ∪ {Con_α} ⪱ T ∪ {Con_β}`。したがって、次の段階「T ∪ {Con}」は理論（公理集合）だけからは決まらず、表示に依存する。理論の上の関数 `F` で、すべての表示についての次段階を与えるものはない（AC9 と同じ形。外からの入力にあたるのが、経験ではなく表示である）。
- **構成の見通し**: `β(x) :⇔ α(x) ∨ ∃p ≤ x (x = ⌜p̄ ≠ p̄⌝ ∧ Prf_α(p, ⌜¬Con_α⌝))`。存在量化が有界なので Δ₁ である。T が Σ₁ 健全なら ¬Con_α の証明は存在しないので、ℕ では α と同じ集合を定める。
  - `T ∪ {Con_β} ⊢ Con_α`: α ⊆ β が 𝗜𝚺₁ で証明できるので、`Con_β → Con_α`。
  - `T ∪ {Con_α} ⊬ Con_β`: 𝗜𝚺₁ ⊢ `Pr_α(¬Con_α) → Pr_β(⊥)` から、もし `T ∪ {Con_α} ⊢ Con_β` なら `T ⊢ Pr_α(Pr_α ⊥) → Pr_α ⊥`。Löb の定理により `T ⊢ Pr_α ⊥`。これは Σ₁ 健全性に反する。形式化された演繹定理（B の T2）は使わない。
- **Lean での見積り**: 中〜大。Foundation の算術化の上で β を半文として構成し、𝗜𝚺₁ で証明可能に Δ₁ であることと、`Pr_α(¬Con_α) → Pr_β(⊥)` の内部証明が必要である。Löb の定理は Foundation にある。
- **新規性**: なし（Feferman 1960 以来の、無矛盾性文の表示依存性の一例）。
- **言えないこと**: 段階を「表示された体系」とする場合（GC 論文 §4 の読み）、表示を固定すれば次段階はやはり前もって決まる。修正案 B が示すのは「理論だけからは決まらない」ことであり、「何によっても前もって決まっていない」ことではない。表示の選択が何に当たるかは、著者の哲学による判断である。

## G. 次段階の表示依存性（G5、2026-10-20 追加。§F の修正案 B）

仕様: `docs/presentation_spec.md`（実装前に固定）。Lean: `MeaningDimension/Godel/PresentationDependence.lean`。テスト: `Tests/PresentationSpec.lean`（仕様の文言の書き起こしと、𝗜𝚺₁・𝗣𝗔 での実例化）。

共通の前提: T が `[T.Δ₁]`（表示 α）、`𝗜𝚺₁ ⪯ T`、Σ₁ 健全。依存公理はすべて標準3公理（`propext`, `Classical.choice`, `Quot.sound`）。

### G1. 二つ目の表示 β
1. **命題**: T の公理集合の、もう一つの Δ₁ 表示 β（`twisted T`）がある。β の定義式は `α(x) ∨ ghost(x)`。`ghost(x)` は「`x = ⌜⊥ ⋏ ⊤ˢ⌝`（⊥ を ⊤ の s 個の連言で水増しした文）で、s が Σ₁ 文 `□_α(¬Con_α)` の証人（Δ₀ 母式の証人）であるような `s < x` がある」。
2. **Lean**: `twisted`, `ghostCh`, `ghostPresentation`, `IsGhost.defined`, `not_isGhost_nat`, `twisted_ch`, `mem_twisted_Δ₁Class`。
3. **状態**: 構成済み。`Theory.Δ₁` の型が要求する二条件（ℕ でちょうど T の公理を定めること、𝗜𝚺₁ で証明可能に Δ₁ であること）を満たす。
4. **依存**: Foundation の Craig の構成の部品（`qqVerums`, `qqAndDef`, `qqFalsumDef`）、`ISigma1.exists_matrix_provable`、`con_unrefutable`（ℕ に幽霊公理がないことに使う）。
5. **新規性**: なし。
6. **言えないこと**: β は人工的な表示である（「α が ¬Con_α を証明したら、⊥ を公理に加える」）。ℕ では α と同じ公理を定めるが、𝗜𝚺₁ はそのことを証明できない（証明できれば Con_α と Con_β が同値になり G4 に反する。この帰結自体は Lean の命題として述べていない）。

### G2. 鍵の補題
1. **命題**: `𝗜𝚺₁ ⊢ □_α(¬Con_α) → □_β ⊥`。
2. **Lean**: `provable_incon_imp_twisted_bot`（補助: `provable_twisted_bot_of_isGhost`, `provable_bot_of_mem_padded_falsum`）。
3. **状態**: 証明済み。𝗜𝚺₁ の任意のモデルの中で、証人 s から `⊥ ⋏ ⊤ˢ` が β の公理になり、内部の連言除去で `□_β ⊥` を得る。完全性定理で 𝗜𝚺₁ の定理にする。
4. **依存**: Foundation の内部の型付き証明（`TProof.byAxm`, `tprovable_iff_provable`）、`complete`。
5. **新規性**: なし。
6. **言えないこと**: 内部（形式化された）主張である。ℕ では `□_α(¬Con_α)` は偽である。

### G3. Con_β から Con_α が出る
1. **命題**: `𝗜𝚺₁ ⊢ Con_β → Con_α`。したがって `T ∪ {Con_β} ⊢ Con_α`。
2. **Lean**: `twistedCon_imp_con`, `provable_con_of_twistedCon`。
3. **状態**: 証明済み。
4. **依存**: Foundation `provable_standardProvability_imp_of_Δ₁Class_subset`（α の公理は β の公理）。
5. **新規性**: なし。

### G4. 逆は出ない
1. **命題**: `T ∪ {Con_α} ⊬ Con_β`。
2. **Lean**: `not_provable_twistedCon`。
3. **状態**: 証明済み。もし証明できれば、G2 と合わせて `T ⊢ Con_α → ¬□_α(¬Con_α)` となり、Foundation の `formalized_unprovable_not_con`（Löb の定理から従う）に反する。
4. **依存**: 演繹定理（メタレベル）、`formalized_unprovable_not_con`。形式化された演繹定理（B の T2）は使っていない。
5. **新規性**: なし。

### G5. 次の段階は真に異なる
1. **命題**: `T ∪ {Con_α} ⪱ T ∪ {Con_β}`。特に二つは同値でない。
2. **Lean**: `strict_twisted`, `not_equiv_twisted`。
3. **状態**: 証明済み（G3 と G4 から）。𝗜𝚺₁ と 𝗣𝗔 で実例化済み。
4. **新規性**: なし。

### G6. 次の段階は理論だけからは決まらない
1. **命題**: (a) 表示 `d₁ d₂ : T.Δ₁` で、`T ∪ {Con_{d₁}}` と `T ∪ {Con_{d₂}}` が同値でないものがある。(b) 任意の `F : ArithmeticTheory → ArithmeticTheory` について、`¬ ∀ d : T.Δ₁, F T ≊ T ∪ {Con_d}`。
2. **Lean**: `exists_presentations_not_equiv`, `not_function_of_theory`（`nextWith T d := T ∪ {Con_d}`）。
3. **状態**: 証明済み。𝗜𝚺₁ と 𝗣𝗔 で実例化済み。
4. **新規性**: なし（Feferman 1960 以来知られている、無矛盾性文の表示依存性の一例）。
5. **言えないこと**: 表示を固定すれば次の段階は決まる。G6 が示すのは「理論（公理集合）だけからは決まらない」ことであり、「何によっても前もって決まっていない」ことではない。

### G7. AC9 との形式上の比較（事実の記録。哲学的な判断はしない）

| | ACSI の AC9 | G6(b) |
|---|---|---|
| 主張の形 | 任意の `F : Self → Self` について `¬ ∀ x, S.IsNew x → incorporate S x = F S` | 任意の `F : Theory → Theory` について `¬ ∀ d, F T ≊ T ∪ {Con_d}` |
| 段階だけでは決まらない理由 | 次の自己は、外から来る新しい経験 x に依存する | 次の段階は、表示 d に依存する |
| 追加の入力の出どころ | 自己の外から来る（モデルの中では任意の経験） | β は T と α から構成される。G6 は二つの表示が**ありうる**ことを示し、どちらが選ばれるかは扱わない |
| 入力を固定した場合 | `incorporate S x` は決まる | `T ∪ {Con_d}` は決まる |
| 反復 | AC8 で、どの段階にも新しい経験がある | G5 は一段について。表示を段ごとに変える上昇は扱っていない |

表示の選び方を「外から来る経験」と同じように扱ってよいかは、著者が判断する（著者は結果を見て判断すると表明している。2026-10-20）。

### G8. 撤回済みの研究との関係（事実の記録）

撤回済みの made-canonicity 監査の M4–M5（`retired_made_canonicity.md`、台帳 M4–M5）は、述語 `□' := □_T ∨ □_T(¬Con_T)` を可証性述語のレベルで扱い、「対応する表示 α' との対応は非形式的」と記録していた。G5 の β はその表示のレベルでの一例にあたり、G2・G3 から `Con_β` は `Con_α ∧ ¬□_α(¬Con_α)` を含意する（逆向きは証明していない）。**G5 は made-canonicity を再導入するものではない。** 著者の承認なしに made-canonicity の研究を再開しないという方針（`strategy_delta.md`）は変わらない。

## H. ACSI とゲーデルの上昇の、部分的な構造同型（CR、2026-10-20 追加）

- 著者の問い:「ゲーデルとの構造的同型を部分的にでも示せる？」
- 仕様: `docs/correspondence_spec.md`（実装前に固定）。
- Lean: `MeaningDimension/Correspondence/Growth.lean`（抽象部分）、`MeaningDimension/Correspondence/ACSIGodel.lean`（両側の実例と同型）。
- テスト: `Tests/CorrespondenceSpec.lean`（仕様の文言の書き起こしと、`singletonMaking`・𝗜𝚺₁・𝗣𝗔 での実例化）。
- 依存公理はすべて標準3公理の部分集合。

**共通の構造（成長系）。** 成長系は四つのものからなる。

- 段階、項目、「段階で項目が成り立つ」、項目の取り込み。
- 公理は二つ。取り込んだ項目は成り立つ。それまで成り立っていた項目は成り立ち続ける。

二つの側の読みは次のとおり。

| | ACSI 側 | ゲーデル側 |
|---|---|---|
| 段階 | 自己 | 理論（公理集合） |
| 項目 | 経験 | 文 |
| 成り立つ | 分類できる | 証明できる |
| 取り込み | `incorporate`（作る働き M を固定） | `T ↦ T ∪ {σ}` |

- (i) の Domain(S) は「S が分類できるもの」と読む（§F3 修正案 A の 1）。
- 過去（有限の項目の列）が**新鮮**とは、各項目が、それを取り込む段階で成り立たないことをいう。
- 過去の**痕跡**は四つからなる。通る段階、取り込む項目、そのあいだの「成り立つ」、過去に沿った継起。
- **同型**は、段階どうしの全単射と項目どうしの全単射の組で、「成り立つ」と継起を保ち、かつ反映するもの。

### H1. 新鮮な過去の標準形
1. **命題**: 任意の成長系で、新鮮な過去 h について次が成り立つ。
   - (a) h の j 番目の項目が k 番目の段階で成り立つのは、ちょうど j < k のとき。
   - (b) `k ≤ h.length` なら、k 番目の段階で成り立つものがすべて m 番目の段階で成り立つのは、ちょうど k ≤ m のとき。
   - (c) h に重複はない。
   - (d) 段階はどれも異なる。
2. **Lean**: `Growth.Fresh.holds_iff`, `Fresh.le_iff`, `Fresh.nodup`, `Fresh.get_injective`, `Fresh.stages_injective`。
3. **状態**: 証明済み。
4. **依存**: 成長系の二つの公理と新鮮さだけ。
5. **新規性**: なし（初等的）。
6. **言えないこと**: —

### H2. 同じ長さの新鮮な痕跡は同型
1. **命題**:
   - 新鮮な痕跡は、その長さの標準の構造と同型である。標準の構造では、段階は 0…n、項目は 0…n−1、「j が k で成り立つ ⇔ j < k」、継起は「k が k を取り込んで k+1」。
   - したがって、任意の二つの成長系（異なってよい）で、同じ長さの新鮮な痕跡は同型である。同型は、k 番目の段階を k 番目の段階に、j 番目の項目を j 番目の項目に送る。
2. **Lean**: `Growth.Fresh.ofStd`, `Growth.traceIso`, `Growth.traceIso_stage`, `Growth.traceIso_item`。同型の型は `Incidence.Iso`（全単射 `≃` 二つと、保存かつ反映の二条件）。
3. **状態**: 証明済み。
4. **依存**: H1。
5. **新規性**: なし。
6. **言えないこと**: 痕跡の同型類は**長さだけで決まる**。これについては H5 の 1 を見よ。

### H3. 両側の新鮮な過去
1. **命題**:
   - (a) ゲーデル側。T が `[T.Δ₁]`、`𝗜𝚺₁ ⪯ T`、Σ₁ 健全のとき、過去 `[Con(T₀), …, Con(Tₙ₋₁)]`（A3 の上昇）は T からの新鮮な過去である。その k 番目の段階は `Tₖ` である。
   - (b) ACSI 側。開放性 `M.IsOpen S₀` のもとで、任意の n について、長さ n の新鮮な経験の過去がある。
2. **Lean**: `conPast`, `conPast_fresh`, `run_conPast`, `conPast_getElem`, `exists_fresh_of_isOpen`。
3. **状態**: 証明済み。(a) は 𝗜𝚺₁ と 𝗣𝗔 で、(b) は `singletonMaking : Making ℕ` と空の自己で実例化済み。
4. **依存**: (a) は各段の Gödel II（A3 の `G2_unprovable`）。(b) は AC8 と同じ議論。
5. **新規性**: なし。
6. **言えないこと**: ACSI 側の過去は、あらかじめ与えられていない（∀n∃h。`acsi_spec.md` M7）。ゲーデル側の過去は、T と n の関数である。

### H4. ACSI とゲーデルの痕跡の同型
1. **命題**:
   - (a) 任意の作る働き M、自己 S₀、S₀ からの新鮮な経験の過去 h について、その痕跡は、同じ長さのゲーデル側の痕跡と同型である。同型は、k 段階の自己を `Tₖ` に、j 番目の経験を `Con(Tⱼ)` に送る。
   - (b) 開放性のもとで、任意の n について、長さ n の新鮮な過去と (a) の同型がある。
2. **Lean**: `acsiGodelIso`, `acsiGodelIso_stage`, `acsiGodelIso_item`, `exists_acsiGodelIso`。
3. **状態**: 証明済み。
   - (b) は `singletonMaking`・空の自己と、𝗜𝚺₁・𝗣𝗔 で実例化した。
   - 具体的な過去 `[0, 1]` と 𝗣𝗔 でも実例化した。`[0, 1]` の後の自己は `T₂` に、経験 1 は `Con(T₁)` に送られる。
4. **依存**: H2、H3。
5. **新規性**: なし。
6. **言えないこと**: H5。

この同型が対応表のどの行を担うかは次のとおり。

| 行 | 同型が保つ内容 |
|---|---|
| (i) | k 番目の項目は k 番目の段階で成り立たない（新鮮さ。経験は分類できない ↔ Con(Tₖ) は Tₖ で証明できない） |
| (ii) | 継起（k 番目の段階が k 番目の項目を取り込んで k+1 番目の段階になる） |
| (iii) | 成り立つものは段階とともに真に増える（H1(b)。ゲーデル側では `Le` は `⪯` なので（`godelGrowth_le_iff`）、`Tₖ ⪯ Tₘ ⇔ k ≤ m`） |
| (v) | (b): どの長さでも同型がある |
| (iv) | **含まれない**（H6） |

### H5. 同型が言わないこと
1. **ゲーデルに固有の内容を区別しない。** H2 により、新鮮な痕跡の同型類は長さだけで決まる。したがって同型は、同じ長さの新鮮な過去のどの二つのあいだにも成り立つ。
   - 二つの ACSI の過去のあいだにも成り立つ。
   - Con ではない独立な文を加えていくゲーデル側の過去とのあいだにも成り立つ。
   - Con(T) が T 自身の指定する文であることと、それが証明できないこと（Gödel II）は、ゲーデル側の過去が新鮮であること（H3(a)）にだけ入っている。
   - H4 が示すのは「両者は、新鮮な成長過程として同じ形をもつ」ことである。「ACSI はゲーデルの上昇と同じものだ」とは言わない。
2. **保つのは、過去に沿った継起だけである。** 取り込み一般は保たない。たとえば j < k のとき、ゲーデル側では `Tₖ ∪ {Con(Tⱼ)} = Tₖ` となる（取り込み直しても何も変わらない）。ACSI 側の `incorporate` は、つねに経験を一つ多くもつ新しい自己を作る。この例は Lean では述べていない。
3. **捨てているもの。**
   - 段階と項目が何であるかを捨てている。
   - AC1–AC4、AC6、AC7、AC10（枠組み、主客未分、評価、互いに先立つこと）も捨てている。
   - AC7 の先行関係 `Base h` は過去の長さだけから定義されるので、同じ長さのどの痕跡にも共通する。これを対応とは主張しない。
4. **続く仮定は異なる。** ACSI 側は開放性、ゲーデル側は Σ₁ 健全性を仮定する（§F1 (v)）。
5. **有限の痕跡だけを扱う。** 無限の過程どうしの同型は述べない。
6. **(i) の「記述不能」は表していない**（§F1）。

### H6. (iv) の共通の形（同型には含めない）
1. **命題**:
   - (a) 抽象形。成長系の段階 s で「差し出される」項目 x、x' があり、それぞれを取り込んだ段階で成り立つものが異なるとする。このとき、段階の関数 F で、差し出されるどの項目についても次の段階（と成り立つものが同じ段階）を与えるものはない。
   - (b) ACSI 側。差し出される項目は全く新しい経験である。`singletonMaking` では、S にとって新しい e ≠ e' を取り込んだ自己は、分類できる経験が異なる。
   - (c) ゲーデル側。差し出される項目は、ある表示から作った T の無矛盾性文である（`conOffer`）。G5 の Con_α と Con_β を取り込んだ理論は同値でない（G5.5）。
2. **Lean**: `Growth.not_predetermined`, `acsi_not_equivalent`, `conOffer`, `conOffer_con`, `conOffer_twistedCon`, `godel_not_equivalent`, `godelGrowth_equivalent_iff`。
3. **状態**: 証明済み。(b) は空の自己と経験 0、1 で、(c) は 𝗣𝗔 で実例化済み。
4. **依存**: (a) は一行。(b) は AC5。(c) は G5.5。
5. **新規性**: なし。
6. **言えないこと**:
   - AC9 と G6(b) が**同じ抽象命題の実例**であることを示しただけである。痕跡の同型（H4）には含まれない。
   - 差し出される項目は両側で異なる。ACSI 側は外から来る全く新しい経験のすべて、ゲーデル側は T と表示から作る無矛盾性文である（§G7）。両者が対応するか、つまり表示の選び方を「外から来る経験」とみなせるかは、著者が判断する。

## I. 意味次元生成の三つの形（反転形・未決定形・細分形）と三者比較（MDG、2026-10-20 追加、同日改訂）

- 指示書: `../CLAUDE_CODE_MDG_INSTRUCTIONS.md`（著者の決定 D1–D7）。
- 仕様: `docs/mdg_spec.md`（実装前に固定。指示書からの調整 J1–J10 と、改訂 §6 を記録）。
- Lean: `MeaningDimension/Generation/`。
  - `Embedding.lean`: 埋め込み、反転文、MDG1（古い領域に制限した評価 `EvalOn` を含む）
  - `RingLanguage.lean`: 環の言語 `ℒᵣ`（`<` なし）
  - `Examples.lean`: MDG1(e)(g)、MDG2、MDG3
  - `Refinement.lean`: 細分、MDG6
  - `Godel.lean`: MDG4、MDG5
  - `Conjugate.lean`: MDG7
  - `Packing.lean`: MDG8（Kappa の梱包。§I11、2026-10-21 追加）
- テスト: `Tests/MDGSpec.lean`（仕様の文言の書き起こしと、`singletonMaking`・𝗜𝚺₁・𝗣𝗔 での実例化）。
- 依存公理はすべて標準3公理の部分集合。

**改訂（2026-10-20、著者側の FB による。仕様 §6）**:
- **名前**: 「矛盾の扉」「未決定性の扉」をやめ、**反転形**（偽→真）、**未決定形**（未決定→決定）、**細分形**（区別されない→区別される）と呼ぶ。Lean 名は `ReversalStep`（旧 `GenStep`）、`Settles`（旧 `UndecidedDoor`）、`RefineStep`。定義の中身は変えていない。
- **言語**: ℝ→ℂ の例で ℂ に部分順序 `ComplexOrder` を入れるのをやめた。数学の例（MDG1(e)・MDG2・MDG3）は、`<` を含まない環の言語 `ℒᵣ` で述べ直した。`<` を使うのは MDG7 だけである。
- **追加**: 古い領域に制限した文の保存（MDG1(f)(g)）と、J8 の読みでの細分形と未決定形の一致（MDG5(f)）。

**著者の決定（2026-10-20、FB の後）**:
- **D8**: ACSI を細分形と同一視しない。細分は ACSI の成長の一つの型である。
- **D9**: 選択（重要でない区別を同一視する）型の成長は、現在のモデルでは表していない。裏づけとして MDG6(d) を加えた。

**主な調整**（詳細は仕様 §1）:
- **J1**: 埋め込みは Foundation の `Tarski.Structure.Embedding`（`M ↪ₛ[L] M'`）をそのまま使う。
- **J2**（改訂）: 数学の例の言語は環の言語 `ℒᵣ`（`0, 1, +, ·, =`）。Foundation にないので、このプロジェクトで定義した。
- **J5**: 理論の「区別」は、証明可能な同値とする。
- **J6**: ℚ(√2) の代わりに ℤ√2 を使う。
- **J8**（指示書にない追加）: MDG5 の結論が J5 の読みに依存するかを確かめる。
- **J9**: 三つの形の名前。英語の説明文では "contradiction" を形の名前に使わない。
- **J10**: 古い領域に制限した評価 `EvalOn` は、相対化した論理式の真理条件を直接与える。

### I1. 前の段を壊さない（MDG1）
1. **命題**: 埋め込み Θ : M ↪ M' について、次が成り立つ。
   - (a) 量化子のない論理式は、M の元をパラメータに含めても、真理値が変わらない。
   - (b) 存在的な論理式は、M で真なら M' でも真。
   - (c) 全称的な論理式は、M' で真なら M でも真。
   - (d) 存在文は真から偽に反転しない。全称文は偽から真に反転しない。
   - (e) 全称文は、制限せずに評価すると真から偽に反転しうる。ℝ→ℂ で、全称文 `∼sentenceC`（∀x, x·x+1 ≠ 0）は ℝ で真、ℂ で偽。
   - (f) **古い領域に制限すれば、すべての論理式の真理値が保たれる。** 量化子をすべて Θ の像に制限して M' で評価すると、どの論理式も M での真理値と一致する。文については、M で真の文は真のまま、偽の文は偽のまま残る。
   - (g) ℝ→ℂ で、ℂ において次の二つが同時に成り立つ。
     - 古い領域 ℝ に制限した `∼sentenceC`（∀x ∈ ℝ, x·x+1 ≠ 0）は真（狭い読み）。
     - 制限しない `∼sentenceC` は偽（広い読み）。
2. **Lean**: `eval_iff_of_open`, `eval_of_isExistential`, `eval_of_isUniversal`, `models_of_isExistential`, `models_of_isUniversal`, `not_true_false_of_isExistential`, `not_flips_of_isUniversal`, `neg_sentenceC_isUniversal`, `neg_sentenceC_true_false`, `EvalOn`, `eval_iff_evalOn`, `models_iff_evalOn`, `realComplex_restricted_unrestricted`。
3. **状態**: 証明済み。
4. **依存**: (a) は Foundation の `Semiformula.eval_hom_iff_of_open`。(b)(c) は存在的・全称的な論理式（`IsExistential`, `IsUniversal`、J3）についての帰納法。(f) は論理式についての再帰で、項の値は Foundation の `HomClass.val_term`、関係記号は `EmbeddingClass.rel` による。
5. **新規性**: なし（モデル理論の標準的な事実。(f) は相対化の補題）。
6. **言えないこと**:
   - 指示書の注釈「新しい段は前の段の事実を一つも取り消さず」は、**制限せずに評価すると**、量化子のない事実と存在文についてだけ正しい。全称文の事実は取り消されうる（(e)、A7 の `Th(ℝ) ⊄ Th(ℂ)`）。
   - 古い領域に制限して評価すると、前の段の文はすべて保たれる（(f)）。取り消されるのは「ℝ がすべてだ」という読み、つまり古い文を新しい領域全体で評価し直したときの真理値である。
   - (f) はどの埋め込みでも成り立つ。反転形の一歩に特有の性質ではない。
   - (f) の制限先は埋め込み Θ の像であり、Θ の選び方による。埋め込みの一意性は扱っていない。
   - `EvalOn` は、相対化した論理式 φᴿ の真理条件を直接与えたものである。R を記号として加えた言語や、φᴿ そのもの（構文）は作っていない（J10）。

### I2. 数学の例は反転形の一歩である（MDG2）
1. **命題**: 次の三つは、いずれも `ReversalStep`（埋め込みがあり、かつ反転文がある）である。言語は環の言語 `ℒᵣ`。三つの反転文はいずれも存在文である。
   - (a) ℕ→ℤ: `∃x (x + 5 = 3)` が ℕ で偽、ℤ で真。
   - (b) ℚ→ℝ: `∃x (x · x = 2)` が ℚ で偽、ℝ で真。
   - (c) ℝ→ℂ: `∃x (x · x + 1 = 0)` が ℝ で偽、ℂ で真。
2. **Lean**: `ringLang`（記法 `ℒᵣ`）, `ringModel`, `ringEmbedding`, `natInt`, `ratReal`, `realComplex`, `sentenceZ`, `sentenceR`, `sentenceC`, `reversalStep_nat_int`, `reversalStep_rat_real`, `reversalStep_real_complex`, `sentenceZ_isExistential`, `sentenceR_isExistential`, `sentenceC_isExistential`。
3. **状態**: 証明済み。文は指示書のとおり（J4）。ℂ に順序は入れていない。
4. **依存**: Mathlib の `Nat.cast`, `Rat.cast`, `Complex.ofReal`, `irrational_sqrt_two`。
5. **新規性**: なし。
6. **言えないこと**: 意味次元生成が**起きた後の**構造の関係を述べるだけで、生成の過程は表さない。

### I3. 埋め込みの条件は必要である（MDG3）
1. **命題**:
   - ℂ から ℝ への `ℒᵣ` の埋め込みはない。
   - ℂ→ℝ にも反転文（`∼sentenceC`。ℂ で偽、ℝ で真）はある。
   - それでも、ℂ→ℝ は `ReversalStep` ではない。
2. **Lean**: `isEmpty_complex_real`, `flips_complex_real`, `not_reversalStep_complex_real`。
3. **状態**: 証明済み。
4. **依存**: MDG1(b)。埋め込みがあれば、ℂ で真の存在文 `sentenceC` が ℝ でも真になり、ℝ で x·x+1 ≠ 0 であることに反する。
5. **新規性**: なし。
6. **言えないこと**: —

### I4. ゲーデルの上昇は反転形を通らず、未決定形を通る（MDG4）
1. **命題**:
   - (a) `T ⪯ T'` で T' が無矛盾なら、T で反証された文を T' は証明しない（理論の反転 `TheoryFlip` はない）。
   - (b) A3 の上昇（T は `[T.Δ₁]`、`𝗜𝚺₁ ⪯ T`、Σ₁ 健全）のどの段 Tₙ→Tₙ₊₁ にも、理論の反転はない。
   - (c) 各段は未決定形の一歩である（`Settles`）。`Con(Tₙ)` は Tₙ で証明も反証もできず、Tₙ₊₁ で証明できる。
2. **Lean**: `TheoryFlip`, `Settles`, `not_theoryFlip`, `ascent_not_theoryFlip`, `ascent_settles`。
3. **状態**: 証明済み。𝗜𝚺₁ と 𝗣𝗔 で実例化済み。
4. **依存**: (a) は A8(a)。(b) は A3（各段の無矛盾性）。(c) は A3 の `G2_unprovable`、Foundation の `con_unrefutable`（各段の Σ₁ 健全性、A2 を使う）。
5. **新規性**: なし。
6. **言えないこと**: 構造のあいだの反転（`Flips`）と理論のあいだの反転（`TheoryFlip`）は別の定義である。ゲーデルの上昇を構造の側から見ること（たとえば各段の模型）はしていない。

### I5. ゲーデルの上昇と細分形（MDG5）
1. **命題**:
   - (a) `T ⪯ T'` なら、T で証明可能な同値は T' でも証明可能。
   - (b) 理論の枠組み `provFramework T`（評価述語は「θ と証明可能に同値」）での同一は、T での証明可能な同値と一致する。
   - (c) `T ⪯ T'` なら、この枠組みで区別の反転はなく、`RefineStep` でない。
   - (d) A3 の上昇のどの段も、この枠組みでは `RefineStep` でない。
   - (e) **（J8。読みへの依存）** 上昇の累積の枠組み `ascentFramework T n`（評価述語は「k ≤ n の各段 Tₖ で証明できる」）では、A3 の仮定のもとで、**どの段も `RefineStep` である**。反転する対は `Con(Tₙ)` と `∼Con(Tₙ)` で、T₀…Tₙ のどれでも証明できず、Tₙ₊₁ では一方だけが証明できる。
   - (f) **（J8 での細分形と未決定形の一致）** 同じ仮定のもとで、どの段 n についても次が成り立つ。
     - Tₙ₊₁ が σ を決めるなら（`Settles Tₙ Tₙ₊₁ σ`）、σ と ∼σ は段 n では区別されず、段 n+1 で区別される。
     - 逆に、段 n+1 で初めて区別される対があれば、その一方は Tₙ で未決定で、Tₙ₊₁ で証明される。
     - したがって、J8 の枠組みで段 n→n+1 が細分形の一歩であることと、未決定形の一歩であることは同値である。
2. **Lean**: `provFramework`, `provable_iff_mono`, `provFramework_same_iff`, `not_distinctionFlip_provFramework`, `not_refineStep_provFramework`, `ascent_not_refineStep`, `ascentFramework`, `ascent_le_of_le`, `ascentFramework_refines`, `ascent_refineStep`, `distinctionFlip_of_settles`, `settles_of_distinctionFlip`, `ascent_refineStep_iff`。
3. **状態**: 証明済み。(d)(e)(f) は 𝗜𝚺₁ と 𝗣𝗔 で実例化済み。
4. **依存**: (a)–(d) は弱化と命題論理。(e)(f) は MDG4(c) と、Tₙ₊₁ の無矛盾性。(f) の逆向きでは、区別が k ≤ n の段では起きないので段 n+1 で起きること、Tₙ で反証される側が Tₙ₊₁ で証明されれば Tₙ₊₁ が矛盾することを使う。
5. **新規性**: なし。
6. **言えないこと**:
   - 指示書の結論「区別の細かさはゲーデルの上昇では起きない」は、**J5 の読み（区別 = 証明可能な同値）での結果**である。
   - J8 の読みでは、上昇の各段は細分形の一歩になる。ただし (f) により、その中身は未決定形と同じものである。Con(Tₙ) と ∼Con(Tₙ) が区別されていなかったのは、まだ決まっていなかったからである。
   - J5 の読みでは、三つの形は別々に保たれる。
   - どちらの読みが著者の「区別の細かさ」に合うかは、著者が判断する（I9 の 4）。

### I6. ACSI の取り込み（MDG6）
1. **命題**:
   - (a) 分類は真から偽に反転しない（AC5(c) の再掲）。
   - (b) **判定の結果: 成り立つ。** 任意の作る働き M、自己 S、経験 e について、`evaluated (M.incorporate S e)` は `evaluated S` のすべての評価述語を保つ（`Refines`）。さらに、e、e' が S にとって全く新しく、e' が生成された範疇の外にあるとき、`(.inr e, .inr e')` は取り込みの前には区別されず（AC4(b)）、後には区別される（AC5(e)）。したがって `RefineStep (evaluated S) (evaluated (M.incorporate S e))`。
   - (c) `singletonMaking : Making ℕ`、空の自己、経験 0、1 で成り立つ。
   - (d) （D9 の裏づけ）取り込みは、区別されていたものを同一視しない。どんな過去 h についても、`evaluated (M.run S h)` は `evaluated S` のすべての評価述語を保つ。したがって、取り込みの後で同一なものは、取り込みの前にも同一だった。
2. **Lean**: `Refines`, `DistinctionFlip`, `RefineStep`, `Refines.refl`, `Refines.trans`, `classifies_incorporate_of_classifies`, `refines_evaluated_incorporate`, `distinctionFlip_evaluated_incorporate`, `refineStep_evaluated_incorporate`, `same_of_same_evaluated_incorporate`, `refines_evaluated_run`, `same_of_same_evaluated_run`。(c) は `Tests/MDGSpec.lean`。
3. **状態**: 証明済み。既存の `evaluated`・`incorporate` を変更していない。`refineStep_evaluated_incorporate` は公理を一つも使わない。
4. **依存**: AC4(b)、AC5(e)。評価述語が保たれるのは、`incorporate` が範疇の列の先頭に一つ加えるだけだからである。(d) は (b) と、過去についての帰納法。
5. **新規性**: なし。
6. **言えないこと**:
   - (b) は M3（`evaluated`）と M5（`incorporate`）の定義からほぼ直接に従う（§E3 の 2 と同じ種類の注意）。結果としては軽い。
   - (b) は、ACSI の取り込みが細分形の一歩**でもある**ことを示すだけである。ACSI を細分形と同一視しない（D8）。
   - 選択型の成長（重要でない区別を同一視する）は、現在のモデルでは表していない（D9）。(d) により、モデルの成長（取り込み）はこの型をとらない。モデルには区別の粗い枠組み（純粋経験の枠組み `Framework.pure`、自己同一の枠組み `selfIdentity`）もあるが、取り込みによってそこへ移ることはない。
   - ACSI には「反証」にあたるものがない。「分類できる」は二値で、取り込み前の「分類できない」が、反証された状態か未決定の状態かを区別しない。そのため、ACSI の取り込みは `Flips`（構造）にも `TheoryFlip`・`Settles`（理論）にも当てはまらない。MDG5(f) のように細分形を未決定形に還元できるかどうかも、ACSI については問えない。

### I7. 細分形の数学の例（MDG7。実現できた）
1. **命題**: ℤ√2（Mathlib の `Zsqrtd`、d = 2）で、次が成り立つ。
   - (a) 共役 a + b√2 ↦ a − b√2 は 0, 1, +, · を保存し、`<` は保存しない（0 < √2 だが 0 < −√2 でない）。
   - (b) `<` を使わない論理式は、共役で真理値を変えない（パラメータなし）。
   - (c) 環の枠組み（`<` を使わない論理式が定める述語）は √2 と −√2 を区別しない。
   - (d) 順序環の枠組み（すべての論理式が定める述語）は、`0 < x` で √2 と −√2 を区別する。
   - (e) したがって `RefineStep ringFramework orderedFramework`。
2. **Lean**: `Z2`, `conj`, `conj_func`, `conj_not_preserves_lt`, `OrderFree`, `IsEqRel`, `val_equiv`, `eval_equiv_of_orderFree`, `definable`, `ringFramework`, `orderedFramework`, `posFormula`, `ringFramework_same`, `orderedFramework_not_same`, `refineStep_ring_ordered`。
3. **状態**: 証明済み。実装は小さかった（約170行）。
4. **依存**: Foundation の `eval_iff_of_equiv` と同じ帰納法を、`<` を使わない論理式に制限して自前で証明した。順序の計算は `decide`（カーネルでの評価。`native_decide` ではない）。
5. **新規性**: なし。
6. **言えないこと**:
   - ℚ(√2) そのものではなく、ℤ√2 についての結果である（J6）。
   - パラメータを許すと、環の言語でも √2 を名指しして区別できる。
   - 「環の言語」は、ここでは `<` を使わない `ℒₒᵣ` の論理式（`OrderFree`）で表した。MDG2 の `ℒᵣ` とは別の扱いだが、表せる論理式は同じである（`ℒᵣ` の記号は `ℒₒᵣ` から `<` を除いたもの）。この対応は Lean では示していない。

### I8. 三者比較

| 移行 | 前の段を含む（D1(a)） | 反転形（偽→真） | 未決定形（未決定→決定） | 細分形（区別されない→区別される、D2） | 判定 |
|---|---|---|---|---|---|
| ℕ→ℤ | 埋め込みあり | あり（存在文 `sentenceZ`） | 対象外 | 調べていない | `ReversalStep` |
| ℚ→ℝ | 埋め込みあり | あり（存在文 `sentenceR`） | 対象外 | 調べていない | `ReversalStep` |
| ℝ→ℂ | 埋め込みあり（`ℒᵣ`。順序なし） | あり（存在文 `sentenceC`）。全称文 `∼sentenceC` は制限しないと真→偽、ℝ に制限すると真のまま | 対象外 | 調べていない | `ReversalStep` |
| ℂ→ℝ | 埋め込みなし | 反転文はある（`∼sentenceC`） | — | — | `ReversalStep` でない |
| ゲーデル Tₙ→Tₙ₊₁ | 構造の埋め込みではなく、定理の包含 `Tₙ ⪯ Tₙ₊₁` | 理論の反転なし | あり（`Con(Tₙ)`） | J5 の読みではなし。J8 の読みではあり、中身は未決定形と同じ（MDG5(f)） | 反転形は通らない。未決定形は通る |
| ACSI の取り込み | 構造ではない。評価述語と分類を保つ | 定義の外（I6 の 6）。「分類できる」は偽→真になり、真→偽にはならない | 定義の外 | あり（新しい経験 0 と 1） | `RefineStep`（細分は ACSI の成長の一つの型。D8） |
| ℤ√2: 環→順序環 | 同じ領域。評価述語を保つ | — | 対象外 | あり（√2 と −√2） | `RefineStep` |

どこで一致し、どこで分かれるか（事実の記録）:
- **一致**: 三者とも、前の段を何らかの意味で保つ。数学は構造の埋め込み（古い領域に制限すればすべての文が保たれる、MDG1(f)）、ゲーデルは定理の包含、ACSI は評価述語と分類である。
- **分かれ方**: それぞれが通る形が違う。
  - 数学の例は反転形を通る。
  - ゲーデルの上昇は反転形を通らず（MDG4(b)）、未決定形を通る（MDG4(c)）。
  - ACSI の取り込みは細分形を通る。ただし細分は ACSI の成長の一つの型であり、ACSI を細分形と同一視しない（D8）。選択型の成長は表していない（D9、MDG6(d)）。
- **ただし細分形については、ゲーデルと ACSI の違いは読みに依存する。** J8 の読みでは、ゲーデルの上昇も細分形を通る。ただしその細分形は未決定形と同じものである（MDG5(f)）。J5 の読みでは、三つの形は別々に保たれる。
- **ACSI と反転形・未決定形**: ACSI の取り込みは、構造の反転にも理論の反転にも未決定形にも当てはまらない。比較できないのであって、通らないことを示したのではない。
- **どの形でも、一つの体系の中で φ ∧ ¬φ は成り立たない**（A8、AC3(b)）。反転形で成り立っているのは、前の段で偽、新しい段で真という、段をまたいだ関係である。MDG1(g) でも、ℂ で同時に成り立つ二つは別の文（制限した文と制限しない文）である。

### I9. 著者に返す判断（Claude Code は判断しない）
1. ~~MDG6(b) は成り立った。ACSI の取り込みを、意味次元生成（細分形）とみなすか。~~ **著者が決定した（D8・D9）。** ACSI を細分形と同一視しない。細分は ACSI の成長の一つの型である。選択型の成長は、現在のモデルでは表していない。
2. 未決定形（ゲーデルの上昇）を、意味次元生成の一つの形に含めるか。
   - 含める場合、ゲーデルの上昇も意味次元生成の一つになる。対比は「ゲーデルの上昇は意味次元生成ではない」ではなく、「ゲーデルの上昇は未決定形しか通らず、反転形は通らない（MDG4）」になる。
   - 含めない場合、未決定形は比較の対象にとどまる。
3. 埋め込みの定義（J1、J2）が、著者の「前の段を特殊な場合として含む」に合っているか。FB を受けて次のように対応した。
   - ℂ の順序: 数学の例から `<` を外した（J2 改訂）。
   - 全称文の事実が保たれないこと: 古い領域に制限すれば、すべての文が保たれる（MDG1(f)(g)）。「含む」をこの意味で読むかどうかは著者が決める。
4. ゲーデルの上昇の「区別」を、証明可能な同値（J5）で読むか、各段での証明可能性の累積（J8）で読むか。
   - J5 では、ゲーデルは細分形を通らず、三つの形は別々に保たれる。
   - J8 では、ゲーデルは細分形も通る。ただし MDG5(f) により、その中身は未決定形と同じものになる。

### I10. 言えないこと（全体）
- 意味次元生成に伴う人間の意思、生成が発見ではないこと、可能無限であることは、形式化していない。
- 数学の例は、意味次元生成が**起きた後の**構造の関係を述べるだけで、生成の過程は表さない。
- 型があらかじめ固定されているので、「まだ存在しない構造」は表せない（ACSI の M7 と同じ限界）。
- ACSI の成長のうち、選択型（重要でない区別を同一視する）は表していない（D9）。
- 英語の "contradiction"（一つの体系の中の φ ∧ ¬φ）は、Lean の三つの形のどれにも厳密には当てはまらない（I8 の最後の項）。訳語をどうするかは著者が決める。
- 数学的に新しい定理はない。新規性は主張しない。

### I11. Kappa の「2+2=5」と埋め込みの条件（MDG8、2026-10-21 追加）

- 指示書: `CLAUDE_CODE_MDG8_KAPPA_INSTRUCTIONS.md`（2026-10-21）。D1–D9 に従う（とくに D4: 「含む」は構造の埋め込み）。
- 仕様: `docs/mdg_spec.md` §7（実装前に固定。調整 J11–J16）。
- Lean: `MeaningDimension/Generation/Packing.lean`（名前空間 `MeaningDimension.Generation.Kappa`。一般の補題 `isEmpty_of_open`・`evalOn_univ`・`models_iff_of_surjective`・`not_flips_of_surjective` は `MeaningDimension.Generation`）。
- テスト: `Tests/MDGSpec.lean` の MDG8 節（仕様の文言の書き起こしと、w = 1、w = −1/2 での実例化）。
- 依存公理はすべて標準3公理の部分集合。
- **Claude Web の見込み（指示書 §0）は、三点とも Lean で確かめられた。** 違いはなかった。

**主な調整**（詳細は仕様 §7.1）:
- **J11**: 構造はどれも台 ℚ にのるので、ℚ に通常の構造、型の別名 `Pack w := ℚ` に梱包の構造を入れる。指示書の `addModel ↪ₛ[ℒₖ] packModel w` は `ℚ ↪ₛ[ℒₖ] Pack w` と書く。
- **J13**: `four`、`five` は原子論理式として直接つくる（“…” 記法は ⌜n⌝ を数字項に読むため）。
- **J14・J15**: 「埋め込みはない」は「量化子のない文が M で真、M' で偽なら埋め込みはない」（MDG1(b)）から、「真理値が同じ」は「全射の埋め込みはすべての文を保つ」（MDG1(f) で像 = 全体）から出す。
- **J16**（指示書にない追加）: 一般の w ≠ 0 での反転文 `∼four`、`ℒᵣ` での MDG3 と同じ形の系（`Flips ℒᵣ ℚ (Pack w) (∼zeroR)`、`¬ ReversalStep`）、(b) の `ℒ⊕`・`ℒᵣ` 版。

1. **命題**（MDG8）:
   - (a) 真理値（`ℒₖ`）: ℚ（通常の加法）で `⌜2⌝ ⊕ ⌜2⌝ = ⌜4⌝` は真、`⌜2⌝ ⊕ ⌜2⌝ = ⌜5⌝` は偽。w ≠ 0 の梱包 `Pack w` で `four` は偽。`Pack 1` で `five` は真（Lakatos の数値）。
   - (b) 通常の加法は w = 0 の梱包である: `packModel 0 = addModel`、`packModelP 0 = addModelP`、`packRing 0 = ringModel ℚ`（構造として等しい）。恒等写像 `idPack : ℚ ↪ₛ[ℒₖ] Pack 0` は全射の埋め込み。
   - (c) 数を定数として固定する言語 `ℒₖ` では、w ≠ 0 なら埋め込み `ℚ ↪ₛ[ℒₖ] Pack w` はない。反転文はある（w ≠ 0 で `∼four`、w = 1 で `five`）が、`¬ ReversalStep ℒₖ ℚ (Pack w)`（MDG3 と同じ形）。
   - (d) 数の記号をもたない言語 `ℒ⊕` では、どの w でも x ↦ x − w が全射の埋め込み `shift w : ℚ ↪ₛ[ℒ⊕] Pack w`。したがってどの `ℒ⊕` の文も ℚ と `Pack w` で真理値が同じで、`¬ ReversalStep ℒ⊕ ℚ (Pack w)`（埋め込みはあるが反転文がない）。
   - (e) 数を 1 と + から作る言語 `ℒᵣ`: どの w でも `Pack w ⊧ “2 + 2 = 4”`（Foundation の数字項 n + 1 は `Pack w` で (n + 1) + n·w を表し、両辺とも 4 + 3w）。w ≠ 0 なら `“0 + 0 = 0”` が ℚ で真、`Pack w` で偽なので、埋め込み `ℚ ↪ₛ[ℒᵣ] Pack w` はない。`∼“0 + 0 = 0”` は反転するが、`¬ ReversalStep ℒᵣ ℚ (Pack w)`。
2. **Lean**: `kappaLang`（`ℒₖ`）, `plusLang`（`ℒ⊕`）, `addModel`, `packModel`, `addModelP`, `packModelP`, `packRing`, `Pack`, `four`, `five`, `fourR`, `zeroR`; (a) `rat_models_four`, `rat_models_not_five`, `pack_models_not_four`, `pack_one_models_five`; (b) `packModel_zero`, `packModelP_zero`, `packRing_zero`, `idPack`, `idPack_surjective`; (c) `isEmpty_of_open`, `isEmpty_kappa`, `flips_not_four`, `flips_five`, `not_reversalStep_kappa`; (d) `shift`, `shift_surjective`, `evalOn_univ`, `models_iff_of_surjective`, `not_flips_of_surjective`, `models_iff_plus`, `not_reversalStep_plus`; (e) `pack_val_numeral`, `pack_models_fourR`, `rat_models_fourR`, `pack_models_not_zeroR`, `isEmpty_ring`, `flips_not_zeroR`, `not_reversalStep_ring`。
3. **状態**: 証明済み。w = 1 と w = −1/2 で実例化済み。
4. **依存**: (c)(e) の「埋め込みはない」は MDG1(b)（量化子のない文は存在的）。(d) の系は MDG1(f)。(e) の数字項は Foundation の `numeral_add_two`。
5. **新規性**: なし。初等的な計算である。
6. **言えないこと**:
   - (b) の「特殊な場合」は、**パラメータ w を 0 にすること**である。MDG1(f) の「古い領域への制限」（埋め込みの像への制限）とは別の操作である。`ℒₖ` と `ℒᵣ` では（w ≠ 0 のとき）埋め込みがないので、像への制限という操作そのものがない。どちらが著者の「前の段を特殊な場合として含む」に当たるかは判断しない。
   - 言語の選択（どの記号の意味を固定するか）を Lean は決めない。MDG8 は、選んだ言語ごとの帰結を並べるだけである。
   - 梱包が「概念の拡張」として正当かどうか、Lakatos の Kappa・Gamma・Theta のどの立場が正しいかは扱わない。Lakatos の読解が正しいかも検証していない（指示書 §1）。
   - 構造はどれも同じ台 ℚ の上にある。通常の加法から梱包への移行は、ℕ→ℤ などと違い、台を広げる移行ではない。

**MDG8 の表**（§I8 の三者比較とは別の表。移行はすべて「ℚ（通常の加法）→ Pack w（梱包）」）:

| 言語 | 埋め込みがあるか | Kappa の文の真理値（ℚ → Pack w） | `ReversalStep` か |
|---|---|---|---|
| `ℒₖ`（⊕、⌜n⌝、=） | w ≠ 0 でなし（`four` が ℚ で真、`Pack w` で偽。量化子のない文） | `four`: 真 → 偽（w ≠ 0）。`five`: 偽 → 真（w = 1）。反転文はある | でない（w ≠ 0） |
| `ℒ⊕`（⊕、=） | どの w でもあり（x ↦ x − w。全射なので同型） | Kappa の文は書けない（数の記号がない）。どの文も真理値が同じ | でない（反転文がない） |
| `ℒᵣ`（0、1、+、·、=。数字は 1 と + から作る） | w ≠ 0 でなし（`0 + 0 = 0` が ℚ で真、`Pack w` で偽） | `fourR`（2 + 2 = 4）: 真 → 真（どの w でも）。`∼“0 + 0 = 0”` は反転する | でない（w ≠ 0） |
| （参考）どの言語でも w = 0 | あり（恒等写像。構造として等しい） | 変わらない | でない |

事実の記録:
- 三つの言語のどれでも、通常の加法 → 梱包（w ≠ 0）は `ReversalStep` ではない。ただし理由が違う。`ℒₖ`・`ℒᵣ` では埋め込みがない（反転文はある）。`ℒ⊕` では埋め込みはある（反転文がない）。
- Kappa の「2+2=5」（`five` が偽 → 真）が書けるのは `ℒₖ` だけである。`ℒᵣ` では数字が + から作られるので、2 + 2 = 4 は梱包でも真のままである。

**著者に返す判断**（Claude Code は判断しない。指示書 §5）:
1. Lakatos の書いた Kappa の例（数を重さとして固定する）に当たるのは `ℒₖ` か。
2. 言語にどの記号を入れるか（どの意味を固定するか）を、Lakatos p.103 の Theta の「拡張してよい構成要素を一部に限る」、p.124 の「意味を固定した形成的用語」と対応させるか。
3. D1(a) の「特殊な場合として含む」は、パラメータの特殊化（(b)）を含まず、構造の埋め込みに限る、という読みでよいか（D4 の確認）。
