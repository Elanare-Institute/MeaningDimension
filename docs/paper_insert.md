# Material for the paper (Philosophia Mathematica resubmission)

> **2026-10-11 役割変更**: 論文原稿は著者と ChatGPT が作成し、Claude Code の担当は Lean 4 による数学的形式化・証明・反例探索のみになった。この文書は論文の構成・内容に関わるため Claude Code の担当外であり、**記録として保存し、以後は更新しない**。論文への適用は著者と ChatGPT が判断する。

Prepared 2026-10-10 against `paper_draft.pdf` (27 pp., 9 October 2026). The newer `PhilMath2.pdf` was not available; section numbers refer to `paper_draft.pdf` and must be re-checked against the latest version. Nothing below has been written into the manuscript.

---

## 1. Verified Formal Results

All results in this section are machine-checked in Lean 4 (v4.34.0) on top of the FormalizedFormalLogic/Foundation library (commit `dfaa003d`). Each proof uses only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`); no `sorry` or additional axioms occur. Throughout, *T* is a theory in the language of arithmetic that contains IΣ₁ and is given by a Δ₁ presentation (a Δ₁ formula, provably Δ₁ in IΣ₁, that defines its axioms in ℕ). The consistency statement Con_T is the Π₁ sentence ¬Prov_T(⌜⊥⌝) built from that presentation.

**Proposition 1 (propagation of Σ₁-soundness).** If *T* is Σ₁-sound, then so is *T* + Con_T.
(Lean: `MeaningDimension.Godel.Stage.sigma1Sound_next`.)

**Proposition 2 (the finite ascent does not terminate).** Let T₀ = T and Tₙ₊₁ = Tₙ + Con_{Tₙ}. If T is Σ₁-sound, then for every n: Tₙ is Σ₁-sound; Tₙ ⊬ Con_{Tₙ}; and Tₙ is strictly weaker than Tₙ₊₁. Hence Tₘ is strictly weaker than Tₙ whenever m < n.
(Lean: `sigma1Sound_ascent`, `G2_unprovable`, `G2_strict`, `G2_strict_of_lt`; instantiated at IΣ₁ and PA.)

**Proposition 3 (consistency does not suffice).** If T is consistent, then T + ¬Con_T is consistent, is not Σ₁-sound, and (T + ¬Con_T) + Con_{T+¬Con_T} is inconsistent.
(Lean: `consistent_union_incon`, `not_sigma1Sound_union_incon`, `inconsistent_next_of_union_incon`; instantiated at PA.)

**Proposition 4 (the ω-stage).** If T is true in ℕ, let T_ω = T ∪ {¬Prov_Tⁿ(⌜⊥⌝) : n ∈ ℕ}. Then T_ω is deductively equivalent to T ∪ U for a Δ₁-presented set U of Π₁ sentences; T ∪ U does not prove its own consistency statement; and adjoining that statement yields a theory strictly stronger than T_ω.
(Lean: `G3`. The Π₁ axiomatization is Foundation's `exists_prenex_axiomatization_turingOmega`. The consistency statement of the ω-stage is the one built from that particular presentation.)

**Proposition 5 (non-finality, and the order of quantifiers).** Call a Δ₁-presented theory *eligible* if it contains IΣ₁ and is Σ₁-sound. Every eligible theory has an eligible, strictly stronger extension. No eligible theory proves every sentence true in ℕ.
(Lean: `G4`, `not_exists_eligible_proves_all_truths`.)

**Proposition 6 (the derivability conditions do not fix the consistency statement).** Let Prov be any provability predicate satisfying D1–D3 and π any sentence; then Prov′(x) := Prov(x) ∨ π satisfies D1–D3, and Con′ ↔ Con ∧ ¬π. In particular, if T is Σ₁-sound and π := Prov_T(⌜¬Con_T⌝), then Prov′ is a Σ₁ provability predicate for T that satisfies D1–D3 and holds in ℕ of exactly the theorems of T, while T ⊢ Con′ → Con_T, T ⊬ Con_T → Con′, and T ⊬ Con′.
(Lean: `MeaningDimension.MadeCanonicity.disj_HBL`, `disj_con_iff`, `standard_disj_sigma1`, `standard_disj_models_iff`, `standard_disj_con_not_implied`, `standard_disj_con_implies`, `standard_disj_con_unprovable`.)

**Proposition 7 (one sentence, two structures).** The first-order sentence ∃x (x·x + 1 = 0) is false in ℝ and true in ℂ; consequently the complete theory of ℝ is not contained in that of ℂ. Under any single interpretation, and in any consistent extension that keeps the language and the theorems of a theory T, a sentence refuted by T cannot be affirmed.
(Lean: `real_not_models_rootSentence`, `complex_models_rootSentence`, `theoryOf_real_not_subset_complex`, `unprovable_of_refuted`, `not_models_of_refuted`.)

### Status of these results

Propositions 1–5 are known results or immediate corollaries of Gödel's second incompleteness theorem; the contribution is a machine-checked formulation with explicit hypotheses, not new mathematics. Proposition 6 is elementary; we have not found it stated in the sources we checked, but we do not claim it as new. Proposition 7 is elementary. **None of these propositions is a new theorem**, and none of them derives any philosophical thesis of the paper.

---

## 2. Known Foundations

- **Gödel's second incompleteness theorem** for Δ₁-presented theories extending IΣ₁ (`consistent_unprovable`) and the strict strengthening T ⪱ T + Con_T: Foundation, `Foundation/FirstOrder/Incompleteness/Second.lean` (S. Saitou, M. Noguchi et al.; Apache-2.0), reused without modification.
- **Abstract derivability conditions, Löb's theorem** and its formalized form: Foundation, `ProvabilityAbstraction/Basic.lean`.
- **T + ¬Con_T proves its own inconsistency**: Foundation, `height_union_incon_eq_one`.
- **Π₁ axiomatization of T + {¬Prov_Tⁿ(⊥)}**: Foundation, `Reflection/IteratedConsistency.lean`.
- **Σ₁ numerations satisfy G2** (so that condition (i) of made-canonicity alone suffices for D1–D3 and G2): Feferman (1960).
- **No Rosser provability predicate satisfies both D2 and D3**: Kurahashi, *Rosser provability and the second incompleteness theorem*, Corollary 3.3 (checked against arXiv:1902.06863).

---

## 3. Philosophical Interpretation

The formal results bear on the paper as follows, and no further.

- Propositions 1–5 are the arithmetic content of conditions (iii) *incorporation* and (iv) *non-completion* of the generative schema (§3.4) **for effectively presented arithmetic theories**. They do not establish the standing axiom that meaning-dimension generation is infinitely possible (§2.3), which concerns meaning in general and remains a philosophical commitment.
- Proposition 3 supports the claim of §6.3 that the technical signature of the ascent is Σ₁-soundness rather than consistency.
- Proposition 5 separates the two quantifier orders of §3.3 only in one direction: "one stage for all questions" fails for eligible stages. The other order — every question handled at some later stage — is, for arithmetic, the Turing–Feferman completeness theorem for transfinite progressions, which is not formalized here and depends on the choice of ordinal notations.
- Proposition 7 shows that what the construction of ℂ changes is the structure in which a sentence is evaluated. It does not exhibit a sentence and its negation both true; in the formal setting the "contradiction door" of §3.2 has the shape "T ⊢ ¬φ, while φ is satisfied under a different interpretation".
- Proposition 6 constrains the made-canonicity criterion (§4): the derivability conditions, extensional correctness and Σ₁ form together do not single out the consistency statement up to T-provable equivalence. Whatever selects the canonical statement must therefore come from condition (ii), and condition (ii) is not yet a formal condition.

---

## 4. Conjectures and Open Problems

The following are **not** proved.

1. A formal definition of condition (ii) of made-canonicity that is invariant under T-provably equivalent rewriting and not reducible to condition (i). The syntactic reading ("no Π₁ clause asserting the non-existence of a proof") is not invariant: α_k(x) := α(x) ∧ ¬∃y Prf_{α↾k}(y, ⌜0=1⌝) violates it but is T-provably equivalent to α for T ⊇ PA; and α'(x) := α(x) ∨ (x = ⌜0=1⌝ ∧ Prov_α(⌜¬Con_α⌝)) satisfies it while changing the consistency statement (cf. Proposition 6; the identification of Prov_{α'} with Prov ∨ Prov(⌜¬Con⌝) is argued on paper, not formalized).
2. *The converse question of §4.2.* On paper (not formalized), D1–D3 do not force Σ₁-ness even up to T-provable equivalence: for Σ₁-sound T, Prov_T(x) ∨ ¬RFN_{Σ₁}(T) satisfies D1–D3 (the formalized part of Proposition 6 covers this), is extensionally correct, and is not T-provably equivalent to a Σ₁ formula (sketch: otherwise RFN_{Σ₁}(T) would be T-equivalent to a true Π₁ sentence π, and T + π would prove its own consistency). If this argument is accepted, made-canonicity is strictly stronger than D1–D3, and condition (i) is not necessary for G2 either.
3. The identification of ⋃ₙ Tₙ with T_ω, and the recursive enumerability of ⋃ₙ Tₙ, are not formalized.
4. Every philosophical thesis listed in §3 above.

---

## 5. Reproducibility

- Repository: `MeaningDimension/` (local; commit `54dc740` for the Lean sources).
- Lean `leanprover/lean4:v4.34.0`; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`; Foundation `dfaa003d0c4533c89ca72ae513d9c055fd3fe7bf` (https://github.com/FormalizedFormalLogic/Foundation). All transitive dependencies are pinned in `lake-manifest.json`.
- Verification: `scripts/check_proofs.sh` (rejects `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; runs `lake build`, including the specification tests `Tests/Spec.lean`; audits the axioms of all 81 declarations; records the environment in `logs/`).

---

## 6. Proposed revisions to the paper

Proposals only; the wording is for the author to decide.

1. **§5, last paragraph ("A Lean 4 formalization verifies the strict hierarchy IΣ₁ < IΣ₁ + Con(IΣ₁) < ··· through ten stages").** The companion repository (Zenodo 10.5281/zenodo.20687363) contains a Lean proof of the first step only; the ten-stage verification there is for the modal logic GL (countermodels). Suggested replacement: "A Lean 4 formalization, built on the FormalizedFormalLogic/Foundation library, verifies that for every Σ₁-sound, Δ₁-presented theory T containing IΣ₁ — in particular IΣ₁ and PA — each stage of T, T + Con(T), … is Σ₁-sound and strictly weaker than the next, at every finite stage; and that consistency alone does not suffice (PA + ¬Con(PA))."
2. **§4.2, D3.** The displayed condition "T ⊢ φ ⇒ T ⊢ Prov(⌜φ⌝) for Σ₁ sentences φ" is a rule (D1 restricted to Σ₁). D3 requires the formalized implication T ⊢ σ → Prov(⌜σ⌝) for Σ₁ σ (provable Σ₁-completeness), as in footnote 49 of the earlier draft.
3. **§4.2, "D1–D3 as consequences".** The derivation uses only condition (i) (together with the requirement that α numerates T in T). It may be clearer to say that D1–D3 follow from condition (i), as is known from Feferman (1960), and that condition (ii) carries the philosophical, not the derivational, weight.
4. **§4.2, "The open converse".** The question as stated ("no provability predicate of complexity greater than Σ₁ that satisfies all three conditions has been exhibited") is settled trivially in its syntactic reading (e.g. Prov(x) ∧ ∀y(y = y)), and, by the argument in §4.2 above, negatively up to T-provable equivalence. Consider restating it, or replacing it by the argument.
5. **§1 and §4 ("selecting the philosophically justified consistency statement").** By Proposition 6, made-canonicity read as (i) + the syntactic gloss of (ii) does not determine the consistency statement up to T-provable equivalence. Either strengthen (ii) beyond its syntactic gloss, or weaken the claim to "excludes the known deviant presentations".
6. **§4.2, Feferman's α\*.** "The condition on which the deviant presentations fail is D3" holds for T extending PA (where α\* satisfies D1 because PA proves the consistency of each finite subtheory). For a finitely axiomatized T it can be D1 that fails. A qualifying phrase would suffice.
7. **§3.1 versus §3.2.** §3.1 says that "within the rules of the current system, both φ and ¬φ hold"; §3.2 and Table 1 say that for a classical T this would make T inconsistent, and recast the door as "T ⊢ ¬φ while the practice demands φ; T + φ derives both". The formal results support only the latter reading. Aligning §3.1 with §3.2 would avoid an objection.
8. **§3.4(iv).** "Mathematically: Σ₁-soundness propagates, and the process iterates" can cite Propositions 1–2, with Proposition 3 for the necessity of more than consistency.
