# The author's position (English, for *Philosophia Mathematica*)

Drafted 2026-10-11 (Phase B). Companion to `author_position_jp.md`. This is a working document, not manuscript text.

## 0. Labels

Every claim below carries exactly one label.

| Label | Meaning |
|---|---|
| **[OAC]** original author claim | A thesis the author advances in their own name. Argued for philosophically; not derived from any theorem. |
| **[SVN]** source-verified Nishida | A statement attributable to Nishida *because the passage was located and read* in a primary text (§3). Only the content of the quoted passage is attributed. |
| **[HA]** heuristic analogy | A structural comparison between the author's position (or Nishida's) and a mathematical or philosophical structure. It guides thought; it proves nothing. |
| **[MR]** mathematical result | A theorem with explicit hypotheses, either from the literature or verified in Lean (see `godel_boundary.md`, `lean_inventory_audit.md`). |

Nothing labelled [MR] is offered as a proof of anything labelled [OAC].

**Order of authority (author's instruction, 2026-10-11).** The author's own position ranks above Nishida.
1. The philosophical reference point of the paper is the author's theses (§2). Nishida is a subordinate resource and point of comparison.
2. Where the author's formulation and Nishida's text diverge, the author's formulation is **not** revised to fit Nishida; only claims *about Nishida* are corrected.
3. Nishida's authority is not used to ground the author's theses. Nishida's text is neither a proof of them nor a criterion of their correctness.
4. When the author uses a term of Nishidan origin (acting intuition; from the made to the making) in the author's own sense, it is marked as the author's usage. Only the content of verified passages is attributed to Nishida.

## 1. Terms and their boundaries

| Term | Working definition | Excluded readings |
|---|---|---|
| **the present (*now*)** | The locus in which reality is generated. | A completed time-line on which past, present and future are equally real regions. No identification with any named theory of time (A-/B-theory, presentism, growing block) is asserted here; comparisons, if any, belong in a separate section after the sources are checked. |
| **trace** | What remains now of a past event, available for inspection now. | — |
| **reconstruction of the past** | The narrative that the present meaning-system forms from traces. The *event* and the *meaning of the event now* are distinguished. | That the event did not occur; that there are no objective events. |
| **the future** | What does not yet exist. A completed future cannot be read off from the present by calculation. | That prediction is impossible; that there are no causal laws; that the future is random; that no mathematical conjecture about the future is possible. |
| **making** | The activity of making that is going on now, inseparable (in the author's sense) from acting intuition and open to the future. | Mechanical iteration of a predefined function such as `next : Stage → Stage`. |
| **retroactive meaning** | A newly generated meaning-dimension, ideology or narrative changes how past events are interpreted. | Alteration of historical records; attributing the new interpretation to historical agents; rewriting of memory traces themselves. |
| **meaning dimension** | A rule or framework that fixes what counts as an object, what counts as a question, and what can be proved, evaluated or chosen. | A mere new word or new proposition inside a fixed framework. |
| **meaning-dimension generation** | The coming-into-being of such a framework. Applies in mathematics and also to ideologies, narratives and historical interpretation. | Discovery of a pre-existing truth; a monotone extension `T ⊆ T'` of a theory in a fixed language (this is at most one limiting case; see `godel_boundary.md` B3). |
| **potential infinity (generative sense)** | For any meaning dimension generated, a further one can be generated; and the possibilities themselves are generated, not selected from a completed space of possibilities. | Actual infinity; a modal space of possibilities given in advance (the author's stated difference from potentialism). |
| **generative dialetheism** | A contradiction is a transition point: neither an error to be excluded nor a permanent truth to be accepted; a meaning dimension in which it is made true can *someday* be generated. | That Lean's classical logic proves this; that formal `φ ∧ ¬φ`, an unmet existence demand, undecidability and an open problem are the same thing. |
| **door** | A limit already present in an existing system through which generation can pass: contradiction, undecidability, limits of available means, open problem. | A cause that compels the next step. |
| **Gödelian non-closure** | [MR] For effectively presented, sufficiently strong theories under stated hypotheses, the theory does not prove its own (canonical) consistency statement, and adjoining it yields a strictly stronger theory; under Σ₁-soundness the process can be iterated. | Any claim about the future, time, meaning, consciousness or LLMs. |

## 2. Theses

### 2.1 Time

- **T1 [OAC].** The present ("now") is where reality is generated. The author rejects the picture of past, present and future as three equally real regions of a completed time-line.
- **T2 [OAC].** The past cannot be observed directly. It is reconstructed as narrative from present traces, by the present meaning-system. The event and its present meaning are distinguished; the claim is not that events did not occur.
- **T3 [OAC].** The future does not yet exist. No calculation performed now reads off a completed future. The point is that present calculation and prediction do not exhaust the possibilities of future generation — not that prediction is impossible.
- **T4 [OAC].** *Making* is the ongoing activity of making, inseparable from acting intuition and open to the future. "Acting intuition" here is the author's usage, not bound by Nishida's definitions. In the author's earlier paper (2025), from a practitioner's standpoint pure experience already contains acting intuition: "seeing while making, making while seeing" is lived before it is theorized; Nishida's two-stage development is read there as a theorist's detour.
- **T5 [OAC].** Generation reaches back to the meaning of the past: new meaning-dimensions, ideologies and narratives change how past events are interpreted. This is not alteration of records, not attribution to historical agents, not rewriting of memory traces.

### 2.2 Meaning-dimension generation and potential infinity

- **T6 [OAC].** Not only vocabulary and propositions but the rules and frameworks of meaning — what is an object, what is a question, what can be proved, evaluated or chosen — can be generated, in mathematics and beyond.
- **T7 [OAC].** *Axiom (standing commitment):* meaning-dimension generation is infinitely possible, in the generative sense of potential infinity. It is presented as the author's axiom, not as a consequence of Gödel's theorems.
- **T8 [OAC].** Generative dialetheism (as defined in §1). The thesis is strong and philosophical. The manuscript (§3.2) separates four doors; generative dialetheism is the thesis about the first.
- **T9 [OAC].** For each question there is some later stage at which it is handled; not: some stage at which every question is handled. The limits of a present system are not to be projected onto every system of meaning that may yet be generated. The quantifier distinction itself is elementary logic **[MR]**; that the *first* reading is true of meaning-generation is **[OAC]**; that the *second* fails for consistent, effectively axiomatized arithmetic theories is **[MR]** (Gödel–Rosser; Lean: `not_exists_eligible_proves_all_truths` for Σ₁-sound Δ₁-presented theories containing IΣ₁).
- **T10 [OAC].** Discovery methodology: using potential infinity deliberately, one can work backwards from conditions that a future meaning-dimension would have to satisfy to new conjectures and research questions. Its relation to abduction is open for examination; no claim of proven originality over inference to the best explanation, creative abduction, or transformational creativity is made. (Not yet in the manuscript.)

### 2.3 Platonism and potentialism

- **T11 [OAC].** Before ℂ was constructed, "i² = −1" had no truth-value — not because it was unknown, but because the question had no meaning in the real-number system.
- **T12 [OAC].** The openness of generation is an actor's openness, not a spectator's survey of a modal space. This is the author's stated difference from Linnebo–Shapiro potentialism. Whether it also requires a change of logic (intuitionism) is **unknown** (the GC preprint says yes; the PhilMath2 draft keeps classical logic) — to be confirmed by the author.

### 2.4 Nishida

- **T13 [OAC].** The author's theses on the non-ready-made character of time, the emergence of the future, and meaning-dimension generation are the author's own philosophy and rank above Nishida. Nishida's acting intuition and "from the made to the making" are important resources, but they are **not identical** with these theses and do not ground them.
- The author does **not** derive from Nishida a rule that the made must not be mixed with the making, nor a static one-to-one correspondence between axiom presentations (made) and provability relations (making). That correspondence belonged to the retired made-canonicity proposal (`retired_made_canonicity.md`).

## 3. What can be attributed to Nishida (source check — subordinate to §2)

This section constrains only what may be *attributed to Nishida*. It does not constrain the author's theses in §2.

**Source and limits.** Passages were retrieved verbatim from Aozora Bunko (raw XHTML, decoded from Shift_JIS; 60 quotations matched as exact substrings by script; 10 re-checked independently on 2026-10-11). Limits: the main texts are **modern-orthography editions** (Iwanami Bunko), not Nishida's original orthography; Aozora has **no page numbers**, so citations to the *Zenshū* still have to be made from the printed edition; the essays 「行為的直観」(1937) and 「論理と生命」(1936) are **not available** on Aozora (in preparation; card pages return 404), so claims about them are **not verified**. English glosses below are our working renderings, not published translations.

Main text: 「絶対矛盾的自己同一」, *Shisō* 202 (1939.3). Aozora card 1755; base text: 西田幾多郎哲学論集Ⅲ (Iwanami Bunko, 1989), parent text: 西田幾多郎全集 第9巻 (Iwanami, 1979). Locators are section number and paragraph count in the Aozora file.

| ID | Passage (verbatim; ruby removed) | Working gloss | What it licenses |
|---|---|---|---|
| N1 | 「時は過去から未来へ、作られたものから作るものへと、無限に動いて行くのである。」（§一 第3段落） | Time moves infinitely from past to future, from the made to the making. | [SVN] The phrase and its tie to time. The GC preprint's English quotation (§2) corresponds to this sentence. |
| N2 | 「動物にはいまだポイエシスということはない。作られたものが作るものから離れない、作られたものが作るものを作るということがない、故に作られたものから作るものへではない。」…「作られたものが作るものを作る、作られたものから作るものへである。故に人間はポイエシス的である」（§一 第12段落） | In animals there is not yet poiesis: the made does not separate from the making, the made does not make the making; therefore it is not "from the made to the making". … The made makes the making: that is "from the made to the making"; hence the human being is poietic. | [SVN] **For attribution only.** Mere non-separation of made and making is, in this text, the mark of *biological* life and explicitly *not* "from the made to the making". The human level is characterized by the made becoming independent of, opposed to, and productive of the making. The author's thesis that made and making are inseparable stands as the author's own; what must be avoided is attributing that thesis to Nishida. |
| N3 | 「なお真に作られたものから作るものへではなくて、作られたものから作られたものへである。」（§二 第9段落） | (In biological life) it is not yet truly from the made to the making but from the made to the made. | [SVN] Same point. |
| N4 | 「作るものが自己自身を否定して作られたものとなることが真に作るものとなるということが、作られたものから作るものへということであるのである。」（§二 第10段落） | That the making, by negating itself and becoming the made, truly becomes the making — this is what "from the made to the making" means. | [SVN] The relation is one of mutual (self-)negation — a dynamic, dialectical relation, not a one-way flow and not a static correspondence. |
| N5 | 「主体と環境とが対立し、主体が環境を、環境が主体を形成し行くということは、過去と未来とが現在において対立し、矛盾的自己同一として作られたものから作るものへということである。」（§一 第22段落） | Subject and environment form each other; past and future oppose each other in the present; as contradictory self-identity, this is "from the made to the making". | [SVN] Reciprocity; the present as the place where past and future meet. |
| N6 | 「行為的直観というのは、我々が自己矛盾的に客観を形成することであり、逆に我々が客観から形成せられることである。見るということと働くということとの矛盾的自己同一をいうのである。」（§二 第5段落） | Acting intuition is our self-contradictorily forming the object and, conversely, our being formed by it; the contradictory self-identity of seeing and acting. | [SVN] Definition-like characterization of acting intuition. |
| N7 | 「かかる意味において、行為と直観とは何処までも相反するということができる。」（§三 第17段落） | In this sense, acting and intuition can be said to be opposed through and through. | [SVN] **For attribution only.** Nishida calls acting and intuition a *contradictory* self-identity and "opposed through and through". "Inseparability of acting and intuition" is the author's own formulation; it stands as the author's thesis (T4) and is not to be attributed to Nishida. |
| N8 | 「行為的直観的に物を把握するということは、作ることによって見ることである、ポイエシスによって物を知ることである。」（§三 第8段落） | To grasp things by acting intuition is to see by making, to know things by poiesis. | [SVN] "Seeing by making". The two-way formula 「作ることによって見、見ることによって作る」 quoted in the author's 2025 paper was **not found verbatim**; the nearest is 「見ることによって働き、働くことによって見る」 (§一 第13段落). |
| N9 | 「それは因果論的に過去から決定せられる世界ではない、即ち多の一ではない、また目的論的に未来から決定せられる世界でもない」（§一 第3段落） | It is a world determined neither causally from the past nor teleologically from the future. | [SVN] Relevant to comparison with T3 (see §4). |
| N10 | 「時が永遠の今の自己限定として成立するというのも、かかる考を逆にいったものに過ぎない。」（§一 第4段落）; 「過去と未来との相互否定的に一である所が現在であり」（§一 第5段落） | Time arises as the self-determination of the eternal now; the present is where past and future are one through mutual negation. | [SVN] Nishida's "eternal now". Comparison with T1 is a hypothesis, not an identity (see §4). |
| N11 | 「未来は未だ来らざるものでありながら既に現れているという矛盾的自己同一的現在」（§二 第2段落） | The contradictory self-identical present, in which the future, though not yet come, already appears. | [SVN] **Note the difference** from T3 ("the future does not yet exist"): Nishida adds that the future already appears in the present. Whether the two conflict is a question for a comparison section, not settled here. |
| N12 | 「しかし過去は自己自身を否定して、未来へ行くことによって過去である。未来ありての過去である、無論その逆も真である。歴史においては、単に与えられたものはない、与えられたものは作られたものである」（§三 第17段落）; 「歴史的世界においては無限の過去が現在においてアウフゲホーベンされているのである。」（§一 第19段落） | The past is past by negating itself and going to the future; there is a past because there is a future. In history nothing is simply given; the given is made. The infinite past is *aufgehoben* in the present. | [SVN] Closest Nishidian material to T2/T5. Nishida does **not** state, in the checked texts, that the past is reconstructed or reinterpreted from the present. |
| N13 | 『善の研究』第一編第一章: 「たとい過去の意識の再現であっても、現在の意識中に統一せられ、これが一要素となって、新なる意味を得た時には、已に過去の意識と同一といわれぬ」; 「過去と感ずるのも現在の感情である。」 | Even a reproduction of past consciousness, once unified in present consciousness and given a new meaning, is no longer the same as the past consciousness; feeling something as past is a present feeling. | [SVN] (Aozora card 946; modern orthography; the first sentence cites Stout.) A further comparison point for T2/T5, from the early work. |
| N14 | 『善の研究』: 「経験するというのは事実其儘に知るの意である。全く自己の細工を棄てて、事実に従うて知るのである。」 | To experience is to know facts just as they are… | [SVN] The sentence quoted in the author's 2025 paper (there written 「事実そのままに」) is confirmed. |

Not found in the checked Aozora texts: the verbatim sentence "we see things by acting" (「我々は行為によって物を見る」); any explicit statement that the past is remade or reinterpreted from the present; "from the made to the making" outside 「絶対矛盾的自己同一」. A note on 「世界新秩序の原理」: "eternal now" occurs there in a passage on the imperial house (Aozora card 3217/3668; the card flags inappropriate expressions). It should not be cited as a neutral statement of Nishida's theory of time without that context.

## 4. Nishida read from the author's position (to be argued, not asserted)

The author's theses are the reference point; Nishida's passages are placed against them. These are **[HA]** or open comparison questions. None is a claim that Nishida held the author's view, or vice versa, and none is a reason to revise the author's view.

| # | Author | Nishida (verified) | Status |
|---|---|---|---|
| H1 | T1: the present generates reality | N5, N10: the present as the self-determination of the eternal now, where past and future meet | Comparison hypothesis. Differences to be examined: the author does not invoke "eternity". |
| H2 | T3: the future does not yet exist | N9 (not determined teleologically from the future); N11 (the future, not yet come, already appears) | Partial convergence (N9), possible divergence (N11). |
| H3 | T2, T5: the past is reconstructed and re-meant from the present | N12, N13 | Comparison hypothesis. Nishida's texts speak of *Aufhebung* and of present unification giving new meaning; the author's narrative-reconstruction thesis is not found there. |
| H4 | T4: making as ongoing activity, inseparable from acting intuition | N2–N4, N6–N8 | Convergence on activity and reciprocity. Where Nishida says "contradictory self-identity" / "opposed through and through", the author says "inseparable"; the author's formulation is retained as the author's. |
| H5 | T7: possibilities themselves are generated | — | No verified Nishida passage checked so far bears directly on this. |

## 5. Mathematical results: pointer

What Gödel's theorems and the project's Lean proofs establish, under which hypotheses, and how they relate to the theses above is set out in `godel_boundary.md`. In brief: they provide **[MR]** about effectively presented formal theories, which can serve as a limited, exact instance of *non-closure under a fixed operation*; they do not establish T1–T13.
