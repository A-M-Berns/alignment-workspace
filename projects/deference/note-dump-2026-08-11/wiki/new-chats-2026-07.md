# New material, July 2026 — reader's guide

*This is the first page to read if you are returning to the project. It summarizes what arrived in July 2026, what it changed, and where each insight lives (or will live) in this wiki. Master map: [[index]]; conventions: [[conventions-and-status-labels]].*

## What arrived

Four bodies of new material:

1. **The FA-critique chat** (`imported-chats/2026-07-01__checking-faithful-acceleration-result__a6632d0f.md`, 43 messages, 2026-07-01 → 2026-07-17). A long adjudication of the faithful-acceleration corpus (`faithful-acceleration.md`, `faithful-acceleration-scope.md`, `pointwise-tower-and-faithful-acceleration.md`, deference-v6) against the Logical Induction paper itself. It found errors in every corpus document, found a printed erratum in the LI paper, rebuilt the positive result twice, and ended with a new frontier (staleness, anticipated deference) that exists nowhere but in the chat.
2. **The origin chat** (2026-05-19, "combining trusted and capable inductors", 14 messages, copied into `imported-chats/`). The seed conjecture that faithful-acceleration later formalized.
3. **A new proof from a Claude Code session** (2026-07-20, session b9e8341b): full-menu Total Trust ⟹ Value by telescoping, bypassing the §1.6 squeeze. See [[total-trust-implies-value-telescoping]].
4. **The FA chat's continuation** (msgs 44–47, archived 2026-07-29): the **delay** question (formerly "staleness" — terminology corrected, see [[conventions-and-status-labels]]) developed properly. Yielded Theorem A (fixed questions are delay-proof, **~0.90 and the strongest statement in the corpus**), Theorem B (an impossibility on fresh questions — **since REFUTED**), Theorem C (a trade-off bound — **half refuted, half surviving**). This **supersedes D1**; see the two ⚠ blocks under §4. Document: `imported-chats/fa-block-staleness-impossibility.md`; results of record: [[faithful-acceleration-result]], [[delay-and-visibility]].

**The headline warning.** The three `fa-positive-*-corrected` files are **mid-chat snapshots**, not final statements. v1 (created at chat msg 27) and v2 (msg 37) are built on an architecture **explicitly retracted at msg 39** — they remain in `notes/` and are actively misleading if read alone. v3 (msg 41) is the best file-form statement, but it predates msgs 42–43, where the most project-relevant new results live. **The chat transcript is the authority**; the wiki pages are written from v3 + msgs 39–43, never from v1/v2.

## Chronology of the FA chat

Condensed from `imported-chats/analysis/delta-report.md` (which supersedes the earlier `chat-digest.md` on chronology). The three files' internal date "2026-07-10" is wrong/stylized.

| msgs | date | event |
|---|---|---|
| 1–6 | 07-01 | Corpus read; first flag of the scope-note §4 step-3 gap; adjudication plan (`fa-scope-adjudication-plan.md`) |
| 7–8 | 07-01 | Claim/counterclaim explainer; pseudorandom-side "reversal" of the gate argument raised |
| 9–12 | 07-02 | **(N)/(P) distinction**: the true sufficient condition for (II) is unidentified anywhere in the corpus |
| 13–16 | 07-02 | **Strength-ladder correction** vs `faithful-acceleration.md` §5 (`fa-ladder-check.md`: Prop A, Prop B, witnesses W1–W7) |
| 17–19 | 07-02 | `fa-step2-verbatim.md`: **LI-paper erratum in Thms 4.8.15/4.8.16**; tower-sparse feedback legality; "patient" = learning family |
| 20–21 | 07-02 | `fa-step3-construction.md`: $g_n$ construction; C4 (wrong-χ comparator), C6 (pre-decision timing) |
| 22–25 | 07-10 | `fa-step4-resolution.md` + `fa-catchup.md`: **reductio**, Forcing Theorem A (via Affine Recurring 4.5.9), Lemma B, Theorem C (4 parts), deference-v6 consequences, the (II) citation-vs-posit fork |
| 26–27 | 07-15 | **v1** created: Feedback Thm 4.8.16 as "Input U", tower-sparse grids, ledger-augmented class + Lemma R |
| 28–35 | 07-15/17 | Q&A: EF-progressions, correlated clusters, Garrabrant–Soares–Taylor 2016 unbounded-delays paper |
| 36–37 | 07-17 | **v2** (in-place rewrite of v1; Abram archived the original) |
| 38–39 | 07-17 | **The retraction**: Recurring theorem alone suffices; H-side is realized cash; erratum not load-bearing; exponential (not tower) spacing |
| 40–41 | 07-17 | **v3** created; msg 41 self-corrects (window-disjointness $d_{k+1} \ge 2^{d_k}$; geometric schedules withdrawn) and adds adaptive Theorem 2 |
| 42–43 | 07-17 | **After v3**: staleness/alternation impossibility, the relative surviving theorem, anticipated deference (both signs), the conservation law |

Key structural facts: the heavy adjudication (msgs 6–25) lives only in intermediate documents created inside the chat, whose bodies did **not** survive into the markdown export (see the recovery note in the Pointers section); v1→v2 is cosmetic but v2→v3 is a substantive reversal; and msgs 42–43 are in no file at all.

## The five headline corrections

### 1. The msg-39 architecture change; the erratum demoted

v1/v2 made the corrected **Unbiasedness From Feedback** theorem (4.8.16) the protagonist, treated the published erratum as load-bearing, required tower-sparse grids ($d_{k+1} \gtrsim R(2^{d_k})$), and asserted the Recurring family "cannot power the squeeze." Msg 39 retracts all of this. The key realization, verbatim:

> "The H-side of the squeeze is not an unbiasedness average at all — it is *realized cash*: the trader buys the sentence at H's low price on a flagged day and sells at day $2^n$ at H's own then-current price, which is *definitionally* the quantity A was forecasting." (msg 39)

> "Consequence: the feedback theorem, and with it the erratum, is not load-bearing for the positive result (the erratum remains a fact about the paper worth reporting); the load-bearing input is the *clause-free* recurring theorem, which is available for every generable divergent weighting." (msg 39)

So only one limit-point statement — the clause-free **Recurring Unbiasedness** Thm 4.8.15 — is needed. Spacing drops from tower to **window-disjointness** $d_{k+1} \ge 2^{d_k}$ (Recurring needs determinacy, not timely computability). Msg 41 caught and withdrew its own intermediate claim that geometric schedules $\{2^k\}$ catch a $1/\log n$ profile (windows $[2^k, 2^{2^k}]$ overlap). The chat put ~0.8 on the corrected route as a whole. v3 then recovers the full deliverable v1/v2 said was undeliverable, via the adaptive one-position trader: Thm 2 ($w_n \to 0$ on all days), Cor 2 (per-day dominance $\liminf_n(E^H_n(X) - a_n) \ge 0$), Cor 3 ($\sum_n w_n < \infty$ on all days) — conditional on A4 expressibility (~0.85) and the Lemma R/D.2 relativization (~0.85); ~0.75 overall. Canonical statement: [[faithful-acceleration-result]]. Erratum details (real, reportable upstream, ~0.95 — but not load-bearing): [[li-paper-erratum]]. Theorem-family anatomy: [[unbiasedness-theorem-families]].

### 2. The strength-ladder errata against `faithful-acceleration.md` §5

Msg 14 / `fa-ladder-check.md`: the printed ladder in faithful.md §5 is **wrong** — the arrow "limit ⇒ bounded-ε-violation" is false at fixed ε (witness W1: $G_n = 1/\log n$, $E^H_n = t - 2\varepsilon$ forever: the product limit holds, yet $\sum_n w_n(\varepsilon) = \infty$). Corrected order: bounded-violation ⇒ ∀ε-Theorem ⇒ single-ε ⇒ averaged, with the conditional-limit form a strictly stronger side node and the product-limit form strictly weaker. **Prop A** proves Abram's conjecture (∀ε bounded-ε-violation ⇒ convergence) in two lines; **Prop B** is the equivalence: at the theorem's own ∀ε,δ quantification, the whole family ⟺ per-day dominance $\liminf_n (E^H_n(X) - a_n) \ge 0$ (~0.95). Two further retractions never recorded in any file: faithful.md line 138's tolerance example ("a credence parked at $t - \varepsilon/2$ forever costs nothing") is false, and line 171 ("the per-day limit statement is not forced here") is false outright by Prop B. Full treatment, with the diagram and W1–W7: [[strength-ladder-corrected]].

### 3. The scope question resolved: the diagonal is degenerate, not excluded

The scope note's gate argument had a hole at step 3 (bounded soft-gate weight bounds summed excess, not day counts), and its (N) claim ("the diagonal family is out") never supported its (P) claim ("everything else is in") — the true sufficient condition for (II) is unidentified anywhere in the corpus. The resolution (msgs 22–23) runs through the reductio — the theorems are theorems and cannot fail, so ask what they *force* — yielding Forcing Theorem A (margin gates force $a_n \to \tfrac12$ on the diagonal, routed through Affine Recurring 4.5.9 so it is erratum-independent), Lemma B (with its $R \le 2^{O(n)}$ caveat), and Theorem C (four parts, including H-side forcing $E^H_n(g_n) \to \tfrac12$ pre-decision). **The diagonal sentence family is not a domain restriction; it is a degenerate stratum** on which the theorem holds vacuously (Paradox-Resistance regime). One judgment remains **explicitly reserved for Abram**: the (II) **citation-vs-posit fork** — if the corpus's "(II)" cites the paper's theorem, the degenerate resolution stands; if it is the corpus's own posit, the scope note's L2 instinct partially survives (everywhere-(II) plausibly false on $g_n$, ~0.6, no construction). Full page: [[fa-scope-resolution]].

### 4. The post-v3 frontier (msgs 42–43) — in no file

Prompted by Abram's observation (msg 42) that real training alternates: AIs equilibrate against *frozen* human data before humans see the frozen AI. Msg 43, in one message, produced:

- **Staleness breaks the unconditional theorem** (candidate separation construction ~0.6): the uncatchable days are those where "the human's credence *dropped* into violation on the same day the quote fired: no A-generable weighting can concentrate on them" (msg 43) — the drop can be timed by the deductive-process feed to be unpredictable one day ahead to both sides.
- **The relative surviving theorem** (~0.8): for every stale-legal gate, the surprise-free violation weight is either finite or asymptotically dominated by the same-day-surprise weight on fired days. "an AI certified against frozen human opinion can underwrite trust only up to the measured mass of same-day human belief movement" (msg 43) — and that surprise mass is ex-post observable, so the guarantee degrades gracefully along a monitorable quantity. Block-alternation is the same statement with "same-day" → "within-block". Page: [[delay-and-visibility]].
- **Anticipated deference** (positive chain ~0.7): compare H's current credence in $X$ with H's current *expectation of* the future quote; chain H's own Recurring Unbiasedness → Cor 2 (scheduled form) → Expected Future Expectations, giving: H's expectation of any future quote is, on average and one-sidedly, at most its current credence $+ o(1)$. Negative direction for free: the diagonal construction is time-agnostic, so the reflective ceiling transfers across time rather than being escaped by it. Page: [[anticipated-deference]].
- **Cross-generational conservation law**: iterating the relative form across training freezes looks "less like a theorem about equilibria and more like a conservation law for how much certification frozen data can carry forward" (msg 43).

The chat's own priority ordering for development: alternation-impossibility construction first (it decides the status of joint clearing), anticipated-deference chain second.

**⚠ Superseded 2026-07-29 (chat msgs 44–47).** The FA chat resumed and developed the first of those two items, and the result **retracts D1's construction rather than confirming it**. Abram rejected the paradox-style aim; the answer relocated the question from staleness to *novelty*. In `imported-chats/fa-block-staleness-impossibility.md` (the only copy) plus `imported-chats/2026-07-29__fa-chat-continuation-msgs-44-47__a6632d0f.md`:

- **Theorem A (~0.85)** — for a *fixed* question, deference survives **arbitrary** staleness (including a forecaster that never sees the human's data). The human's credence in a fixed sentence converges, so the violation gate can be rebuilt from the forecaster's own quote — never stale to itself — and any persistent gap is a one-signed bias its own Recurring Unbiasedness forbids. So D1's fixed-target/forever-swinging-credence construction **cannot exist**.
- **Theorem B — ⚠ REFUTED 2026-07-29, see [[delay-and-visibility]] §3** (was offered at ~0.75 on Assumption P). As claimed, the impossibility was real on **fresh** questions: one new Ackermann-parity conjunction per block with evidence arriving mid-block, both agents the paper's own constructed inductors (freeze implemented as feed timing, so **no joint clearing needed** and both criteria hold by citation), divergent violation weight on a gate that is human-legal and provably not forecaster-legal. Lemma 4's mixed-sign audit is the non-paradox certificate: nobody is exploited, nobody is wrong.
- **Theorem C — ⚠ HALF REFUTED 2026-07-29.** The frozen-certifiable part is **not** finite ([[delay-and-visibility]] §5); the surviving bound is violations $\le O(1) + (C/\varepsilon)\cdot$(within-delay update mass), ~0.75, with tightness unestablished (~0.25).
- **D5** becomes a stated corollary; the **day-scale** version of the question stays open at ~0.6.

**⚠ Second correction, 2026-07-29 (verification pass).** Theorem B **fails in its own environment**, for a structural reason worth knowing: its evidence must be simultaneously *hard* (so the delayed forecaster cannot anticipate it) and *easy* (so the human is forced to respond). LI generability admits **no primitive for the deductive state** (Def. 4.3.5 / 3.4.3), and Provability Induction needs an e.c. sequence of *theorems*, so selecting the refuted blocks means computing the Ackermann-hard parity — nothing forces the human's credence to move. Re-timing cannot fix it: the freeze restricts price visibility, never computation. Theorem B's *methodological* headline — that the verification "largely dissolved" — is retracted with it. What survives is the diagnosis: **the criterion forces a price to respond only to evidence an efficiently computable handle can select.**

Theorem A, by contrast, came out of that pass **stronger** (~0.90) and strictly subsumes v3's Corollary 2 under weaker hypotheses. The result of record is now [[faithful-acceleration-result]] (the two-half factoring and three routes) plus [[delay-and-visibility]]; the page formerly planned as `staleness-and-alternation` is superseded by the latter. Working document: `delay-program.md`. Full content index of the source: `imported-chats/index.md`.

### 5. Consequences for deference-v6

Never propagated to any file (msgs 23/25): **deference-v6 §4.8 "both faces die together" is false on the diagonal** — two_faces_distinct is realized there (pinned honest quote, side-empty); and **deference-v6 §5.11's Value-failure witness (the $\{g_n, \text{const}\}$ menu) collapses** — family-TT holds degenerately, so Value holds degenerately (deferring to an honest-but-empty ½ quote costs nothing against H's own ½). Corrected treatments: [[tower-death]] and [[trichotomy-where-value-sits]].

## Delta list → wiki pages

The D-numbers are from `imported-chats/analysis/delta-report.md` (the 19 insights absent from, or contradicted by, the corrected files).

| item | content | wiki page |
|---|---|---|
| D1 | Staleness / strict-alternation impossibility (~0.6 construction) — ⚠ **construction retracted** by Theorem A (msgs 44–47); impossibility relocated to fresh questions | [[delay-and-visibility]] |
| D2 | Relative surviving theorem under staleness (~0.8) — now **proved with a constant** as Theorem C (msgs 44–47) | [[delay-and-visibility]] |
| D3 | Anticipated deference, positive chain (~0.7) | [[anticipated-deference]] |
| D4 | Future-trust, negative direction (time-agnostic diagonal) | [[anticipated-deference]] |
| D5 | Cross-generational conservation law | [[delay-and-visibility]], [[open-problems]] |
| D6 | v1/v2 built on the msg-39-retracted architecture; erratum not load-bearing | [[faithful-acceleration-result]], [[li-paper-erratum]] |
| D7 | Spacing story superseded: window-disjointness $d_{k+1} \ge 2^{d_k}$, no $R$; geometric-schedule withdrawal | [[faithful-acceleration-result]] |
| D8 | v3's adaptive Thm 2 / Cor 2 / Cor 3 recover the all-days result (~0.75) | [[faithful-acceleration-result]] |
| D9 | "Grid" terminology conflation (value-space vs day-schedule) | [[faithful-acceleration-result]] |
| D10 | Strength-ladder correction: Prop A, Prop B, W1–W7, corrected diagram | [[strength-ladder-corrected]] |
| D11 | faithful.md L138 tolerance example and L171 both false | [[strength-ladder-corrected]] |
| D12 | (N)/(P) distinction; the unnamed sufficient condition; simultaneity heuristic | [[fa-scope-resolution]] |
| D13 | Degenerate-diagonal apparatus: Forcing Thm A via 4.5.9, Lemma B, Theorem C (4 parts) | [[fa-scope-resolution]] |
| D14 | The reductio meta-move; existence of the coupled pair asserted not proved (~0.9) | [[fa-scope-resolution]], [[open-problems]] |
| D15 | Wrong-χ-comparator finding (C4): scope note argued against the wrong diagonal | [[fa-scope-resolution]] |
| D16 | deference-v6 §4.8 and §5.11 corrections | [[tower-death]], [[trichotomy-where-value-sits]] |
| D17 | The (II) citation-vs-posit fork — **reserved for Abram** (~0.6 under the posit reading) | [[fa-scope-resolution]], [[open-problems]] |
| D18 | Step-2 disanalogy: same-agent $\chi^p$ has fast feedback ($f(n) = n+1$ legal) | [[unbiasedness-theorem-families]] |
| D19 | Rate-free grounding: correlated clusters + Garrabrant–Soares–Taylor 2016 unbounded delays | [[faithful-acceleration-result]], [[open-problems]] |
| — | Joint clearing / ledger-augmented class $\mathcal{C}^+$ + Lemma R (~0.85) | [[joint-clearing-and-trader-class]] |
| — | Theorem-family verbatim anatomy; "patient" placement; tower-sparse legality | [[unbiasedness-theorem-families]] |

## The new session proof: Total Trust ⟹ Value by telescoping

Separately from the FA chat, a 2026-07-20 Claude Code session (b9e8341b) produced a proof that exists only in that conversation (extraction: `imported-chats/analysis/session-b9e8341b-proof.md`). Full-menu **Total Trust ⟹ Value** by menu induction: relabel so the comparison option (the fixed option $O^i$ that Value benchmarks the strategy against) is first, walk the menu with keep-or-switch decisions $\widehat S^{(k)} = \widehat S^{(k-1)} + D_k \cdot \mathbb{1}[E^\ast(D_k) > 0]$, apply TT($D_k$, 0) to each derived bet, and telescope: $E^H_n(\widehat S) \gtrsim_n E^H_n(O^i)$. Punchline: two-option Value telescopes to full Value; the §1.6 convex-geometry squeeze is bypassed because Value never needed the tower equality — Value is "one rung below the tower." Uses only the novice's Linearity of Expectation (4.8.4) and Expectation Provability Induction (4.8.10), plus expert coherence + introspection. Three caveats travel with it (no conflict with DDB's hard direction; no conflict with the amplifier; hard-argmax Value remains Mart-only — with soft weights the honest theorem is about the δ-hedged strategy). It closes a genuine gap: deference-v6's §5.9-area gloss "Value ⟺ Total Trust" overstated what §1.2 proves. Pages: [[total-trust-implies-value-telescoping]] (overview; split 2026-07-23 into [[keep-or-switch-telescope]], [[one-shot-hedge]], and [[provable-bound-respect]] — the latter two are post-session strengthenings, unvetted).

## The 2026-07-23 → 07-27 session: the TT ⟹ Value cluster revised, then the triangle closed

A five-day Claude Code arc, driven by Abram's objections, that progressively corrected the telescoping-era material and then closed the deference loop. **Part one (07-23 → 07-25)** is the revision to the true setting, below; **part two (07-26 → 07-27)** follows it. In order: the single write-up split into route pages; `value-iff-total-trust-witness` renamed [[two-option-value-iff-total-trust]] ("witness" oversold); the e.d./e.c. distinction (descriptions vs. values — [[setting-and-notation]] §LUV); [[ledger-decided-tie-breaks]]; then the major revision: **exact F1 retracted** (finite-day inductor expectations respect proven identities only via unexploitability), the **linear-extension surrogate** identified as smuggling expert-side content into notation, and [[total-trust-implies-value]] rewritten in the true LI setting — TT ⟹ Value factors into bounds transfer + self-endorsement; the **punishing-menu counterexample** (argmax Value unconditionally false on selection-referencing menus; exogeneity necessary and nontrivial to define — the definitional ladder); and **conditional-stability** (Abram, 2026-07-25) as the preferred scope condition, under which argmax Value is proved modulo two named items. Strategic note (Abram): TT ⟹ Value was always going to need decision-theoretic assumptions (Counterfactual Mugging as much as Death in Damascus); the desired future direction is to model a *trained policy* trusted directly, abstracting away the decision rule ([[open-problems]]). All unvetted; every affected page carries dated ⚠ revision blocks.

**Part two (07-26 → 07-27): the mass-weighted condition, and the triangle.** First a de-clutter — [[total-trust-implies-value]] stripped to setting → (H1)(H2)(H3) → two lemmas → theorem → necessity, with the definitional ladder moved to [[defining-exogeneity]] and the soft form to [[soft-self-endorsement]]. Then two results. (i) Abram restates conditional-stability **mass-weighted**: multiply each conditional-vs-unconditional gap by the self-prediction mass rather than dividing by it, sum over options, require only $\gtrsim_n 0$. The vanishing denominator was the sole reason an $\varepsilon$-proviso was ever needed, so the uniformity open problem is *retired* rather than solved; and the one-sided form separates the adversarial from the clairvoyant tie-break correctly, the earlier per-index form having over-rejected ([[ledger-decided-tie-breaks]]). (ii) **Value ⟹ Tower directly** ([[value-implies-tower]]): offer the two-option menu "hold $Z$ and pay the expert's price for it, or lose $\varepsilon$." Introspection pins the gap-bet's quote at $0$ whatever $Z$ is, so the expert provably takes it, and Value against the constant reads off the novice's valuation — four lines, no Total Trust, no ramp, and the scope condition is satisfied automatically. That closes **TT ⟹ Value ⟹ Tower ⟹ TT** with three direct arrows instead of six, and gives a fresh argument against *syntactic* exogeneity: it would make probe menus illegal and sever the arrow. Two corrections fell out along the way — conditional-stability cannot be a global axiom (it is refutable on the punishing menu), so it must restrict Value's own menu quantifier; and Mart ⟹ Value is **refuted**, not merely unproved, since the tower holds by `cee` in the self-trust instance while the punishing menu still kills Value.

Transcript: `imported-chats/2026-07-23__tt-value-cluster-revision-arc__5cf76191.md` (74 msgs; folder overview at `imported-chats/index.md`). Artifacts are the wiki pages themselves. Beat-by-beat map in the transcript's "Where to look": the exactness collapse at 35–42, the punishing menu at 45, conditional-stability at 49, the mass-weighted restatement at 63–64, Value ⟹ Tower at 65–66, the triangle audit at 67–68.

## The secondary chats

- **2026-05-19 "combining trusted and capable inductors"** (14 msgs; copied to `imported-chats/`) — the **origin** of the program. Seed conjecture: ask the fast inductor on day $n$ what it expects the slow inductor to believe by $f(n)$; under good feedback this converges to the slow inductor's limit while remaining an inductor itself. Also: identifiability, bootstrapping, path-dependence, and Kosoy epistemic fixed points (endogenous vs exogenous priors, Brouwer, loss of uniqueness).
- **Not copied** (reviewed and set aside): 2026-06-14 LI + cooperative oracles (62 msgs — substantive but off-topic: multi-agent coordination/bargaining, no deference theorems); 2026-06-15 slide deck, 2026-06-17 compilation, 2026-06-25 office hours (presentation/logistics only).
- **The 11 Anson chats** (2026-05-20 → 06-20) were already catalogued with URLs in `anson-notes/INDEX.md` and integrated into deference-v6 §4–§5; they are not part of the July delta.

## Where things live

- **Transcripts**: `imported-chats/` — four of them plus the FA chat's 44–47 continuation fragment, catalogued at `imported-chats/index.md` (start there; it also documents the naming scheme, the message-number citation convention, and the topic index).
- **Chat-authored documents** now in `imported-chats/`: `fa-block-staleness-impossibility.md` (msg 47 — the only copy anywhere, unvetted, deliberately not promoted into the main notes) and `fa-positive-results-corrected-v3.md` (msg 41 — a **higher-fidelity** copy than `notes/fa-positive-results-corrected-v3.md`, which is missing msg 41's §3 self-correction paragraph and has had its LaTeX escapes eaten). Cite the `imported-chats/` copy; the discrepancy is documented in `imported-chats/index.md`.
- **Intermediate working documents** the FA chat authored mid-adjudication: `fa-scope-adjudication-plan.md`, `fa-claim-counterclaim-explainer.md`, `fa-ladder-check.md`, `fa-step2-verbatim.md`, `fa-step3-construction.md`, `fa-step4-resolution.md`, `fa-catchup.md` (created at msgs 6/8/16/18/21/23/25). These predate all three corrected files and contain most of the adjudication apparatus (only fragments reached v1/v2/v3 — the delta report §3 has the carry-over map). ⚠ **Their bodies could not be recovered here**: the markdown export renders every create_file/str_replace call as a parameterless placeholder. Recovery options: download the seven artifacts from the claude.ai chat UI into `imported-chats/fa-chat-artifacts/` (a README there explains), or re-render the raw claude.ai export with tool-input rendering enabled. Their *substance* is preserved in the chat's visible discussion and summarized in `analysis/delta-report.md`.
- **Analysis briefings**: `imported-chats/analysis/` — `delta-report.md` (authoritative chronology + D1–D19), `chat-digest.md` (four-critiques digest + secondary chats; superseded by the delta report on chronology), `session-b9e8341b-proof.md` (the telescoping proof extraction).
- **Legacy files**: retained unmodified as history per [[conventions-and-status-labels]]; the supersession table is in [[index]]. Remember: v1/v2 contain retracted claims; v3 is best but incomplete; the transcript is the authority.
