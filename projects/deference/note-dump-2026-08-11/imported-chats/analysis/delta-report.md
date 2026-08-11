# Delta report: FA chat transcript vs. the three fa-positive-*-corrected files

*Provenance: produced 2026-07-21 by an exploration subagent (Claude Fable 5) during planning of the li-deference wiki reorganization. Task: verify Abram's impression that the corrected files do not capture everything in the chat. Chat file: `imported-chats/2026-07-01__checking-faithful-acceleration-result__a6632d0f.md` (43 messages, 2026-07-01 → 2026-07-17). This report drives the wiki write-ups; treat the transcript as authority.*

---

## Orientation / corrections to prior assumptions

- The chat is **43 messages**, spanning **2026-07-01 → 2026-07-17** (not 25 msgs / not ending 07-10).
- The three corrected files carry an internal date "2026-07-10," but that date is wrong/stylized: `fa-positive-result-corrected.md` (v1) was created at **msg 27 (07-15)**, `fa-positive-results-corrected-v2.md` (v2) at **msg 37 (07-17)**, `fa-positive-results-corrected-v3.md` (v3) at **msg 41 (07-17)**. The adjudication work (msgs 6–25, 07-01→07-10) lives in intermediate documents that predate all three files and were **never copied into the main notes** (they exist only as create_file calls inside the transcript): `fa-scope-adjudication-plan.md`, a claim/counterclaim explainer, `fa-ladder-check.md`, `fa-step2-verbatim.md`, `fa-step3-construction.md`, `fa-step4-resolution.md`, `fa-catchup.md`.

## 1. Chronology

| msg | date | event |
|---|---|---|
| 1–2 | 07-01 | Reads 4 corpus files; notes scope-note edits unapplied |
| 3–6 | 07-01 | Adjudication plan; **first flag of the scope-note §4 step-3 gap**; `fa-scope-adjudication-plan.md` created (msg 6) |
| 7–8 | 07-01 | Claim/counterclaim **explainer** created (msg 8); pseudorandom-side "reversal" of the gate argument raised |
| 9–12 | 07-02 | **(N)/(P) distinction** introduced (msg 10); the true sufficient condition for (II) is "unidentified anywhere in the corpus"; plan+explainer revised (msg 12) |
| 13–16 | 07-02 | **Strength-ladder correction** (msg 14): user's conjecture confirmed but faithful.md §5 ladder shown wrong; `fa-ladder-check.md` created (msg 16) with **Prop A, Prop B, witnesses W1–W7** |
| 17–19 | 07-02 | `fa-step2-verbatim.md` created (msg 18): **LI erratum swap in Thms 4.8.15/4.8.16**, tower-sparse feedback legality, "patient"=pseudorandomness family |
| 20–21 | 07-02 | `fa-step3-construction.md` (msg 21): g_n construction; **C4** (wrong χ comparator), **C6** (pre-decision timing) |
| 22–23 | 07-10 | `fa-step4-resolution.md` (msg 23): **reductio**, **Forcing Theorem A** (via Affine Recurring Unbiasedness 4.5.9), **Lemma B** (R ≤ 2^{O(n)} caveat), **Theorem C** (4 parts), **grid-wise** deliverable, **v6 consequences**, **(II) citation-vs-posit fork** |
| 24–25 | 07-10 | `fa-catchup.md` created — consolidation of all of the above |
| 26–27 | 07-15 | **v1** created: positive-result review using corrected **Feedback** Thm 4.8.16 as "Input U", tower-sparse grids, ledger-augmented class + Lemma R |
| 28–35 | 07-15/17 | Q&A: EF-progressions (msg 31), correlated-clusters remark (msg 33), **Garrabrant–Soares–Taylor 2016 unbounded-delays paper** (msg 35) |
| 36–37 | 07-17 | **v2** created (in-place rewrite; Abram archived the original as v1) |
| 38–39 | 07-17 | **The breakthrough correction (msg 39):** the Recurring theorem alone suffices; the H-side is *realized cash*, not an unbiasedness average; the erratum/feedback theorem is **not load-bearing**; spacing is exponential, not tower |
| 40–41 | 07-17 | **v3** created; msg 41 self-corrects (window-disjointness d_{k+1} ≥ 2^{d_k}; geometric schedules withdrawn — overlapping windows) and adds the **adaptive Theorem 2** recovering the full per-day / all-days result |
| 42–43 | 07-17 | **After v3:** staleness/strict-alternation impossibility, the relative surviving theorem, anticipated deference, the cross-generational conservation law |

Key facts: (a) the heavy discovery predates all three files and is captured only in intermediate docs; (b) v1→v2 is cosmetic, **v2→v3 is a substantive reversal**; (c) v1/v2's core structural claim was **explicitly retracted in msg 39**; (d) msgs 42–43 postdate the last file and are in no file.

## 2. Delta list

### 2A. Content produced AFTER v3 (msgs 42–43) — absent from all files

**D1 — Staleness / strict-alternation as a genuine impossibility (msg 43).** v3 §1(A1)/§6(iii) merely flag alternation as "open." Msg 43: the asymmetric-staleness model (A's calibration instruments see only *yesterday's* human price; the human has same-round sight of the quote) is argued to **break the unconditional theorem**. Failure mode: split true violation days (quote high, today's human credence low) by yesterday's credence; days where the human's credence *dropped into violation the same day the quote fired* are **uncatchable** — no A-generable weighting concentrates on them without predicting the drop from stale data, and the drop can be timed by the deductive-process feed (feed D_H the price-moving evidence only on the trigger day) to be unpredictable one day ahead to both sides. Candidate separation construction: a coupled pair consistent with both criteria in which violations recur forever, riding same-day surprises (~0.6; needs checking it creates no one-day-ahead H-internal arbitrage). Should amend v3 §1 (A1) bullet 3 and §6(iii).

**D2 — The relative surviving theorem under staleness (msg 43, ~0.8).** What provably survives: *for every stale-legal gate, the surprise-free violation weight is either finite or asymptotically dominated by the same-day-surprise weight on fired days.* Derivation = §3 plus a same-day price check on the stale-gated trader. Interpretation: "an AI certified against frozen human opinion can underwrite trust only up to the measured mass of same-day human belief movement" — surprise mass is ex-post observable, so the guarantee degrades gracefully along a monitorable quantity. Block-alternation (whole training runs) is the same with "same-day" → "within-block." Entirely new theorem family.

**D3 — Anticipated deference / trusting the future AI, positive direction (msg 43, ~0.7).** Avoid reference-to-the-unseen by comparing H's current credence in X with H's **current expectation of the future quote**. Positive chain from held pieces: the future quote is a determined LUV of the coupled run → H's own Recurring Unbiasedness makes H's expectations of future quotes track realized quotes on average along schedules → realized quotes are dominated by H's then-credences (Cor 2 / scheduled form) → **Expected Future Expectations** (LI Thm 4.11.x) collapses H's expectation of its own future credence back to its current credence. Net: H's expectation of any future quote is, on average and one-sidedly, ≤ its current credence + o(1). Per-day version would need Thm 2's machinery on the future-quote LUVs.

**D4 — Future-trust, negative direction (msg 43).** The diagonal construction is time-agnostic: a sentence arranged true iff the *future* AI's quote about it is ≤ ½ pins that future quote at ½ by the identical margin-gate argument. Trust in the future AI is also only average, one-sided, content-free on self-referential targets — "the reflective ceiling transfers across time rather than being escaped by it."

**D5 — Cross-generational conservation law (msg 43).** A pipeline of generations inserts a fresh staleness layer at each training freeze; the honest cross-generational statement is the relative surprise-conditional form (D2) *iterated* — "trust in AI_{k+1} conditional on the human-opinion movement during each intervening freeze" — "less like a theorem about equilibria and more like a conservation law for how much certification frozen data can carry forward."

### 2B. Claims INSIDE the files that the later chat undermines

**D6 — v1 and v2 are built on a structural error retracted at msg 39.** v1 §0/§5 and v2 §0/§2.3/§3/§5 make the **Feedback theorem 4.8.16 ("Input U")** the protagonist, treat the **published erratum as load-bearing**, require **tower-sparse** grids (d_{k+1} ≳ R(2^{d_k})), and assert (v1 §5.6, v2 §5.6–5.7) that "the Recurring family cannot power the squeeze." Msg 39 refutes this: the H-side of the squeeze is **realized cash** — the trader buys at H's low price and unwinds at day 2^n at H's own then-current price, which is definitionally what A forecast — so only one limit-point statement (the clause-free **Recurring** Thm 4.8.15) is needed, and "the feedback theorem, and with it the erratum, is not load-bearing for the positive result." **Wiki write-ups must be based on v3, not v1/v2, and must state the erratum is real+reportable but not load-bearing.** v1/v2 remain in notes/ as actively misleading.

**D7 — The spacing/cost story in v1/v2 §4 is superseded.** The R(2^n) no-shortcut conjecture and tower-spacing drop out in v3: Recurring needs **determinacy, not timely computability**, so the schedule condition is only **window-disjointness d_{k+1} ≥ 2^{d_k}** (no R; v3 §3). Also msg 41 *withdrew* the intermediate msg-39 claim that geometric schedules {2^k} catch a 1/log n profile (windows [2^k, 2^{2^k}] overlap) — fixed in v3, worth noting as a live-caught mistake.

**D8 — The three files disagree on the headline deliverable.** v1/v2 §5.6: full-sum ∑w_n < ∞ and per-day w_n → 0 **not delivered**. v3 recovers both via the adaptive one-position trader: **Thm 2** (w_n → 0 all days), **Cor 2** (per-day dominance liminf(E^H_n(X) − a_n) ≥ 0), **Cor 3** (∑_n w_n < ∞ all days), conditional on A4 expressibility (~0.85) + D.2 relativization; overall ~0.75. A write-up cannot cite all three as consistent.

**D9 — "Grid" terminology error still present in v1/v2.** Msg 39 diagnoses a conflation of value-space 1/n discretization ("grid-sum") with the day-schedule ("grid-wise"); v3 fixed exposition by dropping "grid."

### 2C. Earlier-chat findings never carried into any corrected file

**D10 — Strength-ladder correction to `faithful-acceleration.md` §5 (msg 14, fa-ladder-check.md).** Only the conclusion (per-day dominance) reached the files, only in v3. Missing: the ladder is **wrong** — the arrow **limit ⇒ bounded-ε-violation is false at fixed ε** (witness W1: G_n = 1/log n, E^H_n = t − 2ε forever ⇒ product → 0 so "limit" holds, yet ∑ w_n(ε) = ∞); the ∀ε-quantified theorem is **strictly stronger** than the displayed limit rung. Corrected order: bounded-violation ⇒ ∀ε-Theorem ⇒ single-ε ⇒ averaged, with conditional-limit a strictly-stronger side node and product-limit a strictly-weaker side node. **Prop A** (two-line proof of Abram's conjecture: ∀ε bounded-ε-violation ⇒ convergence) and **Prop B** (equivalence: at the theorem's own ∀ε,δ quantification, the whole family ⟺ liminf_n(E^H_n(X) − a_n) ≥ 0). v3 Cor 2 + Cor 3's remark state the equivalence but not the diagram, W1–W7, or that faithful.md §5 is in error.

**D11 — Retraction of faithful.md's "tolerance" example and line 171 (msgs 14/16).** faithful.md line 138's example ("a credence parked at t − ε/2 forever costs nothing") is **false**: it violates the instance at slack ε/4; the theorem forbids permanent fixed shortfalls on solidly-gated days, tolerating only vanishing ones. faithful.md line 171 ("the per-day limit statement is not forced here") is **false outright** by Prop B. Also a g_n gate/diagonal notation collision in faithful §5. None recorded in the corrected files.

**D12 — The (N)/(P) distinction and the "unnamed condition" (msg 10).** (N) "the diagonal family is out" vs (P) "everything else is in": the scope note argues (N) in detail but carries (P) on a bare "so," and **the true sufficient condition for (II) is unidentified anywhere in the corpus** — every condition the corpus verifies for (II) also holds at g_n. Plus the outside-view point (the counterexample was found by transplanting the one known construction, not by search) and the **simultaneity-not-quote-reference heuristic** with the benign past-quote probe x_n ↔ (a_{n−1} ≤ ½) (A reads a_{n−1} as a decided fact, tracks exactly). Not in the corrected files (v3 §6 asserts "no domain restriction" without the (N)/(P) framing).

**D13 — Degenerate-diagonal apparatus beyond "Fact (quote pinning)" (msg 23, fa-step4-resolution.md).** Files' §6 keeps only Forcing Theorem A as a bare "Fact." Dropped: (i) A is routed through **Affine Recurring Unbiasedness 4.5.9** specifically so pinning does **not** depend on the erratum swap-reading; (ii) **Lemma B** (η_n → 0 forcing on the H side) with its **R ≤ 2^{O(n)}** cost-model caveat; (iii) **Theorem C's four parts**: limit-point unbiasedness against all weightings; full-limit along legal grids even with hard conditioning on all past sides; margins below every expressible resolution (side-unreadability/pseudorandomness); **H-side forcing E^H_n(g_n) → ½ pre-decision** (= C6, killing scope §5's "unbounded violation weight" leg).

**D14 — The reductio meta-move (msg 23).** A sound theorem-*legal* gate argument would prove the **coupled pair does not exist** (contradicting obligation 3, asserted by both notes). The organizing insight: "the corpus's question is ill-posed against the source: the theorems can't fail, so ask what they *force*." With it, "existence (obligation 3) asserted, not proved (~0.9)."

**D15 — Wrong-χ-comparator finding, C4 (msg 21).** The scope note's χ/g_n distinction is drawn against the un-indexed intro liar ("never decided," clears at ½ by continuity), whereas the paper's formal diagonal χ^p_n hard-decides, is 0/1, anti-inductive — every property the scope note calls fatal — and Paradox Resistance (Thm 4.11.2) proves the price converges on it. faithful §6's "Dissolved" framing erred the same way from the opposite side.

**D16 — Consequences for v6 (msgs 23/25).** Never propagated: **v6 §4.8 "both faces die together" is false on the diagonal** (two_faces_distinct is realized on the diagonal — pinned honest quote, side-empty); **v6 §5.11's Value-failure witness ({g_n, const} menu) collapses** (family-TT holds degenerately ⇒ Value holds degenerately: deferring to an honest-but-empty ½ quote costs nothing vs H's own ½). Also the scope note's §7 edit list "points the wrong direction."

**D17 — The "(II): citation vs posit" fork (msg 23 §5.6 / catchup §5.6).** Flagged as *the single highest-weight judgment, explicitly reserved for Abram*: if the corpus's "(II)" is a **citation** of the paper's theorem, the degenerate resolution stands; if the corpus's own **posit**, scope's L2 instinct partially survives — nothing forces global side-frequency to converge (only limit points), so everywhere-(II) is plausibly false on g_n (~0.6, no construction). Verdict C-shaped either way, but edit lists differ.

**D18 — Step-2 disanalogy nuance (msg 21).** The same-agent χ^p has **fast feedback** (decided day n, readable n+1): f(n) = n+1 is legal, rich full-support weightings available — a genuine disanalogy with the cross-process 2^n lookahead forcing sparse legality.

**D19 — Rate-free grounding (msgs 33, 35).** The correlated-clusters reading (clusters of size 1, 10, 100, … ⇒ dense selections fail by size-growth, value selections by π-hardness, sparse-with-feedback the unique survivor) and **Garrabrant–Soares–Taylor 2016 "Asymptotic Convergence in Online Learning with Unbounded Delays"** (independent subsequences simultaneously sufficient and maximal; dense evaluation under unbounded delay provably noise; feeble rate bounds intrinsic). Grounds why the whole result is asymptotic/rate-free. Largely absent (one passing citation in v2 §2).

## 3. Intermediate chat documents → what reached v1/v2/v3

- **fa-scope-adjudication-plan.md** (msg 6; rev 12/19/21/23): 6-step plan, Q1–Q5, verdict criteria A1/A2/B/C. Nothing carried.
- **claim/counterclaim explainer** (msg 8; rev 12): L1/L2/L3 anatomy of (N), (P) as a fourth assertion; χ-vs-g_n; §2.1 tolerance story (later retracted, D11). Not carried; only the degenerate-diagonal conclusion survives diffusely.
- **fa-ladder-check.md** (msg 16): Prop A, Prop B, W1–W7, numerics, retractions. Only the Prop B equivalence reached v3.
- **fa-step2-verbatim.md** (msg 18): verbatim theorem families; erratum; tower-sparse legality; "patient" family placement; thm:lp same-agent precedent. Families+erratum+tower-sparse reached v1/v2; v3 keeps only the erratum box.
- **fa-step3-construction.md** (msg 21): g_n existence/β-ledger/e(n)≈n+1/grid-ties/η_n; C4; C6. Only diagonal-existence partially reached §6; C4/C6 not carried.
- **fa-step4-resolution.md** (msg 23): reductio; Forcing Theorem A via 4.5.9; Lemma B; Theorem C (4 parts); grid-wise deliverable; v6 consequences; the fork. Only Forcing Theorem A (as "Fact") + grid-wise deliverable carried (latter superseded by v3).
- **fa-catchup.md** (msg 25): self-contained consolidation. Not carried; superseded by v1's narrower scope.

## 4. Verdict

Abram's impression is correct, and then some: (i) the adjudication apparatus lives only in never-copied intermediate docs; (ii) v1/v2 encode a superseded architecture (a known error); (iii) the most recent, most project-relevant results (msgs 42–43) postdate v3 and are in no file.

Top missing/contradicted items: (1) base everything on v3 + msg 39, demote the erratum (D6, D8); (2) the post-v3 staleness/alternation results (D1, D2, D5); (3) anticipated deference, both signs (D3, D4); (4) the strength-ladder erratum against faithful.md §5 (D10, D11); (5) the v6 consequences and the citation-vs-posit fork (D16, D17).
