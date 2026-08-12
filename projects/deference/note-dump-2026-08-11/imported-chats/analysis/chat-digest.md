# Digest: new web chats relevant to li-deference (planning-phase briefing)

*Provenance: produced 2026-07-21 by an exploration subagent during planning of the li-deference wiki. Digest of the primary FA chat and skim of the other recent logical-induction chats. NOTE: the chronology here was refined by the later delta analysis — `delta-report.md` supersedes this file on chronology (43 msgs, → 07-17) and on what reached the corrected files. Chat filename was later re-exported as `2026-07-01__checking-faithful-acceleration-result__a6632d0f.md`.*

## Primary chat: 2026-07-01 "Checking Faithful Acceleration Result" (43 msgs, 07-01 → 07-17)

Documents reviewed in-chat: `deference-in-logical-induction-v6.md`, `faithful-acceleration.md`, `faithful-acceleration-scope.md`, `pointwise-tower-and-faithful-acceleration.md`, with `references/logical-induction/main.tex` (arXiv:1609.03543v5) as reference text; also `FaithfulAcceleration.lean`.

### Four compounding critiques

1. **(N)/(P) conflation in the scope note** (msgs 9–12): (N) "a counterexample family exists where (II) fails" does not yield (P) "the theorem holds on the complement" — (P) is a fresh universal claim; every condition the corpus verifies for (II) also holds at g_n, so the true separating condition is nowhere named in the corpus ("the L1 gap").
2. **Gate-argument hole at step 3** (msgs 4, 8): "both soft gates carry bounded weight ⟹ a_n = ½ ± o(1) hence a_n ≤ ½" is a non sequitur — bounded soft-gate weight bounds summed excess (a_n − ½)⁺, not the count of days; witness a_n = ½ + c_n with c_n summable. Initially proposed "patient hard gate" repair — later overturned (see 4).
3. **Strength-ladder in faithful.md §5 wrong** (msgs 13–16): printed ladder inverted; "limit ⇒ bounded-ε-violation" false at fixed ε (witness G_n = 1/log n, E^H_n = t − 2ε); tolerance example false; equivocation between product-form and conditional-form "limit." Corrected order: bounded-violation ⇒ ∀ε-Theorem ⇒ single-ε ⇒ averaged. Proved equivalence: full theorem family (all rational t, ε, δ) ⟺ per-day dominance liminf_n(E^H_n(X) − a_n) ≥ 0 (~0.95).
4. **The crux** (msgs 18–23): the corpus's ingredient (II) misstates the paper — the real From-Feedback theorems (4.3.8/4.5.10) carry a support clause (weighting support ⊆ image of a deferral function f, fired value computable by next firing); "patient" belongs to the learning family (Def 4.4.3), not feedback. With f(n) = 2^n, legal feedback weightings are tower-sparse. The gate argument's uniform weightings were never legal instances — on OR off the diagonal. **Printed erratum in the LI paper**: 4.8.15/4.8.16 have a transposed hypothesis (arXiv v5 p.42, pp.112–113), certified by appendix proofs E.11/E.12 (~0.95); reportable upstream. The reductio: 4.8.15/4.8.16 are theorems, they can't fail — ask what they *force*. Resolution: Forcing Theorem A (margin gates via clause-free Affine Recurring 4.5.9 force a_n → ½ on the diagonal — erratum-independent), Lemma B, Theorem C; **the diagonal is not excluded, it is degenerate** (Paradox-Resistance regime 4.11.2); v6 §4.8 "both faces die together" false on the diagonal; §5.11 witness collapses.

### Later development (msgs 26–43) — see delta-report.md for full detail

v1 (msg 27) built on the Feedback theorem + tower-sparse grids ("full sum NOT delivered"); v2 (msg 37) same content restructured after Abram's review; **msg 39 retraction** (Recurring theorem + realized-cash suffices; erratum not load-bearing; exponential window-disjointness); v3 (msg 41) with adaptive Thm 2 recovering all-days results; msgs 42–43 post-v3: staleness/alternation impossibility + relative surviving theorem + conservation law + anticipated deference (both signs).

### Setting of the corrected results ("a somewhat different setting" than v6's abstract theory)

- **(A1) joint clearing / same-round mutual visibility**: both markets clear together as one joint fixed point daily; trader coefficients may depend continuously on day-≤n prices of both markets. Replaces the implicit "recognizable to both" with an explicit ledger-augmented trader class C⁺ + relativization lemma (Lemma R / D.2 remark, ~0.85). Load-bearing vs strict alternation (and msg 43 argues alternation plausibly breaks the unconditional theorem).
- **Determinacy without a run-cost bound (A3)**: target determined via Γ_A (logical condition), letting limit-point Recurring carry the argument with no timing bound — why v3's schedules are merely 2^{d_k}-window-disjoint.
- **Per-X, one-sided, rate-free**: no uniformity across X, nothing constrains days where H's credence exceeds the quote, no rate bounds.
- **No domain restriction**: the diagonal is a degenerate stratum, not an exclusion.

### Open items at end of chat

Existence of the coupled pair (obligation 3, ~0.9, asserted not proved); Lemma R/D.2 relativization needs an actual read of pp. 99–104 (~0.85); A4 expressibility (~0.85); Lemma B's R ≤ 2^{O(n)} caveat; the (II) citation-vs-posit fork (reserved for Abram, ~0.6 that everywhere-(II) is false on g_n under the posit reading, no construction); strict alternation open (msg 43 candidate construction ~0.6); erratum to report upstream; Abram had not yet evaluated steps 2–4 consequences (msg 22).

## Secondary chats (skimmed)

- **2026-05-19 combining-trusted-and-capable-inductors** (14 msgs) — substantive, foundational, different phase: the ORIGIN of the program. Seed conjecture faithful-acceleration later formalizes (ask fast inductor on day n what it expects the slow inductor to believe by f(n); under good feedback converges to slow inductor's limit and is itself an inductor). Identifiability, bootstrapping, path-dependence, Kosoy epistemic-fixed-points (endogenous vs exogenous priors, Brouwer, loss of uniqueness). Copied into imported-chats/.
- **2026-06-14 combining-LI-with-cooperative-oracles** (62 msgs) — substantive but off-topic: multi-agent coordination/bargaining (LI + FixDT + cooperative oracles + ROSE), no deference theorems. Not copied.
- **2026-06-15 slide-deck** (16 msgs) — presentation production only. Not copied.
- **2026-06-17 compilation** (6 msgs) — logistics (chat bundling + extract script). Not copied.
- **2026-06-25 trust-models office hours** (8 msgs) — logistics (Drive retrieval). Not copied.
- The 11 Anson chats (2026-05-20 → 06-20) are already catalogued with URLs in `anson-notes/INDEX.md` and integrated into v6 §4–§5.
