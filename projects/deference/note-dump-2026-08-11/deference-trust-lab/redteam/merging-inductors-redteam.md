# Red-team: Fast-Student / Slow-Teacher merge (`merging-inductors-model.md`)

**Verdict: SALVAGEABLE.** The architecture (AGENDA merge = v2 §10 Value with a constructed
expert `B`; good feedback discharges the one cross-agent premise) is sound and genuinely
illuminating. But **part (a)'s proposed patch for the named gap is the *wrong theorem*** — a
fixable error, not a fatal one — and the headline "no feedback ⇒ endorsement FAILS" **over-states**
what the micro-example and Lean actually show. The Lean file is correct, will type-check, and is
faithful (with one prose over-claim). Fixes below.

Stress tools: `/tmp/redteam_merge.py`, `/tmp/redteam_wubexp.py` (reasoning is reproduced inline so
this file stands alone; those scratch files are not under the lab and may be GC'd).

---

## (a) Is the central claim TRUE? — counterexamples / degenerate cases

### A1. The biggest substantive defect: part (a)'s patch invokes the WRONG theorem (SALVAGEABLE)

The model honestly flags that `thm:wubexp` (Expectation Unbiasedness From Feedback, LI Thm in
`app:wubexp`) **requires the target LUV-combination to be "determined via Γ"** — i.e. it takes the
*same* value `thmval(·)` in *every* world `W ∈ 𝒫𝒞(Γ)` (LI Def. "Determined via Γ for
LUV-Combinations", main.tex:1806). It then proposes to *replace* "determined via Γ" by
"`A`-decidable in `O(f(t+1))`" and calls this "morally `thm:wubexp`."

**This replacement is not sound, and reading the proof shows exactly why.** The proof of `wubexp`
(main.tex:5264–5282) does two things: (1) apply `wubaff` per world `W` to get
`avg wᵢ(𝔼ᵢ(affluv) − 𝔼^W_i(affluv)) ≂ 0` — unbiasedness against the *per-world* value; then (2) use
`conluvapprox` to bound `|𝔼^W_i(affluv) − thmval(affluv)| ≤ b/n`, *collapsing the per-world value to
the single `thmval`*. **Step (2) is exactly where "determined via Γ" is consumed.** The merge target
`μ_t = ℙ^H_{f(t)}(φ_t)` is `H`'s *market price* — an empirical fact about another machine's
computation, **not** a `Γ`-determined value: different consistent worlds `W` need not even agree on
`φ`'s truth, and `H`'s price is not a truth-value of any `Γ`-sentence. So there is no single
`thmval` for `B` to be unbiased toward, step (2) has nothing to collapse to, and `wubexp` delivers
*nothing*. "`A`-decidable in `O(f(t+1))`" buys you the *time* hypothesis but not the
*determined-value* hypothesis; the two are independent, and the patch silently swaps one for the
other.

**The honest route (the smallest fix that makes the claim true):** don't price the *real number*
`μ_t`; price the **decidable threshold sentences**
`ψ^q_t := "ℙ^H_{f(t)}(φ_t) > q"` for rationals `q`. The *truth value* of `ψ^q_t` **is** decidable by
simulating `H` for `f(t)` steps, hence `A`-decidable in `O(f(t+1))`, and it **is** a decidable
sentence — so **`thm:wub` (Unbiasedness From Feedback, the *sentence* form, main.tex:1249) applies
verbatim**, giving `A` `w`-unbiased about the *truth* of `H`'s price-thresholds. Integrating over
thresholds (`μ_t = ∫₀¹ 𝟙[ℙ^H_{f(t)}(φ_t) > q] dq`) recovers `w`-unbiasedness about the price itself.
So Prop A is *salvageable*, but via **`thm:wub` on threshold sentences, not `thm:wubexp` on the
price**, and the integral-over-thresholds step (uniformity in `q`, generability of the family) is a
genuine — if smaller and very plausibly closable — open step. **Recommendation: rewrite (a.2) around
`thm:wub` + thresholds; delete the "`A`-decidable replaces determined-via-Γ in `wubexp`" sentence,
which is false as stated.**

### A2. The no-feedback failure is mis-narrated: bias *per se* does NOT break endorsement (SALVAGEABLE)

Probe 4 (`/tmp/redteam_merge.py`, no-noise persistent bias `b`, `μ→0.70`):

```
bias=-0.25: avgB=0.45  E^H(Shat)=0.30  Value FAIL
bias=-0.20: avgB=0.50  E^H(Shat)=0.50  Value FAIL   (boundary)
bias=-0.19: avgB=0.51  E^H(Shat)=0.61  Value FAIL
bias=-0.10: avgB=0.60  E^H(Shat)=0.70  Value PASS   <-- biased but endorsement HOLDS
bias=-0.05: avgB=0.65  E^H(Shat)=0.70  Value PASS
```

A *persistent downward bias* of `−0.10` (`A` systematically lowballs `H` by 0.1) still **passes**
Value. Endorsement only fails once the bias is large enough to push `B` across the `0.5` **decision
boundary** and flip the winning bet. So the true mechanism is **"bias large enough to flip the
argmax ⇒ failure,"** not the document's repeated "no feedback ⇒ endorsement FAILS." This is actually
*consistent* with the Lean lemma (`S` is monotone in `σ`; the Value *inequality* only breaks when
`σ` crosses to favoring the wrong option) — but the prose in (a.1), (b.3), (c) overgeneralizes.
**Fix: restate as "endorsement degrades monotonically with bias and fails once bias flips the menu's
argmax"** — sharper, true, and it makes the 2-option menu's knife-edge explicit rather than hiding
it. (This also matters for the trust story: a *small* persistent AI bias is survivable; the cliff is
at argmax-flip. That's a more interesting and more honest claim.)

### A3. The good-feedback side is robust, NOT an artifact (SOLID)

Probes 1–3: the good-feedback PASS is *not* an artifact of `p_∞` being far from `1/2`. It holds for
`p_∞ ∈ {0.70, 0.55, 0.51, 0.501, 0.50, 0.499, 0.45}` (Probe 1), survives noise amplitude up to 3.0
straddling the boundary (Probe 2, because the noise is genuinely `w`-mean-zero so the tail average
still tracks `μ`), and the tail-average tracking is phase-robust (Probe 3). This half is solid and
the numbers mean what the document says.

---

## (b) Does a hypothesis secretly smuggle the conclusion? (vacuity / triviality)

- **Hop 2 / Route B is honestly flagged as *relocation*, not discharge** — good discipline. Route B
  adds "`H → A` LUV-Total-Trust restricted to `{⌜ℙ^H_{f(t)}(φ)⌝}`," which makes Hop 2 true *by
  definition*. The document explicitly says this "does not discharge §10's premise from nothing — it
  relocates it." Correct and not a smuggle; it is the genuine deliverable (minimal trust the human
  must extend). No objection.
- **Route A (mutual good feedback) is the load-bearing claim and inherits A1's defect.** "Both
  martingales fire" presupposes the `A`-watching-`H` martingale, which is precisely Prop A — so
  Route A is only as strong as the A1 fix. With the threshold-sentence repair it is plausible; as
  written (via `wubexp`) it is not yet established.
- **Observability ((b.1)(i)) is a real assumption, not a smuggle.** §10 requires `(B_t(O^j_t))_t` to
  be `ℙ^H`-generable; the model supplies it by "`A` *publishes* `B_t` and `H` reads it as an
  expressible feature." This is an honest communicational hypothesis (it is exactly §10.4's
  "observability is structural, not cosmetic"). Fine — but note it is doing real work and should not
  be undersold: off the unobservable class it is precisely what fails, which the model does say.
- **Minor looseness in Hop 1 (not a defect).** Hop 1 cites "`thm:ccee`/`thm:ceu`." `thm:ceu` is the
  *unweighted sentence* martingale `ℙ_n(φ) ≂ 𝔼_n(⌜ℙ_{f(n)}φ⌝)`; the *weighted* form needs `thm:ccee`,
  whose weight is indexed at `f(n)` (not `t`). The model is sloppy about the `w_t` vs `w_{f(t)}`
  indexing. Harmless to the conclusion but worth a one-line tightening.
- **No vacuity from the weighting.** `w ≡ 1` (used in the micro-example) is a legitimate `ℙ^H`-
  generable divergent weighting, so the asserted identities are non-vacuous. Good.

---

## (c) The Lean file: will it type-check, and is it faithful?

**Prediction: it WILL type-check, no `sorryAx`.** Confirmed by reading (not compiling):

- All three imports (`Mathlib.Algebra.Order.Field.Basic`, `Mathlib.Tactic.Linarith`,
  `Mathlib.Tactic.Ring`) are present as prebuilt oleans in the lab's Mathlib build.
- `mul_le_mul_of_nonneg_right` has signature `(hbc : b ≤ c) (ha : 0 ≤ a) : b*a ≤ c*a`
  (Mathlib `Algebra/Order/GroupWithZero/Unbundled/Defs.lean:228`), reachable transitively from
  `Algebra.Order.Field.Basic`. The call `mul_le_mul_of_nonneg_right hσ h2μ` with `hσ : σb ≤ σc`,
  `h2μ : 0 ≤ 2*μ−1` produces `σb*(2*μ−1) ≤ σc*(2*μ−1)` — types match exactly.
- All algebra independently verified on a rational grid (`/tmp` check, sympy-free):
  `S_eq` holds; `S(σc)−S(σb) = (σc−σb)(2μ−1)` so `bias_only_hurts` is correct under `hμ, hσ`;
  `reversal_when_mu_small` (`S 0 σ = 1−σ`) holds. `ring`/`linarith` discharge all of these.
- **Non-vacuity is genuinely certified** by `reversal_when_mu_small`: at `μ=0` monotonicity reverses,
  proving `μ ≥ 1/2` is load-bearing. Good practice.
- **No smuggling of Value:** the lemma concludes `S σb ≤ S σc`, never `S ≥ μ` (the Value
  conclusion). Witness: `S(0.7, σ=0)=0.3 < 0.7=μ` is allowed by the lemma. Confirmed independent.

**Faithfulness gap (the thing the Lean-verify agent should record): the lemma is one abstraction
level above the prose.** `σ` is a *free monotone selector*, decoupled from both the estimate `b` and
the truth `μ`. The model-specific content — *"a downward bias on `b` ⇒ a lower `σ` on the winning
bet"* — is **assumed** (as the hypothesis `σb ≤ σc` / `σbias ≤ σtrue`), **not proved**, because it is
the softmax-monotonicity fact that lives in the confirmed `LeanDeference.softmax_lower_bound` family.
So Lean kernel-checks only the *final algebraic link*: "given the selector already puts less weight
on the winning bet, the return is no higher." That is true and useful, but calling `σ` "the bias"
(docstring of `unbiased_dominates`, "DOWNWARD feedback bias (`σb < σμ`)") **conflates the selector
weight with the estimate bias**. The chain `bias on b → lower σ → lower S` has its middle link
imported, not formalized here. **This is faithful-as-an-isolated-lemma but the prose over-credits it
as capturing "bias only hurts" end-to-end.** Notes for Lean-verify: (i) confirm `#print axioms`
shows only `[propext, Classical.choice, Quot.sound]`; (ii) the lemma name `bias_only_hurts` should
arguably be `selector_weight_helps`/`return_monotone_in_selector` to match what is actually proved.

---

## (d) Smallest changes to make false→true / vacuous→substantive

1. **(a.2) — replace the patch.** Drop "`A`-decidable replaces determined-via-Γ in `wubexp`." Re-route
   Prop A through **`thm:wub` on threshold sentences `ψ^q_t = "ℙ^H_{f(t)}(φ_t) > q"`** (truth
   `A`-decidable in `O(f(t+1))`, a real decidable sentence), then integrate over `q`. This converts a
   false invocation into a true argument with one *new, smaller, plausibly-closable* gap (uniformity
   in `q`). **This is the single most valuable next step.**
2. **(a.1)/(b.3)/(c) — restate the negative result** as "endorsement degrades monotonically with
   bias and fails once the bias flips the menu's argmax" (Probe 4), not "no feedback ⇒ fails." Add the
   `−0.10`-bias-still-passes row to the micro-example — it strengthens the *honesty* and the trust
   moral (small persistent AI bias is survivable; the cliff is at argmax-flip).
3. **Lean — rename + add the missing link as a separate confirmed-import citation.** Either rename
   `bias_only_hurts`→`return_monotone_in_selector`, or add a one-line lemma (or explicit citation to
   `LeanDeference`) establishing `b ↦ σ(b)` monotone, so the prose chain is actually closed in Lean.
4. **Hop 1 — fix the `w_t` vs `w_{f(t)}` indexing** and cite `thm:ccee` (weighted) rather than
   `thm:ceu` (unweighted) for the weighted hop.

---

## Single most valuable next step

**Rewrite Prop A (a.2) around `thm:wub` applied to the decidable threshold sentences
`"ℙ^H_{f(t)}(φ_t) > q"` (truth simulatable in `O(f(t+1))`), then integrate over `q`** — this is the
*correct* theorem, it discharges the `A`-watching-`H` martingale that Route A needs, and it replaces
the model's one genuinely-wrong claim (the `wubexp` substitution) with a sound argument whose only
residual gap (uniform-in-`q` good feedback) is small and standard. Everything else in the note —
the §10 reduction, Route B as honest relocation, the Lean lemma, the good-feedback numerics — is
solid or honestly flagged.
