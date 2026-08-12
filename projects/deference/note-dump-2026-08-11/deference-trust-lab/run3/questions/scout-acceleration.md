# Scout report — lens: Faithful acceleration and the pointwise tower

*Round 3 of the deference-trust lab. Scout session, 2026-07-01. Deliverable of record for the
"faithful acceleration / pointwise tower" lens.*

**What I read.** `faithful-acceleration.md` (all; §5 as of the then-current revision, §8),
`faithful-acceleration-scope.md` (all), `pointwise-tower-and-faithful-acceleration.md` (all),
`anson-notes/no-timely-pointwise-tower.md` (all), `lean-deference/FaithfulAcceleration.lean` and
`TowerAndAcceleration.lean` (all), `lean-deference/SelfReferentialTarget.lean` (declaration
skim), `lean-deference/AUDIT.md` (§2.4–2.5, §3.1–3.6, per-theorem tables),
`run2/todos/TODOS.md` (GLOBAL OFF-LIMITS + laundering ban), the project's recent commit history,
v6 §5.9 vicinity and `li-deference.md` §0.3 vicinity (targeted greps).

**Recent-edit context.** The last ~10 commits rework faithful §5 into: (a) a translation
*chain* from classical Total Trust down to `∑ wₙ < ∞`, explicitly non-derivational ("it pictures
how the statements relate; it does not derive the bottom line"), with the one non-equivalence
named **the weakening** and the day-`n` evaluation named **the seam**; (b) a four-rung
**strength ladder** (bounded-violation ⇒ limit ⇒ bounded-ε-violation ⇒ averaged, "each ⇓ a
strict weakening"); (c) a direct Steps-1–4 proof from ingredients (I)+(II) promoted to primary
(a recent revision), with the trader demoted to illustration. §8 lists three obligations
(observability bookkeeping, coupled existence, **no hidden hard settlement** — the deepest) and
declares the calibration bound **Discharged** as exactly LI Theorem 4.8.16.

**Two things I found while reading that are not (to my knowledge) recorded anywhere in the
corpus** — both hand-verified with exact rationals below, both feeding questions:

---

## Finding A — the scope-note §4 gate argument has a hole (steps 3–4)

`faithful-acceleration-scope.md` §4 argues calibration (II) provably fails on the
quote-referencing diagonal `gₙ ↔ (aₙ ≤ ½)` using exactly three weightings: the soft high gate
`Ind_δ(aₙ > ½)`, the soft low gate `Ind_δ(aₙ < ½ − δ)`, and the uniform weight. Step 3 infers
from "both soft gates carry bounded weight" that "on all but bounded weight, `aₙ = ½ ± o(1)`,
**hence `aₙ ≤ ½`**", and step 4 concludes the uniform bias → −½.

The "hence" is a non sequitur: bounded *soft-gate weight* does not bound the *number* of days
with `aₙ > ½`, only the summed excess. **Counterexample** (hand-verified, exact rationals; any
`δ ∈ (0, ½)`):

    aₙ = ½ + 2⁻ⁿ  (n even),   aₙ = ½  (n odd).

- Soft high gate: `∑ min(1, 2⁻ⁿ/δ) ≤ (1/δ)·∑ 2⁻ⁿ < ∞` — bounded. ✓ (step 1 fires vacuously)
- Soft low gate: support is `aₙ < ½ − δ`, never — weight ≡ 0. ✓
- `Yₙ = 𝟙[aₙ ≤ ½]` = 0 (even), 1 (odd); bias `bₙ = aₙ − Yₙ` = `½ + 2⁻ⁿ` (even), `−½` (odd).
- **Uniform average bias → 0**: over `2N` days the ±½ terms cancel exactly and the leftover is
  `∑_{even n<2N} 2⁻ⁿ ≤ 4/3`, so the average is `O(1/N)`.

So for this quote sequence the three named weightings *all fail to witness miscalibration*:
steps 3–4 as written do not go through. (`aₙ` neither "stays low" nor stays high — it hovers at
½⁺ half the time — so the parenthetical in pointwise §4.1 does not cover it either.)

**The conclusion is nevertheless repairable, and the repair is thematic.** Because `gₙ`
hard-decides — `"aₙ ≤ ½"` is recorded in the ledger by stage `n+1` — a *patient* (one-day
deferred) weighting may read that decided value *discretely*: LI's continuity discipline binds
trading only in the **current day's** prices; dependence on **past** prices is unrestricted
computable. So the hard gates `wₙ⁺ = 𝟙[aₙ > ½]`, `wₙ⁻ = 𝟙[aₙ ≤ ½]` are legal patient
weightings here. Then: `wₙ⁺ + wₙ⁻ ≡ 1`, so at least one is divergent; on `w⁺` the bias is
`bₙ = aₙ > ½` pointwise, on `w⁻` it is `bₙ = aₙ − 1 ≤ −½` pointwise; either way the weighted
average bias is bounded away from 0 on a divergent legal weighting. Calibration fails —
*and the legality of the killing gate comes precisely from the hard settlement*, i.e.
"calibration breaks exactly where tracking does" for the **same structural reason** (the
ledger's hard 0/1 makes the discontinuous gate readable). This sharpens the scope note's own
thesis while fixing its proof. (On my counterexample: `w⁺` = the even-days indicator, divergent,
average bias ≥ ½. ✓)

Status labels: the counterexample and the hard-gate dichotomy are finite/asymptotic real-sequence
arithmetic (kernel-checkable); "patient hard gates are legal C_A-weightings" is an
interpretation-level claim about the LI paper's weighting class (prose, checkable against
Thm 4.8.16's statement — see Q7).

## Finding B — the §5 strength ladder's middle implication is false as stated

faithful §5 (current text, recent revisions) displays four statements "strongest to
weakest (each ⇓ a strict weakening)":

    bounded-violation  ⇒  limit  ⇒  bounded-ε-violation  ⇒  averaged

with **limit** written in product form: `gₙ(E^H_n(X) − t) ≳ₙ 0`. The second arrow
(limit ⇒ bounded-ε-violation) **fails for shrinking soft gates**. Counterexample
(hand-verified; `t = ¾`, `ε = δ = ⅛`):

    aₙ = t + δ/n  ⇒  gₙ = Ind_δ(aₙ − t) = 1/n,      pₙ = E^H_n(X) = 0.

- limit: `gₙ(pₙ − t) = −t/n → 0`, so `liminf ≥ 0` — **limit HOLDS** (vacuously, because the
  gate shrinks).
- bounded-ε-violation: `wₙ = gₙ·Ind_δ(t − ε − pₙ) = (1/n)·1` (the inner ramp saturates since
  `t − ε − 0 = ⅝ ≥ δ`), so `∑ wₙ = ∑ 1/n = ∞` — **FAILS**.
- averaged: gated average of `pₙ` is 0 < `t − ε − δ = ½` — **FAILS too**.

So a configuration satisfying the "limit" rung sits *below* both rungs the ladder places under
it. Intuitively this is a massive trust violation (A forecasts barely above `t` forever, H
parked at 0) that the product-form limit cannot see because `gₙ → 0` damps the product. Note the
configuration is *excluded by the actual Theorem's LI inputs* (calibration would force the gated
averages of `aₙ` and `pₙ` together), so the Theorem is untouched — only the ladder's *ordering
claim* is wrong, plus the accompanying prose "the top two ask that H's credence actually reach
t", which the product-form limit does not ask when the gate shrinks.

**Repair:** the implication holds under a support-nondegenerate gate — if `∃c>0: gₙ > 0 ⇒
gₙ ≥ c` (in particular for hard gates, or for the flagged-days reading "liminf over gate-on
days of `(pₙ − t)` ≥ 0"), then limit ⇒ `wₙ = 0` eventually ⇒ `∑ wₙ < ∞`. (Proof: on
`w`-support, `pₙ < t − ε` and `gₙ ≥ c` give `gₙ(pₙ − t) ≤ −εc`, contradicting
`liminf ≥ 0` beyond finitely many `n`.) The top implication (bounded-violation ⇒ limit) is
sound as written: summability of `gₙ·Ind_δ(t − pₙ)` forces `gₙ(t − pₙ)⁺ → 0` (split at
`t − pₙ ≥ δ` vs `< δ`; both give the product → 0).

---

Everything below is the question list. Global checks: none of these re-proves or re-skins
anything on the run2 GLOBAL OFF-LIMITS list (`Deference*`, `value_iff_totalTrust`,
`Legitimacy.*`, `SelfRefTarget.tracking_fails`/`no_exact_quote` as objects, the round-1 lab
Lean); where an off-limits object is *load-bearing*, the question cites it as a named input,
never re-ships it. The laundering ban is respected: in every LEAN-CORE target below, the
headline conclusion is computed/derived, never assumed; LI facts enter only as the named
hypotheses the corpus already treats as the trusted boundary — and never the target object
itself.

---

## Q1 — `calib-fails-diagonal`: Averaged calibration failure on the quote-referencing diagonal — the soft-gate hole, the counterexample, and the hard-gate repair

**Claim (acceptance target).** A standalone Lean file, sorry-free on the standard axioms, containing:
(i) **the counterexample**: for `aₙ = ½ + 2⁻ⁿ` (even `n`), `½` (odd `n`), with `Yₙ = 𝟙[aₙ ≤ ½]`
and `δ = ¼`: the soft high-gate weight sum `∑ softInd δ (aₙ − ½)` is bounded, the soft low gate
is identically 0, and the uniform average bias `(1/N)∑_{n<N}(aₙ − Yₙ) → 0` — certifying that
the three weightings named in `faithful-acceleration-scope.md` §4 steps 1–4 do **not** witness
miscalibration for this quote sequence (i.e. step 3's "hence aₙ ≤ ½" is a non sequitur);
(ii) **the repaired dichotomy**: for *every* `a : ℕ → ℝ` with `0 ≤ aₙ ≤ 1`, setting
`wₙ⁺ = 𝟙[aₙ > ½]`, `wₙ⁻ = 1 − wₙ⁺`, at least one of `∑w⁺, ∑w⁻` diverges, and on any divergent
one the weighted average bias `∑w b / ∑w` (with `bₙ = aₙ − Yₙ`) is ≥ ½ in absolute value for
all `N` with positive weight — so **no** quote sequence is calibrated against its own inverting
settlement once ledger-readable hard gates are admissible;
(iii) a prose section (labeled *interpretation*) arguing the hard gates are legal *patient*
C_A-weightings exactly because `gₙ` hard-decides (LI continuity binds only current-day prices),
and drawing the corollary: the scope note's conclusion stands, its proof needs this repair, and
"calibration breaks where tracking does" now has a mechanism (the hard settlement is what makes
the killing gate legal).

**Why it matters.** `faithful-acceleration-scope.md` §4 is the load-bearing argument for the
admissible-domain scope of the positive result (its §0 "bottom line"; pointwise §4.1; v6 §5.10);
faithful §8 obligation 3 rests on it. A hole in it — found and repaired — directly serves the
round's legitimacy focus: the inadmissible family is exactly li-deference §0.3-style corrupted
feedback (a target that reacts adversarially to the AI's own output), and this question makes
the "corruption ⇒ no calibration" implication kernel-solid instead of prose-with-a-gap. Also
note: the scope note's §7 recommended edits to faithful.md are *still unapplied* (faithful §4(II)
and the §5 Corollary still say "over all sentences"), so getting §4 right matters for the
pending sync.

**Modality.** MIXED (LEAN-CORE for (i)+(ii); PROSE for (iii); optional EXEC exact-rational check
of (i) as a warm-up).
**Difficulty.** Moderate — (ii) is pigeonhole + pointwise bounds; (i) is geometric-series and
cancellation arithmetic; the Lean is well within one session.
**Novelty risk.** Adjacent to `SelfRefTarget.no_exact_quote` (pointwise defect ≥ ½ — off-limits
as an object): this question must NOT re-prove it and does not — the target here is the
**averaged/weighted** statement, which exists only as (gapped) prose in scope §4 / pointwise
§4.1, plus the counterexample showing the published argument is broken, which exists nowhere.
Distinct from `TowerAccel.two_faces_distinct` (that witness *decouples* a from Y to show the
faces can coexist; this one is about the *coupled* diagonal where they die together).
**Shadow test.** The fake version proves only (ii) (easy) and omits (i), thereby hiding that
the published argument needed repair — or states (i) with hard gates where the scope note used
soft ones. The real version uses the corpus's own `softInd` definition for (i) and must exhibit
the bounded-vs-divergent contrast on the *same* sequence.

## Q2 — `corollary-deep-days`: Kernel-check the §5 Corollary (Theorem ⇒ averaged Total Trust)

**Claim.** A standalone Lean theorem, sorry-free: for `g p : ℕ → ℝ` with `0 ≤ gₙ ≤ 1`,
`0 ≤ pₙ ≤ 1`, `t ε δ > 0`, defining `wₙ := gₙ · softInd δ (t − ε − pₙ)` (the corpus's
`softInd`), if `∑ wₙ < ∞` (as: the partial sums are bounded) and `∑_{n<N} gₙ → ∞`, then for
every `η > 0`, eventually `(∑_{n<N} gₙ pₙ)/(∑_{n<N} gₙ) ≥ t − ε − δ − η` (the `AsympLE`-style
rendering of the liminf bound). The proof must *derive* the deep-days identity — on days with
`pₙ ≤ t − ε − δ` the inner ramp saturates, so `wₙ = gₙ` there — from the `softInd` definition,
not assume it. Plus the strictness witness separating the Corollary from the Theorem (a
configuration with the gated average ≥ `t − ε − δ` but `∑ wₙ = ∞` — the δ-gap the doc asserts
at faithful §5 "the implication is one-directional").

**Why.** faithful §5's Corollary is the statement that actually feeds Value (via
`value_iff_totalTrust`, classwise), and it is currently paper-only: `FaithfulAcceleration.lean`
stops at `¬(W → ∞)` and never derives the averaged bound. AUDIT §2.4 lists the trader chain
only. This is precisely "kernel-check a piece of the chain currently only on paper" — the last
arithmetic mile between the kernel-checked core and the headline classwise-Value reading (v6
§5.9).
**Modality.** LEAN-CORE.
**Difficulty.** Moderate — the split/saturation algebra is elementary but the
eventually-inequality bookkeeping (convergent numerator over divergent denominator) takes care;
one session.
**Novelty risk.** Could be accused of re-skinning `soft_total_trust` — it does not: that theorem
*concludes* `¬(W → ∞)`; this one *starts* from `∑ w < ∞` and derives a different statement (the
gated average bound), which no module contains. Not on the off-limits list. The fake version
takes "deep days have finite gate weight" as a hypothesis (laundering the saturation identity);
the real version proves `wₙ = gₙ` on deep days from `softInd`.

## Q3 — `weakening-ladder`: The §5 strength ladder's middle rung is false for shrinking gates — counterexample, repair, and full kernel-check of the ladder

**Claim.** A standalone Lean file, sorry-free, establishing about the four §5 rungs (all stated
with the corpus's `softInd` gates, `w` never abstract): (a) **the counterexample of Finding B**:
with `t = ¾`, `ε = δ = ⅛`, `gₙ = softInd δ ((t + δ/n) − t) = 1/n`, `pₙ = 0`: the limit rung
holds (`gₙ(pₙ − t) → 0`) while `∑ wₙ = ∞` and the averaged rung fails — so
"limit ⇒ bounded-ε-violation" is **false as stated**; (b) the **repaired implication**: if
additionally `∃ c > 0, ∀ n, gₙ > 0 → c ≤ gₙ`, then `liminf gₙ(pₙ − t) ≥ 0` implies `wₙ = 0`
eventually (hence `∑ wₙ < ∞`); (c) the **top implication** (bounded-violation ⇒ limit) proved
as stated; (d) the doc's two strictness witnesses (`pₙ − t = −1/n` with `g ≡ 1`; `pₙ ≡ t − ε/2`
with `g ≡ 1`) and the no-cancellation incomparability pair (a configuration with bare gated
mean ≥ t but `∑ w = ∞`, and one with `∑ w < ∞` but mean < t) formalized. Deliverable includes a
short prose note proposing the minimal wording fix to faithful §5 (state the limit rung over
gate-on days, or add the nondegeneracy proviso).

**Why.** The ladder is the freshest content in the corpus (three revisions this week) and it carries the *conceptual* weight of the section: it is the
official account of what "the weakening" gives up. Its middle rung being false as stated means
the current text misdescribes the relation between the Theorem and the unforceable per-day
statements — exactly the lens task "understand exactly what the weakening/seam is" and "sharpen
the weakening into either a proof or a counterexample." Files: `faithful-acceleration.md` §5
("The strengths of Total Trust…" block), echoed in v6 (a recent revision touched v6/pointwise
too — the executor should check where the ladder was propagated).
**Modality.** LEAN-CORE (+ a paragraph of PROSE for the wording fix).
**Difficulty.** Moderate — needs harmonic-series divergence (in Mathlib:
`Real.not_summable_one_div_natCast`) and liminf bookkeeping; the rest is ramp arithmetic.
**Novelty risk.** None of the four rungs' interrelations is formalized anywhere
(`FaithfulAcceleration.lean` proves the Theorem's trader core, not the ladder;
`TowerAndAcceleration.lean` is about tower-vs-averaged, a different pair). The fake version
proves only (b)–(c) with hard gates and skips (a), hiding the bug; the real version must
exhibit (a) with the *soft* gate the doc uses.

## Q4 — `direct-squeeze-lean`: Kernel-check the direct Steps-1–4 proof (the weighted-Cesàro squeeze) that the doc now presents as primary

**Claim.** A standalone Lean theorem, sorry-free, matching the §5 proof as rewritten by commit
a recent revision (which "prove[s] the theorem directly from ingredients (I)+(II), demote[s] the trader
to an illustration") — a proof route the Lean corpus does NOT currently check. Statement: for
`w Y a p q : ℕ → ℝ`, `ε > 0`, with `W_N = ∑_{n<N} wₙ`, given
(H1: A-calibration, named) `∑ w (Y − a) / W → 0`;
(H2: H-unbiasedness, named) `∑ w (Y − q) / W → 0` (with `qₙ` H's day-n estimate of its own
future price);
(H3: self-trust, named) `pₙ − qₙ → 0`;
(S: support) `wₙ ≥ 0` and `wₙ > 0 → aₙ − pₙ > ε` — *derived* from the `dsWeight` construction
as in `soft_total_trust_doublysoft`, not assumed abstractly;
then `¬ (W → ∞)`. The engine lemma to prove outright (new, reusable): **weighted Cesàro of a
null sequence** — `eₙ → 0`, `wₙ ≥ 0` bounded, `W_N → ∞` ⇒ `∑_{n<N} wₙ eₙ / W_N → 0` (this is
the doc's "the per-n self-trust gap is null and adds nothing to a divergent weighted average").
Then Steps 3–4: subtract, bound below by `ε` on the support, contradict. Non-vacuity witness
included. The writeup must state plainly how the trusted base *differs* from
`soft_total_trust_doublysoft`'s: the criterion bound `hbdd` is traded for H-unbiasedness (H2),
and say which the doc actually appeals to where.

**Why.** After a recent revision the doc's primary derivation and the kernel-checked artifact have
diverged: §9 checks the *trader* route (`hbias` + `hbdd`), while §5's displayed proof is the
two-unbiased-estimates squeeze (Step 2 explicitly invokes Expectation-Unbiasedness *for H*, a
different named input). Matching the formal artifact to the presented proof is exactly
"kernel-check a piece of the chain currently only on paper", and it surfaces an honest question
the doc currently blurs: whether Step 2's H-unbiasedness is a *weaker* or just *different*
trusted input than the criterion bound. (faithful §5 "Proof (sketch)" Steps 1–4; §9;
AUDIT §2.4.)
**Modality.** LEAN-CORE.
**Difficulty.** Moderate — the Cesàro lemma is the only real analysis; the rest is the
subtraction algebra. One session.
**Novelty risk.** Same conclusion as `soft_total_trust` — the novelty is the *hypothesis set*
(no `hbdd`; H2+H3 instead) and the reusable Cesàro lemma, neither in the corpus. To avoid
re-skin accusations the file must include the hypothesis-set comparison table. The fake version
smuggles the conclusion by assuming `∑ w (a − p)/W → 0` (Step 3's output) directly — banned;
H1/H2/H3 must be the only named inputs and Step 3 must be derived.

## Q5 — `echo-expert`: The echo expert — §5's guarantees are satisfiable with zero acceleration

**Claim.** (i) Kernel-checked: for the echo quote `aₙ := pₙ` (A relays H's *present* price),
the constructed weight vanishes identically — `dsWeight t ε δ p p = 0` for all `ε, δ > 0`
(support needs `p > t` and `p < t − ε` simultaneously) — so the §5 Theorem's conclusion
`∑ w < ∞` holds *identically*, with no appeal to calibration or the criterion; and the
Corollary's bound holds for the echo whenever its gate diverges (instantiate Q2's lemma or
prove directly). (ii) Paper-proved: the echo satisfies ingredient (II)'s conclusion — its
weighted bias against `Yₙ` vanishes — *because* Step 2 of §5's own proof says exactly that
H's present price is an unbiased forecast of `Yₙ` (cite; do not re-derive). (iii) Prose
(labeled interpretation): therefore nothing in §5 forces the *acceleration* in "faithful
acceleration" — every §5/§9 conclusion is met by an A that adds zero lookahead information —
so the note's §7 gloss "relay H's own eventual credence, only *sooner*" is an unforced
interpretive layer; state the minimal additional property that would exclude the echo (e.g.
forced earliness on the timely fragment, where the frozen construction lives) and whether any
corpus result forces it (expected answer: no — the negative note's 2b parenthetical already
names the echo as the degenerate tower-satisfier on quote-free families; this question extends
that one-line observation from the tower *equation* to the *positive result's entire
conclusion set*).

**Why.** Honesty about what the flagship positive result does and does not force. faithful §7
already concedes "not forced to be a better oracle," but still asserts the "sooner"; the echo
shows "sooner" is not forced either, which matters for how v6 §5.9 and li-deference's
"faithful accelerator" motivation may cite the theorem. It is also the cleanest possible
shadow-test on the theorem itself: a reader who believes §5 forces useful deference should be
confronted with the vacuous-satisfier. (faithful §5, §7; no-timely §4 "degenerate way to
satisfy the tower-equation"; pointwise §6.)
**Modality.** MIXED (small LEAN-CORE + PROSE).
**Difficulty.** Easy–moderate; the Lean is a few lines, the value is in the precise prose and
in resisting overstatement.
**Novelty risk.** The echo idea exists as one parenthetical in `no-timely-pointwise-tower.md`
§4 (about 2b's tower equation); extending it to the positive result's Theorem+Corollary and
kernel-checking the vacuity is new. Not adjacent to any off-limits object. The fake version
would dress `dsWeight p p = 0` alone as a discovery; the real deliverable is the (ii)+(iii)
analysis with the one-liner as anchor, and it must fairly quote §7's existing concession.

## Q6 — `legitimacy-continuity`: Settlement continuity as the legitimacy boundary — fixed-point calibratability vs. jump defect

**Claim.** A standalone Lean file + short note. Lean part, sorry-free: model a self-referential
settlement as `s : ℝ → ℝ` mapping `[0,1]` into itself — the target the quote must match is
`s(a)` (for the price-level liar χ, `s` is continuous ≈ constant ½; for the quote-referencing
diagonal, `s = antiInd`, the inverting step). Prove: (i) **legitimate ⇒ calibratable**: `s`
continuous on `[0,1]` with `MapsTo s I I` has a fixed point `a* = s(a*)` (IVT applied to
`s(a) − a`), so a best-responding quoter achieves *zero* pointwise defect; (ii) **quantitative
illegitimacy**: if `s` jumps across the diagonal — precisely, `∃ u < v` in `[0,1]` with
`s(x) ≥ x + J` for `x ≤ u` and `s(x) ≤ x − J'`… (executor to fix the cleanest hypothesis; the
target instance is: for any `s` with `inf_{a∈[0,1]} |s(a) − a| ≥ J`, every quote has defect
≥ J, and for `s = antiInd` compute `inf |s(a) − a| = ½` *as a computed infimum*, generalizing —
not re-shipping — the fixed-`a` bound); (iii) the two witnesses instantiated: `s ≡ ½`
(χ-like: fixed point ½) and `s = antiInd` (defect ½). Note part (labeled interpretation): this
is the faithful-acceleration admissible domain recast as li-deference §0.3 legitimacy — feedback
is *legitimate* exactly when the settlement responds continuously to the AI's output (no
self-fulfilling/self-defeating hard reaction), and the positive result's reach is co-extensive
with feedback legitimacy; connects §8 obligation 3 to the round's legitimacy focus.

**Why.** The round focus is legitimacy + deference, and the faithful-acceleration thread
contains the corpus's sharpest *formal* candidate for the legitimacy boundary — the
admissible/inadmissible split — but nowhere is the *positive* half (continuous settlement ⇒ a
consistent quote exists) stated, even though it is what makes "χ is benign" more than an
example. (scope §2–§3; faithful §6; li-deference §0.3.)
**Modality.** MIXED (LEAN-CORE + PROSE).
**Difficulty.** Easy–moderate: (i) is `intermediate_value_Icc` plumbing; (ii) needs a careful
statement to be non-trivial; the interpretive note must resist slogan-inflation.
**Novelty risk.** HIGH-ADJACENCY, handle with care: `SelfRefTarget.no_exact_quote` /
`residual_half` (pointwise defect ≥ ½ for `antiInd`) are established — (ii) must *cite/copy
with attribution* and add only the computed-infimum/jump generalization; if the executor finds
the generalization collapses to a re-skin, the honest fallback is (i)+(iii) alone (the
fixed-point half is genuinely absent from the corpus). Also must not relabel round-1
`Legitimacy.*` objects — different formal content (those are defect-sign/compliance objects,
not settlement-continuity).

## Q7 — `discharge-audit-4816`: Is the §8 "Discharged" claim honest? Statement-level audit of ingredient (II) against Theorem 4.8.16 as printed

**Claim.** A prose audit (table + verdict), against
`references/logical-induction/main.tex`'s literal statement of **Expectation Unbiasedness From
Feedback** (Thm 4.8.16, p.42 numbering per faithful §2), of every hypothesis needed for the §4
instantiation `Bₙ = ⌜E^H_{f(n)}(X)⌝`, `wₙ = Ind_δ(aₙ>t)·Ind_δ(E^H_n(X)<t−ε)`, deferral
`f(n) = 2ⁿ`. Each hypothesis gets a verdict HOLDS / HOLDS-WITH-LEMMA (state the missing lemma) /
MISMATCH (state the exact quote), specifically: (a) whether the theorem's weighting class
("P-generable divergent weighting", exact wording) admits a weight depending on the *same-day
own price* `aₙ` (the paper's own `Ind_δ(ℙₙ(φₙ)>½)` example — verify it is stated for the
weighting and not just discussed) AND on the *other market's* price `E^H_n(X)` (cross-market
feature legality — is H's price a legal feature of A's world as the paper defines features, or
does this need the observability construction of §8 obligation 1 to convert it into a decided
ledger fact first?); (b) the deferral condition's exact form — whether "each realized value
computable by the time the next weighted term arrives" (faithful's paraphrase) matches the
paper's condition when feedback for day `n` arrives at `2ⁿ` while day `n+1`'s term arrives at
`n+1` (prima facie a MISMATCH in the paraphrase: with `f(n)=2ⁿ` the feedback is NOT in before
the next term — determine whether the paper's actual condition (its deferral function `D`?) is
per-term-when-weighted, subsequence-based, or requires the "patient" reordering faithful
gestures at, and if the last, whether the paper proves the patient variant or it is a missing
lemma); (c) "determined via Γ" for the *coupled* `(H,A)` recursion — what Γ must prove and
whether the paper's definition tolerates the mutual-reference; (d) whether the theorem is
stated for LUV *sequences* varying with `n` (it is a `Bₙ` sequence theorem — verify) and for
the sub-inductor's expectations or only credences. Verdict format: either "Discharged is
honest, modulo obligations 1–2 exactly as §8 states" or a named list of what §8's 'construction
bookkeeping' actually still owes.

**Why.** faithful's Status line and §8 rest the whole "no longer lives or dies on gap 1" claim
on this discharge; v6 §5.9 and the pointwise explainer repeat it. Nobody — including AUDIT.md,
which audits only the Lean — has checked the discharge against the printed theorem. This is the
single highest-leverage skeptic task on the thread, and item (b) is a genuine prima facie
wrinkle: as paraphrased in faithful §2, the deferral condition looks violated by `f(n) = 2ⁿ`.
(faithful §2, §4(II), §8 "Discharged"; ground-rules corpus map bullet for main.tex.)
**Modality.** PROSE (reading a formal theorem statement; no Lean).
**Difficulty.** Moderate–hard: main.tex's §4.8 definitions (generable weightings, deferral
functions, "determined via Γ") must be traced exactly; but it is bounded, one-session work with
a crisp deliverable.
**Novelty risk.** None — this is an audit, not a theorem; duplication risk is nil (no prior
round touched the paper-matching). The fake version quotes the theorem's informal gloss and
rubber-stamps; the real version quotes the formal statement (hypothesis by hypothesis, with
line references into main.tex) and gives at least one nontrivial verdict — item (b) guarantees
there is something nontrivial to say either way.

## Q8 — `lagged-quotes`: Lagged-quote families and the exhaustiveness of the 2a/2b partition

**Claim.** (i) Kernel-checked: for the *lagged* diagonal `gₙ ↔ (aₙ₋ₖ ≤ ½)` (fixed lag
`k ≥ 1`), the best-response quote sequence defined by seeds `a₀..a_{k−1} ∈ [0,1]` and
`aₙ := 𝟙[aₙ₋ₖ ≤ ½]` for `n ≥ k` is well-defined, eventually 2k-periodic, and achieves **zero
tracking defect** — `aₙ = 𝟙[aₙ₋ₖ ≤ ½]`… wait, the *target* of day `n` is the settled value
`Yₙ = 𝟙[aₙ₋ₖ ≤ ½]`, which is computable at day `n`, so `aₙ := Yₙ` gives `|aₙ − Yₙ| = 0`
identically for `n ≥ k` — formalize exactly this (the recursion is well-founded because the
reference is to a strictly earlier, already-published quote; contrast: for `k = 0` the same
definition is circular and `no_exact_quote` gives defect ≥ ½). (ii) Prose: locate lagged-quote
families in `no-timely-pointwise-tower.md` §5's exhaustive partition. As written the partition
is "may reference A's quotes → 2a applies (tower FALSE, defect ≥ ½)" vs "quote-free → 2b". A
family whose atoms reference only *lagged* quotes may "reference A's quotes" yet the 2a
diagonal `gₙ ↔ (aₙ ≤ ½)` is not constructible in it, and (i) shows tracking is *satisfiable*
there — so the partition's first case, read literally, misclassifies lagged families. Determine
the correct amended boundary (proposal: "may reference quotes **not yet published** at quoting
time" vs not) and classify the lagged case: tracking satisfiable; is the *tower* on lagged
families forced, merely satisfiable, or 2b-underivable? (Expected honest answer: satisfiable;
forcedness reduces to whether A's criterion forces timely pricing of H's future credence *in a
decided sentence* — an instance of LI timely-learning whose per-family uniformity should be
flagged as open rather than asserted.) Deliverable: a boundary-case note amending §5's wording,
with the kernel-checked witness that lag strictly matters.

**Why.** The negative result's exhaustiveness claim (`no-timely-pointwise-tower.md` §5, echoed
in pointwise §2.4 "no third kind exists") is load-bearing for "the timely pointwise tower is
closed", and its case split is stated in terms coarse enough to misclassify a natural family.
Settling a boundary case of the partition is exactly the lens task, and the lagged family is
*the* natural probe (it is what "H reads A with bounded delay" makes expressible everywhere).
Also relevant to legitimacy: lag is precisely what makes self-referential feedback
non-corrupting (the settlement cannot react to the quote it settles), a clean formal cousin of
§0.3's non-corrupted-futures condition.
**Modality.** MIXED (small LEAN-CORE for (i) — a recursion + periodicity + zero-defect fact;
PROSE for (ii)).
**Difficulty.** Moderate. The Lean in (i) is elementary; the care is all in (ii)'s honest
classification (must not over-claim forcedness).
**Novelty risk.** `SelfRefTarget.tracking_fails` (k=0 case) is off-limits as an object — cited
as the contrast, not re-proved. No corpus document discusses lagged quote reference (checked:
no-timely §3 "Scope" defines quote-referencing by the atom `aₙ ≤ k` with same-day index;
neither scope note nor pointwise touches lag). The fake version proves (i) and declares the
negative result "wrong"; the real version notes that universal `Mart(H→A)` is untouched (the
same-day diagonal still exists in the full language — failure of one family suffices) and that
only the *per-family partition wording* needs amendment.

---

## Ranking and session-economics

Highest value first, by (finding-backed) × (one-session honest reachability):

1. **Q3** (weakening-ladder) — a verified bug in this week's edits; both directions of the fix
   are elementary Lean; fake version is detectable by absence of the soft-gate counterexample.
2. **Q1** (calib-fails-diagonal) — a verified gap in the scope note's load-bearing argument
   plus a thematically sharp repair; the legality prose must stay labeled as interpretation.
3. **Q7** (discharge-audit-4816) — the highest-leverage skeptic task; item (b) is a concrete
   prima facie mismatch to run down.
4. **Q2** (corollary-deep-days) — the missing kernel mile to the Value headline.
5. **Q4** (direct-squeeze-lean) — realigns the formal artifact with the now-primary proof;
   surfaces the hbdd-vs-H-unbiasedness trusted-base question.
6. **Q5** (echo-expert) — small, sharp, honesty-enforcing.
7. **Q8** (lagged-quotes) — clean boundary case; prose half needs discipline.
8. **Q6** (legitimacy-continuity) — the round-theme bridge; keep it modest (the IVT half is
   thin; the jump-generalization is where any real content lives).

**Claims-status ledger for this report.** Kernel-checked: nothing yet (this is a scout report).
Hand-verified exact arithmetic: Finding A's counterexample sums; Finding B's counterexample
(`g = 1/n`, harmonic divergence). Paper-proved (by me, above, at sketch level): the repaired
implications in Findings A(ii) and B(b), and the top-rung implication B(c). Interpretation:
hard-gate legality-as-patient-weighting (Q1(iii) — to be checked against the paper in Q7(a));
all legitimacy readings (Q6, Q8(ii) framing). I attempted to run the exact-rational checks in
Python this session; the sandbox's command classifier was temporarily unavailable, so the
verification above is by hand — executors should re-run it as their first act (a 20-line
`fractions.Fraction` script per finding).
