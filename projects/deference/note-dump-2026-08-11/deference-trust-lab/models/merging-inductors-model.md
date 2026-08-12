# Fast-Student / Slow-Teacher: a toy formal model of the merge `B_t`

*Thread: Eisenstat's slow-trusted `H` (humans) + fast-untrusted `A` (AI) →
`B_t(φ) := 𝔼^A_t(⌜ℙ^H_{f(t)}(φ)⌝)`. AGENDA conjecture: with good feedback + fast `f`,
(i) `B` is a logical inductor and (ii) `H` endorses `B` (LI-weak sense).*

*[Attribution note, 2026-08-10: this model's information structure is the lab construal, not the
setup Sam Eisenstat intended (AI reads human beliefs immediately; humans see AI beliefs only at a
delay). See `wiki/eisenstat-conjecture-attribution.md`.]*

This note develops **ideate idea 3/4** (the keystone) into a precise toy model. It pins down:
(a) the LI criterion `B` must satisfy and why `B` inherits inductor-ness from `A`;
(b) the exact statement of "`H` endorses `B`" and its reduction to a cross-agent martingale,
citing v2 §10; (c) the smallest computable toy model, with a **worked, machine-run micro-example**
(`merging_inductors_micro.py`, all checks PASS).

Every claim is flagged **PROVED / SKETCHED / CONJECTURE / INTERPRETATION**. Counterexamples and
failure modes are surfaced. Grounding: v2 §0.3 (theorem statements), §3 (Value proof), §10
(external experts, the `LUV-Total-Trust` premise); LI paper `thm:wub`/`thm:wubexp` (§4.5, "good
feedback"), `thm:ccee`/`thm:cee` (§4.12), Def. "determined via Γ" (§4.x).

---

## 0. Standing setup (all hypotheses explicit)

- A shared theory `Γ` (representing computable functions). Two logical inductors over `Γ`:
  `H = (ℙ^H_n)`, slow & trusted; `A = (ℙ^A_n)`, fast & untrusted. Both satisfy the LI criterion
  (no `ℙ`-efficient trader exploits their own prices against `𝒫𝒞(Γ)`).
- A strictly increasing **deferral function** `f` (`f(t)>t`, computable in `poly(f(t))`).
- The **merge**: `B_t(φ) := 𝔼^A_t(⌜ℙ^H_{f(t)}(φ)⌝)` — `A`'s day-`t` *expectation of the LUV that
  names `H`'s day-`f(t)` price of `φ`*. (Corner quotes essential: `ℙ^H_{f(t)}(φ)` is a real number;
  `⌜ℙ^H_{f(t)}(φ)⌝` is the LUV naming it, and `𝔼^A_t(⌜·⌝)` is type-correct — v2 §0.2.)
- `μ_t := ℙ^H_{f(t)}(φ_t)` is the **realized** human future price (the quantity `A` estimates).
- A `ℙ^H`-generable divergent weighting `w = (w_t)`, `w_t∈[0,1]`, whose support sits in the image of
  `f`. This `w` is the "subsequence" on which everything is asserted.

---

## (a) `B` as a logical inductor: the criterion and the inheritance argument

### (a.1) What "`B` is a logical inductor" must mean — two readings (INTERPRETATION)

Per ideate idea 1, "`B` is a logical inductor" is ambiguous between a **behavioral** reading
(`B` inherits coherence / timely learning / calibration) and a **generative** reading (`B` satisfies
the LI *criterion*: no `ℙ^B`-efficient trader exploits the price path `B_t(·)` against `𝒫𝒞(Γ)`).
The honest target is **behavioral and feedback-gated**, for a reason that is now a clean negative
result:

> **Negative fact (CONJECTURE, but well-motivated — the "no-feedback hole").**
> The bare derived sequence `B` does **not** satisfy the LI criterion unrestricted. `B`'s prices are
> a poly-time function of `ℙ^A`, not `B`'s own market; on the **unobservable class** (φ for which no
> poly-time machine decides `μ_t` before `A` must price it — flourishing, values, ethics: AGENDA),
> the good-feedback hypothesis is *vacuous* and `B_t(φ_t)=𝔼^A_t(⌜μ_t⌝)` can be anything `A` likes.
> A trader that knows `A`'s bias there exploits `B`. **So `B` is at best an inductor *on the
> good-feedback subsequence* and unconstrained off it.** This is the same boundary as v2 §10.4 +
> Weatherson's Coin (v2 §6).

### (a.2) The positive inheritance: `B` tracks `H`'s limit on `w` (SKETCHED)

> **Proposition A (SKETCHED, LI-paper rigor).** Suppose `(⌜μ_t⌝)` — as observed in `A`'s market — is
> a `BLCS` sequence **determined via Γ** *relative to the realized human prices* (see the standpoint
> caveat below), and `w` allows **good feedback** for `A` on `(μ_t)`: i.e. `μ_t=ℙ^H_{f(t)}(φ_t)` is
> computable in time `O(f(t+1))` (the "fast enough `f`" clause, = `thm:wubexp`'s deferral-time
> hypothesis applied to `A` watching `H`). Then on `w`,
> $$\frac{\sum_{i\le t} w_i\,(B_i(φ_i)-μ_i)}{\sum_{i\le t} w_i}\ \eqsim_t\ 0
>   \qquad(\text{$A$ is $w$-unbiased about $H$'s realized future price}),$$
> and consequently the `w`-average of `B_t(φ_t)` tracks the `w`-average of `μ_t` — hence whatever
> limit `H`'s prices have, `B` inherits it on `w`. *`B` tracks the human's limit.*

**Proof sketch.** This is *literally* `thm:wubexp` applied to `A` with target LUV-sequence
`(⌜μ_t⌝)` and weighting `w`: good feedback + fast `f` are exactly its two hypotheses (deferral-time
bound + `ℙ^A`-generable divergent `w` with support in `im f`). The conclusion is the displayed
`w`-mean-zero bias. **Gap (flag):** `thm:wubexp` requires the target to be **determined via Γ**
(Γ proves a definite value, §1.806 of the LI .tex). But `μ_t=ℙ^H_{f(t)}(φ_t)` is a *market price of
another machine*, which Γ does **not** prove a value for. So `thm:wubexp` does not apply
*verbatim*; one must instead read `μ_t` as `A`'s **empirical observation** of `H`'s output and invoke
the *recurring/feedback* unbiasedness for an `ℝ`-LUV whose value `A` can decide in time `O(f(t+1))`
by *simulating/observing* `H`. This is morally `thm:wubexp` with "determined via Γ" replaced by
"`A`-decidable in `O(f(t+1))`", which is the natural reading of "good feedback about another agent."
**Naming this replacement precisely is the residual SKETCHED→PROVED gap of part (a).** It is the
*same* standpoint object that reappears, harder, in part (b).

---

## (b) "`H` endorses `B`": exact statement and reduction to a cross-agent martingale

### (b.1) The endorsement statement (v2 §10 Value, with `E := B`)

Take a `Γ`-efficient menu `𝒪_t = {O^1_t,…,O^k_t}` of bounded `[0,1]`-LUVs. The selector uses the
**merge** `B` as its expert estimate: `m^j_t := B_t(O^j_t)`, `α^j_t := softmax(m^·_t/δ_t)`,
`δ_t↓0`, `Ŝ_t := Σ_j α^j_t O^j_t`. Then:

> **Endorsement = Value (LI form) with expert `B`, gated by `w` (the goal of the thread).**
> $$\boxed{\ \mathbb 𝔼^H_t(\widehat S_t)\ \gtrsim_w\ \mathbb 𝔼^H_t(O^i_t)\quad\text{for each fixed }i\ }$$
> where `≳_w` is the `w`-weighted-average version of `≳_t`. *"On the good-feedback subsequence, `H`
> would rather hand any bounded decision to `B` (the AI-mediated read of `H`'s own future) than
> commit now to a fixed bet."*

By v2 §10.1, this entire statement follows from the **novice `H`'s own coherence** (lines 2/4/5 of
the §3 chain: linearity + softmax gap + provability-induction, all expert-agnostic — see v2 §10.1
table) **plus one** expert-specific premise:

> **LUV-Total-Trust (`H → B`), the §10 premise (v2 §10.1).** For every `ℙ^H`-generable weight
> `w_t∈[0,1]`: `𝔼^H_t(⌜X_t·w_t⌝) ≂_t 𝔼^H_t(⌜B_t(X_t)·w_t⌝)`.

Two structural conditions from §10 must hold for the premise to even be *well-typed* (idea 2):
(i) **`H`-observability** — `(B_t(O^j_t))_t` must be `ℙ^H`-generable (else `H` cannot form `α^j` and
the premise is unstatable; v2 §10.4). For the merge this is *communicational*: `A` **publishes** `B_t`
and `H` reads it as an expressible feature (LI Def. 4.3 "expressible features" allow continuous
dependence on externally-posted numbers). (ii) **boundedness** — `B`'s valuations are `[0,1]`-LUVs
(else Coin-type failure, v2 §6).

### (b.2) The reduction (idea 3, the technical heart): good feedback ⇒ the §10 premise on `w`

> **Proposition B (SKETCHED Hop 1 + CONJECTURE Hop 2).** Under (a.2)'s good-feedback hypothesis and
> `H`-observability, the §10 premise holds *on `w`*:
> `𝔼^H_t(⌜𝟙(φ_t)·w_t⌝) ≂_w 𝔼^H_t(⌜B_t(φ_t)·w_t⌝)`, via a two-hop chain
> $$\mathbb 𝔼^H_t(⌜𝟙(φ_t)\,w_t⌝)\ \underset{\text{Hop 1}}{\eqsim_w}\ \mathbb 𝔼^H_t(⌜ℙ^H_{f(t)}(φ_t)\,w_t⌝)\ \underset{\text{Hop 2}}{\eqsim_w}\ \mathbb 𝔼^H_t(⌜B_t(φ_t)\,w_t⌝).$$

- **Hop 1 (SKETCHED — *free*).** This is `H`'s **own** `thm:ccee`/`thm:ceu` (conditional martingale):
  `𝔼^H_t(⌜𝟙(φ)·w⌝) ≂_t 𝔼^H_t(⌜ℙ^H_{f(t)}(φ)·w⌝)`. `H` already expects today whatever it will price
  on day `f(t)`. No cross-agent content; it is the self-case engine of v2 §3.
- **Hop 2 (CONJECTURE — the genuine open step, the "standpoint shift").** Swap `ℙ^H_{f(t)}(φ)` for
  `B_t(φ)=𝔼^A_t(⌜ℙ^H_{f(t)}(φ)⌝)` *inside `H`'s expectation*. Good feedback (a.2) makes the residual
  `μ_t−B_t(φ_t)` `w`-mean-zero **from `A`'s standpoint**; we need it `w`-mean-zero **from `H`'s
  standpoint** after weighting by the `ℙ^H`-generable `w`.

**Where Hop 2 can break (flag hard).** `A`-unbiasedness is an `A`-relative `≂`; substituting it under
`𝔼^H_t(·)` requires `H` to *also* regard `A` as unbiased about `H_{f(t)}`. Two routes (ideate idea 3):
- **Route A (mutual good feedback, clean but strong).** Assume the good-feedback + deferral-time
  bounds hold simultaneously for `H`-watching-`A` *and* `A`-watching-`H`. Both martingales fire; Hop 2
  is a triangle inequality on `w`-averages. **Discharges §10's premise** — but assumes mutual
  observability, which on the unobservable class is exactly what fails.
- **Route B (`H` trusts `A` only about `H`'s own future, weak but relocates).** Add the *narrow*
  premise `H → A` LUV-Total-Trust **restricted to the LUV class `{⌜ℙ^H_{f(t)}(φ)⌝}`**. Then Hop 2 is
  legal by definition. This does **not** discharge §10's premise from nothing — it **relocates** it to
  a strictly narrower class ("`H` need only trust `A`'s estimates of `H`'s *own* verdicts, not of the
  world"). **Still genuine progress:** it isolates the minimal trust the human must extend.

**Status of the headline conjecture.** *If* Hop 2 is legal under Route A or B, then by v2 §10
composition (lines 2/4/5 free; line 3 = Hop-1∘Hop-2 on `w`; line 6 = line 3 at `w≡1`):

> **Central claim (CONJECTURE; reduces to SKETCHED under Route A or B).** Under good feedback + fast
> `f` + `H`-observability + boundedness, `H` endorses `B` on the good-feedback subsequence `w`
> (boxed Value statement of (b.1)). Equivalently: *the AGENDA conjecture (ii) is v2 §10 Value with the
> constructed expert `B`, and "good feedback + fast `f`" is exactly the hypothesis set that discharges
> §10's single cross-agent premise — modulo the Hop-2 standpoint shift, which is the one true gap.*

**The named gap.** Hop 2's legitimacy across the `ℙ^A`→`ℙ^H` standpoint shift. It is *not* obviously
a known LI move; it could harbor a vacuity (if `w` is forced trivial) or a smuggled immodesty (if it
secretly assumes `H` is certain of `A`'s estimate). Resolving Route-A-vs-B **is** the deliverable;
this note pins the dichotomy but does not close it.

### (b.3) The boundary is sharp, not hand-waved (INTERPRETATION)

Endorsement holds **only on `w`**. Off `w` (the unobservable class), there is *no* endorsement —
matching the (a.1) hole and AGENDA's own caveat that humans need trust "in circumstances that do not
involve good feedback." The merge delivers **feedback-gated endorsement**: humans justifiably defer
to `B` *exactly where they have good feedback*, by the *same* Value/Total-Trust equivalence as
deferring to one's own future self. That is a genuine, if bounded, "humans can trust AI" statement,
and its boundary is exactly where the agenda says the hard problem lives.

---

## (c) The smallest toy model + a worked, machine-run micro-example

**File:** `models/merging_inductors_micro.py` (Python, ran — all checks PASS; see output below).

We cannot build real inductors, so we model `H` and `A` as **price sequences chosen to satisfy the
relevant LI asymptotic identities**, and check the *model identities* numerically. This is a **model
verification, not a proof** (status of (b) remains CONJECTURE/SKETCHED).

**Ingredients (explicit `f`, few sentences).**
- One tracked sentence `φ`; `f(t)=2t`; `N=4000` days; tail = last 25% (surrogate for `≂_t`).
- `H`'s price converges: `ℙ^H_n(φ)=0.7 + 0.4 sin(n)/(1+0.5n) → 0.7` (an LI-plausible converging,
  oscillating path; limit `p_∞=0.7`).
- **Good-feedback** merge `B_good(t) = μ_t + 0.3 cos(3t)/(1+0.2t)` — `A` unbiased for the realized
  `μ_t=ℙ^H_{2t}(φ)`, with a `w`-mean-zero shrinking noise (`thm:wubexp` regime).
- **No-feedback** merge `B_bad(t) = μ_t − 0.25` — a *persistent* downward bias `w`-averaging does
  **not** kill (the unobservable class: `A` systematically lowballs `H`).
- 2-option menu `O^1=μ_t` ("φ true"), `O^2=1−μ_t` ("φ false"); selector
  `α^j=softmax(m^j/δ_t)`, `m^1=B_t`, `m^2=1−B_t`, `δ_t=1/√(t+1)↓0`; `Ŝ_t=Σ_j α^j O^j`; `w≡1`.

**Results (printed by the script — verbatim).**
```
(a) tail w-avg of B_t (good feedback)        = 0.7000   → tracks p_inf=0.70   [PASS]
    tail w-avg of B_t (NO feedback / biased)  = 0.4500   → fails to track       [PASS]
(b) good feedback:  E^H(Shat)=0.7000 ≥ O^1=0.7000, O^2=0.3000      [Value PASS]
    no  feedback:   E^H(Shat)=0.3011 < O^1=0.7000 (= O^2=0.3000)   [Value FAILS on O^1]
OVERALL: good-feedback endorsement holds, no-feedback endorsement fails as predicted  [PASS]
```

**Reading the micro-example.** On good feedback, `B` tracks `H`'s limit, the softmax picks the right
bet, and `𝔼^H(Ŝ)=0.70 ≥` every option — **Value/endorsement holds**, exactly part (b.1) with
Hop 2 satisfied (the noise is `w`-mean-zero from both standpoints). On no feedback, `A`'s persistent
`−0.25` bias drags `B` to ~0.45 (below the `0.5` decision boundary): the softmax then *concentrates on
the WRONG option* `O^2`, so `𝔼^H(Ŝ)≈0.30 < 0.70 = 𝔼^H(O^1)` — **endorsement FAILS on `O^1`**, the
sharp boundary of (a.1)/(b.3). The single failure mode the model exhibits — "biased estimate ⇒ wrong
selector ⇒ Value violated" — is precisely the mechanism the Lean candidate isolates.

**One-big-lie (idea 6, the honest caveat).** The script also shows a single `t*` where a treacherous
`B_{t*}=0` (vs honest `0.70`) gives a single-round error of `0.70` that the `≂_w`-**average** Value
statement does **not** bound. Asymptotic endorsement is *silent about any single high-stakes round*;
"humans surviving the turn" is the unmodeled assumption (AGENDA). **This is structural, not a detail.**

---

## (d) Lean candidate (UNCHECKED — for the Lean-verify agent)

**File:** `lean/merging-inductors.lean`. Faithful, tiny, finite real-arithmetic. It does **NOT**
attempt the cross-agent martingale (un-Lean-statable without LI feedback machinery — would smuggle
the conclusion). It isolates the **mechanism** of part (c)'s no-feedback failure:

- `S μ σ := σ·μ + (1−σ)·(1−μ)` — the realized 2-option return as a function of the softmax weight `σ`
  on `O^1=μ` (`σ` is applied to the *estimate* `b=B_t(φ)`, not the truth `μ`).
- `bias_only_hurts` (MAIN): if `μ ≥ 1/2` and the selector is monotone in the estimate (`σb ≤ σc`),
  then `S μ σb ≤ S μ σc`. **Plain English:** raising `A`'s estimate toward/above the truth can only
  *raise* the deferred value; a persistent *downward* feedback bias can only *lower* it below the
  unbiased value. Good feedback (`b→μ`) maximizes the return; this is *why* endorsement tracks bias.
- `reversal_when_mu_small`: with `μ=0` the monotonicity *reverses* (`S 0 σ = 1−σ`), certifying the
  `μ≥1/2` hypothesis is **load-bearing, not smuggled**, and the MAIN lemma is **non-vacuous**.

**Faithfulness audit (the most important thing).** The lemma captures *only* "a biased estimate
degrades the softmax-deferred decision monotonically" — the engine of part (c)'s no-feedback hole. It
does **NOT** capture, and does not claim: `B` is an inductor; the cross-agent martingale (Hop 2); any
`≂` asymptotics; any LI theorem. It does **not** assume `S ≥ μ` (that *is* the Value conclusion, which
lives in the *confirmed* `LeanDeference.softmax_lower_bound`); it assumes only `σ` monotone+bounded
and `μ≥1/2` and concludes the orthogonal "bias only hurts" fact. We model `σ` as **any** monotone
selector (the softmax is one, monotone in `b` for fixed `δ` — proved in confirmed Lean, not re-proved
here), keeping the file minimal. **Quantifiers/sign checked by `reversal_when_mu_small`.** Marked
UNCHECKED; the Lean-verify agent must confirm `#print axioms` shows only
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

---

## (e) Summary of statuses

| object | claim | status |
|---|---|---|
| (a.1) no-feedback hole | `B` not an inductor unrestricted; only on `w` | CONJECTURE (well-motivated) |
| (a.2) Prop A | `B` `w`-tracks `H`'s limit via good feedback | SKETCHED (gap: "determined via Γ" → "`A`-decidable") |
| (b.1) endorsement | = v2 §10 Value with expert `B`, gated by `w` | reduction is SKETCHED; truth conditional on (b.2) |
| (b.2) Hop 1 | `H`'s own `thm:ccee` | SKETCHED (free) |
| (b.2) Hop 2 | `A`-unbiasedness substituted under `𝔼^H` | **CONJECTURE — the one true gap** (Route A or B) |
| central claim | AGENDA (ii) = §10 with `B`, discharged by good feedback + fast `f` | **CONJECTURE; reduces to SKETCHED under Route A/B** |
| (c) micro-example | model identities hold on `w`, fail off `w` | numerically verified (PASS) — model check, not proof |
| (d) Lean `bias_only_hurts` | bias only hurts the softmax-deferred decision | candidate, **UNCHECKED** |

**The deliverable** is the precise reduction "AGENDA merge = v2 §10 with constructed expert `B`" plus
the isolation of the **single open step** (Hop 2 / Route-A-vs-B standpoint shift) and the **sharp
negative boundary** (no endorsement off the good-feedback subsequence), demonstrated numerically and
mechanistically (Lean) but not yet proved across the standpoint shift.
