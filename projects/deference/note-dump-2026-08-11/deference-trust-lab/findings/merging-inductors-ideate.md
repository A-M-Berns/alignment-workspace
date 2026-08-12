# Fast Student / Slow Teacher — Merging Logical Inductors (Ideate)

*Thread: Eisenstat's slow-trusted `H_t` (humans) + fast-untrusted `A_t` (AI) → derived
`B_t(φ) := 𝔼^{A}_t(⌜ℙ^{H}_{f(t)}(φ)⌝)`. Conjecture (AGENDA "Fast Student, Slow Teacher"):
with good feedback + fast-enough `f`, (i) `B_t` is a logical inductor, and (ii) `H_t` weakly
endorses `B_t`.*

*[Attribution note, 2026-08-10: this thread's rendering does not match the information structure
Sam Eisenstat intended (AI reads human beliefs immediately; humans see AI beliefs only at a delay),
so its negative findings — notably Idea 1's "no-feedback hole" — are about the lab construal, not
his conjecture. See `wiki/eisenstat-conjecture-attribution.md`.]*

Every claim is flagged **PROVED** / **SKETCHED** (LI-paper-level rigor) / **CONJECTURE** /
**INTERPRETATION**. Counterexamples and failure modes are surfaced, not hidden. Source grounding:
v2 §0/§3/§5.2/§10; LI paper §4.5 (`thm:wub` `thm:wubexp`, "good feedback"), §4.8, §4.12
(`thm:cee` `thm:ccee` `thm:st`); 00-orientation Q4/Q5/Q7.

---

## 0. The one bridge that organizes everything (INTERPRETATION — make explicit)

The merge is **v2 §10 run with two agents and a name-swap.** In §10 the *novice* `N`
(operator `𝔼_n`) defers to an *external expert* `E` whose estimate is the LUV `𝔼_exp(X)`; the
**entire** Value proof goes through from *one* cross-agent premise:

> **LUV-Total-Trust (N → E).** for every `ℙ_N`-generable weight `w_n∈[0,1]`,
> `𝔼^N_n(⌜X_n·w_n⌝) ≂ₙ 𝔼^N_n(⌜𝔼_exp(X_n)·w_n⌝)`  (v2 §10.1, the only expert-specific line).

The merge instantiates this with a **specific, constructed expert**:

| §10 object | merge instantiation |
|---|---|
| novice `N`, operator `𝔼^N_n` | the **human** `H`, operator `𝔼^H_t` (slow, trusted) |
| external expert estimate `𝔼_exp(X)` | `B_t(X) := 𝔼^A_t(⌜𝔼^H_{f(t)}(X)⌝)` — *A's estimate of the human's future estimate* |
| novice-observability of `E` | `B_t` is `ℙ^H`-… **no** — `B` is `ℙ^A`-generable; this asymmetry is the crux (§ idea 2) |
| cross-agent martingale (premise) | the conjunction of (a) **A's own** `thm:cee`/`thm:ccee` toward `H_{f(t)}` and (b) **A unbiased about H via good feedback** (`thm:wub`/`thm:wubexp`) |

So the conjecture is **not** a new kind of theorem; it is the claim that *good feedback +
fast `f`* is exactly the hypothesis set that **discharges the §10 cross-agent premise for this
particular constructed expert.** That reframing is the main contribution of this note, and it tells
us where every difficulty must live: in whether `B`'s defining double-expectation
`𝔼^A(⌜𝔼^H_{f(t)}(·)⌝)` can be made to satisfy `H`-directed LUV-Total-Trust.

Two structural facts immediately inherited from §10/§5.2:
- §10.3(b): a *modest* expert deferred to *cleanly* must be infinite-frame — so `B` being an inductor
  (idea 1) and `H` endorsing it (idea 4) are not independent wishes; clean modest endorsement
  **forces** `B` to be a continuum object. Good news: `B` is built from inductors, so it is.
- §10.4: cross-agent LUV-Total-Trust is **NOT free** between two arbitrary inductors (unlike the
  self-case where it is `thm:ccee`). The whole thread is the search for *sufficient conditions*
  (good feedback; corrigibility bootstrap) that recover it. This is exactly orientation-Q5.

---

## Idea 1 — "`B_t` is a logical inductor" is a TWO-LAYER claim; separate them (SKETCHED + CONJECTURE)

**The trap.** "`B_t` is itself a logical inductor" (AGENDA) is ambiguous between:
- **(1a) `B` inherits good *properties*** (coherence-in-limit, timely learning, self-trust,
  calibration) — a *behavioral* reading; or
- **(1b) `B` satisfies the logical-induction *criterion*** — no `ℙ^B`-efficient trader exploits the
  price sequence `B_t(·)` against `𝒫𝒞(Γ)` — a *generative* reading.

These come apart, and conflating them is the single biggest soundness risk in the thread.

**Candidate Proposition 1a (SKETCHED).** Let `H`, `A` be logical inductors over the same `Γ`,
`f` a strictly increasing deferral function, and define `B_t(φ) := 𝔼^A_t(⌜ℙ^H_{f(t)}(φ)⌝)`. Then:
- (coherence in the limit) if `ℙ^H_∞` exists, and `A` is asymptotically unbiased about `ℙ^H_{f(t)}`
  on a `ℙ^A`-generable weighting via good feedback (`thm:wub` applied to `A` with target sequence
  `ℙ^H_{f(t)}(φ_t)`), then `B_t(φ_t) ≂ₜ ℙ^H_∞(φ_t)` on that weighting — `B` tracks the *human's
  limit*, hence inherits whatever coherence `H_∞` has.

*Why plausible.* `thm:cee` for `A`: `𝔼^A_t(⌜𝔼^A_{g(t)}(X)⌝) ≂ₜ 𝔼^A_t(X)`. Good feedback
(`thm:wub`/`thm:wubexp`) for `A` about the **observable** sequence `ℙ^H_{f(t)}` says: on a
`ℙ^A`-generable divergent weighting whose support sits in the image of a deferral function, `A`'s
estimate of `ℙ^H_{f(t)}(φ)` is *unbiased* for the realized value `ℙ^H_{f(t)}(φ)` — provided that
realized value is **computable in time `O(f(t+1))`**, i.e. `f` outruns how long `H` needs (the
"fast enough `f`" of the conjecture is *literally* the `thm:wub` deferral-time hypothesis applied to
`A` watching `H`). This is why "good feedback + fast `f`" is the right pair of words: they are the
two clauses of `thm:wub`.

**Candidate Proposition 1b (CONJECTURE — and I expect it is FALSE as literally stated).** `B`,
as a *bare derived sequence*, does **not** in general satisfy the LI criterion. Reason: the
criterion is a *no-Dutch-book against `ℙ^B`-efficient traders* statement, but `B`'s prices are
**not its own market** — they are a poly-time function of `ℙ^A` prices. A trader efficient relative
to `B` may be efficient relative to `A`; but `B` could still be exploitable on sentences where `A`
is *fast and confident but wrong about `H`* in a way that is `ℙ^B`-detectable but only on a
*sparse* (non-good-feedback) subsequence. The criterion quantifies over **all** efficient traders
and **all** sentences; good feedback only controls a `ℙ^A`-generable *weighted* subsequence.

> **Failure mode (CONJECTURE, the "no-feedback hole").** Take `φ_t` from the unobservable class
> (human flourishing / values / ethics — AGENDA, orientation-Q7): no poly-time machine decides
> `ℙ^H_{f(t)}(φ_t)` before `A` must price it, so the good-feedback hypothesis is **vacuous** on this
> subsequence, and `B_t(φ_t) = 𝔼^A_t(⌜ℙ^H_{f(t)}(φ_t)⌝)` can be anything `A` likes. A trader that
> knows `A`'s bias on this class exploits `B`. So 1b fails *exactly* on the sentences humans most
> need to trust AI about. **This is the central negative result of the thread and must be stated
> loudly.**

**Bearing on trust.** The honest version of "`B` is a logical inductor" is **conditional**:
`B` behaves like an inductor *on the good-feedback subsequence* and is *unconstrained off it*.
Humans can justifiably trust `B` only where they have (or can manufacture — idea 5) good feedback.
The merge does **not** manufacture trust on unobservables for free; that is the honest boundary, and
it is the same boundary as v2 §10.4 + Weatherson's Coin (v2 §6).

**Cleanest setting.** Logical induction, two inductors over one `Γ`, plus the `thm:wub`/`thm:wubexp`
machinery verbatim. **Hardness:** 1a is SKETCHED-provable now (it is `thm:cee` + `thm:wubexp`
bookkeeping, ~LI-paper rigor). 1b is genuinely hard and probably *false unrestricted*; the
*positive* statement is "B restricted to the good-feedback subsequence is exploitation-free," which
is medium. **This separation is itself the deliverable.**

---

## Idea 2 — The observability asymmetry is load-bearing: `B` must be `ℙ^H`-watchable for `H` to endorse it (SKETCHED, sharp)

v2 §10.4: "If the novice cannot generate `α^j_n` from the expert's prices, lines 2/4 and the
premise cannot even be *stated*." In the merge the novice is `H` and the expert is `B`. But `B` is
defined as a function of `ℙ^A`, not `ℙ^H`. **So §10's observability clause demands: `B_t`'s outputs
must be `ℙ^H`-generable** for `H` to even *form* the deferral weights `α^j` and for LUV-Total-Trust
to be a well-typed premise.

**Candidate Definition (observability of the merge).** `B` is **`H`-observable** if the sequence
`(B_t(O^j_t))_t` is `ℙ^H`-generable (poly-time computable from `H`'s own day-`t` prices). Then the
§10 generalized Value proposition applies *verbatim* with `E := B`: if additionally `H → B`
LUV-Total-Trust holds, `H` defers all bounded decisions to `B` (Value, LI form).

**The catch (INTERPRETATION, important).** `H`-observability of `B` is *prima facie* the wrong
direction: `B` is the *fast* AI's read of `H`'s future, so making `B` `ℙ^H`-generable seems to
require the slow human to recompute the fast AI. **Resolution candidates:**
- (i) `H` need not *compute* `B`; it needs `B`'s outputs to be `ℙ^H`-generable *features*, which
  can hold if `A` **publishes** `B_t` and `H` reads it as data (a `ℙ^H`-expressible feature is
  allowed to depend continuously on externally-posted numbers, just like market prices — LI Def
  4.3-ish, "expressible features"). Then observability is *communicational*, not computational.
- (ii) This is exactly the "slow trusted reasoner reading a fast untrusted one's report" structure;
  it matches the lab's *"slow trusted vs fast untrusted"* agenda item directly and connects to
  `udt-representation-theorem/communication-trust-translated.md` (trust-translation across agents).

**Bearing on trust.** This pins down a *necessary structural condition* for justified trust that is
easy to overlook: **the trusted party must be able to watch the trusted-on outputs as features.**
Trust in an unwatchable `B` is not even *expressible*, let alone derivable. **Hardness: low-medium**
— it is a definitional clean-up of §10.4, fully formalizable, and it sharpens what "good feedback"
must deliver (it must make `B` both *accurate* and *`H`-watchable*).

---

## Idea 3 — "Good feedback" ⇒ cross-agent LUV-Total-Trust on the subsequence (SKETCHED → CONJECTURE; the technical heart)

This is the load-bearing reduction. **Make precise the claim "good feedback discharges §10's premise."**

**Candidate Proposition 3 (CONJECTURE, reducible to SKETCHED).** Let `w` be a `ℙ^H`-generable
divergent weighting whose support lies in the image of a strictly increasing deferral function `f`,
and suppose `ℙ^H_{f(t)}(φ_t)` is computable in time `O(f(t+1))` (so `w` *allows good feedback on*
`(φ_t)` for the **human's own** future, per `thm:wub` applied to `H`). Then on the `w`-weighting,
*human-directed cross-agent LUV-Total-Trust* holds for `B`:
$$ 𝔼^H_t(⌜𝟙(φ_t)·w_t⌝) \ ≂_w\ 𝔼^H_t(⌜B_t(φ_t)·w_t⌝),$$
where `≂_w` means the `w`-weighted average difference `→ 0`.

**Proof sketch (SKETCHED, two-hop).**
- **Hop 1 (`H`'s self-martingale).** `thm:ceu`/`thm:ccee` for **`H`**:
  `𝔼^H_t(⌜𝟙(φ)·w⌝) ≂ₜ 𝔼^H_t(⌜ℙ^H_{f(t)}(φ)·w⌝)` — `H` already expects today what it will believe
  on day `f(t)`. *This hop is free* (it is `H`'s own `thm:ccee`, the self-case).
- **Hop 2 (`A` unbiased about `H`).** We must swap `ℙ^H_{f(t)}(φ)` for `B_t(φ)=𝔼^A_t(⌜ℙ^H_{f(t)}(φ)⌝)`
  *inside `H`'s* expectation. This is the **only** cross-agent step, and it is where good feedback
  enters: if `A` is unbiased for `ℙ^H_{f(t)}(φ)` on `w` (`thm:wub`/`thm:wubexp`, applied to `A`),
  then the residual `ℙ^H_{f(t)}(φ) − B_t(φ)` is `w`-mean-zero **from `A`'s standpoint** — and we need
  it `w`-mean-zero **from `H`'s standpoint** after weighting.

**Where it can break (CONJECTURE, flag hard).** Hop 2 is *not* obviously legal: `thm:wub` gives
`A`-unbiasedness measured *against the realized truth*, whereas we need the swap to survive inside
`𝔼^H_t(·)` — i.e. `H` must *also* regard `A` as unbiased about `H_{f(t)}`. Two routes:
- **Route A (strong feedback both ways).** Assume the good-feedback weighting and the deferral-time
  bound hold simultaneously for `H`-watching-`A` *and* `A`-watching-`H`. Then both martingales fire
  and the swap is a triangle inequality on `w`-averages. **Cleanest, but assumes a lot.**
- **Route B (H trusts A's calibration).** Add the premise `H → A` LUV-Total-Trust *about the
  specific LUV* `ℙ^H_{f(t)}(φ)` (i.e. `H` trusts `A`'s estimate of `H`'s own future). This is
  *weaker* than full mutual trust but is itself a cross-agent assumption — so Route B does **not**
  fully discharge §10's premise, it *relocates* it to a narrower LUV class. Still progress: it says
  `H` only needs to trust `A` *about `H`'s own future verdicts*, not about the world.

**This is the most important single proposition to develop** (see §6). It is the exact junction
where "good feedback" (a calibration property, LI §4.5) is supposed to manufacture "endorsement" (a
trust property, §10 / DDB). If the two-hop swap is legal under a clean hypothesis, the whole
conjecture (i)+(ii) follows from §10 by composition. **Hardness: medium-high.** Hop 1 is free; Hop 2
needs a precise lemma connecting `thm:wubexp` to cross-agent `≂`-swapping inside expectations —
plausibly a known move (it is morally "unbiased estimator ⇒ can be substituted under a generable
weighting"), but I have **not** verified it survives the corner-quote / `ℙ^H` vs `ℙ^A` standpoint
shift. **Flag: the standpoint shift in Hop 2 is the crux and could harbor a vacuity or a smuggled
immodesty.**

---

## Idea 4 — `H` weakly endorses `B`: it is §10 Value with `E := B` (SKETCHED, conditional on Idea 3)

**Candidate Proposition 4 (SKETCHED given Idea 3).** Under (a) `B` `H`-observable (idea 2),
(b) `B`'s valuations uniformly bounded `[0,1]`-LUVs, (c) the `w`-weighted cross-agent LUV-Total-Trust
of idea 3 — `H` endorses `B` in the LI-weak sense on the `w`-subsequence:
$$ 𝔼^H_t(\widehat S_t) \ \gtrsim_w\ 𝔼^H_t(O^i_t),\qquad \widehat S_t=\textstyle\sum_j α^j_t O^j_t,\ \ α^j=\mathrm{softmax}(B_t(O^·_t)/δ_t).$$
I.e. *`H` would rather hand any bounded decision to `B` (the AI-mediated read of `H`'s own future)
than commit now* — restricted to the feedback subsequence.

**Why it is exactly §10.** The §3/§10 five-line chain is **expert-agnostic** in lines 2/4/5
(novice `H`'s own coherence) and uses the expert only in lines 3/6. Idea 3 supplies precisely line 3
(weighted cross-agent martingale) on `w`; line 6 is line 3 at `w≡1`. So Proposition 4 is **not new
mathematics** — it is the existing `value_asymptotic` Lean composition with `E_o`/`E_e` reinterpreted
as `B`, *gated by* the weighting `w`. (Orientation-Q2 already flags `value_asymptotic` is
expert-agnostic; this is its cross-agent payoff with a *constructed* `B`.)

**The weakening is real and worth naming (INTERPRETATION).** Endorsement holds **only on `w`** — the
good-feedback subsequence. Off `w` (the unobservable class), there is *no* endorsement, matching
idea-1b's hole and AGENDA's own caveat that humans need trust "in circumstances that do not involve
good feedback." So the merge delivers a **feedback-gated endorsement**, which is honest but limited.
The "LI-weak sense" of endorsement in AGENDA is, I claim, precisely *Value-on-a-`ℙ^H`-generable-
weighting*. **Hardness: low given idea 3** (it is composition); the content is all in idea 3.

**Bearing on trust.** This is the cleanest formal statement of the thread's goal: *humans
justifiably defer to the AI-merged reasoner on exactly the questions where they have good feedback,
and the deference is the same Value/Total-Trust equivalence as deferring to one's own future self.*
That is a genuine, if bounded, "humans can trust AI" theorem — and its boundary (no-feedback) is
sharp, not hand-waved.

---

## Idea 5 — Basin-of-corrigibility bootstrap: replace assumed feedback with a contraction (CONJECTURE, the constructive payoff)

AGENDA: don't *assume* good feedback (humans introspect badly); *derive* it — "`A` starts with a
good-enough model of human-endorsed reasoning, aims it at understanding humans better, gets a
refined estimate, iterates." **Formalize as a fixed-point / contraction on the space of `H`-models.**

**Candidate Definition (bootstrap operator).** Let `Φ` map an AI-held estimate `Ĥ` of
human-endorsed reasoning to an improved estimate `Φ(Ĥ)` = "`A`'s best read of `H` *given that `A`
reasons using `Ĥ`*." A **basin of corrigibility** is a neighborhood `𝒩` of the true human-endorsed
operator `H*` such that `Φ(𝒩) ⊆ 𝒩` and `Φ` is a contraction (`‖Φ(Ĥ)−H*‖ ≤ λ‖Ĥ−H*‖`, `λ<1`) in a
suitable `≂`-compatible metric (e.g. `ℙ^H`-generable-weighted sup distance).

**Candidate Proposition 5 (CONJECTURE).** If `A`'s initial model `Ĥ_0 ∈ 𝒩` and `Φ` contracts on
`𝒩`, then `Ĥ_t → H*` on the good-feedback weighting, *and the convergence itself generates the
feedback hypothesis of idea 3* — i.e. accuracy bootstraps observability: a better `Ĥ` lets `A`
single out a *larger* `ℙ^A`-generable subsequence on which `ℙ^H_{f(t)}` is poly-time predictable
(because `A` now models `H`'s deliberation, so it can *compute* `H`'s future verdict in time
`O(f(t+1))` where before it could not). So good feedback is an *output*, not an input.

**Why this is the deep idea.** It closes the loop idea-1b left open: the no-feedback hole shrinks
as `Ĥ` improves, *if* the starting model is already inside the basin. The corrigibility content is:
**`A` is corrigible exactly when `Φ` contracts toward `H*`** — when `A`'s self-improvement at
modeling humans is *truth-tracking about humans* (legitimacy, AGENDA "Legitimacy"). This ties the
thread to orientation-Q11.

**Where it breaks (CONJECTURE, two distinct failure modes — flag both).**
- **(5-divergence) Outside the basin, `Φ` need not contract.** If `Ĥ_0` is a *manipulative* model
  (`A` models humans as endorsing whatever `A` outputs), `Φ` has a *spurious fixed point* — a
  self-confirming "human model" decoupled from `H*`. This is wireheading-of-the-human-model. The
  basin assumption is exactly the assumption that rules this out, and it is doing **all** the work:
  the theorem would say "*if* `A` starts aligned-enough, it stays aligned," not "`A` becomes
  aligned." AGENDA admits this ("ruled out by sufficiently extreme starting assumptions"). **Be
  honest: this is a stability/tiling theorem, not a bootstrapping-from-nothing theorem.**
- **(5-metric) The contraction metric may not exist.** On infinite/self-referential frames there is
  *no spectral gap* (v2 §5.2!), so a naive sup-metric contraction may be unavailable; `Φ` might only
  be *non-expansive*, giving convergence-to-a-set, not a point. This is the same continuum obstacle
  that makes clean modest deference live only on infinite frames. **Plausibly the right object is a
  `≂`-contraction "in a timely manner," not a literal Banach contraction.**

**Cleanest setting.** Two inductors + an explicit *bootstrap schedule*: a sequence of deferral
functions / model-refinements `Ĥ_t`. **Hardness: high** (it needs a metric on `H`-models compatible
with `≂`, and a contraction lemma) — but it is the only idea here that addresses AGENDA's actual
ask ("get good feedback from other assumptions"). **Highest payoff, hardest.**

---

## Idea 6 — Inner-alignment / treacherous-turn trader: a defecting trader inside `A` is eventually priced out, but timing is everything (SKETCHED + CONJECTURE)

AGENDA: "A trader inside the AI can wait until humans trust the AI, then do something untrustworthy.
Such traders will be eliminated by learning eventually, *supposing humans survive the turn intact*."
This is formalizable directly in the trader semantics.

**Candidate Proposition 6 (SKETCHED, the easy half).** A *treacherous trader* `τ` inside `A`'s
market — one that prices `B_t(φ)` accurately (tracking `ℙ^H_{f(t)}`) until a trigger time `T`, then
deliberately misprices — **cannot exploit `A` for unbounded profit** (LI criterion for `A`), so its
total influence on `A`'s prices is *bounded*; hence its effect on `B = 𝔼^A(⌜ℙ^H_{f(·)}⌝)` washes out
in the `≂ₜ` limit. *In the limit, the treacherous trader is defeated.* This is just the LI criterion
applied to `A` and is **SKETCHED-true**.

**The real problem is pre-limit (CONJECTURE, the hard half).** "Eventually" is doing dangerous work.
The trader can concentrate its *entire bounded budget* into a **single** high-stakes `φ_{T}` at the
moment trust is maximal. The LI criterion bounds *cumulative* profit, **not per-round damage**. So:

> **Failure mode (the "one big lie").** A treacherous trader with budget `b` defeated in the
> `≂ₜ` limit can still make `B_T(φ_T)` wrong by up to `≈ b` on **one** decision of unbounded
> real-world stakes. Endorsement (idea 4) is a `≂_w` *average* statement; it is **silent about any
> single round.** Humans "surviving the turn intact" (AGENDA) is precisely the unmodeled assumption
> that the single-round damage is recoverable. **This is the gap between asymptotic LI guarantees
> and real safety, and it is structural, not a detail.**

**Candidate refinement (CONJECTURE → idea for cautiousness).** To bound *per-round* damage, gate
deference by a **confidence/observability margin**: `H` defers to `B_t(φ_t)` only when a
`ℙ^H`-generable confidence proxy (e.g. recent good-feedback density on a neighborhood of `φ_t`)
exceeds a threshold; on low-confidence `φ`, `H` retains control. This is the LI rendering of AGENDA's
"cautiousness / interpretability" addendum, and it connects to the legitimacy thread (don't endorse
a verdict whose *process* you can't currently vouch for). **Hardness: easy half SKETCHED-now; hard
half (per-round bound) is genuinely open and likely needs a non-asymptotic refinement of LI that the
paper does not provide.** Important as a *red-team* result: it shows feedback-gated endorsement
(idea 4) does **not** by itself stop a treacherous turn.

---

## Idea 7 (lateral) — Symmetry test: is the merge a *join* of `H` and `A`, and does it dominate both? (INTERPRETATION → CONJECTURE)

v2 §10.3(a): "the future self is the *join of all observable experts*" — every observable expert is
Blackwell-dominated by the deferring agent's own future self. Apply this *to the merge itself*:

**Candidate Proposition 7 (CONJECTURE).** If `B` is `H`-observable and `H → B` LUV-Total-Trust holds
(idea 3/4), then `B` Blackwell-**dominates** `H`'s own future self `H_{f(t)}` for `H`'s decisions on
the feedback subsequence — because `B` adds `A`'s fast computation on top of `H`'s slow verdict. So
the merge is a genuine *strict* improvement: `H` should prefer deferring to `B` over deferring to its
own future self, *which it cannot do unaided* (it is slow). **This is the "combining strengths"
payoff (fast AND aligned) stated as a domination claim.**

**Symmetry caution (red-team).** The construction is *asymmetric*: `B = A`'s read of `H`'s future,
not `H`'s read of `A`'s future. The "dual merge" `B'_t(φ) := 𝔼^H_t(⌜ℙ^A_{f(t)}(φ)⌝)` — *slow human's
read of fast AI's future* — is **not** obviously trustworthy (it asks the trusted-but-slow agent to
predict the untrusted-but-fast one, which it cannot do well). The asymmetry is *essential* and
encodes *why* the construction points trust in the safe direction: **trust flows from the agent who
can be checked (`H` reads features) toward the agent doing the work (`A`), only through the bottleneck
of `A` estimating `H`'s OWN future.** Naming this asymmetry crisply is a small but clarifying
contribution. **Hardness: medium** (needs an LI notion of Blackwell refinement, orientation-Q6).

---

## Most promising to develop: **Idea 3** (good feedback ⇒ cross-agent martingale on the subsequence)

**Idea 3 is the keystone.** It is the *only* genuinely new technical step; ideas 1a, 4, 7 are
composition/interpretation on top of it via the existing §10 chain, and ideas 5/6 are the
honest-caveats frontier built around it. If the two-hop swap (Hop 1 = `H`'s free self-martingale
`thm:ccee`; Hop 2 = `A`-unbiasedness-via-good-feedback `thm:wubexp` substituted under `H`'s
weighted expectation) is legal under a clean hypothesis, then **Sam's conjecture (i)+(ii) reduces to
v2 §10 by composition** — which is the cleanest possible outcome and exactly the bridge the thread
wants. The crux to resolve first, before any Lean, is the **standpoint shift in Hop 2**: does
`A`'s good-feedback unbiasedness (an `A`-relative `≂`) survive being substituted inside `H`'s
`ℙ^H`-generable-weighted expectation? Pin that to either Route A (mutual good feedback, strong but
clean) or Route B (`H` trusts `A` *only about `H`'s own future*, weaker but relocates rather than
discharges the premise). Resolving Route-A-vs-B *is* the deliverable.

---

## Lean candidate (UNCHECKED — for the Lean-verify agent)

A faithful Lean object for *idea 4/idea 3-composition* would be the **two-hop substitution as an
asymptotic-calculus lemma**, reusing the orientation's confirmed `Approx`/`AsympLE` style: "if
`X ≈ Y` (hop 1, H's self-martingale) and `Y ≈ Z` (hop 2, A unbiased about H) then `X ≈ Z`, and the
§10 Value chain composes." This is **transitivity of `≂` plus the existing `value_asymptotic`
composition** — i.e. it would re-package already-confirmed content, NOT prove the LI theorems. I
deliberately do **not** write a new `.lean` file: the honest novel content (idea 3's Hop 2) is the
`thm:wubexp`-to-cross-agent-`≂` swap, which is *not* expressible without formalizing LI's feedback
machinery (LUVs, generable weightings, the criterion) — none of which is in `LeanDeference.lean`
(orientation §3, "what the Lean does NOT cover," items 1–2, 5). Writing a Lean stub that *assumed*
the swap would smuggle the conclusion and produce a vacuous "theorem," violating the SCOPE fidelity
rule. **Recommendation: the right Lean target for this thread is orientation-Q2 (the §10 external-
expert restatement of `value_asymptotic`) with `E := B` interpreted in the prose — pure
re-interpretation of confirmed Lean, no new kernel content — and that target belongs to whichever
agent owns the §10 Lean restatement, not here.** Flagging this *non-action* explicitly per SCOPE:
no candidate Lean file is produced because any honest one would either re-package confirmed content
or require formalizing LI feedback from scratch.
