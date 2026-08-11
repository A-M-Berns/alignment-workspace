# Scout report — lens: the tower, No-Forced-Trust, and the two positive constructions

*Round 3 of the deference-trust lab, 2026-07-01. Scout lens: the core deference program —
the tower property as THE deference relation, the No-Forced-Trust negative and its
predictable-iff-uninfluenced dichotomy, the sealed-sibling repair, the three fragments,
the soft⇒hard squeeze. Sources read in full: `deference-in-logical-induction-v6.md` (all 976
lines), `lean-deference/AUDIT.md` (all), `anson-notes/INDEX.md`,
`anson-notes/frozen-deliberation-deference-v6.md` (all), `run2/todos/TODOS.md` (GLOBAL
OFF-LIMITS list), `run2/report/RESEARCH-REPORT.md` (headline + ledger), and the legitimacy
passages of `li-deference.md` (§0.3 region). All file paths below are relative to
`` unless absolute.*

---

## 0. Where the seams are (the map behind the questions)

The v6 note and the AUDIT jointly expose a small number of load-bearing soft spots. I list
them once here; each question below targets exactly one.

1. **The forcing is named, not proved — anywhere.** AUDIT §1/§3.1: the market and traders
   are entirely unmodeled; every "the criterion forbids the exploit" is a named hypothesis
   or a trivial stub. T1 (`faithful_tracking`) and T3 (`conditional_tower`) are squeezes over
   hypotheses *equivalent to their conclusions* (AUDIT §3.3). v6 §8 bullet 4 names "model a
   minimal market in Lean" as the only route to real assurance. **Nobody has done any scoped
   version of this.**
2. **The dichotomy is a propositional silhouette.** `predictable_imp_uninfluenced` takes
   opaque `Prop`s; it is never connected to the real `tracking_fails` (2a) or
   `cost_circularity` (2b) (AUDIT §3.5, rec 3; v6 Appendix B: "propositional, never
   instantiated").
3. **The seam theorem's witness is asserted in prose.** v6 §5.7 "Off G, TS does not follow —
   provably" rests on: *a valid inductor family exists whose diagonal is pinned at 0.6 while
   truth alternates, each member mispriced at a single (stage, sentence) pair, "negligible
   for its own asymptotic calibration, so each remains a genuine inductor."* The Lean
   `TS_off_G_fails` is only a real-sequence witness (constant 3/5 vs. alternating); the
   model-theoretic claim needs a perturbation lemma about the LI criterion that is nowhere
   stated or proved.
4. **No-Forced-Trust (§4.1) is `Pr (meta)`** in the vetting ledger — the flagship negative of
   the whole program has no consolidated precise statement + proof; the e.c.-recoverability
   argument lives as a sketch in `anson-notes/` chat 11 (L4555–4605 per INDEX.md).
5. **2b's soft joint (~75–80%)** — whether inexploitability actually forces `A` to pay the
   simulating trader's full runtime, or whether the budgeter / `2^{-k}` weighting opens a
   gap — is flagged in v6 §4.3, §8 and AUDIT (hcost, type-(c)).
6. **`underdetermination_off_G` proves "two points in (0,1)"** (AUDIT §3.4, severity-High
   #3) while carrying the manipulation-boundary safety reading of §6.3 (T7 off G) on its name.
7. **The soft⇒hard squeeze stays prose** (v6 §1.6): only the *parallel-cut* obstruction (the
   amplifier) is formalized; nothing quantitative exists about what the non-parallel cuts
   buy, and §8 separately lists "Quantitative rates" as open.
8. **The resource-bounded existence theorem for `A`** (v6 §5.7 net status, §8) — the one
   construction-internal obligation of the frozen suite — is "standard in flavor, not yet
   written out." Without it, (A4) has no existence witness and the entire T1–T7 suite is
   conditional on an unconstructed object.
9. **The legitimacy program (§6.5, li-deference.md §0.3) is a desideratum, not a model** —
   and its stated formal home is exactly my lens: "the autonomous/blind target is the formal
   operationalization of 'the human isolated from the AI'… The legitimacy program is the
   project of replacing 'all futures' with 'non-corrupt futures' in the target."
10. **Small hygiene gap:** the amplifier cut-values are hand-integrated (AUDIT §3.7, rec 4),
    explicitly listed in v6 §8 as a "fuller pass" item.

Duplication guards applied throughout: run2's GLOBAL OFF-LIMITS list
(`deference-trust-lab/run2/todos/TODOS.md`) — none of the questions below re-proves or
re-skins `Deference.*`, `DeferenceAsymp/Extra/Argmax/Converse/Fold/ConverseAsymp/Trader.*`,
the v2 §§3/5.2/6/10 content, or any round-1 lab Lean object; run2's four REAL results
(aumann-modesty, negative-voi, averaging-hides-spikes, edt-node-value) are disjoint from
everything below. The hypothesis-laundering ban is addressed per-question.

---

## Q1 — A minimal modeled market: make "criterion ⇒ T1" a theorem for one contract stream

**Title:** `minimal-market-forces-tracking`

**Claim (acceptance target).** In Lean 4 + Mathlib, define a minimal market model containing,
as *definitions* (not hypotheses): a settlement stream `Y : ℕ → ℝ` (values in [0,1]), a quote
stream `a : ℕ → ℝ`, a type of **legal strategies** (a trade-size sequence `s : ℕ → ℝ` given by
a *continuous, bounded* function of the current quote — the soft-ramp legality condition,
reusing the `softInd` construction style of `FaithfulAcceleration.lean` as precedent), and a
**profit function computed from the definitions**: `profit s N = ∑_{n<N} s n · (Y n − a n)`
(sell-side mirror included). Take exactly ONE axiom/hypothesis, the criterion:
*for every legal strategy `s`, `profit s` is bounded above.* Prove the theorem: this single
quantified axiom implies `Approx a Y` — where the exploiting strategy for each side is
**constructed** (a soft ramp on the gap at threshold ε), its legality **proved** (continuity +
boundedness), and its divergent profit **derived**, so the conclusion is manufactured from
the axiom rather than named. Mandatory near-misses: (i) exhibit that with the legality
restriction *removed* nothing changes here but with the axiom restricted to a *smaller* class
(e.g. constant strategies only) the conclusion **fails** — a concrete `(a, Y)` pair
satisfying the weak axiom with `¬ Approx a Y` — proving the quantifier over the strategy
class is load-bearing; (ii) a non-vacuity witness market (`a = Y` perturbed by a vanishing
sequence) satisfying the axiom. `#print axioms` clean; every hypothesis of the headline is
the criterion axiom or derived.

**Why it matters.** This is AUDIT recommendation 5 ("the structural fix… the only route that
converts the §3.1/§3.3 gaps") and v6 §8 bullet 4, scoped down to the T1 shape — one contract
per day, settlement exogenous. It converts the two highest-severity AUDIT findings (market
unmodeled; T1 a squeeze over hypotheses ≡ conclusion) into a genuine theorem *for the modeled
market*. It does NOT claim to model LI proper — the deliverable's honest framing is "in any
market where bounded-profit-for-legal-strategies holds and profit is linear in the gap,
tracking follows," which is precisely the inference the corpus currently takes on faith.

**Modality:** LEAN-CORE. **Difficulty:** medium (the analysis is elementary; the work is
getting the strategy type and the two near-misses right).

**Novelty risk.** `DeferenceTrader.round_profit_ge_gap` and `Frozen.tracking_sell_profit` are
off-limits per-round arithmetic stubs — this differs categorically: the profit is summed over
a modeled horizon, the criterion is a single axiom quantified over a defined strategy class,
and the conclusion is derived, not restated. `FaithfulAcceleration.soft_total_trust` is the
closest existing object but runs the *other* direction (calibration hypothesis ⇒ Total Trust)
with `hbias`/`hbdd` named; here the *only* named thing is the no-profit axiom itself and the
target (`Approx a Y`) never appears as a hypothesis — satisfying the laundering ban.
Shadow test: the fake version specializes the axiom to one strategy whose profit is
definitionally the gap (that is the current corpus state); the real version proves legality
of the constructed exploiter and includes near-miss (i).

---

## Q2 — Instantiate the predictable-iff-uninfluenced dichotomy with the real 2a and 2b

**Title:** `dichotomy-instantiated`

**Claim (acceptance target).** In Lean, define the four dichotomy ingredients as *real-typed
predicates over sequences*, not opaque `Prop`s: `Tracks := Approx a Y`;
`QuoteRef := ` the structural data of the quote-referencing family (the rounding stream `r`
with `Tendsto (r−a) → 0` and the LI-PI settlement `Tendsto (Y − antiInd (r n)) → 0`, exactly
the hypotheses of `SelfRefTarget.tracking_fails`); `SatPower := ` joint satisfiability of the
cost data of `cost_circularity` (the `hshare`/`hcost` inequalities for some monotone `R, R_A,
F`); `Blind := ` the settlement factors through `A`-free data (modeled as: `Y = g ∘ h` where
`h` is a designated `A`-free input stream — the modeling choice must be stated and defended
in the notes). Prove the **composed** dichotomy: `(¬Blind → QuoteRef-data exists → ¬Tracks)`
via the real `tracking_fails`, and `(¬Blind → ¬SatPower)` via the real `cost_circularity`,
then conclude `(Tracks → Blind)` / `(SatPower → Blind)` on the same types — so that the §4.4
dichotomy is genuinely *formed*, not merely shaped. Mandatory non-vacuity: a concrete blind
instance where `Tracks` holds (so the dichotomy is not vacuously true by dead antecedents).
An honest NEGATIVE outcome is acceptable and valuable: a precise writeup showing `Blind`
cannot be given a non-question-begging formal rendering at this abstraction level (i.e. the
dichotomy is irreducibly construction-relative), with the failed candidate definitions.

**Why it matters.** AUDIT §3.5 + recommendation 3; v6 Appendix B row "dichotomy: propositional,
never instantiated." §4.4 is the hinge between the negative results and the sealed-sibling
repair ("blindness is derived, not assumed") — right now that derivation exists in Lean only
as a propositional tautology whose types don't even match the theorems it summarizes.

**Modality:** LEAN-CORE. **Difficulty:** medium — the 2a arm is mostly plumbing; the honest
formalization of `Blind` is the research content, and is where a negative finding may live.

**Novelty risk.** Composes existing off-limits-listed theorems (`tracking_fails`,
`cost_circularity`) — but composition-with-matching-types is exactly what the AUDIT says does
NOT exist ("the types do not even match"), so this is the flagged missing object, not a
re-skin. Shadow test: the fake version re-ships the propositional silhouette with cosmetic
type ascriptions, or defines `Blind` as `Tracks ∨ SatPower`'s consequence (circular); the
real version's `Blind` is a structural factoring statement checkable on the non-vacuity
instance.

---

## Q3 — The perturbation lemma behind the seam: does one mispricing preserve inductor-hood?

**Title:** `seam-witness-perturbation-lemma`

**Claim (acceptance target).** Paper-math at LI-paper rigor. State and prove (or refute):
**(Finite-perturbation lemma)** if `P` is a logical inductor over `D` (against class `𝒞`) and
`P'` agrees with `P` except at finitely many (day, sentence) pairs, where prices are changed
to other rationals in [0,1] keeping the sequence computable in the same class, then `P'`
satisfies the LI criterion over `D`. Then apply it to make v6 §5.7's off-`G` seam witness
rigorous: verify that the family `{H^[n]}` with each member's price at the single pair
`(F(n), P^{(n)})` pinned to 0.6 (truth alternating, each `P^{(n)}` settling just after
`F(n)`) (a) consists of genuine inductors, (b) remains a legal settlement target for the §5
construction (`Y_n` still computable at the stated cost, blindness intact), and (c) therefore
yields a valid instantiation in which TS fails off `G` — completing "TS off `G` does not
follow, *provably*" as a theorem rather than an assertion. Required care (this is where a
fake is detectable): the criterion quantifies over traders that can *see and condition on*
the perturbed price, and over unbounded time — the proof must bound the total extractable
profit from the perturbed days (finitely many, bounded stakes per member) and address
computability of `P'`. An honest negative — e.g. "the perturbation breaks e.c.-ness of the
family as indexed, and here is the repair or the obstruction" — is a valid deliverable.

**Why it matters.** v6 §5.7 ("Off G, TS does not follow — provably") and the identical
passage of `anson-notes/frozen-deliberation-deference-v6.md` (Target-Soundness section) carry
the *entire* boundary between the positive and negative results — "the horizon is the seam" —
on this unproved existence claim. AUDIT notes `TS_off_G_fails` is only a sequence witness.
If the lemma is false, the seam might be *thinner* than claimed (soundness could extend past
`G`); if true, the seam theorem is finally solid. Either outcome sharpens the program's most
important boundary.

**Modality:** PROSE (optionally MIXED: an EXEC toy market checking the bounded-extraction
accounting on a finite horizon). **Difficulty:** medium.

**Novelty risk.** Nothing in the corpus states this lemma (checked v6 §7/§8, AUDIT Appendix A,
off-limits list); it resembles standard "finite modifications don't matter" folklore, which is
exactly why it needs writing: the LI criterion's trader feedback loop makes the folklore
non-obvious, and the note's own hedge ("negligible for its own asymptotic calibration")
gestures at calibration, not at the criterion. Shadow test: fake = one paragraph asserting
folklore; real = explicit trader-profit accounting against the perturbed sequence plus the
(b)/(c) compatibility checks with the coupled construction.

---

## Q4 — No-Forced-Trust, stated and proved: the e.c.-recoverability impossibility theorem

**Title:** `no-forced-trust-precise`

**Claim (acceptance target).** Paper-math. Produce the precise theorem the v6 §4.1 box
gestures at, with all quantifiers pinned: define exactly what an "efficiently-checkable
relation between two distinct inductors" is (a `𝒞_H`-computable functional of the two
observable price histories, with the checking schedule made explicit); define
`𝓡(H) := {φ : H_∞(φ) is recoverable by a 𝒞_H functional from H's price history}`; prove
(i) the recoverability theorem `𝓡(H) ⊊ {Γ-undecidable sentences}` for inductors over PA,
with an explicit non-recoverable sentence (or family), and (ii) the corollary: no
efficiently-checkable relation `R(H,A)` has [`R` holds ⇒ `A_∞ = H_∞` on all undecidables] —
while (iii) delimiting what survives (per-sentence convergence on fixed φ; forced agreement
on decidables) exactly as v6 §4.1 lists. The deliverable is either a complete proof or a
precise, documented gap in the chat-11 sketch (e.g. if the recoverability argument needs an
additional assumption on how `R`'s satisfaction is verified, name it and show it necessary).

**Why it matters.** v6 Appendix B rates §4.1 `Pr (meta)` — the program's headline negative
("forced other-trust analogous to self-trust is impossible by the structure of the
framework") has never been consolidated beyond a conversation sketch
(`anson-notes/INDEX.md`, file 11, L4555–4605: "No-unconditional-limit-equality impossibility
+ Limit-non-recoverability theorem & corollary (𝓡(H)⊊𝓢)"). Every later result is motivated
as a response to this theorem; it should exist as a theorem.

**Modality:** PROSE. **Difficulty:** medium-high (the sketch exists; the risk is that
"efficiently-checkable relation" resists a clean definition — which would itself be a
finding, since the theorem's informal force depends on the quantifier's breadth).

**Novelty risk.** Duplicates the chat-11 sketch by design — the task is *consolidation and
verification*, explicitly framed as such, which the honesty norms permit ("cite prior rounds
instead of re-proving" applies to established results; §4.1 is rated NOT established, merely
argued). Not on any off-limits list. Shadow test: fake = restating the v6 §4.1 paragraph with
theorem numbering; real = a definition of the relation class under which (ii) is actually
derivable from (i), plus the explicit non-recoverable witness.

---

## Q5 — Legitimacy-filtered sealed sibling: which legitimacy gates preserve the forcing?

**Title:** `legitimacy-filtered-target`

**Claim (acceptance target).** Paper-math at the rigor level of
`anson-notes/frozen-deliberation-deference-v6.md`. Formalize the minimal version of the
legitimacy program (li-deference.md §0.3; v6 §6.5: "replacing 'all futures' with 'non-corrupt
futures' in the target") *inside* the frozen construction: let `λ = (λ_n)` be a
**legitimacy filter** — a computable predicate (or [0,1] weighting) on deliberation traces of
the sealed sibling `H^[n]` up to `F(n)` — and define the filtered target
`Y_n^λ :=` (the sibling's stage-`F(n)` credence gated/reweighted by `λ_n`). Prove three
claims: **(i) Blind filters inherit T1.** If `λ` is reflectively blind (factors through
`A`-free data) and `𝒞_A`-computable by the horizon, the T1 forcing argument goes through
verbatim for `a_n^λ := E^A_n(C_n^λ)` — `A` is forced to faithfully predict *the legitimate
deliberation*; state exactly which of (A1)–(A5) must be re-verified. **(ii) Quote-dependent
filters die by 2a.** If `λ_n` may reference `A`'s current quote (the natural rendering of
"the AI discounts futures its own output corrupted"), exhibit the anti-inductive filter
(e.g. `λ_n = 𝟙[a_n ≤ ½]` gating between two divergent trace-classes) reproducing the ½-gap
at the *filter* level — a new instance of predictable-iff-uninfluenced: **a legitimacy filter
you can force prediction through is one the predictor cannot influence.** **(iii) The new
seam.** On indices where `λ_n`'s value never settles in `D` (legitimacy itself undecidable —
the realistic case for "was this feedback manipulated?"), the §5.8 silence property applies
to the filter: forcing goes silent, so the forced-soundness boundary moves from
timely-checkable to timely-checkable-**and**-timely-legitimate, and no further. An honest
outcome may be that (i) needs a nontrivial extra condition (e.g. `λ` must be
provably-total for T2's `expprovind` carry) — naming it is the point.

**Why it matters.** This is the round-3 theme (legitimacy) executed through this scout's lens:
v6 §6.5 already asserts "blindness is that norm, formalized" but no one has checked whether
the frozen suite *survives* the substitution of a filtered target — i.e. whether the
program's one concrete positive machine can actually host the legitimacy ingredient it was
built to motivate. Claim (ii) would be the first formal content of "the AI should predict
only non-corrupt futures": corruption-*by-the-predictor* is exactly what the dichotomy
already excludes, and showing the filter must itself be blind turns the §0.3 desideratum
into a constraint with a proof.

**Modality:** PROSE (optionally MIXED: (ii)'s counterexample has a small Lean/EXEC core in
the style of `no_exact_quote`, on new objects). **Difficulty:** medium.

**Novelty risk.** v6 §6.5 and li-deference §0.3 state the *program*; the lab's round-1
`Legitimacy.*` Lean objects (off-limits) are one-pair defect-sign toys unrelated to the
frozen construction. Nothing in the corpus filters the sealed-sibling target. Shadow test:
fake = assuming the filtered target is calibrated to truth (laundering TS through the word
"legitimate") or defining legitimacy as "whatever makes T1 work"; real = `λ` is an
independent structural input, (i) re-derives forcing from (A1)–(A5)+blindness of `λ`, and
(iii) concedes what is NOT forced (the filter's own correctness is never certified — the
§6.3 manipulation boundary reappears one level up, and the writeup must say so).

---

## Q6 — 2b's soft joint: does the budgeter open a gap in cost-circularity?

**Title:** `cost-accounting-soft-joint`

**Claim (acceptance target).** Paper-math. Settle, sharpen, or honestly bound the ~75–80%
step of 2b (v6 §4.3, §8; AUDIT: `hcost` type-(c)). Precisely: in the Garrabrant §5
trading-firm/budgeter construction, the criterion demands inexploitability by every
`𝒞_A`-trader; the 2b argument needs that "a trader computing `Y_n` (cost `R(F(n))`) by day
`n`" is in `𝒞_A` only if `𝒞_A` contains `n ↦ R(F(n))`. The question: does the `2^{-k}`
enumeration weighting / budget mechanism allow either (a) a **sparse-schedule** or
**amortized** simulate-and-arbitrage trader whose per-day cost stays in `𝒞_A` while still
extracting unbounded profit on a subsequence — restoring 2b's contradiction *unconditionally
on that subsequence* (strengthening 2b); or (b) a genuine evasion — the market can stay
inexploitable while no affordable trader ever computes `Y_n` on time — making 2b
*conditional*, with the exact condition (a growth/cofinality property of `R∘F` vs `𝒞_A`)
stated. Acceptance: a proof of (a) or (b) for a cleanly specified rendering of "trader cost"
(per-day runtime of the trading function, as in the LI paper's e.c. definition), or, at
minimum, a theorem-shaped statement of exactly what the cost model must satisfy for each
horn — replacing "~75–80%" with a named fork. The known correction must be respected: the
naive "market runs its traders" mechanism is *wrong* (v6 §4.3), so the argument must go
through the order-theoretic/simulability route.

**Why it matters.** 2b carries half the negative backbone (the quote-free case: "underivable,
not disproven"), and via §4.8 the death of the tower itself off `G`; and via §5.10 the
boundary of the admissible domain. It is the only step of the negative results the corpus
itself rates below ~80%. Both resolutions are valuable: (a) hardens the trichotomy of §5.11;
(b) would *reopen* a corridor for cross-process forcing on quote-free families — a live
positive prospect the program currently believes closed.

**Modality:** PROSE. **Difficulty:** high (honest partial output — the named fork — is
explicitly acceptable and still an improvement over the current state).

**Novelty risk.** The soft joint is flagged, not worked, in every document (v6 §4.3/§8,
AUDIT §3.6/Appendix, self-referential-settlement note per INDEX). No off-limits overlap.
Shadow test: fake = re-deriving the `R_A(n) ≳ R_A(F(n)) > R_A(n)` regress (already
kernel-checked as `cost_circularity`) and calling it a resolution; real = engages the
budgeter/weighting mechanism specifically and produces either the sparse-trader construction
or the evasion model.

---

## Q7 — An honest finite core for T7-off-G: two non-exploitable price paths in a real (finite) trader model

**Title:** `underdetermination-finite-model`

**Claim (acceptance target).** EXEC (Python, exact rationals). Build a small but *principled*
finite market model: a finite sentence pool with settling sentences (settlement schedule
given) and one designated never-settling sentence `φ`; a **finite, exhaustively enumerated
trader class** (all traders of a declared syntactic form — e.g. threshold/ramp functions of
bounded lookback `k` over price history, with rational parameters on a declared grid —
including traders that trade `φ` against its own price history and traders that bank on
settling sentences); and two price paths `p, p'` such that, verified by computation:
(i) both agree at all times on all settling sentences and converge to their settled truth
values; (ii) they differ persistently by a prescribed `γ` on `φ`; (iii) **neither path is
exploitable by any trader in the class** — cumulative profit of every trader stays bounded,
checked exactly over the horizon and extended to all time by an explicit argument
(eventually-periodic prices + bounded-lookback traders ⇒ eventually-periodic profit
increments summing to ≤ 0, or similar), not by truncation hand-waving. Report the class size,
the exploitation check, and the extension argument. Negative outcome acceptable: if every
such pair IS exploitable within the class, that is a finding about what the T7-off-G prose
is silently assuming.

**Why it matters.** AUDIT severity-High finding #3: `Frozen.underdetermination_off_G` proves
"two points in (0,1)" while its name carries T7's off-`G` underdetermination — which in turn
carries the §6.3 manipulation boundary ("the whispering earring rendered as a theorem") and
the §6.5 legitimacy motivation. A finite-model demonstration in which non-exploitability is
*checked against an actual trader class* is the largest honest step available toward the
model-theoretic claim short of formalizing LI, and it directly tests the prose mechanism
("no trader profits from a difference that never settles").

**Modality:** EXEC. **Difficulty:** medium.

**Novelty risk.** Run2 *dropped* a "B-is-not-an-inductor EXEC exploit-search" with the
warning that hand-built mock-LI markets "risk being a caricature proving nothing." That risk
is real and is addressed by inverting the burden: here the deliverable is not "this toy is an
inductor" but "within this declared, exhaustively enumerated class, non-exploitability +
G-agreement + off-G divergence coexist" — with the class definition and its limits stated up
front, and the caricature risk named in the writeup. No overlap with `trust-laundering` (a
static frame search) or any off-limits Lean object. Shadow test: fake = a trader class that
structurally cannot see `φ` (then (iii) is free and empty), or profit checked only to a
truncation with no extension argument; real = the class provably contains `φ`-sensitive
traders and the boundedness argument covers all time.

---

## Q8 — Quantitative soft⇒hard squeeze: how fast do non-parallel cuts pin g to the identity?

**Title:** `soft-squeeze-quantitative-frontier`

**Claim (acceptance target).** EXEC (exact rationals; LP or direct optimization with exact
arithmetic). Finite model of the §1.6 situation: expert-estimate variable `e` on the grid
`{0, 1/N, …, 1}` with measure `μ`, novice conditional-mean function `g : grid → ℚ`, constraint
family = **soft** threshold-trust cuts of width `δ` (both directions,
`E_μ[(X − t)·Ind_δ(E(X) ≷ t)] ≷ 0`-style) over declared bet families: (level-0) bets constant
on `e`-layers — the parallel cuts; (level-1) two-point menus / bets varying within a layer —
the non-parallel cuts of v6 §1.6. Compute, as exact rationals, the maximum of `‖g − id‖∞`
subject to all constraints, as a function of `(N, δ, μ, bet level)`. Acceptance targets:
(i) at level-0 the extremal `g` matches the amplifier family and the max deviation is
governed by boundedness at the extremes (reproducing, as a check, what
`amp_boundedness_forces_id` proves — this is the calibration of the tool, not the result);
(ii) the NEW content: the level-1 max-deviation curve in `δ` — specifically whether it scales
`Θ(δ)` (supporting the conjecture that the soft squeeze loses only `O(δ)`, i.e. the LI-soft
Total Trust family pins the tower up to the smearing width) or exhibits a floor independent
of `δ` (meaning even all-bets soft trust does NOT recover the tower in the limit — a
qualitatively new obstruction beyond the amplifier). Either outcome, reported with the
extremal `g`'s exhibited, is the deliverable.

**Why it matters.** v6 §1.6: "this is why the squeeze stays prose — a genuine convex-geometry
theorem"; §8 lists "Quantitative rates" as open; the frozen note's T6 identifies the
squeeze-frontier with the forcing blind spot. No quantitative information about the
soft-cut family exists anywhere in the corpus. A `δ`-floor finding would be a genuine (and
citable) negative: soft Total Trust — the only kind LI can force — never recovers the
equality face even on all bets, sharpening why T3 needs settlement rather than trust
inequalities.

**Modality:** EXEC. **Difficulty:** medium (careful constraint generation; exact LP via
`fractions`/`sympy` or rational-pivot simplex).

**Novelty risk.** The finite-*exact* (hard-cut) answer is classical (DDB Thm 2.2's convex
characterization — do not re-derive; cite). The amplifier lemmas (off-limits to re-prove) are
used only as a calibration check at level-0. The new object is the *soft*-cut, finite-grid,
quantitative frontier, which neither DDB (hard cuts) nor the Lean corpus (parallel cuts only)
touches. Shadow test: fake = running only level-0 and reporting the amplifier again, or
using floating point (exactness is load-bearing near the extremes); real = exact arithmetic,
level-1 cuts demonstrably active in the LP (report duals/binding constraints).

---

## Q9 — Write out the resource-bounded existence theorem for A

**Title:** `resource-bounded-existence`

**Claim (acceptance target).** Paper-math at LI-paper rigor. State and prove the missing
obligation of v6 §5.7/§8: **for the computably-enumerable clocked trader class `𝒞_A` (traders
carrying explicit runtime bounds, including the simulate-`H`-to-horizon traders of T1 whose
day-`n` cost is `~R_H(F(n))`), a computable logical inductor `A` over `D_A` inexploitable by
all of `𝒞_A` exists** — by adapting Garrabrant et al.'s existence proof (LI §5: trading firm,
budgeter, dovetailing) and verifying each step tolerates (a) the clocked enumeration, (b) the
day-`n` trader costs growing like `2^{O(n)}` while `A` itself remains computable, and (c) the
(A5) publication schedule `e ≥ R` — i.e. `A`'s own per-day computation cost is bounded by a
`𝒞_A`-affordable `R`, so the ledger remains `𝒞_H`-readable on schedule. The deliverable
states exactly *in what class `A` itself* is computable (the note is silent on this), since
that is what (A1)+(A4) jointly consume. An honest negative — a specific step of the LI
existence proof that does NOT tolerate the clocked class or the cost schedule, with the
obstruction isolated — is equally acceptable and more important if found.

**Why it matters.** v6 §5.7 ("the one remaining construction-internal obligation"), §7
trusted-boundary list, and §8 all name this as the sole unwritten load-bearing piece of the
frozen suite: without it, (A4) has no witness and T1–T7 are theorems about a possibly-empty
class of constructions. It is rated "standard in flavor" — which makes it exactly the kind
of item where one focused session either discharges it or discovers it is not standard after
all (either is progress; the second is the more valuable finding).

**Modality:** PROSE. **Difficulty:** medium-high (requires working through LI §5 carefully;
no new ideas expected, but the cost bookkeeping is exactly where 2b-style surprises live —
note the resonance with Q6, which should be assigned to a different agent to keep the two
cost analyses independent).

**Novelty risk.** Not in any Lean module, not in the anson-notes deliverables (INDEX shows
chat 03 flagged the adjacent "R_H ∈ 2^poly lemma (~75%)" as unwritten), not on any off-limits
list. Shadow test: fake = "the existence theorem obviously relativizes" in one paragraph;
real = step-by-step traversal of the LI §5 proof with the three checkpoints (a)–(c)
discharged or refuted, and the class of `A` pinned.

---

## Q10 — Discharge the amplifier cut-integral in Mathlib (hygiene item)

**Title:** `amplifier-integral-mathlib`

**Claim (acceptance target).** Lean 4 + Mathlib, standalone file per GROUND-RULES §2. Prove
via `intervalIntegral`: `∫ e in t..1, ((1+2c)·e − c) = (1+2c)·(1−t²)/2 − c·(1−t)` (and the
lower-cut mirror `∫ e in 0..t`), then restate `amp_upper_cut_nonneg` / `amp_lower_cut_nonpos`
with the *integral expression itself* as the cut value, so the one hand-evaluated
antiderivative in the corpus (AUDIT §3.7) is kernel-checked end-to-end. Non-vacuity/shadow
guard: include a commented near-miss showing a deliberately wrong antiderivative fails
(`example : ¬ (…) := by …` or a failing `#check`-style note), demonstrating the integral step
is now load-bearing rather than decorative. `#print axioms` clean.

**Why it matters.** AUDIT recommendation 4 and v6 §8's parenthetical ("a fuller pass could
also evaluate the amplifier cut-integrals via Mathlib's ∫"). Low value per se (the AUDIT
re-derived the integral by hand and found it correct) but it closes a named gap, is
self-contained, and is a good calibration task for a session's Lean throughput before
attempting Q1/Q2.

**Modality:** LEAN-CORE. **Difficulty:** low.

**Novelty risk.** The `amp_*` sign lemmas are established (do not re-prove the sign algebra —
reuse it); the new content is exactly the integration step the AUDIT identifies as absent.
Trivial-dressing risk is acknowledged up front: this is filed as hygiene, not discovery, and
must be reported as such.

---

## Priority ordering (scout's recommendation)

1. **Q1** (`minimal-market-forces-tracking`) — attacks the corpus's single largest gap; the
   fake version is well-characterized and detectable.
2. **Q3** (`seam-witness-perturbation-lemma`) — cheapest genuine sharpening of the
   negative/positive boundary; a surprise here would matter a lot.
3. **Q5** (`legitimacy-filtered-target`) — the round-3 theme, executed on the program's one
   concrete positive machine; medium risk, high relevance.
4. **Q4** (`no-forced-trust-precise`) — the flagship negative deserves to be a theorem.
5. **Q2** (`dichotomy-instantiated`) — clean AUDIT-mandated composition work.
6. **Q7** (`underdetermination-finite-model`) — honest strengthening of the weakest
   headline stub; caricature risk managed by design.
7. **Q8** (`soft-squeeze-quantitative-frontier`) — new quantitative territory; either
   outcome is citable.
8. **Q9** (`resource-bounded-existence`) — necessary, likely laborious; best given to an
   agent distinct from Q6's.
9. **Q6** (`cost-accounting-soft-joint`) — highest difficulty, highest variance.
10. **Q10** (`amplifier-integral-mathlib`) — hygiene; pair with a bigger Lean task.

*Labeling discipline for all of the above: kernel-checked claims are those ending in
`#print axioms`-clean Lean; Q3/Q4/Q5/Q6/Q9 are paper-proof deliverables and must carry
Proved-on-paper / interpretation flags internally; Q7/Q8 are computational evidence about
finite models, never to be cited as theorems about logical inductors.*
