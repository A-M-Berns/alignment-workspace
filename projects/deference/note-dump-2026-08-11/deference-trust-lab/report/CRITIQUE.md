# CRITIQUE — Completeness Critic (Adversarial Referee)

*Target: `report/RESEARCH-REPORT.md` and the files under it. Stance: harsh referee. I assume the
PROVED/SKETCHED/CONJECTURE labels are mostly applied honestly at the file level (the per-thread
red-teams and the Lean audit are genuinely good and I confirm most of their verdicts). My job is the
**next** layer: where the **report as a synthesis** still over-sells, where a "salvageable" verdict
is doing the work of "we did not finish," where cross-connections are asserted as load-bearing but
are decoration, and the single thing the principal should not believe without more work.*

Each criticism is flagged by **severity**: **[BLOCKER]** (a headline claim the principal might act on
that is wrong or unearned) / **[MAJOR]** (a real gap the report under-weights) / **[MINOR]**
(precision/labelling). Concrete fix after each.

---

## 0. The single most important thing the principal should NOT believe

> **"The entire agenda is the same theorem with the expert-slot filled differently, so the open
> frontier is the single object D3 (cross-agent LUV-Total-Trust)."** (Exec summary; the report's
> through-line.)

**This is half true and half a rhetorical trick, and the trick is load-bearing.** The honest content
is: *given* LUV-Total-Trust toward an expert `E`, Value follows by the §10 composition, and that
composition is the same in every thread. That part is real and is the lab's best contribution.

But "the same theorem" smuggles in that the **interesting** content of each thread is the §10
composition. It is not. In every thread, *all the difficulty lives in discharging the premise*, and
**that discharge is different, hard, and unfinished in every single case**:

- merge (D2): discharge = Hop 2 standpoint shift — **CONJECTURE**, and the one proposed route uses
  the wrong theorem (see §1).
- legitimacy (D5): discharge = "truth-tracking ⇒ small defect" — explicitly **CONJECTURE** = D3
  itself (legitimacy-ideate L1's own fidelity caveat).
- updateless (D4): the relation doesn't even *use* a premise of this form — it's an argmax tautology
  (see §3).
- D6 (UDT1.1): lives in reflective oracles, not LI; the "shared open characterization" claim (report
  §3.2: "D3 also answers when a UDT1.0 inductor may believe it is UDT1.1") is an **unargued
  analogy** — there is no LI inductor anywhere in the D6 work (it is finite PF + a Stag-Hunt 2×2).

So "everything routes through D3" is true in the trivial sense that **D3 is the part nobody solved**.
Saying "the agenda collapses to one object" makes a *failure to close any constructive thread* sound
like a *unification*. **The principal should not believe the agenda has been reduced to a single
tractable problem; it has been reduced to a single *open* problem, and the reduction itself (that the
premise is genuinely the only missing piece, with no second hidden premise for distinct inductors) is
SKETCHED, not proved.** v2 §10.2 is labelled "interpretation; sketched."

**Fix.** Re-state the through-line as: *"Value-given-the-premise is uniform and (modulo LI) checked;
the premise is the entire unsolved problem and we discharged it in zero of the constructive cases.
The contribution is the precise localization of the gap, not its closure."* Demote "the same theorem"
to "the same *reduction target*."

---

## 1. [BLOCKER] The merge (Fast Student/Slow Teacher) is hand-waved at the crucial step — and the report partially conceals this behind "SALVAGEABLE."

This is the agenda's flagship constructive payoff and the task's named concern. Walking the chain:

**1a. Is `B_t` a genuine logical inductor? — NO, and the report's own files say so, but the report
table hides it.** The model/ideate establish (correctly) that `B = 𝔼^A(⌜ℙ^H_{f(t)}⌝)` does **not**
satisfy the LI criterion unrestricted (it is a poly-time function of `A`'s prices, not its own
market; off the good-feedback subsequence it is "anything `A` likes"). The honest status is: **`B` is
NOT shown to be an inductor; it is at best behaviorally inductor-like on a `ℙ^A`-generable weighted
subsequence, and that itself rests on Proposition A which has an open gap.** The report's Exec-summary
sentence "good feedback + fast `f` discharge the §10 premise ⇒ `H` endorses `B`" (D2 row) reads as a
near-result. It is a **double conjecture** (B-inductor-ness AND Hop 2), and AGENDA conjecture (i)
("`B_t` is itself a logical inductor") is **not addressed at all** in the generative sense — it is
quietly redefined to the behavioral reading and then gated.

**1b. Does `H` endorse `B`? — depends entirely on Hop 2, which is CONJECTURE, and the salvage route
introduces a NEW gap that the report waves through.** The red-team correctly killed the original
patch (the `wubexp` "determined-via-Γ → A-decidable" swap is the wrong theorem — `μ_t = ℙ^H_{f(t)}(φ)`
is another machine's market price, not a Γ-determined value, so there is no `thmval` to collapse to).
Good. But the report then presents the **threshold-sentence reroute** (`thm:wub` on
`ψ^q = "ℙ^H_{f(t)}(φ)>q"`, integrate over `q`) as if it nearly closes the gap ("converts a false
invocation into a sound argument with one smaller residual gap"). **Three problems the report does not
surface:**

- (i) **The reroute discharges only `A`-watching-`H` unbiasedness — the Hop-2 STANDPOINT SHIFT is
  still open.** Even granting `A` is `w`-unbiased about `H`'s thresholds, the substitution must
  survive *inside `H`'s `ℙ^H`-generable-weighted expectation* (`ℙ^A`→`ℙ^H` shift). That is the gap
  the model labels "the one true gap," and the threshold reroute **does not touch it** — it only
  fixes the sub-step that feeds Route A. Report §3.2 conflates "fixed the wubexp error" with "fixed
  Hop 2." They are different. **Route A still presupposes mutual good feedback; Route B still merely
  *relocates* the premise.** Neither discharges §10's premise. So the headline "feedback discharges
  the premise" is, after the dust settles, **still false / unproven**.

- (ii) **The "integrate over `q`" step has an unestimated uniformity gap.** `thm:wub` gives
  per-threshold unbiasedness; recovering price-unbiasedness needs uniform-in-`q` control over a
  generable family of weightings. The report calls this "smaller and plausibly closable." That is an
  *assertion*, not an argument; nobody bounded the `q`-integral of the per-threshold residuals or
  checked the family is jointly generable. **A referee should treat this as a second open conjecture,
  not a footnote.**

- (iii) **`H`-observability of `B` is solved by fiat.** §10 requires `(B_t(O^j))_t` to be
  `ℙ^H`-generable, but `B` is `ℙ^A`-generable. The resolution ("`A` *publishes* `B_t`; `H` reads it
  as an expressible feature") is a **modeling assumption smuggled as a structural fact**. Whether a
  published external number can serve as a `ℙ^H`-generable feature in the *exact* sense `thm:ccee`'s
  weight-generability requires (poly-time from `H`'s own market) is **not checked against LI Def
  4.3** — it is asserted by analogy ("just like market prices"). If this fails, the §10 premise is
  not even *well-typed*, and the whole reduction is vacuous. This is the kind of thing that looks
  obvious and turns out to be where the immodesty hides.

**1c. The Lean file does NOT support the merge claim and the report's table over-credits it.** The
Lean-verify report and red-team are honest that `merging-inductors.lean` proves only
`return_monotone_in_selector` (`S` monotone in the *selector weight* σ when μ≥½) — an orthogonal
finite fact with σ a *free* monotone selector **decoupled from both the estimate `b` and the truth
`μ`**. The chain "bias on `b` → lower σ → lower S" has its load-bearing middle link
(`b ↦ σ(b)` monotone) **imported, not formalized**. So the file says: *if* the selector already
underweights the winning bet, the return is lower. That is trivial and is not "merge" content. The
report's Lean table ("softmax-bias monotonicity; reversal at μ=0 certifies non-vacuity") is accurate
*about the file* but the report's framing ("finite cores of every thread … kernel-checked") invites
reading this as evidence for the merge. **It is evidence for nothing about cross-agent trust.**

**Verdict on the task's pointed question — "Is the merge story load-bearing or hand-waved at B being
a genuine inductor / H endorsing B?"** **Hand-waved at exactly those two points.** The reduction
"merge = §10 with expert B" is the genuine and valuable contribution; **everything that would make it
a theorem (B inductor-ness, Hop 2, observability) is open, and two of the three are mislabeled in the
report as nearly-closed.** "SALVAGEABLE" is the right verdict for the *note* but the report should not
let "salvageable" read as "basically works."

**Fixes.** (1) In the D2 row and §3.2, replace "discharge the §10 premise ⇒ endorse" with "**reduce**
endorsement to three open sub-problems: B-observability-as-feature (check vs LI Def 4.3), the
`q`-integral uniformity, and the Hop-2 standpoint shift (Route A needs mutual feedback; Route B only
relocates)." (2) State plainly that **AGENDA conjecture (i) — `B` is a logical inductor — is NOT
established in any sense the agenda asked for.** (3) Stop listing `merging-inductors.lean` adjacent to
the merge claims without the disclaimer that it formalizes an orthogonal selector fact.

---

## 2. [MAJOR] The "no-feedback wall" is correctly identified but the report's *positive* feedback story is thinner than advertised.

The report (and merge files) treat the good-feedback PASS as solid and locate all hardness on the
unobservable class. Fair. But two things are under-stated:

- **2a. "Good feedback" is never defined as an earned object — it is two clauses of `thm:wub` plus a
  *vacuous-when-it-matters* hypothesis.** On the unobservable class the good-feedback hypothesis is
  *vacuously satisfied/unsatisfiable* (no poly-time machine decides `μ_t`), which the files note — but
  this means the entire positive theory holds only where the hard problem is absent **by hypothesis**.
  That is not a small caveat; it is the statement that **the merge has been proven (modulo the gaps in
  §1) to work exactly where it was never needed.** The agenda's actual ask — trust *without* good
  feedback, via the corrigibility-basin bootstrap (idea 5) — is **CONJECTURE with no formal content**
  (the contraction metric "may not exist," it is admitted to be a stability/tiling theorem, not
  bootstrapping). The report's open-problem §6.3 says this, but the ranking table's "Bearing on
  human–AI trust: HIGH" for D2 does not discount for "high only on the easy region."

- **2b. The "one big lie" (single-round) gap is correctly flagged as structural — but the report does
  not draw the obvious consequence for the principal.** Every endorsement result is a `≂_w` average;
  it is silent about any individual high-stakes round; a treacherous trader can dump its whole budget
  into one decision. **This means none of the lab's results bound the thing a safety principal most
  cares about: catastrophic single actions.** The report mentions this (§6.4) but buries it as
  open-problem #4 rather than foregrounding it as a *limit on what the whole research program can
  deliver in its current asymptotic form*. A harsh reading: **the LI deference framework is
  structurally incapable of a single-round safety guarantee without a non-asymptotic refinement of LI
  that does not exist.** That belongs in the executive summary, not problem #4.

**Fix.** Add to the exec summary a "scope limits" sentence: *asymptotic-average guarantees only;
silent on single high-stakes rounds; positive merge results live on the good-feedback region where
trust is least needed.* Discount D2's "bearing" cell accordingly.

---

## 3. [BLOCKER] Updateless deference (D4) is labelled "salvageable / discrimination BROKEN as headlined" — but as a *research direction* it is closer to **vacuous**, and the report's ranking ("High tractability") rewards the wrong thing.

The red-team is excellent and damning: the relation `A updatelessly-defers to u :⇔ U(π_u)=max_p U(π)`
depends on `node_value` **only through its per-node argmax**, and `node_value` is a **free input never
tied to `U`**. Consequences the red-team proved by execution:

- The mugging/Newcomb "discrimination" is supplied **by the modeler's hand-chosen `node_value`**, not
  by the formalism (Probe 1). The relation cannot tell a caver from a non-caver.
- It accepts **adversarial/garbage updates that luck into the optimum** (Probe 3) — blind to process,
  so the INTERPRETATION that it is "endorsement-like / legitimacy-like" is **false**.
- "Reduction to ordinary (van-Fraassen) endorsement" is a tautology mis-glossed: there is **only one
  belief object**; `endorsement_reduction` proves `argmax of separable U is globally optimal`, a
  one-directional triviality. The biconditional with endorsement is **false** even in the separable
  case (Probe 5/6).
- "6/6 cases pass" is unsupported: the executed checker has **3 cases** (verification-count
  inflation).

**The report softens all of this to "the relation does not itself discriminate muggers (a hand-chosen
input does); separable reduction PROVED & KERNEL-CHECKED."** True, but it lets D4 keep a "**High**
tractability / safety-relevant" billing on the strength of a **kernel-checked tautology**
(`split optimum = global optimum`). A kernel check of `argmax is optimal for a decoupled sum` is
real Lean and useless as deference content. **The principal should not count D4 among the lab's
results; it is a relation that is currently a wrapper around argmax, plus a known fact.** The genuine
research is the *unstarted* fix (derive `node_value` as the EDT-conditional of `U`), which the report
correctly lists in Phase 3 — but then the **table** should not present D4 as a near-win.

**Fix.** Re-rate D4: status "**relation BROKEN as a discriminator; the proved Lean is an argmax
identity, not deference**; the real direction (EDT-derived `node_value`) is unstarted, Medium-Hard."
Remove "High tractability" — what is tractable (the tautology) isn't the point; what is the point
isn't started. Correct "6/6" → "3 executed."

---

## 4. [MAJOR] Several "results" are vacuous-as-deference-content: the report's Lean table lets finite algebra masquerade as trust theorems.

The Lean audit is scrupulous *within each file*. But the **report's synthesis** repeatedly lists
"finite cores PROVED & KERNEL-CHECKED" in a way that, read quickly, credits the *thread* with formal
support it doesn't have. Specific offenders, with what is actually proved:

- **`lateral-dtype.lean` (`WAR_of_argmax`)**: a re-skin of `value_of_CM` (δ=0). Proves
  "CM-defect=0 + hard argmax ⇒ diagonal ≥ each fixed option." Genuinely just the existing
  `value_of_CM` content relabelled "WAR." Listed as a checked thread core; it is a **second copy** of
  one already-confirmed fact, not new content.
- **`weak-endorsement.lean` (`equality_endorsement_implies_immodest`)**: the report itself notes it is
  an **independent re-proof** of `CM_implies_immodest` — i.e. a **duplicate** of a confirmed file's
  one-line tail. Counting it as a distinct "finite core" inflates the apparent corpus.
- **`stag_hunt_select`**: the red-team and Lean-verify agree `hb,hc` are **inert**; the checked
  statement is the bare `hgap ⇒ c ≤ (1-δ)b`, true for *any* `b,c`. The "Stag-Hunt selection bridge"
  framing is **docstring-only**; the kernel proves a rearrangement. The report's D6 row ("2×2
  Stag-Hunt bridge & converse … KERNEL-CHECKED") over-credits a one-line inequality.
- **`weak-endorsement-deference.lean` (`hard_endorsement_liar_unsat`)**: the red-team showed the
  load-bearing hypothesis `hw : 0<Ew` is **the model's weakest, contested step** (it presumes
  `E_now(w)>0` for a hard, non-ℙ-generable indicator), and the satisfiability companion `(B)` "rules
  out vacuity" only as a generic one-sided slope, **silent about the actual liar**. So the kernel
  result certifies "**IF** the contested oscillation premise, **THEN** clash" — strictly weaker than
  the prose "hard endorsement on the liar is unsatisfiable." The report's §3.1 *does* recommend the
  value-vs-demand fix (good) but still lists the **current** `hard_endorsement_liar_unsat` as a
  checked core of D1 without foregrounding that its informal force = the strength of an unearned
  hypothesis. The honest fix (`condval=0` vs `condval=t`) is **not yet written** — it is a Phase-0
  to-do, so D1's "finite cores PROVED" should read "**one of which currently imports the contested
  step; the paper-clean restatement is a TODO.**"

**Common pattern:** the report's recurring phrase "finite algebraic core of every thread, kernel-
checked" is true and is good hygiene, but as *synthesis rhetoric* it converts "we Lean-checked the
trivial shadow" into "the thread has machine-checked support." **The uniform honesty boundary
(no LI machinery anywhere; everything enters as scalar/hypothesis) means NONE of the 11 new files
checks a single cross-agent or asymptotic trust claim.** That sentence exists in §4 but should be the
*first* sentence a principal reads about the Lean, not the last.

**Fix.** Add a one-line header to the Lean table: *"All 11 files check finite δ=0 shadows; 2 are
duplicates of confirmed results; 1 imports a contested hypothesis; none checks any LI/asymptotic/
cross-agent statement. Net new *deference* content kernel-checked this run: the corrigibility
sign-flip duality and the legitimacy-defect sign — and even those are pointwise encodings."*

---

## 5. [MAJOR] The corrigibility sign-flip — the report's crispest "limit result" — is real but the report over-reads it as a corrigibility theorem.

`endorsed_signal_complies` / `adversarial_signal_resists` (the "same weighted sum flips sign")
**is** the most genuinely interesting new checked content. But:

- "Endorsed" and "adversarial" are **pointwise sign encodings** (`s·(2d-1)≥0` resp. `≤0`), not
  derived from any cross-martingale or any model of *why* a signal is endorsed. So the theorem is:
  *"a weighted sum is ≥0 if every term is ≥0, and ≤0 if every term is ≤0."* That is **`Finset.sum`
  monotonicity**. The *content* is entirely in the INTERPRETATION that `s·(2d-1)` encodes
  endorsement-faithfulness — which is exactly the unproven D3 object again.
- The red-team flagged (and the report under-relays) that the conclusions are **weak** (`≤`/`≥`):
  `s≡0` satisfies both `hfire`s and gives `adv=0`. So "complies" is **never strict** — the theorem
  buys weak preference, i.e. "**does not strictly prefer to resist**," not "**actively complies**."
  A principal reading "AI complies with endorsed shutdown" overreads a `≥0`.

The structural moral ("corrigibility-as-endorsement cannot be unconditional; a saboteur's signal
flips the sign") is correct and worth keeping. But it is a **statement about the encoding**, not a
limitative theorem about corrigibility-in-LI. The Soares-et-al. analogy is apt rhetorically and
unearned formally (no shutdown utility, no LI dynamics).

**Fix.** Bill it as: *"finite illustration that an endorsement-weighted comply-incentive is
sign-determined by the signal; if a saboteur controls the signal sign, the incentive flips. This
encodes — does not derive — the corrigibility/endorsement link, and yields only weak (non-strict)
preference."* Drop the implication that corrigibility's limits are *proved*.

---

## 6. [MAJOR] The wirehead-decline is mislabeled in the report's own D5 row despite the red-team fix.

The red-team's counterexample (euphoric-but-numb drug: average report rises +3/40, yet witness defect
`+1/40 > 0`) shows "wirehead drives the defect negative" is **false as a consequence of "average
report rises"**; it needs *pointwise* overstatement, and even then "declines" is a **tie**
(`V_now(drug)=V_now(abstain)`), i.e. "never strictly prefers the drug." The report's §3.3 *does*
incorporate this. **But the D5 ranking-table row still says** "a pointwise-overstating 'drug'
successor drives the legitimacy defect ≤0 … ⇒ abstention," and the prose elsewhere ("AI avoids
wireheading the way people avoid addictive drugs") **re-imports the strict-preference reading the
counterexample killed.** Abstention here is *indifference broken toward not-acting*, not a positive
incentive to abstain. The drug-self is "happier and self-coherent yet illegitimate-to-N" — but the
formal object only delivers **`defect ≤ 0` on a pointwise-overstating subclass**, which is a *much*
narrower and less evocative claim than "AI declines addictive drugs."

**Fix.** Make the D5 row say "`defect ≤ 0` for the **pointwise-overstating** subclass (strict only on
positive-mass overshoot); current-endorsement gives **indifference**, read as no-take. A drug that
merely raises *average* reported utility need not be declined (euphoric-but-numb counterexample)."
Drop "drives the defect negative" everywhere.

---

## 7. [MAJOR] The unifying "coarsen-then-trust" cross-connection and the D6 "shared open characterization" are decorative, not load-bearing — and the report leans on them.

- **"coarsen-then-trust" (lateral W4, INTERPRETATION):** the claim that the merge (temporal
  coarsening by `f`), the intentional stance (semantic coarsening by `α`), and size-evasion are "one
  operation" is a **suggestive analogy with no theorem**. It is flagged INTERPRETATION in `lateral.md`
  but the report's §2 elevates it to a "Cross-cutting structural unifier (strongly argued)" that
  "suggests D2, D3, D11 are studying the same theorem." There is no shared formal object — `f` is a
  deferral function (time), `α` is an abstraction map (semantics); calling both "coarsening" is a
  pun unless someone produces a common construction (e.g. a single functor with `f` and `α` as
  instances). **No such construction exists in the corpus.** A referee should not let an
  acknowledged-INTERPRETATION become a structural claim in the synthesis.

- **D6↔D3 "shared characterization" (report §3.2):** "this single object [D3] also answers 'when may
  a UDT1.0 inductor believe it is UDT1.1?'" — but the D6 work contains **no logical inductor**; it is
  a finite PF bound (`(1-δ)Δ ≤ δ·range`) and a 2×2 Stag-Hunt. The bridge from "cross-agent LI trust"
  to "self-belief in reflective oracles" is asserted, never constructed. The red-team further showed
  the D6 headline ("naive bound undershoots; honest bound `δ/(1-δ)`") is **formalization-dependent**:
  under the natural R1 reading the principal's `δ·range` is *correct*; only the contaminated-objective
  R2 inflates it. The report relays this as "SALVAGEABLE — formalization-dependent" but keeps the
  `δ/(1-δ)` constant in the D6 row as if it were *the* answer.

**Fix.** Demote "coarsen-then-trust" back to "a speculative unifying analogy (no shared construction
yet)." In D6, lead with the **R1-vs-R2 dichotomy** as the result (the red-team's recommendation), not
the `δ/(1-δ)` bound; delete the unargued D6↔D3 identification or downgrade it to "conjectured
analogy."

---

## 8. [MAJOR] Agenda items that got shallow or no treatment.

- **"What is a decision problem?" (dependent type / CDT-vs-EDT / tiling):** handled only in
  `lateral.md` Part 1 as INTERPRETATION + a re-skin Lean (`lateral-dtype` = `value_of_CM` again). The
  principal flagged the dependent-type fix and the "rich by whose measure?" problem as wanting real
  work; the lab gives a (correct, standard) Π-type observation and an analogy to control-endorsement.
  **No new formal result.** The "germ-UDT / sheaf-locality" idea (1.4) is a genuinely novel
  CONJECTURE but is one paragraph and unpursued.
- **Agency & Abstraction / Vingean agency (D11):** SKETCHED + a thermostat counterexample; the actual
  deliverable (a finite value-of-info ≥0 lemma discharging Q6) is **not produced**, only flagged as
  "Lean-adjacent." The Blackwell-monotone-abstraction characterization is INTERPRETATION.
- **Aumann-fails-under-modesty (D9):** CONJECTURE, "finite 3-world example is LEAN-ABLE" — **not
  built.** This is arguably the *most directly principal-relevant* item ("the AI disagrees with me"
  reframed) and the most clearly summer-tractable finite example, and it was left as a conjecture
  with no example. **Missed low-hanging fruit.**
- **Legitimacy non-transitivity (D12) / trust-laundering:** CONJECTURE, "close to DDB 7.2.4," not
  developed. Delegation-closure is a concrete safety concern (multi-agent AI) and got one table row.
- **Christiano's reflective-probability framework** (AGENDA explicitly suggests it as an alternative
  setting): **not engaged anywhere.**
- **Updatelessness ↔ Geometric-UDT "updateful about values, updateless about the rest"** (the
  principal's actual conjecture): appears only as the `node_value`-from-`U` fix recommendation; the
  *value/factual asymmetry* (D10) is "factual half near-trivial, asymmetry CONJECTURE" — the
  interesting half is conjectured.

**Net:** the lab went **deep on the LI-self-trust spine** (which was largely already done in v2) and
**shallow on every item requiring a genuinely new construction** (merge discharge, updateless
characterization, Vingean lemma, Aumann example, non-transitivity). The report's breadth table makes
coverage look more even than it is.

**Fix.** Add a "coverage honesty" note: items with *new formal results this run* = {corrigibility
sign-flip, legitimacy-defect sign, the R1-vs-R2 dichotomy, the merge *reduction* (not its discharge)}.
Everything else is re-skin, conjecture, or interpretation. Build the D9 finite example — it is the
cheapest real new result and was skipped.

---

## 9. [MINOR] Likely-false or already-known conjectures.

- **D8 maximality ("soft one-sided Self-Trust is the *strongest* diagonal-surviving schema"):** the
  report admits "strongest" is **not well-posed** (no partial order; incomparable survivors may
  exist). A conjecture that is not yet a well-formed statement should be flagged as *ill-posed*, not
  merely "CONJECTURE." Mild risk it is **false** (a soft two-sided schema on a δ-band excluding the
  diagonal is a plausible incomparable survivor — the report itself names this).
- **Lateral 3.2 "finite mutual soft-CM ⇒ both immodest ⇒ agents merge":** the "merge into one agent"
  step is SKETCHED via "a two-sided version of the §5.2 collapse" that **does not exist** (§5.2's
  soft⇒hard step is itself prose-only and is the lab's biggest acknowledged Lean gap). So this
  conjecture is built on an **unproven** foundation twice over. Plausibly true, but currently
  **air**.
- **D1 forward arm "weak endorsement ⇒ weak deference":** this is the soundest thread (it *is* v2 §3).
  No objection — but note it is **not new**; the report's "develop first / High tractability" is
  really "**consolidate what v2 already proved.**" Fine, but it is consolidation, not research.
- **"Aumann fails under modesty" (D9)** may be **already known** in the Geanakoplos / non-partitional
  literature (agreeing-to-disagree under non-partitional information is studied); the report does not
  check priorart. Risk of re-deriving a known negative result.

---

## 10. [MAJOR] The Lean↔informal correspondence: where a checked theorem does NOT mean its gloss.

Re-examining the audit and Lean-verify reports against the report's claims, the **audits are correct**
and I largely endorse them. The residual correspondence risks the report under-weights:

1. **`value_asymptotic` is the *only* file touching the asymptotic layer, and it ASSUMES all five LI
   theorems.** The report's "v2 §9 is honest" verdict is right, but a principal could read "Value is
   machine-checked" and miss that **the five LI theorems — the entire substance — are unproven
   hypotheses.** The honest one-liner: *"We checked that IF the LI paper's theorems hold, THEN the §3
   composition yields Value. We did not check the LI theorems."* This is buried in §4; it is the most
   important correspondence fact in the lab.
2. **`CM_implies_immodest` / `equality_endorsement_implies_immodest`**: the **soft⇒hard spectral-gap
   step — the only place finiteness is forced, the structural heart of §5.2 — is prose in both.** So
   the *finite-collapse impossibility* (the thing that explains why modesty needs infinite frames, the
   conceptual payoff the report leans on for "why LI") is **NOT machine-checked anywhere**; only its
   trivial tail is. The report says this (§4) but its D1/D8 rows ("finite cores PROVED & KERNEL-
   CHECKED," "finite skeleton KERNEL-CHECKED") let a reader think the impossibility is checked. It is
   not.
3. **`hsel` in `UDT11Belief`**: the pointwise→whole-policy reduction (the entire embedded-agency
   difficulty) is **assumed in a hypothesis**; the file is the whole-policy shadow. The report's D6
   row should not be read as checking embedded self-belief.

**Fix.** Put a single bolded sentence at the top of report §4: *"No logical-induction theorem and no
impossibility result is machine-checked anywhere in the lab; every Lean file checks a finite δ=0
algebraic shadow with the LI/impossibility content entered as hypotheses or left as prose. This is the
same boundary as the original `LeanDeference.lean`."*

---

## Prioritized summary for the principal

1. **[BLOCKER, §0+§1]** "The agenda reduces to one theorem" = "the agenda reduces to one *unsolved*
   problem." The merge — the flagship constructive payoff — is **hand-waved at B-inductor-ness, Hop 2,
   and B-observability**; "SALVAGEABLE" hides "discharged in zero cases." Do not believe humans-can-
   trust-AI follows from anything proved here.
2. **[BLOCKER, §3]** Updateless deference (D4) is a **tautology wrapper around argmax** with a
   hand-fed discriminator; its kernel-checked Lean is `argmax is optimal`, not deference. Re-rate it
   as broken-pending-the-EDT-fix; correct "6/6→3."
3. **[MAJOR, §4+§10]** **No LI theorem and no impossibility is machine-checked anywhere**; all 11 new
   files are finite δ=0 shadows (2 duplicates, 1 importing a contested step). The corpus checks
   *compositions and shadows*, never trust itself. Foreground this.
4. **[MAJOR, §2]** Positive merge results live **only on the good-feedback region — where trust is
   least needed**; the framework is **asymptotic-average only, silent on single high-stakes rounds.**
   These are scope limits, not footnotes.
5. **[MAJOR, §5–§7]** The corrigibility sign-flip and wirehead-decline are **pointwise-encoding
   illustrations giving only weak/indifferent preferences**, not corrigibility/wireheading theorems;
   "coarsen-then-trust" and D6↔D3 are **analogies, not shared constructions**; D6's real result is the
   R1-vs-R2 dichotomy, not `δ/(1-δ)`.
6. **[MAJOR, §8]** Genuinely-new formal results this run ≈ {corrigibility sign-flip, legitimacy sign,
   R1-vs-R2, the merge *reduction*}. Everything else is consolidation of v2, conjecture, or
   interpretation. The cheapest real new result (D9 finite Aumann example) was **skipped**; build it.
