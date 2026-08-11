# Trust Between Logical Inductors — Technical Summary

*A consolidated record of the construction and design choices explored for a formal paper on deference and trust between logical inductors of different computational strength. Organized so that dead approaches and live approaches are clearly separated, with the provable negative results that close the dead branches stated explicitly.*

---

## 1. Setup and necessary context

**The object of study.** Two logical inductors (Garrabrant et al., arXiv 1609.03543) of different computational strength interacting over a shared world, and the question of whether — and on which sentences — the weaker one is *forced* to trust the stronger one's published opinions.

**The shared world.** Fix a propositional language $\mathcal{L}$ with sentence set $\mathcal{S}$, a consistent theory $\Gamma$ able to represent computable functions, and a $\Gamma$-complete **computable** deductive process $D = (D^1, D^2, \dots)$ that reveals $\Gamma$'s theorems over time. A sentence is **decidable** if $D$ eventually settles it; its settled value is its truth value, and this is the only notion of truth in the construction. The decidable/undecidable split is load-bearing throughout: it is exactly the boundary between where forcing can and cannot reach.

**The two reasoners.** Fix complexity classes $\mathcal{C}_H \subseteq \mathcal{C}_A$ (concretely $\mathrm{P} \subseteq \mathrm{EXP}$), each closed under polynomial overhead and computably enumerable. $H$ is the weaker reasoner; $A$ the stronger. $A$ predicts $H$ with lookahead $F(n)$, canonically $F(n) = 2^n$.

**Recurring objects.** $C_n$ / $P^{(n)}$, the contract (an effectively enumerated proposition) being quoted on; $a_n := A_n(C_n)$, $A$'s published day-$n$ quote; $Y_n$, the settlement value the contract pays out; $H^+$, the weaker reasoner *augmented to read $A$'s published quotes*; and the schedules $F$ (deferral), $e$ (emission), $\sigma$ (settlement). **The choice of $Y_n$ is the single most consequential design decision in the project**, and the dead/live boundary runs straight through it (§2.2, §4).

**The governing question.** Garrabrant's self-trust theorem (4.12) forces an inductor to trust its *own* future prices, because there the prices are simultaneously the subject and the resolution criterion of the bet — identity of the agent across time powers the Dutch book. The entire project asks what analog survives when truster and trusted are **distinct agents**. The short answer, established early and never overturned, is that nothing survives *in the forced/Dutch-book sense*; the work since has been finding the strongest true replacement.

A joint-market reformulation (a single market over a language enlarged to include statements about $A$'s prices) was considered as a distinct alternative architecture and is not pursued here; it buys stronger forced statements only by collapsing toward a single agent, which changes the question rather than answering it.

A secondary, fully impersonal motivation runs underneath: the undecidable fragment — where forcing provably cannot reach — is a candidate formal model for genuinely open, never-settled questions, which is part of why the location of the forcing boundary is treated as the real content rather than a technicality.

---

## 2. Dead approaches and the negative results that close them

### 2.1 Two distinct inductors, $A$ predicts $H$, hoping for forced trust

**Setup.** $A$ is a market whose shares on $\phi$ pay out $H_{F(n)}(\phi)$; $A$'s traders may see both price histories through day $n$. Existence is by Garrabrant's standard construction.

**What is true and survives.** *Tracking*: $A$'s prices are forced, by the LI criterion against $H$-aware traders, to track the best efficiently-computable predictor of $H$'s future state from $H$'s observable history. *Per-sentence convergence*: for any **fixed** $\phi$, $A_\infty(\phi) = H_\infty(\phi)$ holds **unconditionally** (the trivial predictor $H_n(\phi)\to H_\infty(\phi)$ already suffices).

**The negative result (No-Forced-Trust).**

> There is no efficiently-checkable relation between two distinct inductors whose satisfaction Dutch-book-forces $H_\infty = A_\infty$ on undecidable sentences.

Precisely:
- On **decidable** $\phi$, forced calibration and forced agreement hold — but there they are idle, since both sides can compute the answer anyway.
- On **undecidable** $\phi$ (the cases that matter), closing the gap requires *inductive generalization* from "$A$ is calibrated on decidable cases" to "$A$ is reliable on undecidable cases." This is permitted by the LI framework (non-dogmatism / pattern-learning) but is **not Dutch-book-forced**. This is the exact, fully localized obstruction.
- The only three ways to force agreement all dissolve the problem: (i) add inductive generalization beyond coherence; (ii) treat $A$'s prices as the resolution criterion, which *is* assuming trust rather than deriving it; (iii) merge the agents, after which it is just self-trust and "the other stops being other."
- *Limit equality is badly conditional.* Any nontrivial efficiently-checkable relation pins $A_\infty$ only on the class where $H_\infty$ is e.c.-recoverable from observable price history. Over rich theories (e.g. PA), limit values on independent sentences are not poly-time recoverable, so equality cannot be forced there.

**Why it's dead, and why that's a result.** Forced other-trust analogous to self-trust is impossible by the structure of the framework, not by a defect of the construction: self-trust is powered by temporal identity of the agent, and there is no analog across distinct agents. Stated as a theorem, this is informative — it pinpoints that any real trust must supply inductive structure, shared resolutions, or merger, none of which coherence alone provides.

### 2.2 The self-referential settlement target $Y_n = H^+_{F(n)}(P^{(n)})$

This is the sharpest dead end, and the one whose failure *derives* the live construction. The motivation was to model the realistic case — the reasoner who has *heard* the AI — by settling contracts against $H^+$'s **own** future credence. Read through, this makes $A$ a fast mirror of $H^+$'s future self ("trust in $A$ = self-trust through a mirror"). Two independent provable negatives kill it as a **universal pointwise** theorem.

**Negative result 2a — anti-inductive counterexample (kills universal pointwise calibration even with unlimited compute).** A calibration theorem must be quantified over an *effective enumeration* of propositions — universality is constitutive. But the effective family then contains anti-inductive instances whose settlement behaves like $\mathbb{1}[a_n \le 1/2]$ (expressible because the quote atoms sit in $H^+$'s own language). For these, *every* possible quote satisfies

$$|a_n - Y_n| \ \ge\ \tfrac12 - o(1).$$

This is the $\chi$-paradox transplanted from the **sentence** level to the **settlement** level. At sentence level the LI framework survives self-reference through trader *continuity*; but a deductive process is a hard $0/1$ oracle, and grid-rounding makes the dependence **discontinuous by construction**, so the continuity escape is gone. Universal pointwise calibration is therefore *false* for the family, independent of compute.

**Negative result 2b — cost-circularity (makes the power assumption unsatisfiable).** Timely per-instance calibration needs a $\mathcal{C}_A$-trader that computes $Y_n$ at stage $n$. If $Y_n$ depends on $A$'s own run, the class $\mathcal{C}_A$ must contain its own market's simulation cost: writing $R$ for total coupled cost with $R \ge R_A$,

$$\mathcal{C}_A \ni R\circ F \ \Longrightarrow\ R_A(n) \gtrsim R_A(F(n)) > R_A(n),$$

a contradiction, and in any settlement language entangled with $A$'s prices a simulate-and-arbitrage trader turns the regress into an explicit exploitation. No satisfiable power assumption of this shape exists.

**The dichotomy these two results force.**

> If the contract family is effective and pointwise timely calibration is provable from a *satisfiable* power assumption, then the settlement map must be **reflectively blind** (independent of $A$'s own quotes). Equivalently: *predictable iff uninfluenced.*

Blindness is the contrapositive of the two impossibilities — derived, not assumed. The paper should state 2a and 2b as propositions *first*, then define blindness as their closure. (Scope caveat to attach: the derivation is internal to this architecture — LI markets, deductive-process settlement, grid rounding — and is not claimed for arbitrary prediction frameworks.)

**What is *not* killed (important for not over-claiming the negative).** With the self-referential target:
- *Externalized self-trust for a fixed $\mathcal{C}_H$-computable contract sequence* is provable by a single inter-temporal arbitrage: under-pricing today is exploited on a round-trip to $F(n)$ where Tracking pins the resale value (the non-triviality relocates cleanly into Tracking plus contract design). This requires a one-sided continuous indicator (so the conclusion lands at exactly $p_n$, not $p_n \pm \delta$).
- *Gated and classwise-averaged* deference statements survive.

What dies is only the **universal pointwise** version — and with it the ambition to make "self-trust through a mirror" the *headline*. That reading is also double-edged on its own terms: because $A$ merely echoes where $H^+$ is heading, the trace cannot distinguish faithful prediction from steering, which is precisely the manipulation attack surface (§6). So the mirror theorem is real but cannot carry the paper, and the self-referential target cannot ground a universal calibration claim.

---

## 3. Substrate choice: universal vs logical inductors

This fork is genuinely load-bearing and maps directly onto the dead/live boundary, so it deserves its own treatment.

**The two substrates.** A plain **logical inductor** is a price sequence over sentences, unexploitable by traders in its class — a finite-support belief state at each stage. A **universal (measure-valued) inductor** carries a genuine probability measure over completions (Garrabrant, "Universal Inductors"; Diffractor's patch), and crucially supports **measure-theoretic conditioning** (Theorem 4.7.2, Closure Under Conditioning).

**The decision hinges entirely on how $H^+$ is built.**

- **Conditioning route ⇒ universal inductor required.** If $H^+$ is built as $H$ *conditioned* on the quote ledger $Q_A$, then $H$ must be a universal inductor: you cannot measure-theoretically condition a finite-support belief state, whereas conditioning a measure is exactly the operation. What this buys is that $H^+$ **carries $H$'s prior joint beliefs about (quote, outcome)** — the ingredient needed for a *genuine* Bayesian-update deference result (an expectation ranging over a quote $H^+$ has not yet seen, rather than a number already sitting in front of it). The cost: Theorem 4.7.2 requires the conditioning sequence $Q_A$ to be **efficiently computable**, which is the sole place the cost bound $e \ge R(n)$ on the emission schedule lives.

- **Direct-founding route ⇒ plain logical inductors suffice.** If $H^+$ is founded *directly* as a logical inductor over $D_H$ extended with quote atoms (no conditioning), universal inductors can be **dropped entirely**. The cost: $H^+$ no longer automatically carries $H$'s prior, and because the extended deductive process injects values computed from the inductors' own earlier outputs, one owes an **introspective-process existence lemma** (≈80% the standard LIA existence proof tolerates a process defined from the inductor's own earlier prices; below 100% precisely because that self-reference is non-standard). In exchange, blindness buys real proof economy and makes the universal quantifier in the calibration theorem sound.

**$A$ is a plain logical inductor either way.** $A$ is built fresh over $D_A$ via the existence theorem and is never conditioned, so it needs only a *computable* $D_A$ (deductive processes need merely be computable, Def. 3.2.1 / Thm. 3.6.1) and incurs no efficiency requirement on $\sigma$. An earlier belief that $A$ also had to be universal/efficiently-conditioned was traced to over-reading the "a universal inductor just is a conditioned bitstring inductor" framing and was dropped: the instant $A$ is a plain LI, the conditioning theorem and its e.c. demand stop touching it.

**Why the project moved off universal inductors.** The conditioning/universal substrate's distinctive payoff is the genuine-conditional-expectation deference result — and the *cleanest* form of that result was tied to the self-referential target $Y_n = H^+_{F(n)}(P^{(n)})$, which §2.2 shows is twice-impossible as a universal statement. The same Bayesian-update *content* (an expectation over a not-yet-published quote) is recoverable on the plain-LI construction without any measure-conditioning: price a ledger contract on $A$'s *future* quote and add one reflection axiom internalizing "this contract settles to the intended future credence." So universal inductors turned out to be **not necessary even for the result they were introduced to secure** — the reflection axiom substitutes for measure-conditioning — and they carry the existence/efficiency overhead besides.

(Universal inductors remain attractive in *neighboring* problems for an unrelated reason — they implement an automatic Solomonoff/Occam prior and dominate the universal semimeasure (4.6.5) — but that prior-structure payoff is not what the trust construction needs.)

**Net recommendation as the logs stand:** plain logical inductors + direct founding + reflectively-blind autonomous target is the coherent live package; the universal/conditioning substrate is the right tool only if a result specifically requires conditioning a genuine measure that the reflection-axiom route cannot reproduce, which has not so far been identified.

---

## 4. Live approach: autonomous target + reflectively blind settlement

This is the live core. It is exactly what §2.2's dichotomy forces.

**Setup, precisely.**
- **Shared world** as in §1: $(\mathcal{L}, \Gamma, D)$ with $D$ $\Gamma$-complete and computable; decidable = settled by $D$; settled value = truth.
- **Reasoners** $\mathcal{C}_H \subseteq \mathcal{C}_A$, each a plain logical inductor.
- **Ledger channel ($H$ reads $A$'s conclusions).** Extend to $\mathcal{L}^+ = \mathcal{L} \cup \{\text{quote atoms}\}$ recording $A$'s published price rounded to $1/n$ on day $n$, via threshold atoms "$A$'s quote $\ge k/n$" with monotonicity axioms. Extend $D$ to $D^+$, which settles each quote atom at the value $A$ actually published, with one day's delay. Since $A$ is a computable belief sequence these are decidable facts, so $D^+$ is again computable, consistent, complete. The ledger puts $A$'s **conclusions** (its numbers, not its reasoning) into $H$'s world as ordinary settled facts.
- **Autonomous, reflectively-blind target.** Contracts settle against the **autonomous** $H$: $Y_n := H_{F(n)}(P^{(n)})$, where $H$ never reads $A$. This zeroes the derivative of the settlement with respect to $A$'s quotes, which is what makes the universal "for all $n$" sound.
- **$H^+$** is founded directly over $D_H \oplus$ quote atoms (no conditioning); plain LI against $\mathcal{C}_H$.

**Schedules and computational assumptions, cleaned.** The earlier overbuilt assumption set collapsed to: an ordering $e(n) < F(n) < \sigma(n)$ kept only as interpretive convention (not a proof obligation), with the one genuine cost bound being the emission bound $e \ge R$ (the publication schedule dominates the coupled cost) read by $H^+$; $R$ is the *total coupled-construction* cost; $A$ needs only computable $D_A$, so the previously-argued $\sigma \ge R(F(n))$ condition was dropped. The "more powerful reasoner" assumption split into named **Regularity** and **Power** conditions with explicit usage annotations; its surviving job is to keep $R$ a tame $\mathcal{C}_A$-bounded function so a dominating $e$ exists, not "so the bets resolve."

**The theorem suite (what is provable here).**
1. **Calibration / Tracking** — pointwise, timely: $a_n - Y_n \to 0$ over the *effective enumeration* of contracts, sound precisely because the target is blind. (The forcing-strength step has the one identified gap; see §5.)
2. **Meta-trust** — pointwise, timely, via provability induction.
3. **Expectation-deference** — the genuine conditional-expectation statement
   $$\mathbb{E}^{H^+}_{n+1}\!\big[\mathbb{1}(P^{(n)}) \,\big|\, a_n\big] \simeq_n a_n,$$
   made rigorous by orthogonality to **all** continuous quote-measurable test weights $w_n = w(a_n)$ (the earlier single-bin "ramp" is just the $w\equiv 1$ instance; the standalone corollary is absorbed as that special case). This is the genuine-update content, obtained without measure-conditioning.
4. **Object-deference** — only in **gated / classwise-averaged** form (4.3.8-style, on $D$-decidable subsequences), and **provably not more**: the anti-inductive counterexample of §2.2 is exactly the obstruction to a pointwise object-level version, so the averaged ceiling is tight rather than a proof-weakness.
5. **Prediction/influence dichotomy** — as a standalone, impossibility-flavored theorem: **prediction of the uninfluenced reasoner is provable, pointwise, timely; influence on the influenced reasoner is underdetermined**, with only averaged/gated theorems available and provably no more. This conservation law is the manipulation worry rendered as a theorem rather than a complaint.

**The honest cost, to be chewed visibly in the paper.** The *predicted* reasoner ($H$, unadvised) and the *advised* reasoner ($H^+$, the realistic one) are different objects, so the headline is about a counterfactual: $A$ predicts what the reasoner *would have* concluded unadvised. The defense is three-part and principled, not ad hoc: (i) the alternative is twice-impossible (§2.2), so blindness is *derived*, the constructive half of a dichotomy; (ii) it coincides with the stop-gradient / non-performative move in the performative-prediction literature, reached from a different formalism — evidence the joint is real; (iii) it has a clean normative reading: good advice moves your advised self toward your unadvised, more-deliberated self, preserving epistemic autonomy by construction. The deflationary objection ("a bigger machine just looks ahead") must be pre-empted directly: the contribution is the **certification-and-transfer chain**, where the provability-induction step does work nothing else does — not the prediction itself.

**Status: live.** Verdict from the working notes: ≈80% worth carrying in this form, conditional on a relativization appendix.

---

## 5. Live refinement: the two-channel (ledger + audit) version

The most recent framing keeps everything in §4 and adds the second direction of sight, plus the project's strongest safety result. It is best read as a *consolidation and sharpening* of §4, not a new construction.

**What it adds: the audit channel.** Alongside the ledger ($H$ reads $A$'s conclusions), $A$'s traders are permitted to use $H$'s past prices (one-day delayed) as inputs to their strategies. The two channels point in opposite directions — $H$ sees $A$'s numbers, $A$ sees $H$'s beliefs — and that opposition is the whole content. The audit direction is what lets a trader exploit persistent $H$–$A$ disagreement on sentences that will settle, which is the engine of forcing.

**The central safety property.**

> Settlement-powered forcing is **co-extensive with the availability of settlement**, and goes **silent** the instant settlement is withdrawn.

The exploiting trader earns by a bank-and-rebuy cycle (buy → wait for settlement → bank → rebuy). On a sentence that never settles there is nothing to bank: the trader can act at most once, never recovers budget, and freezes. It does not *decide* to spare undecidables — it *cannot accumulate* against them. This is half-built into Garrabrant already: the feedback trader's budget is released by the `MO` ("maybe open") settlement detector, which never fires on a sentence that never enters $D$.

**Two nested layers of safety.** Because the budget can only be *timed* to release when the settlement schedule is computable, the trader also goes silent on sentences that are decidable but lack *good feedback* (no computable settlement schedule). The forcing's true support is the **good-feedback fragment ⊂ decidable fragment ⊂ outside the undecidable danger zone**.

*(A small numerical check of this silence property was run to confirm the worth-set is unbounded-above in the settling case and bounded both ways in the non-settling case; it is omitted here. It corroborated the property mechanically but is not a substitute for the general theorem — it imposes persistent disagreement and a calibrated quote rather than deriving them, and mechanizes only one of the two valid forcing traders.)*

**What is preserved from §4.** Decidability = truth; the reflectively-blind / autonomous logic and its consequence that forcing is silent on undecidables; the full calibration/meta-trust/expectation-deference suite; plain logical inductors throughout; and the prediction/influence dichotomy.

**What changes or is newly qualified.**
- The **safety/uplift robustness asymmetry** becomes explicit and is the most important structural takeaway: the *safety* clauses depend on the forcing being *confined*, so they are **robust to the main forcing theorem being weak** (less forcing = more freedom = safer); they are threatened only by forcing being *too strong* (leaking past good feedback) — and that single failure mode is exactly what the silence property guards. The *uplift* clause depends on the forcing theorem's two unverified steps, so if that theorem is weaker than hoped, uplift shrinks but safety is untouched. The worst case for uplift is "less gain than hoped"; the worst case for safety would be "deference leaks onto undecidables," which the construction provably prevents.
- One earlier over-clean claim is **narrowed**: "the LI criterion is the safe policy" still holds (the criterion never *forces* unsafe deference and gates itself with no classification step), but the claim that *voluntarily* exceeding it is always harmless fails on the **decidable-but-unforceable** fragment, where voluntary over-deference is genuine error, not benign authorship. This *strengthens* the case for sticking to the criterion.
- The earlier $\theta$-audit feedback item was found vestigial and dropped: with the inter-temporal-arbitrage proof, the construction reduces to the base process plus the quote ledger, which also better matches the "augment $H$ with the ability to read $A$'s quotes" story.

**The identified open work.** The forcing/uplift theorem's pointwise conclusion still needs two steps: (i) the joint good-feedback of the disagreement weighting, and (ii) the patient-weighting-to-diagonal lift. The precise crux is a **quote-stability sub-lemma**. These are isolated, named, and entirely on the uplift side — never the safety side.

**Status: live, and the best current home for the safety half of the paper.**

---

## 6. Structural findings that sit across the live construction

These are not failed approaches; they are limiting facts the live construction must state honestly.

**Non-conservativity as an operation on limit credences.** The augmented process is a *deductively* conservative extension but is **non-conservative as an operation on limit credences**. The correct slogan is not "$A$'s quotes move the limit" but "$A$, and all the trust it induces, **fails to pin** the endpoint."

**Equilibrium multiplicity = underdetermination, relocated.** The trust apparatus forms a self-consistent equilibrium at *every* deference level and selects none. External trust is **parasitic on self-trust** — $A$ mirrors the augmented reasoner's own deferred credence, so "trusting $A$" reduces to self-trust routed through a relay. This is the same phenomenon as the No-Forced-Trust result of §2.1, seen from inside the augmented reasoner, and it is the formal home of the never-settled residual.

**Manipulation attack surface.** The current construction structurally *cannot* exhibit the manipulation worry, because $A$ has no independent content to inject (external trust is parasitic, above). But equilibrium multiplicity reveals the attack surface: every endpoint passes all the trust tests. A manipulation theorem was sketched requiring (a) a second calibration condition separating calibration-to-self from calibration-to-truth; (b) an evidence/preemption distinction (the Bayesian-persuasion martingale bound holds in the evidence regime, preemption removes it); (c) a transfer-of-trust attack — earn authority on decidable sentences, spend it on undecidable ones; (d) non-recoverability as the formal statement that legitimacy certification is impossible from the trace.

**Certifiability impossibility.** A companion impossibility, framed in the causal paradigm with the LI construction as a concrete witness: one cannot certify *why* the advisor is right from its behavioral trace. The positive program is to characterize the "second channels" that would restore certifiability.

---

## 7. Overall findings: dead vs live

**Dead branches, with the result that closes each:**
1. *Two distinct inductors hoping for forced trust (§2.1).* Closed by **No-Forced-Trust**: forced agreement on undecidables is not derivable from coherence; self-trust is powered by agent identity, which distinct agents lack. Per-sentence convergence on fixed $\phi$ survives but is idle; uniform/forced trust on undecidables does not.
2. *Self-referential settlement target $Y_n = H^+_{F(n)}(P^{(n)})$ as a universal theorem (§2.2).* Closed twice over: the **anti-inductive counterexample** falsifies universal pointwise calibration even with unlimited compute, and the **cost-circularity** makes the power assumption unsatisfiable. Survivors: fixed-contract externalized self-trust and averaged/gated versions — not the universal statement, and not as the headline.
3. *Universal/conditioning substrate as a necessity (§3).* Not strictly dead, but demoted: its distinctive payoff was tied to the dead target, and the same Bayesian-update content is recoverable on plain logical inductors via a reflection axiom, so the universal substrate is no longer load-bearing.

**Live branches:**
1. *Autonomous target + reflectively-blind settlement, plain logical inductors, direct founding (§4).* Forced by the §2.2 dichotomy ("predictable iff uninfluenced"). Provable suite: pointwise timely calibration; meta-trust via provability induction; genuine expectation-deference via orthogonality to test weights; gated/averaged object-deference (tight, not weak); the prediction/influence dichotomy.
2. *The two-channel ledger + audit refinement (§5).* Adds the safety result — **settlement-powered forcing is co-extensive with settlement and silent on non-settling sentences**, with two nested safety layers — and makes explicit that safety is robust to the uplift theorem being weak and threatened only by forcing being too strong, the one mode the construction guards.

**Where the remaining risk sits.** Entirely on the *uplift* side — the strength of the forcing on the good-feedback fragment — concentrated in the named **quote-stability sub-lemma** and two isolated steps. The safety side is the part already mechanically corroborated. The failure mode of the open step is "less uplift than hoped," never "deference leaks onto undecidables."

**The honest contribution.** Not "a stronger machine predicts a weaker one," but the **certification-and-transfer chain** plus the **prediction/influence dichotomy** — a conservation law stating exactly how far forced trust can reach (the good-feedback fragment) and proving it cannot reach the undecidable cases where manipulation would live.

---

*Caveats: the impossibility derivations of §2.2 are internal to this architecture (LI markets, deductive-process settlement, grid rounding) and are not claimed for arbitrary prediction frameworks. On the finest technical points — the exact hypotheses of 4.7.2, the feedback-trader budget construction, the introspective-process existence lemma, the relativization appendix — the primary sources should be checked directly rather than trusted from this summary.*
