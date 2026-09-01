# Final audit

The consolidation is complete only if a fresh agent can answer these from
canonical documents alone, without reconstructing round chronology. Each answer
below is short and names where the full account lives. **If an answer here
disagrees with a round record, this document and the ones it cites are current.**

---

**1. What is Answerability?**
The rules-governed system by which a reasoner's history incurs, carries, and
accounts for normative burdens. Each burden enters as an **answerability slice**
with a birth stage and fixed anchored content; it is thereafter Satisfied,
Disposed, or Remaining, and that decomposition is conserved across every
transition. For the learner it exports a **claim stream** `c^r_t` plus a set of
admissible service traces. → `CURRENT_THEORY.md` §5, `ANSWERABILITY_AND_SERVICE.md` §4.

**2. What is Actionability?**
What a unit of corrective authority accomplishes: a coercivity modulus `phi` with
`Work_N = sum a_t phi(d_t)`. Convergence holds **iff** `phi` is bounded away from
zero away from zero; convexity is not needed for convergence and buys only the
rate. It sits *beside* service allocation, not after it — the scheduler cannot
choose `phi`. → `CURRENT_THEORY.md` §3.3, §4.

**3. What is Progress?**
A two-stage structure, and the staging is canonical even though the bare name is not:

    service-weighted Progress  --Service Transport-->  claim-weighted Progress

*Service-weighted Progress*, `E_{nu^a_N}[d] -> 0` at rate `A_N^{-1/2}`, is the
learner-side mechanism theorem — what the machinery delivers; it always carries its
qualifier. *Claim-weighted Progress*, `E_{mu_N}[d] -> 0`, is the
Answerability-facing endpoint — what was actually owed. The second does not follow
from the first without a transport hypothesis.

**The bare word "Progress" means the claim-weighted form** (settled 2026-09-01), so
every Progress claim carries a transport hypothesis. → `CURRENT_THEORY.md` §3.6.

**4. What is service?**
**Allocated authority** `a = beta`, the enforcement multiplier fixed before the
market maker picks a price. Predictable and freely schedulable. It is *not*
realized corrective force, which is unschedulable, undefined under perfect
compliance, and anti-monotone in conformance. → `CURRENT_THEORY.md` §3.2.

**5. What is liability?**
The cumulative value of the enforcement position over the live assessment worlds —
signed and cumulative, with the identity `V_N = sum_t w_t(d_t - s_t)` on the
**signed** misfit. Force emits it as an obligation; the surrounding layer must
discharge it, and bounded liability is what buys substrate preservation.
→ `CURRENT_THEORY.md` §3.1, §3.5.

**6. What is affordability?**
The schematic question of whether the mechanism can meet the normative demand.
Bounded cumulative liability is *one realization* of it, not its definition.
Exactly characterized for exogenous friction: a persistent schedule fitting a
finite budget exists **iff** `liminf_t L_t(1) = 0`, for any star-shaped date cost.
→ `CURRENT_THEORY.md` §3.9.

**7. What is Service Transport?**
The interface primitive relating delivered service to inherited claims: an adapted
transport plan `T(t,s)` with the claim marginal, service feasibility, stability
`d_t <= L d_s + eps(t,s)` on its support, and a service-to-claim cap. It replaces
contiguity, which is exact for the array problem but not checkable at a finite
horizon, not quantitative, and false of bounded-delay service. The two routes are
**incomparable**. → `CURRENT_THEORY.md` §3.7.

**8. What does Sharp Timely Service prove?**
That under service (S), sharp-linear affordability (L), the MarketMaker ceiling
(M), nested assessment (N) and temporal stability (T),

    E_{mu^r_N}[d^r] <= L_r K_r (2 sqrt(B_r) + sqrt(U_r))/sqrt(A^r_N) + epsbar^r_N(T) + Dbar_r R^r_N/C^r_N ,

so the same liability budget that preserves the learner also drives settlement
friction to zero, leaving only the semantic change incurred while waiting.
→ `CURRENT_THEORY.md` §3.11.

**9. What assumptions does it not construct?**
A plan satisfying (S) and (L) simultaneously; the constants of (T); (L) in the
closed loop; necessity of bounded liability; a converse to the overload
certificate; that `F_r` is ever zero for a real norm. → `CURRENT_THEORY.md` §6.

**10. What part of legitimacy is still missing?**
Everything diachronic and everything counterfactual. Specifically: which reasons
survive a revision; what licenses disposition (equivalently, defeat); how content
transports across representational change *quantitatively*; what makes a successor
answerable to a predecessor; non-capture; and the legitimacy predicate itself,
which has never been written down. → `CURRENT_THEORY.md` §1, `OPEN_PROBLEMS.md`.

**11. Where does counterfactual non-capture enter?**
As an irreducible third pillar. Layers I and II are both blind to it by
construction: their instruments are *was the reason answered* and *could it be
afforded*, and neither sees whether the reason should have been generated at all.
The sharp evidence is that the older four-clause interface gives the **same**
verdict on laundering as on authorized nudging, because laundering runs through
the reason channel. → `LEGITIMACY_DECOMPOSITION.md` §1, `OPEN_PROBLEMS.md` §3.

**12. How is this intended to feed corrigibility?**
Deference needs more than "the advisor predicts well": it needs the principal's
later normative state to be one the principal's own reasons actually shaped and
could still shape. That is Answerability plus non-capture, with affordability as
the realizability side condition. No legitimacy theorem exists yet, so the
interface is a plan, not a result. → `ROADMAP.md` stage 6, `wiki/Deference.md`.

**13. Which prior art is actually being used?**
The test is whether the canonical proof would still stand if the source vanished.
**Direct mathematical dependency:** Gale–Hoffman / Horn, invoked by name in BD1's
sufficiency proof. **Formal substrate:** Logical Induction; imprecise-probability
coherence (Walley, Levi, Williams) for the credal state; convex projection, whose
variational inequality the enforcement compiler uses; and linear-programming duality,
for the exactness-under-Slater remark beside the overload certificate. **Conceptual
dependency:** Brandom's scorekeeping — which is also what gives answerability its
creditor/debtor shape — and Horty with the TMS line for reason representation.
**Verification target:** Carroll et al. on influenceable reward, and `Demski`'s learning-normativity
agenda. → `../../notes/PRIOR_ART.md`.

**14. Which apparent prior art is merely adjacent?**
Contiguity (Le Cam) — the *definition* is inherited, but T1 argues from it directly
via Markov and invokes no lemma. Jackson/EDD — BD2 is a four-line exchange argument
invoking nothing. The Farkas *soundness* theorem, which is self-contained even though
the certificate has that shape. Online competitive analysis — vocabulary only.
Submodular and covering-with-delay optimization — analogues, never inputs.

**The two lists moved during the September cleanup.** Gale–Hoffman was previously
listed as adjacent while the proof invoked it; that was wrong and is corrected.
Independent rediscovery is a fact about our process and never settles dependency —
the proof does. Nine places are marked **literature review needed**, and no novelty
claim should be made outside this repository until they are closed.
→ `../../notes/PRIOR_ART.md` §6.

**15. What are the next three research problems?**
(i) **Certifying semantic transport** — where do the (T) constants come from? The
candidate mechanism is the note's anchored interpretation, and the gap is that it
is ordinal where `eps` is metric. (ii) **Authorized disposition**, which is
simultaneously defeat, the laundering channel, and the repair to EV1's claim-mass
hypothesis. (iii) **The legitimacy predicate** — cheap, undone, and it determines
what non-capture must protect. → `ROADMAP.md`.

**16. Which older concepts should not be revived?**
Rate-region or time-sharing geometry of authority (the budget is a consumable
stock; wrong twice from two directions). Realized force as a service measure
(inverts the sign of successful learning). Any gap or density condition on cheap
dates as a substitute for `D4` (three failed attempts). Also not worth further
energy: sharpening the online competitive ratio for accumulated authority (proved
impossible), improving the exogenous persistence criterion (exact already), and
extending the affordability round. → `SUPERSESSION.md` §4, `ROADMAP.md`.

---

## Self-assessment

**Answerable from canonical documents: all sixteen.** Questions 1–9 and 13–16 are
answered by documents in this directory plus the prior-art note. Questions 10–12
are answered as *statements of what is missing*, which is the honest form.

**Where the audit is weakest.** Question 12 has no theorem behind it, only a plan.
Question 3 carries a reserved decision, but the reservation is now confined to the
*name*: the two-stage structure is stated canonically, so a reader knows what the
program holds even without knowing what it will eventually be called.

**One thing the audit cannot check.** Every "yes" above is about internal
consistency — that the canonical documents agree with each other and with the
sources. It is not a check that they are *right*. The repository default is
`ci-only`: no maintainer has vouched for this content, and a fresh agent should
treat a coherent story as a coherent story rather than as a reviewed one.
