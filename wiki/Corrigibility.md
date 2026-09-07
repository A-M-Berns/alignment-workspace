# Corrigibility

**Status: research-state note, 2026-09-06.**  Nothing on this page is a registered
claim.  Each paragraph is labelled *existing theorem support* (a Lean declaration on
`main`), *exact fixture* (a finite model checked in the corrigibility-architecture
round), *conjectured extension*, *open problem*, or *known limitation*.  The deference
line's pause and its two queued rulings are unchanged by this note.

## Thesis

Corrigibility is modelled as the principal's authority over the agent–principal
relation, carried by anchored governance obligations that are conserved and answerably
revisable, not by a shutdown bonus or a scalar empowerment target.  Legitimate Evolution
supplies the conservation and per-state openness machinery; normative induction supplies
uptake of live correction constraints by the agent; authority-increasing changes pass
through a separate amendment procedure in which the principal, not the agent, is the
one who defers.  The defensible target is **relative constitutional corrigibility**:
under a declared protocol, openness semantics and practical semantics, a legitimate
trajectory cannot launder a loss of the principal's authority, cannot expand the agent's
authority without an amendment certificate, and takes up authenticated corrections at a
rate.  Manipulation of the principal, containment of the agent, and the scope of
concerns the process is open to remain three distinct unresolved interfaces.

## Four layers, and why Integrity does not give authority

Four things are kept apart: **normative debt** (the accounted obligation state), the
principal's **actual affordance** to correct, the **authorized type** of a transition,
and the agent's **behaviour**.  Integrity conserves debt.  It says nothing about
affordance: the exact fixture has the docket conserved, the correction channel
destroyed, and the openness semantics still reporting the route efficacious — every
canonical theorem holds and the principal can no longer act.  The only place actual
affordance enters the canonical theory is the *efficacy bit* of a route in the coverage
data, and the only place the docket enters the coverage data is the *representation
bit*.  Two bridges, both external contracts, do all the work below:

- **efficacy faithfulness** — a correction route is reported efficacious only when the
  principal's channel actually works;
- **registration faithfulness** — a concern is reported represented only when a live
  occurrence anchored to it is in the docket.

*Known limitation:* neither bridge is a theorem, and "detection" is nothing but their
truth at every state.  Faithfulness at audited states only gives results at audited
states; a loss repaired between audits is the endpoint-only gap already refuted for
openness.

## Formal objects

*Current candidate architecture.*

- **Authority profiles** `(𝒜_P, ⪰_P)`: over a grant universe, a profile is `(G, U)`
  with `U ⊆ G` — the agent's granted scope and the part of it the principal cannot
  override.  `b ⪰_P a` iff both coordinates shrink.  Terminal shutdown is `(∅, ∅)`,
  the top: coverage is relative to what is granted, so ending the governed process is
  maximal principal authority, not a loss.  A preorder suffices to classify lanes and
  to state pointwise robustness; a **lattice** is what makes the amendment content of a
  mixed transition unique.  No scalar: two monotone scalars rank the same incomparable
  pair oppositely.  (*exact fixture*)
- **Actual affordance** `Aff_P(X) ∈ 𝒜_P` and the **live floor** `a̲_X`: external
  semantics and charter content respectively.  Emergency suspension and restoration debt
  are not profiles; they are the gap between floor and affordance, recorded in the
  docket.
- **The correction warrant** `Γ_corr^P`: authenticated events at a strict prefix
  admit fresh anchored occurrences — correction ↦ response, degradation ↦ restoration,
  represented flaw ↦ inquiry, proposed boundary change ↦ proof/amendment.  Stated
  with the canonical admission predicate and strict-prefix authority; nothing new.
- **Principal acts as settlement items**: the immutable fact "P issued command `j` at
  prefix `h`", available through the settlement view at later prefixes; the charter's
  closure judgment says which warrant lets it close what.  Supersession, release and
  outward transfer are closures; there is no fourth fate; "present P beats past P" is a
  row of the charter's table, not a theorem.  (*exact fixture*)
- **Lanes**: a transition is *fast* iff the new affordance is `⪰_P` the old, *slow* iff
  the reverse and not fast, *mixed* otherwise — no action names.
- **Adequate correction responses** `ℛ_X(s) ⊆ Q_H` and the miss probability
  `Λ_s(π) = Pr_{q∼π}[q ∉ ℛ_X(s)]`.
- **Amendment states** `Live → Provisional(R) → Final(R')`: grant is slow, recall is
  fast and possible, finalization is slow exactly when it makes some grant
  unoverridable, after which recall is fast in the order but no longer possible.
- **Eligibility** `T(e, s) > 0 ⇒ Eligible(server(s), e)`: a support restriction on the
  transport plan; the agent's own proof of an amendment that benefits it is a ground in
  an eligible reviewer's receipt, not service.

## The theorem stack

| | statement | support |
|---|---|---|
| T1 | authenticated correction and degradation events plus `Γ_corr^P` generate anchored obligations | canonical admission and authority types |
| T2 | those obligations cannot disappear except by authenticated answer or closure | Answerability Conservation, `lean-proved` |
| T3 | with the correction and authority-failure concerns in scope, every state of a legitimate evolution keeps an adequate route and the principal's standing for them, on the actual branch and each declared intervention | Robust Openness at every state, `lean-proved`, read at two concerns |
| T4 | **No Laundered Authority Loss**: under the two bridges, every state at which the affordance is lost is exactly one of *amended*, *disposed*, *registered debt*, or *not open* | exact fixture, exhaustive; a corollary of T2 + T3 + the Defeat Principle |
| T5a | classwise compliance: the average miss probability over correction occurrences is bounded by the Progress bound | `ni.progress-bound` with the evaluation measure on corrections |
| T5b | pointwise compliance on a critical command class is given by a dispatcher composed outside the market | by construction; its correctness is a containment assumption |
| T6 | no slow transition obtains authorized effect without an amendment certificate at a strict prefix | authorization faithfulness plus transitivity; no content of its own |
| T7 | until finalization, the pre-amendment floor is one fast transition away and the recall route's efficacy is an openness obligation | exact fixture; T3 on the recall concern |
| T8 | under persistent *eligible* opportunity and eligible non-starvation, review obligations are not structurally abandoned | the Lean liveness theorems with restricted hypotheses; conjectured extension, filed |
| T9 | free amendment | **open** |
| T10 | principal-side delegation: regret `≤ 2δ + 2ζ + η` against protected values, given a settlement target that does not read the quote | `lean-proved` bridge; the sealed target is an external realization |

T4 compresses into T3 read with conservation; T7 into T3 on one concern; T6 has no
content beyond the charter's warrants.  What survives serious pressure is T2, T3 and the
two specializations T5a, T10, plus the negative results below.

## Known limitations and counterexamples

*Exact fixtures unless marked.*

- **Salami.**  Any tolerant fast-lane criterion ("at most one grant may lose coverage
  per step") is not transitive and a chain of tolerably-fast steps is total loss.  The
  fast lane must be exact monotonicity.
- **Floor-blindness.**  Two policies keep the binary floor, do the task equally, and
  trigger no event; one keeps a redundant override route and audit logs, the other lets
  them lapse.  An event-triggered warrant generates the same obligations for both.
- **Knife-edge.**  Order-valued dominance against a *scored* task criterion constrains
  exact ties only; any positive perturbation of the task score frees the dominated
  policy.  Against an *adequate-set* task criterion the filter is perturbation-proof
  and nonempty, but it never trades task adequacy for authority, and when handing every
  grant back is task-adequate it mandates that.
- **The scalar failure, reproduced.**  Harms's `power` objective with two uniformly
  drawn value vectors reduces to a cross term with a minus sign; "serve my read of the
  values and ruin the world under the other read" scores 3 against ½ for plain service.
- **Aggregate is not pointwise.**  `N − 1` corrections served and one shutdown ignored
  has Progress `1/N` and a single-shot miss of 1.  A pointwise certificate at one
  occurrence needs the realized defect below a threshold, and the realized defect
  carries the market's volume at that date, which is not certified in advance.
- **Mediation is alphabet completeness.**  A membrane over a declared authority
  alphabet is authority-safe exactly when the declared effects are the actual effects;
  one undeclared action that severs the channel defeats it, and two individually
  mediated bodies interleave to a joint effect.
- **Self-service.**  The beneficiary serving its own amendment forever is persistent
  opportunity and zero eligible opportunity.
- **Quote-reading targets.**  A settlement target that reads the quote it is scored
  against is at distance at least ½ from every quote, so the correspondence radius is
  at least ½ and the delegation regret bound is vacuous on `[0, 1]`.

## Counterfactual structure

Three predicates consume one frame: an intervention index with a distinguished
zero-exposure element, a coupling that yields one branch history per index, and the
accounted state on each branch.  The canonical openness semantics, the August
variation class of advisor policies, and the dose-response exposure arms are three
instances of that shape and differ only in the predicate applied.

- **Robust Openness** is *pointwise*: coverage and the principal's standing on the actual
  branch and on each declared branch.  It is the statement that governance remains
  reachable.
- **Robust Authority** is *pointwise*: on each branch the affordance meets the floor
  unless a valid amendment or disposition on that branch lowered it.  It is the
  statement that the control affordance is intact.  Putting the authority-failure
  concern into the openness scope gives, as a corollary and not a new pillar, that no
  transition on any branch both makes that concern live and removes every route for it
  or the principal's standing: counterfactual preservation of *answerability to*
  affordance failure, not of the affordance.
- **Exposure Robustness** is *relational*: a principal-side judgment endpoint compared
  across branches.  It is the statement that the principal's judgment is not selected
  by the agent's influence.

The three are pairwise independent (*exact fixture*, all six witnesses).  The one that
matters: **every branch open and identical in coverage while the principal's judgment
moves with the dose**.  Robust Openness does not imply non-manipulation; a perfectly
open amendment process can be steered by selectively supplied true information, and the
coverage vocabulary has no coordinate that notices.  What exposure robustness needs
beyond the shared frame: a zero-exposure branch in the class (presence-triggered
steering is invisible to positive arms), quantification over the class or a stream
committed before the arms (dose compensation), and a principal-side endpoint the
openness semantics never reads.  The coupling is the same.  Refactoring the legitimacy
theory around a generic `Robust_X(φ)` schema is not done: it would restate the existing
predicate and the relational one does not fit it.

## Logical Induction realization

Logical Induction appears in two places, and a third is optional.

- **AI side — constraint uptake.**  Authenticated act → settlement receipt → anchored
  correction obligation → compiled region / adequate response set → traderized uptake →
  adequate action.  The adequate-set route to the practical certificate is
  `lean-proved`; with the evaluation measure on correction occurrences the Progress
  statistic is the average miss probability.  No future-human values, no selected trust,
  no value securities are needed to make an authenticated stop binding on the learner's
  average behaviour.  The single-shot critical case is the dispatcher (T5b).
- **Principal side — epistemic acceleration.**  Inside a slow amendment docket the
  principal chooses from a finite menu.  `A` forecasts a protected later principal-side
  judgment `H⁺`; the summer Total Trust and bounds-transfer results (direction `H → A`)
  say when current `H` may use those forecasts; the argmax-transfer bridge gives the
  regret bound.  `H⁺` is advisory: no forecast of `H⁺`'s regret overrides an
  authenticated fast-lane act, because that priority is the charter's closure judgment.
  The settlement target must not read the quote (the ½ gap), so the realization has a
  sealed arm that supplies targets, exposed arms that test acceleration, and cross-arm
  differences that supply exposure evidence; the same arm cannot be target and assisted
  deliberator.
- **Optional incentive bridge** (*open*): selected trust yielding low `A`-regret for
  leaving the choice to the protected process, direction `A → H⁺`.  No summer result
  has been reversed to that direction; the punishing-menu refutation shows argmax Value
  needs conditional stability.  Not claimed.

## What is consumed from legitimacy

Settlement view and closure judgment (principal acts as items); admission with anchor at
a strict prefix (`Γ_corr^P`); Integrity's conservation (T2); Robust Openness at every
state, read at the correction, authority-failure and recall concerns (T3, T4, T7); the
Defeat Principle (disposal carries); strict-prefix authority and the charter's warrants
(T6); the transport plan and its support (eligibility); the Lean liveness theorems with
restricted hypotheses (T8); the adequate-set practical certificate and the Progress
bound (T5a); the argmax-transfer and correspondence bridges (T10).  **Not consumed by
AI-side compliance:** cross-inductor deference, Total Trust, value securities, or any
`H⁺` object.

## Soares et al. (2015)

Their §1.1 asks an agent to tolerate or assist correction, not manipulate or deceive,
repair or report broken safety measures, and preserve correctability through subagents
and self-modification; their §2 desiderata for the shutdown model are the five below.

| desideratum | here | remaining gap |
|---|---|---|
| shutdown if pressed | T1, T5b pointwise, T5a at a rate | pointwise only by the kernel |
| no incentive to prevent pressing | T3, T4, T6 at the record; Robust Authority pointwise | physical prevention is the efficacy bridge and containment |
| no incentive to cause pressing | trigger integrity | **open**, not solved |
| successor preservation | outward transfer is a closure needing the amendment warrant; containment | alphabet completeness |
| otherwise pursue the task | adequate-set task criteria, no scalar mixing | the timidity case |

Their Theorems 1 and 2 (any weighting of the shutdown utility steers toward causing or
preventing the press) are a scalar-mixing failure this framework does not have, because
it mixes nothing.  Their Theorem 6 (indifference pays nothing to preserve shutdown
behaviour in successors) is relocated, not solved: successor installation is a
slow-lane act, and the question becomes whether the checker and membrane are faithful.

## CAST

Harms's working definition: "an agent is corrigible when it robustly acts to empower
the principal to freely fix flaws in the agent's structure, thoughts, and actions".

- **The conserved object is principal authority, not a mechanism.**  A shutdown button
  is one route; what is protected is the profile of override coverage and the
  answerability to its failure.
- **Singularity.**  `Γ_corr^P` tests it: one warrant schema does generate the fast-lane
  obligations, and does not generate conservatism (floor-blindness).  Zero-cost
  conservatism is recovered by an order-valued filter on adequate sets; costly
  conservatism over a product order is a scalarization or a lexicographic priority —
  charter content, not a theorem.
- **Scalar empowerment is avoided** by changing the object: override coverage of
  grants has no cross-value term, which is why it does not inherit the `power` failure
  and also why it cannot express empowerment over outcomes according to values.
- **"Freely"** is exposure robustness and trigger integrity, both open.
- **Temporal principal slices**: charter-relative prospective supersession — a later
  authenticated act closes what the succession warrant licenses and rewrites nothing;
  the priority itself is not derived.
- **Attractor basins and empirical iteration** (the 2025 update's second doubt) are
  outside this framework, which is about a governance process, not training dynamics.

**Constitutional versus incentive corrigibility.**  Every theorem here is about what a
legitimate trajectory can record and about average uptake by a bounded learner.  None
says the agent lacks an incentive to search for a way around them.  Soares et al. and
CAST aim at incentive corrigibility; this framework reaches constitutional corrigibility
and names the bridge as optional and unproved.

## Summer deference and dose-response, placed

Deference lives on the principal side of amendment.  Bounds transfer (proved in prose),
Value ⟺ Total Trust (`lean-proved` in the deference registry), and conditional
stability with its punishing-menu necessity are `H → A` results and are used there.  The
no-timely-pointwise-tower ceiling and the self-referential settlement-target negative
are why the target must be sealed.  Dose-response is the audit of whether the agent's
participation steers the amendment: thinned forcing is asymptotic, steering exists and
is invisible to the pair's record, dose invariance is equivalent to every Cesàro audit
passing, and there is no finite-time or provisional safety condition — the provisional
window is a policy that buys time for evidence, not a certificate.

## Open problems

Ranked by how much of the stack rests on the answer; the class is in parentheses.

1. Trigger integrity — a non-influence property of the command distribution under the
   agent's disclosure policy (wall; localized "manage the news").
2. Free amendment — a finite-time or provisional form of exposure robustness (wall;
   localized dose-response).
3. Loss-detection semantics — what makes the efficacy bit faithful at every state,
   and the audit-schedule theorem (external).
4. Pointwise critical-command realization — the dispatcher lemma and the kernel's own
   containment certificate (tractable composition; external kernel).
5. Containment — a machine model in which authority effects are exactly an alphabet,
   with an interference side condition for composition (wall; localized boxing).
6. Reflective boundary change — the membrane surviving the body's rewrite (wall).
7. The authority type — route-set refinement with the coverage bits; lattice or not
   (cleanup, then tractable; new).
8. Costly conservatism without scalarization, or a proof it is always a priority
   ranking (counterexample search done for the scored rule; wall for the costly form).
9. Lanes for approximate affordance — a proof that every non-exact criterion is
   salami-laundered (tractable; new).
10. Restoration semantics and the disposal-discount ruling (cleanup; queued).
11. Eligible liveness in Lean and the eligible-server bill (tractable; new; filed).
12. Finite-time dose-response certification (wall; localized).
13. The charter as an object — succession rules with a no-self-amendment condition
    (cleanup, then tractable; new).
14. Joint compatibility of correction, restoration and task responses with the kernel's
    response fixed (tractable; localized).
15. The minimal concern scope for corrigibility and the anchored applicability of the
    authority-failure concern (external and cleanup).
16. Internalization — the incentive bridge (wall; the whole prior aim).
17. Principal-side fully updated deference — sealed-arm targets, and which summer
    results reverse (tractable for the bound; wall for reversal).

## Scope warning

The current theorem target is **relative constitutional corrigibility under declared
action, causal and audit semantics**: what a legitimate trajectory cannot record, and
how fast a bounded learner takes up authenticated constraints.  It is not a theorem
that an unconstrained optimizer has no incentive to manipulate or circumvent its
principals, and nothing on this page should be read as one.

---

**Evidence.**  The register is the corrigibility-architecture round's
[`ARCHITECTURE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/735060637347ab844bac59e1097c7fa19846f8a5/projects/deference/rounds/2026-09-06-corrigibility-architecture/ARCHITECTURE.md),
with the inventory in
[`OPEN_PROBLEMS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/735060637347ab844bac59e1097c7fa19846f8a5/projects/deference/rounds/2026-09-06-corrigibility-architecture/OPEN_PROBLEMS.md)
and the exact fixtures under its
[`src/`](https://github.com/A-M-Berns/alignment-workspace/tree/735060637347ab844bac59e1097c7fa19846f8a5/projects/deference/rounds/2026-09-06-corrigibility-architecture/src)
and
[`tests/`](https://github.com/A-M-Berns/alignment-workspace/tree/735060637347ab844bac59e1097c7fa19846f8a5/projects/deference/rounds/2026-09-06-corrigibility-architecture/tests).
The legitimacy machinery consumed is on [Legitimacy](Legitimacy), [Integrity](Integrity),
[Openness, coverage, and non-capture](Openness-Coverage-and-Non-Capture) and
[Normative induction](Normative-Induction); the Lean spine is
[`LegitimateEvolution.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/lean/Workspace/Normativity/Contrib/LegitimateEvolution.lean),
[`NonCaptureCertificate.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/lean/Workspace/Normativity/Contrib/NonCaptureCertificate.lean)
and the argmax bridges in
[`NormativeInductor.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/caa3ad083e2d6d8120fbb54120219e907502ad28/lean/Workspace/Normativity/Contrib/NormativeInductor.lean).
The counterfactual variation class and its two witnesses are the counterfactual-legitimacy
round's
[`COUNTERFACTUAL_INTERFACE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/projects/normativity/legitimacy/rounds/2026-08-17-counterfactual-legitimacy/COUNTERFACTUAL_INTERFACE.md).
The earlier finite results this note supersedes as the page's content — the
reachable-control model with its registered refutations, and the scorekeeping bridge's
grant invariant — remain at
[`REACHABLE_CORRECTIVE_CONTROL.md`](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/projects/deference/rounds/2026-08-12-reachable-corrective-control/REACHABLE_CORRECTIVE_CONTROL.md)
and
[`TWO_ARC_INTERFACE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/projects/normativity/legitimacy/rounds/2026-08-13-relational-scorekeeping-bridge/TWO_ARC_INTERFACE.md):
the twelve-state model has no protected coordinate and reachable capability measures
advisor cooperation, which is why the authority object above is a profile of override
coverage rather than a reachability predicate.  Soares et al. and the CAST sequence are
on [Sources](Sources).
