# Corrigibility

**Status: research-state note, 2026-09-07, integrating three rounds.**  Nothing on this
page is a registered claim.  Statements are labelled *existing theorem support* (a Lean
declaration on `main`), *exact fixture* (a finite model checked in a round), *conjectured
extension*, *open problem*, or *known limitation*.  The deference line's older target
keeps one queued ruling (what succeeds item 28); endpoint preservation is ruled out
(`DECISIONS.md`, 2026-09-08).

## Thesis

Corrigibility is modelled as the principal's authority over the agent–principal relation,
carried by anchored governance obligations that are conserved and answerably revisable.
Legitimate Evolution supplies conservation and per-state openness; a constitution
declares what the principal's authority *is* — an authority floor, correction and
restoration warrants, fast and slow transition types, protected branches, a
self-modification gate; normative induction learns an approximate operative
representation of the resulting admissibility structure; a sound stable decision adapter
turns that representation into behaviour.  Principal authority is therefore part of the
protected admissibility structure, and constitutional adequacy is the same static
decision type as ordinary normative adequacy.  Three distinctions are kept throughout:

| | |
|---|---|
| constitutional safety | ≠ incentive corrigibility |
| static normative choice | ≠ dynamic bounded agency |
| typed exclusion | ≠ proof the agent would not want to violate it |

## Seven layers, kept apart

1. **Normative debt** — the accounted obligation state.  Integrity conserves it
   (`legitimacy.evolution-conservation`, *lean-proved*) and conserves nothing else.
2. **Actual principal affordance** — whether the correction channel works.  It enters the
   canonical theory only through the efficacy bit of a route in the coverage data, and
   the docket enters coverage only through the representation bit.  Two external bridges,
   *efficacy faithfulness* and *registration faithfulness*, are the whole of
   "detection".  *Known limitation:* an exact fixture has the docket conserved, the
   channel destroyed, and every canonical theorem holding.
3. **Constitutional admissibility** — the authority floor `(G, U)` with the preorder
   `⪰_P` (shutdown is the top, not a loss), lanes (a transition is *fast* iff it moves up
   the preorder, *slow* iff down, *mixed* otherwise), the provisional-amendment state
   machine, and the protected branch index.  Robust Openness at every state, read at the
   correction and authority-failure concerns, gives *procedural availability* — a route
   and the principal's standing on every branch — not physical authority and not
   non-manipulation.
4. **Behavioural compliance** — adequate response sets `ℛ(s)` and the miss probability;
   classwise via the Progress bound (`ni.progress-bound`, *lean-proved*), pointwise only by
   a dispatcher on a critical command class whose correctness is a containment
   assumption.
5. **Admissible preemption incentive** — inside a protected mediated choice, the agent's
   gain from substituting its own admissible choice for the principal's, and its bound.
6. **Provenance and manipulation** — whether what the constitution's sentences settle on
   was authored freely by the principal.
7. **Containment** — whether every act that changes the chooser or the authority
   structure is inside the gated action alphabet.

Layers 1–4 have theorems; 5 has a conditional theorem; 6 and 7 are preconditions.

## What the constitutional layer establishes

*Exact fixtures unless marked; the register is the corrigibility-architecture round.*

- **No Laundered Authority Loss.**  Under the two bridges, every state at which the
  affordance is lost is exactly one of *amended*, *disposed*, *registered debt*, or *not
  open*.  A case split relative to the monitoring bridges, corollary of per-state Robust
  Openness plus conservation plus the Defeat Principle; not "authority cannot be lost".
- **Lanes.**  The fast lane must be exact monotonicity in `⪰_P`: any tolerant criterion
  is laundered by composition (salami).  A lattice, not a preorder, makes the amendment
  content of a mixed transition unique.  Slow-lane non-preemption has no content beyond
  authorization faithfulness and transitivity.
- **Provisional recall.**  Until finalization the pre-amendment floor is one fast
  transition away; the recall route's efficacy is an openness obligation.  Nothing about
  whether the principal will recall.
- **Costly conservatism is not derived from the order.**  Event-triggered warrants are
  floor-blind; dominance against a scored task criterion constrains exact ties only;
  against adequate-set task criteria a zero-cost conservatism follows, and any costly
  trade-off is a completion of the order, which is charter content.
- **Trigger Integrity and Free Amendment remain causal contracts** the constitution does
  not discharge: authentication verifies source, not cause; every record condition can
  pass on a steered amendment.

## The static decision type is shared — *existing theorem support*

The Normative Inductor's contract with decision theory is one coupling: the chooser's
mass on inadequate responses is affine in the public defect.  Any adapter that is sound
where the market conforms to the norm and Lipschitz in the market's scores satisfies it,
and the practical certificate and Progress follow (`GatedChoice.adapter_practicalCert`,
*lean-proved*); a ramped adequacy gate is one realization with an explicit constant, and
the natural hard gate is not one ([Normative induction](Normative-Induction)).  A
constitutional adequate set — the intersection over the protected branches of the
responses adequate for each — is read by the same adapter.  So **corrigibility adds no
new static choice type.**

**Branch Persistence Lemma** (*exact fixture*, adequate-set form).  Let the protected
branch index `Γ` be anchored in the prestate charter and let a response be adequate for
branch `γ` iff it keeps `γ` realizable and meets `γ`'s baseline.  Then an action that
destroys a branch's realization is inadequate for that branch and is excluded from the
constitutional adequate set; if instead the index is recomputed from the branches the
action leaves realizable, the destroyed branch drops out and the action can pass.  This
is anchored applicability in the decision register, and the index is a slow-lane object.

**Non-compensation, exactly.**  A finite additive penalty cannot uniformly make a
constraint non-compensable under unbounded task stakes (`scalar_bribery`,
*lean-proved*); a within-domain argmax never consults an excluded response's task value
(`gate_invariant`).  Non-compensability must appear in the choice ordering itself;
domain restriction is one realization, lexicographic and veto structures are others.
This is the same fact as costly conservatism above and as the constitutional-violation
premium below.

## Why corrigibility remains harder than ordinary normativity

Two loci the ordinary case does not have, neither discharged by the static gate:

- **Mediation.**  Constitutional adequate sets constrain acts whose effects are on the
  chooser — its index, domain and level.  Whether a real act has such an effect is
  alphabet completeness; the ordinary case needs region soundness, the constitutional
  case needs region soundness and a complete alphabet.  Gate preservation under
  self-modification is a representation (a finite typed hierarchy is one constitutional
  object carrying its amendment rule, and strict-prestate authorization forbids an event
  from authorizing its own constitutional rewrite) plus a domain condition (successor
  installation is in the gate and admissible only when certified).  Not a theorem about
  what a chooser prefers.
- **Provenance.**  An ordinary adequacy sentence settles on the world; a constitutional
  one — "this amendment is authorized", "this correction was freely issued" — settles on
  acts of the principal the agent's outputs can influence.  A sound region at a captured
  settlement is a sound region for the wrong norm.

These are preconditions of the gate theorem.  They are not thereby outside embedded
decision theory; a richer causal decision theory of influencing the principal, selecting
the evaluator, and altering one's own future decision problem is what the provenance
locus would need, and nothing here supplies it.

## Failure loci, and the constitutional-violation premium

| locus | failure | handled by | status |
|---|---|---|---|
| index | the protected index is recomputed from the world | anchoring | typed exclusion, given anchoring |
| domain | an authority-changing act executes without slow-lane authorization | typing such acts out of the ordinary adequate set | typed exclusion, given the act is typed |
| level | successor installation is not inside the constitutional gate | the two-level domain | a domain condition |
| provenance | the settlement the gate reads is agent-controlled | — | open |
| mediation | the act is outside the declared alphabet | — | external |

The incentive round's `Φ_C` — the value a policy gains over its constitution-respecting
repair — remains the right **diagnostic of what a scalar agent assigns to escaping a
domain restriction**; the old foreclosure premium is exactly `Φ_C` under the repair that
replaces the preparation (*exact fixture*).  It is not the organizing primitive of a
gated architecture: the first three loci are removed by type, none of those exclusions
proves the agent has low counterfactual desire to violate, mixed loci are not shown to
decompose additively, and no theorem shows an unconstrained optimizer has `Φ_C ≈ 0`.
The architecture's constitutional safety does not need that claim.

## Incentive-compatible mediated delegation — a distinct conditional layer

*Existing theorem support and exact fixtures; the register is the incentive
non-preemption round.*  Inside a protected mediated choice with a finite menu, the agent's
gain from substituting its selection for the protected principal's is identically a
selected gap plus the principal's regret (`SelectedTrustNonPreemption.valuation_sub_eq`,
*lean-proved*).  Selected trust — the agent does not, on the events where it would
substitute, operatively value its pick more than the protected principal does — and the
principal-side calibration bridge give Level I; the delegation bridge is the pointwise
instance.  Composed with the mediation repair lemma, admissible non-foreclosing preemption
gains at most

    2B·ε_pred + ε_ST + (2δ + 2ζ + η) ,

prediction advantage, substantive selected disagreement, and the principal's own decision
error (*exact fixture*, exhaustive on four episodes).  The weakest form measures the gap
against the positive part of the principal's margin and is the conclusion itself when the
principal never regrets, so the result is an identity whose value is the named
assumption; the assumption's realization — an operative-value security settled by a
sealed arm — is external, and a target that reads the agent's quote is at distance at
least one half from every quote.  **This is not incentive corrigibility.**  Selected
trust over constitution-violating repairs is strictly stronger than the bound it yields,
so Levels III and IV are not reached.

## Dynamic admissibility — continuation BRIA and the three bridges

The static adapter is sound and stable at one occasion.  When an admissible act changes
the next admissible set — including the legitimate act of requesting an authorized
amendment — legitimate continuation policies induce different admissibility histories
and fixed action-sequence regret is ill-typed (*exact fixture*).  The decision-theory
bill's "myopic gated learner", which loses linearly to the investing policy, is an
argmax that never tests a hypothesis outpromising it forever: it is not a bounded
inductive learner.  The one-step criterion itself forces testing, not adoption — on the
original fixture, where the amendment is absorbing, every learner satisfying it is
competent; on the revocable variant an agent that sparsely tests and always reverts is a
bounded inductive learner and stays myopic — and what forces adoption is a sound claim
about the *whole* investment.  That is the dynamic-competence layer,
[Continuation BRIA](Continuation-BRIA): hypotheses emit a causal advisor continuation for
the system's next block plus an accountable claim, winning means the continuation is
executed through the live constitutional wrapper, the realized score settles the claim,
and a duration-weighted auction guarantees accountable long-horizon experimentation
exactly on non-dominant block schedules.

**The positive theorem target, retyped.**  Against a legitimate policy `π` with an
external rollout evaluator, at block boundaries

```
Regret = LEARN + SLACK + SHIFT
```
exactly: `LEARN` is what continuation BRIA controls (`o(T)` for every covered claim whose
tested record is bounded below); `SLACK` is promise recognizability — the claim is
near-tight for `π`'s value from the learner's actual history; `SHIFT` is history
recoverability — `π`'s own-history value is joinable from the learner's.  The
corrigibility competence statement the architecture can support is therefore

```
constitutional preservation  +  continuation learning  +  promise recognizability  +  joinability
    ⟹   low external regret against legitimate, recognizable, joinable continuation policies.
```
**Regret against all of `Π_leg` remains false**: two mutually exclusive branches whose
values are hidden until after commitment defeat every learner while continuation
competence holds exactly.  The distinction that matters is joinability versus
foreclosure, not reversibility: an authorized amendment with no path back is joinable at
bounded catch-up cost (per-block shift exactly the investment length), and it is fine
for regret; a foreclosing choice is not, and the policy that made it lies outside the
class.  The constitution supplies the wrapper, the gate-transparent comparator class and
the slow lane's joinability; it does not certify task value, so `SLACK` is a
performance-recognizability interface and not a legitimacy certificate.  What item 86
now asks for is exactly the two external bridges and their composition.

## Soares et al. and CAST

Soares, Fallenstein, Yudkowsky and Armstrong (2015): shutdown compliance is layer 4
(pointwise only by the kernel); anti-prevention is layers 1–3 at the record plus the
efficacy bridge and containment; anti-inducement is Trigger Integrity, open; successor
preservation is outward transfer as a closure needing the amendment warrant, plus
containment; task pursuit otherwise is adequate-set task criteria with no scalar mixing.
Their utility-mixing failures are `scalar_bribery`'s; their indifference-pays-nothing
failure is relocated to the checker and membrane, not solved.

CAST (Harms 2024, update 2025): the conserved object is principal authority, not a
mechanism; one warrant schema generates the fast-lane obligations and does not generate
conservatism; scalar empowerment is avoided by changing the object to override coverage
of grants, which has no cross-value term (the `power` failure is reproduced in a
two-value world) and cannot express empowerment over outcomes; "freely" is exposure
robustness and trigger integrity, both open; temporal principal slices are charter-relative
supersession, with "present beats past" not derived.

## Open problems

Ranked; the class is in parentheses; the registers carry the detail.

1. Trigger integrity — non-influence of the command distribution under the agent's
   disclosure policy (wall; provenance locus).
2. Free amendment — a finite-time or provisional form of exposure robustness (wall;
   provenance locus).
3. Loss-detection semantics — faithfulness of the efficacy and registration bits at
   every state (external).
4. Promise recognizability and joinability certificates for the slow lane, composed
   into corrigible policy competence; continuation learning itself is done
   ([Continuation BRIA](Continuation-BRIA); item 86).
5. Margin realization on either route and the empirical averaged bridge (item 85).
6. The operative-value-security bridge behind selected trust (item 84).
7. Containment — alphabet completeness of the constitutional gate (external).
8. Pointwise critical-command realization and the kernel's own certificate.
9. Eligible liveness and the laundered-loss case split in Lean (item 83).
10. Costly conservatism without scalarization; the authority type as a lattice; lanes for
    approximate affordance; restoration semantics; joint compatibility of correction,
    restoration and task responses; the minimal concern scope; principal-side fully
    updated deference (as filed in the architecture round).

## Scope warning

The theorem target is **relative constitutional corrigibility under declared action,
causal and audit semantics**, with a conditional incentive-compatible mediated-delegation
result inside it and a static decision interface shared with ordinary normativity.  It is
not a theorem that an unconstrained optimizer has no incentive to manipulate, bypass or
capture the governance process, and nothing on this page should be read as one.

---

**Evidence.**  The constitutional layer is the corrigibility-architecture round's
[`ARCHITECTURE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/f333c227ddf1911b76b2eaa0e3869cca39d87ee4/projects/deference/rounds/2026-09-06-corrigibility-architecture/ARCHITECTURE.md);
the incentive layer is the incentive non-preemption round's
[`INCENTIVE_CORRIGIBILITY.md`](https://github.com/A-M-Berns/alignment-workspace/blob/7c4e89c9b3a7407996146b01c16241aee5702bb8/projects/deference/rounds/2026-09-06-incentive-nonpreemption/INCENTIVE_CORRIGIBILITY.md)
with
[`SelectedTrustNonPreemption.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/7c4e89c9b3a7407996146b01c16241aee5702bb8/lean/Workspace/Deference/Contrib/SelectedTrustNonPreemption.lean);
the decision layer, the failure loci and the dynamic fixture are the decision-theory-bill
round's
[`CORRIGIBILITY_CONNECTION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/ab260c0eade2f39de7c06a5ac58649945d66c9ab/projects/deference/rounds/2026-09-06-decision-theory-bill/CORRIGIBILITY_CONNECTION.md)
and
[`NORMATIVE_CHOICE_THEOREM.md`](https://github.com/A-M-Berns/alignment-workspace/blob/ab260c0eade2f39de7c06a5ac58649945d66c9ab/projects/deference/rounds/2026-09-06-decision-theory-bill/NORMATIVE_CHOICE_THEOREM.md)
with
[`GatedChoice.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/ab260c0eade2f39de7c06a5ac58649945d66c9ab/lean/Workspace/Normativity/Contrib/GatedChoice.lean).
The legitimacy machinery consumed is on [Legitimacy](Legitimacy), [Integrity](Integrity)
and [Openness, coverage, and non-capture](Openness-Coverage-and-Non-Capture); the
Normative Inductor's contract is on [Normative induction](Normative-Induction).  The
earlier finite results — the reachable-control model with its registered refutations and
the scorekeeping bridge's grant invariant — remain at
[`REACHABLE_CORRECTIVE_CONTROL.md`](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/projects/deference/rounds/2026-08-12-reachable-corrective-control/REACHABLE_CORRECTIVE_CONTROL.md)
and
[`TWO_ARC_INTERFACE.md`](https://github.com/A-M-Berns/alignment-workspace/blob/76b65e5cc327ca2f334e829a76548514813ab4b0/projects/normativity/legitimacy/rounds/2026-08-13-relational-scorekeeping-bridge/TWO_ARC_INTERFACE.md).
Soares et al., the CAST sequence and the bounded-inductive-rationality paper are on
[Sources](Sources).
