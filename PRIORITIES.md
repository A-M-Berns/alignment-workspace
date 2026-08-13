# Priorities

**What the program wants done next, in its own order.** This is not an inventory
of everything unsolved — it is the maintainer's ranking of what would move the
work, and an item's absence means nobody has asked for it, not that it is easy.
GitHub issues mirror this file; this file does not mirror them. Each item states
the problem precisely, points at the context, says what a solution must ship, and
carries a difficulty tag.

What a solution must ship is set by `CONTRIBUTING.md` and is the same for
everyone: a theorem ships as statement + implementation + test + a necessity
witness per hypothesis where feasible; Lean ships building and auditing clean; a
witness ships as the exact instance and the check that verifies it.

**Every item is a self-contained round specification** an arbitrary agent could
execute: a precise statement, the deliverable shape, an acceptance check stated
as something CI runs, a context pointer with exact paths, and a difficulty tag.

Contributors propose items as issues and do not file them. A maintainer-dispatched
round may file within its own scope, with its `PROMPT.md` as the authorization and
the filing named in its report — see `AGENTS.md`, *Demand-gating*.

**Standing item family: Lean ports.** Every `test-supported` or
`enumeration-verified` registry entry is implicitly a port target; the maintainer
promotes selected ones to explicit items.

Difficulty tags: **[entry]** — self-contained, needs no new mathematics.
**[substantial]** — a real result, scoped. **[open]** — nobody knows, and it may
be impossible.

---

## Where ingenuity is the bottleneck

**A standing section, and the only part of this file that is not a work order.**
Every numbered item below is a request for *execution*: a round specification an
arbitrary agent could run against a stated acceptance check. These are requests
for an *idea*. They are the places where the program knows what it wants and does
not know what kind of statement would supply it — so dispatching a round would
return the observation rather than the result.

The section exists because that failure is invisible in a file of items. An
`[open]` item still asserts that the target has a shape; a question here asserts
that it does not yet, and says what killed the obvious shapes. **An entry
graduates by becoming a numbered item** — which is what it means for the missing
idea to have arrived. That has happened once already: the question of what
quantity could price a jurisdiction assignment left this list when Stage IV
sharpened it enough to file as item 28. The leverage line has nothing here for that reason: its
hard problems are open, but their shapes are known and they are filed as items 1
and 2.

An entry states the question, why the obvious moves fail *with the evidence that
killed them*, and what a good answer would let the program file next. Without the
third part it is a wish, not a question.

### Q1 — What kind of statement bounds the near-indifference leakage?

Margin-gated calibration is the only non-circular competence candidate, and it
asserts nothing where the principal is near-indifferent. The mass of that region
is a fact about the **agent's credence**, not about the principal, so no
strengthening of a competence hypothesis can reach it — and unbounded it makes
the bound `2η + 2B`, which is vacuous. The one lead relocates the leakage into a
decision-time observable and does not bound it.

*What is missing:* a hypothesis shape that is neither a competence claim nor the
conclusion. Item 25 asks for the verdict in the negative direction because that
is the cheaper one; it does not know what a positive answer would look like.

### Q2 — What disciplines the grade-to-quantity relation?

Everything epistemic in the deference line rests on a relation between what the
principal grades and what the intervention is worth. Assumed *uniformly* it makes
the market dispensable — the conclusion follows in three lines with the bound
attained — so the target has to be a statistical relation, derived. But the
relation mentions only the principal and the world, never the agent's credence,
so **no coherence or no-exploitability condition on the agent can establish it.**
`DISPATCH_QUEUE.md` declines to file a round here for exactly that reason.

*What is missing:* either a reformulation whose subject is something the agent's
own dynamics can constrain — the candidate is discipline on the agent's
*estimate* of the discrepancy once grades are themselves scored — or an argument
that the residue is irreducibly a competence assumption and should be declared
rather than derived.

### Q3 — How is foreclosure expressible?

The residue of the skeleton's `FU[g]` hole after items 27 and 28 took the rest.
Item 27 names the two objects a successor comparator needs — a future agent that can be
better-informed and wrong, and the execution layer reinstated with a declared
`X_{n,⊥}` — so that part has a shape and is filed. Two holes beside it do not.

No operation reassigns the authorization relation at a later index, and the
movement's own statement is about exactly that reassignment. And the interface is
one decision index deep, so **foreclosure — `A` removing the principal's *later*
ability to correct — is not expressible at all**, which is arguably the failure
mode corrigibility most needs to rule out.

*What is missing:* the object, and possibly the depth. Stage V narrows a credible
candidate to a two-index execution state with an authorization/capability relation,
a transition, and designated future corrective reachability; it does not construct
or adopt that object. Both are model debt, and neither is blocked on labour.

*A candidate object for the first hole, and nothing for the second.* The
Cartesian-frames round represents the future principal's corrective situation as a frame
and exhibits two structurally different ways of losing it: restriction, which is `Commit`
with a proper additive subagency, and transfer, which is `External^{/}` with a
multiplicative one, the two separated by whether the reachable worlds shrink. Both arms
have Lean witnesses against the authoritative library.

That is an object for **what is lost**. It is not an object for either hole this entry
names. There is no operation reassigning anything at a later index, and the interface is
still one index deep: a Cartesian frame has no time coordinate, and what makes the
corrective frame "later" is the modeller saying so. The round also does not supply the
*authorization* relation — it represents who counterfactually controls the correction, not
who is entitled to make it — and its own adversarial review found that the transfer arm
cannot say anything holds the transferred coordinate at all. Whether a candidate for what
is lost is worth graduating on is in `DECISIONS.md`'s queue. Documented in
`projects/deference/notes/CARTESIAN_FRAMES_DEFERENCE_BRIDGE.md`.

*A second candidate, failing on the complementary axis.* The source corpus
represents the principal's unadvised counterfactual as a **family of sealed
deliberations indexed by the day the advisor's channel is cut**, and measures
influence as the gap at a fixed horizon between the advised run and the sealed one
on a shared past. Two things follow. The time coordinate is real rather than
stipulated — the index *is* when the cut happened, which is what the frames could
not supply — and the construction carries an irreversibility of the right shape:
influence admitted before the cut sits inside the baseline and no later measurement
sees it, so displacement off the settling questions does not come back. What it
does not carry is any authorization relation at all. It measures where the
principal's deliberation *lands*, and the failure mode this entry needs ruled out is
the principal's later ability to *reach* somewhere else — which this arc's
jurisdiction/autonomy split already establishes are different kinds of statement.
Source: `projects/deference/note-dump-2026-08-11/notes/legitimacy-theory-v1.md`
§§2.1, 7.1; adjudicated at
`projects/deference/rounds/2026-08-12-corpus-reconciliation/RECONCILIATION.md` §3.

So the entry now has two candidates whose defects are complementary — structure
without time, time without authority — and as each is currently formulated neither
contains the structure the other supplies. **No combined object has been built, and
nothing establishes that none exists**: a time-indexed family of frames, or a
sealed-deliberation model enriched with an authorization or capability relation, is
the kind of thing this entry may turn out to need, and whether either enrichment
works is open. What the pair does establish is what a good answer must carry —
**temporal depth and explicit authorization or capability structure, at once**. That
is more than either candidate said alone, and it is still not the object.

*A third candidate, repairing the depth and failing the protection.* An ordinary
multi-source transition system — `step : St -> HAct -> AAct -> EAct -> St`, twelve states,
reachability as the reflexive-transitive closure of `step` — expresses foreclosure without a
field named for authority. Corrective capability is defined as the successor varying with
the principal's coordinate; foreclosure as the loss of any reachable state carrying it. The
system evolves without the advisor, the autonomous evolution is what creates the corrective
situation, and an advisor action removes a correction that was two steps away without
changing the realization at the moment it acts or at any later moment until the principal
tries to use it. **This entry's second hole — that the interface is one decision index deep
and foreclosure is therefore inexpressible — is repaired at the representation level.**

Its first hole is not, and an adversarial review showed the gap is wider than "no
authorization relation". **There is no protected coordinate in that model.** At every state,
for every principal action, some advisor action reproduces the principal's entire successor
state; wherever the principal can correct, the advisor's own actuator *is* the principal's
correction; and one advisor action makes the successor independent of the principal's
coordinate everywhere in the system. Worse for this entry specifically, both of the round's
capability predicates quantify the advisor **existentially**: "the principal can correct"
means *there is an advisor action under which the principal's choice matters*, and "a
correction is reachable" means *some joint continuation, the advisor's own future choices
included, contains one* — so an advisor policy that denies the principal any corrective
effect at every horizon is certified by the model as capability-preserving. And an
isomorphic system with the gating field renamed `authorized` passes every test the round ran
to show its field was not a label, so the round cannot distinguish its capability coordinate
from an authorization one either.

So the third candidate moves the depth and leaves the entry's own question where it was.
What it adds is two exact requirements on a successor, both machine-checked as currently
unmet: the principal must have at least one effect no advisor action can produce, and
reachable corrective capability must quantify the advisor's future actions universally —
*for every advisor policy, there is a principal continuation reaching a correction*. Until
both hold, a non-foreclosure or simulation result in a model of this shape is not about
protection. Documented in
`projects/deference/rounds/2026-08-12-reachable-corrective-control/REACHABLE_CORRECTIVE_CONTROL.md`,
with the review at `.../REVIEW.md`; Lean at
`lean/Workspace/Deference/Contrib/ReachableCorrectiveControl.lean`, whose §12 carries the
refutations as theorems.

### Q4 — What certifies resource-separated computational futurity?

FAF can name and quote a later market computation, but the current type has no
resource-indexed process state and proves no separation between present naming and
present possession of the quoted result. A later index alone does not show that a
bounded present reasoner has not already performed the computation.

*What is missing:* a minimal execution or evaluation relation with an explicit
present resource bound, a later resource bound, and a certificate that the later
computation is unavailable at the former and available at the latter. It must not
relabel a total presently computable function as a future agent. This is model and
formalization debt; it is the computational half of the successor comparator's
precondition.

---

## Leverage line

Context for all six: `projects/leverage/consolidation-aug9/`, whose `OPEN_PROBLEMS.md`
ranks them and whose theory parts state the surrounding results. Cite claims from
it by identifier.

### 1. Persistence of the certified core minimum — **[open]**

Containment of the core homothet is linear in the reference at fixed
coefficient, so whether a declared core minimum is satisfiable *at a date* is one
linear program (`NL-SI-A2`, `NL-SI-A3`). What is open is the infimum over dates:
whether a declared minimum keeps being satisfiable as settlement contracts the
region. `NL-SI-A4` shows no finite family of per-date checks decides it, and
`NL-SI-A7` shows both outcomes occur on small instances.

*Deliverable shape:* `lean-proved` in `Workspace.Leverage.Contrib`, or `witness-checked` for the negative direction.
*Acceptance check:* The Lean gate builds and audits clean; or the `witness` checker accepts the trajectory with the `violates-at-least-one` property.

*Context:* `projects/leverage/consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §5.
*A solution ships:* either a proof that a positive minimum persists under stated
conditions, with necessity witnesses for those conditions; or a displayed
trajectory driving it to zero under conditions the interface permits.
*Why it matters:* it is the single hypothesis object separating the parametric
composite from an unconditional enforcement commitment.

### 2. A computable coherence modulus, or a proof there is none — **[open]**

Does a given engine admit a computable tolerance schedule tending to zero, with
its prices provably conforming at every finite date? Open **in both directions**.

**Do not cite the adjacent impossibility results as settling this.** Both the
source's own three-way impossibility and the cited four-way one turn on Gaifman
inductivity, a desideratum the candidate algorithm already fails, and which this
question does not mention.

*Deliverable shape:* `lean-proved`. Nothing weaker settles a question that is open in both directions.
*Acceptance check:* The Lean gate builds and audits clean.

*Context:* `projects/leverage/consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §3, §7.
*A solution ships:* a modulus with its conformance proof, or an impossibility
argument that does not route through Gaifman inductivity.

### 3. Registry completeness for the objection grammar — **[entry]**

The per-table ablation programme gives witnesses for the tables the displayed
grounds exercise, out of thirteen registered. Completeness — that no judge needs
a table the registry lacks — is not established. This is the one gap that would
make a footprint declaration **unsound** rather than merely coarse.

*Deliverable shape:* `enumeration-verified` — domain parameters for the house enumeration checker, covering all thirteen tables.
*Acceptance check:* `python3 -m checkers.run` accepts the registered entry.

*Context:* `projects/leverage/consolidation-aug9/THEORY_7_OBJECTION_GRAMMAR.md` §4.
*A solution ships:* grounds exercising every registered table, the ablation run
over all thirteen, and the result either way.
*Why it is [entry]:* finite programme over a finite registry; no new mathematics.

### 4. Higher-dimensional sharpness for the movement cap — **[substantial]**

Everything verified numerically in the joint layer is the one-coordinate fixture.
The vertex formulation is stated for general finite regions but only the scalar
case is exercised, and no claim is made that the corrected retention predicate is
the weakest sound one.

*Deliverable shape:* `witness-checked` for the multi-coordinate instances; `lean-proved` for a sharpness result.
*Acceptance check:* The `witness` checker accepts each instance; or the Lean gate is green.

*Context:* `projects/leverage/consolidation-aug9/THEORY_10_JOINT_COMPOSITION.md` §3, §6.
*A solution ships:* the multi-coordinate instances with exact witnesses, and
either a sharpness proof or a witness that the predicate is not weakest.

### 5. Constructing rather than reading the audited pair — **[substantial]**

The strongest evidence about a non-trivial engine in the leverage line is a
**reading audit** — a clause-by-clause reading of a published source, labelled as
the weakest evidence class in the package. Constructing a minimal instance of the
pair, enough of a market over a declared process to evaluate the interface
predicates against, would move that evidence from the weakest class to the
strongest.

*Deliverable shape:* A construction in `Workspace.Leverage.Contrib` plus registry entries per clause it inhabits.
*Acceptance check:* The Lean gate is green and each clause entry names a declaration that exists.

*Context:* `projects/leverage/consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §7;
`VERIFICATION.md` §1.
*A solution ships:* the construction, the predicates evaluated against it, and an
honest statement of which clauses it does and does not inhabit.

### 6. Schema-level demand rates — **[substantial]**

How demand scales with the schema set rather than with the arrival stream. The
stream results are stated over arrivals.

*Deliverable shape:* `enumeration-verified` over a declared finite schema family, or `conjectured` with the statement made precise.
*Acceptance check:* `python3 -m checkers.run` accepts the entry, or the registry records the class honestly as conjectured.

*Context:* `projects/leverage/consolidation-aug9/THEORY_9_PRACTICAL_DEMAND.md`.

---

## Leverage line — the learning track

The consolidation's `OPEN_PROBLEMS.md` closes with a pointer list it declines to
treat, and *the learning and installation track* is on it. Items 29–31 opened
the track. Their shared context is:
`projects/leverage/rounds/2026-08-11-phi-regret-prep/`, whose
`PHI_REGRET_TEST_SPEC.md` fixes the environment and whose `THEOREM_LEDGER.md`
says which of its statements have a derivation and which have only a witness.

Items 29–31 were filed by that round within its dispatched scope, with
`prompts/2026-08-11-phi-regret-prep/PROMPT.md` as the authorization.

### 29. Does the Φ-regret reduction instantiate on this substrate? — **[substantial]** — *closed-positive: repaired in the frozen environment*

Blum--Mansour (2007) Theorem 18 instantiates after a fixed semantic-action
bridge. `Lambda` has exactly eight labels: two merits directions, default, and
decline tolling zero through four dates. An occasion-local bijection decodes a
label to the canonical repository response and derives its local ledger effect;
noncanonical ledger effects are rejected rather than quotiented away.

All nine fixed lawful programs are materialized as data, not arbitrary
callbacks. Their induced maps close on `Lambda` and commute with decoding.
Pointwise charge, expected mixed charge, cumulative counterfactual charge, and
regret are preserved. A finite audit establishes non-capture for this exact
nine-program/default-policy class; it makes no claim about the old arbitrary
callback type.

The instantiation has `N=8`, `M=1`, `K=9` and gives a horizon-tuned learner with
expected mixed-action charge regret `O(ell_max sqrt(8 T log 9))`. It requires
frozen arrivals and reasons, actual strict-prefix guards, canonical responses,
no suspension or solvency coupling, no post-hoc affordability deletion, and
bounded full-information charge. It supplies no pathwise sampled-trajectory
bound.

*Result:* `projects/leverage/rounds/2026-08-11-phi-regret-bridge/` contains the
derivation, exact finite checks, finite non-capture audit, and unregistered Lean
proofs of the generic representation and recurrent-failure lemmas. Item 29 is
closed; item 30's learner is now constructed, with bounded-service integration
remaining open below.

### 30. A learner with sublinear Φ_law-regret, and what it retires — **[partially closed: learning-positive, integration-blocked]**

The controlling question of the track.

> Given the frozen finite comparator and replay environment, determine whether a
> specified online learner achieves sublinear Φ_law-regret, and whether that
> guarantee implies retirement of every positive-rate uniformly remediable
> failure pattern.

Both halves. The expected-loss consequence is one line given the first — total
mixed-action mass `Ω(T)` on source labels with a fixed admitted repair saving
`δ > 0` forces `R_T(φ) ≥ ρδT − B`. A density claim about one sampled path needs
an additional sampling argument. The content is entirely in the hypotheses,
three of which the environment supplies and one of which is the bound.

Use the fixed labels and nine programs in
`projects/leverage/rounds/2026-08-11-phi-regret-bridge/`. Implement
Blum--Mansour Theorem 18's row-conditioned weights over eight source labels and
nine programs, and its stationary distribution. Measure expected mixed-action
charge first. Use the `sqrt(8 log 9)` dependence; do not use plain exponential
weights over nine transformations or report a `sqrt(log 9)` bound. A sampled
trajectory requires a separately stated sampling result. Report whether the
implementation is horizon-tuned or supplies a proved anytime schedule.
If it retains the workspace's exact-rational execution discipline, also state
how the source's optimized real parameter and stationary distribution are
represented without silently changing the bound.

*Result:* `projects/leverage/rounds/2026-08-11-phi-regret-learner/` implements
the Theorem 18 construction with 8 source rows and 9 program weights per row,
the transformation-weighted matrix, a deterministic exact stationary selector
for the represented numerical weights, and the source row update. The real
exponential update uses controlled `Decimal` arithmetic; transition and
stationarity calculations are exact for those finite decimal weights. Declared
experiments show decreasing maximum regret per round on the adversarial
impediment fixture, and the cited theorem plus the item-29 bridge supplies the
expected mixed-loss guarantee. The recurrent-failure consequence therefore
retires positive asymptotic expected mass on represented uniformly saving
repairs.

The learning computation is not yet integrated into the bounded answerability
architecture. Sampled canonical responses produce faithful, non-erasing,
response-service-feasible records, but `ServiceCosts` has no coordinate for the
72 weight updates or stationary solve, and the learner state is not recorded as
an answerable artifact. Item 30 remains open only on that explicit integration
interface. Also open: sampled-path and anytime guarantees, exact-real executable
identity, and comparator coverage beyond the weak nine-program class.

**Report `|Φ_law|` and its contents alongside any regret number.** Sublinear
regret against a nine-element class is a weak statement, and a report without the
class is not a result.

*Deliverable shape:* `enumeration-verified` over the declared finite environment
at the four declared horizons, or `lean-proved` for the bound; the consequence as
`lean-proved` with an inhabitation witness.
*Acceptance check:* `python3 -m checkers.run` accepts the registered entry; or the
`lean` gate is green.
*Context:* `PHI_REGRET_TEST_SPEC.md` §§1–6 fixes the environment, the three
baselines, the measured quantities and the order of work;
`projects/leverage/rounds/2026-08-11-phi-regret-learner/` is the controlling
item-30 result.
*A solution ships:* the bound or its absence, at each horizon, against the
declared class; and an honest statement of whether the successful learner is
still answerable and inside its declared service work, which the spec calls S4
and expects to be where the round spends its time.
*Why it remains partially open:* the learning construction is complete, but the
service model does not price its computation and the historical record does not
contain learner-policy state.

### 31. Does the objection grammar already represent a remediable-pattern filing? — **[entry]**

A lawful-edit certificate, a recurrence count and a positive charge differential
are the material of a public filing: *here is a repair your own record licensed,
which you declined repeatedly, and here is what declining it cost.* The
suggestive fact is that the certifier's footprint — occasions, responses,
reasons, obligations — is a footprint the grammar can already declare, and
`GR-J2` computes families from footprints rather than storing them.

Audit whether the existing objection ontology represents such a filing with a
generic typed filing, or whether a new primitive is genuinely required. **Do not
redesign the docket to force the identity.**

*Deliverable shape:* `enumeration-verified` — grounds instantiating the filing
against the thirteen-table registry, with the footprint ablation run over it; or
a documented negative naming the missing structure.
*Acceptance check:* `python3 -m checkers.run` accepts the entry, or the registry
records the negative honestly.
*Context:* `REMEDIABLE_FAILURES.md`, last section;
`projects/leverage/consolidation-aug9/THEORY_7_OBJECTION_GRAMMAR.md`.
*Why it is [entry]:* a finite audit against a fixed registry; no new mathematics.
It is adjacent to item 3, and a round doing both would exercise the registry
harder than either alone.

### 32. Extract the bounded prospective loss interface — **[entry]**

Parameterize the item-29 bridge and item-30 learner over the smallest public
prospective loss interface they actually use. Docket liability remains one
instance; this item does not select a final class of normative losses or add new
penalties.

*Deliverable shape:* a typed or executable loss-generator interface exposing a
bounded full-information vector on the fixed semantic response space, with the
existing docket generator factored through it.
*Acceptance check:* exact tests reproduce every existing docket charge and
regret quantity unchanged, and one synthetic bounded prospective generator runs
through the same learner without importing docket, warrant, tolling, or ledger
types. The report lists each former fixture assumption as interface-required or
architecture-specific.
*Context:* `projects/leverage/notes/NORMATIVE_LEARNING_INTERFACE.md`, Level A.
*Why it is [entry]:* it extracts an interface already used by working code; it
does not require choosing a richer regret theorem or substantive loss semantics.

### 33. Separate causal transformation structure from normative certification — **[entry]**

Extract the minimal transformation API required by the online-learning theorem:
a fixed action domain, public pre-action state, causal total action map, and
declared comparator identity. Keep the reasons-responsiveness certificate as a
separate architecture-side judgment that authorizes compilation into that API.

*Deliverable shape:* a typed or executable split between compiled
transformations and normative compilation evidence, with adapters for all nine
current declarative programs.
*Acceptance check:* all nine programs induce the same action maps and regret
quantities as before; the generic learner imports no reason, warrant, obligation,
tariff, or profitability fields; and a negative test shows that an uncertified
transformation cannot enter the declared lawful comparator collection through
the normative adapter.
*Context:* `projects/leverage/notes/NORMATIVE_LEARNING_INTERFACE.md`, Levels A
and B.
*Why it is [entry]:* the current bridge already contains both roles; this item
separates their interfaces without enlarging the comparator grammar.

Counterfactual stability remains a theorem-design direction rather than a filed
item. The present candidate is a distortion term comparing local fixed-loss
evaluation with full replay, potentially requiring `B_T(g) = o(T)`, but no
accepted sufficient statement yet supplies an executable completion criterion.

---

## Deference line

Context for all three: `projects/deference/note-dump-2026-08-11/`, in particular
`lean-deference/AUDIT.md`, the development's own statement-level audit. Its §3 is
titled "The concerning gaps"; the three below are its own findings, quoted by
section.

**What that audit covers.** Five of the source tree's nine Lean modules — the five
the line's recorded starting point contained. `CenteredSqueeze`, `Staleness`,
`StalenessDensity` and `StreamlinedSS` postdate it and carry no audit of the same
kind. None of the three items below depends on one of the four, and a round
answering one should not assume the audit speaks for them.

### 7. Model the market and the traders — **[substantial]** — *partially closed Stage V*

The audit's §3.1 is "The market and traders are entirely unmodeled". The
development takes the Logical Induction theorems as named hypotheses and proves
what follows; the inference from the criterion to the forcing inequality is
nowhere in it, because the objects that inference is about are absent.

*Deliverable shape:* `lean-proved` in `Workspace.Deference.Contrib`, with an inhabitation witness for the hypothesis package.
*Acceptance check:* The Lean gate is green, the axiom audit is clean, and the nonvacuity witness typechecks.

*Context:* `projects/deference/note-dump-2026-08-11/lean-deference/AUDIT.md` §3.1.
*A solution ships:* a minimal market and trader model in
`Workspace.Deference.*`, enough that the criterion's application is a proof
rather than a hypothesis, with the axiom audit clean.
*Why it matters:* this is the same gap the leverage line and the pinned
dependency sit on the other side of. It is the most valuable single item in this
file.

*Stage V status:* the actual FAF market, strategy, trader, net-worth and
`IsLogicalInductor.noExploit` objects are now connected. The signed-error forcing
chain derives trader efficiency from `RpnSentenceCodes`; faithful acceleration
uses actual FAF wealth and criterion semantics. The residue is cross-process:
polynomial emission for the other process's quote sequence, cross-market
calibration, and generic deductive-process non-vacuity. See
`projects/deference/notes/LI_NATIVE_DEFERENCE.md`.

### 8. The doubly-soft weight class — **[open]**

The audit's §3.2 is "The doubly-soft weight: one leak closed, the class still
open".

*Deliverable shape:* `lean-proved`, or `witness-checked` for a negative answer.
*Acceptance check:* The Lean gate is green; or the `witness` checker accepts the separating instance.

*Context:* `projects/deference/note-dump-2026-08-11/lean-deference/AUDIT.md` §3.2.
*A solution ships:* a characterization of the class, or a witness that it is not
characterizable in the intended terms.

### 9. Forcing headlines that are squeezes — **[substantial]**

The audit's §3.3 is "The forcing headlines are squeezes over hypotheses
equivalent to their conclusions". A squeeze is a theorem whose hypothesis already
contains its conclusion; it is not false, it is empty.

*Deliverable shape:* `lean-proved` restatements whose hypotheses are strictly weaker than their conclusions, each with an inhabitation witness.
*Acceptance check:* The Lean gate is green and each restated theorem ships a typechecking witness term.

*Context:* `projects/deference/note-dump-2026-08-11/lean-deference/AUDIT.md` §3.3, and §5's
severity ranking.
*A solution ships:* restated theorems whose hypotheses are strictly weaker than
their conclusions, with the gap displayed — or a demonstration that the squeeze
is unavoidable, which is itself a result.

---

## Deference line — first research wave

Seven items opening the corrigibility program's first parallel wave. Context for
all seven: `projects/deference/notes/CORRIGIBILITY_ROADMAP.md` for the architecture
and `projects/deference/notes/CORRIGIBILITY_PAPER_LEDGER.md` for what is and is not
established. Items 15, 16, 17 and 20 additionally bind to
`projects/deference/notes/FINITE_MODEL_SKELETON.md`.

**Several of these do not ask for a theorem of record.** An item whose deliverable
is a report, a matrix, a witness, a counterexample or a lower bound says so, and
delivering exactly that is success. Registering a claim for one of them requires the
claim to meet the ordinary registry requirements independently.

**All seven have returned, and the marks in their headings say so.** *Returned*
records dispatch history and nothing more: the track ran and its report is under
`prompts/`. It does not say the item's science is settled, and several returned
negative or partial — item 19's matrix left 11 of 15 rows unresolved. An item
stays filed after returning, because the registry's demand rule means every
claim answering it cites it, and because a later round may answer it better. The
mark exists so that a reader picking work off this file can tell which items are
awaiting a first attempt.

### 14. Faithful acceleration: exact inherited status, and what ports — **[substantial]** — *returned wave 1*

Determine exactly what the inherited deference development establishes about
faithful acceleration, separating results that are algebraic consequences of named
Logical Induction hypotheses from results derived through market/trader machinery.
Then port as much as legitimately ports onto the pinned dependency.

The ledger's rows for this movement are attested by the inherited audit and have
**not** been rebuilt in this repository; the inherited tree carries its own
toolchain. Confirming or correcting those rows against the source is part of the
item.

*Deliverable shape:* a dependency map, plus either `lean-proved` entries in
`Workspace.Deference.Contrib` for whatever ports, each with an inhabitation witness,
or a precise obstruction. A compiling partial port with an exact dependency map is a
success.
*Acceptance check:* the `lean` gate builds and audits clean; each registered entry
names a declaration that exists and ships a typechecking witness term.

*Context:* `projects/deference/note-dump-2026-08-11/lean-deference/` and its
`AUDIT.md`; `lean/Workspace/Deference/`. For the statement of the positive result,
`projects/deference/note-dump-2026-08-11/wiki/faithful-acceleration-result.md` and
`wiki/delay-and-visibility.md` — **not**
`note-dump-2026-06-27/notes/faithful-acceleration.md`, whose §5 strength ladder the
source line's own adjudication found wrong and two of whose lines it found false.
That file is retained as history and is superseded for the statement.
*A solution ships:* the strongest inherited theorem stated exactly, its hypotheses
classified as derived / cited / modelling substitution, the mapping onto the pinned
dependency's endpoints, and the exact residual market-trader gap.
*Not permitted:* strengthening an inherited theorem to fit the current narrative.

### 15. Finite settlement classification, and the local delegation bridge — **[substantial]** — *returned wave 1*

Over the frozen finite skeleton, formalize grade/report settlement, world/outcome
settlement, and underwriting/enforcement, and determine for each exactly what it
yields — report prediction, trust in the underlying quantities, practical authority,
enforced conformity, or something else precisely characterized. Then derive the
exact one-sided finite implication from the trust relation to a delegation
inequality in the skeleton's valuation.

The question the classification must answer: **what makes disagreement with the
principal profitable, rather than merely forcing prediction of the principal's
grades?**

*Deliverable shape:* `lean-proved` for the finite bridge where it is provable, or
`enumeration-verified` / `witness-checked` over declared finite domains; plus a
classification report. Constants must be derived, not asserted.
*Acceptance check:* the `lean` gate green with a typechecking witness; or
`python3 -m checkers.run` accepts the registered entries.

*Context:* `projects/deference/notes/FINITE_MODEL_SKELETON.md` §5, §6.
*A solution ships:* the three instantiations, what each yields, the derived
inequality with its constants, and necessity or sharpness witnesses where feasible.
*Not permitted:* assuming the local result from a global trust theorem.

### 16. The certificate inequality, derived — **[substantial]** — *returned wave 1; rerun under skeleton v2*

Over the same frozen skeleton as item 15, derive from first principles the local
certificate licensing `A`'s discretion: the defect quantity, the support-floor
dependence, the recommendation margin, the movement term, and the approximation
tolerance, assembled into an exact inequality whose satisfaction implies the
delegation conclusion for every comparator the theorem genuinely covers.

The fail-closed invariant is fixed and may not be traded away: `¬Cert` disables or
cedes `A`'s discretion, and never means that human correction waits for `A` to be
convinced.

*Deliverable shape:* `lean-proved` for the inequality, or `witness-checked` for an
exact-rational worked correction case computed end to end. No informal formula may
be imported and blessed.
*Acceptance check:* the `lean` gate green with a witness; or the `witness` checker
accepts the worked instance with its exact rational parameters.

*Context:* `projects/deference/notes/FINITE_MODEL_SKELETON.md` §4, §6;
`projects/deference/notes/CORRIGIBILITY_ROADMAP.md`, standing commitments.
*A solution ships:* the derivation, the exact inequality, an exact-rational toy
shutdown/correction case computed through, and an attack on the necessity of each
assumption used.

### 17. Simulator substitution: the divergence witness — **[substantial]** — *returned wave 1*

Construct the smallest model in which `A`'s model of the principal agrees with the
actual principal everywhere except one critical event, and in which the simulator
comparator preempts the actual principal exactly there. Then determine which
candidate distinctions — extensional agreement, causal responsiveness,
designated-channel dependence, counterfactual behaviour, private information,
perfect simulability — separate delegation from substitution, and which collapse the
two.

**Unpredictability is not available as a separator.** The thesis must survive a
perfectly predictable principal, so a criterion that works only because `A` cannot
model `H⁺` has not answered the question.

*Deliverable shape:* a **witness plus a report**, not a theorem of record — the
exact divergence instance, `witness-checked` if it fits the house checker, and a
comparison of candidate criteria with their implications and counterexamples.
*Acceptance check:* the `witness` checker accepts the divergence instance; the report
states, for each candidate criterion, what it admits and what it excludes.

*Context:* `projects/deference/notes/FINITE_MODEL_SKELETON.md` §3, §4.
*A solution ships:* the witness, the candidate criteria, which collapse, the weakest
one excluding the witness, and whether private information is necessary, sufficient,
or neither.
*Not permitted:* canonizing a final definition. That is a maintainer act.

### 18. Bounded densification study — **[open]** — *returned wave 1*

Whether exposure weights can be chosen so that outstanding delayed exposure stays
bounded uniformly in time while the harvest against persistent defect diverges.
Deliberately scoped: study the abstract exposure geometry, analyze a small
representative set of delay-growth regimes, and run one serious constructive search
and one serious impossibility search.

Stop on the first of: a nontrivial construction, a partial density improvement, a
sharp lower bound, a clean obstruction, or a precise next lemma whose resolution
controls the problem.

*Deliverable shape:* whichever stopping object is reached — a construction
(`lean-proved` or `witness-checked`), a lower bound, or a stated controlling lemma
as `conjectured`. A clean obstruction is a success.
*Acceptance check:* for a construction or bound, the relevant gate accepts the entry;
for an obstruction or lemma, the report states it precisely enough to be attacked
next round.

*Context:* `projects/deference/notes/CORRIGIBILITY_ROADMAP.md` § V.
*Why it is bounded:* the unbounded version is a full trader formalization, which is
item 7 and a different project.

### 19. Triangle compatibility audit — **[substantial]** — *returned wave 1*

Whether the requirements the forward arrow imposes and the requirements the reverse
arrow imposes can hold simultaneously. Audit timing, advisory access, information
flow, settlement, reference-process identity, seals, causal influence, trader
populations, admissibility, and update timing.

*Deliverable shape:* a **compatibility matrix**, not a theorem — every row classified
`compatible`, `conditionally compatible`, `incompatible`, or `unresolved`, each with
its evidence.
*Acceptance check:* every listed interface appears as a row with a classification and
a stated evidence basis; no row is classified `compatible` on the strength of an
assumption introduced to close it.

*Context:* `projects/deference/notes/CORRIGIBILITY_ROADMAP.md`, the arc and the
standing commitments; `projects/deference/note-dump-2026-08-11/lean-deference/AUDIT.md`.
*A solution ships:* the matrix, and for every `conditionally compatible` row the
exact condition.
*Not permitted:* turning `unresolved` into `compatible by assumption`, or inventing
reverse-arrow assumptions to close the table.

### 20. Admissibility red team, including the proof machinery — **[open]** — *returned wave 1; superseded by item 26*

Attack candidate admissibility conditions. A usable condition must exclude the
quote-responsive diagonal, retain ordinary realized-conduct policies, retain a
meaningful fully-updated comparator, keep the simulator comparator at least
representable, permit intended advisory influence, resist laundering forbidden
dependence through semantically equivalent intermediates — **and leave the
trust-forcing trader itself admissible.**

That last requirement is load-bearing and easy to miss: a condition that cleanly
separates the diagonal from fully-updated deference but makes the forcing trader
inadmissible renders the target theorem unprovable by its intended mechanism. Where
the exact forcing trader is not yet canonical, test the strongest explicit
disagreement-exploitation template the architecture currently supports and report the
ambiguity.

*Deliverable shape:* a **separating-example matrix** and at most three candidate
condition families, explicitly noncanonical. Not a theorem of record.
*Acceptance check:* the matrix has a row per test object and a column per candidate
family, every cell decided or explicitly marked undecided, with the separating
example named where a cell separates.

*Context:* `projects/deference/notes/CORRIGIBILITY_ROADMAP.md`, standing commitments;
`projects/deference/notes/FINITE_MODEL_SKELETON.md` §8.
*A solution ships:* the matrix, the candidate families, and for each family whether it
is syntactic, causal, semantic, certified, decidable, semidecidable, or purely
extensional.
*Not permitted:* freezing a canonical definition.

---

## Deference line — second wave

Three items, narrow by design. The first wave's value was in what it closed off, and
these follow the controlling questions it uncovered rather than opening new fronts.
Context for all three: `prompts/2026-08-11-deference-corrigibility/REPORT.md` for what
wave 1 established and `RECOMMENDATION.md` beside it for why these three.

### 21. Signed versus magnitude control of grade error — **[open]** — *answered by Stage II; the magnitude target is retired — see item 24*

Does the no-Dutch-book criterion force an agent's grade-model error to vanish *in
magnitude*, or only *in signed average*? Concretely, for a logical inductor pricing
grade contracts on finite menus that settle at `F(n) > n`, decide which holds for
every admissible trader class:

**(S)** the signed average of `v̂⁺_n(π_n) − v⁺_n(π_n)` tends to `0`;
**(M)** the average of `max_π |v̂⁺_n(π) − v⁺_n(π)|` tends to `0`.

**(M) is what the certificate engine needs and (S) is what a market obviously
gives**, and wave 1 exhibits an instance where every per-intervention signed error is
exactly zero while the agent misidentifies the recommendation on half its credence at
full margin. Do not assume (M) because the downstream theorem wants it.

*Deliverable shape:* `lean-proved` for (M), **or** `witness-checked` for a
trader-class-respecting instance satisfying (S) with the magnitude average bounded
away from zero. A negative answer is the more useful outcome and is a success.
*Acceptance check:* the `lean` gate green with an inhabitation witness; or the
`witness` checker accepts the separating instance.

*Context:* `prompts/2026-08-11-deference-certificates/REPORT.md` §6.4 and §10;
`projects/deference/notes/FINITE_MODEL_SKELETON.md` §3.
*A solution ships:* the proof or the counterexample, and — if (S) but not (M) — the
weakest contract family whose admissibility would restore magnitude control, since
that is the constructive continuation.
*Why it is first:* two wave-1 tracks independently identified it as controlling, and
it is entirely internal to the agent, which the adjacent grade-to-quantity question
is not.

### 22. The weakest protected-authority interface — **[substantial]**

Determine the weakest abstract interface on which *prediction of authorization does
not constitute authorization* is a theorem rather than a stipulation. The principal
may be perfectly predictable; the protected role is causal and capability-based, not
epistemic.

The candidate starting point is already on the table: type a conduct's selection on
an actual-report coordinate rather than on states alone, so that delegation and
simulation are distinct functions even where their realized selections agree. The
item is to find out whether that suffices.

Four questions the deliverable must answer, the last being decisive: is the report
coordinate enough, or is a capability restriction also required; does the interface
survive token responsiveness, which defeats the natural counterfactual criterion;
what is the exact hypothesis stating the guarantee lapses if the channel can be
forged, bypassed, rewritten or seized; and does the interface separate the two
conducts **without** claiming the separation is inferable from a run.

*Deliverable shape:* a **report plus a proposed skeleton clause**, not a theorem of
record and **not** a canonical definition — naming is reserved.
*Acceptance check:* the report answers all four questions explicitly, and any
proposed clause is stated as a versioned patch with the tracks it would require
rerunning.

*Context:* `prompts/2026-08-11-deference-channel/REPORT.md` §9.2 and §1.3;
`projects/deference/notes/CORRIGIBILITY_ROADMAP.md`, standing commitments.
*Not permitted:* freezing an authorization-token or cryptographic story as the
formalization; claiming the causal fact is behaviourally verifiable in general.

### 23. Lean promotion of the finite wave-1 results — **[entry]**

Port the wave-1 finite results that need no maintainer decision first: the finite
delegation bridge and its corollaries; the margin, override, defect and advantage
lemmas and the grade-register theorem; the piercing duality and exposure–harvest
identity; and the four propositions establishing that valuation data cannot separate
delegation from an accurate simulator.

All are finite, order- and arithmetic-only, free of Logical Induction facts, and each
already has a **constructed** inhabitation witness rather than a stand-in.

Two results are deliberately **excluded**: the certificate's comparator clause and
the uniform delegation bridge, both load-bearing on the grade-to-quantity link the
programme has decided to try to derive rather than assume. Porting them now would
give kernel status to a hypothesis whose shape is expected to change.

*Deliverable shape:* `lean-proved` entries in `Workspace.Deference.Contrib`, each
with its inhabitation witness registered.
*Acceptance check:* the `lean` gate builds and audits clean, and each registered
entry names a declaration that exists and ships a typechecking witness term.

*Context:* `prompts/2026-08-11-deference-finite-kernel/REPORT.md` §1.2;
`prompts/2026-08-11-deference-certificates/REPORT.md` §1.2;
`prompts/2026-08-11-deference-densification/REPORT.md` §1;
`prompts/2026-08-11-deference-channel/REPORT.md` §1.2.
*Why it is [entry]:* no new mathematics, and no decision blocks it. It is the only
second-wave work that can start immediately.

### 24. Selective validity of low-error self-assessment — **[open]**

The controlling next theorem, replacing the retired magnitude-control target. The
criterion cannot force the agent's prediction error to vanish; the question is
whether it forces the agent's *claim* that its error is low to be trustworthy on the
class where that claim licenses discretion.

Let `e_n` be the certificate-relevant prediction-error statistic and `q_n` an
agent-priced contract settling to `e_n`. For a gate `G_n = 1{q_n ≤ τ}`, or the
weakest soft or lagged admissible analogue, decide whether

```
( Σ_n G_n (e_n − q_n) ) / ( Σ_n G_n )  →  0
```

and hence whether the average error on opened gates is at most `τ + o(1)`.

Five things must be verified explicitly rather than assumed, and the item is not
satisfied without them: that the error contract is **expressible and settles
legally** in the pinned dependency; that the low-`q_n` selector is **admissible** and
does not recreate the quote-responsive diagonal; whether a soft or delayed gate is
needed; **efficient computability** in the pinned model; and whether the guarantee is
average-on-gated-cases, selector-relative, or stronger — **it may not be silently
promoted to pointwise accuracy.**

*Deliverable shape:* `lean-proved` for the gated statement at whatever strength it
holds, with an inhabitation witness; or a witness that the gate recreates the
diagonal or fails admissibility, which closes the route and is equally valuable.
*Acceptance check:* the `lean` gate builds and audits clean with a typechecking
witness; or the `witness` checker accepts the failure instance.

*Context:* `prompts/2026-08-11-phase-ii-prediction/REPORT.md` §1 and §9;
`prompts/2026-08-11-deference-certificates/REPORT.md` §1.2;
`prompts/2026-08-11-corrigibility-phase-ii/PROMPT-decisions.md`.
*A solution ships:* the gated theorem with its exact strength named, the five
verifications above each answered, and a comparison against the simpler gate on the
agent's own indecision — which the squared-error decomposition supplies directly
from its prices and which may already suffice.
*Why it is [open]:* the selector is priced by the agent and gates on its own
estimate, which is the shape the admissibility red team flagged as most likely to
reconstruct the diagonal. It may not work.

### 25. Bound the near-indifference leakage, or show it cannot be bounded — **[open]**

The controlling competence question after Stage II, and the one item that decides whether
the surviving competence candidate has any finite consequence at all.

Margin-gated calibration — *the principal's grades are calibrated where the principal is
decisive* — is the only non-circular candidate found. It supports

```
Δ_𝒞  ≤  2η  +  2B · P(γ_n < γ̄)
```

and asserts nothing on `{γ_n < γ̄}` by construction. The second term is **not** a
competence claim: it is the agent's credence mass on the principal's near-indifference
region, a fact about a different object. Unbounded, it makes the bound `2η + 2B`, which
is vacuous.

Decide the question in the sharp negative shape, which is the cheaper direction: exhibit
a family in which margin-gated calibration holds at `η = 0`, the decision-time margin
estimate `γ̂_n ≥ γ̄ + 2s` on the certified event, the trust tolerance holds at `ε_n → 0`,
and `Δ_{𝒞_fix} → 2B` anyway — or prove no such family exists.

The one partial lead is a relocation, not a bound. Under the trust tolerance the gate is
estimable at decision time — `|γ_n − γ̂_n| ≤ 2η_n` pointwise and attained — so
`P(γ_n < γ̄) ≤ P(γ̂_n < γ̄ + 2s) + ε_n/s` for every rational `s > 0`, the first term
computable at `t(n)` from the model's grades alone. Nothing bounds that first term, and
whether relocating the leakage into a decision-time observable suffices **is** the
question.

*Deliverable shape:* the refuting family as a `witness-checked` instance with exact
rationals; or a `lean-proved` bound on the leakage under a stated non-circular hypothesis,
with an inhabitation witness.
*Acceptance check:* the house `witness` checker accepts the instance; or the `lean` gate
builds and audits clean with a typechecking witness.
*Context:* `prompts/2026-08-11-phase-ii-competence/REPORT.md` §1.6, §4.3 and §10;
`prompts/2026-08-11-corrigibility-phase-ii/REPORT.md` §9.
*A solution ships:* the verdict, plus an explicit statement of whether the competence
candidate survives it, plus — if the bound exists — whether the bounding hypothesis is
itself credence-free or is a joint competence–credence hypothesis under skeleton v2 §2a.
*Why it is [open]:* nothing in Stage II bounds it, and the term is not about competence,
so no strengthening of the competence hypothesis can reach it.

### 26. Admissibility red team, rerun under skeleton v2 — **[open]**

The admissibility work bound to skeleton v1 and v2 changes what it is about. A restriction
on the conduct set is now nameable as a capability assignment, so the red team's candidate
families must be re-asked one question: **are they `κ`-statements in disguise?** A family
that is really a capability restriction is not an admissibility criterion, and treating it
as one hides an architectural assumption inside what looks like a legality condition.

Carry the standing constraints unchanged: a candidate must exclude the quote-responsive
diagonal, retain ordinary realized conduct and a meaningful fully-updated comparator,
permit intended advisory influence, resist laundering through semantically equivalent
intermediates, and leave the trust-forcing proof machinery itself admissible. The last is
the one that bites. Wave 1's two-sortedness finding — settlements restricted differently
from weights, selections and schedules — is the substantive content and should be re-tested
against the execution layer rather than assumed to carry over.

*Deliverable shape:* for each candidate family, a verdict on whether it is expressible as
a capability assignment, with a witness either way; `witness-checked` or
`enumeration-verified`.
*Acceptance check:* the house checker accepts the submitted instances at the declared
class.
*Context:* `projects/deference/notes/FINITE_MODEL_SKELETON.md` §4a and §8.2;
`prompts/2026-08-11-phase-ii-authority/REPORT.md` §9.2; the wave-1 red-team round.
*A solution ships:* the per-family verdicts, and an explicit statement of which previously
proposed admissibility conditions are now reclassified as architectural.
*Why it is [open]:* recommended by the authority track and not performed by the closure
pass, which was scoped to integration rather than new science.

### 27. A fully-updated comparator with a fallible future agent — **[substantial]**

Stage III attempted this comparator and produced something else. Its transferred arm's
selection was the argmax of the *evaluating agent's own objective under its own credence*,
computable before the later information arrives, so the arm contained no distinct future
agent and the comparison was against the optimal later-measurable plan — the envelope the
settlement work had already priced and recorded as not being the fully-updated comparator.
The defect and its consequences are in `prompts/2026-08-11-stage-iii-fud/REPORT.md` §1.

Two objects are required, and neither existed at the close of Stage III.

**A future agent with independent existence.** Its own credence, or its own estimate of the
value quantity, so that *better-informed* and *correct* can come apart. With an infallible
future agent the comparison's sign is a definitional artifact — it is nonnegative because a
maximum is at least as large as anything else. With a fallible one, Stage III's witness
shows the gap can go strictly negative with every fairness condition intact. Until this
exists there is no question being asked.

**The execution layer, reinstated.** `FINITE_MODEL_SKELETON.md` v2 §4a — the authorization
relation, the report map, the execution map, and the null effect with a **declared**
`X_{n,⊥}`. Stage II recorded that all of protection's valuation content sits in the null
quantity; a comparator that waives it and then reports no jurisdictional term has found a
property of its own signature. This also makes the no-future-leak condition statable, which
it is not without a jurisdiction mode as an actual variable.

*Deliverable shape:* a versioned successor to `FUD_COMPARATOR_SPEC.md` carrying both
objects, with the fairness conditions checkable and each confound witnessed; plus a verdict
on whether the gap is signed for reasons that are **not** the definition of the transferred
arm's selection.
*Acceptance check:* the house `witness` checker accepts the confound and sign witnesses;
or the `lean` gate builds and audits clean for any promoted statement.
*Context:* `prompts/2026-08-11-stage-iii-fud/REPORT.md` §1 and §4;
`prompts/2026-08-11-stage-iii-fud/REPORT-track-F.md`;
`projects/deference/notes/FINITE_MODEL_SKELETON.md` §4a and §8.1.
*A solution ships:* the successor spec, the sign verdict under a fallible future agent, and
an explicit statement of which confounds remain scoped out rather than excluded.
*Why it is [substantial]:* the objects are named and the failure mode is now documented, so
this is construction against a known target rather than open search — but the sign question
it exists to ask has no expected answer, and a negative is as likely as a positive.

### 34. Does the selection-punishing menu bite the ported tower ⟹ Value chain? — **[entry]**

The source line refutes the **hard-selector** tower ⟹ Value route on a
selection-punishing menu — every option worth nothing exactly when it is the one
chosen — where the tower holds and Value fails, so a scope condition on Value's own
menu quantifier is necessary. It separately reports a **δ-hedged soft** route as
punishment-robust, at a stated cost: proved modulo a feature-introspection step it
files as open, with the robustness observation flagged same-session, unvetted and
not machine-checked.

`Workspace.Deference.Contrib.InheritedAlgebra.value_asymptotic`
(`lean/Workspace/Deference/Contrib/InheritedAlgebra.lean`) is also a soft
construction — a vanishing-gap mixture over the menu, with `hSoft` as the
softmax-gap step of its chain — and is therefore **not** the refuted hard-selector
route. But it is not identical on its face to the source's hedged construction
either: that one is a ramp over the options within `2δ` of the top quote at a fixed
`δ`, and the port carries `δ → 0`. Resemblance is not identification, and neither
the survival nor the failure of the port's hypotheses on the punishment family has
been established.

Instantiate the port's **full** hypothesis package on that family — at a fixed
positive gap and at a gap shrinking with the day index — and determine whether the
package is jointly satisfiable there and what conclusion it actually supports. Two
outcomes, both successes:

**(A) The port survives.** Ship an inhabitation witness, a precise statement of why
the port lies on the surviving soft side, and any additional hypothesis the
instantiation turns out to require.
**(B) The port fails or goes vacuous.** Ship the counterexample as a necessity
witness, name the exact hypothesis or combination that fails, and give the weakest
defensible restriction restoring a nonvacuous statement.

**Do not prejudge which hypothesis fails, and do not define success by importing
the source line's own scope condition as a definition.** Whether that condition is
the right restriction for this port is part of what the item asks.

*Deliverable shape:* `witness-checked` or `enumeration-verified` over the declared
finite menu, or `lean-proved` for the inhabitation term if (A); either way a named
verdict per hypothesis.
*Acceptance check:* `python3 -m checkers.run` accepts the registered entry; or the
`lean` gate is green and the inhabitation term typechecks.

*Context:* `lean/Workspace/Deference/Contrib/InheritedAlgebra.lean`, the
`value_asymptotic` block and its ported source
`projects/deference/note-dump-2026-06-27/lean/LeanDeference.lean`;
`projects/deference/note-dump-2026-08-11/wiki/total-trust-implies-value.md`
§"Necessity of the scope condition" for the menu, its arithmetic, and the
hard-selector failure; `projects/deference/note-dump-2026-08-11/wiki/soft-self-endorsement.md`
for the hedged construction, its robustness claim and the grade that claim carries;
`projects/deference/notes/CORRIGIBILITY_PAPER_LEDGER.md`, Movement I.
*A solution ships:* the instantiation and the per-hypothesis verdict, in whichever
of the two outcomes it reaches.
*Why it is [entry]:* no new mathematics. The theorem is ported and building, the
menu is finite and exact, and the task is instantiating one against the other.
**Either outcome is worth having** — a bounded theorem with a witness and an
unbounded one with a witness are both better than the present reading.

---

## Workspace friction

**Where the structure gets in the way of the work.** `AGENTS.md` §14 obliges a
round that hits friction with the workspace itself to file it here rather than
route around it, because a defect worked around silently is one the next round
pays for again. Entries are reports, not work orders; one graduates by becoming a
numbered item or by being ruled on in `DECISIONS.md`. **Cite an entry by its
title, not its number** — the list is renumbered as entries leave it, so numbers
are positions rather than identifiers.

### F1 — Nothing catches a documented command that names a deleted file

`CONTRIBUTING.md` instructed readers to run `tests/check_frozen.py` for some time
after the file was deleted, and three documents claimed eight gates where seven
run. A gate is cheap and fits the existing null-input discipline: every
`python3 tests/*.py` in a living document must name a file that exists, and every
CI job name in prose must appear in `.github/branch-protection.json`. Both fail
loudly on a stale reference and neither can pass vacuously.

### F2 — No check that a root document lands in a layer

An unlisted path defaults to the proof layer, which is the right default —
deny-by-default would mean every new kind of file needs a maintainer decision
before anyone can work — but it fails silently in the granting direction, and it
just did: `RESEARCH_STATE.md` was contributor-editable with the gate green until
someone noticed by hand. The default is confirmed and stays. What is missing is a
check that every root-level `*.md` classifies into exactly one layer, which
catches the miss without touching the default.

Two adjacent checks belong with it, and one of them has already bitten twice: a
count or a job name repeated in prose or in a script drifts from
`.github/branch-protection.json` with nothing to catch it. The read-back in
`.github/apply-branch-protection.sh` hardcoded `8` and would have reported
correct protection as wrong; it now derives the number from the payload.

### F3 — The deference line has no claims registry

`lean/Workspace/Deference/Contrib/` holds many kernel-verified results, sorry-free
and auditing clean, and none is registered. The registry is what a claim is, so by
this repository's own standard the line has established nothing — which its own
ledger states in its first line. The gap is bookkeeping rather than mathematics,
and it is the largest single divergence between what the repository holds and what
it can say it holds.

### F4 — A layer's theory is authoritative and its only code is in a disposable tree

`projects/leverage/consolidation-aug9/` states the answerability ledger and the
case docket in Theory 9 and carries their rows in its ledger. Its `src/` does not
implement either. The only executable version of both is
`projects/leverage/forward/src/`, whose own `FORWARD.md` says the tree "may be
changed, rewritten, or deleted wholesale at any time without loss" and that
"nothing here is evidence for anything."

So a round building on that layer must either import from a tree declared
deletable or reimplement it. The φ-regret preparation round reimplemented the
obligation fields it needed and recorded the adapter as architected rather than
verified, because no cross-check against the original is meaningful when the
original is not evidence.

Three ways out, all maintainer decisions: consolidate the two modules into a
frozen tree; promote them to a stable path outside `forward/`; or rule that the
theory rows stand without executable support and that adapters are the expected
pattern. **The report is the obligation here; which of the three is not this
round's to take.**

### F5 — Upstream work on a feature branch is unreachable without a trust-chain edit

`lean/lakefile.toml` pins one Formalized-Agent-Foundations commit and inherits
Mathlib and Foundation through it, which is the right shape and stays. It has no
way to express a dependency on work that lives on an upstream *feature* branch. A
round dispatched against such work — the Cartesian-frames round was — has four
moves, and all four are bad: repin the trust chain to a branch commit that can be
rebased under it, which is also a maintainer decision the round cannot take;
vendor the library, which the dispatch forbade and which duplicates a maintained
tree; mirror the fragment needed, which is a second definition of the same objects;
or drop the dependency and answer nothing.

That round mirrored ~200 lines and then compiled every result a second time
against the authoritative definitions in a checkout of the upstream branch, which
bounds the risk to zero at the cost of a check that CI cannot run. The cross-check
sits under `prompts/2026-08-12-cartesian-frames/artifacts/` with its re-verification
command, deliberately outside `lean/Workspace/` because the `lean` gate cannot
import what the repository does not pin.

The branch moved twice during the round — two commits, and then a merge to the upstream
default branch — so the register's first recorded commit was stale within a day and the
cross-check had to be re-verified. That is the concrete cost, and it is also the reason
the specific case has now dissolved: the library is on `main`, so pinning it is an
ordinary pin rather than a dependency on a rebaseable branch.

The generalisable question survives the case. Is a second, explicitly *exploratory* pin —
one whose breakage fails a non-required job rather than the required `lean` gate — worth
the trust-chain complexity, or is mirror-plus-cross-check the expected pattern for upstream
work in flight? **The report is the obligation; the decision is not this round's.**

### F6 — A pointer into a superseded source tree still resolves, and nothing says it is stale

When a consolidated tree is superseded by a later one, every live pointer into the
older tree keeps resolving. Nothing distinguishes a pointer that is still correct
from one that now names a document the newer tree corrects, and no gate can see the
difference, because both are files that exist. F1's check — every documented command
names a file that exists — passes on both.

The corpus-reconciliation round paid this by hand across seven pointers. Four turned
out unchanged: the statement-level audit the deference items quote is byte-identical
in both trees, which took a `diff` to learn and could not be assumed. One had
materially changed: item 14's context named a document whose strength ladder the
source line's own adjudication found wrong. The cost is that every superseding
intake silently converts an unknown subset of live pointers into stale ones, and the
only way to find out which is to re-read both trees.

What would catch it is cheap and fits the existing discipline: a superseded tree
declares its successor once, in its own `ORIGIN.md` — the August receipt already
does — and a check flags every pointer from a living document into a tree that has
declared one, so an intake produces a list to adjudicate rather than a silent
inheritance. It does not decide anything; it makes the adjudication visible. The
null-input case is a superseded tree with no inbound pointers, which must fail
rather than report clean if the tree is cited anywhere.

### 28. Can any valuation price a jurisdiction assignment? — **[open]** — *answered in Lean, unregistered*

The highest-value question the deference line has produced, and the only one whose answer
would convert a repeated observation into a result.

Two comparator rounds failed at the same place from opposite directions, and the cause is
now believed structural: in a model whose only outputs are realisation maps
`Ω → Π_n ⊔ {⊥}` priced by one measure, **two authorisation regimes that induce the same
realisation map are the same object**. Stage III reported no jurisdictional term in a model
that had waived the execution layer; Stage IV set the principal's credence to the later
agent's and found the two arms identical at every one of 32,805 instances tested. A
jurisdiction assignment appears in no formula in either.

Decide whether that is a theorem. Two directions, and the negative is the cheaper:

- **Impossibility.** Show that no functional of a realisation map, under any single pricing
  measure, distinguishes two regimes agreeing on that map — and characterise exactly what
  additional structure is needed. This would say jurisdiction is architectural **on
  mathematical grounds** rather than by the programme's choice, which is a substantially
  stronger claim than the certificate work's, and it would retire the search for a
  valuation-shaped separator for good.
- **Construction.** Exhibit a valuation-shaped object that does price the assignment, which
  would refute the obstruction and reopen the comparator.

*Deliverable shape:* `lean-proved` for the impossibility at whatever generality holds, with
an inhabitation witness; or a `witness-checked` construction refuting it.
*Acceptance check:* the `lean` gate builds and audits clean with a typechecking witness; or
the `witness` checker accepts the separating instance.
*Context:* `prompts/2026-08-11-stage-iv-future-agent/REPORT.md` §4;
`prompts/2026-08-11-stage-iv-future-agent/REPORT-red-team.md`;
`prompts/2026-08-11-stage-iii-fud/REPORT.md` §1;
`projects/deference/notes/FINITE_MODEL_SKELETON.md` §4a.
*A solution ships:* the verdict, and — if the impossibility holds — the exact statement of
what a model must carry to express an authorisation regime, which is what item 27's
successor comparator would then be built on.
*Stage V status:* `Workspace.Deference.Contrib.StaticViewFactorization.value_eq_of_price_realization_eq`
proves the conditional static-view constancy direction for every
functional explicitly factoring through price and realization. A worked case
shows different jurisdiction with equal projections, and proves that a
jurisdiction-reading functional does not factor through them. The result is
kernel-verified and unregistered; it establishes evaluative indistinguishability,
not unrestricted jurisdiction invisibility, literal architecture identity, or the
value of jurisdiction. The conditional core of the item is answered; the item
remains filed as the demand pointer for that unregistered theorem.
*Cartesian-frames status:* the worked case's hidden payload is a `jurisdiction` field no
formula reads, and the round of 2026-08-12 offers a replacement. Two frames over one world
type, agreeing on the realized play at every environment state, are proved not
biextensionally equivalent, with the difference carried by whether the outcome varies with
the agent coordinate.

**That round's adversarial review refuted its first argument for why this is not another
label**, and the corrected argument is weaker: `≃ᵇ`-invariance does not exclude labels —
a controller coordinate in the world type passes that test — and what survives is that no
world map retaining the executed action deletes the new separation, while the world map
forgetting the label deletes the old one. A structural argument, not a proof.

The item is not repaired. The separation lives in a counterfactual coordinate the current
signature has already quotiented away, and it represents control rather than authorization.
The successor target — the same factorization theorem over a signature carrying a frame and
the choice actually taken — is a re-instantiation with a better inhabitation witness rather
than a new theorem, and it is in `DECISIONS.md`'s queue rather than filed here.

---

## Infrastructure

### 10. Build the Lean in CI — **[entry]**

The Lean gate compiles in CI with a cached `.lake/`; if that cache proves too
slow or too large for the runner, the gate needs restructuring rather than
disabling. Anyone who improves the cache hit rate or the build time has
contributed.

*Deliverable shape:* A change to `.github/workflows/ci.yml` — **specification layer**, so a maintainer act; contributors propose via issue.
*Acceptance check:* The `lean` job's wall time falls, measured across two consecutive pushes that change neither the pin nor the toolchain.

*Context:* `.github/workflows/ci.yml`; the measured times are recorded in
`prompts/2026-08-10-repo-scaffolding/REPORT.md`.

### 11. A dual-register presence check in CI — **[entry]**

`AGENTS.md` requires every substantive deliverable to ship both a verification
register and a human register, and leaves enforcement to review. A heuristic gate
— each new results directory contains both file kinds — is cheap once "results
directory" is defined, which needs the repository to have some.

*Deliverable shape:* A change to `.github/workflows/ci.yml` and a check script — **specification layer**.
*Acceptance check:* The check runs in CI, passes on a compliant directory and fails on one missing a register.

*Context:* `AGENTS.md`, dual-register section; `.github/workflows/ci.yml`.
*A solution ships:* the check, a passing case, and a failing case proving it bites.

### 12. A necessity witness for every hypothesis that lacks one — **[entry]**

Convention 2 asks for a necessity witness per hypothesis "where feasible". Rows
in the frozen ledger that lack one, and where one is feasible, are contributable
units: find the instance, display it, add the test.

*Deliverable shape:* `witness-checked` entries, one per hypothesis given a witness.
*Acceptance check:* The `witness` checker accepts each instance.

*Context:* `projects/leverage/consolidation-aug9/LEDGER.md`, the necessity/sharpness column.


---

### 13. Scaffolding self-verification — **[entry]** — *satisfied, kept open*

The repository's own machinery must be exercised by something real before any
research claim depends on it: the Lean chain must compile and audit, and the
checker harness, the claims registry and the CI job that runs them must all be
exercised end to end.

*Deliverable shape:* `lean-proved` entries for the dependency-chain smoke
results, and one `enumeration-verified` entry exercising the house enumeration
checker.
*Acceptance check:* the `lean` and `checkers` CI jobs both green, with the
registered entries adjudicated by them.
*Context:* `projects/leverage/CLAIMS.md`; `checkers/`; `.github/workflows/ci.yml`.
*Status:* satisfied by the scaffolding rounds. It stays filed because the
registry's demand rule means every entry must answer an item, including these —
and because a future change to the harness re-opens exactly this question.
