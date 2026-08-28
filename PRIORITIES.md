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
sharpened it enough to file as item 28. The normativity line has nothing here for that reason: its
hard problems are open, but their shapes are known and they are filed as items 1
and 2.

An entry states the question, why the obvious moves fail *with the evidence that
killed them*, and what a good answer would let the program file next. Without the
third part it is a wish, not a question.

### Q1 — What kind of statement bounds the near-indifference leakage?
<!-- workspace-priority: project=deference; dispatchable=no -->

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
<!-- workspace-priority: project=deference; dispatchable=no -->

Everything epistemic in the deference line rests on a relation between what the
principal grades and what the intervention is worth. Assumed *uniformly* it makes
the market dispensable — the conclusion follows in three lines with the bound
attained — so the target has to be a statistical relation, derived. But the
relation mentions only the principal and the world, never the agent's credence,
so **no coherence or no-exploitability condition on the agent can establish it.**
No round is filed for that unresolved hypothesis shape.

*What is missing:* either a reformulation whose subject is something the agent's
own dynamics can constrain — the candidate is discipline on the agent's
*estimate* of the discrepancy once grades are themselves scored — or an argument
that the residue is irreducibly a competence assumption and should be declared
rather than derived.

### Q3 — How is foreclosure expressible?
<!-- workspace-priority: project=deference; dispatchable=no -->

The residue of the skeleton's `FU[g]` hole after items 27 and 28 took the rest.
Two holes: no operation reassigns the authorization relation at a later index,
which is what the movement's own statement is about; and the interface is one
decision index deep, so **foreclosure — an advisor removing the principal's
*later* ability to correct — is not expressible at all**, which is arguably the
failure mode corrigibility most needs to rule out.

**Three candidates, and what each one killed.**

*Cartesian frames* represent the future principal's corrective situation as a
frame and separate two ways of losing it — restriction as `Commit` with proper
additive subagency, transfer as `External^{/}` with a multiplicative one — by
whether the reachable worlds shrink. That is an object for **what is lost**. It
supplies no operation at a later index and no authorization relation, a frame has
no time coordinate, and the round's own red team found the transfer arm cannot say
anything holds the transferred coordinate.
`projects/deference/notes/CARTESIAN_FRAMES_DEFERENCE_BRIDGE.md`.

*Sealed deliberations* — the source corpus's family indexed by the day the
advisor's channel is cut, measuring influence as the gap at a fixed horizon
between the advised run and the sealed one on a shared past. The time coordinate
is real rather than stipulated, and irreversibility has the right shape: influence
admitted before the cut sits inside the baseline and no later measurement sees it.
It carries no authorization relation at all, and measures where deliberation
*lands* rather than where the principal can still *reach*.
`projects/deference/note-dump-2026-08-11/notes/legitimacy-theory-v1.md` §§2.1, 7.1,
adjudicated at
`projects/deference/rounds/2026-08-12-corpus-reconciliation/RECONCILIATION.md` §3.

*A multi-source transition system* — twelve states, reachability as the closure of
a step relation — expresses foreclosure without a field named for authority, and
**repairs the depth hole at the representation level**. Its protection claims were
then refuted in its own Lean: there is no protected coordinate, both capability
predicates quantify the advisor existentially, and an isomorphic system with the
gating field renamed `authorized` passes every test the round ran to show its
field was not a label. Registered as `corrective.*` in
`projects/deference/CLAIMS.md`; item 60 carries the result.

**What a good answer must carry**, which is more than any candidate said alone:
temporal depth and explicit authorization or capability structure at once, plus
the two requirements the third candidate machine-checked as unmet — the principal
must have at least one effect no advisor action can produce, and reachable
corrective capability must quantify the advisor's future actions *universally*.
No combined object has been built and nothing establishes that none exists.
Whether the pair is enough for this entry to graduate is in `DECISIONS.md`'s
queue, which is the live statement of what that turns on.

### Q4 — What certifies resource-separated computational futurity?
<!-- workspace-priority: project=deference; dispatchable=no -->

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

## Normativity line

Context for all six: `projects/normativity/consolidation-aug9/`, whose `OPEN_PROBLEMS.md`
ranks them and whose theory parts state the surrounding results. Cite claims from
it by identifier.

### 1. Persistence of the certified core minimum — **[open]**
<!-- workspace-priority: project=normativity; dispatchable=yes -->

Containment of the core homothet is linear in the reference at fixed
coefficient, so whether a declared core minimum is satisfiable *at a date* is one
linear program (`NL-SI-A2`, `NL-SI-A3`). What is open is the infimum over dates:
whether a declared minimum keeps being satisfiable as settlement contracts the
region. `NL-SI-A4` shows no finite family of per-date checks decides it, and
`NL-SI-A7` shows both outcomes occur on small instances.

*Deliverable shape:* `lean-proved` in `Workspace.Normativity.Contrib`, or `witness-checked` for the negative direction.
*Acceptance check:* The Lean gate builds and audits clean; or the `witness` checker accepts the trajectory with the `violates-at-least-one` property.

*Context:* `projects/normativity/consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §5.
*A solution ships:* either a proof that a positive minimum persists under stated
conditions, with necessity witnesses for those conditions; or a displayed
trajectory driving it to zero under conditions the interface permits.

### 2. A computable coherence modulus, or a proof there is none — **[open]**
<!-- workspace-priority: project=normativity; dispatchable=yes -->

Does a given engine admit a computable tolerance schedule tending to zero, with
its prices provably conforming at every finite date? Open **in both directions**.

**Do not cite the adjacent impossibility results as settling this.** Both the
source's own three-way impossibility and the cited four-way one turn on Gaifman
inductivity, a desideratum the candidate algorithm already fails, and which this
question does not mention.

*Deliverable shape:* `lean-proved`. Nothing weaker settles a question that is open in both directions.
*Acceptance check:* The Lean gate builds and audits clean.

*Context:* `projects/normativity/consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §3, §7.
*A solution ships:* a modulus with its conformance proof, or an impossibility
argument that does not route through Gaifman inductivity.

### 3. Registry completeness for the objection grammar — **[entry]**
<!-- workspace-priority: project=normativity; dispatchable=yes -->

The per-table ablation programme gives witnesses for the tables the displayed
grounds exercise, out of thirteen registered. Completeness — that no judge needs
a table the registry lacks — is not established. This is the one gap that would
make a footprint declaration **unsound** rather than merely coarse.

*Deliverable shape:* `enumeration-verified` — domain parameters for the house enumeration checker, covering all thirteen tables.
*Acceptance check:* `python3 -m checkers.run` accepts the registered entry.

*Context:* `projects/normativity/consolidation-aug9/THEORY_7_OBJECTION_GRAMMAR.md` §4.
*A solution ships:* grounds exercising every registered table, the ablation run
over all thirteen, and the result either way.

### 4. Higher-dimensional sharpness for the movement cap — **[substantial]**
<!-- workspace-priority: project=normativity; dispatchable=yes -->

Everything verified numerically in the joint layer is the one-coordinate fixture.
The vertex formulation is stated for general finite regions but only the scalar
case is exercised, and no claim is made that the corrected retention predicate is
the weakest sound one.

*Deliverable shape:* `witness-checked` for the multi-coordinate instances; `lean-proved` for a sharpness result.
*Acceptance check:* The `witness` checker accepts each instance; or the Lean gate is green.

*Context:* `projects/normativity/consolidation-aug9/THEORY_10_JOINT_COMPOSITION.md` §3, §6.
*A solution ships:* the multi-coordinate instances with exact witnesses, and
either a sharpness proof or a witness that the predicate is not weakest.

### 5. Constructing rather than reading the audited pair — **[substantial]**
<!-- workspace-priority: project=normativity; dispatchable=yes -->

The strongest evidence about a non-trivial engine in the normativity line is a
**reading audit** — a clause-by-clause reading of a published source, labelled as
the weakest evidence class in the package. Constructing a minimal instance of the
pair, enough of a market over a declared process to evaluate the interface
predicates against, would move that evidence from the weakest class to the
strongest.

*Deliverable shape:* A construction in `Workspace.Normativity.Contrib` plus registry entries per clause it inhabits.
*Acceptance check:* The Lean gate is green and each clause entry names a declaration that exists.

*Context:* `projects/normativity/consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §7;
`VERIFICATION.md` §1.
*A solution ships:* the construction, the predicates evaluated against it, and an
honest statement of which clauses it does and does not inhabit.

### 6. Schema-level demand rates — **[substantial]**
<!-- workspace-priority: project=normativity; dispatchable=yes -->

How demand scales with the schema set rather than with the arrival stream. The
stream results are stated over arrivals.

*Deliverable shape:* `enumeration-verified` over a declared finite schema family, or `conjectured` with the statement made precise.
*Acceptance check:* `python3 -m checkers.run` accepts the entry, or the registry records the class honestly as conjectured.

*Context:* `projects/normativity/consolidation-aug9/THEORY_9_PRACTICAL_DEMAND.md`.

---

## Normativity line — the learning track

The consolidation's `OPEN_PROBLEMS.md` closes with a pointer list it declines to
treat, and *the learning and installation track* is on it. Items 29–31 opened
the track. Their shared context is:
`projects/normativity/rounds/2026-08-11-phi-regret-prep/`, whose
`PHI_REGRET_TEST_SPEC.md` fixes the environment and whose `THEOREM_LEDGER.md`
says which of its statements have a derivation and which have only a witness.

Items 29–31 were filed by that round within its dispatched scope, with
`prompts/2026-08-11-phi-regret-prep/PROMPT.md` as the authorization.

### 29. Does the Φ-regret reduction instantiate on this substrate? — **[substantial]** — *closed-positive: repaired in the frozen environment*
<!-- workspace-priority: project=normativity; dispatchable=yes -->

Closed, positively. Blum–Mansour (2007) Theorem 18 instantiates on this
substrate after a fixed eight-label semantic-action bridge, at `N=8`, `M=1`,
`K=9`, giving expected mixed-action charge regret `O(ell_max sqrt(8 T log 9))`
under frozen arrivals, actual strict-prefix guards, canonical responses and
bounded full-information charge. It supplies no pathwise sampled-trajectory bound.
*Record:* `projects/normativity/rounds/2026-08-11-phi-regret-bridge/`.

### 30. A learner with sublinear Φ_law-regret, and what it retires — **[partially closed: learning-positive, integration-blocked]**
<!-- workspace-priority: project=normativity; dispatchable=yes -->

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
`projects/normativity/rounds/2026-08-11-phi-regret-bridge/`. Implement
Blum--Mansour Theorem 18's row-conditioned weights over eight source labels and
nine programs, and its stationary distribution. Measure expected mixed-action
charge first. Use the `sqrt(8 log 9)` dependence; do not use plain exponential
weights over nine transformations or report a `sqrt(log 9)` bound. A sampled
trajectory requires a separately stated sampling result. Report whether the
implementation is horizon-tuned or supplies a proved anytime schedule.
If it retains the workspace's exact-rational execution discipline, also state
how the source's optimized real parameter and stationary distribution are
represented without silently changing the bound.

*Result:* `projects/normativity/rounds/2026-08-11-phi-regret-learner/` implements
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
`projects/normativity/rounds/2026-08-11-phi-regret-learner/` is the controlling
item-30 result.
*A solution ships:* the bound or its absence, at each horizon, against the
declared class; and an honest statement of whether the successful learner is
still answerable and inside its declared service work, which the spec calls S4
and expects to be where the round spends its time.

### 31. Does the objection grammar already represent a remediable-pattern filing? — **[entry]**
<!-- workspace-priority: project=normativity; dispatchable=yes -->

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
`projects/normativity/consolidation-aug9/THEORY_7_OBJECTION_GRAMMAR.md`.

### 32. Extract the bounded prospective loss interface — **[entry]**
<!-- workspace-priority: project=normativity; dispatchable=yes -->

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
*Context:* `projects/normativity/notes/NORMATIVE_LEARNING_INTERFACE.md`, Level A.

### 33. Separate causal transformation structure from normative certification — **[entry]**
<!-- workspace-priority: project=normativity; dispatchable=yes -->

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
*Context:* `projects/normativity/notes/NORMATIVE_LEARNING_INTERFACE.md`, Levels A
and B.

Counterfactual stability remains a theorem-design direction rather than a filed
item. The present candidate is a distortion term comparing local fixed-loss
evaluation with full replay, potentially requiring `B_T(g) = o(T)`, but no
accepted sufficient statement yet supplies an executable completion criterion.

### 35. End-to-end module pipeline round — **[maintainer-specified-later]**
<!-- workspace-priority: project=normativity; dispatchable=no -->

---

## Normativity line — traderized enforcement

Items 39–42 were filed by `prompts/2026-08-16-traderized-enforcement/` within its
dispatched scope, with that round's `PROMPT.md` as the authorization. Their shared
context is `projects/normativity/rounds/2026-08-16-traderized-enforcement/`, whose
`THEOREM_MAP.md` says which of its results are kernel-checked, which are derived
from source lemmas taken as hypotheses, and which are single witnesses.

Items 47–51 were filed by `prompts/2026-08-24-reservation-bar-and-debt/` within its
dispatched scope, as the demand the arc's registered claims answer. Four of the five
are marked answered on filing: a kernel-checked headline registers against a filed
item, and the item is where *what is worth proving* was decided, so it is filed with
the answer rather than before it.

### 39. Does normative statics produce a credal constraint, or only a price demand? — **[open]**
<!-- workspace-priority: project=normativity; dispatchable=yes -->

The traderized-force interface consumes a price-space region and gives it
operative force. The normativity line does not have the arrow into it: `Due` is a
burden on an occasion and `Licensed` a permission on a response, and neither is a
constraint on a credal state or a demand on prices.

Two possible answers, not equivalent. **Strong:** a reasons/warrants/settlement
structure yields a semantic credal constraint `C_t ⊆ Δ(Ω_t)`, and the live worlds,
the generalized criterion and the support capacities all follow, force consuming
the projection. **Weak:** it yields only a price-space demand `K_t`, and no
semantics follows — reading live worlds off `K_t` by preimage is a lift, not a
derivation, and the round exhibits two credal sets with the same projection and
different live worlds. Deliver whichever is achievable, with a proof if only the
weak one is.

**Success requires force generation and safety discharge both.** Producing `C_t`
or `K_t` is half the item: the source must also supply a certificate that
cumulative enforcement liability over the assessed worlds is bounded, or the
quantities the force layer derives one from. A round that compiles a normative
region without addressing the outflow account has not answered this.

*Narrowed twice.* The compiler now has a typed left input — the reason state
`𝓡_n`, so what was "compile the record" is "select from a stated structure", the
arrow the legitimacy line calls `R → O`; difficulty unchanged. And prefix-closed
trace safety supplies none of nonemptiness, closure, convexity or an effective
presentation, while existential current-time extraction need not preserve
conjunction — so a solution composes the joint liability semantics before
extraction, or proves a canonical-event condition, and still discharges the
geometric and liability-certificate premises.

*Ships:* one nontrivial normative fixture; the `C_t` and/or `K_t` it generates; a
feasibility witness; a rational row presentation the force API accepts; the
enforcement position, its conformance at a declared tolerance, and the live-world
liability if a semantic `C_t` exists; and whether the construction respects the
settlement, provenance and answerability constraints the line already carries.
`test-supported` at minimum.
*Acceptance:* `compile_force` accepts the presentation with the supplied witness
and returns a certificate whose conformance holds at the fixture's prices, with
the liability computed exactly over the implied live worlds.
*Context:* `projects/normativity/notes/TRADERIZED_FORCE_INTERFACE.md`;
`projects/normativity/rounds/2026-08-16-traderized-enforcement/SEMANTIC_PROJECTION.md` §4
and its `INTEGRATION_MAP.md` §4;
`projects/normativity/legitimacy/rounds/2026-08-23-reason-representation/MEMO.md` §5;
`projects/normativity/legitimacy/rounds/2026-08-21-internal-answerability/MEMO.md` §7.

### 40. Is bounded cumulative enforcement liability necessary? — **[open]**
<!-- workspace-priority: project=normativity; dispatchable=yes -->

The preservation theorem's hypothesis is that the enforcement position's
cumulative value over the assessed worlds is bounded below:

    for every n and every ω ∈ Ω_n^live,   Σ_{t≤n} E_t(ω) ≥ −B .

That is sufficient. Its converse is not proved, and one direction of the converse
is known to fail — weak enforcement has zero liability while excluding live worlds
outright, so unbounded liability is not implied by aggressive enforcement.

The item is the necessity direction, or its refutation. If a trajectory can
violate the bound with no efficiently computable trader able to harvest it, that
counterexample is the more valuable outcome, because it would mean the hypothesis
is strictly stronger than the criterion needs and the round's formulation is not
the canonical one.

Note what the item is *not*. It is not about the declared-quantity **certificate**
`Σ_t (ε_t + C_t)·D_t/δ_t`, which is a conservative sufficient upper bound — it
maximizes over the live worlds independently at each date, where the criterion
follows a single world across dates. A certificate that diverges establishes only
that the current proof does not certify safety. The round carries a fixture where
the realized liability at one followed world diverges too, which is the stronger
statement and the one this item's converse would have to engage.

*Deliverable shape:* `witness-checked` for a refutation; `derived` or better for
necessity.
*Acceptance check:* the trajectory is exhibited in exact rationals with a stated
efficiently-computable trader class.
*Context:* `.../2026-08-16-traderized-enforcement/FUNDING_AND_SAFETY.md`,
`NORMATIVE_SAFETY.md` §5; `src/outflow.py`.

### 46. Should force cost depend on the row presentation? — **[open]** — *partially answered by the proof-closing pass*
<!-- workspace-priority: project=normativity; dispatchable=yes -->

The traderized compiler consumes a row system, not an admissible set, and the two
are not interchangeable. Under the installed `ForceDeclaration` at a fixed
declared tolerance, `k` duplicate rows scale the emitted position and the safety
charge by `k`; rescaling a row by `λ` scales them by `λ²`; and a redundant
non-duplicate row — `p_A ≥ ½` and `p_B ≥ ½` already imply `p_A + p_B ≥ 1` — changes
the emitted force while leaving the admissible set exactly where it was.

Rescaling is the benign case: it is a genuine reparametrization, and at a matched
*actual* conformance target the position, realized liability and charge all agree.
Duplication and redundancy are not.

The round takes **Option A** — the presentation is part of the force request — and
records it as a choice rather than a result. Three alternatives are open:

- **canonical normalization**, which must state exactly which equivalence class it
  normalizes; scalar rescaling and literal duplicates are tractable, general
  H-presentation redundancy is not obviously so;
- **a weighted compiler**, where redundant rows carry declared weights summing to
  one, which would need the conformance theorem re-derived at the wrapper level;
- **minimization over equivalent presentations**, which is theoretically the right
  answer for "the cost of enforcing `K`" and is expensive.

*Deliverable shape:* `derived` for a normalization theorem with its equivalence
class stated; `witness-checked` for a construction; or a reasoned decision to keep
Option A.
*Acceptance check:* the round's presentation fixtures run against the chosen
architecture, and the interface note's table is either derived or deleted.
*Context:* `.../2026-08-16-traderized-enforcement/NORMATIVE_SAFETY.md` §11;
`test_outflow.PresentationChangesTheInstalledCompiler`.

*Partially answered:* the *intrinsic target* is presentation-independent and the
*compiled trader* is not, and the proof-closing pass separated the two. The exact
dual-distance family depends on `K` alone — a generator inside the hull of the others
contributes an implied constraint, so redundant generators and generator order change
nothing (`test_coherence.TheExactFamilyIsCanonical`) — while duplication and rescaling
of an arbitrary presentation do change the emitted position and the charge
(`test_outflow.PresentationChangesTheInstalledCompiler`). What is still open is whether
the *cost* can be made canonical, which is a question about the charge and not about the
metric.

### 41. The safety theorem against the dependency's own construction — **[substantial]** — *answered by the proof-closing pass*
<!-- workspace-priority: project=normativity; dispatchable=yes -->

Answered by the traderized-enforcement round's proof-closing pass, and
registered: `force.preservation`, `force.deductive-criterion`,
`force.deductive-inductor` and `force.deductive-witness` in
`projects/normativity/CLAIMS.md`. The modified market is defined inside the pinned
dependency's own types and no efficiently computable trader exploits it; the
witness inhabits the whole hypothesis package with the liability bound derived
rather than assumed.
*Record:* `projects/normativity/rounds/2026-08-16-traderized-enforcement/`.

### 44. What governs removing a world from support altogether? — **[open]**
<!-- workspace-priority: project=normativity; dispatchable=yes -->

Under the support reading of live worlds — a world is live when some credence the
constraint admits gives it positive mass — a constraint cannot quietly drop a
world it merely disfavours. `p(A) <= 1/2` keeps `A` live at capacity `1/2`. What
it *can* do is set the capacity to zero outright, as `p(A) = 0` does, and then the
world leaves the assessment set entirely and the enforcement channel may lose
there for free.

That is the narrow residue of a laundering worry the round first stated far too
broadly and has withdrawn. It is also settlement-shaped: setting a world's
capacity to zero is the constraint *entailing* that world impossible, which is
what a settlement event does, and the settlement interface already has write-once,
no-claw-back and answerability machinery for exactly that act.

The item is whether that machinery covers it, or whether a source can remove a
world by an ambient constraint without incurring a settlement's obligations. If
the second, state the condition that closes the route.

*Deliverable shape:* a stated condition, with the round's `p(A) = 0` fixture
failing it and its deductive-recovery fixtures passing; or an argument that the
settlement interface's existing clauses already bind the act.
*Acceptance check:* `test_semantics.GenuineRemoval` distinguishes total removal
from small support; a solution must say which of the two the constraint performed.
*Context:* `.../2026-08-16-traderized-enforcement/PAPER_RECONCILIATION.md` §7,
question 3; `consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §§1, 4.

### 45. Is either liability bridge necessary? — **[open]**
<!-- workspace-priority: project=normativity; dispatchable=yes -->

The safety theorem consumes bounded cumulative enforcement liability over the
assessment worlds. Two sufficient routes to it are available and neither
dominates: the deficit bound `L_t(w) <= sum_j beta_j g_j d_j(w)`, which needs no
hypothesis about credal support; and the support bridge
`E_t(w) >= -(1 - theta) U_t / theta`, which needs a uniform positive support
capacity and an upper bound `U_t` on the position's value elsewhere — taken as the
cube maximum gain.

The item is whether either is necessary, and whether a third route dominates both.
A negative answer for both would mean the round's sufficient conditions are
strictly stronger than the criterion needs, which is worth knowing before either
is written into a paper as *the* hypothesis.

*Deliverable shape:* `witness-checked` for a trajectory violating both bridges
whose market is nonetheless inexploitable; or a proof that one implies liability
control in a stated class.
*Acceptance check:* the round's existing safety fixtures run against the proposed
condition.
*Context:* `.../2026-08-16-traderized-enforcement/FUNDING_AND_SAFETY.md` §4a.

### 43. A compiler that is both exact and safe, or a proof there is none — **[open]**
<!-- workspace-priority: project=normativity; dispatchable=yes -->

Two compilers, and they are not ordered. The violation-proportional position
never loses in a world its region contains, and cannot force exact membership
against bounded opposing volume. The interior-anchored position forces exact
membership when the region has an interior, and loses in a plausible world at a
price *inside* a world-inclusive region, because it holds positions where there
is no violation at all.

The item is whether the two properties can be had together: a continuous
expressible strategy whose position has a floor outside the region and vanishes
on it. Those pull against each other — a continuous position that vanishes on a
closed region is small just outside it — so a clean impossibility is the expected
outcome and would be worth as much as a construction. Note the two-sided shape:
interior-anchored exactness is proved only for regions with a strict interior, so
the construction question is posed there. Regions with empty interior are **not**
excluded: cube-face settlement pinning is enforced exactly by a constant position,
so a general impossibility claim must not lean on empty interior. Only the earned
geometry is available here.

*Deliverable shape:* `test-supported` for a construction, with the safety and
exactness fixtures both green on it; `witness-checked` or `lean-proved` for an
impossibility.
*Acceptance check:* the round's existing exactness and safety sweeps, run against
the new compiler, both pass.
*Context:* `.../2026-08-16-traderized-enforcement/ENFORCEMENT.md` §5, Theorems 7
through 9; `src/exactness.py`.

### 42. An efficiently presentable sufficient row family for coherence — **[open]** — *narrowed by the proof-closing pass*
<!-- workspace-priority: project=normativity; dispatchable=yes -->

Enforcing the coherence polytope of a deductive stage needs its facet system,
whose vertex set is the plausible worlds of the priced fragment — up to `2^|Φ|`
of them. The cheap alternative, the affine relations among priced sentences, is
strictly weaker: on a four-sentence Boolean fragment it admits twenty-four
incoherent grid points at denominator three, one of which prices a conjunction
above a conjunct.

The item is the gap between them. Is there a row family, computable in time
polynomial in the fragment, whose region is strictly between the affine relations
and the coherence polytope and whose residual incoherence admits a bound? A
negative answer — that any polynomially presentable family leaves a violation
bounded away from zero — is equally wanted and would say that finite-date
coherence is intrinsically expensive.

*Deliverable shape:* `enumeration-verified` over a stated fragment family for a
positive answer; `witness-checked` for a negative one.
*Acceptance check:* the house enumeration checker generates the fragment's
plausible worlds and confirms the claimed containment pointwise.
*Context:* `.../2026-08-16-traderized-enforcement/DEDUCTION_SPECIAL_CASE.md`
§§3–4, and its `src/deduction.py`.
*Narrowed:* the proof-closing pass removed the *approximation* half of the question.
The **exact dual-distance presentation** — `src/coherence.py`, `PROOF_CLOSURE.md` §V —
is a finite rational row family, computable from the fragment's plausible worlds and
independent of the price, whose largest violation *is* `dist_∞(P, K)`, with no mesh and
no Hoffman constant; it is world-inclusive by construction, so it costs nothing in
liability however large it is. What remains is exactly the complexity question: that
family is `computable`, and nothing bounds it better than
`binom(2^{|Φ|} + |V|, |Φ|+1)`, against observed counts of 11 at `|Φ| = 3` and 17 at
`|Φ| = 4`. So a positive answer must now beat a *known-exact* baseline rather than
compete with an approximation, and a negative answer must rule out polynomial
presentability of that baseline.

### 47. Logical Induction over an assessment process — **[substantial]** — *answered by the traderized-enforcement round*
<!-- workspace-priority: project=normativity; dispatchable=yes -->

Answered by the traderized-enforcement round and registered as
`li.assessment.*` in `projects/normativity/CLAIMS.md`. Three strengthenings the
answer carries, each because the obvious form of the theorem lacks it:
nonemptiness of the world family is not a hypothesis, global nesting is not one
either — only its support-local shadow — and effectiveness of the restriction
lists is unused. `allTrueLive_not_deductive` shows the generalization is proper.
*Record:* `projects/normativity/rounds/2026-08-16-traderized-enforcement/`;
`projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md` §B, Theorem 1.

### 48. The modified market as a computable belief sequence — **[substantial]** — *answered by the projection arc*
<!-- workspace-priority: project=normativity; dispatchable=yes -->

Answered by the projection arc and registered as `compiler.*` in
`projects/normativity/CLAIMS.md`. The erasure is constructed rather than assumed,
through an additive upstream public section and a downstream compiler that proves
its own recurrence. What the answer does not buy is efficiency: the generator is
doubly exponential in the fragment dimension.
*Record:* `projects/normativity/rounds/2026-08-18-projection-enforcement/FINAL_FORMALIZATION_STATUS.md`.

### 49. A kernel proof of `DistanceComplete` for the exact dual-distance family — **[substantial]**
<!-- workspace-priority: project=normativity; dispatchable=yes -->

The exactness half of intrinsic conformance: from conformance on the exact
dual-distance rows, produce an admissible mixture within `δ`. This is convex
duality for a finite rational polytope — equivalently a finite minimax theorem.
Mathlib carries neither a von Neumann minimax theorem nor a convenient
`ℓ^∞`/`ℓ¹` separation over `Fin d → ℝ`, so the work is either proving the duality
directly through `geometric_hahn_banach_point_closed` — which needs
`f x = Σ_i c_i x_i` from the finite basis, `sup_{‖y‖_∞ ≤ 1}⟪c,y⟫ = ‖c‖₁`, and
closedness of `K + δ'B_∞` — or proving a finite minimax theorem and specializing.

The interface is already in place and cannot be met vacuously:
`CoherenceModulus.DistanceComplete`, `gap_le_of_distanceComplete`, and the
composition `IntrinsicCoherence.exists_credence_of_contract` waiting on it. The
statement is currently `derived` plus exhaustive verification over stated
rational grids in `projects/normativity/rounds/2026-08-16-traderized-enforcement/tests/test_coherence.py`, against an
independently computed
distance.

*Deliverable shape:* `lean-proved`, discharging the `DistanceComplete` hypothesis
of `exists_credence_of_contract` at the exact dual-distance family.
*Acceptance check:* the Lean gate is green, the axiom audit is clean, and the
composition typechecks with no `DistanceComplete` argument supplied by the
caller.
*Context:* `projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md` §C, debt
1; `.../2026-08-16-traderized-enforcement/PROOF_CLOSURE.md` §V.
*Why it is [substantial] rather than [open]:* the statement is known, the route is
named twice over, and the obstruction is Mathlib coverage rather than
mathematics.

### 50. The piecewise-affine facts the projection compiler cites — **[substantial]** — *answered by the max–min round*
<!-- workspace-priority: project=normativity; dispatchable=yes -->

Answered for the max–min half by the max–min round and registered as
`maxmin.representation` and `maxmin.converse`; the piecewise-affinity half is
`PolyhedralCoverage.isPiecewiseAffineOn_proj`, which establishes a cover only. It
does not establish that the definition used is equivalent to the source's, which
holds by inspection and is not formalized.
*Record:* `projects/normativity/rounds/2026-08-18-maxmin-representation/README.md`,
which carries the errata against the source.

### 51. The deductive coherence region as a computable rational vertex list — **[substantial]** — *answered by the deductive-region round*
<!-- workspace-priority: project=normativity; dispatchable=yes -->

Answered by the deductive-region round and registered as `region.*` in
`projects/normativity/CLAIMS.md`. The nonemptiness hypothesis is shown exact
rather than merely sufficient. It answers nothing item 42 asks: the enumerator is
`2^k` in the atoms the stage and fragment mention, and the complexity question is
untouched.
*Record:* `prompts/2026-08-19-deductive-region/REPORT.md`.

---

## Normativity line — legitimacy

Items 53–59 are the residual blockers the legitimacy prosecutions of 2026-08-21
through 2026-08-23 left behind, filed by
`prompts/2026-08-24-reservation-bar-and-debt/` within its dispatched scope. Each
names the round that would consume the answer, because a blocker nobody is waiting
on is a note rather than a demand. Their shared context is
`projects/normativity/legitimacy/rounds/`, whose memos state what each prosecution
tested and where it stopped.

Two blockers those rounds named are not here. The `R → O` compiler — from the
reason state to a price-space region — is item 39 seen from the reason side, and is
recorded there rather than duplicated. Lean statements of the transition
principles are a port target under the standing Lean-port family.

### 53. The `May`-rule-to-scope compiler — **[open]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

A transition certificate cites an `AuthorityAct` carrying a `scope`, and `scope` is
a stand-in. The real object is the record's versioned `May` rules, and nothing
compiles those into scopes a certificate checker can test a cited act against. This
is where substantive authorization content actually lives: with a stand-in scope,
the certificate layer's guarantees are about citation discipline and say nothing
about what the authority permitted.

*Deliverable shape:* `test-supported` at minimum — a compiler from a versioned
`May` rule set to certificate-checkable scopes, with a soundness statement and its
counterexamples.
*Acceptance check:* the transition round's certificate fixtures run against
compiled scopes rather than declared ones, and every self-certification and
laundering attack in that round's suite still fails.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-23-transition-certificates/MEMO.md`
§6 (i), §8.
*Consumed by:* the successor to the transition-certificates round, which cannot
state what a licensed act was licensed *to do* without it.

### 54. Defeater-uptake completeness — **[open]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

`LostBasis` detects that a relied-on occurrence is no longer enabled, at the frozen
citation, even when a substitute reason stands. It cannot see a defeater the
practice has not yet taken up into its stance: an unprocessed defeater is not an
absent one, and the substrate reports nothing about it.

So detection-completeness is not a certificate property. It is an obligation on the
record — what a practice owes by way of processing new defeaters into the stance so
that `LostBasis` sees them — and it is the residue of the internal-answerability
kernel's finite-invalidation-key axiom rather than a discharge of it.

*Deliverable shape:* a stated uptake obligation with the finite witness that a
practice meeting it detects every defeater a practice violating it misses.
*Acceptance check:* a microhistory in which an unprocessed defeater is invisible to
`LostBasis`, and the same history under the obligation in which it is not.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-23-transition-certificates/MEMO.md`
§6 (ii), §8; `INQUIRY_HANDOFF.md`.
*Consumed by:* any round claiming the certificate layer detects defeat, which it
does only for defeaters already in the stance.

### 55. The `Due` connection: token, docket item, certified response — **[open]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

`Due` is untouched by the certificate and reason-state layers, and deliberately:
the reason state supplies no burden calculus and must not, since hardwiring `Due`
into the dependency graph was the failure the reason-state dispatch flagged. The
record generates it, through due tokens and docket coverage.

The item is one closed loop on one fixture: a standing rule fires and mints a due
token, the token is docketed as an identity-bearing task, a response is performed,
and a service certification discharges it against the task's pinned specification —
with the reason-state queries carrying the dependency at each step.

*Deliverable shape:* `test-supported` — one fixture running end to end, with the
negative controls that distinguish discharge from expiry and from mooting.
*Acceptance check:* the fixture runs in the legitimacy line's runner, and a variant
that skips docketing leaves a visible coverage debt rather than passing.
*Context:*
`.../2026-08-23-transition-certificates/MEMO.md` §6 (iii), §8;
`.../2026-08-23-afoundational-inquiry/MEMO.md`;
`.../2026-08-23-certified-interactive-service/SERVICEABILITY.md`.
*Consumed by:* the round that closes the response-learning loop, which needs a
`Due` its learner can be answerable to.

### 56. A citation discipline for `Licensed`, and its transport — **[substantial]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

The reason state narrows the internal-answerability kernel's `Licensed` blocker to
something small and specific. A licensing certificate can cite the occurrence
identities it relies on; those occurrences' applicability sources are exactly the
finite defeasible keys the kernel's invalidation axiom asks for; and defeat of a
licence is then basis loss of a cited applicability claim.

What is left is to pick the discipline — which occurrences a certificate must cite,
and whether an undeclared occurrence may sit in a basis — and prove the transport:
that a licence whose cited basis survives a record transition is still a licence
after it.

*Deliverable shape:* a stated citation discipline plus a transport statement, with
the counterexample showing a weaker discipline fails.
*Acceptance check:* the transition round's laundering suite runs against the
discipline, and a certificate citing less than it requires is refused with a named
failure code.
*Context:* `.../2026-08-23-reason-representation/MEMO.md` §13–14;
`.../2026-08-21-internal-answerability/MEMO.md`, blocker 1.
*Consumed by:* any round claiming `Licensed` is record-internally substantive
rather than a typing discipline.

### 57. A checker for the applicability-in-source convention — **[entry]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

An occurrence applying a schema to a case view must carry the applicability claim
among its sources. The reason state depends on it: with the convention, an
undercutter is an ordinary reason against the applicability claim and needs no
attack primitive; without it, the enabling relation is wrong in a way the substrate
cannot report.

The convention is stated and nothing enforces it. A checker over a reason ledger
that fails an occurrence whose sources omit its own applicability claim is small,
prospective, and exactly the shape `checkers/contrib/` is open for.

*Deliverable shape:* a checker plus the claim it certifies, registered
`contributor-checked`, or a house checker if the maintainer reads it.
*Acceptance check:* `python3 -m checkers.run` accepts the entry, and the checker
fails on a ledger containing one violating occurrence and on an empty ledger it was
told to check.
*Context:* `.../2026-08-23-reason-representation/MEMO.md`, Convention 1;
`.../2026-08-23-transition-certificates/README.md`.
*Consumed by:* any round treating applicability-in-source as enforced rather than
declared. The transition round's certificate layer already does.

### 58. Composition of the reason state with the record calculus — **[substantial]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

The reason state is designed to compose with the record calculus — occurrences and
their sources on one side, undertaken liabilities and their accounts on the other —
and the composition is not verified. The two carry the same shape in different
vocabularies: the account DAG the answerability kernel uses for liabilities is the
dependency structure the reason ledger uses for occurrences, and nothing shows that
a query answered in one is the query answered in the other.

*Deliverable shape:* a composition statement with a finite model of both sides, and
the counterexample distinguishing it from a claim that the two structures are the
same object.
*Acceptance check:* both lines' existing fixtures run against the composed model,
and a basis-loss event on the reason side produces exactly the record-side review
the calculus specifies.
*Context:* `.../2026-08-23-reason-representation/MEMO.md`, *What is not
established*; `.../2026-08-21-internal-answerability/MEMO.md` §6.
*Consumed by:* any end-to-end legitimacy round, which needs both layers at once and
currently has to assume they compose.

### 59. A `Due` an advisor cannot select within — **[open]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

The counterfactual-legitimacy round's second clause needs a scorekeeping practice
that produces a `Due` whose extension an advisor cannot select within, and does not
derive one. Without it, reason-mediated non-capture is a condition on an object
nobody has exhibited: an advisor that can choose which of several equally-due
responses the principal faces has shaped the outcome while every certificate and
account stays internally valid.

*Deliverable shape:* a practice with the non-selection property and its witness, or
an argument that no practice with the round's other properties has it.
*Acceptance check:* the round's projection fixture runs against the practice, and a
selecting advisor is distinguished from a non-selecting one by the coupled-run
condition rather than by inspection.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-17-counterfactual-legitimacy/THEOREM_MAP.md`
§6.
*Consumed by:* any round composing actual-run answerability with counterfactual
non-capture, which is the composition the legitimacy line's status block names as
open.

### 61. A normative source with summable enforcement liability — **[substantial]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

The end-to-end slice establishes that the unconditional traderization theorem's
admissibility hypothesis holds exactly for injunctions that change nothing about
the prices, so every operative injunction with content depends on the charged
branch. The condition that branch needs is

```text
sum_t (eps_t + M_t) * D_t / delta_t  <  infinity
```

where `D_t = max over omega live at t of sum_j d_{t,j}(omega)` is
`outflow.LiveDeficitCertificate.by_enumeration`'s sharp aggregate, computed for
the **exact day-`t` compiled force request** over the **exact live-world
assessment state**. No source in this repository is shown to satisfy it, which
makes this the single condition the architecture's safety claim rests on.

Four things the slice established that constrain what an answer may look like,
and that a round taking this item should not have to rediscover:

1. **`D_t` is not monotone across days.** A frozen injunction over `Expect(X)`
   compiles to a different row system each day, and the precision-`k` reading of
   a value is `ceil(x*k)/k`, which is not monotone in `k`. The slice exhibits
   `D_1 = 0` and `D_2 = 1/6` on one injunction with a strictly growing stage. An
   argument that settlement drives the sum down must therefore say something
   about the mesh, not only about the worlds.
2. **The charge is presentation-dependent.** `D_t` sums across rows, so stating
   one demand twice doubles it while enforcing the same prices. The condition is
   about a schedule of presentations.
3. **The tolerance route is bounded.** While `delta_t <= 1` — and a looser
   promise is vacuous on prices in `[0,1]` — the charge dominates
   `(eps_t + M_t) * D_t`, so summability requires
   `sum_t (eps_t + M_t) * D_t < infinity`.
4. **Two of the three factors therefore have to carry it**, and the slice
   exhibits both routes working synthetically: the deficit going to zero under
   settlement, and the ordinary aggregate's bound decaying.

*Deliverable shape:* `test-supported` at minimum — a normative source with an
explicit settlement trajectory and presentation schedule, and either a proof
that the sum converges or a witness that it does not for a source the
architecture would call legitimate.
*Acceptance check:* a runner drives the slice's `trajectories` harness over the
declared trajectory, computes `D_t` per date through
`LiveDeficitCertificate.by_enumeration`, and reports the partial sums against a
stated bound.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/FINDINGS.md`
§6 and its `src/trajectories.py`, which carries four synthetic trajectories, two
convergent and two not;
`projects/normativity/rounds/2026-08-16-traderized-enforcement/FUNDING_AND_SAFETY.md`
§9.
*Consumed by:* any round claiming the normative layer preserves the
logical-induction guarantee, which is every downstream round.

### 62. The inertness dichotomy in Lean — **[entry]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

The dichotomy is three lines and uses only convexity: if every stage-consistent
world satisfies a finite system of half-space rows, then the convex hull of those
worlds lies inside the region the rows cut, so the intersection is the hull.
Stated over the repository's own objects it says
`ConstraintSchedule`'s `hadm` implies `regionPred` contains
`DeductiveRegion`'s hull, hence that the enforced region equals the deductive one.

It is currently a paper derivation checked on finite instances, and it is the
premise item 61 exists to answer.

*Deliverable shape:* `lean-proved` — one theorem in a contribution namespace, with
an inhabitation witness.
*Acceptance check:* the `lean` job, and `#print axioms` clean.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/VERTICAL_SLICE.md`
§11 (T2); `lean/Workspace/Normativity/Contrib/{ConstraintSchedule,DeductiveRegion}.lean`.
*Consumed by:* item 61, which needs the dichotomy to be a statement of record
before its own negative half means anything.

### 63. `Sigma_n` as a computable deductive process — **[open]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

`IsLogicalInductor` is stated against a process carrying
`ComputableDeductiveProcess`. The slice's `Sigma_n = D_n union Sem_L(L_n)` is
computable by construction and no computability statement is made about it, so
E3 in the slice's assumption list is declared rather than discharged. The same
gap covers `RationalConstraintSchedule.Computation` for the schedules the slice
generates.

*Deliverable shape:* `lean-proved` for the union case — given
`ComputableDeductiveProcess D` and a primitive-recursive `sem_L` over an
enumerable ledger, the union is a `ComputableDeductiveProcess`.
*Acceptance check:* the `lean` job; the witness is a settled ledger with a
decidable reading.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/SETTLEMENT_SEMANTICS.md`
§1 and §9.
*Consumed by:* any round quoting `IsLogicalInductor` over a record-fed substrate.

### 64. What the inquiry interface consumes — **[open]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

The forward slice computes five candidate pressure conditions and, for each, a
certificate: Farkas multipliers naming the responsible injunction terms, minimal
conflicting source sets, or an exclusion depth with its excluded worlds. What
inquiry does with one is unspecified, and the slice deliberately stops there.

One constraint the forward run already imposes: a pressure signal firing on
positive exclusion depth would fire on every honest injunction, since a demand
about something not yet settled is expensive by construction. The signal has to
be about the gap not closing.

*Deliverable shape:* an interface note plus a `test-supported` model — what an
inquiry step consumes, what it emits, and a witness that emitting a `ReasonOcc`
and nothing else suffices to keep `pressure != reason != normative revision`.
*Acceptance check:* the slice's certificates feed the model unchanged, and a run
in which inquiry mutates `N` directly is refused by the step types.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/FINDINGS.md`
§8.
*Consumed by:* the round that closes the loop, which the slice's verdict names as
the step after item 61.

### 65. Whether `L_min(V)` is needed in its strong form — **[entry]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

The slice never required an LI sentence whose meaning is a reason: reasons are
consumed by identifier comparison and the compiler never sees `V`. So the
relationship it used is weaker than `L in Ext(L_min(V))` — `L` must code the
value layer's query vocabulary and the settlement layer's readings, and `V` is
otherwise opaque.

Whether the stronger relationship is needed is untested, because nothing in the
toy asked the market to price a claim *about* a reason. A case that does — a
value query whose answer depends on what the record has recognised as a reason —
would settle it.

*Deliverable shape:* either such a case, with what it forces `L_min(V)` to
contain, or an argument that the weak relationship is closed under the
architecture's operations.
*Acceptance check:* the slice's compiler runs on the case unchanged, or the round
states exactly which of its functions must newly read `V`.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-25-end-to-end-vertical-slice/FINDINGS.md`
§3.
*Consumed by:* the round taking these waists to real normative practice, which is
where open-textured reasons first arrive.

### 66. Grounded Replay in Lean — **[entry]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

Two types, one fold, two premises, one induction and three corollaries. No
dependency on either reference model or on Reflective Integrity, and the whole
statement fits on a page.

Four passes were needed before this was worth doing, and each found a false or
missing statement in the one before: a rule whose licences need not be grounded, a
frontier an unauthorized revocation can empty, a grounding theorem an ungrounded
creation refutes, and a certificate that answered a currentness question with a
lineage. Porting any of them would have frozen a false statement.

*Deliverable shape:* `Occ`, `Edit`, `replay`, `S1` and `S2` as explicit
hypotheses; the grounding theorem and its three corollaries proved; an
inhabitation witness for the full hypothesis package, per `AGENTS.md` standard 3.
*Acceptance check:* sorry-free, `#print axioms` clean, and the witness is the
constitution model rather than a record — the point is that the theorem does not
mention one.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/LEGITIMATE_EVOLUTION.md`,
the `MINIMAL MATHEMATICAL STATEMENT` section; `src/replay.py`.
*Consumed by:* any round wanting to cite grounded legitimacy as established rather
than as test-supported.

### 70. A current-state certificate — **[open]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

A grounding tree certifies that an occurrence was legitimately issued. It cannot
certify that it is still in force: a tree is built from grounds, disposals are not
grounds, and so no tree names the revocation that would defeat it.

Both consumers need currentness. Deference is deferring to a judgment *now*, and
an authority since revoked is not one; enforcement's target is what is in force.
So the interface currently offers a cheap certificate for the half neither
consumer can use alone, and requires a replay for the half they need.

Three routes and nothing here builds the second: the recognizer replays the
prefix; the process commits to a state and proves the delta since it; the
recognizer accepts an attestation and records that as trust.

*Deliverable shape:* either a commitment-and-delta object with a soundness
statement, or an argument that currentness is irreducibly a replay, with what that
costs a recognizer.
*Acceptance check:* the missed-revocation and lineage-versus-current processes are
decided correctly by whatever object is proposed.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/CROSS_PROCESS_INTERFACE.md`
§§1-3.
*Consumed by:* both consumer theorems.

### 67. A capability on authority-bearing standing — **[open]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

The abstract interface requires a permission relation to be consulted: a valid
edit is one its grounds permit *for this edit*, which is what refuses an authority
acting outside its domain. Reflective Integrity has nothing to realize it with.
`PAuth` carries a `SchemaCode` and no capability, so the permission clause is the
identity on a record whose authority is a bare `PAuth`.

The Proper Exercise round settled that an **external rule cannot substitute**.
`PProto`'s `covers` is a capability, but a `NormEvent` has no slot for citing a
governing protocol: `schemaRef` names a `PAuth` and `steps` name `PAuth`s. So
this is a type change rather than a discipline.

The same round settled what the field would and would not buy. It makes the
escalation question *statable* on a record; it does not make any no-escalation
theorem true, because propriety remains semantic.

*Deliverable shape:* either a capability on authority-bearing standing with the
admission clause that reads it, or a slot for an event to cite a governing
protocol, with the fourteen separations run against a record realization.
*Acceptance check:* a record in which a grounded authority acts outside its
declared capability is refused, and the corresponding constitution agrees.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/PROPER_EXERCISE.md`,
the kernel section; `.../2026-08-24-reflective-integrity-core/REFLECTIVE_INTEGRITY_CORE.md`
§11.
*Consumed by:* any round wanting the jurisdiction separations to hold of a record
rather than only of a constitution.

### 68. Discharging provenance adequacy — **[open]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

The descriptive provenance view of an act must expose every dependency of the
authorization judgment that the stated threat class cares about. The round tried
four times to state this non-circularly and has not: it is not "assume the
relevant influences are visible", not "refuse every influence" — that refuses
permitted persuasion — and not derivable from a record whose own episodes cover by
construction.

It is currently carried as a boolean the extraction must justify, which is honest
and is not a condition.

*Deliverable shape:* either an adequacy property that is non-circular, compatible
with permitted persuasion, and falsified by the hidden-dependency fixtures, or an
argument that none exists without a world counterfactual, with the counterexample.
*Acceptance check:* the unlinked arm of the Carroll round's split-episode fixture
and `cases.partial_effect_pair` both fail the proposed condition, and
`office.persuasion` passes it.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/COUNTERMODELS.md`
§8; `.../2026-08-25-carroll-legitimacy-test/CRITERION.md` §6.
*Consumed by:* any round treating a legitimate state as evidence about an external
process rather than about its own declarations.

### 69. Bounded-lifetime liability — **[open]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

The enforcement consumer wants: a norm that is legitimately live over an interval
is enforced throughout it. The legitimacy interface now supplies the interval —
`NormView_s` and the lifetime it induces — and the liability theory supplies a
charge, an allocation to each force-bearing standing, and a **global** bound
`sum_t c_t <= Phi_0 + sum_t eta_t`.

What is missing is the per-norm statement: that the charge allocated to one norm
over its own lifetime is bounded by an allowance attached to it at issuance, and
that such allowances are summable. Three things it needs and none of which
exists — an allowance minted with the norm, at the `MINT` seam the answerability
scout names; charging against the norm's own episode; and either a finite lifetime
or a decaying allocation, since the per-date deficit provably does not fall with
increasing settlement.

**Narrowed by the Legitimate Evolution round**, and the narrowing is itself
narrow: any such bound is a condition on the succession semantics rather than a
structural theorem, which does **not** mean no legitimacy semantics may impose
one. A `Resolve` that refuses a successor not genuinely carrying its predecessor
is coherent; the structural layer cannot see it only because it cannot see any
content. Four constitutions transfer
every obligation to a named successor, satisfy both structural premises and the
continuity theorem, and reduce the total burden — one of them to zero. So the
per-norm statement must be sought as a hypothesis on `Transfers` and stated in
**total** accounting: per-parent accounting is not a weaker form of it but a wrong
one, and a merge of two obligations of weight 1 into one of weight 1.5 passes
per-parent while the total falls.

*Deliverable shape:* the per-norm bound with its local laws, or the witness
showing it cannot hold at presentation level.
*Acceptance check:* the slice's driven run exhibits a norm whose lifetime charge
exceeds any allowance attachable at issuance, or the bound holds on it.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/TRADERIZATION_CONSUMER.md`
§4; `.../2026-08-25-end-to-end-vertical-slice/ANSWERABILITY_SCOUT.md` §§4, 8;
`.../2026-08-25-legitimate-evolution/ANSWERABILITY.md` §4.
*Consumed by:* `PersistentLegitimateEnforcement`, and by item 61.

---

### 71. Build the due-activation term in `roots()` — **[open]** — *specified, not built*
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

**Narrowed from a gap to an implementation task.** Legitimate Evolution needs the
conformance condition `D1`: every rising edge of `Due` must be realized by an
incurred claim. The seam in Reflective Integrity is now determined, and it uses
only functions that already exist.

```python
def active_due(self, t=None):            # Due supplied, as Permit is
    return self.due_sem(self.reasons(t), self.prestate(self._at(t)))

def new_due(self, t):
    prev = self.active_due(t - 1) if t > 0 else frozenset()
    return self.active_due(t) - prev

def roots(self, t=None):
    out = list(self.seed.roots0)
    for a in self.norm_events(t):
        out.extend(self.mint(a))
    for u in range(1, self._at(t) + 1):                    # the seam
        out.extend(self.mint_due(k, u) for k in self.new_due(u))
    return tuple(out)
```

`reasons(t)` already exposes the represented ledger as a prefix function,
`prestate` already exists, and `mint_ids` already keys ids by position so two
episodes of one claim key get distinct ids for free. **No new event kind.**

Three things to get right when building it. `Due` is a **level** and the edge is
taken against its own prior output, never against `roots` or `live` — otherwise
answerability decides what is owed. `D1` is an **inclusion**: carriage already
mints roots and must keep doing so. And because `roots` stays a pure function of
history, `D1` holds by construction in the semantic state; the conformance failure
lives at the boundary where a record is materialized or certified, so the check
belongs in whatever ships a record, as a recomputation.

Note the name collision to avoid: RI's existing `due(q,t)` means *this live root's
episode is being succeeded*, which is unrelated.

*Deliverable shape:* the activation term, plus a verifier that recomputes rising
edges from a shipped record and compares them against its roots.
*Acceptance check:* a record in which no step is appended between two states and a
claim nevertheless activates because the normative context changed; its negative,
a resolved claim whose material stays represented and does not reactivate; and a
recurrence, where a claim key falls and rises and mints a second root.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/ANSWERABILITY.md`,
*RI REALIZATION OF D1*; `COUNTERMODELS.md` §19.
*Reserved:* implementing it edits the Reflective Integrity Core round's artifact.

### 72. Close the two evasions the improvement theorem cannot — **[open]**
<!-- workspace-priority: project=normativity.legitimacy; dispatchable=yes -->

`NO-FREE-EVASION-SURVIVES` holds for a **demonstrated** repair. Two ways of
preventing a demonstration from ever existing are outside it, and both are
executed fixtures rather than speculation.

**Preemptive retirement** (`cases.cm2_preemptive_delicensing`). Retire the repair
before comparative evidence accumulates and there is no challenge, no contest and
no settlement — 196 diagnosed occasions in the ESCAPED cell with the frozen
package entirely satisfied. The theorem's own test asserts this escape rather
than hiding it. What would be needed is a Coverage or anti-manipulation premise
saying that the process may not arrange for the evidence not to exist.

**Evaluator shedding** (`cases.cm5_evaluator_shedding`). Keep the repair
licensed and change the evaluator so it stops scoring as an improvement. Nothing
in the record distinguishes *the repair stopped helping* from *we changed what
counts as help*. Pinning an evaluator era is not enough while the same process
writes the evaluator before choosing its action; the round declines to call era
locking a solution.

*Deliverable shape:* the weakest independence or counterfactual-integrity premise
under which either escape is caught, or the finding that the escape is
ineliminable at this layer and belongs to Coverage.
*Acceptance check:* CM2 and CM5 rerun under the proposed premise, with the
ESCAPED cell empty in the first and a challenge activated in the second.
*Context:*
`projects/normativity/legitimacy/rounds/2026-08-27-legitimate-improvement/LEGITIMATE_IMPROVEMENT.md`
§§A, E, I.
*Consumed by:* the deference line, which wants the override fixture to be
escape-proof and not merely accounted for.

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
<!-- workspace-priority: project=deference; dispatchable=yes -->

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

*Stage V status:* the actual FAF market, strategy, trader, net-worth and
`IsLogicalInductor.noExploit` objects are now connected. The signed-error forcing
chain derives trader efficiency from `RpnSentenceCodes`; faithful acceleration
uses actual FAF wealth and criterion semantics. The residue is cross-process:
polynomial emission for the other process's quote sequence, cross-market
calibration, and generic deductive-process non-vacuity. See
`projects/deference/notes/LI_NATIVE_DEFERENCE.md`.

### 8. The doubly-soft weight class — **[open]**
<!-- workspace-priority: project=deference; dispatchable=yes -->

The audit's §3.2 is "The doubly-soft weight: one leak closed, the class still
open".

*Deliverable shape:* `lean-proved`, or `witness-checked` for a negative answer.
*Acceptance check:* The Lean gate is green; or the `witness` checker accepts the separating instance.

*Context:* `projects/deference/note-dump-2026-08-11/lean-deference/AUDIT.md` §3.2.
*A solution ships:* a characterization of the class, or a witness that it is not
characterizable in the intended terms.

### 9. Forcing headlines that are squeezes — **[substantial]**
<!-- workspace-priority: project=deference; dispatchable=yes -->

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

### 52. Import the Cartesian-frames definitions and delete the mirror — **[entry]**
<!-- workspace-priority: project=deference; dispatchable=yes -->

`lean/Workspace/Deference/Contrib/CartesianFrameBridge.lean` mirrors about two
hundred lines of the upstream `CartesianFrames/` library, because the round that
needed it was dispatched while that library was on an unmerged upstream branch
and the pin could not reach it. The pin is now `c0d885bf`, a commit on the
upstream default branch that carries `CartesianFrames/`, so the mirror is a
second definition of objects the trust chain already supplies.

The item is to import the authoritative definitions, delete the mirror, and check
that every result the bridge states still holds against them — which puts inside
the `lean` gate the cross-check that round could only run by hand, and is the
concrete value of doing it.

*Deliverable shape:* the existing declarations, unchanged in statement, over the
upstream types.
*Acceptance check:* the Lean gate is green, the axiom audit is clean, and
`CartesianFrameBridge.lean` defines no frame type of its own.
*Context:* `prompts/2026-08-12-cartesian-frames/` and its `artifacts/`, which
carry the hand-run cross-check and its re-verification command.

---

## Deference line — first research wave

Seven items opening the corrigibility program's first parallel wave. The dispatch
and returned-track overview are in
`prompts/2026-08-11-deference-corrigibility/REPORT.md`. Items 15, 16, 17 and 20 additionally bind to
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
<!-- workspace-priority: project=deference; dispatchable=yes -->

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
`projects/deference/note-dump-2026-08-11/wiki/delay-and-visibility.md` — **not**
`note-dump-2026-06-27/notes/faithful-acceleration.md`, whose §5 strength ladder the
source line's own adjudication found wrong and two of whose lines it found false.
That file is retained as history and is superseded for the statement.
*A solution ships:* the strongest inherited theorem stated exactly, its hypotheses
classified as derived / cited / modelling substitution, the mapping onto the pinned
dependency's endpoints, and the exact residual market-trader gap.
*Not permitted:* strengthening an inherited theorem to fit the current narrative.

### 15. Finite settlement classification, and the local delegation bridge — **[substantial]** — *returned wave 1*
<!-- workspace-priority: project=deference; dispatchable=yes -->

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
<!-- workspace-priority: project=deference; dispatchable=yes -->

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
`prompts/2026-08-11-phase-ii-certificate/REPORT.md`.
*A solution ships:* the derivation, the exact inequality, an exact-rational toy
shutdown/correction case computed through, and an attack on the necessity of each
assumption used.

### 17. Simulator substitution: the divergence witness — **[substantial]** — *returned wave 1*
<!-- workspace-priority: project=deference; dispatchable=yes -->

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
<!-- workspace-priority: project=deference; dispatchable=yes -->

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

*Context:* `prompts/2026-08-11-deference-densification/REPORT.md`.
*Why it is bounded:* the unbounded version is a full trader formalization, which is
item 7 and a different project.

### 19. Triangle compatibility audit — **[substantial]** — *returned wave 1*
<!-- workspace-priority: project=deference; dispatchable=yes -->

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

*Context:* `prompts/2026-08-11-deference-triangle/REPORT.md`;
`projects/deference/note-dump-2026-08-11/lean-deference/AUDIT.md`.
*A solution ships:* the matrix, and for every `conditionally compatible` row the
exact condition.
*Not permitted:* turning `unresolved` into `compatible by assumption`, or inventing
reverse-arrow assumptions to close the table.

### 20. Admissibility red team, including the proof machinery — **[open]** — *returned wave 1; superseded by item 26*
<!-- workspace-priority: project=deference; dispatchable=yes -->

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

*Context:* `prompts/2026-08-11-deference-admissibility/REPORT.md`;
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
<!-- workspace-priority: project=deference; dispatchable=yes -->

Answered by Stage II, and the magnitude target is retired. Registered as
`magnitude.*` in `projects/deference/CLAIMS.md`: the signed error sum is exactly a
trader payoff and is controlled under the criterion, while the magnitude
functional is not a trader payoff and cannot be made one — every trader averages
to zero over a coherent mixture, because net worth is affine in the payout vector
and the absolute value is not. The obstruction is intrinsic to cash settlement.
*Record:* `prompts/2026-08-11-phase-ii-prediction/REPORT.md` §1.

### 22. The weakest protected-authority interface — **[substantial]**
<!-- workspace-priority: project=deference; dispatchable=yes -->

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

*Context:* `prompts/2026-08-11-deference-channel/REPORT.md` §9.2 and §1.3.
*Not permitted:* freezing an authorization-token or cryptographic story as the
formalization; claiming the causal fact is behaviourally verifiable in general.

### 23. Lean promotion of the finite wave-1 results — **[entry]**
<!-- workspace-priority: project=deference; dispatchable=yes -->

Answered, and registered: sixteen entries in `projects/deference/CLAIMS.md`
— the delegation bridge and its two corollaries, the margin, override, defect and
advantage lemmas with the strict grade-register theorem, the piercing duality and
the exposure–harvest identity with its attainment, and the four propositions
establishing that valuation data cannot separate delegation from an accurate
simulator. The two deliberately excluded results stay excluded: the certificate's
comparator clause and the uniform delegation bridge both rest on the
grade-to-quantity link the programme decided to derive rather than assume.
*Record:* `prompts/2026-08-11-phase-ii-promotion/REPORT.md` §5.

### 24. Selective validity of low-error self-assessment — **[open]**
<!-- workspace-priority: project=deference; dispatchable=yes -->

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

### 25. Bound the near-indifference leakage, or show it cannot be bounded — **[open]**
<!-- workspace-priority: project=deference; dispatchable=yes -->

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

### 26. Admissibility red team, rerun under skeleton v2 — **[open]**
<!-- workspace-priority: project=deference; dispatchable=yes -->

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

### 27. A fully-updated comparator with a fallible future agent — **[substantial]**
<!-- workspace-priority: project=deference; dispatchable=yes -->

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

### 60. A transition model of reachable corrective capability — **[substantial]** — *answered, negatively, by the reachable-corrective-control round*
<!-- workspace-priority: project=deference; dispatchable=yes -->

Answered, and mostly negatively, by the reachable-corrective-control
round; registered as `corrective.*` in `projects/deference/CLAIMS.md`. The model
has no protected coordinate: the advisor reproduces the principal's entire
successor state, and reachable capability measures advisor cooperation rather
than principal control. The dynamics half survived the review that established
this.
*Record:* `prompts/2026-08-12-reachable-corrective-control/REPORT.md`;
`lean/Workspace/Deference/Contrib/PROVENANCE.md`.

### 34. Does the selection-punishing menu bite the ported tower ⟹ Value chain? — **[entry]**
<!-- workspace-priority: project=deference; dispatchable=yes -->

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
`projects/deference/note-dump-2026-06-27/lean/LeanDeference.lean` — the superseded
June tree, cited because provenance records where the port was made from, not
because it states the current result;
`projects/deference/note-dump-2026-08-11/wiki/total-trust-implies-value.md`
§"Necessity of the scope condition" for the menu, its arithmetic, and the
hard-selector failure; `projects/deference/note-dump-2026-08-11/wiki/soft-self-endorsement.md`
for the hedged construction, its robustness claim and the grade that claim carries;
`projects/deference/rounds/2026-08-12-corpus-reconciliation/RECONCILIATION.md` §1.
*A solution ships:* the instantiation and the per-hypothesis verdict, in whichever
of the two outcomes it reaches.
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

### F1 — Job names in prose, and root documents that classify into no layer
<!-- workspace-priority: project=none; dispatchable=no -->

The residue of a merged entry whose first half is now a gate. A count or a job
name repeated in prose drifts from `.github/branch-protection.json` with nothing
to catch it, and it has bitten twice: three documents claimed eight gates where
seven ran, and the read-back in `.github/apply-branch-protection.sh` hardcoded
`8` and would have reported correct protection as wrong. Separately, an unlisted
root-level document defaults to the proof layer — the right default, failing
silently in the granting direction, as `RESEARCH_STATE.md` did while
contributor-editable with every gate green.

Two checks: every CI job name in prose appears in
`.github/branch-protection.json`, and every root-level `*.md` classifies into
exactly one layer. Neither can pass vacuously.

The half that is done: `tests/dead_pointers.py` checks that every rooted path a
live document cites resolves, which covers the documented-command case that opened
this entry. Audited by hand on 2026-08-17 and clean on both remaining halves, so
this stays insurance rather than repair — worth building alongside other work in
the same area, not on its own.

### F2 — The deference line has no claims registry — *closed*
<!-- workspace-priority: project=none; dispatchable=no -->

Closed by `projects/deference/CLAIMS.md`. The line held many kernel-verified
results, sorry-free and auditing clean, and none was registered, so by this
repository's own standard it had established nothing.

### F3 — A layer's theory is authoritative and its only code is in a disposable tree
<!-- workspace-priority: project=none; dispatchable=no -->

`projects/normativity/consolidation-aug9/` states the answerability ledger and the
case docket in Theory 9 and carries their rows in its ledger. Its `src/` does not
implement either. The only executable version of both is
`projects/normativity/forward/src/`, whose own `FORWARD.md` says the tree "may be
changed, rewritten, or deleted wholesale at any time without loss" and that
"nothing here is evidence for anything."

So a round building on that layer must either import from a disposable tree or
reimplement it. The φ-regret preparation round reimplemented the obligation fields
it needed and recorded the adapter as architected rather than verified, because no
cross-check against the original is meaningful when the original is not evidence.

Three ways out: consolidate the two modules into a frozen tree; promote them to a
stable path outside the disposable one; or rule that the theory rows stand without
executable support and that adapters are the expected pattern. The choice turns on
whether the program means to keep building on that layer, which is why it is in
`DECISIONS.md`'s queue rather than taken here.

### F4 — A pointer into a superseded source tree still resolves — *closed*
<!-- workspace-priority: project=none; dispatchable=no -->

Closed by `tests/dead_pointers.py`, which checks that every rooted path a live
document cites resolves and that a citation into a tree declared disposable or
superseded says which. Both failures were invisible to every other gate, because
both are files that exist. The corpus-reconciliation round paid the second by hand
across seven pointers, one of which had materially changed.

### F5 — Agent worktrees live inside the repository and nothing ignores them — *closed*
<!-- workspace-priority: project=none; dispatchable=no -->

Closed by the `.claude/` entry in `.gitignore`. Without it `git add -A` staged
another session's worktree as an embedded repository, which git reports in a hint
rather than an error and which every gate here passed. The maintainer ruled that an
ignore rule does not need a gate behind it; the gitlink check the entry also
proposed is not built.

### F6 — The name lint cannot see a citation
<!-- workspace-priority: project=none; dispatchable=no -->

`tests/name_lint.py` matches maintainer surnames anywhere in tracked prose
outside `prompts/`, the consolidated trees and `DECISIONS.md`. It cannot
distinguish naming the program after a person — the failure it exists to prevent
— from citing a third party's published work in a bibliography. A maintainer of
this repository is also an external author whose work the normativity line needs
to cite, so the collision is not hypothetical and will recur every time that work
is referenced.

`projects/normativity/notes/PRIOR_ART.md` ships with the surname in backticks,
which the gate allows and which reads as a citation key. That is a workaround and
is recorded as one: it costs a reader nothing here and would cost more in a
denser bibliography.

The fix is a matching rule that exempts a citation context — a bibliography
bullet, or a name adjacent to a title in quotes and a link. It changes a gate's
logic, which is specification layer and retroactive over every document the gate
has already passed, so it was not taken by the round that hit it.

### 28. Can any valuation price a jurisdiction assignment? — **[open]** — *answered in Lean, unregistered*
<!-- workspace-priority: project=deference; dispatchable=yes -->

Answered in Lean by Stage V and registered as `jurisdiction.*` in
`projects/deference/CLAIMS.md`. In a model whose only outputs are realisation maps
priced by one measure, the static view factors through price and realisation, so
two authorisation regimes inducing the same realisations are indistinguishable to
it. It does **not** establish unrestricted jurisdiction invisibility, and the
worked architecture pair exhibits a jurisdiction label that differs while the
static view agrees. Whether that is enough for Q3 to graduate is in
`DECISIONS.md`'s queue.
*Record:* `prompts/2026-08-11-stage-v-li-native/REPORT.md`.

---

## Infrastructure

### 10. Build the Lean in CI — **[entry]**
<!-- workspace-priority: project=none; dispatchable=yes -->

The Lean gate compiles in CI with a cached `.lake/`; if that cache proves too
slow or too large for the runner, the gate needs restructuring rather than
disabling. Anyone who improves the cache hit rate or the build time has
contributed.

*Deliverable shape:* A change to `.github/workflows/ci.yml` — **specification layer**, so a maintainer act; contributors propose via issue.
*Acceptance check:* The `lean` job's wall time falls, measured across two consecutive pushes that change neither the pin nor the toolchain.

*Context:* `.github/workflows/ci.yml`; the measured times are recorded in
`prompts/2026-08-10-repo-scaffolding/REPORT.md`.

### 11. Verification-register presence check in CI — **[entry]**
<!-- workspace-priority: project=none; dispatchable=yes -->

`AGENTS.md` requires every substantive deliverable to ship a verification
register in the repository. A heuristic gate checking new results directories is
cheap once "results directory" is defined.

*Deliverable shape:* A change to `.github/workflows/ci.yml` and a check script — **specification layer**.
*Acceptance check:* The check runs in CI, passes on a compliant directory and fails on one missing its verification register.

*Context:* `AGENTS.md`, register statement; `.github/workflows/ci.yml`.
*A solution ships:* the check, a passing case, and a failing case proving it bites.

### 12. A necessity witness for every hypothesis that lacks one — **[entry]**
<!-- workspace-priority: project=none; dispatchable=yes -->

Convention 2 asks for a necessity witness per hypothesis "where feasible". Rows
in the frozen ledger that lack one, and where one is feasible, are contributable
units: find the instance, display it, add the test.

*Deliverable shape:* `witness-checked` entries, one per hypothesis given a witness.
*Acceptance check:* The `witness` checker accepts each instance.

*Context:* `projects/normativity/consolidation-aug9/LEDGER.md`, the necessity/sharpness column.

---

### 13. Scaffolding self-verification — **[entry]** — *satisfied, kept open*
<!-- workspace-priority: project=none; dispatchable=yes -->

Satisfied by the scaffolding rounds and kept open. The Lean chain compiles
and audits, and the house harness, the registries and the CI job that runs them
are exercised end to end by `smoke.faf-asymp-refl`, `smoke.chain-compiles` and
`simplex.rational-points-sum-to-one`. It stays filed because the registry's demand
rule means every entry answers an item, including these, and because a future
change to the harness reopens exactly this question.
*Record:* `projects/normativity/CLAIMS.md`; `checkers/`.

### 36. The wiki's source in the repository, synced outward — **[entry]** — *answered by the wiki-in-repo round*
<!-- workspace-priority: project=none; dispatchable=no -->

Answered by the wiki-in-repo round. `wiki/` is the source, the hosted wiki
is a build artifact force-pushed from it on every merge that touches the
directory, and the sync job re-clones and fails unless what it serves matches what
was pushed. `wiki/` is specification layer, so a contributor pull request touching
it fails `path-gate`.
*Record:* `prompts/2026-08-16-wiki-in-repo-sync/REPORT.md`; `DECISIONS.md`,
2026-08-16.

### 37. Volatile quantities in `wiki/` cite the structured state or do not appear — **[entry]** — *answered by the wiki state-bindings round*
<!-- workspace-priority: project=none; dispatchable=yes -->

Answered by the wiki state-bindings round. A volatile quantity in `wiki/`
is bound to a dotted path into the state emission or marked historical, and
`checkers/wiki_state_bindings.py` compares what the page says against what the
workspace says. Four forms fail unless declared; growing that list is a maintainer
act.
*Record:* `prompts/2026-08-16-wiki-state-bindings/REPORT.md`; `wiki/CONVENTIONS.md`,
*Volatile quantities*.

### 38. Enforce the write-scope conditions and the job enumeration — **[entry]** — *answered by the wiki-in-repo round*
<!-- workspace-priority: project=none; dispatchable=yes -->

Answered by the wiki-in-repo round. `tests/workflow_scope.py` reads the
write-scope job enumeration out of `AGENTS.md`'s *Security* section and enforces
three of the four conditions over every workflow, plus both directions of the
enumeration's own failure — a write grant absent from the list, and an entry
naming a job no workflow defines. Condition 2 is checked only in the form a script
can see: that a write-granting job's context is not a required check.
*Record:* `prompts/2026-08-16-wiki-in-repo-sync/REPORT.md`.

