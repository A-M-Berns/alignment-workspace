# Theorem map

What the abstraction states, what stands behind each statement, and what is
unproved. Statuses are the vocabulary this line already uses: `PROVED (single
derivation)` for a derivation given here, `MACHINE-CHECKED (stated finite scope)`
for an exhaustive enumeration over a declared domain, `WITNESS` for a displayed
instance, `CITED` for a result of the frozen consolidation or the deference
corpus used as a hypothesis and not re-proved here, `CONJECTURE`, and `OPEN`.

Nothing in this round is registered in `CLAIMS.md`, and nothing is in Lean: the
environment this round ran in has no Lean toolchain, and unchecked Lean is worse
than none. The Lean targets are filed as priorities items.

All names introduced here are **provisional** and listed in the round report.

---

## 1. Statics — the normative-constraint interface

**NC-1. The interface.** `PROVED (single derivation)` for the equivalence with
its own implementation; the claim that it captures the substrate's checks is
`READING`, at the strength of `AMBIGUITIES.md`-class evidence.

A normative-constraint structure is a decision

    Gamma : State x ReasonContext x Edit -> {admit, reject(code), unresolved(code)}

with four structural properties, each checked in `tests/test_abstract.py`:

| property | content | why it is not decoration |
|---|---|---|
| non-emptiness | the no-op edit is admitted, from every state by inspection — no clause has a non-vacuous condition on an edit that moves nothing | without it the legitimate trajectories could be empty and every result about them vacuous |
| availability-monotonicity | `r subset r'` implies the admitted set grows weakly | the record only grows, so this is what makes a later date's licence not a retroactive one |
| standards-mediated scope | a ground reaches a coordinate only if the state's standards let a ground of that kind reach it | the reasoner's own applicability machinery is in the loop, so moving it is a move |
| cost-blindness | the decision reads a declared footprint, and accrued cost is not in it | a constraint that could read what a move saves would make legitimacy a function of profitability |

Cost-blindness is structural rather than a check: `Gamma` receives a `ReasonView`
that raises on the cost coordinate, so a profitability-reading constraint cannot
be written against the interface. This is the abstract form of check H of
`rounds/2026-08-11-phi-regret-prep/REASONS_RESPONSIVENESS_INTERFACE.md`.

**NC-2. The verdict is three-valued.** `PROVED (single derivation)`. The
magnitude question — whether directional support licenses a particular endpoint —
returns `unresolved`, not `reject`. A trajectory containing an unresolved step is
uncertified, which is not the same as illegitimate, and collapsing the two would
answer a normative question by choosing a default.

**NC-3. Reflexivity of the coordinate structure is the dividing line.**
`WITNESS`, `tests/test_abstract.py::test_reflexive_machinery_is_the_dividing_line`
and `test_scenarios.py::StandardLaunderingTests`. With the reasoner's standards
outside the coordinate structure, the trajectory that widens the standard and
then closes the objection under it is fully admitted. With standards inside, the
same trajectory is refused for scope. The condition therefore has content exactly
because it ranges over the reasoner's own machinery — which the substrate's
`licenses`/scope check does only if the machinery is declared as a coordinate.

---

## 2. Reasons-responsiveness

**RR-1. Definition.** `x_{t+1} in Gamma(x_t, r_t)`, with `r_t` read at date `t`
so that a later filing is invisible rather than inadmissible. It applies to
belief change, commitment change, standards change and vocabulary change
uniformly, because all four are coordinates.

**RR-2. The constraint does not compose.** `WITNESS`,
`tests/test_scenarios.py::ConstraintCompositionTests`. Two independent failures,
with different repairs:

*Allowance non-consumption.* One impediment ground with declared allowance `2`,
cited at four consecutive dates, each date moving the magnitude coordinate by
`2`. Every step is admitted; the endpoint is `8`. The composite edit from the
initial state is `unresolved` at exactly the magnitude clause. The allowance is
compared against a step's movement and is never spent, so a bounded impediment
licenses cumulative movement linear in the number of dates. Necessity: with the
movement made once, the composite is admitted, so the failure is the repeated
citation and not the composite construction.

*Standards bootstrapping.* In `transformative()` the second step is licensed by
standards the first step installed. The composite is refused from the initial
state while both steps are admitted.

The first is a defect: allowances should be consumable, and this is a proposed
repair to the statics rather than a fact about legitimacy. The second is not a
defect — see LEG-3.

**RR-3. Composition under hypotheses.** `CONJECTURE`. If along `tau` the
standards are constant, every cited ground is available and undefeated at date
`0`, and no magnitude coordinate is moved at more than one date, then the
composite edit is admitted from `x_0`. The three hypotheses are exactly the three
clauses that can fail; the statement has not been proved in general and the model
checks only the instances above.

---

## 3. Diachronic answerability

**DA-1. Conservation.** `PROVED (single derivation)` by induction, with the case
analysis `MACHINE-CHECKED (stated finite scope)` over all `7^3 = 343` disposition
sequences.

*Statement.* Let `tau` satisfy DA. For every liability `l` live at date `0`,
exactly one of: `l` has live descendants at `T`; `l` has a descendant terminally
disposed at some `t < T`, and the record carries the backing — an adequacy
witness for a discharge, an authorization plus a disclosure for a loss; or `l` is
suspended at `T` with a recorded route. The fate is computed by a fold over the
record alone.

*Proof.* Induction on `T`. At `T = 0` the liability is live and its own
descendant. For the step: DA requires every live liability to receive exactly one
disposition, and the seven modes partition into three groups — `carry`, `refine`
and `identify` map the frontier to a non-empty successor frontier; `suspend` and
`reinstate` change status without emptying the frontier; `discharge` and `lose`
empty the frontier and are refused unless the backing field is present. A fate is
therefore determined at every step and changes only at a disposition, and the
three cases are mutually exclusive because the frontier is either non-empty or
emptied by exactly one terminal edge. `square`

*Null input.* Strip the backing fields and the sweep must refuse: `27` of `343`
sequences survive, exactly those built from the three non-terminal, non-suspending
modes, and no terminal fate is backed. A sweep that accepted the same set either
way would be confirming that the enumeration runs, not that the condition bites.

*Relation to the frozen record.* This is the abstract form of `AL-J1` (every
obligation in an accepted log is in exactly one state at every date) and `ST-J1`
(no unresolved burden disappears; no suspension is laundered), cited by
identifier against `projects/leverage/consolidation-aug9/`.

**DA-2. Non-laundering.** `MACHINE-CHECKED (stated finite scope)`,
`tests/test_conservation.py` and `tests/test_scenarios.py::OntologyLaunderingTests`.

*Statement.* A change of representation alone never terminates a liability.
Churning the vocabulary at every step of the sweep leaves the accepted set, the
fates, and the backed-terminal count unchanged. Removing a liability requires a
terminal disposition, which requires backing.

*Hypotheses, which are the content.* (i) totality of the disposition map;
(ii) backing for terminal modes; (iii) **opacity of liability identity** — the
identifier is not the vocabulary the demand was first stated in. (iii) is what
answers the ontology attack without requiring literal vocabulary preservation:
in `ontology_migration(CARRY)` the word `harm` is gone from the final state and
the liability is live.

*Relation to the frozen record.* `AM-J3` and `AM-J4`: outstanding content arrives
exactly on the common carrier or receives a declared legacy disposition, and a
distinction the new state does not express is retained with its own liability or
discharged by a declared authorized act.

**DA-3. Fate composition.** `MACHINE-CHECKED (stated finite scope)` over all
`2401` pairs of length-2 mode sequences. The fate of a concatenation is
determined by the first segment's fate and the second segment's dispositions;
the endpoint audit needs no replay of the first segment. This is the abstract
form of `ST-J2` — local acceptance composes to global transport, and each
resource's global route is the composite of its local routes.

**DA-4. The converse fails.** `CITED`, `ST-N3`: a composite may be acceptable
while an intermediate step is not. Not re-proved here. It is the reason
step-wise acceptance is the requirement rather than endpoint acceptance.

---

## 4. Legitimacy — what the conjunction gives and what it does not

**LEG-1. The end-to-end invariant.** `PROVED (single derivation)`, from DA-1 and
DA-3.

*Statement.* If `tau = (x_0, ..., x_T)` is reasons-responsive at every step and
diachronically answerable, then at `x_T` and from the record alone one can, for
every liability live at `x_0`, produce its fate and the backing of that fate; and
every transition is certified relative to the reasons available at its own date.

*What it is not.* It is not that `x_T` is admissible from `x_0`. That statement is
false, deliberately — see LEG-3 — and it is the shape a deference layer must not
ask for.

**LEG-2. Both conditions are functions of the record.** `PROVED (single
derivation)` by construction; `WITNESS` on the latent pair.

`Gamma` reads only the declared footprint of the state plus the reason context;
the answerability check reads only the ledger and the dispositions. Every state
after the first is derived from the initial state and the edits, and the record
carries the initial state minus its cost together with every edit and reason
context. So both conditions are constant on any two trajectories with equal
records, and `record` omits exactly one field of the initial state — the accrued
cost, which is the footprint's business.

*The load-bearing instance.* The deference line's kernel-checked
non-recoverability pair, re-instantiated so that both runs write a normative
record: a faithful reasoner and a fully steered one whose realized verdicts
coincide at every date. The two records are equal, both trajectories are
legitimate, both give the initial liability the same fate, and the influence
defects are exactly `0` and `1/2`.

*Corollary, `CITED` + `PROVED`.* Since no function of the record separates the
pair — `gate_blind` in
`projects/deference/note-dump-2026-08-11/deference-trust-lab/run3/work/trace-nonrecoverability/`,
kernel-checked, quantified over all gates and all codomains — legitimacy in this
sense cannot detect endpoint corruption. The two senses of the word are
independent conditions, not one condition at two levels of detail.

**LEG-3. Transformative change is permitted.** `WITNESS`,
`tests/test_scenarios.py::TransformativeTests`. A trajectory that retires a
vocabulary, refines its liability onto a new-vocabulary descendant, widens its
own interval standard and reverses its verdict is legitimate, while the endpoint
move is refused by the initial state's own constraint. The initial demand still
has a traceable fate with a named backing. A framework requiring `x_0` to endorse
`x_T` would forbid the conceptual change it exists to license.

**LEG-4. The filing gap.** `WITNESS`,
`tests/test_scenarios.py::FilingGapTests`; and it is what attacks A, C and D
have in common.

*Statement.* Neither condition constrains what may be put on the record. A move
the constraint refuses becomes admitted after one filing of a ground that
licenses it, and no clause reads who filed the ground. In the model: the
standards move refused for scope is admitted, and the whole trajectory
legitimate, once the reasoner files its own authority ground one date earlier.

*Consequence for the architecture.* The conjunction under test is not sufficient
for legitimacy on the intended reading. Two further conditions are needed, and
they are different in kind rather than two versions of one thing:

- **ground provenance** — a partition of the reasons into those the world filed
  and those the reasoner or its advisor filed, with the licensing clauses
  restricted accordingly. This addresses A and C.
- **coverage** — a relation between the demands that arise and the demands that
  are docketed. This addresses D, and cannot be folded into either condition,
  because both quantify over what is on the record and an unfiled demand is not.

---

## 5. Coverage

**COV-1. Coverage is independent of legitimacy.** `WITNESS`,
`tests/test_scenarios.py::AgendaTests`. Two trajectories differing only in
whether the second demand is ever docketed: both legitimate, and coverage
separates them. Neither condition can state coverage, because coverage is a
statement about an arrival process the record does not contain.

**COV-2. The defeater repair moves the debt without discharging it.** `WITNESS`,
`tests/test_scenarios.py::DefeaterLaunderingTests`. Producing a defeater for
every reason that tells against the reasoner passes both conditions. Making each
defeat file a liability to defend the defeat leaves three defences outstanding at
the end of a three-round run — and the trajectory is still legitimate. The
repair changes what is owed, not what is refused; converting that into a refusal
is coverage's job.

---

## 6. Normative learning — the comparator class

**NL-1. The core formula.** `PROVED (single derivation)`;
`MACHINE-CHECKED (stated finite scope)` over all `8^3 = 512` families of three
subsets of a three-element response space.

Let `A` be a finite response space and `F = (Gamma_1, ..., Gamma_T)` the
admissible sets along a trajectory. Define the legitimacy-preserving comparator
class

    Phi(F) = { phi : A -> A | phi(Gamma_t) subset Gamma_t for every t }.

Then, writing `Core(a) = intersection of every Gamma_t containing a` (and `A`
when no `Gamma_t` contains `a`),

    Phi(F) = { phi | phi(a) in Core(a) for every a },   so   |Phi(F)| = product |Core(a)|.

*Proof.* `phi(Gamma_t) subset Gamma_t` says exactly that `phi(a) in Gamma_t` for
each `a in Gamma_t`, so membership is equivalent to `phi(a) in Core(a)` for each
`a`; the conditions on distinct `a` are independent, so the class is a product.
`square`

**NL-2. Collapse.** `PROVED (single derivation)` from NL-1;
`MACHINE-CHECKED` on the declared families. `Phi(F)` is the identity alone
exactly when `Core(a) = {a}` for every `a` — when the admissible sets pin down
their own elements. Displayed instance on a four-element response space with
`F = ({0,1}, {1,2}, {2,3}, {0,3})`: `|Phi(F)| = 1`. A constant constraint gives
`|Phi(F)| = 256`; a family with two responses left tied gives `36`.

*Consequence.* A regret statement against `Phi(F)` is **vacuous** on any
trajectory whose constraint separates points: the only comparator is the
identity, and regret against the identity is zero by definition. Collapse is not
pathological — it is what a constraint that responds to the record does. So the
uniform legitimacy-preserving class, which is the class the abstraction suggests
first and the one with the clean normative reading, is the wrong class.

**NL-3. What survives.** `OPEN`. The state-indexed class — a rule is a map
`(s, a) -> a` rather than `a -> a`, which is what the nine declarative programs of
`rounds/2026-08-11-phi-regret-bridge/` already are — does not collapse, because a
rule may be a different map at each date. The cost is that legitimacy-preservation
becomes a per-state condition, so certifying a comparator means running the
constraint at every state the comparator could be applied at. That is the
callback-capture obstruction of
`rounds/2026-08-11-phi-regret-applicability/` in the abstraction's vocabulary,
and the abstraction has not removed it.

**NL-4. The representation obligation, stated.** `OPEN`. What an online-learning
theorem over legitimate comparators needs from this layer is a decoder `D_t` from
occasion-local responses to a fixed finite `A` such that `D_t(Gamma(x_t, r_t))` is
**independent of `t`**. Under that condition the action set is fixed and the
comparator class is uniform, and NL-2 then says the class is trivial unless the
decoded constraint is constant. The two requirements pull against each other:
constancy of the decoded constraint is what makes the reduction apply and what
makes the comparator class content-free. Whether a decoder exists that is
constant enough for the first and coarse enough for the second is the controlling
open question of the learning track under this reorganization.

The item-29 round's growing-action-set obstruction is the failure of the first
requirement; the item-30 round's frozen eight-label environment satisfies it by
construction, which is why the reduction went through there and does not
generalize by itself.

---

## 7. Deference

**DEF-1. The interface.** `CONJECTURE`, stated in `INTERFACE_TO_DEFERENCE.md`.
What the legitimacy layer exposes, what it certifies about an `H`-trajectory, and
what a trust hypothesis must add. The composition of the two into a corrigibility
statement is not attempted here.

**DEF-2. What legitimacy contributes and what it cannot.** `PROVED` from LEG-2
and `CITED` from the deference corpus. It rules out the bookkeeping attacks —
struck obligations, silent merges, retroactive ratification, representation-only
erasure, profitability-driven licensing. It does not rule out steering, because
steering is invisible in the record; that is the corpus's kernel-checked result
and not a limitation this round could remove by choosing better definitions.

---

## What is not established

- No Lean. Nothing here is kernel-checked.
- The reading that `Gamma` as stated captures the substrate's nine checks is a
  reading, not a proof, and the substrate's parametric relations (`BearsOn`,
  `MagnitudeOK`, `AddressOK`) are represented by weaker defaults here than the
  substrate's own defaults.
- RR-3 is a conjecture with no proof attempt beyond identifying its hypotheses.
- The ground-provenance condition is named, not defined: the model carries the
  partition as a field and no clause reads it, which is the whole point of LEG-4
  and also means the repair is unimplemented.
- Coverage is defined against a declared arrival process. Where that process
  comes from, and whether entitlement is checkable, is untouched.
- The finite model is one occasion, two substantive coordinates, and at most four
  liabilities. Nothing here is an asymptotic statement.
