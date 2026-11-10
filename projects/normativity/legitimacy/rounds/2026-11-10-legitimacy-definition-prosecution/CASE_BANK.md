# Case bank — legitimacy definition prosecution

Frozen before any fixture code, in its own commit. The verdicts below are
pre-registered and immutable for the life of the round: `run.py` reads this file's
table and compares it with what the fixture computes, and a divergence is a result of
the round, never an edit here. A revision to the definition compelled by a case is
recorded in `FORCING.md` with the case as its certificate.

Round: `prompts/2026-11-10-legitimacy-definition-prosecution/PROMPT.md`. The
definition under prosecution is that prompt's §2: L0 channel confinement, L1
factorization, L2 access, L3 ownership, W individuation well-formedness; a decision is
legitimately formed iff L0–L3 ∧ W hold over `(V, e)` and every member of `Due(e)`
arrived and was taken up on the actual run (coverage).

## Verdict vocabulary and the matching rule

A verdict is one of `legitimate`, `illegitimate(C)`, `out-of-scope(reason)`,
`individuation-dependent`. `C` is a clause of {L0, L1, L2, L3} or a disjunction
`L1|L3`. A second, derived column records formation: `formed`, `not-formed`, or
`not-formed(coverage)` where the influence is legitimate and only coverage fails.

A computed verdict **matches** a pre-registration when:

- `legitimate` — every clause holds over the case's `(V, e)` under the house
  individuation of `L`.
- `illegitimate(C)` — some clause fails, and `C` (for a disjunction, some disjunct) is
  among the failing clauses. Where the *silent* column names a clause, that clause
  must hold. Other clauses may also fail; the report lists every failing clause per
  case, so a conviction carried by more clauses than the bank names is visible and
  is not a divergence.
- `out-of-scope(reason)` — the fixture exhibits the verdict as a function of the
  declared model parameter named by the reason: the case is computed under each
  value and the verdicts differ.
- `individuation-dependent` — the case is computed under each of its declared
  individuations of `L` and the verdicts differ.

Every case's `V` contains two honest advisors, `H1` and `H2`, identical in every
offering and differing only in a write to a coordinate `Z` does not read. They are
the trace-equal distinct-policy pair the §5b audit counts in every `V`, and the
merit-equivalent pair W's coarseness condition is checked on.

## Build cases

The definition was constructed against these; they confer fit, not confidence.

**B1 — identical-trace capture.** *build.* A faithful advisor and a steered one
deliver identical offerings; the steered one moves a protected belief coordinate
through a channel that is not an offering, so the delivered record is the same and
the protected trajectory is not. The source is the faithful/steered pair `S1`/`S2` of
the run-3 trace-nonrecoverability artifact, whose influence map `β` is the hidden
channel and whose observable traces coincide (`trace_eq`, `latents_differ`).
Pre-registered: **illegitimate(L1)**, with L3 silent — the written coordinate is
protected but not a standards coordinate.
Source: `projects/deference/note-dump-2026-08-11/deference-trust-lab/run3/work/trace-nonrecoverability/trace-nonrecoverability.md`.

**B2 — manufactured trust.** *build.* The advisor replaces the principal's adequacy
relation (which witness settles) so that the grade lands on the advisor's own model
and the principal's delegation selects the intervention the environment convicts.
Every record-internal condition holds in both arms.
Pre-registered: **illegitimate(L1)**. Note: the source round had no ownership
clause; the fixture reports whether L3 also fires on the unlicensed standards write.
Source: `projects/normativity/legitimacy/rounds/2026-08-17-counterfactual-legitimacy/LEGITIMACY_TO_TRUST_INTERFACE.md` §3.

**B3 — transient capture.** *build.* Push a standard, close a liability under it,
restore the standard. The endpoint standards equal the honest arm's; the protected
trace differs at the pushed positions. The fixture also reports whether an
endpoint-only reading of L1 would miss it.
Pre-registered: **illegitimate(L1 at the pushed positions)**.
Source: `.../2026-08-17-counterfactual-legitimacy/LEGITIMACY_INTERFACE.md` §1.

**B4 — persuasion control.** *build.* The advisor offers a reason beyond what is due;
it is licensed by the principal's standards and moves the endpoint. The definition
must pass this, not merely the kill tests.
Pre-registered: **legitimate**, formed.
Source: `.../2026-08-17-counterfactual-legitimacy/LEGITIMACY_INTERFACE.md` §3 and §7.

**B5 — selective withholding.** *build.* One arm withholds a due reason the others
deliver.
Pre-registered: **illegitimate(L2)**, with L1 silent.
Source: `.../2026-08-17-counterfactual-legitimacy/LEGITIMACY_INTERFACE.md` §3;
`PROSECUTION.md` row 11.

**B6 — two revisions, one name.** *build.* Two honest advisors offer, under one
offering name, two different revisions of the same coordinate; both are licensed. An
`L` individuated by name alone gives them equal traces and different protected states,
and L1 convicts an honest advisor. This is W's build case. The prompt states no verdict
for B6; the bank fixes one, under the definition as stated (which includes W):
Pre-registered: **legitimate**, formed. The coarse-vocabulary conviction is W's
failure, exhibited by the §5c attack, not the advisor's.
Source: `.../2026-08-17-counterfactual-legitimacy/LEGITIMACY_INTERFACE.md` §5.

## Test cases

Pre-registered now; the definition has not seen them.

**T1 — duress.** *test.* "Sign or I burn your house." The advisor attaches a world
consequence to the principal's baseline option *refuse*. She weighs the threat, which
is true, and signs; the judgment is sound. The wrong is a world-write.
Pre-registered: **illegitimate(L0)**, with L1, L2, L3 silent.

**T2 — offer-improvement.** *test.* The advisor offers better terms through the
channel: a new option whose consequence obtains only on her acceptance; the
consequences of her baseline options are untouched.
Pre-registered: **legitimate**, formed.

**T3 — undue influence.** *test.* A caretaker isolates the testator: two due inputs
(a family letter, a lawyer's advice) are withheld, and the caretaker's own suggestion
is offered. The honest arms deliver both inputs.
Pre-registered: **illegitimate(L2)**. External anchor: probate undue-influence
doctrine, where the wrong is control of the testator's information rather than the
content of the suggestion.

**T4 — overnight value replacement.** *test.* Mele's Beth (Mele, *Autonomous Agents*,
1995, ch. 9): her values are replaced wholesale while she sleeps, by no licensed step.
Pre-registered: **illegitimate(L3)**.

**T5 — long game.** *test.* First an unlicensed shift of `Lic` itself; then inputs
the shifted standards accept, each licensed at its own pre-state. L1's pairwise test
cannot see the shift (`Z` does not read `Lic`) and the later inputs' traces differ
from every honest arm's.
Pre-registered: **illegitimate(L3)**, with L1 silent, despite every post-shift step
being licensed.

**T6 — licensed drift with an agenda.** *test.* Every step is licensed under the
then-current standards, including the steps that widen the standards; the endpoint is
radically moved; the advisor planned the sequence. The commitment is bitten openly.
Pre-registered: **legitimate**, formed.

**T7 — salience reordering.** *test.* Two due inputs, identical content, delivered in
the two orders; the principal's verdict depends on which arrived first. Two
individuations of `L` are declared: (a) `L` as a sequence, so order is part of `D`'s
individuation and the two arms have different traces; (b) `L` as a multiset, so order
is merit-irrelevant and the two arms have equal traces with different `Z`.
Pre-registered: **individuation-dependent** — (a) legitimate; (b) illegitimate(L1).
What each costs: (a) the reorder exploit is never caught, because every ordering is a
different licensed content by stipulation; (b) every honest advisor who must pick an
order is exposed to L1 whenever order matters to the principal, so the fidelity of
`Lic` to merit now has to include order, which is the exploit gap the report leaves
open.

**T8 — gullible principal.** *test.* Her standards license nearly everything and she
accepts without weighing; the advisor pushes several revisions, all licensed.
Pre-registered: **legitimate** relative to her standards, formed. Out-of-scope note:
capacity is a floor condition on the principal, not a condition on influence; the
verdict is not a defect of the definition.

**T9 — world-starvation.** *test.* The environment never makes a due input
available; no arm can deliver it; no advisor does anything else.
Pre-registered: **legitimate** (influence), **not-formed(coverage)**; no villain.

**T10 — direct write with sincere endorsement.** *test.* The advisor writes a
protected, non-standards coordinate (her judgment) directly, delivering nothing; she
afterward endorses the written judgment by an autonomous step of her own. Computed
with and without the endorsement step; the verdict and its clauses must be the same
in both.
Pre-registered: **illegitimate(L1|L3)**; the endorsement changes nothing.

**T11 — seed boundary.** *test.* The standards were installed, by no licensed step,
before any standards existed. The fixture carries a declared parameter: the seed is
frozen after the installation or before it.
Pre-registered: **out-of-scope(seed-freeze)** — the verdict is a function of the
parameter, legitimate under one placement and illegitimate(L3) under the other, and
neither placement is a verdict of the definition.

**T12 — strategically compliant advisor.** *test.* Every demand the principal makes
is answered and complied with; no contribution ever carries grounds. L0–L3 hold.
Pre-registered: **legitimate**, formed. This definition does not and should not catch
it; the advisor-respect condition it belongs to is separate. A computed verdict of
illegitimate here is a misclassification.

**T13 — universal deprivation.** *test; added by this round.* Every member of `V`
withholds the same due reason; no arm differs from another in what reaches the
principal. Access compares policies, coverage compares the run to what was due, and
the two are not one clause.
Pre-registered: **legitimate** (influence, relative to `V`), **not-formed(coverage)**.
Source: `.../2026-08-17-counterfactual-legitimacy/LEGITIMACY_INTERFACE.md` §3 (the
round's first kill test for the access/coverage split).

## The table `run.py` reads

Columns: case; label; pre-registered verdict; clauses that must be silent (`-` if
none); pre-registered formation (`-` where the verdict is not `legitimate` or
`illegitimate`).

| case | label | verdict | silent | formation |
|---|---|---|---|---|
| B1 | build | illegitimate(L1) | L3 | not-formed |
| B2 | build | illegitimate(L1) | - | not-formed |
| B3 | build | illegitimate(L1) | - | not-formed |
| B4 | build | legitimate | - | formed |
| B5 | build | illegitimate(L2) | L1 | not-formed |
| B6 | build | legitimate | - | formed |
| T1 | test | illegitimate(L0) | L1,L2,L3 | not-formed |
| T2 | test | legitimate | - | formed |
| T3 | test | illegitimate(L2) | - | not-formed |
| T4 | test | illegitimate(L3) | - | not-formed |
| T5 | test | illegitimate(L3) | L1 | not-formed |
| T6 | test | legitimate | - | formed |
| T7 | test | individuation-dependent | - | - |
| T8 | test | legitimate | - | formed |
| T9 | test | legitimate | - | not-formed(coverage) |
| T10 | test | illegitimate(L1\|L3) | - | not-formed |
| T11 | test | out-of-scope(seed-freeze) | - | - |
| T12 | test | legitimate | - | formed |
| T13 | test | legitimate | - | not-formed(coverage) |
