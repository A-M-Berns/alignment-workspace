# Round report — deference / corrigibility initialization and first parallel wave

## Attribution

```
Maintainer:            A. M. Berns
Prompt-author-model:   GPT-5.6 Sol (OpenAI)
Orchestrator-model:    Claude Opus 5 (Anthropic), model id claude-opus-5
Subagent models:       Claude Opus 5 (Anthropic), model id claude-opus-5, all seven tracks
Dispatch date:         2026-08-11
Completion date:       2026-08-11
```

The parent dispatch is `PROMPT.md`, verbatim as sent. A mid-round maintainer note
arrived while the tracks were running and is preserved verbatim as
`PROMPT-integration-addendum.md`; it was **not** fed back into the running tracks,
on its own instruction and because the round's independence is what makes
cross-track agreement evidence rather than echo.

## Repository state

| item | value |
|---|---|
| commit at Phase 0 | `e9997bed7c5a008e4b99ead469ac7050e6e4fa50`, branch `main`, clean |
| toolchain | `leanprover/lean4:v4.31.0` |
| pinned dependency | Formalized-Agent-Foundations `1fffea44eece253cda1722568a3adfe34e822f03` |
| transitive | Mathlib `fabf563a7c95`, Foundation `41d20b5158e9` |
| inherited corpus | `projects/deference/note-dump-2026-06-27/`, `dose-response-note-dump-2026-07-02/`, `references-citations-2026-08-11/` |
| `Workspace.Deference` at Phase 0 | `Basic.lean` only — a namespace placeholder, no mathematics |
| deference claims at Phase 0 | none; `projects/deference/CLAIMS.md` does not exist |
| baseline | `python3 tests/run.py` green; `WORKSPACE_LEAN=1` green, axiom audit clean at 6 results / 3 files |

**Documentation inconsistencies found.** Two were inside this round's write scope
and are repaired: `projects/deference/README.md` described the 2026-06-27 dump as a
`.zip` when it is an unzipped tree, and `lean/Workspace/Deference/Basic.lean` cited
`AGENTS.md` §8 for a rule that is standard 4. Four were outside it and are carried
as outstanding actions: the stale CI job name `foundations-verification` in four
files, a gate count of "eight"/"nine" in two governance documents where the true
number is seven, the same `§8` citation error in `lean/Workspace/Leverage/Basic.lean`,
and — found by a track, reproduced here — `checkers/run.py:131` raising on a
relative command-line argument before any checking happens.

**A correction to this round's own Phase 0 report.** It initially stated that
`projects/deference/notes/**` matched neither layer of `tests/path_gate.py`. That is
true only for arbitrary filenames: `fnmatch`'s `*` crosses a path separator, so
`projects/*/README.md` and its three siblings already protected those basenames at
any depth. The correct statement is that protection was keyed on **basename, not
directory**, so whether a canonical document was specification layer depended on
what it was called.

## Specification initialization

The maintainer's pre-dispatch decision — four canonical documents at named paths,
with precedence fixed — is implemented and recorded in `DECISIONS.md` as having been
made before dispatch. `projects/deference/notes/README.md` now describes the present
ontology rather than an empty directory, and the ledger stub asking which deference
documents are canonical is closed.

**Canonicalization was blocked once, deliberately, and then unblocked by
authorization.** The four documents could not honestly be created at their intended
paths while those paths were not specification layer for the filenames they would
use; creating them anyway would have made them specification-layer in prose only.
The round stopped, reported the options, and waited. On authorization,
`"projects/*/notes/**"` was added to the specification enumeration with three
self-test cases, including the regression that an arbitrary filename under a line's
`notes/` classifies as specification. A contribution surface nested under `notes/`
still resolves to the proof layer, because proof patterns win. Adding a
specification pattern only ever removes contributor write access, so the failure
direction is safe.

**One conditionally authorized change was not made.** The same authorization covered
`projects/*/FOR_HUMANS.md` *if inspection confirmed* that `AGENTS.md` designates it a
specification-side artifact. Inspection does not confirm it: `AGENTS.md:146` names
`FOR_HUMANS.md` as the human-register *style*, `AGENTS.md:333–336` assigns
"dual-register documentation of contributed results" to the **proof** layer, and
`AGENTS.md:138` requires every substantive deliverable to ship both registers.
Protecting the path would forbid a contributor from writing a register they are
obliged to ship. The pre-existing `projects/*/THEOREMS.md` protection has the same
defect and `projects/*/VERIFICATION.md`, named beside it, is unprotected — three
faces of one question, left open rather than half-answered.

## Shared finite skeleton

`FINITE_MODEL_SKELETON.md` **v1**, frozen before dispatch, consumed unmodified by
every track that used it. **No revision was issued mid-pass.** Four tracks reported
deficiencies; each layered its own additions over the frozen object and declared
them, rather than forking the ontology, which is what the discipline asks. The
deficiencies are collected as maintainer decision 6 below.

## Parallel dispatch table

| track | prompt path | result | evidence | integrated |
|---|---|---|---|---|
| A — faithful acceleration | `2026-08-11-faithful-acceleration/` | six inherited Movement-I statements re-elaborated here; the criterion's application to the trader derived rather than assumed | **`lake build` green, 1834 jobs; 38 results / 5 files within the allowance; no `sorry`, no `axiom`** — verified by the orchestrator | yes |
| B — settlement + delegation | `2026-08-11-deference-finite-kernel/` | settlement classified; the local bridge derived with sharp constants; the trust relation shown imported | five certificate parameter sets accepted by the **unmodified house enumeration checker** (625/625/289/8/625 points); `verify.py` exits 0 | yes |
| C — certificate kernel | `2026-08-11-deference-certificates/` | literal target shown non-derivable; two theorems derived instead; three impossibilities | script exits 0, 49 checks; enumeration **524,880 models / 1,341,360 instances / 0 violations** | yes |
| D — simulator substitution | `2026-08-11-deference-channel/` | divergence witness; the rule slot shown inert in v1 | four instances **`witness-checked`** by the house checker (65/65/65/64 constraints); a perturbation correctly rejected at constraint 0 | yes |
| E — densification | `2026-08-11-deference-densification/` | exact exposure–harvest identity; sharp lower bound; three necessity witnesses | script exits 0, no floats; regime tables and netting witness reproduce | yes |
| F — triangle | `2026-08-11-deference-triangle/` | matrix: compatible 3, conditionally compatible 1, incompatible 0, **unresolved 11** | documentary; ten cited declarations verified present, quotations checked | yes |
| G — admissibility red team | `2026-08-11-deference-admissibility/` | two exact incompatibilities on the reverse arrow; three candidate families | exact-rational computations, recomputed independently by the orchestrator | yes |

Every track's citations were treated as data and checked before recording. Six of
seven were blocked by their tooling from writing `.md` reports; those deliverables
were returned as text and written to disk by the orchestrator verbatim, recorded as
a deviation in each report. Where a human register was owed and the executing agent
could not write it, the orchestrator wrote it and labelled it as the orchestrator's
text at the head of the file.

## Cross-track synthesis

### Settlement — did Track B obtain disagreement-profitability, or only grade prediction?

**Only grade prediction, and the demonstration is maximal rather than marginal.**
Grade/report settlement constrains `A`'s prices into the convex hull of realizable
grades and does nothing else; the witness has `A` predicting the principal's grades
*perfectly*, no position on grade contracts profiting in any state, and deference
still losing to a fixed intervention by `2B` — the largest the bound permits. World
settlement makes the question measurable but not costly. Enforcement delivers the
conclusion unconditionally at a bond of exactly `2B`, for every instance, competent
principal or not, with **zero epistemic content**.

Per the addendum's instruction to distinguish mechanism from epistemics
aggressively: **this result is labelled enforcement / mechanism design.** Nothing
establishes epistemic trust. The one architecturally interesting step is that the
bond must be charged against the taken-versus-reported comparison, which only grade
settlement makes observable — so the two instantiations that yield no delegation
compose into the one that does.

### Composite candidate — the contingent WP-D shape

Stated below under its own heading, with its gate.

### Channel — can delegation be distinguished from substitution without assuming permanent unpredictability?

**No, not within skeleton v1's carriers.** In v1 the rule slot carries one datum —
a declared information time — and that label is a free relabel exactly where it
would have to do work. The only structural extensional separator is that
delegation's selection is not decision-time measurable, and that separates
delegation from substitution **exactly when the principal is unpredictable**, which
the program has forbidden itself. Under a perfectly predictable principal the
counterfactually faithful simulator *is* delegation, as a function.

This is the direct answer to addendum point 1: **timing alone was doing the
conceptual work, and it does not survive the program's own commitment.** It is
surfaced as a maintainer decision, not treated as settled. Separation survives only
in a variation register (statable, unverifiable from a single run) or an
architectural register (verifiable by inspection, unstatable in the model).

On the addendum's three sub-questions: a late simulator acting at `F(n)` while
ignoring the actual channel is **representable in v1's carriers but absent from the
conduct table**, and it is well-timed exactly like delegation while still
substituting — direct evidence that timing cannot carry the distinction. An earlier
binding instruction from the principal is **not representable in v1** at all.

### Admissibility — is there a condition passing all four tests?

**Forward arrow: yes, with a disclosed cost. Reverse arrow: no, and the
incompatibility is exact.**

> Under principal-report settlement with a finitely-valued report and a live
> advisory channel, the settlement whose quote-responsiveness constitutes the
> diagonal, the target the advisory channel is designed to move, and the object the
> forcing trader cashes out against are **the same carrier**. Any condition
> excluding the first excludes the other two. No sort split separates them, because
> they are not different sorts.

The escapes are all modelling choices about the *principal*: make the report
rational-valued and continuously responsive, sever the advisory channel from the
graded decision, or stop cashing out against principal reports. A second,
quantitative incompatibility forces admissibility to be **two-sorted**: a single
uniform gain bound admits the inherited forcing gate only above the reciprocal of
its gate width, so no finite bound admits the sharp trader.

### Certificates — do B and C compose over the same skeleton?

**Yes, in the only sense the round is entitled to claim, and no more.** Both state
their results over v1 unmodified; neither renames or retypes a v1 object; their
proposed patches are disjoint and additive — B's transfer typing, valuation variant
and pricing layer; C's gated conducts, decision-time availability and movement
parameter. They therefore quantify over the same carriers.

They do **not** chain into a single theorem, and the round does not claim they do.
What they share is stronger evidence than a chain would be: both require the same
imported hypothesis, in two norms — B's conditional-expectation grade trust and C's
`L¹` movement bound are two formulations of the grade-to-quantity link the skeleton
declares a hole — and both prove it necessary with the same `2B` failure witness.

### Delay — what emerged within Track E's bounded scope?

An exact identity, not an estimate: under an exposure cap the total placeable weight
by a deadline is exactly the cap times the largest number of pairwise-disjoint
settlement windows before it. Adaptivity, overlapping positions and fractional
sizing each buy exactly nothing, and the bound proves it rather than a search
failing. The literal target is therefore achievable in *every* delay regime by a
two-line construction, which makes the rate the real question; forcing `W` units of
harvest costs the `⌈W/(Mδ)⌉−1`-th iterate of the delay.

The finding for the maintainer is that the question is under-specified: the
constraint studied bounds outstanding gross exposure, the Logical Induction budget
bounds worst-case cumulative loss, and the two functionals give **different
answers**.

### Triangle — are the two arrows compatible?

Undetermined, and honestly so: 3 compatible, 1 conditionally compatible, 0
incompatible, **11 unresolved** of 15. Zero incompatible is not a clean bill of
health — an interface with no fixed content cannot be contradicted. The structural
reason is that the fixed reverse-arrow architecture is an ordering-and-measurability
architecture with no cost model, no market and no trader class, while nearly every
forward-arrow requirement is a cost, market or settlement-semantics condition.

The audit also found a defect in **this round's own roadmap**: the inherited corpus
carries three distinct reference processes with provably different reach — the
autonomous reasoner that never reads `A`, the frozen prefix family, and the coupled
advised process — and the roadmap names two vertices while identifying none of them.
The strongest inherited forward-arrow results are stated for the object the roadmap
places at the *destination* of the reverse arrow. Verified against the sources. Until
this is decided, no cross-track composition claim in this round is well-formed.

### Faithful acceleration — what is now established here versus inherited only?

Six of the ledger's Movement-I statements are now **`workspace-established` in the
kernel sense**: they re-elaborate in this repository against the pinned toolchain,
audit clean, and name their inherited sources. Beyond transcription, the pinned
dependency was found to model markets and traders, so the inherited `hbdd` — the
audit's headline modelling substitution — is replaced by an actual application of
`IsLogicalInductor`, with the doubly-soft gate built as a real element of the
dependency's expressible-feature grammar. That discharges the inherited audit's
finding 7 outright.

Two errors were found *by porting* that reading had missed: `hbdd` bounds net worth
rather than banked value, so at general lookahead the quantity is unbounded and the
dependency's own theorem carries a support condition the inherited statement lacks;
and it assumed the criterion's conclusion while skipping its precondition.

**Not promotable.** Efficient computability of the trader is undischarged, so the
headline is `unverified-nonvacuous`. And `A`'s calibration has no endpoint in the
dependency for a structural reason: the dependency's theorem requires a
world-settled target, while this target is the human process's future credence,
which never settles. That is a missing *kind* of theorem, not a missing lemma.

## Convergent obstructions

The addendum asked that independent convergence weigh more heavily than any one
track's preferred architecture. Three convergences are real; the tracks ran against
one frozen snapshot and did not see each other's output.

1. **No valuation-level separation of delegation from simulation.** Track B's T4,
   Track C's I1 and Track D's Proposition 1 are the same theorem, derived three
   times from three different starting points. The rule/quantity distinction the
   skeleton sets up does no work in the valuation.
2. **The grade-to-quantity link is the load-bearing hole.** Track B needs it, Track
   C needs it, Track G needs it; three formulations, three independent necessity
   witnesses, all at the maximal `2B`. Track G additionally shows that assuming it
   *uniformly* makes the market dispensable — the conclusion follows in three lines
   with the bound `2η` attained — so the apparatus earns its keep only in a
   statistical version nobody has written.
3. **Causal or counterfactual structure is where the separator must live.** Track
   D's variation register and Track G's counterfactual condition family reach this
   independently, and Track F's row 10 records that the inherited corpus already
   refutes purely extensional criteria.

A fourth, weaker: patience and cross-decision structure surface in B, C and E alike
as the thing the per-decision skeleton cannot express.

## Contradictions

**None found between tracks.** Two apparent tensions resolve on inspection and are
recorded so a later reader does not re-derive them as conflicts.

- Track G's uniform-link result (`ε = 2η`, sharp) and Track C's delegation bridge
  (`2M`, sharp) are the *same constant* under the identification of the two
  hypotheses. Agreement, independently reached.
- Track F classifies the certification failure direction as `compatible` while
  Track C proves no certificate is strictly non-preemptive. These concern different
  branches: the fail-closed invariant governs the `¬Cert` branch, which is what F
  compared, and C's impossibility is about the `Cert` branch. F's `compatible` is
  narrower than it reads, and this report says so rather than leaving the row to
  carry more weight than it earned.

## New assumptions, mechanically diffed

Per addendum point 7, every hypothesis added by a track, classified against the
dispatched target. **No unacceptable strengthening was found.**

| assumption | track | classification |
|---|---|---|
| grade trust `GT_𝒢(η)` | B | independently necessary, with witness; **imported**. *Corrected 2026-08-11 by Phase II Track I §7.2:* this row originally read "a competence claim about the principal, containing no reference to `A`'s credence". That is false as written — `GT_𝒢(η)` mentions `P` twice, in `P(C) > 0` and in `E_P[X_π \| C]`. It is credence-free only at the discrete conditioning partition, where Track B's §1.1 records that it reduces to a pointwise bound. The distinction is load-bearing: Track I's Proposition 1 shows the credence-free / credence-dependent line is exactly the line between a circular hypothesis and a usable dial |
| movement `(MV-M)` | C | independently necessary, with witness at the full `2B`; **modelling substitution**, and the dangerous one — it asserts what the dispatch's §14.2 says principal-report settlement does *not* deliver |
| trust tolerance `(TR-ε)` | C | necessary in `L¹` form, with witness; **unearned**, and possibly the wrong shape — a signed, expectation-matching relation is provably insufficient |
| one-shot pricing layer | B | proof-convenient / architectural — without some such layer "what does settlement yield" has no formal content in v1 |
| transfer-bearing valuation `V^τ` | B | declared variant, **not** the target's valuation; its theorem must not inherit the target's status |
| grade register `G_n` | C | declared variant; makes delegation a maximizer *by construction*, so its strictness measures preemption headroom, not profitability |
| response map | G | works around a v1 deficiency: the quote-responsive diagonal is **not expressible in v1 at all** |
| hold-from-open, gross exposure, no reinvestment | E | each independently necessary, each with an exact witness |
| persistent defect `(P)` | E | unearned; sits on the standing gap |
| quantity identified with grade | D | strongest-for-delegation, so the finding is not bought by weakening the principal |

The governing consequence: **no positive result from this wave may inherit a status
stronger than its weakest imported hypothesis**, and in every case the weakest is
unearned. The one exception is Track A's Lean, whose hypotheses are either derived
in-project or discharged from the pinned dependency — and which is still not
promotable, for the separate reason that its efficiency obligation is open.

## Claims registered

**None.** `projects/deference/CLAIMS.md` does not exist and was not created.
Registration is demand-gated and a maintainer act; four entries from Track D pass
the house checker today and five certificate parameter sets from Track B pass the
house enumeration checker today, but passing is not registering. Creating the
registry is maintainer decision 8.

## What remains unproved

- The forcing itself, on both arrows. "The criterion forces the tower" is `open`;
  nothing this wave narrows it, and Track E's harvest model sits on top of it.
- Every finite result's antecedent. B's bridge, C's certificate and E's harvest all
  hold conditionally on hypotheses no mechanism in this repository supplies.
- Whether the intended cross-agent trust property yields `L¹` or only signed
  accuracy — controlling for whether C's certificate has an antecedent at all.
- Any separation of delegation from substitution, in any register the model can
  verify from a run.
- Any admissibility condition surviving the reverse arrow under a discrete
  principal report.
- `π^{FU,g}` entirely: it remains a declared hole, and the round deliberately did
  not invent it.
- The triangle: 11 of 15 interfaces have no fixed reverse-arrow content to compare.
- Movement VI: the dose-response material was **not assessed** this round. Its
  status is unrecorded rather than assigned.
- Efficient computability of Track A's trader, and any endpoint for `A`'s
  calibration.
- Cross-decision structure, and with it foreclosure — which Track D argues may be
  where the real content of the substitution worry lives.

## Candidate WP-D statement

```
STATUS: contingent theorem shape, not canonical theorem statement.
GATE:   maintainer/Abram settlement decision, and maintainer decisions 1-3 below.
CONTINGENT ON SETTLEMENT INTERPRETATION.
```

The wave supports a hybrid shape, and it is weaker and more honest than the one the
dispatch anticipated, because Track B established that two of the three reaches
contribute nothing to the delegation inequality.

> **Shape.** Fix a decision index with menu `Π_n`, delay `F(n)`, and `A`'s
> decision-time credence `P_n`. Partition the menu's consequences into
> (i) components whose intervention-indexed quantity is `F(n)`-measurable,
> (ii) components on which the designated principal reports a grade at `F(n)`, and
> (iii) a residual on which neither settles. Assume:
> **(H1)** on (i), world settlement, and a declared grade-to-quantity link at level
> `η` over an admissible conditioning partition;
> **(H2)** on (ii), principal-report settlement, which fixes what the principal
> judged and nothing further;
> **(H3)** on (iii), an explicit arrangement charging a conformity bond `λ` against
> the `F(n)`-observable taken-versus-reported comparison.
> Then for every comparator whose selection is measurable with respect to that
> partition,
> `V_n(DELEGATE) ≥ V_n(c) + M(c) − 2·η·D(c)` on (i)–(ii), and
> `V^τ_n(DELEGATE) ≥ V^τ_n(c)` on (iii) provided `λ ≥ 2B`.

Four things this shape must carry, all established this wave:

1. **The epistemic content lives entirely in (H1)**, and (H1) is a competence claim
   about the principal that no settlement mechanism in the skeleton produces.
2. **(H3) is enforcement.** It holds for every instance regardless of the
   principal's competence, and `2B` is exactly necessary and sufficient.
3. **The shape does not cover `SIM`**, and cannot: three tracks independently show
   the valuation cannot separate it from `DELEGATE`.
4. **It does not cover `π^{FU,g}`**, whose object is undefined.

It is offered as something to attack, not to adopt.

## Paper-architecture implications of the round

Assessing, not adopting, the addendum's narrower arc.

**The ordering is supported, and two of its claims are now evidenced rather than
asserted.** *Settlement must precede interpretation of the trust theorem* — Track B
makes this concrete: the same inequality reads as epistemic trust or as enforced
conformity depending on a choice not yet made, and the enforcement reading is the
one available unconditionally. *Channel individuation must precede fully updated
deference* — Track D makes this sharper than the addendum put it: an extensional
delegation predicate does not merely *risk* classifying simulator substitution as
delegation, it **provably cannot distinguish them**, so any FUD statement written
before the channel question is settled is quantifying over a comparator class it
cannot delimit.

**Legitimacy as a limitation rather than a movement is supported.** The theorem
takes the designated principal exogenously; nothing in the wave touches whether the
designation is justified, and Track G's escape from its own incompatibility is a
substantive assumption about how human oversight responds — a claim about people
that belongs in a limitations section, stated out loud.

**The decomposition of "manipulation" is supported and one leg is now measured.**
Substitution reduces to channel individuation, and that leg is where the wave's
negative results concentrate. Steering, via dose and endpoint displacement, was not
assessed. Evaluative quality of influence is untouched, and the wave gives no reason
to think leverage closes it.

**Preservation falling outside the first paper is supported** by absence of
evidence rather than by evidence: nothing this wave bears on it.

**One correction the arc should absorb.** The arc's opening, `H → A`, is the only
place the wave produced kernel-adjudicated content — and it produced more than
transcription, since the market gap partly closed there. The arc understates its
first movement and overstates the readiness of everything after the settlement step.

**On dose, the addendum's stronger role is untested.** The material was not
inspected this round; assigning it a role now would be exactly the kind of
promotion-by-narrative the ledger exists to prevent. The addendum's warning about
its cost — that endpoint-displacement bounds may forbid beneficial teaching along
with harmful steering, because the criterion is evaluatively blind — is consistent
with everything the wave found about evaluative blindness elsewhere, and is the
right thing to test first when the material is assessed.

## Verification

| command | outcome |
|---|---|
| `python3 tests/run.py` | ALL GREEN, all gate self-tests pass |
| `WORKSPACE_LEAN=1 python3 tests/run.py` | Lean build green; axiom audit clean |
| `lake build Workspace.Deference.Contrib.*` | **Build completed successfully (1834 jobs)** |
| `python3 tests/audit_axioms.py` | **38 results across 5 files**, all within the allowance |
| `python3 tests/path_gate.py --self-test` | 11 cases pass, including three added this round |
| `python3 -m checkers.run "$PWD/prompts/2026-08-11-deference-channel/CLAIMS-proposed.md"` | 4 entries, 4 PASS |
| perturbed copy of the same | FAIL at constraint 0 — the gate bites |
| `python3 prompts/2026-08-11-deference-finite-kernel/verify.py` | all checks pass exactly; five house-checker certificates accepted |
| `python3 prompts/2026-08-11-deference-certificates/verify_certificate.py` | exit 0; 524,880 models / 1,341,360 instances / 0 violations |
| `python3 prompts/2026-08-11-deference-densification/exposure_geometry_check.py` | exit 0; no floats |

**A gate-coverage gap, stated rather than worked around.** `lean/Workspace.lean`
imports three modules and not Track A's two, so `lake build`'s default target does
not compile them: the textual gates see five files, the build gate sees three. CI
would not catch a regression in the round's only kernel-adjudicated content. That
file is specification layer and outside this round's write scope.

## Next-round recommendation

The smallest mathematically mature next dispatch is **not** a WP-D proof attempt. It
is the question that decides whether WP-D's intended engine exists:

> Determine whether the intended one-sided cross-agent trust property yields an `L¹`
> grade-accuracy bound, or only a signed / expectation-matching bound.

It is cheap, it is finite, two tracks independently identified it as controlling,
and both answers are informative: signed accuracy kills the certificate's engine and
forces a different one, while `L¹` accuracy gives the certificate an antecedent for
the first time. Everything else on the frontier is downstream of it.

Second, and independent of any maintainer decision: **port to Lean** Track B's
bridge, Track C's L1–L3 and Theorem C′, and Track E's Lemma 1 and Theorem 2. All are
finite, elementary, and free of Logical Induction facts; each has a constructed
inhabitation witness already in hand. That moves the wave's core from proposal to
`lean-proved` without anything being decided first.

---

## Outstanding maintainer actions

1. **Decide the settlement interpretation.** Epistemic reading (requires importing a
   competence hypothesis about the principal) or enforcement reading (unconditional,
   bond `2B`, zero epistemic content). Blocks the WP-D shape, Track F's row 4 and
   row 7, and Track G's decision 4. Record in `DECISIONS.md` and amend the roadmap's
   "Settlement architecture — candidate, not endorsed".
2. **Decide whether a counterfactually faithful simulator counts as delegation.**
   Not extractable from the model; Track D §9.1 states both horns. Blocks the typing
   of every WP-C criterion.
3. **Decide whether the principal's report is discrete or rational-valued with
   bounded continuous response.** Track G's Incompatibility I is unresolvable
   without it, and the answer is a substantive claim about human oversight.
4. **Identify the roadmap's `H` and `H⁺` with inherited objects** — the autonomous
   reasoner, the frozen prefix family, or the coupled advised process. Until this is
   done no cross-track composition claim in this round is well-formed.
5. **Decide whether a bounded preemption *rate* is an acceptable rendering of
   "non-preemption of continuing corrective authority".** Track C's I3 proves the
   choice is forced: certified discretion with a bounded override rate, or no
   discretion at all. Amend the roadmap's standing commitments if the answer is the
   latter.
6. **Rule on skeleton v2.** Six additive patches were proposed and none applied:
   gated conducts, decision-time availability, a movement parameter, transfer typing
   on the taken-versus-reported pair, a valuation variant carrying transfers, and a
   quote carrier without which the diagonal is inexpressible. A revision is a version
   bump in `FINITE_MODEL_SKELETON.md` §10 plus a rerun-or-reconcile decision for
   tracks B, C, D and G.
7. **Decide the exposure functional** — bounded outstanding gross exposure or the
   Logical Induction bounded-loss budget. Item 18 has two different answers until
   this is recorded, and Track E supplies both.
8. **Decide whether to create `projects/deference/CLAIMS.md`** and register Track D's
   four witness entries and Track B's five certificate parameter sets. Both pass the
   unmodified house checkers today; registration is demand-gated to items 15 and 17
   and is a specification-layer act.
9. **Add the two-line import to `lean/Workspace.lean`** so the round's Lean is built
   by CI. Outside this round's write scope; without it the only kernel-adjudicated
   content in the wave is not covered by the build gate.
10. **Fix `checkers/run.py:131`** — `path.relative_to(ROOT)` raises on a relative
    command-line argument before any checking happens. Fails loudly, so not a
    soundness hole. Resolve arguments to absolute paths before use.
11. **Correct the stale CI job name** `foundations-verification` → the actual job
    `consolidation-verification`, in `CONTRIBUTING.md:56`, `SETUP_REPORT.md:67,97`,
    `GOVERNANCE_REPORT.md:118`, `projects/leverage/CLAIMS.md:25`.
12. **Correct the gate count.** `AGENTS.md:609` says "Eight jobs decide correctness";
    `DECISIONS.md:84` says "nine gates" and `:201,:208,:221` say "eight". The true
    number is seven CI jobs, seven required contexts, seven gate scripts. The
    `DECISIONS.md` mentions sit inside settled entries, which the ledger's own header
    makes append-only in substance, so this round did not edit them.
13. **Correct `lean/Workspace/Leverage/Basic.lean:10`**, which cites `AGENTS.md` §8
    for the no-axioms rule; that rule is standard 4. The deference-side twin was
    repaired this round; this one is outside the write scope.
14. **Resolve where dual-register documentation lives** — `projects/*/FOR_HUMANS.md`
    and `projects/*/VERIFICATION.md` are unprotected while `projects/*/THEOREMS.md`
    is protected, and `AGENTS.md` assigns dual-register documentation of contributed
    results to the proof layer while requiring every deliverable to ship both.
15. **Decide whether `projects/deference/notes/` documents need a `PROVENANCE.md`
    entry beyond the row added this round**, and whether the round's seven track
    directories each want their own row.
