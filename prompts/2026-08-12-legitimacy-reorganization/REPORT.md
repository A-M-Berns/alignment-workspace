# Report — legitimacy reorganization

**Attribution.** Prompt author: GPT-5.6 Sol (OpenAI). Executor: Claude Opus 5
(Anthropic). Dispatched 2026-08-12; executed 2026-08-12.

**Verdict: partial success**, on the prompt's own criteria. The decomposition is
real; the proposed two-part equation for legitimacy is not sufficient and the
round exhibits what is missing; the end-to-end invariant exists and was already
proved under a different description; and the online-learning target is worse off
than it looked, with the obstruction isolated.

---

## What was done

`projects/leverage/rounds/2026-08-12-legitimacy-architecture/` — the abstract
conditions as executable checks, six attacks, six independence witnesses, an
exhaustive conservation sweep, and the comparator-class analysis. 54 tests.

`projects/leverage/notes/LEGITIMACY_ARCHITECTURE.md` and its human register — the
consolidation artifact the prompt's §IX asks for, at line level rather than
inside the round, so it is a consolidated view rather than a round record.

`RESEARCH_STATE.md`, `projects/leverage/README.md`, `PRIORITIES.md`,
`DECISIONS.md` — updated to the architecture, with five items filed and three
entries appended to the queue.

## What was proved or mechanically checked

- **Conservation.** Every liability live at the start of a diachronically
  answerable trajectory has exactly one fate — live descendants, a backed
  terminal disposition, or a routed suspension — computed by folding the record.
  Derived by induction; the case analysis is exhaustive over all `343` mode
  sequences of length three. The gate refuses `316` of them when the backing
  fields are stripped, so the sweep is not confirming that the enumeration runs.
- **Non-laundering.** Churning the vocabulary at every step changes no accepted
  set, no fate and no backed-terminal count. The hypothesis doing the work is the
  opacity of liability identity, not preservation of any vocabulary.
- **Fate composition.** The fate of a concatenation is fixed by the first
  segment's fate and the second segment, over all `2401` segment pairs. The
  endpoint audit needs no replay.
- **Record-measurability.** Both conditions are functions of the record, by
  construction of the footprint and by the checks' inputs.
- **The comparator core formula.** `Phi(F)` is the product over responses of the
  intersection of the admissible sets containing them; verified against
  enumeration over all `512` three-region families on a three-response space.
- **Collapse.** `Phi(F)` is the identity alone exactly when those intersections
  are singletons. Displayed at `|Phi| = 1` on a four-response family, against
  `256` for a constant constraint and `36` for a partially-moving one.

## What the prosecution found

Three attacks pass, and they pass for one reason: **neither condition constrains
what may be put on the record.** Self-filed grounds relicense a laundered
standard; unbounded defeater production is admitted; an undocketed demand is
invisible. The first two want a ground-provenance condition, the third wants
coverage, and neither can be folded into the two conditions — a record predicate
cannot quantify over what is absent from the record.

The fourth is inherited and decides what this layer can ever contribute to the
manipulation problem. Re-instantiating the deference line's kernel-checked
non-recoverability pair so that both runs write full normative records: the
records are equal, both trajectories are legitimate, and the influence defects
are exactly `0` and `1/2`. Since `gate_blind` is quantified over all gates, no
strengthening of a record predicate reaches endpoint corruption.

Two attacks fail, which is the architecture working. Ontology laundering is
defeated outright. Excessive conservatism is absent: a trajectory that retires
its vocabulary, rewrites its own standard and reverses its verdict is legitimate,
and its endpoint is refused by its own initial constraint.

Independence holds in all six cells. The last two are sharper than asked: the
illegitimate routes attain the *same* charge as the best legitimate trajectory,
so at its optimum the performance criterion does not discriminate legitimacy at
all.

## Two defects found in the existing machinery

**A declared magnitude allowance is never consumed.** It is compared against a
step's movement, so one impediment with allowance `2`, cited at four dates,
licenses cumulative movement of `8` with every step admitted and the composite
refused. This is a defect in the statics rather than a fact about legitimacy, and
the repair — consumable allowances — is filed as item 36.

**The end-to-end theorem already existed.** `ST-J2` of the frozen consolidation —
if every step of a history is accepted, the composed transport is accepted and
each resource's global route is the composite of its local routes — is the
composition result the prompt's §V.5 asks for. It was filed as a result about
migration. Reorganizing is what made it findable, which is the clearest single
piece of evidence that the reorganization was worth doing.

## Prior art the first draft under-cited

Two headline observations restate a moral the workspace already holds, and the
round's documents originally labelled them `CITED` without naming where the
framing came from. `THEOREM_MAP.md` §6a now does.

The legitimacy programme is the deference line's: `li-deference.md` §0.3, human
notes by Abram Demski, already identifies the legitimacy of feedback as the
missing object and names manipulation that the feedback subsequently confirms as
a mode to exclude. The provenance principle is stated in `legitimacy-theory-v1.md`
§2.3, whose §3 already classifies trace conditions as provably empty — so LEG-2 is
that classification applied to a new pair of predicates rather than a new
principle. And `RECONCILIATION.md` has already adjudicated one independent
convergence on this shape; the ground-provenance finding here is a third
instance, from the reasons side.

What is not a restatement: the conservation, non-laundering and composition
results; NL-1 and NL-2; the allowance defect; and the `ST-J2` observation.
Ontology shift is named in `li-deference.md` §0.3 as something that line does not
model, so the diachronic half is not duplicated work.

## Deviations

1. **No Lean.** The execution environment has no Lean toolchain, so nothing could
   be kernel-checked and shipping unchecked Lean would be worse than shipping
   none. Four port targets are filed as item 35 instead. This also means the
   round did not run the full check list of §XI.10; `python3 tests/run.py` is
   green, `lake build` was not run.
2. **No directory or identifier rename.** §VIII asks for the umbrella name to be
   deprecated in active roadmap and explanatory material, which was done. The
   directory `projects/leverage/`, the claim identifiers, the frozen tree's own
   text and the deck's title keep their names: three are frozen or load-bearing
   for citation and the fourth is the author's own words, and §VIII's own caution
   against churn in formal identifiers applies. Recorded as technical debt in the
   queue rather than done silently.
3. **The explicit terminology marking in §VIII was not used.** "Formerly developed
   under the working name X" is the construction `AGENTS.md`'s *no negative
   ontologies* rule forbids in living documents. The correspondence is kept where
   that rule keeps history — the round record's `MAPPING.md`, and the
   `DECISIONS.md` queue entry — and the living documents state the present
   architecture without narrating the change. Flagged rather than absorbed
   because it is a real conflict between the dispatch and a binding standard.
4. **The architecture as shipped has four conditions, not two.** §XI.7 directs
   revision in response to findings; the prosecution showed the conjunction
   insufficient, so ground provenance and coverage are stated as conditions
   rather than as caveats.
5. **The consolidation artifact went to `notes/` rather than into the round
   directory.** A round directory is a round record; a document intended as the
   line's entry point is a consolidated view, and the repository's layering puts
   those in different places.
6. **`legitimacy` collides with a live sense already in the workspace.** The
   deference note dump uses it for endpoint-preservation. Both senses are live,
   so both are named — *record legitimacy* and *endpoint legitimacy*,
   provisional — rather than one being silently displaced.

## What this does not establish

- Nothing is kernel-checked; nothing is registered in `CLAIMS.md`.
- That the abstract constraint captures the substrate's nine checks is a reading
  at the strength of a reading audit, not a proof. The substrate's three
  parametric relations are represented here by weaker defaults than its own.
- The composition conjecture RR-3 has no proof attempt beyond identifying its
  three hypotheses.
- Ground provenance is named and unimplemented: the model carries the partition
  as a field that no clause reads, which is the finding and also the gap.
- Coverage is defined against a declared arrival process. An advisor who controls
  what *arises* rather than what is *filed* is out of scope.
- The corrigibility composition is a conjecture; no theorem combining the two
  layers was attempted.
- The finite model is one occasion, two substantive coordinates, at most four
  liabilities, horizons of at most four dates. Nothing here is asymptotic.
- The relation between the constraint's non-transitivity and the deference line's
  trust non-transitivity conjecture is noted as a structural echo and is
  unexamined.

## Workspace friction

**F7 — a round with no Lean toolchain cannot tell the difference between "no Lean
was warranted" and "no Lean was possible."** Filed in `PRIORITIES.md`. The
report says which applies here; nothing in the repository records it, and the
next reader of a Lean-free round has no way to tell.

## Filings

Items 35–39 filed in `PRIORITIES.md` under this round's dispatched scope, with
this prompt as the authorization. F7 filed under *Workspace friction*.

## New names introduced, all provisional

`normative constraint` (as the name of the statics layer), `diachronic
answerability`, `record legitimacy`, `endpoint legitimacy`, `ground provenance`,
`filing gap`, `constraint core`, `comparator collapse`, `consumable allowance`.
`reasons-responsiveness` and `coverage` are the line's existing terms and are
unchanged.

## Outstanding maintainer actions

1. **Rule on the umbrella name.** The dispatch deprecates `leverage` as the
   umbrella and this round did so in the living documents while leaving the
   directory, the claim identifiers, the frozen tree and the deck alone. Confirm
   the split, or direct the rename. *Doing it* is one decision; *waiting* leaves
   the living documents and the directory name disagreeing, which is the state
   this round is proposing rather than assuming.
2. **Rule on the two senses of `legitimacy`.** Confirm the disambiguated pair, or
   name one of them something else. Two live senses in one workspace is the case
   `AGENTS.md` permits disambiguating; which words do the disambiguating is
   reserved.
3. **Rule on whether the architecture equation is four-part.** The round found
   the two-part conjunction insufficient and shipped four conditions. Adopting
   that is a `DECISIONS.md` entry; without one the architecture note is a
   consolidated view like any other.

All three are appended to `DECISIONS.md`'s *Awaiting the author*.
