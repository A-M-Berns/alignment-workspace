# Provenance

| file or glob | generator | review status | date |
|---|---|---|---|
| `*.md` | Claude Opus 5 (Anthropic) | `ci-only` | 2026-09-01 |

A **consolidation checkpoint**, not a research round. No claim is registered, no
Lean is written, no settled definition is changed, and no prior round's artifact
is edited. Every statement here is a restatement, a classification, or a reading
of work that already existed; where a document draws a conclusion the sources do
not state — the four-layer decomposition, the audit of the dependency spine, the
reconciliation of the renewable and consumable budgets, and the assessment of the
candidate legitimacy decomposition — that is said in the document itself and is
marked as the checkpoint's own judgment rather than an inherited result.

## Inputs read in full

- `projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/`,
  all documents, as merged;
- `projects/normativity/legitimacy/rounds/2026-08-30-progress-consolidation/`,
  for the Progress schematic, Surface Fairness, and Persistent Relevance;
- `projects/normativity/legitimacy/rounds/2026-08-30-liability-theory/` and
  `.../2026-08-30-progress-liability-hard-pass/`, for Common-Mixture
  Affordability and covered underwriting;
- `projects/normativity/notes/TRADERIZED_FORCE_INTERFACE.md` and
  `projects/normativity/rounds/2026-08-16-traderized-enforcement/`, for the force
  layer and what is kernel-checked;
- `projects/normativity/consolidation-aug9/`, chiefly
  `THEORY_11_SETTLEMENT_INTERFACE.md`, `GLOSSARY.md`, `README.md` and
  `OPEN_PROBLEMS.md`;
- `projects/normativity/legitimacy/rounds/2026-08-25-carroll-legitimacy-test/`,
  `.../2026-08-30-answerability-carriers/`,
  `.../2026-08-30-anchored-slices-auth-transfer/`,
  `.../2026-08-31-faithful-semantic-preservation/`,
  `.../2026-08-30-cf-coverage-continuity-interface/` and
  `.../2026-08-30-proper-exercise-calculus/`, at README and headline level. The last
  five were read from a working checkout before they reached `main`; see *One finding
  about the repository itself* below;
- `wiki/Deference.md`, `wiki/Corrigibility.md`, `wiki/Roadmap.md`,
  `wiki/CONVENTIONS.md`.

## The external input

*Diachronic Answerability Under Self-Revision — a calculus of provenance,
succession, semantic conservation, and service*, 31 August 2026, twenty-two pages,
supplied by the maintainer outside this repository. **Read in full**, all twelve
sections. It is not vendored here: it is an unpublished draft, and this checkpoint
cites it by section and theorem number rather than reproducing it. Where its
repository counterpart rounds carry the same statement, they are cited too.

The note describes itself as a *"working mathematical synthesis; paper proofs, not
Lean-verified"*, and it is treated at exactly that strength throughout —
`STATUS_LEDGER.md` rows 36–45 record its results as **paper-derived**, and its
semantic-authentication and service assumptions as **interface assumptions**,
because the note itself declares them application-supplied.

**No blocker.** The file was available and was read; nothing in the consolidation
is conditional on an unavailable input.

## One finding about the repository itself, and its repair

While this checkpoint was being written, six research rounds — *answerability
carriers*, *anchored slices and authenticated semantic Transfer*, *faithful semantic
preservation*, the two *CF-coverage* rounds and *proper-exercise calculus* — **were
not on `main`**. Their pull requests are marked merged on the forge and were merged
into *each other*: the stack was based on `round/2026-08-30-liability-theory` and
then on `round/2026-08-30-answerability-carriers`, and nothing from the top of that
stack to `main` was ever opened.

It was found the right way. This checkpoint first cited two of those rounds by path,
`tests/dead_pointers.py` failed in CI and passed locally, and the local pass was the
misleading signal — the working checkout carried the directories as untracked files
left by another session.

**Repaired on the same day, at the maintainer's instruction.** The stack was landed
as its own pull request: current `main` merged in, three additive conflicts resolved
as unions, generated views regenerated, no round document edited. The repository's
runner count went from thirty-five projects to forty-one. This checkpoint's path
citations are restored and `STATUS_LEDGER.md`'s Layer II rows cite the rounds
directly.

**What the episode leaves behind.** *Workspace friction* F8 is closed, but kept, for
the lesson: a merged badge names the base the pull request had, not `main`, and no
current gate checks that a round directory referenced anywhere reached the default
branch. Between the first draft of this checkpoint and its repair, the repository
asserted something false about its own contents, and the only reason it was caught is
that a citation happened to point at one of the missing trees.

## The September cleanup pass

A second dispatch on the same branch, after the answerability stack landed. It added
no theory and opened no research question. What it changed:

- **One prior-art reclassification, on evidence.** Gale–Hoffman / Horn moved from
  *adjacent prior art* to **direct mathematical dependency**, because
  `BOUNDED_DELAY_TRANSPORT.md`'s sufficiency proof invokes the feasibility condition
  by name. The previous entry said "we take nothing formally" while the proof took
  something formally. Every other §6 entry was re-checked against its proof by the
  same test — *would the canonical proof stand if this theorem vanished?* — and the
  rest held, with Farkas split into a self-contained soundness theorem and an
  LP-duality-dependent exactness remark.
- **Four citation repairs.** Pollock and Williams were pinned to exact works and
  verified. Pettit was demoted, then **removed**: the maintainer confirms no source
  was read for it, so it was not a dependency with a missing citation. The
  "Łukasiewicz" attribution was demoted, then partly recovered: on the maintainer's
  recollection it is Thomas Lukasiewicz, and the Biazzo–Gilio–Lukasiewicz–Sanfilippo
  coherence line checks out as the right family — de Finettian coherence with
  conditional constraints and a nonlinear-to-linear reduction, which belongs beside
  Walley and Levi rather than in a probabilistic-logic section. It is recorded as a
  **candidate identified, not confirmed read**, alongside the older Hailperin and
  Nilsson anchors. No entry was completed by guessing a plausible work; this one was
  narrowed by a maintainer recollection and then checked.
- **One terminology split**, applied throughout: *closed for research sequencing*
  now names the sequencing judgment and never the evidence, which is
  `STATUS_LEDGER.md`'s business.
- **Scope repairs** to `wiki/Legitimacy.md`, whose inherited record-and-inquiry
  status paragraphs read as global claims and contradicted the four-layer map.
- **One strength correction**: the EV1 / Proposition 8.17 comparison is labelled an
  interpretive analogue rather than a reduction, since no map between the systems
  was constructed.

## Web use

Seven bibliographic verifications, for `../../notes/PRIOR_ART.md`: the Gale–Hoffman
feasibility condition; Le Cam's contiguity definition and its date; Horn's 1974
preemptive-feasibility conditions; Jackson's 1955 earliest-due-date rule; Pollock's
1987 *Cognitive Science* paper on defeasible reasoning; Williams' 1975 conditional-
previsions report and its 2007 printing; and Nilsson's 1986 *Probabilistic Logic*
together with the Hailperin attribution behind the linear-programming
characterisation. Each is cited for a bibliographic fact and for the substance of a classical
statement, and each is used to record that a repository result is **probably a
rediscovery** rather than to import a theorem. No mathematical content was taken
from a web source.

## What is asserted and what is not

Asserted: that these documents accurately restate their sources; that the
supersessions listed are the ones the sources actually made; that the status
labels are not stronger than the sources support.

Not asserted: that the four-layer decomposition is the right one; that the
candidate legitimacy decomposition is correct — it is explicitly assessed as a
research framing; that the prior-art classification is complete, three entries
being marked **literature review needed**; or that any result here has been
independently reviewed. The repository default is `ci-only`, and it applies.
