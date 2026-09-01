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
- `projects/normativity/legitimacy/rounds/2026-08-25-carroll-legitimacy-test/`, at
  README and headline level;
- the *answerability carriers*, *anchored slices*, *faithful semantic preservation*,
  *CF-coverage* and *proper-exercise* rounds, at README and headline level, read from
  a working checkout. **They are not on `main`** — see *One finding about the
  repository itself* below — so they are named here without repository paths;
- `wiki/Deference.md`, `wiki/Corrigibility.md`, `wiki/Roadmap.md`,
  `wiki/CONVENTIONS.md`.

## The external input

*Diachronic Answerability Under Self-Revision — a calculus of provenance,
succession, semantic conservation, and service*, 31 August 2026, twenty-two pages,
supplied by the maintainer outside this repository. **Read in full**, all twelve
sections. It is not vendored here: it is an unpublished draft, and this checkpoint
cites it by section and theorem number rather than reproducing it. Since its three
repository counterpart rounds are not on `main`, the note is the only citable
statement of the Layer II results, and every such citation names it directly.

The note describes itself as a *"working mathematical synthesis; paper proofs, not
Lean-verified"*, and it is treated at exactly that strength throughout —
`STATUS_LEDGER.md` rows 36–45 record its results as **paper-derived**, and its
semantic-authentication and service assumptions as **interface assumptions**,
because the note itself declares them application-supplied.

**No blocker.** The file was available and was read; nothing in the consolidation
is conditional on an unavailable input.

## One finding about the repository itself

The note's three repository counterpart rounds — *answerability carriers*, *anchored
slices and authenticated semantic Transfer*, and *faithful semantic preservation* —
**are not on `main`**, and neither are the CF-coverage and proper-exercise rounds
beside them. Their pull requests are marked merged on the forge and were merged into
*each other*: the stack was based on `round/2026-08-30-liability-theory` and then on
`round/2026-08-30-answerability-carriers`, and nothing from the top of that stack to
`main` was ever opened.

It was found the right way. This checkpoint first cited two of those rounds by path,
`tests/dead_pointers.py` failed in CI and passed locally, and the local pass was the
misleading signal — the working checkout carried the directories as untracked files
left by another session.

**Consequences recorded rather than repaired.** Every Layer II citation here now
names the note by section and theorem number rather than a repository path;
`STATUS_LEDGER.md` carries a caution under its Layer II table saying that those rows'
exact fixtures do not run in this repository's CI and are paper-derived only from
`main`'s point of view. Landing the stack is a merge decision with its own review and
is filed as *Workspace friction* F8, not performed here.

## Web use

Four bibliographic verifications, for `../../notes/PRIOR_ART.md` §6: the
Gale–Hoffman feasibility condition; Le Cam's contiguity definition and its date;
Horn's 1974 preemptive-feasibility conditions; and Jackson's 1955 earliest-due-date
rule. Each is cited for a bibliographic fact and for the substance of a classical
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
