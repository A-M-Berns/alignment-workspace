# Provenance

| files | generator | review status | date | originating round | chat bundle |
| --- | --- | --- | --- | --- | --- |
| `*.md`, `src/*.py`, `tests/*.py` | Claude Opus 5 (Anthropic); prompt author Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-03 | `prompts/2026-09-03-defeat-landing-horty-standing/` | none |
| `lean/Workspace/Normativity/Contrib/NormativeContinuity.lean` §§5.2, 5.4, 5.7–5.9 | Claude Opus 5 (Anthropic); prompt author Claude Fable 5.1 (Anthropic) | `ci-only` | 2026-09-03 | same | none |

The dispatch names its executor `unrecorded`; the executor was Claude Opus 5.

## What this round consumed

**As hypotheses** (`depends_on`):

- `2026-09-02-unified-grounds-answerable-defeat` — the unified trace, `DefeatTrace`,
  D1–D3. This round repairs its `contested` clause and supplies the Lean witness its
  report named as missing.
- `2026-08-30-normative-continuity-settlement` — the settled `IssueTrace` layer, which
  the witness is built on and which is unchanged.

**Read, not consumed.** Sources for the prior-art check, with their status, because
the difference is the round's largest caveat:

| source | status |
| --- | --- |
| Modgil & Prakken, *The ASPIC+ framework for structured argumentation: a tutorial* | **read** (PDF, author's site) |
| Stanford Encyclopedia of Philosophy, *Defeasible Reasoning* | **read** |
| **Horty, *Reasons as Defaults*, Draft #2, 16 Aug 2006** (79 pp.) | **READ** — supplied by the maintainer mid-round, from `~/Downloads`, after the first pass had recorded the primary text as unreachable. Carries Definitions 1–7, fixed- and variable-priority theories, and threshold theories. |
| Horty, *Reasons as Defaults*, **OUP 2012** (the book) | **NOT read** — certificate mismatch on the author's host, blocked archive, paywall |
| Pollock, *Defeasible Reasoning*, 1987 | **NOT read** — `PRIOR_ART.md`'s recorded URL no longer resolves. Horty credits the distinction to Pollock **1970**. |

## What changed outside this directory

- `DECISIONS.md` — the Defeat Principle ruling; the reservation struck from *Awaiting
  the author*; the previous round's entry restated as unconditional.
- `PRIORITIES.md` — item 77 updated with the Horty verdict and what still blocks it.
- `projects/normativity/notes/PRIOR_ART.md` — §2's Horty, Pollock and ASPIC+ entries
  and the §7 dependency note; the dead Pollock link recorded.
- `projects/normativity/legitimacy/rounds/2026-09-02-unified-grounds-answerable-defeat/`
  — `THEOREMS.md`, `DEFEAT.md`, `REPORT.md`: the conditional qualifier struck and the
  `contested` correction recorded. **History is annotated, not rewritten**: the round's
  findings and verdict stand as written.
- `lean/Workspace/Normativity/Contrib/NormativeContinuity.lean` — the participant in
  `Licence` / `standsFor` / `contested`; §5.7 laundering on both sides; §5.8 the
  principal-relative form; §5.9 the witness. Eight new `#print axioms` lines.
- `state/rounds.json` — the round record.

## Web use

Three searches and six fetch attempts, all for the prior-art check, **including the
four that failed**. No mathematical content was taken from a web source: the sources
are used for what two published frameworks do and do not contain, which is exactly what
a prior-art check is for.

**The check was then redone against a primary text.** The maintainer supplied Horty's
2006 paper part-way through, and every finding was rechecked against it; two were
sharpened and none withdrawn. `HORTY.md` §0 records both states of the check rather
than presenting the second as if it had been the first — the failed-access record is
part of the provenance, not an embarrassment to tidy away.
