# PATCH ROUND — PRIORITIES rename and slop discipline

Extends the governance architecture; AGENTS.md rules apply. Read from the public
repo at `917c7da`. Confirm current state yourself; pointers are not a spec.

## A. Rename `OPEN_PROBLEMS.md` → `PRIORITIES.md`

`git mv`, then update every live reference. Fourteen tracked files outside
`frozen/` and `prompts/` mention it, including three code paths —
`checkers/registry.py`, `checkers/run.py`, `tests/path_gate.py` — where a missed
string breaks a gate silently rather than loudly. Also `README.md`,
`CONTRIBUTING.md`, `AGENTS.md`, `PROVENANCE.md`, `SETUP_REPORT.md`,
`GOVERNANCE_REPORT.md`, `.github/PULL_REQUEST_TEMPLATE.md`, and
`projects/leverage/README.md`. Files under `projects/leverage/forward/attic/` are
retired material — leave them.

Rewrite the file's own heading and any prose calling the items "open problems".
The framing shifts with the name: this file says what the program wants done next,
in its own order, not merely what happens to be unsolved. Difficulty tags stay.

No stub, no redirect note, no "formerly" line — per no-negative-ontologies. Round
records under `prompts/` keep the old name. DECISIONS.md gets the dated entry;
that is where the rename lives.

After the rename, confirm the gates still find the file: run the checkers and
path-gate suites and report that they exercised the renamed path rather than
passing on an empty match. A gate that silently stops checking looks identical to
a gate that passes.

## B. Slop discipline — new section in AGENTS.md, summarized in CONTRIBUTING.md

Why it belongs in a verification repository, stated first so the rule is not read
as taste: a reader who cannot tell which sentences carry content cannot audit; a
document that restates itself three ways hides its own errors; and volume inflates
the cost of the maintainer review the whole architecture depends on.

The rule, adapting the wording:

1. **Every sentence does work.** Cut restatement, throat-clearing, and previews of
   what the document is about to say. Prefer the shortest form that keeps the
   content.
2. **No padding structure.** Headings, tables, and lists are for material that is
   genuinely sectioned, tabular, or enumerable. A document that would be four
   paragraphs is four paragraphs.
3. **No inflated register.** No "comprehensive", "robust", "powerful",
   "seamlessly", "leverage" as a verb; no assertion of a result's importance in
   place of stating the result.
4. **Hedging is content or it is cut.** "May", "could", "arguably" are right when
   they mark a real epistemic state — and the epistemic classes exist to record
   that precisely. Hedging that softens a claim the writer will not commit to has
   no place in a record whose function is to say what is established.
5. **No summary of a summary.** Each deliverable ships a verification register and
   a human register; neither gets its own executive summary, and reports do not
   restate their findings in a closing section.
6. **Empty results are reported as empty** — cross-reference the existing rule on
   stating what was not shown; do not restate it.
7. **The maintainer may reject on these grounds alone.** A pull request whose
   content is correct and whose prose is padded is a legitimate rejection, said
   plainly rather than merged and cleaned up later.

Add: agent reports are deliverables under this rule. A 900-line report for a
40-line result is a round done badly.

## C. Bounded application pass

`README.md` (92 lines), `CONTRIBUTING.md` (207), `AGENTS.md` (494),
`PRIORITIES.md` (240). Read each against §B and cut what plainly violates it.
Report before/after line counts per file with what was cut.

Two constraints. Do not cut content to hit a number — if a document does not
violate the rule, say so and change nothing; do not manufacture edits to
demonstrate the pass ran. And do not cut anything a gate depends on: several
checkbox and field names in `CONTRIBUTING.md` and the PR template are parsed or
enforced, so verify against the scripts before shortening them.

Leave `prompts/` (history) and `frozen/` (immutable) alone. AGENTS.md is the
longest document and the one most likely to hold real duplication after five
rounds of amendment; it is also the binding document, so cuts there are removals
of restatement only — no rule loses force in this pass.

## Report

ROUND_REPORT.md per convention: the rename's full reference list including the
three code paths, the gate-exercise confirmation from §A, the AGENTS.md diff,
per-file counts from §C with what was cut, and any place where applying §B would
have cost content rather than padding — left in place and listed.

Under **Outstanding maintainer actions**, list anything reserved.

---
Prompt author: Claude Fable 5 (Anthropic), 2026-08-11, in a maintainer-directed
session. Dispatched by the maintainer.
