# Report — the personal lens: profiles, the you-annotation, receipts, recency

Shaped by a GPT-6 Astra design consult of 2026-11-09 (working material, not in the tree;
its adopted content is this report). Every page still renders identically for a
signed-out reader; the lens is client-side, from public JSON and this browser's storage.

**Profiles.** `/by/<handle>/` is a person's current position with history underneath:
avatar (the GitHub identity's image, an `<img>`, no script), kind and GitHub link,
"N concepts scored · M active axis scores · updated", then their active scores grouped
by target with rationales visible — the substance of the page — beside their wants and
owned frames, and their events as contribution history. An empty record reads "No
published scores yet." The owner, signed in on their own page, additionally gets a
client-rendered workbench: pending submissions ("Remembered on this browser; the pull
requests are on GitHub"), three what-to-score-next suggestions from the priorities
ordering minus their scored axes and pending proposals, and the link to the filtered
ordering.

**The you-annotation.** Signed in, every hero axis carries one quiet line beneath the
standing number: the reader's published score ("You: 4 / 5"), their pending proposal
("Proposed 4 · awaiting merge", linking the pull request), or the invitation. The
standing number's provenance labelling (the AI star and seed status) is unchanged. The
submit button is *Open the score PR*, and the receipt says plainly that the score
becomes public after merge and rebuild.

**Receipts.** A successful submission stores {event id, target, axis, score, pull
request} in this browser; the annotation and the workbench read it, and a receipt
retires itself when the build's active-event map carries that exact event id — the
reconciliation Astra asked for, against the event, never a matching number.

**The filter.** `/priorities/` gains *Unscored by you* (visible signed-in;
`?mine=1` arms it): entries where the reader scored every axis hide, the rest say which
axes are open, pending proposals excluded from "open".

**Recency.** ISO dates across the panels and profiles render relative with the exact
date on hover and focus; `/activity/` marks rows dated after this browser's previous
visit with an ink-token *new* label and one explanatory line, the boundary captured once
per visit, nothing invented on a first visit.

From the consult, declined or deferred, with reasons: polling GitHub for
closed-without-merge pull requests (needs per-view API calls; a receipt whose pull
request was closed unmerged therefore shows *awaiting merge* until the reader clears it
— the known gap of this design); the profile shell for a signed-in account no handle
maps to (every mapped handle has a generated page, and an unmapped account's chip
already says what is missing); skip-for-now memory on suggestions and the axis dropdown
(complexity ahead of any human score existing); reordering the activity panels to lead
with action items (the maintainer just ordered those panels by hand).

Friction found and fixed (contained, §14): `DECISIONS.md` reached `main` carrying git
conflict markers — a merge resolution had staged it unresolved, and no gate reads for
markers, so two CI runs passed it. The entries on both sides are kept and the markers
resolved; `tests/dead_pointers.py`, which already walks every live document, now fails on
a surviving `<<<<<<< ` or `>>>>>>> ` line, both directions self-tested. The dated
`DECISIONS.md` entry records it agent-decided.

Not shown: every personalization path runs against a ledger with zero human assessment
events, so the annotation, filter, workbench and scores data are exercised only by their
empty states and the build's own shapes; the first human scores are the test. The
recency boundary and receipts are per-browser facts and say so on the page.

## Attribution

Prompt-author: the maintainer, in conversation, kept verbatim (`PROMPT.md`). Executor:
Claude Fable 5 (Anthropic); design consult GPT-6 Astra (OpenAI), 2026-11-09.
