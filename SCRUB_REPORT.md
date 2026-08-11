# Scrub report — the note-dump bundles

2026-08-11. First-pass scrub of the frozen note dumps under the scrubbing rules
in `AGENTS.md`, performed so that the maintainer's read-through is a second pass
rather than the only one.

**This is not the release gate.** The gate is the maintainer's explicit
read-through sign-off, recorded in `DECISIONS.md`. It has not happened. The
repository is already public, at the maintainer's direction and with that
understood.

## What was cut

Two cuts, both **category 3** — candid assessment of a named person's abilities.
Both marked inline as `[scrubbed]`, with no category label, per rule 5.

| file | what went |
|---|---|
| `deference-note-dump-2026-06-27/anson-notes/trust-between-inductors-chats/10_2026-05-27_two-inductors-roadmap.md` | a remark about how quickly a named colleague would grasp a result |
| same file, the reply | the assistant's echo of that remark back to the author |

Both are frank assessments of a person, made in private, about someone who did
not participate in that conversation. Rule 3 sends those out and keeps technical
engagement with published work; the surrounding mathematics is untouched, and the
sentence each cut was embedded in continues from `[scrubbed]`.

`dose-response-note-dump-2026-07-02/` needed no cuts.

## Judgment calls, including the ones decided in favour of keeping

Rule 3 says "when in doubt, cut and flag". Where I kept something, the reasoning
is here so the maintainer can reverse it in their pass.

**1. The mentorship line — KEPT, flagged.** Three chat summaries open with a bio
line naming the author, his programme stage, and his mentor. Rule 3 lists
"mentorship characterizations" among the things that go. I kept it: it is the
author's own factual affiliation rather than an assessment of anyone's abilities,
and both people named are this repository's maintainers. **This is the call most
worth reversing if the author disagrees** — it appears in three files and is a
one-line deletion in each.

**2. Named cc'd non-participants — KEPT, flagged.** The email thread names two
people in its cc line who have no messages in it. They are disclosed as having
been in a private correspondence. I kept the attribution because removing it
would misrepresent who the thread was addressed to, and the thread is being
published by two of its four participants. **The two cc'd people have not
consented to publication**, and that is the author's to weigh, not mine.

**3. Technical engagement with named researchers — KEPT.** "X's claim about the
empty-process case, which I'm confused by"; "Y's conjecture". These are
engagement with published or stated positions, which rule 3 explicitly keeps.
Cutting them would gut the notes.

**4. A rendered-LaTeX theorem image — KEPT, after nearly cutting it wrongly.**
`email-thread-timely-tower-theorem.jpeg` is named as though it were a screenshot
of an email thread, and I removed it on that basis before checking. It is not: it
is a rendered LaTeX image of the "no timely tower on the diagonal" theorem,
extracted from the correspondence. That is technical content, which rule 4 keeps.
It was restored. **The general lesson: an image cannot be scrubbed by a text
pass, so filenames get checked against contents, not assumed.**

**5. The email thread itself — KEPT, already partly scrubbed upstream.** Its
transcriber's note records that email addresses and routing URLs were removed
before it entered the bundle. My own scan confirms no addresses, phone numbers,
API keys or home paths anywhere in either bundle — 51 files, zero hits across all
four patterns.

## What a scrub cannot do

**It cannot un-publish.** The bundles were public before this scrub, and the
unscrubbed content remains in this repository's git history and is reachable by
commit SHA. Removing content at `HEAD` does not remove it from the record; only a
history rewrite would, and that is blocked by branch protection, breaks the freeze
tags, and cannot recall what has already been fetched. **If either cut matters
enough to require erasure rather than removal, say so — that is a different and
much larger operation, and it gets less effective every hour.**

**It cannot judge tone.** Categories 2 and 3 are irreducibly human. I searched for
the markers a machine can search for — health, family, career deliberation,
evaluative language about persons — and the two cuts above are what surfaced. A
remark that is cutting without using any of those words is exactly what the
maintainer's read-through is for.

**It has not been reviewed.** This report and the cuts are `llm-unreviewed`.
