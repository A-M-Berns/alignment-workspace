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

---

# Round 2 — 2026-08-11

**Judgment calls 1 and 2 above are reversed by maintainer decision.** The
mentorship bio line and the named cc'd non-participants are cut, not kept. The
sections above record what round 1 decided; this section records what supersedes
it, so nothing here should be read as still standing.

The scrub was also widened by a standing instruction: *anything more about the
maintainer and his career than about the research content goes.*

## The test applied

Passage by passage: **is this about the research, or about him?** Research
reasoning stays even when he is the one reasoning and even when it is addressed
to him in the second person. What goes is material whose subject is his
situation, standing, or trajectory.

## Cuts, by category

**A — non-consenting third parties (4 edits).** The two people named in the email
thread's cc line, who have no messages in it, are removed from the cc line and
from an acknowledgement in `notes/li-deference.md`. No initials or roles
substituted; the acknowledgement now reads "and others", and the cc line retains
the fact of a cc without identifying anyone.

**B — bio, affiliation, credentials (19 edits across 4 files).** Programme-stage
and mentorship framing, standing bio sentences introducing him to a model,
background and credential recitals, and two identity-management passages — one
instructing a model not to mention his programme, mentor, or a named
philosophical influence, and one echoing it back.

**C — self and career material (13 edits).** Five whole paragraphs whose subject
was his situation: a mentorship-and-funding-signal passage; a career-positioning
passage weighing which research direction is better placed with which audience
and which has more funding pathways; a mentorship-deliverable passage; a
funding-and-career passage naming specific funders; and a passage about what his
mentor would count as progress. Plus mixed-passage cuts described below.

## Mixed passages — where the seam was judged

Per the instruction, the personal clause was cut and the research argument left
standing, without rewriting to smooth the seam.

| passage | kept | cut |
|---|---|---|
| the propagation theorem as work that has to happen regardless of direction | the research argument entire | the clause about demonstrating competence to a named person and to grant committees |
| a conclusion that a direction does not deliver | the conclusion | the following sentences about grant timelines, meetings, deliverables, and the exhaustion of sitting in a stuck state |
| a hand-off instruction to a fresh model instance | the technical instruction | the parenthetical identifying the deliverable as a note for his mentor |
| a section heading reading "What this means for the meeting" | — | the heading, replaced by `[scrubbed]` |
| "the thing I'd actually want you to say to Demski, because he's exactly the person who…" | the intellectual content that followed | the characterization of the person |

## Judged and kept — with reasons, so they can be reversed

**"For the meeting with Demski: …" as an occasion frame.** Roughly a dozen
passages open this way and then deliver research content — what the negative
result is, why option B is the direction, that the computability assumption was
not actually relaxed. **I cut explicit mentorship management** — what the mentor
wants, whether he is enthusiastic, what a mentee owes at a given stage — **and
kept passages where the meeting is only the occasion and the payload is
research.** The alternative reading is that any sentence naming the meeting is
about him; on that reading a dozen more passages come out. **This is the largest
remaining judgment call and the one most worth a maintainer's eye.**

**A methodological passage advising a few days on a Bayesian sandbox** "as a
design tool, not the deliverable" was kept: its subject is which setting to
settle design questions in, not how he should spend his week.

**Technical engagement with named researchers** stays, per rule 3 — including
disagreement with a named person's stated claim, and a mentor's metaethical
concerns treated as a technical constraint.

**His name as an interlocutor** stays throughout. This is not an anonymization
exercise; he is a named maintainer of a public repository.

## Not found

No personal associates named as people in his life rather than as authors —
searched for friend/colleague phrasings and found none. No health, family, or
relationship content. No addresses, phone numbers, keys, or home paths, in either
bundle. The `dose-response-note-dump-2026-07-02/` bundle needed no cuts in either
round.

## One near-miss worth recording

A name-based sweep for one of the cc'd people matched `Roman10-Bold` and
`Roman12-Bold` in a PDF font table inside an unrelated transcript. A naive
substitution would have silently corrupted a font listing. Names were matched in
full and checked in context, not substituted globally.

## Coverage, honestly

The sweep was marker-driven: funding and grant vocabulary, mentorship and meeting
vocabulary, career and audience-positioning vocabulary, morale and
self-assessment vocabulary, bio and credential strings, and the specific names.
**A passage that is about him without using any of those markers would not have
surfaced.** The concentrations named in the dispatch were all found and worked;
the two heaviest files were read passage by passage at the hits. Nothing was
flagged as a whole-file removal: the two most affected files are long research
conversations with a recurring personal frame, not files predominantly about him.

## What this does not do

It removes content **at HEAD only**. The pre-scrub text remains in this
repository's git history and is reachable by commit SHA. That residue has been
assessed and accepted by the maintainer; this round does not attempt a history
rewrite.
