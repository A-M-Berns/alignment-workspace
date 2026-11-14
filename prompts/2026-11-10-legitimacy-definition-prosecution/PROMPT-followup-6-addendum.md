# Addendum to the sixth follow-up on PR #145 — a source and the concept map

Sent on 2026-11-14 while the sixth follow-up was running, at the maintainer's request. It
adds two housekeeping tasks and extends the write scope to cover them. It changes nothing
else in the dispatch.

## 1. Noggle's book as a source

File Robert Noggle, *Manipulation: Its Nature, Mechanisms, and Moral Status* (New Topics
in Applied Philosophy, Oxford University Press, 2025, doi:10.1093/9780198924920.001.0001)
as a source in the argument map under `graph/`, by whatever route `graph/PROTOCOL.md`
gives an agent for filing a source, and file the companion paper with it ("The Mistake
Account of Manipulation", *Journal of Practical Ethics* 14(1), 2026,
doi:10.3998/jpe.9951). A source is a bibliographic entry: **do not add the book's text or
any file of it to the repository.** Verify the bibliographic details before filing. Attach
the source to the nodes it bears on (the legitimacy line and this round), following the
protocol.

If filing needs an author handle that is not in `graph/policy.yaml`, do not add a handle;
write the exact entry under Outstanding maintainer actions instead, as the dispatch
already says for items.

## 2. The concept map

Update the concept network (`state/concepts.json`, and whatever the site contract in
`site/README.md` and `python3 -m checkers.workspace_state --check` require alongside it) so
that it reflects where the legitimacy line stands after this pass.

- **Trajectories.** Make sure the map has a concept for trajectories (the post's
  *histories*): whole courses of events, as the type of thing the principal's utility and
  her evaluation take as input. Check first whether a concept already covers it under
  "history" or another name; if so, extend that one and do not duplicate it; if the two
  names are both in live use, say which is primary. Link it to the concepts for her
  utility or evaluation, for legitimacy, and for the corrigibility score. Its blurb says
  what it is; it does not narrate what utility used to be defined on.
- **This pass's notions.** Add or revise concepts only for what this pass leaves
  standing, with the standing it leaves them (nothing is registered, so nothing is shown
  as established): manipulation as induced mistake, the two kinds of mistake, honest
  conduct as the adviser's reference, warranted self-trust as legitimacy. A notion the
  pass refutes gets no concept.
- Tag the merged-work entry for this pull request as the concept schema requires.

Every new concept name is provisional and is listed under new names in the report. Run
`python3 -m checkers.workspace_state --check`, `python3 -m checkers.graph --root .` and
`python3 site/build.py` (Python 3.12 or later) and commit only what the plain run writes
and the protocol says is committed.

**Write scope added:** `graph/` for the source and its attachments, `state/concepts.json`
and the structured state that must agree with it.

Report both tasks in the Sixth follow-up section, and name this addendum in the report's
account of the dispatch. If time is short, these two tasks come after questions 1–5 and
before the rest.
