# The argument map

A map of arguments about how the relationship between humans and AI
systems might go. Claims are nodes under `graph/nodes/`; a story about how
a claim fails is a row of a `cases` table; what humans have checked and
judged is one JSON line per act in `graph/events/<handle>.jsonl`; every
level, status, probability, value and task comes out of `checkers/graph.py`
and never goes into a file by hand. `graph/PROTOCOL.md` says how it all
works (its §9 lists every refusal the checker can make); the repository's
`AGENTS.md` says what an agent may do here.

## What is here to start from

The graph carries structure and two rulings, and no other judgment yet:
every root reads *no belief*, every table is a proposed draft awaiting a
human's one-word admission, and the first ranked tasks are two-minute
gestalts on the roots. Two clusters are filed: the deference line (the toy
collapse as a shared claim, and the bounded-agent programme as a sub-frame
over its steps) and the instrumental-convergence cluster (two risk stories
sharing the fixed-objective assumption). The outside option and the
undescribed-failure valuation are `cases` nodes over the outcome classes,
weighted equally by the maintainer's two `rule` events; argue a row's
weight and every plan's comparison moves. Everything the numbers will do
once judgments arrive is exercised by `tests/test_graph.py` on a synthetic
graph.

## First steps, with a coding agent

1. From the repository root, in the terminal: `python3 -m checkers.graph
   --root .` It prints one line, `OK <n> nodes, <n> events, <n> ranked
   units; <the commit line>`, on stderr, and regenerates the four committed
   files `graph/derived.json`, `graph/versions.json`, `graph/tasks.md` and
   `graph/view.md`. Those four are rendered the same way whatever flags you
   add, so a run never leaves personal noise in a pull request. A `WARN`
   line before the `OK` names something that passed but deserves a look
   (a malformed design-log line, a record without a claims registry).
2. To look without writing: `--print` prints the task list and the view on
   stdout and writes nothing; `--dry-run` prints the whole derivation as
   JSON on stdout for scripts, and also writes nothing.
3. Personal renders: `--why` adds the numbers behind the order (a `## Why`
   appendix), `--as @handle` renders under that user's presentation
   settings, `--scope <node id>` ranks inside one node's support. Each
   prints a task list and view on stdout, marked *not a committed file*;
   `--out <path>` writes it to a file instead, which must lie outside
   `graph/`. The committed files are written as in step 1 regardless.
4. Pick a handle (`@<name>`) and have your agent add it to `handles:` in
   `graph/policy.yaml` with your GitHub account and `kind: human`. Your
   ledger is `graph/events/<name>.jsonl`, and every event id in it begins
   with `<name>-` (so `@anson` writes `anson-001`, `anson-002`, …): ids are
   unique across all ledgers, and the prefix keeps two contributors' pull
   requests from colliding.
5. Tell your agent how you want things shown (numbers or only orderings,
   how much derivation to explain, whether audits are on); it records this
   as your `users:` entry in `graph/policy.yaml`.
6. Open `graph/tasks.md`. The top task is ranked unit 1 (the audit line
   above it is the session's audit share, never ranked). Do it in chat with
   your agent: it quotes the statement at its current version and the
   source passages; you say what you checked and did not, in your own
   words, and give a range. The agent writes that one event into your
   ledger and tells you what the answer is expected to change.
7. Rerun the checker, read the digest at the top of `graph/tasks.md`
   (statuses and root statuses that flipped, levels that moved, events
   counted since the last committed derivation), and open a pull request
   with your ledger and the four regenerated files.

Records of formal results (`leaf_kind: record`) reach level 4 only when
the checker is pointed at the claims registry of the line they belong to:
`--registry projects/<line>/CLAIMS.md`. Without it they wear the flag
*registry unchecked* in the view and cap at level 2.

The checker refuses rather than repairs: a number in a node file, a
judgment by an AI handle, a regenerated file edited by hand, a component
of roots too large to enumerate, or a missing `graph/DESIGN-LOG.md` stops
it with `REFUSE <rule> <path>: <reason>` on stderr; PROTOCOL §9 has the
rule numbers.

## When something does not make sense

Say so to your agent. The protocol is meant to be revised by use: a rule
that produces a confusing file, task or number is a finding, and the agent
is expected to ask you whether a step makes sense before and after taking
it, and to propose a change rather than work around the rule. Every change
to the design, every edit that had to be rolled back and every confusion
worth recording is one dated line in `graph/DESIGN-LOG.md`.

Everything under `graph/` and `chats/` is public, under handles.
