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

The top frame asks how the relationship between humans and AI systems goes
and what can be done about it; its owner is the maintainer. Under it sit
one plan and a set of risk stories:

- `trust-modelling`, the maintainer's research agenda, filed as a frame
  (a plan whose parts are plans): its lines along two axes,
  decision-theoretic stance (`updateful-trust-li`, `updateless-dt-programme`)
  and level of computability (`level-super-turing`,
  `level-above-quantifiable`, and `level-poly-time`, which is not opened),
  the cruxes the agenda names, and the abstraction arc as its later stage.
  Each line is in turn a frame over programmes, steps and shared claims,
  about thirty sub-frames in all, down to task leaves that name concrete
  work in the repository (a round, a `PRIORITIES.md` item, an open
  statement).
- Risk stories (the instrumental-convergence cluster among them), each a
  claim that some failure happens by default under stated conditions.
- Wants, inside the lines, each a state of affairs its owner wants,
  stated in research terms and weighted by the owner's priority word,
  never by an AI number. A want an agent filed from the
  owner's public writing (`filed_from: quote`) reads as medium and says
  *owner has not confirmed* until the owner gives the word.
- Beside most toy results, an improvement claim ("X can be improved until
  it reflects R well") with its routes, the research the map asks for.

Every number on a leaf, a row or a goal is an AI estimate or gestalt at the
bottom of the judgment ladder (J 0), with the generating agent's
reasoning in its `gloss`, argued from the claim's content and public
sources; no human has judged a node yet. A want carries no AI number and
the view shows no probability for it. The tables are
proposed drafts awaiting a human's admission. The outside option and the
undescribed-failure valuation are `cases` nodes over the outcome classes,
weighted equally by the maintainer's two `rule` events. Everything the
numbers will do once human judgments arrive is exercised on a synthetic
graph by `checkers/tests/test_graph.py`, run by `tests/run.py` or by
`python3 -m unittest discover -s checkers/tests -t .`.

The li-deference cluster (the logical-induction deference collapse, its
scoped refinements and its improvement claim) lives in the
`updateful-trust-li` sub-frame; `--scope li-deference-collapse` ranks
inside it, and `--scope li-deference-collapse@valid` adds the goals that
read the collapse as an implication.

## First steps, with a coding agent

1. From the repository root, in the terminal: `python3 -m checkers.graph
   --root .` It prints one line, `OK <n> nodes, <n> events, <n> ranked
   units; <the commit line>`, on stderr, and regenerates the four committed
   files `graph/derived.json`, `graph/versions.json`, `graph/tasks.md` and
   `graph/view.md`. Those four are rendered the same way whatever flags you
   add, so a run never leaves personal noise in a pull request, and the
   digest compares with the derivation committed at `HEAD`, so rerunning
   changes nothing. A `WARN` line before the `OK` names something that
   passed but deserves a look (a malformed design-log line, a work pointer
   to a round that is not in the repository, a Source naming private
   material).
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
   above it is the session's audit share, never ranked; the commit line
   is about which plan to commit to, not what to read next, and names the
   rank of the unit it favours). The header says in one sentence how the
   list is ordered. Each unit prints on two lines, plus a third with the
   work itself where the unit names one: what to do and, when it serves a
   goal other than its own target, which goal it is *for*; then its *path*
   from the top frame through the frames and goals down to the target
   (`→` a part, `⇢` evidence), so you can see what a ten-minute read
   serves before you do it. `## Research and whole-argument units`, above
   the list, gathers the best-ranked research units (improve, do,
   re-examine, spell-out, connect) with their ranks, since they rank far
   below the half-hour checks; `## By goal` further down is the same tree
   as an outline, one row per goal with its best unit. Do the task in chat
   with your agent: it quotes the statement at its current version and
   the source passages; you say what you checked and did not, in your own
   words, and give a range. The agent writes that one event into your
   ledger and tells you what the answer is expected to change.
7. Tell your agent what you want to see. It files a *want* under your
   handle (a claim such as "the toy collapse is written up with its proof
   kernel-checked"), as a root of the frame you name or of the top frame,
   connected to nothing if you have no view yet on how it connects; the
   list then offers you `spell-out` (read the agent's draft of the
   sub-goals and tasks under it) and `connect` (pick an edge or leave it),
   ranked like any unit, so they show in the printed forty or the research
   section only when they rank there (`--as @you` or `--all` shows the
   rest).
   Say one word, `high`, `medium`, `low` or `none`, and the agent records
   it as your `priority` on the want; it weights every task that informs
   it, and nobody but you can set it; no AI number goes on a want. A want
   an agent filed from words you wrote in a public document shows *owner
   has not confirmed* until you do; the pooled
   list prints one line per owner for these, and `--as @you` lists each
   with the start of its Source.
8. Pick an item from `## Agent work` when you want the map to move
   without you: these are task leaves whose `who` is `agent`, ranked by the
   same score, and your agent can do one on its own and show you the
   result, which you then confirm or send back.
9. Rerun the checker, read the digest at the top of `graph/tasks.md`
   (statuses and root statuses that flipped, levels that moved, events
   counted since the last committed derivation, wants filed, spell-out
   candidates, the agent work the map wants most), and open a pull request
   with your ledger and the four regenerated files.

Records of formal results (`leaf_kind: record`) reach level 4 when a
claims registry listed under `registries` in `graph/policy.yaml` holds
their statement of record as kernel-backed; the committed files read
those registries on every run, so no flag is needed. A record no listed
registry holds wears *not in a claims registry* and caps at level 2.
`--registry <CLAIMS.md>` adds one more registry to a personal render only.

Every number you see at first is an AI's: a line that says nothing about
it rests on AI judgments like every other (the list header says so once);
your range on the same quantity supersedes the AI's in the pooled number
and the AI's stays in its ledger as history. `--why` shows, for any unit,
the goals it informs with their weights, its minutes and bits, and the
full path.

The checker refuses rather than repairs: a number in a node file, a
level-minting event or a priority word by an AI handle, an AI estimate or
gestalt on a want, a regenerated file edited by hand, a frame without a
human owner, a node attached to nothing, one formula whose shared
variables need more than 2^15 assignments to evaluate, or a missing
`graph/DESIGN-LOG.md` stops it with `REFUSE <rule> <path>: <reason>` on
stderr; PROTOCOL §9 has the rule numbers, and `python3 -m checkers.graph
--self-test` runs every refusal's null input.

## When something does not make sense

Say so to your agent. The protocol is meant to be revised by use: a rule
that produces a confusing file, task or number is a finding, and the agent
is expected to ask you whether a step makes sense before and after taking
it, and to propose a change rather than work around the rule. Every change
to the design, every edit that had to be rolled back and every confusion
worth recording is one dated line in `graph/DESIGN-LOG.md`.

Everything under `graph/` and `chats/` is public, under handles, so the map
cites only what a public reader can open: published work, public posts and
this repository. Private material may shape what is filed but is never
cited, quoted or reported (PROTOCOL §7).
