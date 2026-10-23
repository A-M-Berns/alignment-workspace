# The argument map: protocol

*The files under `graph/` hold a map of the arguments about how the
relationship between humans and AI systems might go. AI agents maintain the
map; humans contribute judgment in short recorded acts; the checker
(`checkers/graph.py`) derives every number from those acts. This document
is the protocol the checker enforces and the vocabulary every file under
`graph/` uses; the files already there are the examples of every format.
Each paragraph carries a register: **Decided** (the maintainer has ruled;
the brackets give the date where the ruling is recorded in
`graph/DESIGN-LOG.md`), **Default** (adopted so that something runs; the
maintainer may reverse it)
or **Open**. §8 is the glossary; §9 lists the refusal rules.*

**In brief.** At the top sits a *frame*, a node holding the shared question,
its human *owner*, and the list of *roots*: the claims directly under it,
which are plans, risk stories, the claims they share, and *wants*, states of
affairs a contributor wants to see, owned by that contributor. A plan that
is a line of research is itself a frame, so the frames nest into a *goal
hierarchy*: the top question, lines, programmes, steps, and under them the
concrete work, *task leaves*. Claims decompose into conjunctions and
alternatives; a story about how a claim fails becomes one row in a table of
exclusive scenarios (*pictures*), each with a *weight* (the probability that
the scenario obtains) and a *conditional* (the probability that the claim
holds given it); attacks and responses are edits to that table. A claim's
probability may be made to depend on another claim's through a *given*
edge, and beside every toy result sits an *improvement claim*, that the toy
can be improved until it reflects the real system. Every claim carries a
*vettedness level* from 0 to 20, derived from the acts of human checking
logged in per-contributor *ledgers* and kept apart from its *credence*. A
plan's *value* is its expected utility on a shared scale of outcome classes,
compared only with the *outside option*, committing to no plan. A *ranking*
proposes the next task by what it would teach about the goals it informs,
in bits weighted by what each goal bears on and how promising it looks,
prints each task's *path* from the top frame down to it, and reports beside
it what it would do for the choice of plan.

## 1. What this is for

The map shows which plans might work, which risk stories bear on them,
which claims they share, and for each piece how carefully it has been
checked, where it has been attacked and how the attack was answered, and
what the most useful next piece of work is. The goal is to map the space of
possibilities well: a crisp refutation is worth as much as a success, and
the map shows every live option with its standing. **Decided.**

**The frame tree is the goal hierarchy, and every task has a path.** The top
frame's question is deliberately broad, so that other agendas serving it can
be recognised; the maintainer's own research aim is one plan under it, filed
as a frame whose roots are its lines, each line a frame whose roots are its
programmes and steps, down to the concrete work. The ranker's output names
specific tasks, each shown as part of a path from the high-level goal
through mid-level goals to the task, and AI bridges the gap between the
high-level agenda and the concrete research going on in the repository,
whose activity shows how the agenda spells out. So every ranked
line prints its path from `top` through the frames and goals to the task
(§6), and agents file the concrete work as task leaves and `work` pointers
under the goals it serves (§2). **Decided** for the broad
frame, the owned wants and the paths; **Default** for the shape of the
hierarchy below the agenda's own items.

A claim's **status** is *open*, *established* (checked by a named human to
the frame's required depth, no admitted failure story standing) or
*conceded* (an admitted story in which it fails has been judged by a human,
after reading, more likely than not; §4). The **checker** validates every file,
refuses files that break a rule (it never repairs), and regenerates every
derived quantity into graph/derived.json (written on every plain run, not
committed), from which `graph/tasks.md` and `graph/view.md` are rendered. **Kernel-checked** means certified by the
Lean 4 kernel; "registered" means listed in a claims registry
(`projects/<line>/CLAIMS.md`) as `lean-proved`, `enumeration-verified` or
`witness-checked`. **Decided** for the three statuses and
what concedes; **Default** for the vocabulary of checking.

| file | holds |
|---|---|
| `graph/frame.yaml` | question, owner, outcome classes, roots with roles, settings |
| `graph/nodes/<id>.md` | one node per file; never a level, credence, status or number |
| `graph/events/<handle>.jsonl` | one append-only ledger per contributor |
| `graph/policy.yaml` | see the key list below the table |
| `graph/proposals/P-<n>.md` | structural proposals with a checker-computed delta |
| `graph/versions.json`, `tasks.md`, `view.md`; graph/derived.json, graph/index.json | the five *generated files*, regenerated by the checker, never edited, each carrying a `generated_hash` over its content; rendered the same way whatever flags the checker ran with. The first three are committed; `derived.json` and `index.json` are not (ruling F3, 2026-10-23: `.gitignore` excludes them, CI keeps them as artifacts and publishes `main`'s to the branch `derived`, and `versions.json` records each one's derivation hash under `generated`). `index.json` is the *structure-only index* (ruling M8, 2026-10-22): every node with its kind, fields, Statement, Source, Notes, narrative, pointers and edges, every frame with its roots and owners, the handles, the decision anchors and rounds the map points at, the narratives, and every event of every human ledger, with no derived number, level, status or rank; its schema is in `graph/MAP-AS-CANONICAL.md` §6.1 and every id in it is the id a URL carries |
| `PRIORITIES.md` (repository root) | a *render* of the map's item nodes (ruling M6, 2026-10-22), written by `checkers/priorities_render.py` on the plain run from `state/priorities_sections.md` (the standing preamble and each section's intro) and the item nodes in `maintainer_order`; `tests/run.py` gates that the committed file equals the render |
| `graph/DESIGN-LOG.md` | one dated line per design change, rollback or recorded confusion |
| `graph/MAP-AS-CANONICAL.md`, `graph/SURVEY.md` | the 2026-10-22 round's proposal document (the map as the program's canonical index: the ontology mapping, the governance of contribution, the schema of `index.json`) and its survey of every surface the map indexes |
| `chats/<session>.jsonl` | one agent session's transcript per file; events point into it |

**Keys of `policy.yaml`**, with what reads each. `anchor_rules`: the
version of the ladder of §3, the value every event's `rule` field carries
(`"2026-10-02.1"`: the date the ladder was fixed and a counter), recorded
and not yet compared. `floor_table`: the width floors of §3, read by the
belief computation. `rate_table`: minutes by task kind and size (`S`, `M`,
`L`) with `prior: true` until refit from logged `minutes`, one row per
unit kind of §6 (`map-read`, `trace`, `vet`, `admit`, `attack`, `revive`,
`reread`, `improve`, `do`, `spell-out`); read by every cost and rate.
`task_overhead_minutes` (3): added to a unit's minutes in its rate.
`read_error` (0.3): the probability a map-read misreads a leaf;
`improve_error` and `do_error` (0.3 each): the same for an `improve` and a
`do` unit, whose output is a draft; read by the ranking. The ranking's
weights (§6): `promise_exponent` (1), `stake_floor` (1/4),
`others_wants_weight` (1/2), `verdict_c` (0.2), `verdict_record_floor`
(0.15), `gestalt_mix` (1/2), `structure_suspect_odds` (4),
`suspicion_weight` (1/2), `ai_conjunct_threshold` (3). The task list's
shape (§6): `path_max` (8), `also_for_share` (1/5), `tasks_shown` (40).
Each of these is range-checked under rule 10 and is a prior until the
ledgers refit it. `registries`: the claims registries (`CLAIMS.md` paths
from the repository root) every derivation reads for anchor 4 (§3), so
that the committed files never depend on a flag; one naming no file is
refused under rule 10.
`evaluative_words`: the factual-form lint's list.
`maintainer`: a human handle or a list of them (ruling M1, 2026-10-22);
required, since `rule` and `survey` events are refused unless a maintainer
signs them, and anchor 18 reads any of them. `handles`: each
`{kind: human, github}` or `{kind: ai, model}`; every handle is a real
contributor, and every number in the graph comes from one of them. `users`:
per handle `{audits, show_numbers, alternative_calculations,
presentation_asked}`, the last an ISO date, the day the agent asked; read by
`--as`. `reask_days` (90) and `time_tested_years` (3): reserved for the
re-asking of stale judgments and for anchor 16; nothing reads them yet.
**Default.**

**Running the checker.** From the repository root, `python3 -m
checkers.graph --root .` lints every file under `graph/`, derives, and
writes the five committed files (and renders `PRIORITIES.md` from the item
nodes); it exits non-zero on the first refusal,
printed on stderr as `REFUSE <rule> <path>: <reason>` (§9), prints `WARN`
lines on stderr for things that pass but deserve a look, and ends with one
`OK` line on stderr. Nothing goes to stdout in a plain run. `--why`, `--as
@handle`, `--scope <id>` (or `--scope <id>@valid`, §2), `--all`, `--lambda
x`, `--window-dp` and `--frontier K` produce a *personal render*, a task
list and view for one user or one scope, printed on stdout (or written to
`--out <path>`, outside `graph/`); the committed files are still written as
in a plain run and are identical to it. `--print` prints the task list and
view and writes nothing; `--dry-run` prints the derivation as JSON on
stdout and writes nothing (for scripts and tests). `--registry <CLAIMS.md>`
adds one more claims registry to those `policy.yaml` lists, for a personal
render only (the committed files ignore it); `--today <date>` fixes the date;
`--self-test` runs the checker's own cases: every refusal's null input and
the synthetic graph's facts. A committed file edited by hand is refused
(its `generated_hash` no longer matches), as is a missing `DESIGN-LOG.md`
or a file outside the layout. **Default**, except that no number is typed
and the design log exists, which are **Decided**.

## 2. The graph

**The frame** (`graph/frame.yaml`) holds `question`; `owner`, the human
handle of the person whose question it poses, or a list of handles where
several people pose it (ruling M5, 2026-10-22; the top frame's question is
kept broad so that it represents the overall goals and lets other agendas
serving them be recognised); `narrative`, the wiki page that narrates the
frame (below); `classes`, the
*outcome classes*, named kinds of future each with a `utility` in [−1, 1]
(§4), a `severity` rank, the human `placed_by` and an optional `provisional`
mark; `valuations`, the ids of the *valuation nodes*, `cases` nodes read as
distributions over the classes (§4), among them `outside_option`, the node
valuing "commit to no plan" (the default trajectory of AI development with
no additional safety work), and `undescribed_failure`, the node valuing a
failure no filed story describes; the settings `bar`,
`establishment_level`, `dependence` (§4), `commit_level`, `window_minutes`,
`commitment` (§6) and `audit_share` (§5); and `roots`, each `{id, role,
preset}` with `success_class` on a plan and `budget` where the preset needs
one, or `{id, role: want}` for a want (below). The frame is a *node of
choice*: a question with options, so it has no probability, status or
value; its display is the map and its expansion policy is the ranking
(§6). An owner is a presentation and ranking input (`--as`, §6), never a
permission: anyone files under anyone's frame. **Decided**;
**Default** for every field name and value, and for the owner's role as
input only.

**Sub-frames: lines, programmes and mid-level goals.** A plan root may be
a *programme*: a node of kind `frame` whose children are its own roots, its
*steps*, listed in its `roots` field exactly as `frame.yaml` lists the top
frame's (plans with a `success_class`, shared claims, wants), with its own
`question`, its own human `owner` and, optionally, its own `outside_option`
(a valuation node of the top frame; absent, the top frame's is used). The
classes and the undescribed-failure valuation are always the top frame's.
Frames nest to any depth, and this nesting is how the agenda is filed: the
maintainer's research aim is a frame under the top frame, each of its lines
(a decision-theoretic stance at a level of computability) a frame under
that, each programme a frame under its line. A frame whose roots are not
yet spelled out has `roots: []` and `children: []`: it is *unspelled*, has
no status, value or proof set, is outside the plan decision, and its unit
is `spell-out` (§6). A frame marked `opened: false` records a line
deliberately not opened: it may hold shared claims and risk stories as
roots but no plan root, gets no `spell-out` unit, is outside the plan
decision, and the view prints *not opened; see Notes*. A step's status,
probability and value are derived as any root's; what the parent frame
reads from the sub-frame is in §4 and §6. A frame node is a root only as a
plan. **Decided** that
programme-shaped plans are sub-frames, that the agenda's lines and cruxes
are its first roots and that the top frame has an owner; **Default** that
every sub-frame has a human owner too (rule 2 refuses one without), for the
fields, for what the parent reads, for unspelled frames and for `opened:
false`.

**Shared roots.** A node two frames read, a plan or claim both lines build
on, is filed once and listed as a root of each frame that reads it (the
graph is a DAG, and a node may have several parents); the first frame in the
frame tree's order is its *home*, the frame its paths run through, and the
view prints *also a root of* the others. A want is a root of exactly one
frame, its placement being its owner's word; a node listed twice by one
frame, or with different roles by different frames, is refused (rule 1).
**Decided (2026-10-22, ruling M2)** that a root belonging to two lines is
filed once; **Default** for the home rule.

**Narratives and drafted frames.** `narrative`, on the top frame, a frame or
any node, names one `wiki/<Page>.md` page or a list of them, the pages that
narrate it; a page that does not exist is refused (rule 2), and the
structure-only index lists every page with the nodes it narrates. A frame an
agent drafted from a wiki page rather than from a maintainer's filing carries
`filed_from: wiki` and shows *owner has not confirmed (drafted from …)*
until its owner removes the field, which is how a drafted decomposition is
confirmed (ruling M3, 2026-10-22). **Default.**

**Roots.** A *plan* root says a described course of action leads to an
outcome in its `success_class`; a *risk story* says some failure happens by
default under stated conditions; a *shared claim* is a proposition several
plans and risk stories rest on, kept as a root so that settling it is
progress in itself; a *want* (below) is a state of affairs a contributor
wants to see. Every root carries a *preset* (§4; a want's is `worst-case`,
implied by its role) and a status; a plan root also carries a value and is
an option in the plan decision (§6); a risk story, shared claim or want
shows probability and status and enters the comparison through the plans
whose tables cite it. The first roots come from the maintainer's
research agenda as filed in the map (a plan under the broad top frame, its
lines along two axes, decision-theoretic stance and level of computability,
with its named cruxes as `cases` nodes and the abstraction arc as its later
stage) and from the repository's claims registries. **Decided.**

**Owned wants.** Any contributor may add and own more specific
wants without having a view on how they connect, so that contributors can
say what they wish to see. A *want* is a claim node with `want: true` and a
human `owner`: a leaf of `leaf_kind: want` while unspelled, or an `and`,
`or` or `cases` once spelled out (the mark stays). Its Statement is the
state of affairs its owner wants, in factual form and research terms ("The
li-deference results are written up with every proof kernel-checked."); its
id begins `want-`. It is a root of exactly one frame, role `want`, with no
`success_class` or `budget`, so it has no value and is outside the plan
decision; it has a status under the worst-case rule (§4) and no displayed
probability, and it is a *goal* of the ranking (§6), weighted by its
owner's *priority word*, one of `high`, `medium`, `low`, `none` (1, 1/2,
1/4, 0; unset reads as `medium`), given as a `priority` event (§5) that
only the owner writes; `none` disowns it. A want may be connected to
nothing: the ranking's `connect` unit then proposes edges and a frame to
move it to, and the owner, or anyone, confirms one or says to leave it
unattached. A want an agent filed from its owner's quoted words carries
`filed_from: quote` and shows *owner has not confirmed* until the owner's
first priority word; such a want sits under a line only when the quoted
words name that line, otherwise at the top frame. Another owner's wants
count in a personal render at `others_wants_weight` times their priority.
**Decided** that contributors own wants, which need not be
connected; **Default** for the shape, the priority words and their weights,
the placement of quoted wants and the weight of others' wants.

**A want carries a priority, not a forecast.** A want's Statement says what
is wanted; it never forecasts what a person will do, finish or endorse. No
AI handle writes an `estimate` or `gestalt` on a want, on a row of one or
on a field of one (rule 5), and the map computes no AI probability that a
want will be met: a want's promise in the ranking is a human's gestalt on
it where one is logged, else 1/2, never a number derived from the claims
under it (§6), and the ranking asks for no gestalt on it. An agent files a
want only from its owner's answer in the session or quoted from public text
the owner wrote; a want known only from private writings is not filed.
**Decided (2026-10-20).**

**Node kinds.** Below the roots is a directed acyclic graph of six kinds.
An `and` holds if all its children hold and carries exactly one
*completeness leaf*, a child saying "no unlisted conjunct is needed". An
`or` holds if any child holds: for belief it reads as a disjunction, any
child sufficing, unless it carries `tag: choose-one` (a choice between
deployments, read as its best child); for establishment one child suffices
and the cheapest is its proof set (§4). A `frame` is a sub-frame (above):
for status it reads as an `or` over its plan steps, for belief as its
leading step and for value as its best step (§4). A `leaf` has no children;
its `leaf_kind` is `assumption`, `hypothesis` (of a formal result), `record`
(the exact statement a formal result certifies), `bridge` (the claim that a
formal statement means what the informal claim it is cited for means),
`step` (one gap between a toy result and a real question), `question` (a
proposition nobody has yet argued for; infinite cost until it is given
children), `route` (one direction by which a toy result might be improved;
below), `improvement` (an improvement claim in leaf form; below), `task` (a
concrete piece of work; below), `want` (an unspelled want; above),
`picture`, `completeness`, `partition` or `terminal` (an early failure of a
named class ends a deployment). A `cases` node is a claim split into
pictures. A `choose` node is a choice point inside a plan that its executors
will decide, a choice for the decision machinery and alternatives for the
map; only under a plan root, with `decided_at` (`commit` or `runtime`) and
`committed` (a child id or `none`). **Decided** for
`and`, `or`, `leaf`, `cases`, `frame` and for `choose-one` against
either-suffices; **Default** for `choose`, the `leaf_kind` list and the
disjunction reading of an untagged `or`.

**Pictures: how claims are attacked and defended.** When the first story
arrives about why a claim might fail, the claim becomes a `cases` node: a
table of *pictures*, exclusive and jointly exhaustive scenarios, with one
*residual row* ("none of the above", `residual: true`) whose weight is the
remainder. Each row is `{picture, class, observable}` plus `residual: true`
on the residual row. `class` is the outcome class the claim's failure leads
to in that picture: a class id, a valuation node's id, or `null`, which on
the residual row means the frame's `undescribed_failure` node (a failure
nobody has described) and on any other row the outside option (§4).
`observable` says when the picture can be told apart from the others
(`never`, `at-commit`, `at-runtime`); parsed, not yet used. The claim's
probability is Σ w·p. A later story splits one row into sub-pictures
(`refines: <picture id>`; the old picture keeps its file with
`superseded_by` and leaves the table); a table past five rows is
re-examined. Picture statements are ordinary nodes with their own
vettedness; w and p are *judgments*, numbers a human gives (§3). A picture
is *admitted* once it is in the computations: at filing for a contributor's
own, at a human's `admit` for one an AI session drafted, *proposed* until
then. An *attack* lowers the claim's standing (add a picture, argue a weight
up or a conditional down); a *response* raises it. Any leaf may be split, a
completeness leaf or a bridge included, which is how an attack on an `and`
lands; the table's exclusivity and exhaustiveness are its *partition leaf*,
whose Statement names the rows, so adding a row changes it and bumps its
`version` (the agent's duty; the checker does not compare the two). When a
leaf becomes a table, a range judgment given on the leaf no longer fits (a
table's probability is Σ w·p): it is marked *stale: leaf became a table*,
enters no number, and is offered under the residual row's conditional as a
suggestion. A kernel-checked record has p = 1 in every picture, so stories
about a theorem land on its hypotheses or bridge. **Decided**, except the
partition leaf, `refines`, `observable` and the
stale-range rule, which are **Default**.

**Formal results.** An `and` of a *record* leaf (`statement_of_record`, the
registered declaration; `hypotheses`, its hypothesis leaves' ids, or the word
`unread`), one leaf per hypothesis with a `discharge` tag (`definitional`,
`proved-in-model`, `restates-conclusion`, `open`), a *bridge* with
`attribution` (`author-stated`, `formalizer-stated`, `reconstructed`) and a
completeness leaf. A hypothesis that restates the conclusion is held at level
0, so a theorem whose hypotheses do the work reads at level 0 with the reason
beside it. **Hypotheses are filed when read, not parsed** (ruling F1,
2026-10-23): a record whose hypotheses no one has filed by reading says
`hypotheses: unread`, its Source carries the declaration's signature verbatim
(binders included) so a reader has what to file them from, the result is then
the `and` of record, bridge and completeness leaf, and `derived.json`, the
index and the view flag it *hypotheses unread*; a list that mixes ids with the
word is refused. A record built from a registry entry carries `registry_id`
(the entry's id, which the index resolves to the node whatever the node's id)
and its `and` carries a `priorities` pointer to the item the entry's
`answers_item` names (ruling F2): the registry join is an edge, and the index
inverts it (`items[].answered_by`, `formal_result.answers`). **Default**,
following the repository's standard that a theorem ships as its statement,
its proof, its registry line and its bridge.

**Conditional tables.** A conditional probability table is allowed, X's
probability an affine function of Y's, with utilities kept spelled out
rather than derived from Y's. A claim leaf (of kind `assumption`,
`hypothesis`, `bridge`, `step`,
`question`, `route`, `improvement`, `task` or `want`) or a `cases` row may
carry `given: Y` or `given: Y@valid` (below), Y a claim leaf, `and`, `or`
or `cases` node, never a frame, a `choose`, a valuation node, a picture, a
partition or a completeness leaf; Y is the edge's *given parent*. The
judgment on the dependent node X then splits into two ranges, P(X | Y) and
P(X | not Y), the target fields `if-holds` and `if-fails` (`p-if-holds` and
`p-if-fails` on a row), ordinary judgments on the ladder of §3, and X's
probability is the affine mixture at Y's probability. A plain range on X
stands in for either conditional that has no judgment of its own, so
adding an edge to a judged node changes no number; the flag *given:
conditionals not judged* stands until both sides have their own. The edge
carries belief only: X's proof set, cost and load are those of the edge-free
tree, and Y's status moves X's status not at all (a given edge is
evidence, never a part). Where a judged edge has P(X | not Y) above
P(X | Y) the dependent root carries *interval not a bound (negative
evidential edge)*. Failure classes are spelled out per side: `class_given:
{holds: <class>, fails: <class>}` on a given leaf or row names X's failure
class in worlds where Y holds and where Y fails (a side absent falls back
to the row's `class`, or to untagged); a human `classify` may set them as
`class-if-holds` / `class-if-fails`. One parent per edge; a conjunction of
evidence is a `given` on an `and` filed for the purpose. A node reached by
a given edge alone is *attached* to the map (rule 1) and has no structural
path; its printed path runs through the evidence hop (§6). **Decided** that
conditionals are affine in the parent and utilities are
spelled out; **Default** for the fields, the fallback, the status rule and
the single parent; **Open** whether a table keyed on two parents is needed.

**Validity as an implication.** `X@valid`, for an `and`-shaped argument X,
names X read with every `assumption` and `hypothesis` leaf in its support
held true (`discharge: restates-conclusion` included): the implication the
argument establishes, apart from whether its premises hold of anything.
Pictures and rows are untouched, so a theorem valid only in one reading of
its setting keeps that reading's weight. `X@valid` is a legal `given`
target and a legal `--scope`; the view prints, on every such `and`, the
implication beside the literal claim ("as an implication P(X@valid) = …;
literally P(X) = …", numbers under `--why`). It exists because each node
is evaluated literally, which reads the toy's validity as a
good sign for its improvability, never as a condition of it, and because a
cluster whose literal toy multiplies out near zero can still be worth
improving: the implication is what the improvement routes condition on.
**Decided** for the reading; **Default** for the name and
the forcing.

**Improvement claims.** Every plan has, beside its literal
evaluation, a non-literal one pointing at it: that the plan can be improved
until it reflects reality well, an ordinary claim node with more detailed
cases (assumptions to relax, informal directions to take, changes of
formalism to represent specific things better); and it makes the toy's
validity a good sign for such research, not a requirement, since an invalid
toy can still be improved fruitfully. An *improvement claim* carries
`improves: <X>` and `reality: "<R>"`, R one noun phrase naming the system
the improved claim is to hold for, and its Statement follows one template,
"<X, in a clause> can be improved until it reflects <R> well."
(rule 3 refuses a Statement that omits the `reality` phrase). It takes one
of three shapes: a *leaf* of `leaf_kind: improvement`; an `or` over
*routes*, each one direction stated factually (a `route` leaf, an `and` of
gap claims with its completeness leaf, an improvement claim on a refinement
of X, or a literal claim about R), with exactly one `route` child marked
`residual: true`, the *residual route* ("some refinement not yet described
goes through"); or a `cases` table of *diagnoses*, exclusive readings of
what stands between X and R, each row's conditional the probability that X
is improvable given that this is the gap. A route or leaf-form claim
conditions on `given: X@valid` (or `given: X` where X is not an `and`),
never on X as a conjunct, since validity is evidence and not a condition
(the checker warns when the `given` lies outside X's refinement family). A
literal claim drafted as a refinement of another carries `refinement_of:
<id>`; a node a refinement supersedes keeps counting wherever a parent
still lists it and shows *superseded by*. An improvement claim is a
shared-claim root of the frame holding X's root, and every route, residual
included, is a goal of the ranking (§6). Route and improvement leaves are
never established by a check on themselves; the claim is established only
through a realised refinement (§4). **Decided** for the claim,
its cases and the role of validity; **Default** for the three shapes, the
Statement template, the residual route and the position.

**Task leaves and work pointers.** The bridge from the maintainer's
high-level agenda to the concrete research is left to AI: the
high-level ideas need spelling out, which is itself a task and can be
inferred from the repository's activity. A *task leaf* (`leaf_kind: task`)
is a concrete piece of work whose deliverable no existing claim captures;
its Statement says the deliverable exists with its stated property ("A
document lists the trust principles by axis, with the implication status of
each pair."). Required: `action`, one imperative sentence, the work to do,
and `who`, `human`, `agent` or `either`; optional `work` (below) and
`files`, the paths it touches. Its probability is *feasibility if
attempted*: the chance the deliverable can be produced with its stated
property if someone attempts it, never a forecast that someone will. It
hangs under the goal it serves as a route child of an `or` (one way to reach
the goal) or as the given parent of the claims its outcome bears on, and is
a conjunct only when the goal's Statement names the deliverable as a part of
what it claims, so that filing tasks never multiplies a goal's probability
down. It is established by a human `external` event whose `ref` is the
commit or file that delivered it, conceded through a `negation_of` partner
(the attempt failed and says why), and a finished task is superseded by the
node recording its result. Where the work *is* settling an existing open
leaf (a `question`, `step`, `route`, `improvement`, or a `hypothesis` with
`discharge: open`), that leaf carries `action` and `who` itself, an
*actioned claim*, and no task leaf is filed. `work: [{kind, ref}]` on any
node points at the work it stands for: `priorities` (an item number; it
resolves to the item node carrying that number, below, and is refused
otherwise, rule 1; on the item's own node it is redundant and warns), `open`
(a Lean declaration name), `round` (a round: a directory of the repository,
or a round id or path of `state/rounds.json`; a warning when it is neither),
`decision` (a maintainers' ruling: the anchor of a `DECISIONS.md` entry,
below; refused when no entry carries it, rule 1) and `foundation` (an id of
`state/foundations.json`, the inherited claim sets kept under their own
ledgers; refused otherwise). A pointer to material a public reader cannot
open is not filed (§7); the retired kind `private` still parses, with a
warning, until the map holds none. The ranking asks for a task as a `do`
unit, agent work in its own section (§6); neither list reorders the other.
**Decided** that AI bridges the agenda to concrete work; **Default** that the
work is filed as task leaves and pointers under the goals it serves, and for
the fields, the feasibility reading, the attachment rule and the pointer
kinds, and **Decided (2026-10-20)** that no pointer names private material.

**Item nodes.** Every entry of `PRIORITIES.md` is one node of the map
(ruling M6, 2026-10-22): a `task` leaf for a work order, a `question` leaf
for an entry of the ingenuity section, or whatever node already stood for
the item, with id `item-<n>` (`item-q<n>`, `item-f<n>`) and the fields
`item` (the number as a string), `title`, `section` (the `## ` heading it
sits under), `maintainer_order` (its position in the file, transcribed, not
a priority word), `difficulty` (the heading's bold bracket, absent on an
ingenuity or friction entry), `heading_notes` (the heading's trailing
annotations, verbatim), `project` and `dispatchable` (the
`workspace-priority` marker's values), `item_status` (`open` or `closed`,
read from the annotations), `deliverable`, `acceptance` and `context` where
the entry states them, and a `## Item` section holding the entry's body
verbatim. `PRIORITIES.md` is rendered from them (§1); an item node hangs
under the goal it serves as a route or as evidence, or, where no finer goal
is identified, as a route of its project's *docket*, an `or` that is a
shared-claim root of the line's frame. Item nodes are specification layer
(`tests/path_gate.py`, `.github/CODEOWNERS`). **Decided** for the render and
the transcription; **Default** for the fields and the dockets.

**Decision anchors.** Each entry of `DECISIONS.md` carries one machine line
(ruling M7, 2026-10-22): `<!-- decision: <anchor>; touches: <kind:ref>, …
-->` on the line after a settled entry's heading, or `<!-- decision:
<anchor>; touches: …; status: open -->` as the last line of a queued bullet,
the anchor `<date>--<slug>` or `open--<slug>` and `touches` the item numbers
(`item:87`), registry ids (`claim:…`) and node ids (`node:…`) the ruling
bears on, or `none`. The checker reads the anchors, refuses a `decision`
pointer that resolves to none, and warns on an entry no node points at. The
ledger stays the maintainers' prose record: an agent adds anchors and
pointers and rewords no ruling. **Decided (ruling M7)**; **Default** for the
comment form and the slug.

**A node file** (`graph/nodes/<id>.md`) is flat frontmatter, a
`## Statement` of one or two factual sentences in the claim's own terms, a
`## Source` pointing at the text it is drawn from, with a verbatim quotation
where the attribution is a reconstruction, and `## Notes`. The *factual-form
lint* refuses a Statement containing a word from the policy file's
`evaluative_words`. Fields on every node: `id`, `kind`, `children` (the only
edge; absent on a leaf), `author` (a *handle*, §3), `size` (`S`, `M`, `L`:
node and source read in under ten minutes, under an hour, longer) with
`size_reason` (one phrase saying why: "two passages, one page each"; for a
partition leaf "three rows to compare"; for a residual picture "every
system outside the other pictures"), and `version`, an integer bumped
whenever the Statement's *normalized text* changes: apostrophes and
quotation marks deleted, every other punctuation mark read as a space,
whitespace collapsed, case folded, so that a changed comma, apostrophe or
hyphen is no change. `graph/versions.json` keeps the history
and every human act records the version it was given against. Optional
fields: `source` (a path); `supersedes` and `superseded_by` (the node this
one replaced, or that replaced it; a superseded node may be parentless);
`refines` (§2, pictures); `tag` on an `or` under a plan root, `choose-one`
or `either-suffices` (how the decision term and the belief read it; absent,
belief reads a disjunction and an unranked `tag` item asks for it, set in
the node file, since the tag is structure and no event sets it; an
improvement `or` reads as `either-suffices` and needs none); `negation_of`, two
leaves that are one proposition under two signs, mutual attacks needing no
admission; `provisional: true` on a valuation node, printed wherever its
value feeds; `given` and `class_given` (conditional tables, above);
`improves`, `reality`, `refinement_of` and `residual` (improvement claims);
`action`, `who`, `files` and `work` (task leaves and actioned claims);
`want`, `owner` and `filed_from` (wants); `narrative` (the wiki pages that
narrate the node); the item fields (item nodes, above); and the per-kind
fields of §2 (`question`, `roots`, `owner`, `opened`, `filed_from: wiki`
and the optional `outside_option` of a `frame`). A node is *attached* when
it is a root of some frame, a
valuation node, listed in an attached node's `children`, or the given
parent of an attached node or of a row of an attached table; every
non-superseded node must be attached, and a top-frame root or valuation
node is listed in no `children`. A file containing a level, credence,
status, weight, conditional, value or utility is refused. **Decided** that no
number is typed; **Default** for the fields and the
attachment rule.

## 3. Vettedness

**Checks, events, ledgers.** A *check* is an act in which a named human
reads a statement and a source and records, in their own words, what they
verified and did not. Every check and judgment is an *event*: one JSON line
in the acting person's *ledger*, `graph/events/<handle>.jsonl` (the handle
without its `@`), append-only, written by the agent from the person's words
(§5). A *handle* is the name a contributor goes by; `policy.yaml` maps it to
a GitHub account and marks it `human` or `ai`; an AI handle writes
estimates and gestalts, which count at J 0 (below), and mints no level. A
node's *vettedness* is which checks have been performed on it,
by whom and how thoroughly, as a *level* V from 0 to 20, read beside its
*credence* and never blended with it; an event recording a number or an
acceptance and no act of reading moves credences and widths, never a level.
**Decided.**

**The ladder.** Anchors sit on the even numbers, each names an event that
must be in the ledgers, and no anchor is skipped. **Decided** for spacing
and derivation; **Default** for the wording:

- **0 generated**; **2 machine-checked**: the checker passes, the ceiling
  for an informal claim with no reader.
- **4 kernel-backed.** Validity only: the record's `statement_of_record`
  resolves in a claims registry (`registries` in `policy.yaml`) to a
  kernel-backed class (`lean-proved`, `enumeration-verified`,
  `witness-checked`); 2 without one. A registry entry is found by its id,
  its declaration's full name, or the declaration's last component where
  no other entry shares it.
- **6 map-read.** One named human read the node and a source and logged a
  *checked list*: what is claimed, in whose name, under which assumptions,
  that the labels are honest, and what was not checked.
- **8 traced.** One named human followed the argument step by step
  (validity) or checked that the formal statement captures the informal
  claim (reference), and logged what was not checked; installments display
  as a range, "6–8 (2/3)".
- **10 independently traced.** A second human, neither author nor first
  tracer, logged a trace. **12 broken-at.** A `pass` by a non-author whose
  checked list names every admitted picture under the node as answered or
  conceded.
- **14 externally scrutinized.** An `external` event, logged by a human
  other than the node's author, whose `ref` points at the outside record
  (a publication, a referee report, a public reply). **16 time-tested**
  (`retrospective`); **18 accepted** (`survey`, by the maintainer alone);
  **20** reserved.

Odd numbers are reserved for intermediate events named later under a new
version of the anchor rules, which every event carries as `rule`. **No
rounding:** a level is reached only when its criterion is fully met. Levels
0–4 are the machine's; 6 and above exist only as human events; 10 and above
need a logger other than the author. Each item of a checked list is *said*
(in the human's own words) or *approved* (the agent's draft accepted); a
level-minting event needs a said item in `checked` and a non-empty
`not_checked`. **Decided**, including that approval
alone mints no level (an anchor at 5 for approved-but-unread drafts was
considered and declined: it would display a level with no reader behind
it); **Default** otherwise.

**Levels after a revision.** In practice vetting usually produces a new,
longer and better draft that is itself unvetted,
so the output of vetting is seldom vetted material. So a level-minting
event counts toward the headline only at the Statement version it was
given against. The best level earned at an older version is kept beside
the headline as "read at vk" ("V 2 · read at v1: 6") with the flag
*revised since read (v1 → v2)*, and the list offers the cheap re-read: a
`map-read` unit on such a node is priced from the rate table's `reread`
row, and its prompt lists the items checked at the older version and the
word diff of the two normalized Statements. A human who revises a node
records the pass as a `revise` event (§5), flagged *human-revised (@h,
vn)*; an AI redraft is a version bump or a new node, never an event that
moves the node's number. Judgments keep counting across versions, flagged
*stale*, their floor read at the current level. **Decided**
that research outputs drafts, not vetted material; **Default** that an
older read stops counting rather than counting with a flag, for `revise`
and for the `reread` price.

**Two dimensions, flags.** A level is a pair, *validity* (established as
stated?) and *reference* (means what it is taken to mean?); an event's
`dimension` is `valid`, `ref` or `both`; the headline is the minimum with the
weaker dimension named. Flags beside it, none changing it: *under attack*
(a proposed picture awaits admission); *conceded by <picture or child>*;
*stale* (a judgment was given against an older statement version; it
still counts as a judgment, with the floor of the current level, where a
level-minting event at an older version counts for no level and shows as
*read at vk*); *revised since read (vk → vn)* and *human-revised (@h, vn)*
(above); *stale: leaf became a table* (§2); *attribution unvetted*, on a
bridge or any leaf with `attribution: reconstructed`, cleared by one thing
only: an `attribution` event on the node (§5) from a human other than the
author, who read the source the node cites and says `vouched` or
`disputed`, with a `ref` to what they read; a `disputed` verdict clears the
flag and sets *attribution disputed (@handle)* in its place; nothing in a
map-read, trace or external record clears it; *no belief* (a closure
leaf with no range, or a table none of whose rows is admitted or judged;
the inference holds it at 1/2); *withdrawn* (an event on the node was
withdrawn); *unread-weighted* (a J 6 judgment, §3); *AI number* (every
judgment on the node is an AI handle's); *registry unchecked* (a record
read with no claims registry listed); *not in a claims registry* (a
record whose statement of record no listed registry holds; it caps at 2);
*registry class C* (a registered record of a class that is not
kernel-backed); *provisional* (a valuation node marked
so); *given Y*, *given: Y established* / *conceded* and *given:
conditionals not judged* (a conditional table, §2), and on a root,
*interval not a bound (negative evidential edge)*; *superseded by Y*,
*refinement of X* and *improvement claim on X (reality: R)* (§2);
*unspelled* and *not opened; see Notes* on a frame, *owner has not
confirmed* and *disowned by owner* on a want (§2). **Default**, except the
attribution rule, which is **Decided**.

**A ladder for numbers.** Weights, conditionals, leaf ranges, the two
sides of a conditional table (`if-holds` / `if-fails`, `p-if-holds` /
`p-if-fails`, §2), gestalts (§4), class tags and dependence answers are
*judgments* on the *judgment ladder*
J: 0 *generated*, a number an AI handle wrote, with its reasoning in the
event's `gloss`; 6 a quick answer with no reason by a human who has not
read the target; 8 with a said reason or after a read; 10 two humans'
intersecting ranges (midpoint the mean, range their hull; ranges that do
not intersect keep the lower J, show their hull and raise a *reconcile*
task); 12 after a counted pass on the node. AI handles fill in the numbers
first and humans revise them where they seem wrong: a human judgment on a
quantity supersedes every AI judgment on it in the pooled number (the AI
events stay in the ledger as history, listed beside it), several AI
judgments with no human one pool at J 0 (mean, hull, no reconcile task),
an AI conditional concedes nothing (status needs J 8), and every display
marks a number that rests on AI judgments only: the node's flag *AI
number*, the root's line "rests on AI numbers", the ranked unit's "vet this
AI number". A judgment's displayed interval is at least as wide as the
*width floor* at the smaller of the statement's level and its own: 1 at 0–5,
0.50 at 6, 0.30 at 8, 0.20 at 10, 0.12 at 12, 0.08 at 14, 0.05 at 16, 0.03
at 18, 0 at 20, odd levels interpolating. A *gestalt* (§4) is the one
exception: a holistic judgment on a whole root, its floor is read at its
own J alone, since the root's level measures how far the derivation below
it has been checked, which is what the gestalt stands apart from. A quick
answer sets a midpoint at the floor's width, marked *unread-weighted*, and
the read's closing range supersedes it; a vetting event changes a width and
never a midpoint. **Decided** for the quick-answer
rule, the gestalt exception and the AI anchor; **Default** for the floors.

**Rulings on a table.** The maintainer may set a table's weights and
conditionals in one event of kind `rule` targeting the `cases` node, with
`rows` mapping each picture to `{w, p}` ranges (the residual row takes no
`w`; a row with a given parent takes `p-if-holds` and `p-if-fails` in place
of `p`, and never a `given` of its own, since an edge is structure in the
node file) and `ref` naming the ruling. The checker reads it as the
maintainer's J 8 judgment on every row named, admits those rows, and lets a
later `estimate` by the maintainer on a row supersede it like any judgment;
other contributors' estimates pool with it as usual. This is how the
valuation nodes of §4 get their first weights. **Default.**

## 4. Status and value

**Status.** The frame's *bar* is 0.5 and its *establishment level* 8. A
`cases` node is *conceded* when an admitted row's conditional is below the
bar at J 8 or above (a J 6 conditional concedes nothing) or its partition
leaf is conceded; *established* when its own level reaches the
establishment level and no admitted row is below the bar; else *open*. A
leaf is conceded when its `negation_of` partner is established, established
at the establishment level, else open; a `question`, `route` or
`improvement` leaf is never established by a check on itself (a route or
improvement claim only through a realised refinement), and a `task` or
`want` leaf only by a human `external` event at its current version (the
deliverable delivered, the state of affairs obtained). A want root takes
the worst-case rule, implied by its role. A row with a given parent is
tested at the side the parent's status settles (P(X | Y) where Y is
established, P(X | not Y) where Y is conceded, the mixture at Y's displayed
mid otherwise), and concedes only when every judgment used is at J 8 or
above; the given edge itself carries no status (§2).
An `and` is established when every child is and conceded when any is; an
`or` the reverse; an uncommitted `choose` reads as an `or`, a committed one
as its child; a `frame` (a programme) reads as an `or` over its plan steps,
so it is established when a step is and conceded when every step is, and
its shared-claim steps enter only through the plans that cite them. The bar
test is the only place a credence enters status. A conceded node carries a
*diagnosis* (the conceding picture or child) and a *revival cost*, the rate
table's `revive` minutes or the trace cost of a filed response that
`refines` the conceding picture; the revival itself is a ranked unit (§6).
**Decided** that one reasoned counterexample
concedes, that a programme is a sub-frame and that non-plan roots show a
status; **Default** for the rest.

**Presets are status rules.** A root's preset may concede it beyond the node
rules; moving along the row adds information and changes nothing logged.
The view shows an open `worst-case` root's *safety margin* (below) and a
`probabilistic` or `expected-utility` root's failure mass or expected loss
beside its budget; a root's digest line names a budget concession as such.
**Decided.**

| preset | concedes the root additionally when | needs |
|---|---|---|
| `worst-case` (default) | never | no numbers |
| `probabilistic` | failure mass Σ w·(1 − p) over the proof set exceeds `budget` | w and p |
| `expected-utility` | expected loss Σ w·(1 − p)·(U(success) − U(row class)) exceeds `budget` | class tags too |

**Proof set, costs, load, margin.** A root's *proof set* is the cheapest
way to establish it: every child at an `and`, the cheapest child at an `or`
or `choose`, a `cases` node with its partition leaf, a shared leaf once. A
leaf's *cost to establish* is the *rate table*'s minutes to reach the
establishment level: zero when established, infinite for a question, the
revival cost when conceded, map-read plus trace otherwise; a root's cost is
the sum over its proof set and its *disproof cost* the least `attack` cost
over its proof-set leaves. A node's *load* is the set of roots whose status
depends on it: roots in whose support it lies that are conceded once it is
conceded and not conceded once it is established (a root conceded for some
other reason is not its load). An open `worst-case` root shows its *safety
margin*: the least number of established proof-set leaves whose concession
would concede it. A proof set is unchanged by given edges. **Default.**

**Inference.** Probabilities come from an exact recursion over the *closure*
of a formula: the variables (leaves and `cases` nodes) reachable from it
through `children` (a committed `choose` reduced to its child, a frame to
its plan children, an `or` to all of them) and through `given` edges; the
sub-DAG is built once per formula. Each leaf of the closure holds with its
range midpoint (or with the side of its conditional table that its given
parent's truth selects), each `cases` node picks a row at the weights'
midpoints and holds with its conditional (a given row likewise by its
parent's truth), variables independent (`dependence`); the interval runs
from all conditionals low to all high. A variable reached by two or more
distinct paths is a *cutset* item: the recursion enumerates the cutset's
assignments and, under each, evaluates the rest as a tree, one upward pass
for the formula's probability and one downward pass for the joint mass of
every node in it with the formula, so that every unit's bits and decision
term are read from those joints and never by one enumeration per unit. A
node whose whole closure is reached only through it collapses to the single
binary "it holds", weighted by its own recursive evaluation. *Forcing*
restricts a variable's outcomes (a leaf to true or false, a table to a
subset of its rows) and is a factor on that variable alone, which is how
`X@valid` (§2), the value computation (below) and a unit's observation are
evaluated. One formula's cutset is capped at 2^15 assignments; a larger one
is refused under rule 13, which names the formula, the shared variables and
the count, and the remedies in order: make a conjunct shared across several
of the formula's children its own shared-claim root (sharing across goals
costs nothing; sharing inside one formula is what the cutset pays for),
coarsen a table, or move part into a sub-frame; the cap is never raised. The
enumerator of every world, kept in the test module as the oracle, is what
the recursion is checked against to the last fraction. A root whose closure
(its support plus its evidence parents) holds a variable carrying no
judgment has an undefined probability and value (*no belief*); a table none
of whose rows is admitted is held at 1/2 with no belief, and that propagates
to every root whose closure reads the table, through `children` or through a
judged `given` edge. The exception is a `given` edge whose child carries no
conditional of its own (a leaf with neither `if-holds` nor `if-fails`, a row
with neither `p-if-holds` nor `p-if-fails`): the child falls back to its
plain range on both sides, the parent cannot move its number, and the
parent's lack of a belief blanks nothing (§2, conditional tables). A ranked
`admit` on a table that blanks roots says how many (*blanks k roots*), and
the whole-argument read (`re-examine`) is offered on a goal even where a
leaf of its argument has no belief, saying which. **Default** for the
recursion, the collapse, the cap and the propagation; **Open** whether
independence is adequate, and whether a root resting on an unadmitted AI
table should show its number at the drafted rows with a flag instead of *no
belief* (a display choice for the maintainer).

**Value is expected utility.** Every number compared across roots lives on
the frame's class scale. A plan's value is its probability of success times
the utility of its `success_class`, plus each failure story's mass times the
utility of the class it names; in a world where several of its leaves fail
the worst named class counts, which the inference computes by *class-wise
forcing*: the classes a plan's failures can name (row `class`, a
`class_given` side resolved by its parent's truth, leaf class tags) ordered
by utility then severity, and the mass failing with worst class c read
from the passes that force the sets of worse-or-equal classes to hold. An
untagged failure is valued at the outside option; the residual row's
failure, the one nobody has described, at the `undescribed_failure` node.
A plan falls below the outside option only when its own failure stories
name worse outcomes. Every plan step is valued as reaching its success
class on success, an approximation accepted as one that may fit
some cases and not others, and grading by finer outcome classes needs no new
feature, only tagged failure stories. A `provisional` class or node widens
every interval it feeds to the whole scale. A risk story, shared claim or
want shows a probability interval and status, no value; the ±1 status
display is never compared with the outside option. **Decided** that expected
utility is the only value and the outside option the default trajectory;
**Default** for the forcing.

**Valuation nodes: the outside option and the undescribed failure.** The
*outside option*, committing to no plan, is the expected value of
default-trajectory AI development with no additional safety work. It is not
a number anyone types: it is the value of the `cases` node the frame's
`outside_option` names, `default-trajectory`, whose rows are the frame's
outcome classes, each row's weight the probability that the default
trajectory lands in that class and its conditional the probability that the
class is where it lands given the picture. Such a *valuation node*'s value
is Σ w·p·U(class) over its admitted rows, divided by Σ w·p (the mass its
rows describe), weights at midpoints; with equal weights and conditional 1
on every row it is the mean of the classes' utilities, 0 on the present
classes. "Failure nobody has described", the residual row of every table,
is valued likewise by the node the frame's `undescribed_failure` names,
`undescribed-failure`, over the same classes without the top one: mean
−0.25, a little worse than the default trajectory, since it is a failure.
Both nodes carry `provisional: true` and move when the classes or the
weights do; their weights are judgments like any row's, first set by the
maintainer's `rule` events (§3) and open to argument by anyone, and both
are attackable like any table. A valuation node whose rows are not all
judged has *no belief*: it reads as 0 with the whole scale as interval,
every plan's value interval is the whole scale, and the view says so. A
valuation node's rows name placed classes only. **Decided** that both are
`cases` nodes with these first weights; **Default** for
the renormalized form and the residual row's placement.

**A programme's value.** A plan root that is a `frame` (a programme over
its steps, §2) is valued in the parent frame as its best non-conceded
step's value, the derived expectation or a gestalt standing in; it has no
`success_class` and no gestalt of its own, and for belief it reads as its
*leading step*, the best non-conceded step by value, else the most
probable. Once every step is conceded it is worth the sub-frame's outside
option (the top frame's unless the frame node names another); while no
step has a value it has none, and its steps' gestalts are the first tasks;
an unspelled frame (§2) has no value and no probability. The parent frame
reads from the sub-frame exactly this value, the programme's status (§4,
an `or` over the plan steps), and the steps' units (§6); it does not read
the sub-frame's own commit line, regime sentence or ordering, which the
view prints under the sub-frame's heading (`## Sub-frame F (in P): <question>`,
in the frame tree's order, parents before children, after a legend that
says once what the block lines mean), and the sub-frame reads from
the parent its classes, its valuation nodes and, absent its own, its
outside option. **Decided** that a programme-shaped plan is a sub-frame;
**Default** that it is valued by its best step (the decision semantics of a
frame, applied to a sub-frame), for what the
parent reads and for the leading-step reading.

**Outcome classes, provisional.** The placed classes are the maintainer's,
held with high uncertainty: orderings may flip and the granularity may
exceed what arguments need. AI sessions may invent classes to represent
arguments; utilities, class orderings and `severity` come only from humans
given reference points, named in `placed_by`. **Decided.**

**Gestalt credences.** Any *goal* of the ranking (§6: a non-frame root of
any frame, an improvement claim, a route, a refinement, a want) may carry a
*gestalt*: a holistic probability for the whole of it (an event of kind
`gestalt` with `derived: false`; a human's, or an AI handle's at J 0 with
its reasoning, except on a want, where only a human's stands, §2), shown
beside the derived probability, standing in for a plan's value when the
derived value is undefined or the gestalt lies outside its interval,
setting the goal's *promise* in the ranking (§6), never entering status;
its displayed width follows its own judgment level alone (§3). A programme
carries none. A goal whose derived probability is undefined and which has
no gestalt is outside both ranking terms; its gestalt is the first ranked
task ("about two minutes"), except on a want, whose promise is 1/2 without
one (§2). A goal with a derived probability and no gestalt lists its
gestalt unranked, as "no gestalt yet", or earlier in the unranked block
where its number multiplies several unread AI guesses or sets the promise
of top-ranked units (§6). **Decided** that gestalts stay
out of status and that AI handles write them first (a want excepted, §2);
**Default** for the rest, including gestalts below the roots.

## 5. How work happens

**AI-maintained structure, humans in chat.** AI sessions file sources,
draft nodes, pictures, attacks, responses and checked lists, and run the
checker. The agent quotes the statement at its version, poses the task,
writes the event from the human's own words, says once what the answer is
expected to do to the map, labelled as an expectation, and offers the next
task or "stop"; the vocabulary beyond answers is "next / skip (reason) / why
/ stop". Chat is the first channel; an exported task list annotated offline
(`via: obsidian`) and voice confirmed in chat are the others, accepted as
labels. **Decided** for the order; **Default** for the
rest.

**The event line.** One JSON object per line. Its fields, with *checked*
marking what the checker reads and refuses on, and *recorded* what it
stores for people and later tooling:

| field | holds | |
|---|---|---|
| `id` | `<handle>-<suffix>`, the handle of the ledger without its `@`, then a suffix of the contributor's choosing (`anson-001`); unique across every ledger, so two contributors' pull requests never collide | checked |
| `by` | the handle; the ledger file is named for it | checked |
| `date` | ISO date; never decreases within a ledger | checked |
| `rule` | the anchor-rules version the event was logged under, `YYYY-MM-DD.n`, as `anchor_rules` in `policy.yaml` | checked (form) |
| `via` | `chat`, `obsidian` or `voice` | checked |
| `kind` | an event kind (below) | checked |
| `target` | `{"node": id}`, with `"field": "if-holds" \| "if-fails"` on a node with a given parent; `{"row": [cases id, picture id], "field": "w" \| "p" \| "class"}`, or `"p-if-holds" \| "p-if-fails"` on a row with a given parent, `"class-if-holds" \| "class-if-fails"` for a `classify`; `{"pair": [id, id]}`; `{"proposal": "P-n"}`; `{"event": id}` | checked |
| `version` | the Statement version the act was given against; older than the node's makes a judgment *stale* and a level-minting event count for no level (§3); above the node's is refused | checked |
| `from` | on `revise`: `{"version": n}`, n below the event's `version`, or `{"node": id}`, a node whose `superseded_by` names the target | checked |
| `dimension` | `valid`, `ref` or `both` (default) on level-minting events | checked |
| `checked`, `not_checked` | lists of `{"item", "how": "said" \| "approved"}`; a level-minting event has a said item in `checked` and a non-empty `not_checked`; anchor 12 and the attribution flag read the items' text | checked |
| `installment` | `{"done": k, "of": n}` on a trace done in parts; the level shows "6–8 (k/n)" until complete | checked |
| `estimate` | `[lo, hi]` in [0, 1]; a class id; `same`, `positive` or `independent` (pairs); `accept` or `reject`; on `priority`, one of `high`, `medium`, `low`, `none` | checked |
| `reason` | the human's stated reason for a number; its presence (any non-empty string) makes the judgment J 8 | checked |
| `derived` | `false` on every gestalt: the number is holistic, not computed | checked |
| `ref` | on `external`: the pointer to the outside record; on `attribution`: what the attribution was checked against; on `rule`: the ruling | checked (presence) |
| `verdict` | on `audit`: `agree` or `disagree` with the audited check; on `attribution`: `vouched` or `disputed` | checked |
| `rows` | on `rule` targeting a `cases` node: `{picture: {w: [lo, hi], p: [lo, hi]}}` for the rows the ruling sets (no `w` on the residual row); read as the maintainer's J 8 judgments, admitting the rows | checked |
| `verbatim` | the human's own words for the answer | recorded; checked against the chat turn when `answer` is present |
| `gloss` | the agent's reading of the answer, kept apart from it | recorded |
| `minutes` | time the act took, for refitting the rate table | recorded |
| `attested_by` | `{"session", "model"}` of the agent that wrote the line | recorded |
| `question`, `answer` | `chats/<file>.jsonl#t<n>`, turns of one chat file; optional, checked when present | checked when present |

A range on a map-read or trace is both the level event and the reader's J 8
judgment; `withdraw` names an earlier event by the same handle; `rule` and
`survey` are the maintainer's. An AI handle writes `estimate` and `gestalt`
events in its own ledger, each with its reasoning in `gloss` (refused
without), counted at J 0 (§3); it writes no `map-read`, `trace`, `pass`,
`external` or `attribution` (levels record who has read what, which is
human work), no `admit`, `approve`, `classify` or `identify` (acceptance
and tagging are a human's), no `revise` and no `priority` (a revision pass
and a want's weight are their human's). **Decided** as to
shape and for what an AI handle writes; **Default** for the field list and
the id form.

**What an AI number rests on.** An AI handle's `gloss` argues from the
claim's content and from sources a public reader can open. A person's
confidence, doubt, progress, reading or feelings is no evidence about a
claim and appears in no gloss: where a number leaned on one, the agent
re-estimates from the content and says why. No AI handle forecasts a named
person's actions (whether someone will write, finish, read, endorse or
reply), and no gloss or node says what a person has or has not read, done,
drafted, started or settled. **Decided (2026-10-20).**

**Event kinds and task kinds.** An *event kind* is what a ledger line
records; a *task kind* is what the task list asks for. Most coincide.
Event kinds, with what they mint: `map-read` (V 6, J 8 on the closing
range), `trace` (V 8), `pass` (V 12), `estimate` and `gestalt` (J 0, 6 or
8), `admit` (a draft enters the computations; no V), `classify` (an outcome
class or a `class-if-holds` / `class-if-fails` side; J; an `or`'s
`choose-one` or `either-suffices` is its `tag`, set in the node file),
`identify` (whether two leaves are one assumption or
co-vary; J on the pair), `approve` (a proposal may be applied), `audit` (a
past check re-performed without seeing its verdict: `target.event` names
the check, `verdict` says whether the auditor agrees; it moves no level or
number and is counted per auditor as calibration data), `withdraw`,
`external` (V 14; on a task or want leaf, its establishment), `attribution`
(a human other than the node's author read the source the node cites and
says whether the node's attribution is honest, `verdict: vouched |
disputed`, with `ref` to what was read; it is the only event that clears
the *attribution unvetted* flag and mints no level), `revise` (a human's
revision pass on a node, §3: no level, no judgment, the flag
*human-revised* and a per-handle count), `priority` (a want owner's word
on their want, §2: no level, no judgment, the want's weight),
`retrospective`, `survey`, `rule` (a maintainer's decision; with `rows` on
a table, the maintainer's judgments on its weights and conditionals, §3).
Task kinds that are not event kinds, because their outcome is recorded as
other events or as files: `vet` (a map-read then a trace, valued as one
unit), `revive` (argue the conceding conditional of a table back above the
bar; its outcome is an `estimate` or a response picture), `re-examine`
(read a node's analysis as a whole and say whether it holds; a finding,
then a revised draft or a proposal), `reconcile` (two humans' ranges on
one target do not intersect; each re-estimates), `improve` (relax an
assumption, change the formalism, take an informal direction, or critique
and redraft; its outcome is a draft an agent files), `do` (the work of a
task leaf or actioned claim; its outcome is the deliverable and, once a
human confirms it, an `external`), `spell-out` (read an agent's draft of a
want's or frame's sub-goals and tasks and say which stand; its outcome is
node files) and `connect` (choose among an agent's proposed edges for an
unattached want, or leave it; its outcome is a `given` edge or a move). A
`reread` is a `map-read` at a different price (§3). Tasks are rendered by
the checker over the node's committed fields, with AI-drafted text prefixed
`DRAFT:`. **Decided** for `attribution`; **Default**
otherwise.

**Unilateral action; no second person.** A contributor's own filings count
at once. A picture an AI session drafted enters the table once any human
accepts it by one word, including the human whose session drafted it; the
acceptance mints no level. An AI session's numbers need no acceptance: they
count at J 0 the moment they are filed, marked as AI numbers until a human
revises them (§3). Others contest a row by arguing its judgment the other way
(a disagreement; status waits on the reconcile task), by attacking the
picture statement, or by asking the maintainer to rule; nobody removes
another person's row. The same holds of structure: anyone files a frame
under anyone's frame, a given edge, a route or a task leaf, and a want's
connections; only the want's own position and priority are its owner's
word. A second person's confirmation may be required once the group is
larger. **Decided** that none is required now; **Default** for
the acceptance rule and the contest paths.

**Withdrawal, self-correction, audits, refuted nodes.** A person who decides
an earlier act of theirs did not count withdraws it through the agent, with
no notes beyond the commit message, and the level recomputes; a flaw an
author finds in their own *claim* is a picture in its table. An *audit*
re-performs a randomly chosen past check without showing the auditor the
verdict; it is a per-user setting, on by default, one contributor
re-performing another's check preferred; the frame's `audit_share` of each
session is listed first and never scored. A conceded node stays live with
its diagnosis and revival cost, because it may be revived; long-conceded
nodes may be cleaned up during a deliberate re-examination, never urgently.
**Decided**; **Default** for the audit share.

**What an agent does alone, and what it must pose.** Alone: file sources;
create node files at level 0 (adding structure cannot raise a root),
frames with their lines and steps, improvement claims and their routes,
task leaves and actioned claims, `work` pointers, given edges and
refinements; file pictures, rows and responses as drafts; draft checked
lists; draft the sub-goals and tasks a `spell-out` asks for and the edges
a `connect` offers; sharpen vague statements, bumping `version`; compute
proposals; run the checker; write the digest; and fill in numbers,
estimates and gestalts, the two sides of a conditional table included, in
its own ledger at J 0 with its reasoning in `gloss`, so that the map has
numbers to start from and humans revise the ones that seem wrong. Only
from its human's answer: a human judgment, an acceptance, a vetting event,
an attribution verdict, a withdrawal, a `revise`, a `priority` word, and a
want, filed under that human's handle as owner (with `filed_from: quote`
when the words are quoted from a public document the human wrote rather
than said in the session), written in that human's ledger. Never: a
utility, a class ordering, a severity order, a `rule`, a priority word, or
an edit to a generated file. A *proposal* (`graph/proposals/P-<n>.md`: a
`kind` such as merge, split or new-root, `targets`, `ops`, a `## Change`
paragraph and a `## Delta` the checker fills with each affected root's
cost, load, status and value before and after) is applied only after a
counted `approve` when its delta could raise a value or lower a cost, and
may be applied on filing when it only adds structure, cost or width.
**Default**; the finer grain is **Open**.

**Dialogue, revision and the design log.** This protocol is young, and the
way to find its faults is to use it on real research. An agent working
against `graph/` asks its user whether a thing makes sense before acting on
it and whether the result made sense afterwards, says so when a rule
produces a file or a number the user finds confusing, and proposes a
revision of this protocol when use shows a problem, in chat or as a
proposal, rather than working around it. Every design change, rolled-back
edit and recorded user confusion is one line in `graph/DESIGN-LOG.md`:
date, `change`, `rollback` or `confusion`, handle, one-line reason; the
checker requires the file and warns on a malformed line. The log makes the
cost of this malleability visible: when rollbacks and confusions accumulate,
or once the design has settled, the encouragement to revise is scaled back.
**Decided.**

**Presentation is each user's own.** Before its first task with a user, an
agent asks how that user wants information presented (numbers or only
orderings, how transparent to be about the derivation, whether to show
alternative calculations), unless a user-specific `CLAUDE.md` or `AGENTS.md`
in the agent's context already records this. The answers are the user's
`users` entry in `policy.yaml`; `--as @handle` renders under them, and
weights that user's wants in full (§6). **Decided.**

## 6. What to work on next

**Two decisions, kept apart.** The map serves *what to research next* and
*what plan to execute*. The ranking values a *unit* of work by a *map term*,
what it teaches about the map, and reports beside it a *decision term*, what
it does for the eventual choice of plan. For acting, the options are the
plan roots, at every depth of the frame tree, with a defined value (or a
gestalt standing in) that are not conceded, each refined through its
`choose` nodes (a committed child is taken, else the best child), plus the
outside option; a programme enters through its steps, each a non-conceded
plan step with a value being an option in its own right (committing to the
programme is committing to its best step, so the decision term treats the
steps as the parent's units), and a sub-frame's own outside option, where
it names one, is an option too; a conceded plan leaves the option set
until revived and the commit line says so; wants, risk stories, shared
claims and unspelled or not-opened frames are never options. For
research, any node may be examined, internal nodes and roots included.
*Commitment* is the point where
resources the research cannot take back are spent (a training run,
deployment-like activity). `window_minutes` (360) is the span the planner
schedules exactly; `commitment` is a distribution over researcher-minutes
before the act is forced, each mass with its forcing event (a placeholder
point at 200 researcher-hours until the maintainer states one). The planner
stays myopic, a handful of researcher-hours at a time. **Decided**;
**Default** for the window and the placeholder.

**Units.** Each unit is a piece of work on one *target* and is ranked by
the objective below. The checking units: `vet` (a map-read followed by a
trace, valued at its end) on any proof-set element below the establishment
level; `trace` alone from level 6; `map-read` alone, a noisy observation
with error `read_error` (priced from the `reread` row on a node read at an
older version, §3); `revive` on a conceded table (the table a conceded
plan's diagnosis chain ends at, or any conceded table on a proof set; on
the root itself when a preset's budget alone conceded it): arguing the
conceding conditional back above the bar, priced at the revival cost and
valued, like a vet, as an exact observation of the table's truth;
`gestalt` on a goal with neither a gestalt nor a derived probability,
listed first. The research units, whose output is a draft and which are the
cases of an improvement claim: `improve` on an
open `step`, `question`, `route` or `improvement` leaf without an
`action` ("relax an assumption, change the formalism, take an informal
direction, or critique and redraft"), an
observation of the target's truth with `improve_error`, priced from the
`improve` row; `do` on any open leaf carrying an `action` (a task leaf or
an actioned claim), its text the action and its work pointers, an
observation with `do_error`, priced from the `do` row; a unit whose `who`
is `agent` ranks by the same score in the *Agent work* section (below) and
is never asked of a human. The drafting units, each a read of an agent's
draft with `read_error`, priced from the `spell-out` row: `spell-out` on a
childless want, a leaf-form improvement claim or an unspelled frame (the
agent drafts sub-goals and tasks from the repository's own activity; the
human says which stand), in place of the target's map-read while it has no
children; `connect` on an unattached want (the agent proposes edges and,
for a want sitting in the top frame, a frame to move it to; the human
confirms one or says to leave it). The admission unit, `admit`, ranked on a
table with proposed rows as the read of its rows ("read the rows and say
which enter"), valued as an observation of the table's truth with
`read_error`, priced from the table's `map-read` row, with the one-word
*quick admit* beneath it in the unranked block, saying what admitting the
rows unread would move each goal from and to. The structural unit,
`re-examine`, ranked on every `and`, `or` or `cases` goal that carries a
gestalt ("read its analysis as a whole and say whether it holds, or file
the structure that reconciles the two readings"), also where a leaf of the
argument carries no belief (the signal *no belief on x; the read also
prices it*), valued as a read of the goal's truth at the prior
`gestalt_mix` between its shrunk derived and gestalt readings, priced from
the `trace` row, and carrying the signal *structure suspect: derived x
against gestalt y* where the two readings' odds differ by
`structure_suspect_odds` or more; this is the unit that lets a promising
argument filed as a long conjunction of unread guesses be read whole, which
no leaf unit does. A programme's steps are units in the parent frame's list
like any root's elements. The *unranked block*, in this order, each line
naming the goals it informs and the goal it sits under: a `priority` line
for every want whose owner has given no word ("say high, medium, low or
none; unset reads as medium", or "confirm or disown" for a quoted want,
each with the first words of the want's Source; the pooled file prints
one line per owner, "N wants of @h await a priority word", and `--as @h`
lists h's wants one by one),
by the weighted goals the want informs; then, never on a want, a `gestalt`
on every `and` goal whose derived number multiplies
`ai_conjunct_threshold` or more conjuncts that rest on AI numbers alone and
which has no human gestalt ("the derived number multiplies k unread
guesses"), a *promise gestalt* on every other goal whose promise rests on
AI judgment and which carries the largest share of a unit in the top ten
("it weights units n, m"), and the "no gestalt yet" gestalts; `estimate`
lines on rows and leaves below J 8, each ending "or read first: ranked unit
n" where that read exists; then `classify` (a row's class, an
uncommitted `choose`), `tag` (an untagged `or` under a plan, not an
improvement `or`), the quick admits, `reconcile`, `approve`, the structural
re-examination of a table past five rows, and `connect` on every one-leaf
shared claim or risk story no goal reads (file it into the argument it
bears on, or say it stands alone). The `## Lines` block above the ranked
list holds the *commit line*, the *regime sentence* and the *act line*
(below) and the *audit line*, `audit (<minutes> min of this session):
re-perform <event> by <handle>; cross-audit preferred`, the session's
`audit_share` of `window_minutes`, listed first and never ranked (one
contributor re-performing another's check is preferred to a self-audit; the
draw is fixed for the day). The top task is ranked unit 1; the commit line
is about which plan to commit to, not what to read next. **Decided** for
read-first admission, examinable internal
nodes, the research units' cases and the agent's bridging; **Default** for
every unit's price, error and placement; chains of units (an `improve` then
the `vet` of its draft), bundles and dependence questions are **Open**.

**The objective.** A unit's score is the information it is expected to
yield about each *goal* its target informs, weighted by what that goal
bears on and by how promising it looks, summed over those goals, per hour
of the unit. The ranking is to put first the vetting of what is
especially central or especially promising as a picture to refine, mixing
the most promising ideas with the most suspicious ones (those most in need
of a human reader), mostly promising first because so much unvetted material
may prove valuable; a poor allocation is to be met by
improving what the formula measures, such as weighting a root's status bits
by what they bear on, never by imposed shares. So:

```
score(u) = Σ_{g ∈ G, x informs g}  w_g · Δbits_u(g)  /  hours(u)
  w_g     = stake_g · (π̂_g ^ e + s · [g structure suspect])
              (e = promise_exponent, 1; s = suspicion_weight, 1/2)
  stake   : plan (U(success_class) − E[U | failure])/2 | want: owner's
            priority | improvement claim, route, refinement: largest
            stake of the plans and wants reading it or its claim's
            family | risk story, shared claim: largest stake of a goal
            reading it × the share of that goal's entropy its truth
            settles | at least stake_floor (1/4)
  π̂      : gestalt on g, verdict-shrunk, if logged; else, for a want,
            1/2; else derived P(g) in the verdict model; else 1/2
  Δbits   : H(T_g) − E_o H(T_g | o), in the verdict model, o the unit's
            observation of its target
  hours   : (task_overhead_minutes + rate_table[kind][size]) / 60
  D       : printed under --why, never added
```

The *goals* G are every non-frame root of every frame (plans, risk
stories, shared claims and wants at every depth), every improvement claim
and every child of an improvement `or` (the residual route included), and
every node carrying `refinement_of`; frames, other internal nodes, other
leaves, valuation nodes, `choose` nodes and task leaves are not goals. Two
exceptions. A shared claim or risk story that is one leaf with no `given`
edge, a single sentence rather than an argument, is no goal of its own: a
check of it counts through the goals that read it, and one that no goal
reads is listed unranked as `connect` (file it as a part, picture or given
parent of the argument it bears on). And the roots of a frame marked
`opened: false`, at any depth, with the nodes only they contain, are goals
only under `--scope` of that frame. T_g is g's *settled truth*, the status
it would reach if its proof set were vetted to the establishment level,
over the inference of §4. A node *informs* a goal when the goal's closure
reads it, through `children` or `given`, itself or as the implication
`X@valid` (X's truth implies its validity); a node informing several goals
carries each one's bits, which is how centrality is computed rather than
declared. An observation of X itself carries bits only about goals whose
closure holds X's own truth; a goal that reads X only as `X@valid` learns
from checks of X's leaves.

*Stakes.* A plan's stake is half the span from its success class's utility
down to the expected utility of its failure: each failure story's mass at
its class (row classes, `class_given` sides, leaf class tags, the
undescribed-failure valuation of a residual row), the unexplained rest at
the outside option, capped above at the outside option's value; a plan
with no derived failure mass reads the outside option. So a plan whose
failure can land in a worse future weighs more than one whose failure is
merely the default, in proportion to how much of its failure does, and a
residual row of small mass moves the stake a little rather than lifting it
at the first admitted row. A want's stake is its owner's priority. An
improvement claim, a route under it and a refinement take the largest
stake of the plans and wants that read them or the *family* of the claim
they serve (the claim and its refinements), unscaled: the improved version
matters to whatever reads the claim, however its literal version fares. A
shared claim or risk story takes, over the goals that read
it, the largest of that goal's stake times the share of that goal's
entropy its own truth settles (I(T_g; T_h)/H(T_h), from h's joints in the
verdict model): a claim borrows weight from a container in proportion to
what settling it tells the container, so a sentence a want cites but
barely moves borrows almost nothing. Every stake is at least `stake_floor`.
The rules are applied to a fixed point (an `X@valid` reading lets a
container have the smaller closure). `--why` prints each goal's rule and
the goal its stake came from; a unit whose goal borrows its stake from a
want its owner has not confirmed carries the signal *stake from <want>
(owner has not confirmed)*.

*Promise and suspicion.* The *promise* π̂ is the goal's shrunk gestalt
where one is logged (on a want, a human's only); else, for a want, 1/2;
else its shrunk derived probability, else 1/2;
`promise_exponent` 0 treats confirming and refuting alike for every goal
(available by one key), 1 is mostly promising first, 2 strongly
so. A goal of kind `and`, `or` or `cases` whose derived forecast and shrunk
gestalt sit `structure_suspect_odds` (4) or more apart in odds is
*structure suspect*: its weight gains `suspicion_weight` (1/2, below a
typical promise, so promise stays first) times its stake. The comparison
with the threshold is exact (a Fraction of the float odds ratio).

Under `--scope x` the goals are those that read x or lie under x, plus the
units on x's closure; under `--as @h`, h's wants count at their priority
and other owners' at `others_wants_weight` times theirs, and the committed
files stay pooled. A leaf that several nested goals lean on (a plan, its
improvement claim, a route, a refinement) counts once per goal, so filing
more intermediate goals weights a leaf more; `--why` prints per unit how
many of its goals lie on one such chain. **Decided** that the ranking is
across goals, serves mapping, prefers promise,
attends to suspicion and is improved rather than overridden; **Default**
for the goal set and its two exceptions, the stake rules, the sensitivity
scaling, the suspicion summand and its weight, the promise and the
per-goal counting; **Open** whether a chain of nested goals should count
once, and whether a root no goal reads should count as a goal at all.

**The verdict model.** Inside the ranking only, every judged probability
enters shrunk toward 1/2 by how little it has been read: p̂ = 1/2 + ρ(p −
1/2), ρ = 1 − `verdict_c` · floor(level), the level that its displayed
width already uses (the judgment's own for a gestalt); a record confirmed
by a claims registry is shrunk by `verdict_record_floor`; row weights are not
shrunk; a proposed table enters the forecast at its drafted rows (shrunk
like any AI number) while display and status hold it at 1/2. So an unread
AI number at 0.985 is forecast at 0.888 and displayed at 0.985, and the
forecast approaches the display as humans read. Every displayed number,
status and value is unchanged by it. The model's constants are priors
until the ledgers' AI-versus-human pairs refit them. **Default.**

**The decision term** D of a unit is the expected value of the best option
after observing what the unit observes, minus the value of the best option
now; it is positive only when the observation could change which plan is
best, over every plan in the frame tree. It is read for every unit from
the joint masses the inference's passes already carry (§4), so its cost
grows with the plans and not with the units. `--window-dp` runs an exact
schedule over the shortlisted units within the window and `--frontier K`
adds a greedy continuation of K units toward commitment; both are off by
default and reorder nothing. **Decided** that
no viability threshold enters the act; **Default** for one-step D.

**Combination.** The list is ordered by map rate; D prints beside every unit
under `--why` (the committed list shows no numbers) and drives the commit
line; it reorders the list only under `--lambda x`, which scores `rate + x
· D / window hours` and says so. The *commit line* reads "commit now → P"
when no unit has D > 0 and P's weakest proof-set leaf (the least-vetted
element of its proof set) is at `commit_level` (6) or above; "research
first: the decision term (printed, not applied) favours U (ranked unit n),
D d" when some unit has D > 0, U the best-ranked unit with D > 0, so the
line names the unit's place in the list and the size of what drives it;
"no plan vetted
enough to commit to; leading candidate P" otherwise, P being the best
non-conceded plan (a step is named through its programme, "F → P"), with
any conceded plan named as "not a candidate" and its revival pointed at
("revive T: ranked unit n"); "no non-conceded plan to commit to (…); the
outside option stands until a revival (revive T: ranked unit n)" when every
plan in scope is conceded; "suspended: no plan has a value yet (no belief
on …)" when plans exist and none has a value; "suspended: no plan step in
scope" when the plan roots in scope are programmes with no step in scope;
"suspended: no plan in scope" when there is none. The *regime sentence*
names what drives the order: the map alone, with the reason D is silent (no
plan in scope; no plan step in scope; no plan with a value; every plan
conceded; one plan whose failure stories name no class below the outside
option; the leading plan leads in every world), or how many units D would
reorder and the largest D. The *act line* says what the decision term
rests on: the act's leading option and its value, whether that value rests
on AI numbers only, and the option's gestalt where it sits 0.2 or more
from the derived probability, so a reader can see when one AI-derived step
near certainty holds the act and silences D. Where the outside
option's node has no belief the appendix prints it as *no belief on
default-trajectory (read as 0; interval the whole scale)*. **Decided** that
the two terms are reported separately
and never rescaled against each other ad hoc, and that a programme's plan
value is its best step's (§4); **Open** how to combine the terms and
whether the probability that a root overtakes the leader should enter
directly.

**Paths and signals.** Every ranked unit prints on two lines: `n. <kind>
<target> (<size>)[ — for <goal>][; also <g2>, <g3>][ — <signal>;
<signal>]`, then `path: top → … → <target>`, and a third, indented, with
the unit's text where it has one (a `do` unit's action, the improve
prompt). *For* names the unit's *top-share goal*, the goal carrying the
largest share of its weighted bits, where that goal is not the target
itself (then the path carries its place, and the line reads `— also for`
when other goals reach the threshold); *also* names the goals carrying
`also_for_share` or more (at most two, compared exactly); shares are per
goal, and print as percentages under `--why`, where a share under half a
percent is left out. The *path* runs from `top` through the frame chain of the
top-share goal's *home root* (the goal itself when it is a root, else the
root whose support or improvement closure holds it by the shortest chain),
the root, the nodes down to the goal, and the hops from the goal to the
target: the support chain where the target is in the goal's support,
otherwise the shortest chain over `children` and `given`. A hop down a
`children` edge prints `→`, an evidence hop down a `given` edge prints
`⇢`. On the chain, frames, goals, `cases` crux roots, the target's parent
and the target print, and a run of other nodes prints as `…`; above
`path_max` printed nodes the first four and the last three stay. A unit
whose target informs no goal has no ranked line, and the view says
*informs no goal*. *Signals*, at most two per line, in this order: *read
at vk, now vn*; *structure suspect: derived x against gestalt y*;
*attribution unvetted*; *vet this AI number* (every judgment on the
target is an AI handle's); *promise rests on AI judgment* (the top-share
goal's promise rests on AI numbers alone); *owner has not confirmed*;
*kernel-checked record*; *work order #n* / *open statement* / *private
source* (the retired pointer kind); *private source only* (on a `vet`,
`trace` or `re-examine` whose target's Source says private and names no URL
and no path that exists in the repository: a citation §7 removes, so the
trace has nothing public to open); *stake from W (owner has not
confirmed)*; *blanks k roots* (on a ranked `admit`). A signal that would
appear on every printed ranked line is said once in the list header
("Hoisted from every line: …", one sentence naming every hoisted signal)
and dropped from the lines, so that a line names a signal only where it
sets the unit apart; it returns to the lines as soon as one line lacks it.
`tasks_shown` ranked and unranked units print, with a count of the rest;
`--all` prints every unit, and `derived.json` carries every unit with its
full path, signals and `rank` (its place in the main list, as `tasks.md`
numbers it). The list header says the ordering rule in one sentence.
**Decided** that every task shows its path and that the
default view shows orderings, kinds and sizes; **Default** for the printing
rules, the signal order and the hoisting.

**Research, agent work, the goal table, the digest.** `tasks.md` carries,
before the ranked list, `## Research and whole-argument units`: the fifteen
best-ranked units of the kinds that produce new structure or read an
argument whole (`improve`, a human's `do`, `re-examine`, `spell-out`,
`connect`, `revive`), each numbered by its rank in the list. It changes no
order (what is ruled out is imposed shares, not a gathered display); it
exists because under bits per hour a research unit, priced in hours and
observing with error, ranks far below the half-hour checks, and a reader looking for
research should not have to scroll to rank 400. After the ranked list, `##
Agent work`: the twenty `do` units with `who: agent` of largest score, in
the same format, work an agent can do without a human and the map's own
ordering, not `PRIORITIES.md`'s; and `## By goal`: one row per goal and one
outline row per frame, in the frame tree's order (depth-first, roots in file
order, so the table reads as the agenda's outline), indented by depth, with
kind and role (plan of F, want of @h, route under I, shared claim of F), the
best ranked unit and its rank, the count of units, and the Statement's first
clause (to the first comma outside brackets, or the first thirty words where
that clause is under five words); weights, forecasts and bits only with
numbers on. The digest (statuses and levels that moved, events counted,
revisions recorded, wants filed since the previous derivation, proposals
awaiting) lives in `derived.json` and on the checker's `DIGEST` line, which
names what it compared with: the branch `derived` (the derivation of `main`
CI publishes), else the `derived.json` on disk when the `versions.json` at
`HEAD` records its derivation hash, else nothing (ruling F3, 2026-10-23); it
left `tasks.md` then, because a committed file reads nothing that varies with
what is on disk or fetched, so rerunning the checker leaves the committed
files as they were. `tasks.md` keeps the spell-out candidates (unspelled
frames and childless wants, with the top three by weight), the agent work
the map wants most and the proposals awaiting approval. **Decided** for the
mid-level view; **Default** for its form and for the research
section; **Open** whether agent work should feed `PRIORITIES.md`, and
whether bits per hour is the right normaliser across unit kinds or research
units should be priced by budgeted multi-step value of information.

**Scope, numbers.** `--scope <id>` restricts the settled truth to the goals
that contain the node or lie under it, the units to its closure and the
options to the plans containing it, labelled "scoped: bits about <id> only";
`--scope <id>@valid` does the same for an argument's implication (§2). The
committed `tasks.md` shows orderings, kinds, sizes, paths, signals and the
regime sentence; `--why` or a user's `show_numbers` adds, to the personal
render only, minutes on every line and a `## Why` appendix with the
objective's formula and the policy values in force, a table of every goal
(kind, home root, stake and its rule, promise and its source, whether it
rests on AI numbers, probability, forecast, bits, weight, closure and cutset
sizes), each unit's minutes, weighted bits, rate, D (`D_window`, the window
schedule's value, under `--window-dp`, which shortlists only the units
observing with error 0, `vet`, `trace` and `revive`, since its forced
branches are exact observations), its signals, its goals with weighted bits
and shares, how many of them lie on one chain, the rate rows used (labelled
prior) and its full path, the largest cutsets against the cap, and each
root's probability, value interval, gestalt and the leaves it has *no belief
on*. A user's `alternative_calculations` adds the *comonotone companion*,
the root's probability under full positive dependence (the least hold
probability over its proof set). **Decided.**

## 7. Publication

Everything under `graph/` and `chats/` is public: inventory, statuses,
events, numbers, rankings, task lists and process data (minutes,
calibration, audits). Contributors appear by handle in the graph files
because the checker keys events to handles; the handle map is public, so a
handle is a presentation rule, not anonymity, and prose names people as the
document needs (ruling of 2026-10-02). Views pool numbers; event files carry
their signer because levels depend on who vetted what.

**The public map cites only what a public reader can open.** A node's
Source, a gloss, a reason, a `work` pointer, a task's `files` or `action`
and every generated file cite published papers, public posts, and files
and history of this repository; nothing else. Private material (notes,
journals, chats, correspondence, calls, recordings and their write-ups,
review comments, unpublished drafts) may shape the map, deciding what is
filed and what is looked at first, but it is never cited, quoted,
paraphrased or dated, and no placeholder stands in for it ("correspondence,
private", "the maintainer's notes", a path outside the repository). Where
a private source was doing work, the claim rests on public grounds or is
stated as the weaker claim those support. The map reports nothing anyone
said, planned or holds privately: another person's unpublished work, plans
or views enter only through their public words, and a claim about a
person's intent (an attribution bridge) rests on that person's public
words or is stated as the formal claim without the attribution. A node
whose subject is a private interaction (a message to send, a meeting, a
recording, a consent request, a question pending with a person) is not
filed. The checker warns on a Source naming private material and on the
retired `private` pointer kind. **Decided** that the design discussion
stays private; **Decided (2026-10-20)** for the rest, except that the
maintainer's design rulings are stated as rules, never quoted and never
cited by number, which is **Default**.

An AI-drafted attack on a living researcher's published argument is
published once a human has admitted it; everything else publishes on
commit; a handle is created by a pull request adding its line to
`handles:`. **Default.**

## 8. Glossary

- **Frame, owner, root, goal hierarchy.** A node holding a question, the
  human whose question it is, and the claims directly under it; the nesting
  of frames (top question, lines, programmes, steps) that the paths follow.
- **Programme, sub-frame, step, leading step.** A plan root of kind
  `frame`; the frame it holds, with its own question, owner and roots; one
  of those roots; the step whose value (else probability) the programme
  reads as its own.
- **Unspelled frame, not opened.** A frame with `roots: []`, awaiting a
  `spell-out`; a frame marked `opened: false`, a line recorded and
  deliberately left closed, with no plan roots and no `spell-out`.
- **Want, priority word, owner has not confirmed, unattached.** A claim
  with `want: true` and a human owner, a root of role `want`: a state of
  affairs its owner wants to see, carrying its owner's priority and no AI
  number; the owner's `high`, `medium`, `low` or `none` (1, 1/2, 1/4, 0;
  unset reads as medium) given as a `priority` event; the flag on a want
  filed from its owner's quoted words (`filed_from: quote`) until the first
  priority word; a want with no children, no given edge and no goal
  containing it.
- **Task leaf, action, who, actioned claim, feasibility.** A leaf whose
  Statement says a deliverable exists with its stated property; the one
  imperative sentence of work to do; `human`, `agent` or `either`; an open
  question, step, hypothesis, route or improvement leaf carrying `action`
  and `who` itself; a task leaf's probability, the chance the deliverable
  can be produced if the work is attempted.
- **Work pointer.** `work: [{kind, ref}]`: `priorities` (an item node, by
  number), `open` (a Lean declaration), `round` (a round directory or a round
  of `state/rounds.json`), `decision` (a `DECISIONS.md` anchor) or
  `foundation` (an id of `state/foundations.json`); `private` is retired and
  warns.
- **Shared root, home.** A node listed as a root by several frames, filed
  once; the first of those frames in the frame tree's order, through which
  its paths run.
- **Narrative, drafted frame.** The wiki page or pages that narrate a frame
  or node (`narrative`); a frame an agent drafted from a wiki page
  (`filed_from: wiki`), flagged *owner has not confirmed* until the owner
  removes the field.
- **Item node, docket, decision anchor.** The node of one `PRIORITIES.md`
  entry (`item-<n>`), from which the file is rendered; the `or` of a
  project's work orders no finer goal was identified for, an `or` filed as a
  shared-claim root of its line or programme whose Statement says what it is
  (ruling F6, 2026-10-23: "Work orders filed against <programme>, not yet
  attached to the goal each serves; their placement is the maintainer's"); the
  machine line of a `DECISIONS.md` entry that a `decision` pointer names.
- **Structure-only index.** graph/index.json, the fifth generated file (not
  committed since 2026-10-23; published to the branch `derived`): the map's
  structure and the human ledgers, with no derived number.
- **`cases` node, picture, weight, conditional, residual row, partition
  leaf.** A claim split into exclusive, exhaustive scenarios; one scenario;
  its probability of obtaining; the claim's probability given it; the row
  for no listed story; the leaf asserting the table is exclusive and
  exhaustive.
- **Conditional table, given parent, if-holds / if-fails, class_given.**
  A claim leaf or row whose judgment is split by another claim's truth
  (`given: Y`); that other claim Y; the two sides, P(X | Y) and P(X | not Y)
  (`p-if-holds` / `p-if-fails` on a row), ordinary judgments; the failure
  class spelled out per side.
- **`X@valid`.** An `and`-shaped argument read with its assumption and
  hypothesis leaves held true: the implication it establishes; a legal
  given target and scope.
- **Improvement claim, reality phrase, route, residual route, diagnosis
  table, refinement.** A node with `improves: X` and `reality: R` whose
  Statement is "X can be improved until it reflects R well."; R, the system
  the improved claim is to hold for; one direction of improvement, stated
  factually, a child of an improvement `or`; the one route marked
  `residual: true`, standing for refinements not yet described; an
  improvement claim in `cases` form, each row a reading of what stands
  between X and R; a literal claim carrying `refinement_of: X`.
- **Attached.** A node that is a root of some frame, a valuation node,
  listed in an attached node's `children`, or the given parent of an
  attached node or row; rule 1 requires it of every non-superseded node.
- **Cost to establish, revival cost.** Rate-table minutes to reach the
  establishment level; the minutes to argue a conceding picture back up.
- **Judgment (J), level (V).** A number a human or an AI handle gives, and
  its ladder (J 0 *generated* for an AI's); which checks have been performed
  on a statement, 0–20, from ledger events, human events only, counted at
  the Statement version each was given against.
- **AI number.** A judgment that rests on AI handles only, no human having
  revised it; marked wherever it feeds, and "vet this AI number" is its
  signal.
- **Map-read, trace, pass.** Levels 6, 8, 12: a read with a checked list;
  the argument followed step by step; an adversarial pass logged complete.
- **Revision pass, read at vk, reread.** A human's revision of a
  Statement, recorded as a `revise` event; the level a node had at an older
  version, shown beside its headline once the Statement moved on; the
  cheaper map-read of such a node, priced from the `reread` row.
- **Outcome class, outside option.** A kind of future with a utility in
  [−1, 1]; committing to no plan, valued by the default-trajectory node.
- **Valuation node.** A `cases` node whose rows are outcome classes, read as
  a distribution over them; its value is the weighted mean of their
  utilities. Two exist: `default-trajectory` (the outside option) and
  `undescribed-failure` (where a failure nobody has described lands).
- **Revive.** The ranked task of arguing a conceded table's conditional back
  above the bar, priced at the revival cost.
- **Proof set.** The cheapest way to establish a root (load is defined
  below, with the weakest proof-set leaf).
- **Closure, cutset, forcing.** The variables a formula's probability
  depends on, reached through `children` and `given`; the variables reached
  by two or more paths, whose assignments the inference enumerates;
  restricting a variable's outcomes (a leaf to true or false, a table to
  some rows), the factor by which `X@valid`, failure classes and a unit's
  observation are evaluated.
- **Goal, settled truth, informs.** In the ranking: a non-frame root of
  any frame (not a one-leaf shared claim or risk story, and not under a
  frame that is not opened), an improvement claim, a route, a refinement
  or a want; the status a goal would reach if its proof set were vetted to
  the establishment level; a node informs a goal when the goal's closure
  reads it, itself or as `X@valid`.
- **Stake, sensitivity, promise, suspicion, weight, weighted bits.** What a
  goal bears on: half the span from a plan's success utility to the
  expected utility of its failure, a want's priority, the stake of what
  reads an improvement claim's family, or for a shared claim the largest
  stake of a goal reading it times its *sensitivity*, the share of that
  goal's entropy its truth settles; how promising it looks, its shrunk
  gestalt or derived probability (a want's: a human's gestalt or 1/2); the
  summand `suspicion_weight` a structure-suspect goal adds to its promise; stake times (promise to the
  `promise_exponent` plus suspicion); the bits a unit yields about a goal's
  settled truth times that goal's weight.
- **Verdict model, forecast.** The ranking's inner reading of every judged
  number, shrunk toward 1/2 by its level's floor; the number so read, as
  against the number displayed.
- **Unit, top-share goal, home root, path.** One piece of work on one
  target, ranked; the goal carrying the largest share of a unit's weighted
  bits, named after *for*; the root that goal is or sits under by the
  shortest chain; the printed chain from `top` through frames, the home
  root and the goal to the target, `→` a part and `⇢` evidence.
- **Signal, hoist.** A short tag on a ranked line (*read at vk, now vn*,
  *structure suspect*, *attribution unvetted*, *vet this AI number*,
  *promise rests on AI judgment*, *owner has not confirmed*,
  *kernel-checked record*, a work pointer, *private source only*, *stake
  from W*, *blanks k roots*); saying a signal once in the header when every
  printed line would carry it.
- **`improve`, `do`, `spell-out`, `connect`.** The research unit on an
  open step, question, route or improvement leaf (relax, reformalise, take
  a direction, or critique and redraft); the unit that does a task leaf's
  or actioned claim's `action`; the read of an agent's draft of sub-goals
  and tasks under a childless want, a leaf-form improvement claim or an
  unspelled frame; the read of an agent's proposed edges for an unattached
  want.
- **Ranked admit, quick admit.** The read of a table's proposed rows,
  ranked; the one-word admission beneath it in the unranked block, with
  what admitting unread would move each goal from and to.
- **Re-examine, structure suspect.** The ranked read of an internal goal's
  analysis as a whole, where it carries a gestalt; the signal, and the
  weight summand, when its derived and gestalt readings' odds differ by
  `structure_suspect_odds` or more.
- **Research section, agent work, goal table.** The `## Research and
  whole-argument units` section of `tasks.md`, the best-ranked units that
  produce structure or read an argument whole, gathered without reordering;
  the `## Agent work` section of `tasks.md`,
  `do` units whose `who` is `agent`, never asked of a human; the `## By
  goal` section, one row per goal in the frame tree's order.
- **Said / approved.** In the human's own words / the agent's draft
  accepted; only said items raise a level.
- **Verbatim, gloss, reason.** The human's words for an answer; the
  agent's reading of it, kept apart; the human's stated ground for a
  number (its presence makes the judgment J 8).
- **Committed files, personal render.** The five files the plain run
  writes, identical under every flag (and `PRIORITIES.md`, rendered beside
  them where the tree holds item nodes); a task list and view for one user
  or scope, printed and never committed.
- **Handle prefix.** Every event id begins with its ledger's handle
  (`anson-001`), so ids never collide across contributors.
- **Weakest proof-set leaf, bears on, load.** The least-vetted element of a
  root's proof set; the roots whose proof set holds a unit's target; the
  roots whose status depends on a node (conceded once it is conceded, not
  conceded once it is established).

## 9. Refusal rules

The checker stops at the first violation and prints `REFUSE <rule>
<path>: <reason>` on stderr. One line per rule; the reason names the file
and, where there is one, the line. `--self-test` runs a null input for
every clause below.

| rule | refused when |
|---|---|
| 1 | an id is not unique across nodes, proposals and events; a reference (`children`, a row's `picture`, `hypotheses`, `negation_of`, `refines`, `committed`, `supersedes`, `superseded_by`, `given` on a node or a row, `improves`, `refinement_of`, an event `target`, a frame's `roots`, a `priorities` pointer where the tree holds item nodes, a `decision` pointer's anchor, a `foundation` pointer's id) resolves to nothing; two item nodes carry one item number; the graph over `children` and `given` edges (rows included, `@valid` stripped) has a cycle; a non-superseded node is attached to nothing (§2: not a root of any frame, not a valuation node, listed in no attached node's `children`, the given parent of no attached node or row), every such node named; a top-frame root or valuation node is named in a `children` list; a want is a root of more than one frame, a node is listed twice as a root of one frame, or a shared root's entries name different roles; an event targets `if-holds` or `if-fails` on a node without `given`, or `p-if-holds` or `p-if-fails` on a row without it |
| 2 | a kind, `leaf_kind`, role, preset, event kind, `how`, `via`, `dimension`, `who`, `filed_from` value, `work` kind or class id is unknown; a kind's required fields are missing (a leaf's `leaf_kind`, an `and`'s one completeness child, a `cases` node's one partition child and matching rows, a `choose`'s `decided_at`, a hypothesis's `discharge`, a record's `statement_of_record` (its `hypotheses` a list of ids or the word `unread`, never both), a formal result's one bridge with `attribution`, a `frame`'s `question`, human `owner` and `roots` naming exactly its children, the top frame's human `owner`, a task leaf's `action` and `who`, an improvement leaf's `improves`); a `choose` lies outside every plan root's support; a choice point (an uncommitted `choose` or a `choose-one` `or`) lies in the support of two plan roots that are not programmes (each plan is refined by its own pick, and a shared one would be evaluated under one plan's pick; refused until shared choices have a ruled meaning); a frame node is not a plan root of some frame, or is a root in another role (a retired frame, one carrying `superseded_by`, is exempt and holds no roots and no children: they moved to the frame that supersedes it, ruling F4 of 2026-10-23); a frame has `opened: false` and a plan root, or `roots: []` and children; `given` sits on a leaf kind other than assumption, hypothesis, bridge, step, question, route, improvement, task or want, or names a frame, a `choose`, a valuation node or a picture, partition or completeness leaf; `@valid` names anything but an `and` (in a `given` or in `--scope`); `class_given` appears without `given` or is not a map of `holds` and `fails`; a `rule`'s row carries `given`; `improves` appears without `reality` (or with an empty one) or `reality` without `improves`, or `improves` sits on a frame or on anything but an improvement leaf, an `or` or a `cases` node; an improvement `or` lacks exactly one `residual: true` route child; `residual: true` sits on anything but a route child of an improvement `or`; a route leaf lies in no improvement claim's support; a node with `want: true` lacks a human owner, has an id not beginning `want-`, is a leaf of a kind other than `want`, or is not a root of role `want`; a want leaf lacks `want: true`; a root of role `want` lacks `want: true` or carries `preset`, `success_class` or `budget`; `action` or `who` sits on a leaf kind other than task, question, step, hypothesis, route or improvement; a `priorities` work ref is no integer; a frame's `owner` (the top frame's included) is not a human handle or a list of human handles; `narrative` names a page that is not under `wiki/` or does not exist; `filed_from` is neither `quote` nor `wiki`, or `filed_from: wiki` sits on anything but a frame; an item node lacks `item` (the number as a string), `title`, `section`, an integer `maintainer_order`, `dispatchable` or `item_status`, or a node whose id begins `item-` carries no `item` |
| 3 | a Statement has no sentence or uses a word from `evaluative_words`; an improvement claim's normalized Statement omits its normalized `reality` phrase |
| 4 | a node file or row carries a level, credence, status, weight, conditional, value, utility, load or cost; a Statement's normalized text changed without a `version` bump, or `version` was bumped with the text unchanged |
| 5 | an event lacks a required field; its `by` is not a mapped handle or the ledger is not named for it; its id does not begin with the ledger's handle; its `rule` is not of the form `YYYY-MM-DD.n`; its `version` is above its node's; a level-minting event lacks a said `checked` item or `not_checked`; a `withdraw` names another handle's event; a `rule` or `survey` is not a maintainer's; a `rule` with `rows` targets no `cases` node, names a non-row, or sets `p` on a row with a given parent; an AI handle writes a level-minting event, an `external`, an `attribution`, an `admit`, `approve`, `classify`, `identify`, `revise` or `priority`, an `estimate` or `gestalt` without a `gloss`, or an `estimate` or `gestalt` on a want, a row of one or a field of one; a gestalt lacks `derived: false` or targets a node that is no goal (§6); an `external` lacks `ref`; an `audit` lacks a `verdict` or names no event; an `attribution` is not by a human other than the node's author, or lacks `verdict` (`vouched` or `disputed`) or `ref`; a `revise` targets no node, lacks `from`, has `from.version` not below its `version`, names in `from.node` a node the target does not supersede, or names a `version` known to neither `versions.json` nor the node file; a `priority` is written by anyone but the want's owner, targets a node without `want: true`, or carries an `estimate` outside `high`, `medium`, `low`, `none`; a ledger is empty; dates in a ledger decrease; `policy.yaml` names no human `maintainer`, or its list holds a handle that is not a human's |
| 6 | `question` or `answer` is present without the other, resolves to no turn of one chat file, or `verbatim` does not occur in the answer turn |
| 7 | a committed file's `generated_hash` is missing or does not match its content (edited by hand; deleting the file lets the checker regenerate it); a proposal's `## Delta` differs from the checker's recomputation |
| 8 | a class lacks a utility or a human `placed_by`; `outside_option` or `undescribed_failure` names no valuation node, or a valuation node is not a `cases` node whose rows all name placed classes; a `success_class` names no class; a plan root lacks `success_class`, or a programme root carries one; a sub-frame's `outside_option` names no valuation node; a `probabilistic` or `expected-utility` root lacks `budget` |
| 9 | a proposal is `approved` or `applied` without a counted `approve`; a proposal op names a missing node or row, or an unknown op |
| 10 | the residual row's weight is judged or ruled; non-residual weights' midpoints sum above 1; a range lies outside [0, 1] or has lo > hi; a class tag, row class or `class_given` side names no class or valuation node; a rate-table row is not a `{S, M, L}` map or has minutes below zero; `registries` is not a list of paths or names a file that does not exist; a policy key lies outside its range: `promise_exponent` in [0, 2], `stake_floor`, `others_wants_weight`, `verdict_c`, `verdict_record_floor`, `gestalt_mix`, `also_for_share` and `suspicion_weight` in [0, 1], `improve_error` and `do_error` in [0, 1/2], `structure_suspect_odds` at least 1, `ai_conjunct_threshold` an integer at least 2, `path_max` at least 3, `tasks_shown` at least 1 |
| 11 | `graph/DESIGN-LOG.md` is missing; a file under `graph/` lies outside the layout of §1; a chat file changed after the commit that added it; `--out` points inside `graph/` |
| 12 | a file breaks the flat-YAML subset, a frontmatter lacks its closing `---`, a node file lacks `## Statement` or `## Source`, an item node lacks its `## Item` section, the frame or policy is missing, `versions.json` is not JSON |
| 13 | one formula's cutset is too large: the variables it reaches by two or more paths need more than the per-formula cap of 2^15 assignments; the reason names the formula, the shared variables and the count, and the remedies in order (make a conjunct shared across several of the formula's children its own shared-claim root, coarsen a table, move part into a sub-frame; §4) |
