# Addendum: machine-readable lab state and epistemic promotion

This addendum is part of the same round. Its purpose is not to introduce a new framework or reorganize for its own sake. It makes the repo's **current epistemic and project state mechanically discoverable and mechanically checkable**, so future agents do not need to reconstruct what is current by interpreting prose.

The governing principle is:

> **State lives as structured data; prose is a view. Research artifacts produce candidate evidence; explicit registration promotes evidence into workspace state.**

Prefer the smallest implementation compatible with the repo's existing checker architecture. Reuse existing registries and parsers where possible. Do not add a new dependency solely to obtain a preferred serialization format.

## A.1 Epistemic promotion rule

Make the distinction between **research output** and **registered workspace state** explicit in `AGENTS.md` and `CONTRIBUTING.md`.

A completed round may contain proofs, witnesses, experiments, criticism, conjectures, interpretations, and reports. Their mere presence in a completed round does **not** make every statement in them a current claim of the workspace.

A result becomes consumable as current state only when the round promotes it through the appropriate registered surface:

`round artifact → statement of record → registered claim/status → current workspace state`

Accordingly:

* Future agents may inspect completed rounds when their task requires the underlying evidence, history, or argument.
* For orientation, they should consume the registries/current-state query rather than infer status from old prose.
* The wiki may characterize an Established result only if it has crossed this registration boundary.
* Superseded, failed, or unregistered material remains available historically but cannot silently re-enter current state merely because an agent finds it persuasive.
* A round that changes a registered claim, project status, vocabulary item, priority, or theorem-facing interface must update the corresponding structured state in the same PR.

Add this rule without changing any existing epistemic classes.

## A.2 Persistent machine-readable state

The three hand-off artifacts required by §2 — final path map, canonical vocabulary sheet, and verdict/status inventory — must not exist only in the round report. Give their durable content machine-readable homes in the repo.

Inspect existing registries first and avoid parallel sources of truth. The target logical objects are:

### Projects / paths

A structured project registry containing, at minimum:

* stable project ID;
* human display name;
* current repo path;
* active / deprecated status where applicable;
* parent project or subproject relation;
* canonical repo entry points.

The IDs must survive future directory renames. `normativity`, `normativity.legitimacy`, and `deference` should therefore be identifiers independently of their filesystem paths.

### Claims

There must be exactly one authoritative claim registry.

If the existing `CLAIMS.md` is already sufficiently structured and checker-parsed, formalize and validate that structure rather than replacing it. Otherwise, move the authoritative fields into a structured source and make `CLAIMS.md` a generated or mechanically synchronized human-readable view.

For every registered claim for which the fields make sense, machine-readable state should expose:

* stable claim ID;
* owning project/subproject;
* short name;
* current status;
* epistemic class, verbatim;
* statement-of-record locator;
* originating or latest decisive round;
* supersedes / superseded-by relation when applicable;
* dependencies on other registered claims where already explicit.

Do not invent dependencies merely to fill the schema.

### Rounds / verdicts

Create or formalize a machine-readable round index containing:

* stable round ID/name;
* date;
* current path;
* verdict string verbatim;
* epistemic class or classes actually registered by the round;
* prompt path;
* claims added, changed, refuted, or superseded, where this relation is already part of the record.

This index becomes the durable source for the §2 verdict/status inventory.

### Vocabulary

Create a small machine-readable vocabulary registry containing:

* stable term ID;
* preferred human-facing term;
* deprecated aliases;
* scope where needed;
* repo/code identifiers when they differ from prose notation;
* replacement term(s) for deprecated vocabulary.

Do **not** duplicate philosophical definitions here. Definitions and exposition belong in the wiki Glossary.

Amend §4.4 accordingly:

> The wiki Glossary is the canonical **human exposition** of vocabulary. The repo vocabulary registry is the canonical **machine-readable record** of preferred labels, aliases, deprecations, and identifier mappings. Neither duplicates the other's job.

This resolves the otherwise undesirable situation in which repo agents are forbidden to consult the wiki for instructions but the repo's vocabulary source of truth exists only there.

### Priorities

If `PRIORITIES.md` currently contains statuses or identifiers that agents must parse to know what work is active, either make its syntax formally checker-readable or introduce one structured priority source and derive/synchronize the Markdown view from it.

At minimum expose:

* stable priority ID;
* project;
* title;
* state;
* dependencies if explicitly known;
* provenance/origin;
* whether the item is specified enough to dispatch.

Do not turn the priority list into a project-management system. Its job is only to make the existing research queue unambiguous.

## A.3 The theorem-facing interface as data

The Architecture page required by §4.3 is important enough not to exist solely as a hand-maintained wiki table.

Create a compact structured **hypothesis/interface ledger** for the current normative-learning theorem interface. It should encode the objects already required by §4.3:

* `A`;
* `E_g`;
* `F_g`;
* `ℓ_t`;
* `δ_g`;
* coverage;
* Due → selector compilation.

For each object/interface, record only facts already supported by the repo:

* producing module(s);
* consuming module(s);
* registered soundness claim ID(s);
* status of those claims;
* write-access class;
* statement-of-record pointer where applicable.

The wiki Architecture page remains the explanatory document, but its factual table must be checked against this ledger rather than becoming an independent source of module-state truth.

Do not encode aspirational architecture as if implemented. Unsupported fields may be `open` or absent.

## A.4 Generated views, not synchronized prose

Where a Markdown file exists primarily to restate structured state, prefer generation over hand synchronization.

In particular, determine whether `RESEARCH_STATE.md`, `CLAIMS.md`, parts of `PRIORITIES.md`, or a small root status summary can become generated views.

A generated file must say so at the top and name its source and regeneration command.

Do not generate explanatory READMEs, wiki prose, round reports, or statements of record. Generation is for inventories and projections of state, not research writing.

The target is that changing a status in two hand-maintained places becomes impossible or obviously erroneous.

## A.5 One canonical machine query for future agents

Add one lightweight command, using the existing checker/tooling conventions, that validates and emits the current workspace state in a compact machine-readable form.

Desired behavior, naming chosen to fit the repo:

```text
<workspace-state-command> --check
<workspace-state-command> --json
```

The JSON view should be sufficient for an agent to answer:

* What are the active projects and where are they?
* What claims are currently registered?
* What is each claim's exact status and epistemic class?
* What completed rounds supplied the current results?
* Which vocabulary is preferred or deprecated?
* What priorities are currently active?
* What theorem-facing interfaces are registered?

This is an orientation interface, not a replacement for reading statements of record when the underlying argument matters.

If implementing a single query command would require disproportionate machinery, provide the smallest equivalent composition of existing checker commands and document it in `AGENTS.md`.

## A.6 Referential-integrity checks

Extend the checker suite so CI fails on structured-state inconsistency that can be detected mechanically.

At minimum check:

1. every registered repo path exists;
2. every claim's owning project exists;
3. every registered round path exists;
4. every claim-to-round reference resolves;
5. every supersedes/superseded-by reference resolves and is non-self-referential;
6. every epistemic class belongs to the existing allowed set;
7. no deprecated project ID is used as an active project;
8. vocabulary aliases do not resolve ambiguously to multiple active preferred terms unless explicitly marked as such;
9. theorem-interface claim references resolve to registered claims;
10. generated state views are fresh relative to their structured sources, if generation is introduced.

Where feasible, also make duplicate stable IDs a hard failure.

Do not make repo CI depend on network access to the GitHub wiki.

## A.7 Wiki/repo handshake

Because the wiki is a separate repository, do not create an architecture in which either repository must be fetched over the network for ordinary validation.

Instead:

* the repo exposes stable IDs and structured factual state;
* the wiki cites immutable repo statements of record as already required;
* wiki exposition uses the repo's preferred vocabulary IDs/labels;
* during this coordinated round, run a local cross-repo check with both clones present.

That cross-repo check should verify, at minimum:

* every repo-side pointer to a wiki page resolves in the local wiki clone;
* every wiki Established claim that names a registered claim ID resolves to the repo registry;
* preferred vocabulary used in machine-significant wiki tables agrees with the vocabulary registry;
* Architecture-page registered objects agree with the theorem-interface ledger.

This may be a round-local validation script or mode rather than permanent repo CI.

## A.8 Current-state orientation file

After the restructuring, the root should give an agent a deterministic startup path.

`AGENTS.md` should direct an orienting agent approximately as follows:

1. read the rules;
2. run/read the machine-readable workspace-state view;
3. inspect the relevant registered claim/interface/priority;
4. read the statement(s) of record needed for the task;
5. inspect historical rounds only when the task requires their evidence or development history;
6. consult the wiki only for conceptual synthesis when the dispatch permits or requires it.

The intended property is that an agent can learn **what the lab currently believes and what it is currently working on without reading narrative prose or guessing which artifact is newest**.

## A.9 Stable identity over path identity

Where this round introduces structured objects, use stable IDs rather than paths as identity.

A rename such as `projects/leverage` → `projects/normativity` should therefore require updating a path field, not rewriting the identity of every claim, round, or interface object associated with the project.

Do not retroactively assign elaborate identifiers to every historical artifact. Apply this where it reduces future rename and reference cost.

## A.10 Restraint / anti-framework rule

This addendum is successful if it makes the existing lab state easier to query and harder to contradict accidentally.

It is unsuccessful if it produces a large metadata framework that future rounds must service without clear epistemic value.

Therefore:

* prefer extending existing checker machinery;
* prefer four small registries over a generalized database abstraction;
* do not introduce schemas for information that currently has no consumers;
* do not migrate historical prose merely to populate metadata;
* do not encode interpretations that belong in the wiki;
* do not create new epistemic statuses;
* do not require every research artifact to carry every possible field.

When choosing between elegance and a small inspectable implementation, choose the small inspectable implementation.

## A.11 Acceptance additions

Add the following to §5 acceptance:

**Machine-state side:**

* one canonical machine-readable route exists for active project/path state;
* claim status and epistemic class are mechanically queryable without interpreting prose;
* round verdicts are mechanically queryable verbatim;
* deprecated vocabulary is mechanically detectable;
* the theorem-facing interface ledger exists and all of its claim references resolve;
* no hand-maintained Markdown file duplicates machine state without an explicit synchronization mechanism;
* the complete structured-state validation suite passes;
* demonstrate one intentional broken reference or stale generated view and show that the checker fails loudly;
* demonstrate the orientation query in the report with its output summarized, not pasted wholesale.

**Cross-repo side:**

* run the local repo/wiki consistency check with both clones present;
* report unresolved repo→wiki pointers: target zero;
* report unresolved wiki Established-claim→repo references: target zero.

## A.12 Report additions

Add to §6:

* structured-state files introduced or formalized;
* which pre-existing files remain authoritative versus become generated/views;
* stable-ID conventions;
* checker commands;
* any information deliberately left prose-only and why;
* one example of the epistemic promotion path from a completed round to current registered state;
* machine-state inconsistency count: target zero;
* cross-repo inconsistency count: target zero.

Add one final report verdict component:

`repo-consolidated / wiki-live / machine-state-valid / <n> drift-risk files remaining`
