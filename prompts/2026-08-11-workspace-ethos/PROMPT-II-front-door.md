# Workspace Ethos Pass II — Front-Door Consolidation and Live-State Legibility

**Maintainer:** A. M. Berns
**Prompt-author-model:** GPT-5.6 Sol (OpenAI)

Continue the workspace-ethos work already in progress.

This is not a fresh redesign. Preserve the framing developed in the current ethos round unless inspection reveals a concrete problem.

The expanded mandate is:

[
\boxed{
\text{make the workspace's public/front-door surfaces accurately represent the live research architecture}
}
]

without turning the repo into a procedural bureaucracy and without disrupting active Stage IV deference research.

The main concern is now **compression and legibility**.

The deep research state is increasingly coherent, but the repo's first surfaces have accumulated historical residue. A fresh human or agent should not need to read `DECISIONS.md`, several round reports, and old prompts merely to discover that a front-door statement is obsolete.

---

# 1. First: recover and inspect your current ethos work

There were uncommitted ethos changes restored after an accidental Stage III `git add -A` sweep.

Reported restored surfaces included:

* `RESEARCH_STATE.md`;
* `prompts/2026-08-11-workspace-ethos/`;
* `AGENTS.md`;
* `CONTRIBUTING.md`;
* `README.md`;
* `prompts/README.md`.

Before making further edits:

1. inspect the current working tree;
2. verify those recovered changes are intact;
3. compare them against current `main`;
4. check whether Stage III's merge or conflict resolution changed any of the same surfaces;
5. do not blindly preserve an older recovered version when `main` now contains a newer substantive edit.

The goal is a semantic merge, not recovery for recovery's sake.

Record any reconstruction uncertainty honestly.

---

# 2. Current research context

Stage III is now merged into `main` as a negative research result.

Its central outcome should be reflected correctly by current-state surfaces:

* the attempted FUD comparator did not contain a genuinely later agent;
* the purported jurisdiction-transfer dominance theorem was actually envelope dominance;
* the relevant Lean mathematics survives under the corrected `EnvelopeDominance` interpretation;
* Stage III erased the execution layer and therefore could not expose jurisdictional value;
* no FUD theorem should be inferred from Stage III;
* successor work requires a genuinely later, better-informed, fallible agent and a live execution layer including (\bot).

Stage IV is active and should be treated as **research-lab / provisional state**, not silently canonized.

Current provisional Stage IV status reportedly includes:

* a nontrivial future-agent finite model passing its local gate;
* later information strictly finer than the principal's but coarser than truth;
* future agent better-informed but fallible;
* separate evaluator, later-agent, and principal credences;
* live (\bot);
* explicit advice loss;
* anti-collapse checks passing;
* a likely result that comparator model debt has been reduced and competence is becoming the controlling obstruction;
* independent red-team review still required before that comparator can be described as successful.

Do not convert those provisional Stage IV findings into human-canonical claims before the round closes.

---

# 3. The ethos distinction to preserve

The workspace should distinguish:

[
\boxed{
\text{Research Lab}
\longrightarrow
\text{Agent-Consolidated State}
\longrightarrow
\text{Human-Canonical State}
}
]

with these meanings:

## Research Lab

Exploratory work: tracks; prompts; harnesses; provisional definitions; competing models; failures; speculative theorem shapes.

Lab artifacts may be excellent evidence without representing the current official research view.

## Agent-Consolidated

An agent's best synthesis of the available research state: reconciled; compressed; current-seeming; explicit about failures and debts.

This is a status of synthesis, **not human endorsement**.

## Human-Canonical

The deliberately small set of claims, framings, definitions, and priorities that have received maintainer judgment.

Do not manufacture human-canonical status in this pass.

You may identify proposed canonical deltas.

---

# 4. Keep orthogonal status dimensions orthogonal

Do not collapse every kind of status into one hierarchy. These answer different questions:

### Research-state layer

lab; agent-consolidated; human-canonical.

### Verification/evidence

Lean/kernel checked; exhaustive finite enumeration; witness/counterexample; report-level argument; not yet checked.

### Human review

maintainer-reviewed; not yet maintainer-reviewed.

### Research achievement

aspirational / constructed / gap.

### Debt

Why does constructed state not reach aspiration?

These dimensions may coexist. Avoid compound bureaucracy such as `human-canonical-lean-proved-maintainer-reviewed-agent-consolidated`. Use plain prose/tables where that is clearer.

---

# 5. Front-door consolidation is now in scope

Audit the surfaces a fresh visitor is likely to read first. At minimum inspect: root `README.md`; root `CONTRIBUTING.md`; root `AGENTS.md`; `RESEARCH_STATE.md` if present; `PRIORITIES.md`; `DECISIONS.md` only as the historical/governance source needed to check current claims; `projects/deference/README.md`; `projects/deference/notes/README.md`; current deference roadmap/ledger; `prompts/README.md`; CI workflow descriptions where front-door docs refer to them.

The question is:

> **Does the front door describe the repo that actually exists now?**

---

# 6. Known stale-state patterns to check

Do not assume these exact defects remain; verify them.

## 6.1 Retired frozen infrastructure

Check whether the root README or CONTRIBUTING still describe things such as `frozen/` as a live foundation; `tests/check_frozen.py`; a `frozen-integrity` workflow; checksummed frozen inputs as current architecture.

If `DECISIONS.md` and live CI show those have been retired in favor of consolidation verification or newer machinery, repair the front-door text. Do not erase historical records explaining that the old machinery once existed.

## 6.2 Stale deference landing page

Check whether `projects/deference/README.md` still speaks as though the finite-kernel round has not landed; the project is awaiting its first real research round; the notes structure is essentially empty; the current multi-stage corrigibility/deference program does not yet exist.

If so, rewrite the landing page so it functions as a **current orientation surface**, not an archaeological artifact. Do not duplicate the whole roadmap. Its job should be to tell a new reader: what this research line is about; where the current state lives; where formal artifacts live; where research history lives; what status claims do and do not have.

## 6.3 Numerical/status drift

Check canonical/consolidated surfaces for stale counts such as theorem totals; number of Lean files; axiom-audit totals; stage numbers; current PR/round status.

Do not turn the repo into a dashboard requiring constant manual number edits. Where exact counts are not conceptually useful, prefer wording that is robust to ordinary growth. Where counts are useful and currently asserted, make them correct. A canonical document should not contradict itself because one headline count predates a later section.

---

# 7. Build a genuinely useful front door

The root README should answer, quickly:

## What is this repository?

Not merely "a collection of alignment notes", but approximately: a live AI-assisted alignment/agent-foundations research workspace in which exploratory research, finite computational models, Lean/FAF formalization, adversarial review, consolidation, and human judgment are kept visibly distinct. Use wording appropriate to the repository's actual state and maintainer voice.

## How does work flow?

At a high level: research → verification/challenge → agent consolidation → human judgment. Do not make this sound more formalized than it is.

## Where should I start?

Give a small number of useful entry points — current workspace research state; current priorities; project landing pages; Formalized Agent Foundations / Lean material; decisions/history; prompts/research logs. Avoid turning the README into an exhaustive directory listing.

---

# 8. `RESEARCH_STATE.md` should be a compression surface, not another archive

If the current ethos round created `RESEARCH_STATE.md`, refine it into a genuinely useful **current-state front door**. It should be short enough to scan; explicitly agent-consolidated unless/until maintainer-adopted; clear about what is provisional; project-level rather than a giant chronological log.

A useful shape might be: how to read this document; active research lines; and for each major line — question; aspirational mathematical picture; constructed mathematical state; aspirational philosophical gloss; constructed philosophical gloss; controlling debt; next controlling question; where to go deeper.

Do not force every minor project into this shape. Use it for research lines mature enough to benefit from consolidation.

---

# 9. Make Aspirational / Constructed / Gap visible at the front door

This distinction should not live only in an ethos document. At least the major current research-state surface should make it easy to distinguish what success would look like from what has actually been built; and separately, what the hoped-for mathematics would philosophically mean from what the existing mathematics currently licenses.

For deference/corrigibility, do not copy these blindly, but the shape should resemble:

### Aspirational mathematical

A fair FUD theorem comparing retained principal jurisdiction against transfer to genuinely later AI cognition.

### Constructed mathematical

Actual FAF integration, finite execution/jurisdiction semantics, negative prediction/competence/certification boundaries, Stage III envelope-dominance results under corrected interpretation, and whatever Stage IV has safely established by the time this pass closes.

### Aspirational philosophical

Superhuman cognitive contribution need not imply transfer of final jurisdiction.

### Constructed philosophical

Current work has established several separations between epistemic performance, behavioral certification, and architectural jurisdiction; the positive FUD bridge remains open.

That distinction should remain honest even if Stage IV later succeeds.

---

# 10. Debt accounting should become useful, not decorative

Use the lightweight research-debt vocabulary developed in the first ethos pass. Likely categories: model debt; theorem debt; assumption debt; interface debt; formalization debt; verification debt; interpretation debt; scope debt; compression debt.

Do not attach all nine labels to every project. Use only debt categories that affect what work should happen next. The purpose is orchestration. A phase changing debt type is itself a meaningful research result.

---

# 11. Explicitly treat compression debt as a workspace concern

Define compression debt roughly as: the current research state cannot be recovered cheaply from the consolidated/canonical surfaces without reading substantial historical lab output.

Warning signs: agent initialization prompts become enormous; several reports must be read just to determine the current definition; superseded terminology keeps resurfacing; new agents cite historical reports as though current; multiple canonical-ish documents disagree; project landing pages describe retired states.

Front-door consolidation should pay down compression debt.

---

# 12. Consolidation must reduce the live working set

Do not respond to stale documentation by producing only another synthesis file. Where appropriate: repair stale front-door prose; mark historical surfaces as historical; update links; remove dead links; collapse duplicate onboarding explanations; retire obsolete current-state claims; point detailed historical readers toward the surviving round record.

Guiding rule: history may grow; the live research state must remain compressed.

---

# 13. Current vs historical precedence

A future chatbot should not infer the research program's present view by counting mentions across the repository. Make it structurally clear that current-state interpretation should prefer human-canonical > agent-consolidated > lab/history, while still allowing newer lab evidence to challenge current canonical claims.

Prompts should remain historical records. Do not rewrite old prompts because terminology later changed. Similarly, round reports should normally remain intact except for clearly necessary pointer repair.

---

# 14. Keep provenance and endorsement separate

A result can be authored/discovered by an agent; Lean-verified; independently red-teamed; agent-consolidated; and not human-canonical. That is a perfectly coherent state.

Do not imply Lean-verified ⇒ maintainer-endorsed interpretation.

Stage III should be treated as the paradigmatic example: theorems correct + initial interpretation incorrect. Use this example, if useful, to explain why the layers exist.

---

# 15. Do not rush into `CLAIMS.md`

Inspect the current deference treatment of registered/workspace-established claims. Do not create `CLAIMS.md` merely to promote the status of existing Lean results.

The workspace may benefit from first having: verified substrate → agent consolidation → human selection → statement of record.

A small number of important human-selected claims is more useful than registering every kernel theorem. If the existing architecture clearly requires a change here, propose it for maintainer review rather than performing it casually.

---

# 16. Front-door wording should reveal the research methodology

One thing the workspace now genuinely demonstrates is: idea → formalization → challenge → correction → consolidation.

The root/project front door should make this visible. But avoid self-congratulatory language. Show the mechanics.

For example, Stage III is useful because: a comparator was built; the mathematics verified; an independent red team showed the interpretation collapsed; valid mathematics was retained under a corrected name; the positive theorem was not dispatched; successor requirements were recorded.

This is the kind of research behavior the repo is intended to make easy.

---

# 17. Keep the repo legible for external researchers

Assume a technically sophisticated alignment researcher opens the repository with little context. Within a few minutes they should be able to determine: what the workspace is; what research is currently active; what the deference/corrigibility question is; what has actually been formally constructed; what has been ruled out; what is still aspirational; where Formalized Agent Foundations enters; which surfaces are current versus historical; where to inspect proof artifacts; what question is controlling the next phase.

They should not have to understand the internal orchestration machinery first.

---

# 18. Human review surfaces

At the end of this pass, identify a small review surface for the maintainer. Do not ask the maintainer to review every changed sentence equally. Provide something like: proposed definition of human-canonical; proposed front-door description of the workspace; deference aspirational vs constructed gloss; debt taxonomy actually retained; any substantive change to current project framing.

Separate those from mechanical stale-link/count cleanup.

---

# 19. Procedural-bloat red team

Perform a deliberate second pass asking:

> What machinery did this ethos work create that is more expensive to maintain than the ambiguity it resolves?

Look for duplicated status fields; redundant documents; status requirements on low-value artifacts; mandatory templates; repeated counts; several files saying the same thing; a taxonomy nobody needs to act on; procedures requiring constant maintainer intervention.

Delete or simplify such machinery. The ethos pass should be able to demonstrate that it **removed more confusion than process it added**.

---

# 20. Parallel-safety with Stage IV

Stage IV is active.

Do not: alter future-agent semantics; change FUD comparator definitions; rename active Stage IV mathematical objects; modify Lean APIs; change finite harness behavior; reclassify provisional Stage IV findings as canonical; move active Stage IV files; modify Item 25/27 substance merely to fit the ethos vocabulary.

You may: improve current/historical labeling; point to Stage IV as active lab work; classify its provisional debt; repair unrelated front-door staleness; incorporate closed Stage III accurately.

If Stage IV closes before this pass does, reconcile with its **persisted final report**, not an earlier status message.

---

# 21. Suggested implementation target

Aim for something approximately this small: refine/finish `RESEARCH_STATE.md`; update root `README.md`; update `CONTRIBUTING.md` where it describes retired workflow; make minimal `AGENTS.md` changes needed to define the layers/conventions; repair `projects/deference/README.md`; repair `projects/deference/notes/README.md`; update `prompts/README.md` if needed to make prompts clearly historical/research-lab artifacts; correct obvious stale current-state claims in canonical/consolidated docs; preserve history.

Do not create many new files unless inspection shows a clear need.

---

# 22. Verification

Before closing: inspect every changed link; search for references to retired `frozen/`/`check_frozen.py` machinery; search for stale descriptions of the deference project as pre-round; search for broken pointers to scrubbed/deleted reports; search for contradictory theorem/file counts where exact counts remain; confirm historical prompt references are intentionally preserved; run repository documentation/house checks applicable to your changes; ensure Stage IV active artifacts are untouched unless a purely documentary link update was required; review the final diff specifically for procedural bloat.

---

# 23. Deliverable: before/after front-door audit

Persist or report a compact audit:

## Before

What would a fresh reader misunderstand?

## After

What can they now recover directly?

## Intentionally historical

What stale-looking material remains because it correctly records research history?

## Still unresolved

What compression debt remains?

---

# 24. Deliverable: proposed human-canonical delta

Do not mark substantive research material human-canonical yourself. Instead give the maintainer a small proposed delta. For example: adopt this description of the workspace; adopt this current deference question; adopt this aspirational/constructed philosophical distinction; adopt these debt categories; adopt this precedence rule.

Make approval cheap.

---

# 25. Commit discipline

Keep this ethos/front-door work separate from object-level Stage IV research. If currently mixed in the working tree, split it cleanly.

Commit with explicit model attribution according to repository policy.

If it reaches a coherent, independently reviewable endpoint, push it on its own branch / PR as appropriate under current repo practice.

Do not merge it yourself unless current maintainer instructions explicitly authorize that.

---

# 26. Final memo

End with:

1. What front-door inconsistencies did you find?
2. Which were repaired?
3. What did you deliberately preserve as history?
4. What is now the status of `RESEARCH_STATE.md`?
5. How are lab / agent-consolidated / human-canonical distinguished?
6. How are aspirational and constructed separated mathematically?
7. How are they separated philosophically?
8. Which debt categories survived contact with the actual repo?
9. What compression debt remains?
10. What procedural machinery did you decline or delete?
11. Can a fresh agent recover the current state without reading old rounds?
12. Can an external researcher understand the repo from the front door?
13. What exact maintainer judgments remain?
14. Did you touch any active Stage IV research semantics?
15. What are the human review surfaces?
16. Commit / PR state.

The governing criterion is:

[
\boxed{
\text{the repo should make the current research state easier to recover than the history that produced it.}
}
]

while preserving:

[
\boxed{
\text{the history needed to understand, challenge, and replay that state.}
}
]

And the repo should make it cheap to answer four questions:

[
\boxed{
\begin{array}{l}
\text{What are we trying to show?}\
\text{What have we actually constructed?}\
\text{What blocks the gap?}\
\text{What has a human actually adopted?}
\end{array}}
]

Do that with the least machinery that works.

**Prompt-author-model:** GPT-5.6 Sol (OpenAI)
