# Research Roadmap — the long arc

*Filed 2026-07-30 from Abram's spoken brain-dump of intentions for this folder and the deference-in-logical-induction project. This is the steward's copy of the vision: the staged arc, the cross-cutting programs, and pointers to where each piece is filed. The actionable versions live in the task and reading queues; this document is for re-orienting after time away.*

**How to use this file**: read the stage you're in, follow the pointers, and check `wiki/open-problems.md` for the live technical frontier. Stages are roughly sequential ("first… then… then…") but the cross-cutting mastery program (§B) runs in parallel with everything.

---

## A. The staged arc

### Stage 1 — Finish translating DDB (Deference Done Better) into logical induction
*Status: this is the current main work. Files: `li-deference.md` (working document), `wiki/` (per-result pages, `wiki/index.md`), `deference-in-logical-induction-v5.md`/`-v6.md` (older monoliths), `references/deference-done-better/`, `lean-deference/` (machine checks).*

Sub-goals, in Abram's words:
- A **more thorough exploration of all the trust principles** we might consider in logical induction (the five-variations analysis in `li-deference.md` §"Five Variations of Total Trust" and `wiki/deference-notions.md` are the start, not the end).
- **Finish reading DDB**, thinking about translations of the various results *as I go* — a reading-translation loop, not reading then translating.
- **Translate the accuracy material** of DDB to LI.
- Understand the **geometric difference between total trust and reflection** as explained in DDB.
- Understand the relationship between **per-sentence versions and whole-belief versions**, and the **convex/biconvex characterization**.
- Whatever else arises out of these explorations.

### Stage 1′ — Same treatment for "A Decision-Theoretic Approach for Managing Misalignment"
Give the Managing Misalignment paper the full DDB treatment: close reading, translation of its results into the LI setting, integration into the wiki corpus.

### Stage 2 — Legitimacy, and the open problems of the formalism
"Then figure out this legitimacy stuff, and work on the other stuff described in `li-deference.md` — all the open problems I've already listed for the formalism."
- Legitimacy: `legitimacy-theory-v1.md` is the existing draft.
- Open problems: `wiki/open-problems.md` (the live ledger), `li-deference.md`, plus the not-yet-imported items it lists (deference-v6 Appendix B, forcing-question pages).

### Stage 3 — Legitimacy meets syntax: inferentialism and the shape of theories
Relate legitimacy to syntactic stuff — **local rules of sanity** — connecting **inferentialist semantics to map-territory semantics**. Requires understanding inferentialism better, amongst other things. Threads to weave in:
- **Brandom** and **Habermas** (inferentialism; discourse ethics).
- The **market logic sequence** on LessWrong (Abram's own).
- Theories of **formality and informality**; **vagueness and crispness**; **fuzziness**; and other ways a theory can break out of the mold of "a set of sentences in a classical logic."

### Stage 4 — Condensation, and the dynamics of theories
Stage 3 connects to condensation, but furthermore wants a **dynamics of theories**: semantics as some kind of flow over time; understanding **ontological shifts**.

Specific analytical targets:
- Condensation uses essentially the **simplest available category-theoretic notion of probability transformation**, and characterizes "the same concept" through something like isomorphism. Spend real time analyzing **the notion of function, and the notion of isomorphism, involved**.
- Suspicion to investigate: **the observables are doing some of the work of making sure correspondence is meaningful**, in a way that could possibly be generalized. Rather than assuming a common set of "givens" between the two agents, look at a **richer representation of Alice interpreting Bob as a belief-haver**.
- Mine Abram's LessWrong posts on Condensation for the other ideas already written up there.
- Related existing task clusters in the task queue: the `[[implementation]]` cluster (causal implementation, triviality, degree-based recovery) and the `[[abstraction]]`/`[[condensation]]` cluster (Petersen, Wentworth's AIT framing, integration with condensation).

### Stage 5 — Abstraction + logical induction: the representation theorem
Having thoroughly explored existing theories of abstraction (and many variations), and having mastered the relevant math and proof technique: **a theory combining abstraction with logical induction in a natural way**, and a **representation theorem about when it is natural to interpret something as a logical inductor**.
- This would be a theory of **Dennett-style agency** (the intentional stance, made math): applying something like the **Wentworth representation theorem**, but for logical induction, within a theory of abstraction compatible with logical induction.
- Shape (details may turn out different): a relationship between **semantics and (imputed) syntax** — an LIA fitted to an LIC, but furthermore showing **when it is appropriate to interpret something that way**, using simplicity-like arguments. Might require a generalized LIC, transformed for the setting.
- Precursor already filed: the `[[udt]] [[tiling]]` representation-theorem intention in the project's task queue.

### Stage 6 — Decision theory in the right setting; scale-free agency
The Stage-5 object has a claim to being **the right setting to do decision theory in** — so do decision theory there. This is the continuation of the **Coherent Care** post (LessWrong, spring 2026).

Ultimate targets:
- A notion of **scale-free agency** based on a solid theory of the abstraction of agency, in turn based on a theory of abstraction which deconfused **"story of a blob"** — i.e., characterizes continuity of concepts over ontological crises while also characterizing agency itself.
- A **characterization of approximate cooperative equilibria as agents**, with meaningful advice about how to steer towards such equilibria.
- Along the way: insights about AI safety and alignment.

---

## B. Cross-cutting program: mastery, not just reading

"There's a lot of stuff I want to read or re-read and start making flashcards of; I'd like to achieve mastery over all this stuff — not just read it, but really become fluent in it. Work on learning stuff well at the same time as applying it and reformulating it."

- **Integrate spaced repetition into the research todo system.** This is itself a filed task (high priority in the task queue); the reading queue is the seed — a sampled reading/flashcard queue alongside the task queue. Related prior task: the incremental-reading-system task under the `[[abstraction]]` cluster.
- **The corpus to master** (seeded in the reading queue): information theory connected with Sam Eisenstat's condensation; algorithmic information theory (Steve Petersen's work); the structure and dynamics of theories; John Wentworth's work; Scott Garrabrant's work; Brandom and Habermas; and more as it arises.
- **All of Abram's LessWrong posts count as research todos** — to integrate into the picture. Likewise (longer horizon) the posts of Sam, Tsvi, Scott, Jessica, John, … Step-by-step integration into the growing picture, not a one-shot review. (The low-priority LessWrong-post-tracking-system task in the task queue is the tooling side of this.)

---

## C. Housekeeping (acknowledged, deliberately deferred)

The folder is disorganized: some older project stuff (pre-deference), now littered with deference-in-logical-induction files at top level. **This is fine for now** — the project is the main work and isn't too large yet. A low-priority reorganization task is filed so it doesn't get forgotten. When it happens, the wiki (`wiki/`) is already the model: per-result pages beat monoliths.

---

## D. Where everything is filed

| Intention | Filed as |
|---|---|
| Finish DDB → LI translation (all five sub-goals) | the task queue, high-priority parent task with subtasks |
| Managing Misalignment → LI treatment | the task queue, high-priority |
| Spaced repetition in the todo system | the task queue high-priority + the reading queue  |
| Legitimacy + open problems | the task queue, medium; `wiki/open-problems.md`; `legitimacy-theory-v1.md` |
| Inferentialism / rules of sanity / Brandom, Habermas | the task queue, medium; readings in the reading queue |
| Condensation function/isomorphism analysis; observables suspicion | the task queue, medium |
| Dynamics of theories / ontological shifts | the task queue, medium |
| Representation theorem; scale-free agency / Coherent Care | the task queue, low-priority north-star task (details here, §A5–A6) |
| Reading & flashcard corpus | the reading queue |
| Folder reorganization | the task queue, low-priority |
