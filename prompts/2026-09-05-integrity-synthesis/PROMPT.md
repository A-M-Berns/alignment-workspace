Work in `A-M-Berns/alignment-workspace`.

You are the **orchestrator** for the next research batch. Your job is not to solve the agenda yourself. Orient against current `main`, dispatch several sharply separated subagents in parallel, make them produce auditable artifacts, then synthesize what survived cross-examination.

At dispatch time, expected `main` is:

`5ff9539b44debc464128e6a1921ef1690f7b6487`

PR80, PR82, the conceptual wiki consolidation PR83, and the PR84 `.lake` hygiene fix have landed. If `main` has moved, use the actual current `main` and record the difference rather than forcing this SHA.

Read `AGENTS.md` first and obey it.

Then run/read:

```sh
python3 -m checkers.workspace_state --json
```

and inspect at minimum:

* `DECISIONS.md`
* `PRIORITIES.md`
* `RESEARCH_STATE.md`
* `wiki/Legitimacy.md`
* `wiki/Integrity.md`
* `wiki/Settlement-Interface.md`
* `wiki/Openness-Coverage-and-Non-Capture.md`
* `wiki/Normative-Induction.md`
* `wiki/Normative-Inductor.md`
* `wiki/Roadmap.md`
* the landed PR80 defeat/standing round
* the landed PR82 Normative Inductor realization
* relevant current Lean spines when a subtask reaches formal statements.

The wiki is explicitly permitted as conceptual orientation for this dispatch. It is not proof evidence.

Do **not** edit the wiki in this batch. The latest conversation introduces research hypotheses that are deliberately newer than the current wiki and should be tested before becoming canonical.

# Shared research orientation

Hold the following as the current starting picture, with the indicated epistemic status.

## Fairly settled architecture

Legitimacy is fundamentally about **cognitive evolution**, not absolute certification of a state from first principles.

The proof-relevant object is naturally a history segment

$$
H_{m:n},
$$

while the useful downstream-facing object is likely an endpoint relation such as

$$
H_m \preceq_{\mathrm{leg}} H_n,
$$

witnessed by a legitimate intervening segment.

A trajectory may inherit bad starting commitments. Legitimacy constrains how those commitments are subsequently revised, challenged, answered, defeated, discharged, represented, or extended.

Declared normative scope is application-relative. This is a modeling parameter, not a defect of the generic theory.

Integrity and Non-Capture are different:

* **Integrity:** did the trajectory faithfully preserve and account for what entered it?
* **Non-Capture:** could the process improperly determine what was able to enter, challenge, or evaluate it?

Non-Capture is intentionally billed to an external counterfactual/institutional theory.

Counterfactual practical/value semantics are likewise intentionally billed to an external theory. The generic Normative Inductor should specify what certificate is required and prove what follows from it, rather than solve general counterfactual identification.

## Working hypothesis to test, not doctrine

The most important new hypothesis is:

$$
\boxed{
\text{Trajectory Integrity}
\Longrightarrow
\text{Diachronic Answerability}.
}
$$

Do **not** assume this is true by definition.

Test whether the existing Answerability Conservation machinery is really the obligation/debt projection of a more general Integrity theorem, or whether normative debt conservation requires an additional primitive axiom that generic history integrity does not supply.

## New settlement distinction to test

The current wiki partially conflates two layers. Use the following cleaner hypothesis as the starting point.

An **external settlement item**

$$
s\in \operatorname{SetView}(H_n)
$$

is an authenticated input supplied through the declared trusted settlement boundary.

The evolving internal reasoner separately judges something like

$$
\boxed{
\operatorname{Closes}(H_n,s,\alpha)
}
$$

meaning:

> according to the rules/reasons legitimately in force at \(H_n\), settlement item \(s\) is sufficient to close obligation \(\alpha\).

The actual normative transition is a discharge backed by:

1. authenticated availability of \(s\);
2. an internally valid `Closes` certificate;
3. whatever authority/provenance conditions Integrity requires.

Thus:

```text
external settlement item
        ↓
internal Closes judgment
        ↓
discharge event
```

Do not assume that a settlement item arrives already semantically typed as “settles obligation α”.

Settlement items may remain immutable even while the reasoner's judgment about their relevance changes.

A later reasoner may discover that an earlier `Closes` judgment was defective. The desired response is probably not retroactive history rewriting. It may instead incur a new reopening/reconsideration obligation. This is a research question for the Integrity lane.

The meaning of the external settlement trust boundary is domain-relative. In a narrow empirical domain it might authenticate a specific observation/report atom. At the most general epistemic level, it may bottom out in assumptions about the trustworthiness of perception, memory, or basic cognitive functioning.

Do not force one universal settlement ontology.

# Parallel phase: dispatch five subagents

All five should start from the same resolved `main`.

Keep them isolated from one another during their initial pass. Do not let one agent's proposed definitions silently become another's assumptions.

Each subagent gets its own branch/worktree and its own uniquely named research-round directory. Avoid shared-file conflicts. In the initial phase, subagents should not edit:

* `wiki/**`
* `DECISIONS.md`
* global vocabulary/state files
* existing consolidated/frozen artifacts.

If a subagent discovers a structural blocker that repository rules require filing, have it report the proposed filing to you; the orchestrator may make shared register changes centrally during synthesis rather than have several workers race on the same files.

Each subagent must preserve the repository evidence taxonomy. External facts enter as hypotheses, not Lean axioms.

## Agent A — Constructive Integrity / Legitimate Evolution

This is the primary theory-discovery worker.

Its problem:

> Find the smallest mathematically clean theory of Integrity for cognitive/normative history segments and determine whether Diachronic Answerability follows from it.

It should inspect all relevant existing machinery rather than redesign from memory:

* normative continuity;
* anchored slices;
* authenticated semantic transfer;
* faithful semantic preservation;
* unified grounds;
* defeat;
* standing;
* settlement interface;
* answerability carriers;
* current history abstractions.

Core questions:

1. What is the minimal history/event substrate required to state Integrity?

2. Can Integrity be characterized by a local transition predicate such as

   $$
   \operatorname{ValidStep}(H_n,e,H_{n+1})
   $$

   whose iteration gives a global segment theorem?

3. Which things must be immutable?

4. Which things may legitimately evolve?

5. What exactly must remain anchored across representational/ontological change?

6. Can provenance, authority, no-self-grounding, replayability, and anti-laundering be compressed into one general transition discipline?

7. How should authenticated external settlement items enter?

8. How should internal

   $$
   \operatorname{Closes}(H,s,\alpha)
   $$

   be represented?

9. If a later state rejects an earlier `Closes` judgment, what integrity-preserving mechanism reopens or reconsideres the matter without rewriting history?

10. Does answer / valid discharge / carry emerge as a theorem for obligation components?

11. If not, identify the exact extra normative axiom required.

12. Is the proof-relevant primitive best a history segment while the consumer-facing abstraction is an endpoint relation?

13. What composition theorem is available?

Aim for something like:

$$
\operatorname{Integrity}(H_{m:n})
\land
\operatorname{Integrity}(H_{n:k})
\Rightarrow
\operatorname{Integrity}(H_{m:k}),
$$

and, if justified,

$$
\operatorname{Integrity}(H_{m:n})
\Rightarrow
\operatorname{AnswerabilityConservation}(H_{m:n}).
$$

Do not force a preorder/category presentation merely because composition exists.

Produce:

* proposed minimal definitions;
* theorem spine;
* comparison to current Answerability machinery;
* explicit countermodels for discarded clauses where feasible;
* Lean definitions/lemmas for the parts that are naturally structural;
* exact fixtures for finite counterexamples;
* a crisp verdict on the working hypothesis `Integrity -> Answerability`.

Do not edit current conceptual wiki pages.

## Agent B — Integrity adversary / laundering audit

This worker is intentionally hostile to the compression proposed above.

Its problem:

> Assume we try to replace much of the existing Answerability machinery with a generic Integrity-of-history theory. Find every way a trajectory can still launder normative debt while satisfying superficially plausible integrity conditions.

Initially work independently of Agent A.

Attack at least:

* revision of the rule determining `Closes`;
* a genuine settlement item given a newly convenient interpretation;
* retroactive reopening versus silent retroactive invalidation;
* changing applicability under ontology revision;
* semantic renaming;
* obligation splitting;
* obligation merging;
* successor chains and cycles;
* replacing an old obligation with a weaker “new” one;
* forged or circular provenance;
* self-grounded authority;
* moving live debt to answered status through representation change;
* later changes to standing/licence retroactively affecting old transitions;
* genuine external settlement facts used under invalid internal closure rules;
* challenge/disposition chains that preserve syntax while losing substantive debt;
* coalitions laundering standing or authority;
* histories that are replayable but normatively evasive.

Distinguish carefully:

* failure of generic Integrity;
* failure of Answerability specifically;
* failure of Non-Capture instead;
* failure of external settlement soundness instead.

The key question is:

$$
\boxed{
\text{Is debt conservation really derivable from generic history integrity?}
}
$$

Produce the smallest counterexamples you can.

Where possible, make them exact executable fixtures or Lean countermodels.

Do not “repair” each attack immediately. Classify which missing condition would block it and whether that condition belongs in:

* generic Integrity;
* obligation-specific Answerability;
* Non-Capture;
* settlement trust;
* practical semantics.

## Agent C — Non-Capture certificate minimization

This worker is not to invent a universal counterfactual semantics.

Its problem:

> Determine the weakest external certificate that the legitimacy theory actually needs in order to derive Robust Openness.

Treat declared normative scope and declared intervention class as application inputs.

Start from something schematically like:

$$
\operatorname{NonCaptureCert}
(P,\Gamma,\mathcal J,\mathfrak I).
$$

Determine which properties must survive interventions in \(\mathcal J\).

Candidates include:

* target/concern identity;
* applicability;
* representability;
* route existence;
* standing/access;
* route efficacy;
* ability to produce an accountable receipt;
* relevant settlement/evaluation access.

Do not include a clause merely because it sounds normatively desirable. Give an attack showing why each clause is required, or remove it.

Separate:

* actual-prefix Coverage;
* counterfactual persistence of the route;
* counterfactual persistence of the concern's identity/applicability;
* counterfactual efficacy once the route is exercised.

Ask what coupling/holding-fixed information an external counterfactual framework must provide.

The desired output is an interface theorem approximately of the form:

$$
\operatorname{Coverage}_{\mathrm{actual}}
+
\operatorname{NonCaptureCert}
\Rightarrow
\operatorname{RobustOpen}.
$$

Compare several possible external intervention semantics only to determine the bill our theory issues. Do not choose a universal causal framework.

Produce:

* minimal certificate schema;
* clause-by-clause necessity attacks;
* exact distinction from Integrity;
* what an application must instantiate;
* what remains genuinely outside the generic theory.

## Agent D — Practical / counterfactual semantics certificate minimization

This worker is likewise an interface-minimization agent.

Its problem:

> Determine the weakest practical-semantics certificate the abstract Normative Induction theorem needs, and which factorizations are merely convenient realizations.

The public endpoint is something like:

$$
\boxed{
\operatorname{PracticalCert}(e,s):
\quad
\mathbb E[\ell_e(Y_s)]
\le
M_{es}d_s+\epsilon_{es}.
}
$$

Do not assume that scalar counterfactual value vectors are the definition of practical semantics.

PR82's value-correspondence path is one sufficient factorization:

```text
authenticated counterfactual semantics
        ↓
value calibration / ambiguity
        ↓
approximate decision rule
        ↓
decision regret
        ↓
anchored response adequacy
        ↓
PracticalCert
```

Test whether this factorization is:

* minimal;
* unnecessarily strong;
* appropriate only for utility-like domains.

Find other direct sufficient routes if natural, especially for procedural, constraint-like, rights-like, or non-scalar obligations.

Press on **joint practical-response compatibility**:

One service occurrence produces one realized decision/response distribution. If several exposures are matched to it, each edge certificate must apply to that same response.

Characterize the weakest useful bundle-level or edge-level condition ensuring this.

Possible legitimate outcomes of incompatibility include:

* different service contexts;
* upstream licensed adjudication/aggregation;
* a common adequate response;
* residual mass.

Do not let “joint price-space feasibility” stand in for practical compatibility.

Produce:

* minimal public certificate;
* one or more sufficient factorizations;
* necessity/counterexample results;
* exact bill to an external counterfactual/evaluation theory;
* relation to the existing PR82 theorem constants.

Do not solve general counterfactual identification.

## Agent E — End-to-end Normative Inductor gap auditor / theorem grinder

This worker treats specification uncertainty as typed hypotheses and asks how much of the remaining composed theorem is now mechanical.

Its problem:

> Starting from current `main`, enumerate the exact theorem gaps between the landed components and a conditional end-to-end Normative Inductor theorem, then prove or mechanize the agent-sized ones without redesigning the conceptual theory.

It should consume, as abstract hypotheses where needed:

* an Integrity / legitimate-evolution certificate;
* a Robust Openness / Non-Capture certificate;
* a settlement trust interface;
* a practical-response certificate.

It should not invent their semantics.

Audit the current chain:

```text
history
  -> qualitative obligation export O_P
  -> compiler
  -> joint operative region
  -> affordable service
  -> traderized uptake
  -> practical response
  -> service transport
  -> Progress
  -> preservation of ordinary LI
```

Identify the exact missing statement at each arrow.

High-value targets include:

* unified concrete event/history export;
* `O_P` adapter theorem;
* compiler-soundness theorem for a declared schema;
* accountable `Conflict` / `Unknown`;
* representability hypotheses stated at the correct level;
* joint-feasibility lemmas;
* declared-workload affordable scheduling;
* bundle/edge practical compatibility plumbing;
* full finite-horizon Progress transport theorem;
* quantitative semantic-transport composition;
* effective projection/compiler conditions;
* augmented-trader preservation of LI;
* a final conditional theorem whose assumptions are all named and independently dischargeable.

Mechanize what is naturally mechanizable.

Do not encode semantic or causal assumptions as Lean axioms.

When a gap is substantive rather than mechanical, state the exact typed hypothesis and continue the composition beyond it.

The deliverable should make it obvious how much of the remaining end-to-end gap is:

* actual mathematical research;
* formalization/integration work;
* an intentionally external contract.

# Phase-two cross examination

After the five initial reports exist, do not immediately average them into a synthesis.

Run targeted cross-review.

## Cross-review 1: Agent B attacks Agent A

Give the Integrity adversary Agent A's exact definitions/theorem spine.

Ask B to find:

* a model satisfying A's Integrity but violating existing Answerability desiderata;
* a history that passes A's local transition checks while laundering debt;
* a composition failure;
* a problematic interaction with evolving `Closes`;
* an example showing A has accidentally imported Non-Capture or settlement truth into Integrity.

Then give A only the concrete attacks and let A repair or concede.

Do not allow definitional patching without explaining what conceptual clause the patch represents.

## Cross-review 2: Agent E checks Agents C and D as interfaces

Give the realization auditor the proposed Non-Capture and Practical-Semantics bills.

Ask:

> Are these sufficient as typed hypotheses for the actual end-to-end composition, or is some missing output discovered only when attempting to consume them?

This is an interface type-check, not permission for E to expand the bills with implementation details.

If E finds a missing output, send that specific issue back to C or D.

## Optional follow-ups

Spawn at most two additional focused workers if and only if the first cross-review exposes a precise mathematical fork that would benefit from an independent result.

Do not respond to disagreement by launching another broad architecture round.

# Settlement issues the synthesis must resolve or clearly leave open

The batch should return a position on the following distinctions.

### External settlement item

What minimal assumptions make

$$
s\in\operatorname{SetView}(H)
$$

a legitimate trusted input?

Separate at least:

* provenance/interface authenticity;
* epistemic trustworthiness of the source;
* monotonicity or immutability, if actually required;
* anti-suppression/non-capture properties.

Do not automatically put all four under the name “Settlement Integrity”.

In particular, the current wiki phrase “cannot delay or suppress settlement” may belong to Non-Capture rather than internal/interface Integrity. Test the typing rather than inheriting it.

### Internal closure judgment

Clarify the role of

$$
\operatorname{Closes}(H,s,\alpha).
$$

The reasoner uses its evolving rules/reasons to decide whether an authenticated external item is enough to discharge \(\alpha\).

Determine:

* what authenticates that judgment;
* whether closure rules themselves need anchored provenance;
* whether a valid discharge remains an immutable historical fact after the reasoner later rejects its old closure reasoning;
* how reconsideration/reopening is represented;
* whether the original obligation token stays terminal while a successor/reconsideration obligation is born.

Do not let “settlement-backed discharge” collapse external settlement truth, internal reasoning, and the discharge transition into one primitive relation unless the analysis proves that is preferable.

# Orchestrator synthesis

After cross-review, produce a compact synthesis rather than a mega-report.

The synthesis should answer:

1. **What is the best current type for Integrity?**
2. **Does Integrity imply Diachronic Answerability?**

   * yes under exactly which hypotheses;
   * no, with the minimal extra normative clause;
   * or still unresolved, with the smallest separating countermodel.
3. **What is the best proof-relevant type for legitimate evolution?**
4. **What endpoint relation should downstream deference/corrigibility consume?**
5. **What exactly is an external settlement item?**
6. **What exactly is the internal `Closes` judgment?**
7. **What happens when later cognition overturns an earlier closure rationale?**
8. **What is the minimal Non-Capture bill?**
9. **What is the minimal Practical-Semantics bill?**
10. **How is joint practical compatibility typed?**
11. **Which remaining NI gaps are agent-sized integration theorems?**
12. **Which remaining gaps are genuine research?**
13. **Which gaps are intentionally external and should stop appearing as internal TODOs?**

Give one dependency graph for the resulting program.

For every proposed theorem/interface, label it as one of:

* Lean-proved;
* exact witness/counterexample supported;
* paper-derived;
* proposed definition/interface;
* ambient assumption;
* open problem.

Do not promote any result merely because multiple agents agree with it.

# Repository outputs

Each subagent should have its own local round artifact with:

* verbatim dispatched prompt;
* concise report;
* theorem/counterexample ledger where appropriate;
* implementation/tests/Lean where appropriate;
* provenance.

The orchestrator should maintain a separate synthesis round that depends on the five worker rounds.

Do not merge worker branches directly into `main`.

Do not edit canonical wiki/decision/vocabulary surfaces merely to reflect research conclusions.

At the end, prepare either:

1. one synthesis PR containing only non-conflicting research artifacts and mechanized results that are genuinely ready for review, or
2. a clean report saying why no integration PR should yet be opened.

Canonical conceptual changes should be presented as explicit recommendations for a later maintainer consolidation, unless this dispatch uncovers a narrow correction required for factual accuracy.

Run all relevant project tests and repository checks on any proposed integrated branch.

# Success criterion

The purpose of this batch is **not** to announce a finished legitimacy theorem.

It is to turn the remaining conceptual uncertainty into a small number of typed interfaces and theorem obligations.

A successful batch should leave us able to say, with precision:

```text
what Integrity guarantees,
whether Answerability is derived from it,
what settlement gives from outside,
what Closes is decided inside,
what Non-Capture must certify,
what practical semantics must certify,
and exactly what remains to compose a Normative Inductor theorem.
```

If that decomposition survives the adversarial passes, the next phase should be theorem completion rather than another architecture search.
