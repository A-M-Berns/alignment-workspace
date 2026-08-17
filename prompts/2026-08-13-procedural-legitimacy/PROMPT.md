# Agent Task: Prosecute the Four-Condition Theory of Procedural Legitimacy

**Maintainer:** A. M. Berns
**Model provenance:** GPT-5.6 Sol
**Date:** 2026-08-12

## Mission

Investigate whether the emerging four-condition architecture is sufficient for **procedural legitimacy of a bounded reasoner’s trajectory**, and determine the precise mathematical form each condition must take.

The four candidate components are:

\[
\boxed{
\text{Provenance}
+
\text{Inquiry Adequacy}
+
\text{Reasons-Responsiveness}
+
\text{Diachronic Answerability}
}
\]

The central question is:

\[
\boxed{
P + I + RR + DA
\stackrel{?}{\Longrightarrow}
\text{Procedural Legitimacy}.
}
\]

Do **not** assume the answer is yes.

The primary objective of this round is to try to construct a trajectory satisfying all four candidate properties that should nevertheless count as procedurally illegitimate. If such a counterexample exists, isolate the missing fifth property or show that one of the four has been formulated too weakly.

This is a sufficiency prosecution, not primarily an implementation round and not primarily a terminology round.

The task must end in a draft PR containing the strongest surviving definitions, attacks, counterexamples, theorem/conjecture map, and an explicit verdict on sufficiency.

---

# I. Current Research Architecture

The former umbrella program developed under `projects/leverage/` has recently been reorganized into a clearer architecture.

The current live picture distinguishes:

### A. Normative constraint/statics

A reasoner state \(x\), a context of available reasons \(r\), and a normative constraint

\[
\Gamma(x,r)
\]

describing which successor states or edits are admissible.

The statics include the existing machinery concerning reasons/warrants, applicability, commitments, defeaters, credal constraint, constraint propagation, settlement, enforcement, and related finite constructions.

### B. Trajectory conditions

The previous round extracted two distinct trajectory-level conditions.

**Reasons-responsiveness (RR):**

\[
x_{t+1}\in\Gamma(x_t,r_t).
\]

Each individual transition must be licensed by the reasons available at its date.

**Diachronic answerability (DA):**

Normative liabilities must remain traceable across changes in standards, commitments, representation, vocabulary, or ontology. They may remain live, migrate, suspend, split/refine, or receive a backed terminal disposition, but they may not silently disappear.

The previous round found a genuine end-to-end conservation/composition structure on the answerability side.

### C. The previous sufficiency failure

The previous legitimacy prosecution showed that

\[
RR + DA
\]

is not sufficient.

Three attacks exposed a common boundary problem:

1. a reasoner can file a ground that authorizes a standards change and then use it;
2. a reasoner can manufacture defeaters for inconvenient reasons;
3. a relevant demand can simply fail to enter the docket.

This exposed two additional candidate requirements:

- **provenance discipline** on grounds/reasons;
- **coverage or inquiry adequacy** governing which demands/questions enter deliberation.

The same round also inherited an independent impossibility from the deference line: two trajectories may have identical records while differing radically in advisor influence. Therefore **no record/process predicate alone can guarantee absence of steering or endpoint corruption**.

This round must respect that boundary.

The target is **procedural legitimacy**, not total alignment, endpoint legitimacy, or manipulation-freedom.

---

# II. The Target Concept: Procedural Legitimacy

Before modifying implementations, state an independent target notion of procedural legitimacy.

Do not define it as “whatever satisfies the four conditions.”

The intended concept is approximately:

> A trajectory is procedurally legitimate when the reasoner encounters the normative demands it is entitled to confront, receives and uses reasons only with authority justified by their provenance, makes each revision in accordance with the resulting normative constraints, and remains answerable for inherited normative liabilities throughout conceptual and evaluative change.

A sufficient theory should rule out, at minimum:

- self-authorization;
- circular or retroactive authorization;
- laundering authority through long chains of derivative reasons;
- changing standards without an appropriately grounded licence;
- suppressing entitled inquiries;
- strategically manipulating which questions become live;
- silently deleting liabilities through vocabulary or ontology change;
- unauthorized merging of distinct liabilities;
- discharge without appropriate backing;
- making a revision merely because it erases charge or historical responsibility.

It must nevertheless permit:

- endogenous discovery of new reasons;
- proof, inference, and conceptual innovation;
- generation of genuine defeaters;
- revision of the reasoner’s own standards;
- revision of inquiry procedures;
- ontology and vocabulary change;
- reversal of earlier judgments;
- transformation whose endpoint would not have been endorsed by the initial state.

The framework must therefore distinguish **legitimate transformation** from both conservatism and laundering.

---

# III. Candidate Property 1: Provenance

The previous round represented grounds with an exogenous/endogenous source field but did not let the normative constraint read it. That was intentionally insufficient.

Do not solve provenance by declaring:

> external reasons good; internal reasons bad.

A bounded reasoner must be able to produce reasons itself.

Instead investigate a notion closer to **typed, non-circular authority ancestry**.

A candidate ground may have structure such as

\[
g =
(\text{content},
\text{origin},
\text{basis},
\text{authority scope},
\text{time}).
\]

Investigate a judgment of the form

\[
\Pi_t(g,c)
\]

meaning that at time \(t\), ground \(g\) has a valid provenance certificate entitling it to bear on coordinate or transition-component \(c\).

Questions to answer:

1. What is the minimal information a provenance object must contain?
2. What distinguishes deriving a new reason from manufacturing new authority?
3. How should authority propagate through inference?
4. Can authority weaken, strengthen, or only preserve under derivation?
5. What prevents cycles such as

   \[
   g_1 \text{ authorizes } g_2,
   \qquad
   g_2 \text{ authorizes } g_1?
   \]

6. What prevents a standards change from creating the authority that retroactively licenses that same standards change?
7. Does provenance require a well-founded graph, a temporal ordering, a typed derivation system, capability-like scopes, or some combination?
8. How do advisor-supplied reasons differ from advisor-supplied authority?
9. Can the same content be legitimate for one purpose but illegitimate for another?

A promising principle to prosecute is:

> **No authority amplification:** a derived ground may not possess normative jurisdiction that cannot be traced to appropriately scoped authority in its ancestry.

Do not adopt this principle without testing it.

Determine whether provenance belongs:

- inside the definition of the valid reason context supplied to \(\Gamma\);
- as an independent trajectory condition;
- or partly in both.

A likely target is something like

\[
R_t^{\mathrm{valid}}
=
\{g\in R_t:\Pi_t(g,c)\text{ holds for the use in question}\}
\]

followed by

\[
x_{t+1}\in\Gamma(x_t,R_t^{\mathrm{valid}}).
\]

But extract the best abstraction from the existing machinery rather than forcing this exact syntax.

---

# IV. Candidate Property 2: Inquiry Adequacy

The previous coverage model compared the docket against a declared arrival list.

That is not sufficient for the intended theory.

If an advisor or reasoner controls which demands ever “arrive,” then perfect coverage relative to a manipulated arrival list is vacuous.

This round should investigate an **inquiry-generation model**.

A candidate structure is:

\[
I_t(h_{\le t})
=
\text{the inquiries generated by the situation/history at time }t.
\]

Then introduce some notion of entitlement:

\[
\operatorname{Entitled}_t(q).
\]

The docket/service layer may then satisfy something like

\[
\operatorname{Entitled}_t(q)
\Longrightarrow
\exists s\le t+\Delta:
\big(
\operatorname{Docketed}_s(q)
\lor
\operatorname{BackedRefusal}_s(q)
\big).
\]

Do not assume this is the right form.

Investigate at least three distinct questions:

### A. Inquiry generation

What features of a case, environment, existing commitments, contradictions, unresolved liabilities, defeaters, or observations generate a new inquiry?

Can the existing decision-docket / case-generation work supply this object?

### B. Entitlement

Not every syntactically generable question must impose a normative obligation.

What makes an inquiry one the reasoner is obligated to confront?

Can entitlement be grounded in:

- prior commitments;
- standing schemas;
- practical decisions that must be made;
- unresolved contradictions;
- existing liabilities;
- environment-triggered cases;
- explicit requests from authorized sources?

### C. Coverage/service

Once an entitled inquiry arises, what must happen?

Possibilities include:

- docket it;
- answer it;
- explicitly suspend it;
- refer it;
- refuse it with backing;
- generate a descendant inquiry that inherits the obligation.

Determine the relation between inquiry objects and the existing answerability ledger.

A promising architecture is:

\[
\text{Encounter}
\rightarrow
\text{Inquiry generation}
\rightarrow
\text{Docket/service obligation}
\rightarrow
\text{Judgment}
\rightarrow
\text{Answerability}.
\]

Test whether the existing proposed decision-docket machinery can be reinterpreted as the service layer of this inquiry model.

---

# V. Candidate Property 3: Reasons-Responsiveness

Make RR as abstract and austere as possible.

The intended core remains approximately:

\[
RR_t
\iff
x_{t+1}\in\Gamma(x_t,R_t^{\mathrm{valid}}).
\]

But prosecute the exact form.

The state \(x_t\) must be rich enough that RR applies reflexively to changes in the reasoner’s own machinery.

At minimum investigate whether \(x_t\) must include:

- substantive commitments;
- standards/applicability rules;
- vocabulary/ontology;
- inquiry-generation rules;
- entitlement rules;
- docket/service rules;
- liability state;
- relevant policy state.

A reasoner must not be able to evade RR merely by changing the mechanism that determines what RR reads.

Determine:

1. what exactly belongs inside the state;
2. what belongs inside the reason context;
3. which transitions are subject to RR;
4. whether no-op is always admissible;
5. whether the verdict should remain three-valued:

   \[
   \{\text{admitted},\text{refused},\text{uncertified}\};
   \]

6. whether magnitude/resource allowances must be consumable across time;
7. whether availability should be monotone;
8. which form of cost/profitability blindness is actually required;
9. whether a provenance-valid reason context suffices to close the filing gap.

Do not require composite admissibility from \(x_0\) to \(x_T\). The existing transformative examples show why that would be too conservative.

---

# VI. Candidate Property 4: Diachronic Answerability

Do not freeze the next theory around the existing single-valued notion of “one fate per original liability” without checking branching refinement.

A liability may evolve as

\[
\ell
\rightarrow
\{\ell_1,\ell_2\},
\]

after which one branch can be discharged while another remains live.

The conserved object may therefore need to be a **fate forest**, partition, or transport structure rather than a single fate label.

Investigate an object of the form

\[
F_{s\to t}(\ell)
\]

recording all descendants and terminal/suspended branches of \(\ell\).

A possible endpoint representation is:

\[
F_T(\ell)
=
(
L_T,
S_T,
D_T
)
\]

where:

- \(L_T\) is a set/tree of live descendants;
- \(S_T\) is a set/tree of suspended descendants with routes;
- \(D_T\) is a set/tree of terminal branches with backing.

The target conservation theorem should ideally say:

> Every branch descending from an initial liability is accounted for exactly once as live, suspended with a route, or terminally disposed with the required backing.

And a composition theorem should take a form analogous to

\[
F_{0\to T}
=
F_{s\to T}\circ F_{0\to s}.
\]

Questions to settle:

1. what is the correct carrier: relation, forest, DAG, multiset, transport morphism, or another object?
2. how are refinement and identification represented?
3. when may two liabilities merge?
4. what prevents an authorized merge from laundering a distinction that mattered?
5. what is required for discharge?
6. what is required for declared loss?
7. how does suspension compose?
8. how does conceptual migration interact with branching liability identity?
9. can endpoint audit avoid replay of the full history?

Before porting the previous conservation result into Lean, test explicitly whether mixed branch fates break its current abstraction.

---

# VII. The Central Sufficiency Question

Once the four properties have precise candidate forms, prosecute:

\[
P + I + RR + DA
\stackrel{?}{\Longrightarrow}
L^\star
\]

where \(L^\star\) is the independent procedural-legitimacy target stated at the beginning of the round.

The key test is not whether each property independently stops its motivating attack.

The key test is:

> **Can all four hold simultaneously in a trajectory that is still procedurally illegitimate?**

Prefer a minimal finite counterexample over a vague philosophical objection.

If a counterexample exists, classify it:

1. one property was formulated too weakly;
2. interaction between two properties requires a compatibility condition;
3. a genuinely fifth property is needed;
4. the target concept of procedural legitimacy was itself underspecified.

Do not automatically add a fifth conjunct. First attempt to strengthen or correctly type the existing four.

---

# VIII. Mandatory Whole-Architecture Attacks

Construct small adversarial trajectories satisfying as many of the proposed conditions as possible.

The final prosecution must include at least the following.

### Attack A: Long-chain authority laundering

No direct self-filed permission.

Instead construct:

\[
g_0\to g_1\to\cdots\to g_n
\]

such that each local derivation appears permitted but the final ground acquires authority not present at the root.

Does provenance detect this?

### Attack B: Circular authorization

Construct mutually supporting reasons, standards, or provenance certificates.

Can a finite cycle manufacture authority?

### Attack C: Pre-emptive inquiry-rule revision

The reasoner legitimately revises its inquiry-generation machinery immediately before a case that would otherwise produce an inconvenient inquiry.

All provenance and RR conditions should be respected.

Does inquiry adequacy still catch it?

### Attack D: Entitlement laundering

Leave generation intact but revise the rule determining which generated questions are entitled to service.

Can the reasoner make an inquiry “not count” just before it matters?

### Attack E: Formulation manipulation

Generate and docket a question, but formulate it so narrowly that the relevant issue is never actually considered.

Can the model distinguish:

\[
\text{“question appeared”}
\]

from

\[
\text{“the substantive demand was represented”}?
\]

### Attack F: Coverage flooding

Generate or docket a huge number of formally distinct inquiries so that a salient one is indefinitely delayed while nominal coverage remains high.

Does inquiry adequacy require deadlines, priority, service guarantees, or resource-sensitive fairness?

### Attack G: Provenance-valid defeater laundering

Generate defeaters through apparently legitimate derivations rather than arbitrary self-filing.

Can provenance + inquiry + RR + DA still allow systematic escape from every adverse reason?

### Attack H: Branch-selective answerability

Split one inconvenient liability into several descendants, discharge convenient branches, and preserve only a weakened remainder.

Can DA detect loss of substantive burden despite perfect formal lineage?

### Attack I: Authorized distinction collapse

Merge two liabilities through an apparently authorized identification.

Can all four properties hold while a normatively important distinction is destroyed?

### Attack J: Profitable-but-formally-licensed laundering

Find a trajectory where every transition is genuinely licensed and all liabilities are accounted for, but the sequence is chosen specifically because it removes future accountability cost.

Does the existing cost-blindness condition actually prevent this at the appropriate level?

### Attack K: Radical legitimate transformation

A positive adversary against excessive conservatism.

The reasoner must be able to:

- change its concepts;
- revise its standards;
- revise its inquiry rules;
- reverse a major judgment;
- produce new endogenous reasons;

while satisfying all four conditions.

If the architecture rules this out, it is too strong.

### Attack L: All-four counterexample

The highest-priority test.

Construct, if possible:

\[
P=I=RR=DA=\text{true}
\]

while the trajectory is clearly procedurally illegitimate according to the independently stated target.

Spend substantial effort here.

---

# IX. Independence and Necessity Tests

Also seek witnesses for:

- \(P\) without \(I\);
- \(I\) without \(P\);
- RR + DA without provenance;
- P + RR + DA without inquiry adequacy;
- P + I + DA without RR;
- P + I + RR without DA.

Determine whether each component adds a genuinely independent restriction.

Then test whether any component can be absorbed into another at the correct abstraction level.

In particular:

- provenance may belong inside the construction of \(R_t^{\mathrm{valid}}\);
- coverage may decompose into generation + entitlement + service;
- inquiry-service obligations may generate liabilities consumed by DA.

A cleaner factorization is preferable to four labels maintained only for symmetry.

---

# X. Relationship to the Inquiry/Docket Work

Explicitly inspect the existing answerability-docket and proposed decision-docket/inquiry material.

Determine whether the right architecture is approximately:

\[
\text{Case / encounter}
\overset{G}{\longrightarrow}
\text{generated inquiry}
\overset{E}{\longrightarrow}
\text{service entitlement}
\overset{D}{\longrightarrow}
\text{docket}
\overset{RR}{\longrightarrow}
\text{judgment/revision}
\overset{DA}{\longrightarrow}
\text{accountable fate}.
\]

Do not force both historical mechanisms to retain the word “docket.”

Clarify:

- what belongs to inquiry generation;
- what belongs to service;
- what belongs to answerability;
- whether docketing itself creates a liability;
- whether an inquiry may be transformed/refined while preserving its service obligation;
- how “non liquet,” referral, suspension, and backed refusal fit.

If an inquiry-based model naturally supplies a rigorous coverage condition, implement the smallest model needed to test it.

---

# XI. Relationship to Deference and Corrigibility

Preserve the separation established by the previous rounds.

Even perfect procedural legitimacy may coexist with advisor steering if two trajectories are record-equivalent but differ counterfactually in influence.

Therefore do **not** claim:

\[
P+I+RR+DA
\Longrightarrow
\text{no manipulation}.
\]

Instead investigate whether the clean interface is:

\[
\boxed{
\text{procedurally legitimate }H\text{-trajectory}
}
\]

plus a separately supplied condition concerning:

- advisor influence;
- endpoint preservation;
- protected human authority;
- counterfactual dependence;
- or whatever the deference line ultimately validates.

The desired downstream theorem shape is approximately:

\[
\text{Procedural Legitimacy}
+
\text{Counterfactual Trust/Control Condition}
\Longrightarrow
\text{Legitimate Corrigibility}.
\]

State exactly what the four-condition layer would export to such a theorem.

Do not attempt the full corrigibility theorem unless a small, clean composition result becomes available naturally.

---

# XII. Relationship to Normative Learning

Temporarily treat online performance as downstream.

The order should be:

\[
\text{define legitimate trajectory space first}
\]

then

\[
\text{ask whether a learner performs well inside it}.
\]

Do not spend the round trying to repair the current \(\Phi\)-regret theorem unless the sufficiency investigation itself produces a necessary representation theorem.

At the end, state what a future normative-learning theorem would consume from this work.

A likely architecture is:

\[
\text{Procedural Legitimacy}
+
\text{Inquiry Adequacy}
+
\text{Online Performance}
\Longrightarrow
\text{Normative Learning},
\]

but this round may determine that inquiry adequacy already belongs inside procedural legitimacy. Treat that as an open architectural question rather than a terminological commitment.

---

# XIII. Required Theorem / Counterexample Map

Produce a theorem map separating:

### Definitions

The final candidate forms of:

- provenance validity;
- inquiry generation;
- inquiry entitlement;
- inquiry service/coverage;
- reasons-responsiveness;
- diachronic answerability;
- procedural legitimacy.

### Proved or mechanically verified statements

At minimum preserve or revise:

- answerability conservation;
- non-laundering under representation change;
- composition of answerability transport.

### Counterexamples

Every whole-architecture attack that succeeds.

### Conjectures

Especially any sufficiency theorem.

### Open obligations

Anything needed before the architecture can be treated as stable.

Explicitly distinguish:

\[
\text{necessary}
\neq
\text{sufficient}
\neq
\text{independent}.
\]

---

# XIV. Success Criteria

## Strong success

The round produces:

1. precise substrate-independent forms of P, I, RR, and DA;
2. a corrected branching-safe answerability/conservation object;
3. a generative inquiry model yielding a non-vacuous coverage condition;
4. a provenance condition that permits endogenous reasoning while forbidding authority manufacture;
5. an exhaustive whole-architecture prosecution;
6. no surviving small counterexample to

   \[
   P+I+RR+DA\Rightarrow L^\star
   \]

   within the explored model classes;
7. a clean candidate sufficiency theorem with explicit hypotheses;
8. a crisp deference interface.

Do **not** call finite counterexample failure a proof of general sufficiency.

## Partial success

The four-way decomposition remains useful but a whole-architecture counterexample survives.

This is a good result if the round isolates exactly whether:

- an existing property needs strengthening;
- a compatibility condition is missing;
- or a fifth independent property is necessary.

## Failure

Treat the architecture as needing major revision if:

- provenance collapses into arbitrary trusted labels;
- inquiry adequacy only works by assuming the correct inquiry list;
- RR cannot remain abstract once inquiry/provenance machinery is included;
- DA cannot express branching liability conservation;
- all-four trajectories remain easy to game in qualitatively distinct ways;
- the target notion of legitimacy systematically outruns every formal condition;
- avoiding the attacks requires freezing standards or inquiry machinery against legitimate transformation.

Do not hide a failure verdict.

---

# XV. Execution Order

Proceed in this order:

1. Read the binding repository instructions and current research-state/decision surfaces.
2. Inspect the previous legitimacy-architecture round and its prosecution.
3. Inspect the current answerability, inquiry/docket, reasons-responsiveness, and deference non-recoverability artifacts.
4. State an independent procedural-legitimacy target \(L^\star\).
5. Formulate candidate definitions of P, I, RR, and DA.
6. Before coding extensively, state the proposed sufficiency theorem.
7. Construct the mandatory attacks against the conjunction.
8. Revise the definitions in response to attacks.
9. Repeat until either:
   - a stable four-condition candidate survives the declared prosecution, or
   - a minimal all-four counterexample identifies the missing structure.
10. Only then produce the consolidation artifact and roadmap changes.
11. Port short, stable mathematical statements to Lean where warranted and where the toolchain is available.
12. Run relevant tests, checkers, Lean build, axiom audit, provenance checks, and repository gates.
13. Perform an adversarial review in a separate context if feasible.
14. Open a draft PR.

Do not optimize for a clean success story.

---

# XVI. Repository / Governance Discipline

Follow `AGENTS.md` and the repository’s precedence rules.

Preserve historical round records.

Do not silently rewrite older artifacts to use the new terminology.

Do not register claims merely because tests pass.

Names introduced in this round are provisional unless already decided by the maintainer.

Do not rename `projects/leverage/` or formal identifiers merely to match the conceptual reorganization unless explicitly authorized.

If this investigation changes the architecture, update the living consolidated view and priorities, but distinguish:

- evidence;
- consolidated interpretation;
- maintainer adoption.

If the round discovers a workspace defect, file it rather than routing around it silently.

---

# XVII. Required Consolidation Artifact

Create or substantially revise a central artifact answering:

1. What is procedural legitimacy?
2. What is the exact provenance condition?
3. What is the exact inquiry-adequacy condition?
4. What is RR after provenance and inquiry are made explicit?
5. What is the branching-safe DA condition?
6. Are the four independent?
7. Are they jointly sufficient?
8. What all-four attacks were tried?
9. What counterexamples survived?
10. What theorem is actually conjectured?
11. What does the four-condition layer export to deference?
12. What remains outside its scope?
13. What does a future normative-learning theorem consume?
14. Which existing repository results instantiate each piece?

The abstract theory must be clearly separated from finite test models.

---

# XVIII. Draft PR Requirements

The draft PR must make it possible to answer, from the PR description alone:

- What precisely are the four candidate properties?
- Why is provenance not merely “external versus internal”?
- What generates inquiries?
- What makes an inquiry entitled to service?
- How does inquiry service relate to the docket and answerability ledger?
- What is the corrected object conserved by DA?
- What is the strongest all-four attack?
- Was an all-four counterexample found?
- Are the four sufficient, insufficient, or still only plausible?
- If insufficient, is the problem a weak definition, an interaction condition, or a fifth independent property?
- What transformations remain legitimately possible?
- What does this establish about manipulation, and what does it explicitly not establish?
- What exact object can now be handed to the deference/corrigibility line?
- What should be proved next?

The PR should end with a clear verdict:

\[
\boxed{
\text{Four-condition sufficiency: supported / refuted / unresolved}
}
\]

with the strength of evidence stated explicitly.

---

# Final Research Question

The previous round asked:

> What is missing from reasons-responsiveness plus diachronic answerability?

This round asks the next question:

> **Once provenance and inquiry adequacy are added, have we actually characterized the procedural legitimacy of a bounded reasoner’s trajectory, or have we merely moved the boundary one level outward?**

Find out.

**Model provenance:** GPT-5.6 Sol
