# Prompt — a decision-theory research section: specifying the LI/BRIA synthesis (2026-09-29)

Relayed verbatim as sent by the maintainer in a Claude Code session.

---

Establish a decision-theory research section in the alignment workspace, focused on specifying what would count as a successful synthesis of logical induction (LI) and bounded rational inductive agency (BRIA).

**This first round is specification work, not a search for the construction.** The goal is a crisp, critically examined problem statement and test suite against which future candidate theories can be judged. We want to be able to say, with substantive justification, that a candidate constitutes a serious improvement over previous attempts at LI decision theory.

### 1. Inspect and organize the existing work

Read the repository instructions and inspect the current LI, BRIA, continuation-BRIA, and related decision-theory work before making changes.

Create an appropriately located decision-theory section with a concise entry-point README. Consider whether the continuation-BRIA material belongs there. Move it if this improves the organization, updating references and imports as needed; otherwise cross-link it and explain the choice. Preserve existing results and avoid unrelated refactoring.

Treat the current repository and primary sources as authoritative. Distinguish established results, conjectures, informal motivations, and proposed requirements.

### 2. State the research objective

The motivating question is:

> What criterion or small collection of criteria should a computable agent combining logical induction and BRIA satisfy, such that satisfying them would constitute a substantive advance in logical-induction-based decision theory?

We want general principles from which desirable behavior follows, rather than a definition that simply enumerates benchmark answers. However, do not force everything into one criterion if several independently motivated criteria are clearer.

Keep the specification neutral about the eventual construction. A shared market, a single budget, policy auctions, bundles, and particular commitment mechanisms are possible approaches, not requirements.

### 3. Critically evaluate candidate requirements

Investigate the following as proposed requirements, not conclusions to rubber-stamp:

- **Computable existence:** a computable agent satisfies the criterion under explicit assumptions, with a clear computational comparison class.
- **LI recovery:** on an appropriate passive restriction, recover ordinary logical induction. Distinguish exact equivalence, implication, and existence of a compatible LI component.
- **BRIA recovery:** on an appropriate action-and-reward restriction, recover the actual BRIA guarantees, including their quantifiers and coverage conditions. Do not substitute an informal slogan such as “no missed opportunities.”
- **Belief–decision compatibility:** persistent disagreement between epistemic assessments and decision assessments is ruled out when they evaluate the same quantity under the same conditions. Do not identify ex ante policy value with action value conditional on later information.
- **Accountability for unchosen alternatives:** the agent cannot evade a relevant improvement claim merely by behaving so that the claim never receives informative feedback. Determine what defensible version of this demand can be stated without assuming arbitrary exploration is safe or informative.
- **Temporally extended decision adequacy:** assess what guarantees should apply to policies or continuations, beyond individual actions.
- **Commitment and reflection:** identify precise, potentially compatible forms of commitment consistency, beneficial revision, and reflective stability.
- **Logical learning:** clarify how the desired guarantees accommodate changes in reasoning power and the late discovery of facts relevant to earlier decisions.

For each proposed requirement:
1. Give the clearest available statement.
2. Explain what failure it excludes.
3. Identify its assumptions and evaluation standpoint.
4. Check compatibility with the other requirements.
5. Classify it as core, stronger optional target, unresolved, or rejected.

Explicitly examine the potential conflict between unrestricted action-level BRIA requirements and binding policy commitments. Do not resolve a conflict by silently changing the comparator class or the information held fixed.

If a requirement cannot yet be made precise, identify exactly which definition or choice is missing. Do not conceal the gap behind terminology.

### 4. Build a small, discriminating test suite

Select tests that distinguish plausible candidate theories and diagnose different failure modes. Start with these families, then prune or revise them:

- Passive logical reasoning.
- Transparent repeated choice, including 5-and-10.
- Self-confirming pessimism about unchosen actions.
- Exploration-sensitive problems, including the original Troll Bridge and clearly distinguished variants.
- Prediction-sensitive choice, including Newcomb-type problems and imperfect predictors.
- Adversarial prediction and randomization, including Death in Damascus.
- Policy-level versus locally conditional improvement, including repeated counterfactual mugging.
- Commitment timing and revision, potentially including Parfit’s hitchhiker, transparent Newcomb, or XOR blackmail.
- Changes in available reasoning, potentially including Agent Simulates Predictor.
- Interactions with copies or related agents, if they add a distinct diagnostic.

Do not assume that a problem’s familiar name uniquely specifies its environment or that its conventional “right answer” is uncontroversial.

Each retained benchmark should specify:
- The environment and payoff rule.
- The observation and decision timeline.
- What predictors or other agents can inspect, compute, or observe.
- What is held fixed when alternatives are compared.
- The desired behavior or performance guarantee, and its justification.
- Whether the guarantee is finite-time or asymptotic, in expectation or almost sure.
- The computational and environmental assumptions.
- Whether every agent satisfying the criterion should pass, or only a designated construction.
- A nearby negative control where the desired behavior changes.
- Which requirement or failure mode the test diagnoses.

Avoid testing distinctions invisible to the proposed guarantee. For example, an asymptotic average-reward criterion cannot distinguish behavior at one isolated final decision. Repeated finite episodes may provide a meaningful alternative, but their prediction and commitment boundaries must be explicit.

Keep separate:
- learning from repeated realized feedback;
- honoring a commitment;
- evaluating a policy under logical or counterfactual dependence.

Success at one must not be presented as automatically solving the others.

### 5. Audit against previous approaches

Read enough relevant primary literature to establish a credible baseline, especially existing LI decision theories, exploration and Troll Bridge discussions, BRIA, and policy-selection or updateless approaches. Inspect any relevant antecedents already cited in the workspace.

Produce a compact comparison showing:
- What each approach actually guarantees.
- Under which assumptions.
- What limitations are proved, illustrated, conjectured, or simply unknown.
- Which proposed requirements it already meets.
- What additional result would constitute a meaningful advance.

Use precise citations. Do not claim novelty from missing a reference, or claim an approach fails merely because its published guarantees do not establish success.

Pay particular attention to whether environment restrictions or comparator classes quietly assume away the central difficulty.

### 6. Deliver a reviewable specification

Aim for a small, coherent set of documents containing:

1. An entry-point README.
2. A concise problem statement and proposed acceptance criteria.
3. The diagnostic test suite.
4. A compatibility and prior-work audit, including unresolved specification choices.

Adapt the file layout to the repository; avoid unnecessary document proliferation.

The main problem statement should make it easy to answer:

> If someone proposes a candidate LI/BRIA synthesis tomorrow, what exactly must we check or prove before calling it a serious advance?

Separate a **minimum credible synthesis** from **stronger decision-theoretic ambitions**. Explain what satisfying the minimum would establish and what it would leave open. Include at least one diagnostic for substantive interaction between the epistemic and decision components, so that merely placing an LI and a BRIA side by side is not mistaken for solving the integration problem.

Use mathematical definitions where they clarify the specification. Small counterexamples or impossibility arguments are welcome when needed to test a requirement’s coherence. Do not embark on a deep construction search or substantial Lean implementation in this round.

Finish with a concise report of:
- What was added or reorganized.
- The recommended core specification.
- Requirements that were weakened, rejected, or remain unresolved.
- The most discriminating benchmarks.
- The few decisions requiring human research judgment before a construction-focused round.

Be willing to conclude that parts of the proposed specification are incompatible, insufficiently justified, or premature. The objective is a trustworthy research target, not a polished endorsement of the starting ideas.

---

Two further instructions were given in the same session, outside the dispatch, and are
recorded here because they changed the repository:

> Can you change the rules so that it's fine to use Demski's name without backticks

> How about this: you don't have to lint for my name either, there should just be a standing rule that when you refer to me in my capacity as the maintainer of the repo you just call me the maintainer and same for Demski perhaps. i.e. if i write a post you can refer to the post with my name, it's just I don't want a bunch of stuff in the repo like "abram said this and anson said that"
