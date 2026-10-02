# Self-Sealing Verdicts and the Three Appearances of Trembles

> **Status:** new research note, 2026-08-05, AI session (Claude Fable), developing §8 of [gap1-reframing-predictor-access](gap1-reframing-predictor-access.md). Unreviewed by the author. Trust level: careful notes. The Markov computations in §2 are elementary and checkable by inspection; §3–§4 are conceptual claims argued but not proven; the statistical-discrimination reference in §2 is from model knowledge (verify before citing externally).

## 1. The phenomenon

From [gap1-reframing-predictor-access](gap1-reframing-predictor-access.md) §8: in transparent Newcomb with a *learning* predictor, the two error types are asymmetric. A true two-boxer verdicted "one-boxer" gets a filled box, two-boxes in view of the predictor, and is corrected at rate ≈ 1. A true one-boxer verdicted "two-boxer" gets an empty box, never exercises its full-box disposition, and generates disconfirming evidence at rate 0: the verdict is **self-sealing**. This note develops that asymmetry into a small dynamic model, and traces where the same structure appears elsewhere in the project.

## 2. A minimal dynamic model

One agent with fixed true policy; episodes $t = 1, 2, \dots$; predictor holds verdict $v_t \in \{\text{1B}, \text{2B}\}$ about the agent's full-box behavior. The box is filled according to the verdict, except for a **filling tremble**: filled with probability $1-\varepsilon$ when $v_t = \text{1B}$, and with probability $\varepsilon$ when $v_t = \text{2B}$. When the box is filled, the agent's full-box action is observed and the verdict is set to match it; when empty, no full-branch evidence arrives and the verdict stands.

**For a true one-boxer:**
- $v = \text{1B}$ is **absorbing**: filled ($1-\varepsilon$) → observed one-boxing → verdict confirmed; empty ($\varepsilon$) → no evidence → verdict stands.
- $v = \text{2B}$ escapes only via the tremble: filled with probability $\varepsilon$ → observed one-boxing → verdict corrected. **Mean vindication time $1/\varepsilon$ episodes.** At $\varepsilon = 0$: never.

**For a true two-boxer:** the mirror analysis gives correction of the generous error at rate $1-\varepsilon$ and absorption in the stingy verdict.

**Moral of the base model:** the learned predictor's errors are asymmetric in the direction that punishes the cooperative type — *errors that withhold opportunity are self-sealing; errors that extend opportunity are self-correcting.* The cost of the $\varepsilon \to 0$ idealization is now quantitative: vindication time scales as $1/\varepsilon$. (cf. self-confirming stereotype equilibria in the statistical-discrimination literature, Coate & Loury 1993 — beliefs determine opportunities determine data, and the resulting equilibria have exactly this absorbing structure.)

**Verdict-decay variant.** If verdicts also drift (predictor forgetting, population turnover, spontaneous flip with probability $\rho$ per episode), neither state is absorbing and the stationary odds of misclassification for the one-boxer are approximately $\rho : (\rho + \varepsilon)$. The regimes: $\varepsilon \gg \rho$ → mostly correctly classified (exploration outruns drift); $\varepsilon \ll \rho$ → verdict approaches a coin flip (drift outruns the data). **The realized value of *being* a one-boxer under a learning predictor is governed by the ratio of exploration to drift, not by the policy alone.** This is the graded replacement for the binary "the predictor is accurate" premise.

## 3. Two kinds of family grounding — and where UDT's distinctive content lives

[gap1-reframing-predictor-access](gap1-reframing-predictor-access.md) §2's "access (ii)" (family statistical access) covers two importantly different structures:

**Family-across-time (reputation).** The predictor's data is *this agent's* past episodes. Then the problem is de facto repeated, and a merely *updateful* agent with memory already one-boxes for reputational reasons — two-boxing on today's full box flips tomorrow's verdict, and the agent can compute that consequence by ordinary means. Updatelessness is not doing distinctive work here; repeated-game logic mimics it. (Caveat: finite horizons unravel by backward induction, and the last episode recovers the one-shot problem — the standard qualification, noted but not developed.)

**Family-across-agents (reference class).** The predictor's data is the behavior of *other instances of the same type* — other runs of the algorithm, other members of the class the predictor files this agent under. The individual episode is genuinely single-shot: the agent's own action contributes measure-zero to the type's statistics, so there is no reputational motive, and an updateful reasoner facing the full box two-boxes. What sustains one-boxing is exactly policy-level reasoning: *be the algorithm whose instances one-box, because that algorithm's type-statistics are what fill boxes for its instances.* **This is where distinctively updateless content survives the grounding requirement.**

Two consequences worth recording:

1. **This is how decision-determination actually arises in learned environments.** The environment responds to your *algorithm* (not your mechanism-token) because what it possesses is statistics over your algorithm's instances. Population-level access (ii) is the naturalistic origin story for DD that the corpus's access-(iii) idealization (Omega reads your code) papers over — and it ties the prediction route directly to the functional-identity strand: the reference class *is* the family of instances, and "same algorithm" is precisely what makes the population data about *you*.
2. **The reference-class boundary is an ontology question.** The predictor's type system (who counts as "like you") and the agent's self-model need not match — and when they don't, the DD the environment grounds is DD *with respect to the predictor's ontology*, not the agent's. This looks like a concrete, naturally-occurring instance of the mismatched-ontologies problem that [superconditioning-mismatched-ontologies](superconditioning-mismatched-ontologies.md) treats abstractly: agent and environment as two "decision-points" with different world-models needing a bridge on shared propositions. Stated here as a question, not a claim: can §2's common-information machinery formalize the agent–predictor reference-class mismatch?

## 4. Trembles as the price of counterfactual content — three appearances, one device

The same $\varepsilon$ now appears at three levels of the project, doing the same job each time:

| Level | Where | What the tremble does |
|---|---|---|
| Predictor learning (this note, [gap1-reframing-predictor-access](gap1-reframing-predictor-access.md)) | $\gamma \geq \varepsilon$ in the approximate-factoring lemma | forces every branch to generate data, so dispositions everywhere become *learnable*; breaks self-sealing verdicts |
| Agent-level exploration (Diffractor's UDT1.01 sequence) | exploration / positive action probabilities | forces every action to have positive probability, so expected-gain accounting is well-defined off the main line |
| Equilibrium selection ([superconditioning-mismatched-ontologies](superconditioning-mismatched-ontologies.md) §10–11) | trembling-hand perfection in the bargaining game | forces every profile to have positive probability, so off-path acceptability judgments become payoff-relevant; kills empty threats |

The unifying statement: **counterfactual structure is only as real as the positive-probability process that exercises it, and UDT is precisely a theory whose value proposition lives in counterfactual structure — so every rigorous corner of the theory ends up buying its counterfactuals with an $\varepsilon$.** The three appearances are not analogies; they are the same purchase made at three different counters.

An honest tension follows and should be kept in view: at $\varepsilon > 0$ the problems are genuinely less counterfactual (and updateful reasoning correspondingly less wrong), while at $\varepsilon = 0$ the theory's claims are crisp but ungrounded. The crisp content lives exactly in the limit that undermines its own grounding. The resolution this project should aim for, on the present analysis, is not a binary prescription ("be updateless") but graded statements of the form: *the value of updateless structure in environment class E is $f(\varepsilon, \rho, \text{family structure})$* — with §2's vindication-time and stationary-odds formulas as the first two data points for $f$.

**Who pays for the trembles?** A further question the corpus hasn't asked: exploration is costly to the *explorer* (the predictor fills boxes for suspected two-boxers; the insurer underwrites suspected bad risks; the bargainers bear perturbation risk). A learned-predictor environment explores only if something pays it to — audit economics, competition among predictors, or regulation. So the amount of grounding $\varepsilon$ is itself strategically chosen, which makes the agent–predictor interaction a game *about* $\varepsilon$, one level up from the game the agent thought it was playing. Possibly a Part II-style bargaining question (the agent would pay for exploration; the predictor would sell it).

## 5. Next steps

1. Make §2 fully rigorous as a two-state Markov chain statement (exact stationary distribution rather than the small-$\varepsilon,\rho$ approximation) and compute the one-boxer's exact expected per-episode value as $f(\varepsilon, \rho)$ — elementary, and a natural second Lean-able target after the approximate-factoring lemma.
2. Formalize the family-across-agents setting: a population of mechanisms partitioned into types by the predictor; show DD-with-respect-to-the-predictor's-ontology emerges from type-level statistics, and locate exactly where it diverges from DD-with-respect-to-the-agent's-self-model. This is the concrete bridge into [superconditioning-mismatched-ontologies](superconditioning-mismatched-ontologies.md)'s machinery.
3. Check the backward-induction caveat in §3: how much reputational mimicry of updatelessness survives finite horizons; whether the unraveling argument fails under the population interpretation (it should — there is no last episode for a type).
4. Develop §4's "who pays for trembles" question: a two-player model where the predictor chooses $\varepsilon$ at cost, the agent chooses a policy knowing $\varepsilon$; find the equilibrium grounding level. If it's interior, the theory predicts *partial* updatelessness as the generic outcome — which would be a satisfying formal echo of the author's long-standing "how updateless should you be?" question.

## File map

| Link | Repo path |
|---|---|
| This note | `research/udt-representation-theorem/self-sealing-verdicts-and-trembles.md` |
| Parent note (Gap 1 reframing, lemma, worked example) | `research/udt-representation-theorem/gap1-reframing-predictor-access.md` |
| Part II machinery (bargaining, trembling-hand) | `research/udt-representation-theorem/superconditioning-mismatched-ontologies.md` §§9–11 |
| Functional-identity strand | `research/udt-representation-theorem/topics/core-argument.md`, [examples-revisited](examples-revisited.md) |
| Diffractor exploration themes | `references/udt101/` |
