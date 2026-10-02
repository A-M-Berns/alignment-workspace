# The author's Newcomb correction, made a theorem

Part of `two-lesions-index` · Part III, page 13 · Previous: [non-responsiveness](non-responsiveness.md) · Next: [clean-source-and-llc](clean-source-and-llc.md). Status per `two-lesions-provenance`. Source: [clean-source-and-policy-responsiveness](../directions/clean-source-and-policy-responsiveness.md) §1, §9 (numbers); [defining-cdt-in-the-learning-setting](../directions/defining-cdt-in-the-learning-setting.md) §5; [iv-design-draw-as-instrument](../directions/iv-design-draw-as-instrument.md) §3; [two-lesions-exchange-2026-09-19](../two-lesions-exchange-2026-09-19.md); `04-comparing-licdt-and-liedt`.

**Headline.** A learner that estimates the effect of its act from its exploration episodes alone one-boxes in Newcomb iff Omega's accuracy on the *exploration coin* exceeds the payoff threshold, whatever Omega knows about the deliberate draw; the policy that actually pays one-boxes iff Omega's accuracy on the *deliberate draw* exceeds the same threshold; so the learner fails exactly when its exploration is a genuine intervention Omega cannot see [checked]. The author's sentence — "the agent does poorly precisely when the interventionist assumption fits reality well" — is that theorem. What the exchange's account had backwards was the sign of the correlation between the learner's welfare and the validity of its interventionist assumption [derived].

## The account and the correction

The Docs Claude, on the ideal deterministic CDT: its causal knowledge "has to be inherited from its bounded predecessors' randomization. That works in a stationary environment like the double lesion, and it fails exactly where the environment responds to the current procedure rather than to the act, which is Newcomb. I find that a satisfying account of why CDT fails Newcomb: it is trusting experiments its predecessors ran, in a world that responds to something those experiments couldn't vary."

AUTHOR: "I think in the above paragraph you were making some mistakes, thinking that you can explain why CDT fails newcomb through letting the agent know which actions were exploration, and letting it learn based on those instances alone. This works in cases where Omega cannot predict the exploration, so that they're true interventions, but it doesn't work when Omega predicts those well, in which case the agent would learn an EDT-like picture. That is: the agent does poorly precisely when the interventionist assumption fits reality well. Your explanatory theory got it backwards."

## The model

One point with acts {one-box, two-box}. Each round: deliberate draw $D \sim \mathrm{Bern}(p)$ ($D = 1$ one-box); exploration flag $E \sim \mathrm{Bern}(\varepsilon)$; coin $K \sim \mathrm{Unif}\{1, 2\}$; realized act $A = K$ if $E$, else $D$. Omega fills the box iff its prediction $\Omega = 1$. Payoff $U = 10\cdot\mathbf{1}[\Omega = 1] - \mathbf{1}[A = 1]$ (post 04's normalization). The predictor's information is the parameter: a **label-probe** Omega fills w.p. the trembled label $q_\varepsilon = (1-\varepsilon)p + \varepsilon/2$, independently of $(D, E, K)$ — post 04's fallible Omega and, under Definition 6, the only way a tree reads a label; an **$(r_D, r_K)$-Omega** matches $D$ w.p. $r_D$ on non-exploration rounds and matches $K$ w.p. $r_K$ on exploration rounds — $(1, \tfrac12)$ is the run's *deliberate-sharing* predictor, $(1, 1)$ the perfect one, $(\tfrac12, 1)$ a coin-only one.

Five evaluators of "one-box minus two-box": **LICDT** (`04-comparing-licdt-and-liedt` l. 25), $E[U \mid E{=}1, A{=}1] - E[U \mid E{=}1, A{=}2]$ — the exploration-episode learner the author's correction is about; **ITT**, $E[U \mid D{=}1] - E[U \mid D{=}2]$ — the exchange's "condition on the intention"; **LIEDT**, the act-conditional on all rounds; **forcing** at the live node, $-1$ always; **deviation**, $V(p{=}1) - V(p{=}2)$ with $\varepsilon$ held.

## Proposition A

> **Proposition A.** [checked at twelve parameter combinations to $10^{-9}$] With an $(r_D, r_K)$-Omega, for every $p, \varepsilon \in (0,1)$:
> $$\text{LICDT gap} = 10\,(2r_K - 1) - 1, \qquad \frac{dV}{dp} = (1-\varepsilon)\,\big(10\,(2r_D - 1) - 1\big).$$

So the exploration-episode learner one-boxes iff $r_K > 0.55$, independently of $r_D$, $p$, $\varepsilon$; the policy-optimal act is one-box iff $r_D > 0.55$; and the learner's best-response fixed point is optimal iff the two thresholds agree. Against a label-probe Omega the LICDT gap is $-1$ at every $p$ while $V(p) = 9 q_\varepsilon$: the learner two-boxes and earns $0.45$ where $8.55$ was available (at $\varepsilon = 0.1$).

*Proof sketch* [derived]. On exploration rounds $A = K$ and $\Omega$ depends on $K$ alone, so $P(\Omega{=}1 \mid E, A{=}1) = r_K$ and $P(\Omega{=}1 \mid E, A{=}2) = 1 - r_K$. $V(p)$ is affine in $p$ because the policy enters only through $D$ on the $(1-\varepsilon)$ non-exploration mass, where $P(\Omega{=}1 \mid D) = r_D$ or $1 - r_D$. The label-probe row: $\Omega \perp (D, E, K)$ makes every act-conditional gap $-1$ while the label moves the box.

| predictor $(r_D, r_K)$ | LICDT | ITT | LIEDT | deviation | LICDT fixed point, $V$ | optimum |
|---|---|---|---|---|---|---|
| label-probe | $-1.00$ | $-0.90$ | $-1.00$ | $+8.10$ | two-box, $0.450$ | one-box, $8.550$ |
| deliberate-sharing $(1, \tfrac12)$ | $-1.00$ | $+8.10$ | $+8.00$ | $+8.10$ | two-box, $0.450$ | one-box, $8.550$ |
| perfect $(1, 1)$ | $+9.00$ | $+8.10$ | $+9.00$ | $+8.10$ | one-box, $8.550$ | one-box, $8.550$ |
| coin-only $(\tfrac12, 1)$ | $+9.00$ | $-0.90$ | $0.00$ | $-0.90$ | one-box, $4.050$ | two-box, $4.950$ |
| fallible $(0.9, 0.9)$ | $+7.00$ | $+6.30$ | $+7.00$ | $+6.30$ | one-box, $7.650$ | one-box, $7.650$ |
| draw $0.9$, coin $\tfrac12$ | $-1.00$ | $+6.30$ | $+6.20$ | $+6.30$ | two-box, $1.350$ | one-box, $7.650$ |

[checked; $p = \tfrac12$, $\varepsilon = 0.1$]

## The author's sentence, made exact

"This works in cases where Omega cannot predict the exploration, so that they're true interventions" — with $r_K = \tfrac12$ the learner two-boxes. "It doesn't work when Omega predicts those well, in which case the agent would learn an EDT-like picture" — with $r_K$ high it one-boxes. "The agent does poorly precisely when the interventionist assumption fits reality well" — the assumption fits when $r_K = \tfrac12$, and that is the row where, for any $r_D > 0.55$, the learner sits at the two-box fixed point and forgoes $(1-\varepsilon)(10(2r_D - 1) - 1)$ per round — $8.1$ at $r_D = 1$.

Two riders the numbers add [derived]. (i) "Predicts the exploration well" is necessary and sufficient for the learner to one-box, but the one-boxing is *correct* only if Omega also reads the deliberate draw — the coin-only Omega makes the learner one-box where two-boxing pays ($4.05$ vs $4.95$); the learner's verdict tracks the wrong parameter in both directions. (ii) A learner that varies its *policy* across blocks and regresses payoff on $p$ adopts the optimal endpoint in all four predictor rows, at the cost of its exploration blocks [checked, Monte Carlo].

## What was backwards

Three things, in increasing order of importance [derived; the reading of the Docs text is ATTRIBUTION-UNVETTED as to its author's intent]. First, the account assumed exploration-based learning yields two-boxing; Proposition A says it does so only when $r_K \approx \tfrac12$. Second, the account located the failure in the experiments' *invalidity* — an unvaried variable the world responds to, i.e. confounding. In the failing row the experiments are *maximally valid* interventions on the act: the coin is independent of everything, Omega included, and the learner correctly estimates $\partial U/\partial A$ at fixed policy as $-1$. It loses because a correct answer about the act is the wrong estimand; and in the row where the experiments are *invalid* as interventions — Omega reads the coin — the learner one-boxes and wins. The learner's welfare is anti-correlated with the validity of its interventionist assumption. Third, "something those experiments couldn't vary" is false of the policy-level version of the same learner: varying $p$ across blocks *does* move a policy-reading Omega, and the block regression sees $V(p) = 9 q_\varepsilon$. The inheritance story is fine at the policy level and wrong only at the act level.

**The exchange's own construction one-boxes.** The paragraph's learner "samples an intention from its policy, records the sample, and acts on it unless overridden … Conditioning on the intention rather than the realized act" — that is ITT. Against the deliberate-sharing Omega the ITT gap is $+8.1$, the deviation gap; against $(0.9, \tfrac12)$, $+6.3$. The intention-conditioning learner does not two-box against any predictor that reads what it conditions on. It two-boxes ($-0.9$) against the label-probe Omega, whose dependence on the policy is *label*-dependence (Remark 5.1), which no conditioning on a draw can see. So "ITT = deviation" holds exactly when every policy-dependence in the tree is branching-dependence on the live draw, and fails under Definition 6's independent redraws, where Omega's simulation is a label-probe — the run's P04-B′ wedge [checked on the one-point tree; the general statement derived].

## Checked on v2's tree

[defining-cdt-in-the-learning-setting](../directions/defining-cdt-in-the-learning-setting.md) §5 ran the same correction on a v2 Newcomb tree ($L = 10$, $S = 1$, $p = 0.9$, tagged exploration $\eta = 0.05$) [checked]. Under Definition 6 (Omega samples the label): the tagged interventionist's exploration fill rates are equal across acts at every label ($0.12$, $0.5$, $0.88$ at $q = 0, \tfrac12, 1$), so it learns "no effect" — *true as physics* — two-boxes, and the policy value falls from $8.825$ to $2.175$. Under Definition 6′ (Omega reads the live draw): fill rates $0.9$ versus $0.1$ at every label; it reads its exploration as an intervention that moved the box — *false as physics*, Omega predicted it — one-boxes, and wins. Its verdict is a function of whether the environment reads the draw, not of anything about the agent. Its formal content is v2's Q12: the "shadow of predecessors' exploration" is a *run semantics*, not a tremble rate, and Definition 10 must carry that choice (`next-coherent-care`).

## Where the inheritance story is right

The IV note observes that the retracted sentence — "trusting experiments its predecessors ran, in a world that responds to something those experiments couldn't vary" — is *wrong of Newcomb* and *right of Troll Bridge*: the bounded predecessors' safe crossings are an experiment on a different treatment variable ($\mathrm{Cross}_M$), for which independence held, and carrying its result to $\mathrm{Cross}$ is an external-validity error — the doc's §7 last paragraph. The direction should keep the sentence under its correct problem (`lobian-lesion`).

## The principle it corrects

`epsilon-versus-voi` ended with the Docs Claude's rule, "condition on the clean source." Proposition A shows the clean source (the coin Omega cannot see) gives the losing verdict and the dirty source (the deliberation Omega reads) the winning one. What is consistently right is the estimand that varies the variable the environment *reads*. [clean-source-and-llc](clean-source-and-llc.md) states the duality this exposes, and [policy-responsiveness](policy-responsiveness.md) the criterion that reads direction.
