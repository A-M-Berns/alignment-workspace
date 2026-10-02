# Two Lesions: On Calibration in Decision Problems (Claude Docs document, verbatim copy)

Verbatim copy of the author's Claude Docs document *Two Lesions: On Calibration in Decision Problems* ([scrubbed]), byline "Sep 18, 2026 · the author", as pasted into the Claude Code session on 2026-09-19. The doc is live and was mid-revision when pasted (see [two-lesions-exchange-2026-09-19](two-lesions-exchange-2026-09-19.md): Definition 4 was to be replaced by a "lab CDT", §6's conclusion and Proposition 10 restated); the canonical text is the doc itself. Written in a claude.ai Docs conversation with Claude drafting and the author directing (ATTRIBUTION per the exchange); treat every numbered result as AI-derived and unvetted unless the author says otherwise. Display math is in ```latex fences as in the doc. Companion analysis: [smoking-lesion-exploration-and-boundaries](smoking-lesion-exploration-and-boundaries.md); research directions: `research/decision-problems/directions/`.

---

## §1 The Problem

Two decision problems share a shape, and it has been urged that they ought not to share a fate.

In Smoking Lesion, a lesion of the brain disposes its bearer both to smoke and to contract cancer. Smoking itself is causally inert with respect to cancer, and pleasant. The evidential decision theorist, conditioning on the act, observes that smokers contract cancer more often than abstainers, and abstains. The causal decision theorist, intervening on the act, observes that smoking alters nothing about cancer, and smokes. The received verdict is that the causal theorist is right, and that the evidential theorist has been taken in by a correlation he did not himself produce.

In Troll Bridge, an agent whose reasoning is carried out in a formal theory T (Peano arithmetic will do) must decide whether to cross a bridge guarded by a troll. The troll destroys the bridge, with the agent on it, if and only if the agent crosses and T is inconsistent. A Löbian argument, rehearsed in §7, shows that the agent proves in T that its crossing entails the inconsistency of T, hence the destruction of the bridge; so the agent stays home, though T is (let us suppose) consistent and the bridge would have held.

The shape the two problems share is that of a common cause. Something antecedent to the act—a lesion, an inconsistency—produces both the act and the harm, so that the act is symptom rather than cause of the harm, and the evidential agent, who reads symptoms, is misled. Regiment decision problems in a certain natural way, it has been said, and Troll Bridge simply is Smoking Lesion.

The calibration requirement. It has been proposed that a decision problem may be used to evaluate a decision procedure only if the statistics the problem stipulates are those that would in fact obtain were an agent running that procedure placed in the problem's situation. Call this the calibration requirement. XOR Blackmail illustrates it: an evidential agent placed in that situation receives the blackmailer's letter with high probability, a causal agent only rarely, so that no single stipulated probability of receiving the letter is calibrated for both. The requirement was advanced with a particular consequence in view: that Smoking Lesion, so evaluated, is not a legitimate test of evidential decision theory, while Troll Bridge remains a genuine difficulty for it.

Three challenges have been raised in correspondence. First: why may we not calibrate Smoking Lesion by populating the situation with both causal and evidential agents, and letting the agent under evaluation be uncertain which it is? Second: since Troll Bridge has Smoking Lesion's shape, must not the requirement either admit both problems or exclude both? Third: embedded agents are made of matter and may really have lesions; is it not question-begging to exclude, on grounds of embedded agency, the very problems that embedded agency makes vivid?

The plan. §2 regiments the requirement and shows that the argument first offered on its behalf proves too much. §3 states the amendment—that ideal rationality is a limit of bounded rationality—and constructs a calibrated Smoking Lesion, which we call the double lesion. §§4–5 work out its fixed points and its dynamics; the results are less tidy than either party to the dispute has supposed, and the untidiness is instructive. §6 introduces the notion of a tag, shows that with it the problem dissolves, and shows that without it the problem afflicts causal and evidential learners alike. §7 formalizes Troll Bridge and locates the two respects in which it differs. §8 returns to the three challenges. §9 draws morals.

## §2 Decision Problems and Their Calibration

We first say what a decision problem is, so that we may say what it is for one to be calibrated.

An agent is a decision procedure together with an epistemic state; we write α, β for agents, and α_E, α_C for the ideal evidential and ideal causal agents. A situation is a function S from agents to probability measures over histories, a history being a record of the acts taken and the outcomes received. The situation is the world's contribution: it says, for each agent that might be placed in it, what would ensue. A presentation of a decision problem is a pair ⟨D, u⟩, D a joint probability measure over acts and outcomes and u a utility function on outcomes. The presentation is what the theorist hands the agent; it is what the philosophical literature calls the decision problem, and what the agent conditions upon or intervenes within.

Definition 1. A presentation ⟨D, u⟩ is calibrated for agent α in situation S if D is the act–outcome marginal of S(α).

The calibration requirement, so regimented, says that a presentation may be used to evaluate α only if it is calibrated for α.

The point of the requirement is that S is a function of the agent. In XOR Blackmail, S(α_E) and S(α_C) assign different probabilities to the arrival of the letter, because the blackmailer's conduct depends on how the recipient will respond. A theorist who fixes a single D and asks how each of α_E and α_C fares against it is evaluating each against a situation that, for at least one of them, would not have arisen. The requirement is in this respect a cousin of the demand, familiar from the theory of games, that a solution concept be assessed at the profile it induces rather than at one stipulated from without.

The basic argument. Here is the argument first offered for the claim that Smoking Lesion fails the requirement with respect to evidential decision theory. Let ⟨D, u⟩ be any presentation of Smoking Lesion on which the evidential verdict is to abstain. Then α_E, handed D, abstains with certainty; so S(α_E) assigns probability zero to smoking. But D assigns positive probability to smoking. It must, or D would carry no conditional probability of cancer given smoking, and the evidential computation could not be run. Hence D is not the marginal of S(α_E), and the presentation is not calibrated for α_E. The statistics α_E is asked to reason from are statistics about a population to which α_E does not belong: a population some of whose members smoke.

The argument is valid. Its trouble is that it proves too much.

Why it proves too much. Take any presentation ⟨D, u⟩ on which the ideal agent α, handed D, selects a single act a* with certainty. Then S(α) is degenerate on a*, and D, which must give positive probability to every act if the agent is to have conditional expectations for every act, is not the marginal of S(α). By the basic argument, no presentation with a determinate solution is calibrated for the agent that solves it. This disqualifies Newcomb's problem, XOR Blackmail, and Troll Bridge itself, in which α_E never crosses, so that any presentation assigning positive probability to crossing is, by the basic argument, uncalibrated for α_E. The argument that was to separate Smoking Lesion from Troll Bridge separates neither from anything.

Diagnosis. The argument trades on an ambiguity in what D is. D might be the agent's credence about its own acts; or D might be the family of conditional measures D(· | a), one for each act a, that the agent consults in deliberating. For an ideal agent the first is degenerate and the second is not. The requirement, sensibly construed, constrains the second. It asks that D(· | a) be the conditional outcome measure that would obtain, in S(α), on the event that α does a. But if S(α) gives a probability zero, that conditional is undefined, and calibration cannot be checked. What is wanted is a source of positive probability for every act that is consistent with the agent's being α. The amendment of §3 supplies one.

## §3 The Amendment and the Double Lesion

The amendment. Ideal rationality, on the view under examination, is not a starting point but a limit. The ideally rational agent is what a bounded agent becomes when it has learned all there is to learn; it is an idealization of competence, not of innocence. Accordingly the ideal agent α is to be understood as the limit of a sequence of bounded agents α₁, α₂, …, each of which assigns positive probability to every act—through deliberate exploration, or through imperfect command of its own conduct—with these probabilities vanishing in the limit. The conditionals D(· | a) that the ideal agent consults are the limits of the conditionals the bounded agents would have learned. A presentation is calibrated for α, on the amended criterion, when its conditionals are these limits.

The amendment restores Newcomb's problem, XOR Blackmail, and Troll Bridge to legitimacy: in each, the bounded agents sometimes take the act the ideal agent forgoes, and the limit conditionals are defined. It restores Smoking Lesion too, provided we can say what the bounded evidential agents' conditionals converge to. To say this we must say where the bounded agents' variation in conduct comes from, for the answer determines the correlation between act and lesion that the agent learns.

Sources of variation. There are two. The agent's conduct may vary because the agent varies it—it explores—or because something other than the agent varies it. In the original problem the second source is the lesion; it is what makes smokers smoke. To be faithful to the problem we should let the lesion be a source of variation in the act. But the lesion alone will not do, for it varies conduct in one direction only. A bounded evidential agent inclined to abstain will, through the lesion, occasionally smoke, and will thereby acquire data on smoking. A bounded evidential agent inclined to smoke will never abstain, and will have no data on abstention; the conditional on abstention would be undefined at exactly the fixed point we most need to examine. Hence the anti-lesion: a second condition, harmless, which occasionally forces abstention, and which excludes the lesion as the lesion excludes it. The two together we call the double lesion.

Definition 2 (the double lesion). Fix parameters ε_L, ε_A > 0 with ε_L + ε_A < 1; δ ∈ (0, 1]; π > 0; C > 0. In each episode the agent is in exactly one of three states: L, with probability ε_L; A, with probability ε_A; N, with probability 1 − ε_L − ε_A. The agent contracts cancer in that episode if and only if it is in L. In state L, with probability δ the agent smokes regardless of its policy; in state A, with probability δ the agent abstains regardless of its policy; in every other case the agent acts on its policy. A policy is a probability p ∈ [0, 1] of smoking when acting on policy. Smoking yields utility π; cancer yields −C; utilities add.

Two remarks. First, the formalism is neutral between two readings. The probabilities may be frequencies across the episodes of one agent's life, the lesion coming and going; or they may be frequencies across a population of agents running the same procedure, each with a lesion, or without one, for life. Under the second reading a "policy" is the procedure's recommendation and an "episode" is an agent. The population reading recurs in §8. Second, δ measures the lesion's grip—how often it overrides the agent. That the grip is a probability rather than a certainty is what makes the forced and the unforced acts of a single agent commensurable. The value δ = 1 is permitted; it is the case in which the lesion always overrides.

The evidential computation. Write P_p for the measure on triples (state, act, outcome) induced by policy p. The evidential agent at policy p computes P_p(cancer | smoke) and P_p(cancer | abstain), and prefers smoking, prefers abstaining, or is indifferent, according as π exceeds, falls short of, or equals

```latex
\Delta(p) \;=\; C\,\bigl[\,P_p(\mathrm{cancer}\mid\mathrm{smoke}) \;-\; P_p(\mathrm{cancer}\mid\mathrm{abstain})\,\bigr].
```

Define the best response β(p) to be {1} if π > Δ(p), {0} if π < Δ(p), and the whole interval [0, 1] if π = Δ(p). A policy p* is a fixed point if p* ∈ β(p*). A fixed point is a policy that, once adopted, generates the very conditionals on which the evidential agent would adopt it. The amended calibration requirement says that the double lesion is a legitimate test of the evidential agent at exactly its fixed points; for only there are the conditionals the agent consults the conditionals its own conduct produces.

The explicit forms. Counting gives, with κ = 1 − δ(ε_L + ε_A),

```latex
\begin{aligned}
P_p(\mathrm{smoke}) &= \varepsilon_L\delta + \kappa\,p, &\qquad P_p(\mathrm{cancer}\wedge\mathrm{smoke}) &= \varepsilon_L\,(\delta + (1-\delta)\,p),\\[2pt]
P_p(\mathrm{abstain}) &= \varepsilon_A\delta + \kappa\,(1-p), &\qquad P_p(\mathrm{cancer}\wedge\mathrm{abstain}) &= \varepsilon_L\,(1-\delta)(1-p),
\end{aligned}
```

so that

```latex
P_p(\mathrm{cancer}\mid\mathrm{smoke}) \;=\; \frac{\varepsilon_L\,(\delta + (1-\delta)\,p)}{\varepsilon_L\delta + \kappa\,p},
\qquad
P_p(\mathrm{cancer}\mid\mathrm{abstain}) \;=\; \frac{\varepsilon_L\,(1-\delta)(1-p)}{\varepsilon_A\delta + \kappa\,(1-p)}.
```

These two quotients are the objects of §4. Each is a ratio of affine functions of p, hence monotone; a short computation shows both are strictly decreasing in p. The first falls from 1 at p = 0 to ε_L/(1 − ε_Aδ) at p = 1; the second falls from ε_L(1−δ)/(1 − ε_Lδ) at p = 0 to 0 at p = 1. Their difference is not monotone, and that is the whole story.

## §4 Fixed Points of the Double Lesion

Throughout we assume

```latex
\text{(H)}\qquad \pi \;<\; C\cdot\min(\varepsilon_L,\;1-\varepsilon_L),
```

which says that the pleasure of smoking is small against the cost of cancer, whether that cost is weighted by the base rate of the lesion or by its complement. These are the standard numbers of the problem: cancer is catastrophic, and the lesion is not vanishingly rare.

Proposition 1 (abstention is a fixed point). Δ(0) = C(1 − ε_L)/(1 − ε_Lδ). Hence, under (H), p = 0 is a fixed point for every δ ∈ (0, 1].

Proof. At p = 0 the only smoking is forced, so P₀(cancer | smoke) = 1. Abstention occurs in state L when unforced, in state A, and in state N, so P₀(cancer | abstain) = ε_L(1−δ)/(1 − ε_Lδ). Subtract and multiply by C. Since 1 − ε_Lδ ≤ 1 we have Δ(0) ≥ C(1 − ε_L) > π by (H), so β(0) = {0}. ∎

Proposition 2 (smoking is not a fixed point). Δ(1) = Cε_L/(1 − ε_Aδ). Hence, under (H), p = 1 is not a fixed point for any δ ∈ (0, 1].

Proof. At p = 1 the only abstention is forced, and forced abstention occurs only in state A, where there is no cancer; so P₁(cancer | abstain) = 0. Smoking occurs in every other case, so P₁(cancer | smoke) = ε_L/(1 − ε_Aδ). Since 1 − ε_Aδ ≤ 1 we have Δ(1) ≥ Cε_L > π by (H), so β(1) = {0}, which does not contain 1. ∎

Remark. It is worth seeing what does the work in Proposition 2. It is not that smoking is evidence of the lesion. At p = 1 the evidential agent's smoking is nearly uninformative, P₁(cancer | smoke) lying within a factor (1 − ε_Aδ)⁻¹ of the base rate. It is that abstention is perfect evidence of the anti-lesion, hence of the lesion's absence. The agent that never abstains by choice finds, in the record of its abstentions, only the harmless compulsion; and the evidential agent, reading that record, credits abstention with eliminating the base-rate risk of cancer, a benefit worth Cε_L. Under (H) this exceeds the pleasure of smoking. The mutual exclusion of lesion and anti-lesion is what makes this so. Were the anti-lesion independent of the lesion, forced abstention would carry the base rate of cancer, Δ(1) would be of order δ, vanishing with the lesion's grip, and smoking would be a fixed point for every sufficiently small δ. The exclusion is faithful to the original problem, in which abstainers are less likely than average to bear the lesion; but it should be seen for what it does.

Proposition 3 (the interior, and the singular limit).
(i) Δ is convex on [0, 1].
(ii) For p in any closed subinterval of (0, 1), as δ → 0,

```latex
\Delta(p) \;=\; C\,\varepsilon_L\,\delta\left[\frac{1-\varepsilon_L}{p} + \frac{\varepsilon_A}{1-p}\right] \;+\; O(\delta^2).
```

In particular Δ(p) → 0 for each p ∈ (0, 1), while Δ(0) → C(1 − ε_L) and Δ(1) → Cε_L.
(iii) Let m(δ) be the minimum of Δ on [0, 1]. Under (H): if m(δ) > π, the unique fixed point is 0; if m(δ) < π, there are exactly three fixed points, 0 < p̌(δ) < p̂(δ) < 1, the latter two being the solutions of Δ(p) = π. To first order in δ, m(δ) = Cε_Lδ(√(1−ε_L) + √ε_A)², so the three-fixed-point regime obtains for δ below

```latex
\delta^* \;\approx\; \frac{\pi}{C\,\varepsilon_L\,\bigl(\sqrt{1-\varepsilon_L}+\sqrt{\varepsilon_A}\bigr)^2},
```

and in that regime

```latex
\check p(\delta) \;=\; \frac{\varepsilon_L\,\delta\,\bigl(C(1-\varepsilon_L)-\pi\bigr)}{\pi} + O(\delta^2),
\qquad
1-\hat p(\delta) \;=\; \frac{\varepsilon_A\,\delta\,\bigl(C\varepsilon_L-\pi\bigr)}{\pi} + O(\delta^2).
```

Proof. (i) Write a′ = ε_L(1−δ), b′ = ε_Lδ. Then P_p(cancer | smoke) = a′/κ + b′(1 − a′/κ)/(b′ + κp), and a′ < κ because ε_L + δε_A < 1; so it is a positive constant times a convex function of p, plus a constant, hence convex. Write a = ε_L(1−δ), b = ε_Aδ, x = 1 − p. Then P_p(cancer | abstain) = ax/(b + κx), whose second derivative in x is −2abκ/(b + κx)³ < 0; it is concave in x, hence concave in p. A convex function less a concave one is convex. (ii) Expand each conditional to first order in δ with p held fixed in a compact subset of (0, 1); the two first-order terms are ε_Lδ[(1−p)(1−ε_L) + pε_A]/p and −ε_Lδ[(1−p)(1−ε_L−ε_A) + ε_A]/(1−p) respectively, and their sum simplifies to the bracket displayed. (iii) By Propositions 1 and 2, Δ exceeds π at both endpoints. A convex function exceeding π at both endpoints either exceeds π throughout or falls below π on a single open interval bounded by exactly two crossings. The best response is {0} where Δ > π and {1} where Δ < π, so the fixed points are 0 together with the crossings, at which the agent is indifferent. Minimizing the bracket in (ii) gives the first-order value of m(δ) and so δ*. For the crossings near the endpoints the expansion (ii) is not uniform and one solves Δ(p) = π directly from the exact forms, holding the slowly varying conditional at its endpoint value; this yields the displayed asymptotics. ∎

Numerically, with ε_L = ε_A = 0.2, C = 100, π = 1: δ* ≈ 0.028; at δ = 0.1 the unique fixed point is 0; at δ = 0.001 the fixed points are 0, 0.0159, and 0.9961, against the asymptotic predictions 0.0158 and 0.9962.

Corollary (the limit of the fixed points is not the fixed point of the limit). Let Δ₀(p) = lim Δ(p) as δ → 0. By Proposition 3, Δ₀ vanishes on (0, 1) and equals C(1 − ε_L) at 0 and Cε_L at 1. The best-response map of Δ₀ has 0 as its unique fixed point. But the fixed points of the δ-problems converge, as δ → 0, to the set {0, 1}: p̌(δ) → 0 and p̂(δ) → 1.

Two readings of the amendment. The amendment of §3 said that the ideal agent's conditionals are the limits of the bounded agents' conditionals. It did not say at which policy the limit is to be taken, and the Corollary shows that this matters.

On the first reading, one fixes the ideal agent's policy and takes the limit of the bounded conditionals at that policy. This yields Δ₀, and the ideal evidential agent has abstention as its unique fixed point. The classical verdict is vindicated: the calibrated evidential agent forgoes π for nothing, its risk of cancer being ε_L whatever it does.

On the second reading, one takes the limit of the bounded agents' fixed points. This yields {0, 1}: the ideal evidential agent may abstain, or may smoke, the latter as the limit of the policies p̂(δ), in which it abstains by choice with a probability of order δ—just enough that its chosen abstentions are not swamped by its forced ones. On this reading the calibrated Smoking Lesion leaves the evidential agent an equilibrium in which it fares exactly as the causal agent does.

The two readings differ over the conditional on an act of vanishing probability. The first fixes it by the forcing mechanism alone: if the agent never abstains by choice, the record of its abstentions is a record of the anti-lesion. The second fixes it as the limit of the agent's own mixtures: if the agent abstains by choice however rarely, and its chosen abstentions are not outpaced by its forced ones, the record is uninformative. Neither reading is forced by the amendment as stated. The amendment says "limit" and does not say in what order.

The question of order is not a quibble. It is the question whether the agent's own exploration or the lesion's grip vanishes faster; and that is a question about the agent's relation to its own conduct, not about the logic of its decision rule. We add that where the lesion's grip is strong—δ above δ*—the question does not arise: abstention is then the unique fixed point, and the claim that the evidential agent must learn not to smoke holds without qualification. It is in the regime of weak grip, where the problem most resembles its classical statement, that the claim becomes hostage to the order of limits. §5 makes this precise.

## §5 Dynamics, and What Selects the Fixed Point

A fixed point is a resting place; it says nothing about whether a learner arrives there. We consider two idealized learners. Each begins with some policy, computes the evidential penalty from statistics it has gathered, and moves its policy toward the best response. They differ in which statistics they consult.

The recency learner consults the statistics of its present policy. Its penalty at step t is Δ(p_t), the penalty its present conduct generates, as though it kept a running window over a past recent enough to reflect its present dispositions. It also explores: with probability η_t it acts at random, taking each act with probability one half. Its update is

```latex
p_{t+1} \;=\; (1-\eta_{t+1})\,b_t \;+\; \tfrac{1}{2}\eta_{t+1}, \qquad b_t \in \beta(p_t),
```

so that its smoking rate is its best response to its own current statistics, diluted by exploration.

The cumulative learner consults the statistics of its whole history. Writing p̄_t for its historical smoking rate, its penalty is Δ(p̄_t), and its best response b_t ∈ β(p̄_t) enters the running average:

```latex
\bar p_{t+1} \;=\; \bar p_t \;+\; \frac{b_t - \bar p_t}{t+1}.
```

This is fictitious play against oneself. That Δ(p̄_t) is the right cumulative penalty is not an approximation: the joint frequencies P_p are affine in p, so a history compounded of episodes at policies p₁, …, p_t has exactly the joint frequencies P_{p̄}.

Proposition 4 (the recency learner). Let δ be fixed and η_t → 0. Under (H), p_t → 0. If instead δ_t → 0 as well, then p_t → 1 when η_t/δ_t → ∞, and p_t → 0 when η_t/δ_t → 0.

Proof. Suppose b_t = 1, so that p_{t+1} = 1 − η/2 with η = η_{t+1}. The learner's chosen abstentions now occur at rate η/2 and its forced abstentions at rate ε_Aδ. By the exact form of §3,

```latex
P_{1-\eta/2}(\mathrm{cancer}\mid\mathrm{abstain}) \;=\; \frac{\varepsilon_L(1-\delta)\,\eta/2}{\varepsilon_A\delta + \kappa\,\eta/2}.
```

If η/2 ≫ ε_Aδ, this is close to ε_L, the penalty is Cε_Lδ(1 − ε_L) + 2Cε_Lε_Aδ/η + O(δ²), and for δ small and δ/η small this is below π: the learner keeps b = 1 and stays near 1. If η/2 ≪ ε_Aδ, this is close to 0, the penalty is close to Cε_L > π, and b_{t+1} = 0, so p_{t+2} = η/2. At p = η/2 with η/2 ≪ ε_Lδ, the chosen smokings are swamped by the forced ones, P(cancer | smoke) is close to 1, the penalty is close to C(1 − ε_L) > π, and b = 0 thereafter. With δ fixed and η_t → 0 the second case obtains eventually whatever the initial policy, so p_t → 0. With both vanishing, which case obtains is decided by the ratio. ∎

Proposition 5 (the cumulative learner). Let δ be fixed. Under (H): if δ > δ*, then p̄_t → 0 from every initial policy. If δ < δ*, so that the fixed points 0 < p̌ < p̂ < 1 exist, then p̄_t → 0 when p̄₀ < p̌ and p̄_t → p̂ when p̄₀ > p̌. Since p̌ = O(δ), the second case is generic: from almost any initial policy the cumulative learner converges to p̂(δ) = 1 − O(δ), and smokes with a probability that tends to 1 as δ → 0.

Proof. The recursion is an Euler scheme, with steps 1/(t+1) whose sum diverges, for the differential inclusion dp̄/dt ∈ β(p̄) − p̄. If δ > δ*, then β ≡ {0} and p̄ decreases to 0. If δ < δ*, then on (0, p̌) we have β = {0} and p̄ decreases; on (p̌, p̂) we have β = {1} and p̄ increases; on (p̂, 1] we have β = {0} and p̄ decreases. So 0 and p̂ attract, p̌ repels, with the basins stated. ∎

Numerically, with the parameters of §4 and δ = 0.01: the recency learner with η_t = t^{−1/2} reaches 0.0035 after twenty thousand steps from initial policies 0.05, 0.5, and 0.95 alike, and is heading to 0; the cumulative learner from 0.5 or 0.9 reaches 0.954 = p̂, and from 0.001 reaches 0.

What the two learners show. The recency learner, whose statistics reflect its present dispositions, ends at abstention whenever its exploration is outrun by the lesion's grip. The cumulative learner, whose statistics pool its whole past, ends near smoking from almost every start. The difference is a difference in memory. The cumulative learner's early exploratory abstentions, unforced and carrying the base rate of cancer, remain in its record forever and dilute the forced abstentions that accumulate later. The recency learner forgets them and is left with the forced abstentions alone.

Observe the direction of the effect. The recency learner's conditional, P(cancer | abstain) under its present policy, is the more accurate; it is the frequency that actually obtains under the dispositions the agent now has. The cumulative learner's conditional is a frequency over a heterogeneous reference class that no longer describes it. Yet it is the accurate learner that is trapped and the inaccurate one that escapes. This is not paradoxical once seen aright. Under the agent's present dispositions, abstention really is diagnostic of the anti-lesion, because under those dispositions abstention really is almost always forced. The evidential agent that knows this acts on it. Its error, if error it is, lies not in its statistics but in counting a forced act and a chosen one as the same act. §6 gives the agent the means to tell them apart.

Two conclusions for the dispute. First, the claim that the calibrated evidential agent must learn not to smoke is true of the recency learner when the lesion's grip is fixed; true of every learner when the grip is strong; and false of the cumulative learner when the grip is weak. It is a claim about learning dynamics and stands or falls with them. Second, and more important, nothing in Propositions 4 and 5 turns on the learner's being evidential rather than causal. The quantity the learner computes is a difference of two empirical frequencies drawn from the record of its own acts. A causal learner that estimates the effects of its acts from that same record computes the same difference. §6 makes this precise.

## §6 Tags: The Tickle Regimented, and the Collapse of a Distinction

The Tickle Defense, in its classical form, holds that the evidential agent who knows his own inclinations has already learned whatever the lesion has to teach him, so that the act, given the inclination, is no further evidence. Its critics reply that the agent may not know his inclinations, or that the lesion may work through the very deliberation by which he would come to know them. The double lesion lets us regiment both the defense and the reply.

Definition 3 (tags). An agent is tagged if its record of each episode includes, besides the act and the outcome, whether the act was forced or chosen. It is untagged if its record includes the act and the outcome alone. Neither kind of agent observes the state directly.

The tagged agent does not know whether it bears the lesion. It knows only whether, on this occasion, it acted or was acted upon. That is the Tickle Defense's minimal demand: not self-transparency, but the ability to tell a decision from a compulsion.

Proposition 6 (tags dissolve the problem). For the tagged evidential agent and every p ∈ (0, 1),

```latex
P_p(\mathrm{cancer}\mid\mathrm{smoke},\,\mathrm{chosen}) \;=\; P_p(\mathrm{cancer}\mid\mathrm{abstain},\,\mathrm{chosen}) \;=\; P_p(L\mid\mathrm{chosen}) \;=\; \frac{\varepsilon_L(1-\delta)}{\kappa}.
```

Hence the tagged agent's penalty on chosen acts is 0, its best response is {1} at every policy at which both conditionals are defined, and its unique fixed point is to smoke.

Proof. Given that the act was chosen, it was produced by the policy, which does not depend on the state; so the act is independent of the state given "chosen," and P_p(L | act, chosen) = P_p(L | chosen). Chosen acts occur in state L with probability ε_L(1−δ), in A with probability ε_A(1−δ), and in N with probability 1 − ε_L − ε_A; the total is κ, and the share in L is ε_L(1−δ)/κ. Cancer occurs iff L. Both conditionals are defined whenever both chosen acts have positive probability, that is, for p ∈ (0, 1); at p = 1 the conditional on chosen abstention is undefined and is supplied by any positive exploration, under which it again equals ε_L(1−δ)/κ. At p = 0 with exploration the same equality holds, so 0 is not a fixed point; the tagged agent's policy moves to 1 and stays. ∎

Remark. The tagged agent also learns that P(cancer | smoke, forced) = 1 and P(cancer | abstain, forced) = 0. But forced acts are not among its options, and these conditionals do not enter its deliberation. The tagged agent has partitioned its record into the acts that were its own and the acts that were the lesion's, and consults only the former. It knows its own inclinations in exactly the sense the Tickle Defense requires: not what it would do, but that what it is now doing is its own doing.

Definition 4 (the causal learner). The causal learner treats each of its own acts as an intervention, and estimates the effect of an act on an outcome by the empirical frequency of the outcome among the episodes in which it performed the act. It prefers the act with the higher estimated effect on utility. It is tagged or untagged according as its record is. This is the natural learning-theoretic rendering of causal decision theory: the agent that sets its act from outside and reads off what follows. It is also what a reinforcement learner does.

Proposition 7 (the two learners coincide). In each tagging regime, the causal learner and the evidential learner compute identical conditionals from identical records, and so have identical best-response maps, identical fixed points, and identical trajectories under either learning rule of §5.

Proof. The untagged causal learner's estimate of the effect of smoking is the empirical frequency of cancer among all episodes in which it smoked—forced and chosen alike, since it cannot tell them apart—which is P_p(cancer | smoke); likewise for abstention. These are the untagged evidential learner's conditionals. The tagged causal learner excludes the forced episodes, which were not its interventions, and estimates the effect of smoking by P_p(cancer | smoke, chosen); this is the tagged evidential learner's conditional. In each regime the best response is a function of the same pair of numbers. ∎

Corollary. Propositions 1 through 5 hold verbatim of the untagged causal learner. Proposition 6 holds verbatim of the tagged causal learner.

Discussion. The causal decision theorist's classical advantage in Smoking Lesion consists in this: he is told that smoking does not cause cancer, and he acts on what he is told. The evidential theorist is told the same and declines to act on it, since the correlation remains whatever its source. In the setting of the amended calibration requirement, neither agent is told anything. Each must learn the structure from the record of its own conduct, and the record is the same for both. What the causal learner adds to the record is the assumption that its acts are interventions—that they are, in the terminology of Definition 3, chosen. If they are, the tagged evidential learner has reached the same conclusion by conditioning on that very fact. If they are not, the causal learner's assumption is false, and it is deceived in exactly the way the untagged evidential learner is deceived.

A causal learner might instead be model-based, carrying a prior over causal structures and updating it on the record. But the untagged record cannot discriminate the structure in which the lesion causes both smoking and cancer from the structure in which smoking causes cancer directly; the two are observationally equivalent while the lesion is unobserved. The model-based causal learner's verdict is then a function of its prior, which the data cannot correct. If the prior favors the true structure it smokes, and if not, not. That is not learning but luck; and the evidential learner's verdict on the same record is prior-independent. On no construal does the causal learner outperform the evidential learner in the calibrated problem, except by being handed in advance what the calibration requirement forbids it to be handed.

Conclusion of the section. The distinction that survives calibration is not the distinction between conditioning and intervening. It is the distinction between an agent that can tell its decisions from its compulsions and one that cannot. Where the agent can, the problem dissolves for evidential and causal learner alike. Where it cannot, both are trapped alike, by the fixed-point structure of §4 and the dynamics of §5. The third challenge of §1—that embedded agents may really have lesions—is thereby granted, and relocated. What matters is not whether the agent has a lesion but whether the lesion's workings are, to the agent, distinguishable from its own. Where the lesion produces a compulsion the agent can feel, the agent is tagged. Where the lesion works through the deliberation itself, shifting the weights the agent deliberates with, the agent is untagged, and its own reasoning has become the channel of the confound. That is the case of §7.

## §7 The Löbian Lesion

We now formalize Troll Bridge far enough to see where it parts from the double lesion.

The setting. Let T be a consistent, Σ₁-sound, recursively axiomatized extension of Peano arithmetic, and let □φ abbreviate the arithmetized assertion that T proves φ. We use the derivability conditions—if T ⊢ φ then T ⊢ □φ; T ⊢ □(φ → ψ) → (□φ → □ψ); T ⊢ □φ → □□φ—and Löb's theorem: if T ⊢ □φ → φ then T ⊢ φ. An agent is a program about whose code T can reason; Cross is the Σ₁ sentence asserting that the program outputs "cross," and Stay its negation. Payoffs: T ⊢ Stay → U = 0; T ⊢ Cross ∧ ¬Blow → U = 10; T ⊢ Cross ∧ Blow → U = −10. The troll: T ⊢ Blow ↔ (Cross ∧ □⊥). The troll destroys the bridge if and only if the agent crosses and T is inconsistent.

The evidential agent 𝔄. 𝔄 carries a credence function P over sentences and crosses if and only if E_P[U | Cross] > E_P[U | Stay]. We assume P is T-respecting, in that P(φ) = 1 whenever T ⊢ φ, and non-dogmatic, in that P(Cross) > 0 and P(□⊥) > 0: the agent doubts, a little, both its own inaction and its own consistency. We assume further that T can verify these features of 𝔄:

```latex
(\alpha)\quad T \vdash \Box\varphi \rightarrow P(\varphi)=1, \qquad\qquad (\beta)\quad T \vdash \mathrm{Cross} \leftrightarrow \bigl(E_P[U\mid\mathrm{Cross}] > E_P[U\mid\mathrm{Stay}]\bigr).
```

These are idealizations—unbounded proof search, a credence function formalizable in T—and the standard devices for bounded search and for logical inductors are known. We set them aside.

Lemma 8 (the Löbian lesion). T ⊢ Cross → □⊥.

Proof. We argue in T. Suppose □(Cross → □⊥). By (α), P(Cross → □⊥) = 1, whence P(□⊥ | Cross) = 1, since P(Cross) > 0. By the troll's rule, P(Blow | Cross) = P(□⊥ | Cross) = 1, so E_P[U | Cross] = −10. Since T ⊢ Stay → U = 0, E_P[U | Stay] = 0. By (β), ¬Cross. A fortiori, Cross → □⊥. We have shown in T that □(Cross → □⊥) → (Cross → □⊥). By Löb's theorem, T ⊢ Cross → □⊥. ∎

Proposition 9. 𝔄 stays. Any agent occupying 𝔄's place that crosses receives 10.

Proof. By Lemma 8 and T-respect, P(Cross → □⊥) = 1, so P(□⊥ | Cross) = 1, so P(Blow | Cross) = 1, so E_P[U | Cross] = −10 < 0 = E_P[U | Stay]. By 𝔄's rule, 𝔄 stays and receives 0. T is consistent, so □⊥ is false, so Blow is false whatever any agent does; an agent that crosses receives 10. ∎

Remark (the lesion is a theorem). Lemma 8 is the double lesion's correlation—the lesion made probable by the act—in the form of a theorem: crossing provably entails inconsistency. Compare the quantities of §4. There, P_p(cancer | abstain) was a frequency; it varied with the agent's policy, and the tagged agent could partition it into a forced part and a chosen part (Proposition 6). Here P(□⊥ | Cross) = 1 is not a frequency and does not vary. It is fixed by (α) and Lemma 8 at every policy at which P(Cross) > 0. No exploration alters it, because it was not learned from exploration; and no tag partitions it, because the subcase the tag would isolate—"crossing, and T consistent"—is one that T proves empty. The Tickle Defense of §6 asks the agent to condition on the act's being its own. Lemma 8 says that any crossing by 𝔄 is accompanied by inconsistency. There is nothing left to condition on.

Note what Gödel contributes. The tagged agent of §6 needed only to distinguish force from choice; it did not need to know its state. 𝔄, to escape, would need to know that T is consistent, for that is what "this crossing is sound" comes to. Gödel's second theorem denies T that knowledge, and so denies it to any T-respecting P. Troll Bridge is the untagged case of §6 made necessary. The agent is untagged not because its introspection is poor, but because the tag it would need is one that no consistent theory can supply about itself.

Remark (the lesion is self-created). The double lesion's forcing is a feature of the situation; it works on the causal learner as on the evidential one (Proposition 7). The Löbian lesion is otherwise. Its proof used (β) at one step: from P(□⊥ | Cross) = 1 to ¬Cross. That step says that 𝔄, were it to believe that crossing entails inconsistency, would stay. It is 𝔄's responsiveness to the hypothesis that lets Löb's theorem discharge the hypothesis. Remove the responsiveness and the proof fails.

Proposition 10 (a causal agent is not afflicted). Let 𝔅 carry the same credence function P and cross if and only if 10 − 20·P₀(□⊥) > 0, where P₀(□⊥) is 𝔅's credence in inconsistency formed without regard to its own act—the credence of an agent whose causal model has □⊥ as an exogenous root and its act as an intervention upon that model. If P₀(□⊥) < 1/2, then 𝔅 crosses, receives 10, and T ⊬ Cross_𝔅 → □⊥.

Proof. 𝔅 crosses by its rule and receives 10 by Proposition 9. Cross_𝔅 is a true Σ₁ sentence, so T ⊢ Cross_𝔅. Were T ⊢ Cross_𝔅 → □⊥, then T ⊢ □⊥, a false Σ₁ sentence, contrary to Σ₁-soundness. ∎

The Löbian argument, run for 𝔅, stalls at the step that used (β). Under the hypothesis □(Cross_𝔅 → □⊥), 𝔅's credence P₀(□⊥) is unmoved, being formed without regard to the act; so 𝔅 crosses; so the hypothesis does not yield Cross_𝔅 → □⊥, and Löb's theorem finds no purchase. The correlation between crossing and inconsistency is a theorem for 𝔄 and not for 𝔅. It is brought into being by 𝔄's disposition to respect it.

Remark. The exemption is fragile in an instructive way. An agent causal about the bridge but evidential about itself—one that, told that crossing entails inconsistency and predicting that it will cross, raises its credence in inconsistency accordingly—satisfies the analogue of (β) and is afflicted like 𝔄. The trap is not for evidential agents as such. It is for any agent whose credence in the lesion answers to a theorem linking act to lesion. What (β) records is that responsiveness; evidential agents have it by design.

The fallible troll and the bounded agent. Suppose the troll, when it destroys the bridge, does so only with probability q, and consider bounded versions 𝔄_M of 𝔄 whose proof search is limited to proofs of length at most M. For 𝔄_M the modality in (α) is bounded provability, for which Löb's theorem fails (T proves ¬□_M⊥ outright, so Löb for □_M would make T inconsistent); the argument of Lemma 8 is unavailable, P(□⊥ | Cross_M) is whatever 𝔄_M's evidence makes it, and 𝔄_M crosses and, T being consistent, survives. Its record fills with safe crossings. For 𝔄 itself the argument is available, P(□⊥ | Cross) = 1, and provided q > 1/2, so that E[U | Cross] = 10 − 20q < 0, 𝔄 stays. (For q ≤ 1/2 the step through (β) fails, Lemma 8 does not go through, and 𝔄 crosses.)

The record of safe crossings does not help 𝔄. It is a record of Cross_M for various M, sentences about other programs, for which Lemma 8 does not hold and which are compatible with the consistency of T. Lemma 8 holds for Cross. 𝔄 cannot argue from its predecessors' safety, because the theorem that binds it does not bind them; and it cannot argue from T's evident consistency to the safety of its own crossing, because the theorem tells it that its own crossing would be the very mark of inconsistency. Indeed the record makes matters worse in one respect: it raises 𝔄's credence that T is consistent, whence, by Lemma 8, its credence that it will stay. Its beliefs are coherent and its conduct is poor. This is the precise sense in which Troll Bridge, unlike the double lesion, cannot be learned around. In §5 the agent's own exploration could, if it outran the lesion's grip, dilute the confound. Here the predecessors' exploration leaves the successor's theorem untouched.

## §8 Two Objections Considered

We return to the first two challenges of §1; the third was answered in §6.

The second challenge: Troll Bridge is Smoking Lesion. In the formalism of §2 a situation is a function from agents to measures over histories, and Troll Bridge is such a function. Its value at any agent is determined by whether the agent crosses and by the sentence □⊥; it is a situation that reads the agent's act and the agent's theory. In this it belongs with XOR Blackmail and Newcomb's problem, situations that read the agent. And its causal shape is Smoking Lesion's: a condition antecedent to the act—inconsistency—stands to the act and to the harm as the lesion stands to smoking and to cancer. So far the objection is correct, and we concede more than has been conceded. The basic argument of §2 disqualifies Troll Bridge exactly as it disqualifies Smoking Lesion, since 𝔄 never crosses; and the amendment of §3 readmits both, since the bounded 𝔄_M sometimes cross and the limit conditional is defined. Under the calibration requirement, uncorrected or corrected, the two problems stand or fall together.

They are separated only by the analysis of §§4–7, and the separation lies not in the situation but in the source of the agent's conditional. In the double lesion the conditional P(cancer | abstain) is a frequency. It varies with policy (Proposition 3), it is diluted by exploration that outruns the lesion (Propositions 4 and 5), and it is partitioned by a tag (Proposition 6). In Troll Bridge the conditional P(□⊥ | Cross) is a theorem (Lemma 8). It does not vary, is not diluted, and admits no partition. And it holds for the evidential agent and not for the causal one (Proposition 10), because it is generated by the evidential agent's disposition to respect it.

A formalism that represents the agent's epistemic state as a body of frequencies cannot see this difference, for in such a formalism there is nothing for a theorem to be but a frequency of 1. That, we take it, is what is meant by saying that Troll Bridge cannot be represented in the calibration formalism. The situation can be written down. What cannot be written down, in a formalism of frequencies, is how the agent came by its conditional—by counting or by proving—and that is where the two problems part.

We add that Troll Bridge exhibits the calibration phenomenon in its most extreme form. The requirement of §2 arose from the observation that the situation may depend on the agent. In Troll Bridge the confound itself depends on the agent: it obtains for 𝔄 and not for 𝔅. A theorist who asked whether crossing correlates with inconsistency, without saying for whom, would be asking an ill-formed question. This is not an objection to the calibration requirement. It is the requirement's vindication, in a case where the dependence on the agent runs all the way down.

The first challenge: mixed populations and self-uncertainty. It was asked why the situation may not be populated with both causal and evidential agents, the agent under evaluation being uncertain which it is. The reply given—that one agent is placed in the situation, not a superposition of two—is correct, and we can now say why.

For a mixed population to yield the correlation of Smoking Lesion by way of the mixture, the lesion must influence the agent's type: it must make causal agents, who smoke, while its absence makes evidential agents, who abstain. Otherwise type and lesion are independent, the correlation of smoking with cancer is that of Definition 2, and the mixture contributes nothing to it. Suppose then that the lesion does influence type, and consider the agent uncertain of its type in the act of deliberating. It is deliberating evidentially—computing P(lesion | smoke)—and this is not something it can do without being in a position to know that it is doing it. The population whose statistics bear on it is the population of agents that perform this computation; within that population there is no variation in type, and the correlation by way of type is screened off. The uncertainty that would revive the problem is uncertainty about the character of one's own present deliberation. In the double lesion that is not a coherent epistemic state. It is the tag of §6, which every deliberating agent carries by virtue of deliberating.

But the first challenge, pressed, leads to §7. Troll Bridge is precisely the case in which an agent cannot know the character of its own deliberation—not which procedure it is running, but whether the procedure's outputs are sound. Gödel denies it that knowledge, and Lemma 8 turns the denial into a confound. The superposition that the first challenge wished to introduce by stipulation, Troll Bridge introduces by theorem. The agent that cannot rule out its own inconsistency is, in the relevant sense, uncertain what kind of agent it is; and this is the one form of self-uncertainty that the amendment of §3 cannot idealize away, because no quantity of experience resolves it.

## §9 Morals

We draw five.

First. The calibration requirement is right in its motive and wrong in its first formulation. Its motive is that a situation is a function of the agent, and that a decision procedure should be judged against the situation its own adoption would produce. Its first formulation—that the stipulated statistics must be the marginal of the agent's own conduct—disqualifies every problem with a determinate solution, Troll Bridge included. The requirement needs the amendment of §3, and the amendment needs a source of variation in the act. Supply the source faithfully, as the double lesion does, and Smoking Lesion becomes a fixed-point problem with a singular limit.

Second. The singular limit means that the slogan "ideal rationality is the limit of bounded rationality" underdetermines the ideal agent's verdict. The ideal agent is a limit, and limits do not commute; to speak of the ideal agent's verdict without saying how the limit is taken is to speak of nothing in particular. Whether the calibrated evidential agent smokes or abstains depends on whether its own exploration or the lesion's grip vanishes faster, and on whether its statistics remember or forget its exploratory past. These are facts about the agent's relation to its own conduct, not about the logic of conditioning as against intervening. The claim that the evidential agent must learn not to smoke is true in some of these regimes and false in others; it is a claim about learning, not about decision theory.

Third. The distinction that survives calibration is between the agent that can tell its decisions from its compulsions and the agent that cannot. Given the tag, the problem dissolves for evidential and causal learner alike. Without it, the two learners are the same learner (Proposition 7), trapped or freed together. The classical case for causal decision theory in Smoking Lesion rests on handing the causal agent a structure it did not learn and, under calibration, could not have learned. Smoking Lesion, made legitimate, is no longer an argument between the two decision theories.

Fourth. Troll Bridge is the untagged case made necessary and made partisan. Made necessary, because the tag the agent would need—that its crossing issues from sound reasoning—is one no consistent theory can certify of itself; Gödel closes the door the Tickle Defense would open. Made partisan, because the confound is a theorem for the evidential agent and not for the causal one (Lemma 8, Proposition 10); it is the evidential agent's disposition to respect the correlation that brings the correlation into being. The double lesion's confound is contingent, escapable, and indifferent to the decision rule. The Löbian lesion's is necessary, inescapable, and created by the decision rule. That is the asymmetry the calibration requirement was reaching for, and it is sharper than calibration alone can state.

Fifth. The three challenges of §1 are each partly right. Embedded agents may have lesions; what matters is whether the lesion's channel is the agent's own reasoning. Troll Bridge is Smoking Lesion in the formalism of situations; what that formalism omits is the difference between a frequency and a theorem. Self-uncertainty about one's type is incoherent for a deliberating agent in the double lesion; it is forced upon the deliberating agent in Troll Bridge. On this last point the two problems finally converge. What no agent can learn about itself by any experience is that it may be trusted; and the Löbian lesion is what that ignorance becomes when the agent's own reasoning is the channel through which the harm arrives.
