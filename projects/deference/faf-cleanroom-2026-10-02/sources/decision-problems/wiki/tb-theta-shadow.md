# Troll Bridge as a tree: the shadow TB(θ)

Part of `two-lesions-index` · Part IV, page 17 · Previous: `lobian-lesion` · Next: [marginal-formula-learner](marginal-formula-learner.md). Status per `two-lesions-provenance`. Sources: the run's P11 ledger (`sl-workflow/notes/repair/P11.md`) and [sl-defensible-claims](../sl-workflow/notes/final/sl-defensible-claims.md) S23; [clean-source-and-policy-responsiveness](../directions/clean-source-and-policy-responsiveness.md) §4, §9; [non-responsiveness-learnability](../directions/non-responsiveness-learnability.md) §8 D; [smoking-lesion-exploration-and-boundaries](../smoking-lesion-exploration-and-boundaries.md) §9.3.

**Headline.** Written as a v2 tree, Troll Bridge is a forced-act lesion problem with two calibrated labels — not-crossing on the merits and crossing vacuously — and a separatrix at $\theta/(1-\theta)$; what the tree lacks and the bridge has is a *selector*: the Löbian proof makes the not-cross label the only one available to a proof-respecting rule, whatever the empirical frequencies [the run's P11; derived]. At the stay label every tremble device is swamped by the fixed forced mass, exactly as the double lesion's abstain label swamps vanishing exploration, while the deviation counterfactual is untouched [checked]. The run's tree is bypass-shaped, with gap $10(1-\theta)$; a tree faithful to the doc's troll gives $10(1 - 2\theta)$, which is Proposition 10's crossing rule [derived]. "Troll Bridge is the real Smoking Lesion" is confirmed in one precise sense and refined in another.

## The tree

The run's shadow $\mathrm{TB}(\theta)$: a root chance node `bot` with probability $\theta$ leads to a *forced* crossing at payoff $-10$; otherwise the decision-point $d = (s, \top, \{\mathrm{cross}, \mathrm{not}\})$ is consulted, with cross $+10$ and not $0$; Definition 6 semantics. "$O_d = \top$ is the v2 image of 'cannot prove its own consistency' — a stipulation in the tree, a theorem in the post."

This is §7.3's Smoking Lesion structure — an upstream "lesion" `bot`, an uninformative observation — with the lesion-branch act *forced* rather than drawn: the run's compulsion/bypass row ([double-lesion](double-lesion.md)) with cross for smoke. In the wiki's channel vocabulary it is channel 2a; the bridge itself is channel 3 (`channels-and-agent-boundary`).

## What the tree shows

[the run's P11-9′, 11′, 12′, 13′, 15′; checked there]

- **Definition 12 is vacuous.** For every label $q < 1$ both act-events have positive mass, so every procedure is zero-respecting; what is mugged is Definition 17's EDT at the Definition-8 state. The catch-22 of the 2019 post is, in v2, one-sided along the *referent* axis: every world-event-conditioned evidential evaluator ratifies not crossing at $q = 0$, every tree-intrinsic counterfactual selects crossing.
- **Two calibrated-and-approved pure labels for every $\theta \in (0,1)$.** $q = 0$ on the merits: at the stay label the only crossers are forced, $P(\mathrm{bad}\mid\mathrm{cross}) = 1$, $V_s(\mathrm{cross}) = -10 < 0$. $q = 1$ vacuously. Plus the interior tie $q^\ast = \theta/(1-\theta)$ iff $\theta < \tfrac12$. Selectors of crossing: Theorem 1's forcing ($G_q(\mathrm{cross}) = 10$), Theorem 2's deviation ($10(1-\theta) > 0$), and per-run SSC with a full-support self-model inside $\mathrm{occ}(d)$ ($V(\mathrm{cross}) = 10$ — unreviewed as a v2-sanctioned combination; if sanctioned, "the v2 form of the tickle defence with the tickle replaced by the occurrence"). The tremble devices — Definition 10's limit, Remark 3.12's tremble-consistency, the advice-stance evaluator — all approve not-crossing at the stay label.
- **"The troll punishes exploration" is reproduced, not confirmed:** fixed forced mass swamps vanishing trembles. At $\theta = 0.05$, $P(\mathrm{bad}\mid\mathrm{cross})$ at the stay label is $0.513, 0.913, 0.991, 1.000$ for $\varepsilon = 0.1, 0.01, 0.001, 10^{-6}$ (EDT's value of crossing $-0.26, -8.27, -9.81, -10.00$); at the cross label it is $0.0525 \to 0.05$ [checked]. This is the crossover of [double-lesion-fixed-points](double-lesion-fixed-points.md) with `bot` for the lesion.
- **Multiplicity without a selector.** The tree fails the 2021 post's first test of "real Troll Bridge" — crossing is not impossible, $q = 1$ is calibrated and approved for every $\theta$. "v2 has multiplicity without a selector; Troll Bridge is a selector without multiplicity." The 2019 post's LIDT that crosses for a long time and then stops is a jump between the two basins triggered by the proof.
- **"The real Smoking Lesion", confirmed and refined.** Confirmed: the population correlation $P(\mathrm{bot} \mid \mathrm{cross}) - \theta$ is real and strictly calibrated at $O = \top$ at labels $q < 1$ ($\tfrac{9}{10}, \tfrac{9}{110}, 0$ at $q = 0, \tfrac12, 1$ for $\theta = 0.1$) and vanishes at $q = 1$ — label-dependent and self-fulfilling, "better-posed than P01's lesion." Refined: in the post the lesion is unobservable *in principle* (Gödel II); in the tree $O_d = \top$ is a *stipulation* the modeller may lift — SSC, or $O_d = \{\mathrm{bot} = 0\}$, dissolves the problem as the tickle instantiation dissolves Smoking Lesion. "TB is the lesion problem whose correlation survives strict calibration at an uninformative observation at the pessimistic labels and dies under occurrence-conditioning — the tickle defence Gödel-blocked in the post, stipulation-blocked in the tree." And "forced crosser ≠ deliberator."

## Bypass-shaped versus doc-faithful

The run's tree writes crossing on the `bot` branch *without consulting $d$* — the inconsistent world forces the act — so its deviation gap is $V(\mathrm{cross}) - V(\mathrm{not}) = 10(1-\theta)$. The doc's troll (`lobian-lesion`) has the agent cross in the $\Box\bot$ world by its own rule (in the pure-logic version, by the chicken clause), and the payoff is $-10$ only on $\mathrm{cross} \wedge \Box\bot$. A **doc-faithful tree** consults $d$ in both worlds: payoff $-10$ on cross $\wedge$ `bot`, $+10$ on cross $\wedge$ ¬`bot`, $0$ on stay. Its deviation gap is $10(1-\theta) - 10\theta = 10(1 - 2\theta)$, positive iff $\theta < \tfrac12$ — *verbatim* Proposition 10's rule "cross iff $10 - 20 P_0(\Box\bot) > 0$" with $P_0 = \theta$ [derived; [clean-source-and-policy-responsiveness](../directions/clean-source-and-policy-responsiveness.md) §4]. Both trees classify `bot` as non-responsive ([policy-responsiveness](policy-responsiveness.md)); they differ only in whether the label controls the inconsistent world's act. The session note's §9.3 used the run's shape and its numbers are corrected accordingly; the qualitative claims survive.

## Five evaluations of "cross" at the stay label

$O_d = \top$, $\theta = 0.1$, on the run's tree [checked, [non-responsiveness-learnability](../directions/non-responsiveness-learnability.md) §8 D]:

| evaluator | value of crossing |
|---|---|
| the act-event conditional $E[U \mid \{\mathrm{cross}\}]$ | $-10$ |
| Axiom NR's $\sum_e P(e) P(\cdot \mid \mathrm{cross}, e)$ ([non-responsiveness](non-responsiveness.md)) | $8$ |
| the draw-conditional $E[U \mid \mathrm{draw} = \mathrm{cross}]$ | $8$ |
| Theorem 1's single-node forcing $G_q$ | $10$ |
| Theorem 2's deviation $V_B(C[d \mapsto \mathrm{cross}])$ | $8$ |

At $\theta = \tfrac14$ the middle three are $5$; at $\theta = \tfrac35$ they are $-2$ and the agent should stay. So the exogenous-rigidity axiom selects Theorem 2's referent, not Theorem 1's (at $O = \top$ its marginal is the population marginal), and coincides with the draw-conditional — the act/draw split of `tags-and-draw-coordinate` is what separates the first row from the rest.

## A caution about the tree as a stand-in

In the actual bridge every crossing a consistent agent ever makes is safe, so a tagged binding-coin agent learns $P(\mathrm{bad} \mid \text{coin-cross}) = 0$ ([clean-source-and-llc](clean-source-and-llc.md)). $\mathrm{TB}(\theta)$ makes inconsistency a *frequency* — a `bot` branch that crosses and is blown up with probability $\theta$ — and on the realized-act algebra pools those crossings with the coin's; then a coin at rate $\varepsilon \ll \theta$ is swamped and the pooled tremble agent stays. That is the Smoking-Lesion crossover, not a fact about the bridge: the doc's "there is nothing for a theorem to be but a frequency of 1" biting the tree from the other side. The deviation evaluator does not see it either way.

## Told-You-So is not Troll Bridge

The run also checked the tempting identification of v2's §7.1 example (the announcer who tells you which of two amounts you will take, the zero-respecting procedure taking the smaller) with "Troll Bridge with the logic replaced by an announcer": withdrawn. Told-You-So is the calibration shadow of the *spurious-proof* problem the chicken rule solves; the shared lever is the adversary's order, but the exploited object differs — a zero-respecting *policy* there, an *evaluator at the event referent* here [the run's P11-10′; reconstructed].

## What the shadow is good for

It makes three things checkable that the post states in prose: that the not-cross fixed point is calibrated and self-fulfilling (the doc's "the refuser is right"); that the swamping of trembles by fixed forced mass is arithmetic, not logic; and that every tree-intrinsic counterfactual crosses. What it cannot do is *select* — and the wiki's account of the selector is [marginal-formula-learner](marginal-formula-learner.md): the proof-respecting rule is what makes crossing imply inconsistency, and a rule that does not consult the act-conditional is a Definition-4 procedure for which the selector never fires.
