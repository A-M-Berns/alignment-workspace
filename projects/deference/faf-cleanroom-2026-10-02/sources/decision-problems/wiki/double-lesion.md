# The double lesion

Part of `two-lesions-index` · Part I, page 4 · Previous: `basic-argument-and-amendment` · Next: [double-lesion-fixed-points](double-lesion-fixed-points.md). Status per `two-lesions-provenance`. Sources: [two-lesions-doc-2026-09-18](../two-lesions-doc-2026-09-18.md) §3; [smoking-lesion-exploration-and-boundaries](../smoking-lesion-exploration-and-boundaries.md) §1; [sl-defensible-claims](../sl-workflow/notes/final/sl-defensible-claims.md) S1–S4; [iv-design-draw-as-instrument](../directions/iv-design-draw-as-instrument.md) §0–§2.

**Headline.** The double lesion is Smoking Lesion with a source of variation in the act that is faithful to the problem: the lesion sometimes forces smoking, a mutually exclusive and harmless anti-lesion sometimes forces abstention, and the agent acts on its policy otherwise [the doc's Definition 2]. "Forces" is ambiguous between two trees with one run law — the lesion acts *instead of* the agent (bypass) or *overwrites* what the agent decided (overwrite) — and they differ at the subjective-state grade [derived; `tags-and-draw-coordinate`]. In v2 both are failures of Definition 7's recording, which is exactly the hypothesis the textbook inconsistency theorem needed [derived; the run's S3].

## Why an anti-lesion

The amendment (`basic-argument-and-amendment`) needs bounded agents that sometimes take the act the ideal agent forgoes. The doc's §3 names two sources: the agent varies its conduct (exploration), or something else does. To be faithful to Smoking Lesion the lesion should be that something. But the lesion varies conduct in one direction only: a bounded EDT agent inclined to abstain acquires data on smoking through the lesion, while one inclined to smoke never abstains and has no data on abstention — the conditional is undefined "at exactly the fixed point we most need to examine." Hence the anti-lesion, "a second condition, harmless, which occasionally forces abstention, and which excludes the lesion as the lesion excludes it."

## Definition

> **Definition 2 (doc), generalized.** Fix $\varepsilon_L, \varepsilon_A > 0$ with $\varepsilon_L + \varepsilon_A < 1$; grip $\delta \in (0, 1]$; pleasure of smoking $\pi > 0$; cost of cancer $C > 0$; cancer rates $\gamma_1$ in state $L$ and $\gamma_0 < \gamma_1$ otherwise (the doc: $\gamma_1 = 1$, $\gamma_0 = 0$). In each episode the agent is in exactly one of $L$ (probability $\varepsilon_L$), $A$ ($\varepsilon_A$), $N$ (the rest). In $L$, with probability $\delta$ the agent smokes regardless of its policy; in $A$, with probability $\delta$ it abstains regardless; otherwise it acts on its policy, a probability $p \in [0,1]$ of smoking. Utilities add: $+\pi$ for smoking, $-C$ for cancer.

Two readings are built in (doc §3): frequencies across one agent's episodes with the lesion coming and going, or across a population of agents running one procedure, each lesioned or not for life. Under the second a "policy" is the procedure's recommendation and an "episode" is an agent.

## Explicit forms

Write $\kappa = 1 - \delta(\varepsilon_L + \varepsilon_A)$ for the mass of episodes in which the agent acts on policy (the *compliers*), and $c_C$ for the cancer rate among them:

$$
c_C \;=\; \frac{\varepsilon_L(1-\delta)\,\gamma_1 + (1 - \varepsilon_L - \varepsilon_A\delta)\,\gamma_0}{\kappa}.
$$

Then, with $P_p$ the law induced by policy $p$ [checked; the doc's forms at $\gamma = (1, 0)$]:

$$
\begin{aligned}
P_p(\text{smoke}) &= \varepsilon_L\delta + \kappa p, &\qquad P_p(\text{cancer} \wedge \text{smoke}) &= \varepsilon_L\delta\,\gamma_1 + \kappa\, c_C\, p,\\
P_p(\text{abstain}) &= \varepsilon_A\delta + \kappa(1-p), &\qquad P_p(\text{cancer} \wedge \text{abstain}) &= \varepsilon_A\delta\,\gamma_0 + \kappa\, c_C\,(1-p).
\end{aligned}
$$

Every observable is affine in $p$ — the fact `epsilon-versus-voi` and `iv-reading-of-decision-problems` build on. The conditionals the evidential agent computes are ratios of affine functions:

$$
P_p(\text{cancer} \mid \text{smoke}) = \frac{\varepsilon_L\delta\,\gamma_1 + \kappa c_C p}{\varepsilon_L\delta + \kappa p}, \qquad
P_p(\text{cancer} \mid \text{abstain}) = \frac{\varepsilon_A\delta\,\gamma_0 + \kappa c_C (1-p)}{\varepsilon_A\delta + \kappa(1-p)}.
$$

Both are strictly decreasing in $p$ (doc §3). At $p = 0$ the only smokers are lesion-forced, so the first equals $\gamma_1$; at $p = 1$ the only abstainers are anti-lesion-forced, so the second equals $\gamma_0$. The *evidential penalty* is $\Delta(p) = C\,[P_p(\text{cancer}\mid\text{smoke}) - P_p(\text{cancer}\mid\text{abstain})]$, and the evidential agent smokes, abstains, or is indifferent as $\pi$ exceeds, falls short of, or equals $\Delta(p)$. Its analysis is [double-lesion-fixed-points](double-lesion-fixed-points.md).

## Two trees, one run law

"Smokes regardless of its policy" can be realized on a v2 tree in two ways ([smoking-lesion-exploration-and-boundaries](../smoking-lesion-exploration-and-boundaries.md) §1):

- **Bypass.** Root chance over $(L, A, N)$; on the $L$ branch a chance node sends mass $\delta$ to a leaf-world with $m = 1$ *without consulting the decision-point* $d$; symmetrically on the $A$ branch with $m = 0$; all other mass consults $d$. The forced runs are not in $\mathrm{occ}(d)$. This is a **coverage failure** in Definition 7's sense.
- **Overwrite.** Every run consults $d$; after the draw, a chance node replaces the drawn action with $m = 1$ w.p. $\delta$ on the $L$ branch and $m = 0$ w.p. $\delta$ on the $A$ branch. The forced runs are in $\mathrm{occ}(d)$ but the leaf-world's act is not the draw. This is an **action-veridicality failure**.

Both trees have the same law $\nu_{B,C}$ over $(\ell, \ell', m, k)$ at every policy [checked]. They differ in what $\mathrm{occ}(d)$ is and in whether the draw is a coordinate of the world. The doc's Definition 2 is neutral between them, and the difference is decision-relevant only for conditioning on the realized act at the subjective-state grade (`tags-and-draw-coordinate`); for the label-level verdict it is idle (`double-lesion-dynamics`). The instrumental-variable reading needs the overwrite tree, because an instrument must take a value on every unit (`iv-reading-of-decision-problems`).

## Where it sits in v2 §7.3

v2's §7.3 stipulates Smoking Lesion as (S1) lesion-only cancer, (S2) correlated conditionals at the queried state, (S3) one queried point with the uninformative observation $O_d = \top$, and proves (Proposition 11) that it is inconsistent for *every* procedure: Lemma 3 gives $m \perp (\ell, k)$ under every realizable worldview, so (S2) is no worldview of any instantiation. Proposition 12 shows the *tickle instantiation* — lesion-informative observations, distinct points — is consistent and EDT and CDT both smoke there.

The Smoking-Lesion run found (S3, its ledger's Claim, adopted as amendment SL-29) that (S1)–(S3) do *not* entail recording: a one-node $O_d = \top$ tree on which something other than the draw sometimes writes $m$ satisfies them literally and has (S2) true for every $C$. Proposition 11 needs a fourth stipulation, **(S4): the act coordinate is written only by $d$'s draw** — Definition 7's recording. Dropping (S4), the textbook contrast has exactly two consistent homes (S2): the reference-class instantiation (coverage failure — others write the act) and the compulsion instantiation (action-veridicality failure — the lesion overwrites the draw). The double lesion's bypass tree is the reference-class row with a second writer for abstention; its overwrite tree is the compulsion row with an anti-compulsion. The anti-lesion is what is new: in the one-sided rows the smoke label is trivially consistent because nobody else writes abstention; the anti-lesion makes abstention informative at the smoke label ([double-lesion-fixed-points](double-lesion-fixed-points.md)).

## What the state sees, by grade

**At observation calibration with $O_d = \top$ (Claim 1.1 of the session note) [checked].** Definition 8 conditions on the world-event $\top$, so $P_{s_d} = \nu$ on both trees, forced runs included. Both acts have positive probability under every $C$ once $\delta > 0$, so strict OC already gives EDT content — no masking, no Definition-10 trembles needed. Forcing supplies from the environment's side the off-path mass trembles supply from the agent's.

**At subjective-state calibration (Claim 1.2) [checked].** Per-run SSC conditions on $\mathrm{occ}(d)$. On the bypass tree the forced runs drop out, Lemma 3 applies to what remains, the evidential gap is exactly $0$ for every label, and EDT smokes; without trembles the unchosen act has no consulted mass and approval is vacuous. On the overwrite tree $\mathrm{occ}(d)$ is every run, the realized act is correlated with $\ell$ inside it, and the OC analysis repeats verbatim. Adding a *draw* coordinate and conditioning on it restores Lemma 3 on either tree (`tags-and-draw-coordinate`).

So the author's "perhaps I should take a version of the problem seriously after all" is grade- and algebra-relative: yes at OC with an uninformative observation on either tree; yes at SSC on the overwrite tree read on the realized-act algebra; no at SSC on the bypass tree; no on any tree once the agent's own draw is an event it can condition on.

## Parameters used in this wiki

Two sets recur. **The doc's:** $\varepsilon_L = \varepsilon_A = 0.2$, $C = 100$, $\pi = 1$, $\gamma = (1, 0)$; hypothesis (H) of [double-lesion-fixed-points](double-lesion-fixed-points.md) holds. **The session note's:** $\varepsilon_L = \varepsilon_A = 0.1$, $\gamma_0 = 0.05$, $\gamma_1 = 0.6$, $C = 10$, $\pi = 1$, $\delta = 0.05$; (H) fails, since $C(\gamma_1 - \gamma_0)\varepsilon_L = 0.55 < \pi$. Results quoted from either source name which set they use.
