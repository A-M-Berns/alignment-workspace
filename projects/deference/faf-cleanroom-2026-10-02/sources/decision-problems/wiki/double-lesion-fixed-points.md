# Fixed points of the double lesion

Part of `two-lesions-index` · Part II, page 5 · Previous: [double-lesion](double-lesion.md) · Next: `double-lesion-dynamics`. Status per `two-lesions-provenance`. Sources: [two-lesions-doc-2026-09-18](../two-lesions-doc-2026-09-18.md) §4 (Propositions 1–3, Corollary); [smoking-lesion-exploration-and-boundaries](../smoking-lesion-exploration-and-boundaries.md) §1, §8 and `smoking-lesion-antilesion-check.py`; [iv-design-draw-as-instrument](../directions/iv-design-draw-as-instrument.md) §5; [sl-defensible-claims](../sl-workflow/notes/final/sl-defensible-claims.md) S5.

**Headline.** Under the hypothesis that the pleasure of smoking is small against the lesion's cancer cost weighted by either its base rate or its complement, abstention is a fixed point of the evidential agent for every grip, smoking is not, and for weak grip two interior fixed points appear whose limit is $\{0, 1\}$ while the fixed point of the limiting penalty is $\{0\}$ [the doc's Propositions 1–3 and Corollary; endpoint values checked in general]. Outside that hypothesis the smoke label is itself a fixed point and the abstain basin is small [checked]. Either way the ideal agent's verdict is a matter of how a limit is taken, not of its decision rule.

## The object

The evidential agent at policy $p$ compares $\pi$ with the penalty $\Delta(p) = C[P_p(\text{cancer}\mid\text{smoke}) - P_p(\text{cancer}\mid\text{abstain})]$ ([double-lesion](double-lesion.md)). Its best response $\beta(p)$ is $\{1\}$ if $\pi > \Delta(p)$, $\{0\}$ if $\pi < \Delta(p)$, and $[0,1]$ at indifference. A **fixed point** is $p^\ast \in \beta(p^\ast)$: a policy that, once adopted, generates the very conditionals on which the agent would adopt it. The amended calibration requirement (`basic-argument-and-amendment`) says the double lesion is a legitimate test of the evidential agent exactly at its fixed points.

## Hypothesis (H)

$$
\text{(H)} \qquad \pi \;<\; C\,(\gamma_1 - \gamma_0)\cdot\min(\varepsilon_L,\; 1 - \varepsilon_L).
$$

"The pleasure of smoking is small against the cost of cancer, whether that cost is weighted by the base rate of the lesion or by its complement" (doc §4). With $\gamma = (1,0)$ this is the doc's (H). The doc's parameters ($\varepsilon_L = 0.2$, $C = 100$, $\pi = 1$) satisfy it; the session note's ($\varepsilon_L = 0.1$, $C(\gamma_1-\gamma_0) = 5.5$, $\pi = 1$) violate its first half, since $0.55 < 1$.

## The endpoints

**Proposition 1 (abstention is a fixed point).** [derived in general; the doc's proof at $\gamma = (1,0)$]

$$
\Delta(0) \;=\; \frac{C\,(1-\varepsilon_L)\,(\gamma_1 - \gamma_0)}{1 - \varepsilon_L\delta} \;\geq\; C(1-\varepsilon_L)(\gamma_1-\gamma_0) \;>\; \pi \quad\text{under (H)},
$$

so $\beta(0) = \{0\}$ and $p = 0$ is a fixed point for every $\delta \in (0,1]$. At $p = 0$ the only smoking is forced, so smoking is near-perfect evidence of the lesion.

**Proposition 2 (smoking is not a fixed point).** [derived in general]

$$
\Delta(1) \;=\; \frac{C\,\varepsilon_L\,(\gamma_1 - \gamma_0)}{1 - \varepsilon_A\delta} \;\geq\; C\varepsilon_L(\gamma_1-\gamma_0) \;>\; \pi \quad\text{under (H)},
$$

so $\beta(1) = \{0\}$ and $p = 1$ is not a fixed point for any $\delta$.

**What does the work (the doc's remark).** At $p = 1$ the agent's smoking is nearly uninformative — $P_1(\text{cancer}\mid\text{smoke})$ is within a factor $(1-\varepsilon_A\delta)^{-1}$ of the population rate. It is that *abstention is perfect evidence of the anti-lesion*, hence of the lesion's absence: the agent that never abstains by choice finds in its record of abstentions only the harmless compulsion, and credits abstention with eliminating the lesion's base-rate risk, worth $C\varepsilon_L(\gamma_1-\gamma_0)$. The mutual exclusion of lesion and anti-lesion is load-bearing: were the anti-lesion independent of the lesion, forced abstention would carry the base rate of cancer, $\Delta(1)$ would be $O(\delta)$, and smoking would be a fixed point for every small $\delta$. The exclusion is faithful to the original problem, in which abstainers are less likely than average to bear the lesion — but it should be seen for what it does. Neither endpoint gap depends on $\delta$ as $\delta \to 0$ [checked: at $\delta \in \{0.2, 0.05, 0.01, 0.001\}$ the session note's gaps converge to $\varepsilon_L(\gamma_1-\gamma_0) = 0.055$ and $(1-\varepsilon_L)(\gamma_1-\gamma_0) = 0.495$].

## The interior and the singular limit

**Proposition 3 (doc, $\gamma = (1,0)$).** (i) $\Delta$ is convex on $[0,1]$. (ii) For $p$ in any closed subinterval of $(0,1)$, as $\delta \to 0$,

$$
\Delta(p) \;=\; C\,\varepsilon_L\,\delta\left[\frac{1-\varepsilon_L}{p} + \frac{\varepsilon_A}{1-p}\right] + O(\delta^2),
$$

so $\Delta(p) \to 0$ on the interior while $\Delta(0) \to C(1-\varepsilon_L)$ and $\Delta(1) \to C\varepsilon_L$. (iii) Let $m(\delta) = \min_{[0,1]} \Delta$. Under (H): if $m(\delta) > \pi$ the unique fixed point is $0$; if $m(\delta) < \pi$ there are exactly three, $0 < \check p(\delta) < \hat p(\delta) < 1$, the latter two solving $\Delta(p) = \pi$. To first order $m(\delta) = C\varepsilon_L\delta(\sqrt{1-\varepsilon_L} + \sqrt{\varepsilon_A})^2$, so the three-fixed-point regime obtains for $\delta$ below

$$
\delta^\ast \;\approx\; \frac{\pi}{C\,\varepsilon_L\,(\sqrt{1-\varepsilon_L} + \sqrt{\varepsilon_A})^2},
$$

with $\check p(\delta) = \varepsilon_L\delta\,(C(1-\varepsilon_L) - \pi)/\pi + O(\delta^2)$ and $1 - \hat p(\delta) = \varepsilon_A\delta\,(C\varepsilon_L - \pi)/\pi + O(\delta^2)$. [reconstructed from the doc; the general-$\gamma$ version presumably carries a factor $(\gamma_1 - \gamma_0)$ — guess, not re-derived]

Numerically (doc): $\delta^\ast \approx 0.028$; at $\delta = 0.1$ the unique fixed point is $0$; at $\delta = 0.001$ the fixed points are $0$, $0.0159$, $0.9961$ against the asymptotic predictions $0.0158$, $0.9962$. Independently reproduced [checked, [iv-design-draw-as-instrument](../directions/iv-design-draw-as-instrument.md) §5]: at $\delta = 0.01$ the crossings are $0.1670$ and $0.9540$.

**Corollary (the limit of the fixed points is not the fixed point of the limit).** Let $\Delta_0 = \lim_{\delta\to 0}\Delta$: it vanishes on $(0,1)$ and equals $C(1-\varepsilon_L)$, $C\varepsilon_L$ at the endpoints. Its best-response map has $0$ as unique fixed point. But the fixed points of the $\delta$-problems converge to $\{0, 1\}$: $\check p \to 0$ and $\hat p \to 1$.

## Two readings of the amendment

The amendment said the ideal agent's conditionals are the limits of the bounded agents' conditionals, and did not say at which policy the limit is taken (doc §4).

- **First reading.** Fix the ideal agent's policy and take the limit of the bounded conditionals at that policy: $\Delta_0$. Abstention is the unique fixed point; the classical verdict is vindicated — the calibrated evidential agent forgoes $\pi$ for nothing. In v2 this is Definition 10, limit calibration at a fixed label.
- **Second reading.** Take the limit of the bounded agents' fixed points: $\{0, 1\}$. The ideal evidential agent may smoke, as the limit of the policies $\hat p(\delta)$, in which it abstains by choice with probability $O(\delta)$ — just enough that its chosen abstentions are not swamped by its forced ones. In v2 this is Remark 3.12's tremble-consistency, evaluated along the sequence.

They differ over the conditional on an act of vanishing probability: fixed by the forcing mechanism alone (first), or as the limit of the agent's own mixtures (second). "The amendment says 'limit' and does not say in what order." The question of order "is the question whether the agent's own exploration or the lesion's grip vanishes faster; and that is a question about the agent's relation to its own conduct, not about the logic of its decision rule." Where the grip is strong, $\delta > \delta^\ast$, the question does not arise and abstention is the unique fixed point without qualification.

## Outside (H): the session note's regime

When $C\varepsilon_L(\gamma_1 - \gamma_0) < \pi$ — the lesion's *population-average* cancer excess is worth less than smoking — Proposition 2 fails and the smoke label is a fixed point. In the session note's regime ($\delta = 0.05$) both pure labels are fixed points, with gaps $0.0553$ at the smoke label and $0.4975$ at the abstain label against a threshold of $\pi/C = 0.1$ [checked]. The interior indifference sits near $p^\ast \approx 0.02$ [checked in [iv-design-draw-as-instrument](../directions/iv-design-draw-as-instrument.md) §5; the session note's coarser grid put it near $0.04$–$0.08$], so the abstain basin is small: a learner that deliberately smokes more than about one time in fifty is pushed to smoking. With the earlier session reply's idealization $\gamma = (1,0)$, $C = 10$, $\pi = 1$, the smoke label is a fixed point iff $\varepsilon_L < 0.1$; at $\varepsilon_L = 0.1$ exactly it just fails to be (gap $0.1005$ against $0.1$, a knife-edge finite $\delta$ tips). This corrected the first session reply's claim that abstention is the *unique* fixed point "with standard numbers": uniqueness is (H).

## Exploration and the crossover

Adding lesion-uncorrelated noise at rate $\eta$ — the agent's own tremble or an environment-side coin, it makes no difference (`epsilon-versus-voi`) — dilutes both gaps. The abstain fixed point survives iff $\eta$ is small relative to $\delta$ [checked, session note §8]:

| $\delta$ | $\eta = 10^{-4}$ | $10^{-3}$ | $10^{-2}$ | $10^{-1}$ |
|---|---|---|---|---|
| 0.2 | both fixed | both | both | both |
| 0.05 | both | both | both | smoke only |
| 0.01 | both | both | smoke only | smoke only |
| 0.002 | both | both | smoke only | smoke only |

This is the doc's Proposition 4 (the recency learner: $p_t \to 1$ when $\eta_t/\delta_t \to \infty$, $\to 0$ when $\to 0$) seen statically, and the same crossover reappears in Troll Bridge as "fixed forced mass swamps vanishing trembles" ([tb-theta-shadow](tb-theta-shadow.md)).

## The question of instability, from [another person in the thread]

The population statistic is label-dependent: the smoking–cancer correlation is $(1-\varepsilon_L)(\gamma_1-\gamma_0)$-sized at one label and $\varepsilon_L(\gamma_1-\gamma_0)$-sized at the other, so what the problem "says" about the population changes with which agent is dropped in. The Smoking-Lesion run made this an identity (S5, Corollary 12′, Lean-checked for the arithmetic): on the two-branch lesion tree with smoking rates $q_1, q_0$ at the lesioned and unlesioned points,

$$
\nu(k \mid m{=}1) - \nu(k \mid m{=}0) \;=\; \frac{(\gamma_1 - \gamma_0)(q_1 - q_0)\,\rho(1-\rho)}{\nu(m{=}1)\,\nu(m{=}0)},
$$

with sign $= \operatorname{sign}(q_1 - q_0)$: the population correlation *is* the procedure's type-difference, and a population of calibrated evidential agents shows the lesion–smoking correlation only if their desirabilities differ by lesion. That is the instability [another person in the thread] was asking about, and the reason a mixed population revives the problem only by making the lesion influence the agent's type (`tags-and-draw-coordinate`).
