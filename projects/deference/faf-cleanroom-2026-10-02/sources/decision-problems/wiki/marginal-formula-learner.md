# The marginal-formula learner: 𝔅 at the act level and its policy-level lift

Part of `two-lesions-index` · Part IV, page 18 · Previous: [tb-theta-shadow](tb-theta-shadow.md) · Next: [troll-variants](troll-variants.md). Status per `two-lesions-provenance`. Sources: [smoking-lesion-exploration-and-boundaries](../smoking-lesion-exploration-and-boundaries.md) §9.3–§9.4; [policy-level-fdt-learner](../directions/policy-level-fdt-learner.md) (specification, runs, conjecture); [non-responsiveness-learnability](../directions/non-responsiveness-learnability.md); [two-lesions-doc-2026-09-18](../two-lesions-doc-2026-09-18.md) §7; the CDT=EDT? sequence posts 04, 11, 12, 13; `Logsidian/journals/2023-05-28.md`.

**Headline.** The agent that crosses the bridge evaluates acts by the *marginal formula* $\mathrm{cf}(U \mid do\,a) = \sum_w P(w)\, E(a, w)$ — its marginal over exogenous variables including the logical state, composed with the environment's response function — and never consults its act-conditionals; it is the doc's $\mathfrak{B}$, and on the tree it is CDT with the logical state in the fixed algebra [derived]. Lifted to the policy level, with the exogenous set decided by a policy-invariance test, it smokes in the double lesion, one-boxes against every policy-reading Omega, two-boxes against a policy-invariant box, refuses XOR, pays the mugging, takes 10, and crosses every troll bridge whose trigger is a fact about the environment [checked by simulation, five seeds]. Relocation to the policy level does not by itself save EDT from Lemma 8; only the non-responsiveness clause does [derived]. The learner mis-partitions exactly when the environment reads a feature of the agent that is not a coordinate of its policy [checked]. Its convergence is stated as a conjecture whose statistical parts look provable and whose VOI part is the sequence's own open problem.

## The act-level agent

The session note's §9.3, as corrected in its §9.4. An **FDT learner** — a name now flagged as a collision, see below — evaluates

$$
\mathrm{cf}(U \mid do\,a) \;=\; \mathbb{E}_{w \sim P}\big[E(a, w)\big],
$$

the marginal belief over world-states $w$ — including $\mathrm{Incon}$ — composed with the response function $E$; $E(a, \cdot)$ is learned from tagged outcomes of the agent's own draws and from proofs about the environment's rule (the troll's stated trigger); $P(\mathrm{Incon})$ is small by non-dogmatism. Three consequences:

1. **Lemma 8's inner step fails.** Crossing with the proof in hand is consistent with the rule, since the rule never consults $P(\mathrm{bad} \mid \mathrm{cross})$; so crossing does not imply misfire, Löb does not fire, and (the theory being sound) no proof exists. Counterfactual and conditional never *actually* disagree — the author's point at `13-my-current-take-on-counterfactuals` l. 787 — the disagreement is hypothetical.
2. **The exogeneity of the draw is a policy, not a belief** — *corrected*: the session note said the formula alone shields the marginal because the proof constrains $P(w \mid a)$, never consulted. Wrong as the reason: under coherence a believed $\mathrm{Cross} \to \Box\bot$ moves $P(\Box\bot)$ through $P(\mathrm{Cross})$. The shield is the *language* the marginal is formed over — NR3 of [non-responsiveness](non-responsiveness.md) — and that is what the doc's "formed without regard to its own act" has to mean. The agent does not believe its draw is sound; it declines to treat its draw as evidence about soundness, and it does so by not having a name for itself in the language its exogenous marginal lives in. *The tickle defence adopted as a policy where Gödel makes it unavailable as a belief.*
3. **It is a Definition-4 procedure under Definition 6; the proof-respecting agent is not.** In consistent worlds it crosses regardless of $\mathrm{Incon}$; the evidential agent's crossing implies $\mathrm{Incon}$, so its draw has a parent other than its state. "Troll Bridge is outside the type" (the run's S23) is a fact about the *agent*, and the type boundary is normative (`channels-and-agent-boundary`).

**The naming collision.** This object is the doc's Proposition 10 agent $\mathfrak{B}$ — a "causal agent" — and on the run's tree it is $\mathrm{CDT}_G$ with the temporal structure $\mathrm{bot} \to m$ (cross iff $\theta < \tfrac12$), i.e. classical CDT with $\mathcal{E}_0 = \langle\Box\bot\rangle$ ([learning-cdt-renderings](learning-cdt-renderings.md)). Its FDT character appears only at the policy level, where responsiveness fixes the roots and it one-boxes. Read "FDT learner" in the session note as "marginal-formula agent"; the policy-level lift below is the FDT candidate.

**Why VOI alone does not rescue EDT** [derived]. With the proof in hand a proof-respecting conditional has $P(\neg\mathrm{bad} \mid \mathrm{cross}) = 0$, so the information value of crossing is exactly zero. The author's 2023 conditional-contracts idea (`Logsidian/journals/2023-05-28.md` ll. 29–35) — a discounted logical inductor "should see value-of-information in crossing … since the P(A|B)=C(A|B) enforcement trader must disagree with some other traders" — works because the market contains traders *not* bound by the proof, i.e. an FDT-like component whose disagreement the VOI resolves; [non-responsiveness](non-responsiveness.md) shows the bundle price is the market's form of the marginal formula and that the shield it gives is finite-horizon. VOI exploration depends on the marginal formula; it is not an independent escape.

## The policy-level lift

From [policy-level-fdt-learner](../directions/policy-level-fdt-learner.md) §1. [derived; implemented]

**Policy.** A Definition-4 procedure restricted to the points the learner can occupy and quotiented by observation-functionality: a map from observations to mixed actions, one label per point, applied at *every* node carrying that point (Omega's simulation node and the live node draw i.i.d. from the same label). The learner varies a label for a whole round — exactly Definition 22's all-occurrence point-deviation, never Theorem 1's single-instance forcing.

**State.** A policy set $\Pi$; a set of observed per-round variables partitioned into *exogenous* $W$ and *responsive* $R$, recomputed from data; a belief $P$ over $W$-configurations, with a prior $P_0$ for *latent* exogenous variables ($\mathrm{Incon}$) that data can move only through the likelihood; a response function $E(\pi, w)$ stored per cell; admitted proofs of the forms "$\forall w\, E(\pi, w) = \dots$" and "$P(w) = \dots$".

**Decision rule.** $\mathrm{cf}(U \mid do\,\pi) := \sum_w P(w)\, \mathbb{E}_{E(\pi, w)}[U]$, maximized over $\Pi$. On visited policies with a correct partition this equals $E[U \mid \pi_t = \pi]$, so the FDT property holds by construction on the visited set, and the formula differs from policy-level EDT only at unvisited policies (extrapolation), at latent $W$, and wherever something asserts $P(w \mid \pi) \neq P(w)$ for a $w \in W$ — which is the whole of Troll Bridge.

**Exploration.** VOI under a discount near $1$; the simulation uses Thompson sampling over $(P, E)$ as a flagged stand-in — posterior sampling explores in proportion to residual disagreement and vanishes as the posterior concentrates.

**Updates.** Every observation of a $W$-variable updates $P(w)$ as a *pooled* frequency over all rounds whatever the policy — $P(w)$ is never indexed by $\pi$. Every $(\pi_t, w_t, \text{outcome})$ updates the cell $E(\pi_t, w_t)$. The partition: for each observed variable, a Dirichlet-multinomial marginal-likelihood test of "one law pooled over policies" against "one law per visited policy"; the variable is in $W$ iff the pooled model wins (the penalty for the per-policy model grows like $|\Pi| \log n$).

**Non-responsiveness clause.** A theorem about the *composite* — any sentence "$\pi_t = \pi \to \varphi(w)$" derived from the agent's own code — is inert: it constrains $P(w \mid \pi)$, never formed. A theorem about $E$ or about $P(w)$ is admitted. This is Definition 6 adopted by the agent for channel 3.

**Relation to $\mathfrak{B}$.** The doc's $\mathfrak{B}$ is the act-level, one-shot, zero-data, latent-$W$ instance: $W = \{\Box\bot\}$, $P = P_0$, $E$ supplied by the troll's stated rule, $\Pi = \{\mathrm{cross}, \mathrm{stay}\}$. What the learner adds: $E$ learned from cells, $P(w)$ for *observable* $w$ decided by the invariance test instead of by fiat, and the policy level. The exchange's "I don't see a learning path to it" is answered halfway: for observable $w$ the path is the partition test — exogeneity *earned* from variation; for latent $w$ it remains a design clause.

## Verdicts

[checked by simulation, five seeds, 3000 rounds, 11-policy grid; [policy-level-fdt-learner](../directions/policy-level-fdt-learner.md) §2]

| problem | intended verdict | learner's verdict | match |
|---|---|---|---|
| double lesion, bypass tree, $\delta \in \{0.01, 0.1\}$ | smoke | $q = 1$ in 5/5; $W = \{k\}$ | yes |
| double lesion, overwrite tree (± draw exposed) | smoke | identical | yes |
| Newcomb, Omega reads the policy (threshold), perfect | one-box | $q = 0.6$ in 5/5: box always full, two-boxes 40% — exploits the coarseness; payoff $1000.3 > 1000$ | yes, and better |
| same, accuracy $0.9$ | one-box | one-box side 99.8–100% | yes |
| same, accuracy $0.4$ | two-box | $q \in [0, 0.2]$, 5/5 | yes |
| Newcomb, label-probe Omega | one-box | $q = 1$, payoff $1000$ | yes |
| Newcomb, shared-seed Omega | one-box | $q = 1$ | yes |
| Newcomb, policy-invariant box ($P(\text{full}) = 0.9$) | two-box | $W = \{b\}$; $q \in [0, 0.1]$ | yes |
| Newcomb, Omega reads the act only on exploration-flagged rounds | two-box deliberately | oscillates; one-box side | **no** |
| Newcomb, slow Omega (fill = moving average of past acts) | one-box | $W = \{b\}$; two-boxes; $\approx 450$ vs $1000$ | **no** |
| XOR blackmail | refuse | $W = \{D\}$; refuse 99.8–100% | yes |
| counterfactual mugging ($x = 1, y = 3$) | pay | $q = 1$; payoff $\approx (y - x)/2$ | yes |
| 5-and-10 | take 10 | $q = 1$ | yes |
| Troll Bridge, fallible troll (5% spurious) | cross | $q = 1$; payoff $\approx 9$ | yes |
| TB($\theta = 0.1$) | cross | $q = 1$; payoff $\approx 8$ | yes |
| stricter troll, neutral prior / pessimistic prior | cross / trap | crosses / never crosses | as predicted |

In the double lesion the learner is neither the doc's recency nor its cumulative learner but policy-indexed, and its verdict is grip- and memory-independent because the policy value is affine (`double-lesion-dynamics`). Against a threshold-reading Omega it sits at the smallest grid point above the threshold and collects more than a pure one-boxer — correct optimization against a predictor that reads a coarse feature of the policy.

## The Löbian argument at the policy level

Löb needs: $\Box(\pi_t = \mathrm{cross} \to \mathrm{bad}) \to (\pi_t = \mathrm{cross} \to \mathrm{bad})$, proved by "suppose the hypothesis; suppose the agent adopts cross; *examine the agent* — the only way it adopts cross given the hypothesis is a misfire, i.e. $\mathrm{Incon}$; so bad." For this learner the "examine the agent" step fails [derived]: its adoption of cross is the event $\mathrm{cf}_t(\mathrm{cross}) > \mathrm{cf}_t(\mathrm{stay})$, and $\mathrm{cf}_t$ is a function of $(P_t, E_t)$, which are functions of data and admitted proofs about $E$ and $P(w)$. The hypothesis is a composite sentence; it changes neither. So under the hypothesis the agent adopts cross iff it would have anyway, adopting cross does not imply misfire, and Löb's antecedent is not established — as it must be, since in the consistent world the agent crosses and collects 10, making the sentence false and (the theory sound) unprovable.

**Relocation alone does not save EDT** [derived]. Policy-level EDT, $\mathrm{cf}_{\mathrm{EDT}}(\pi) := E[U \mid \pi_t = \pi] = \sum_w P(w \mid \pi) E(\pi, w)$, agrees with the learner on the double lesion, Newcomb, XOR and the mugging — there $P(w \mid \pi) = P(w)$ for the exogenous variables and the responsive ones are inside $E$. In Troll Bridge the composite theorem asserts $P(\mathrm{Incon} \mid \pi = \mathrm{cross}) = 1$; policy-level EDT, being T-respecting, adopts it, and Lemma 8 runs with "$\pi_t = \mathrm{cross}$" for $\mathrm{Cross}$. So the policy level buys [scrubbed] — counterfactual mugging and transparent Newcomb become choices made before learning the branch — and no more. Troll Bridge is a fact about the agent's *formula*, invariant under the act/policy relocation.

## Mis-partitions

The learner must learn from its own policy variation which variables respond to policy. It mis-partitions exactly when the environment reads a feature of the agent that is not a coordinate of the policy [checked for two cases; the general statement derived]:

- **An exploration-flag Omega** — reads the act on rounds the learner flags as exploratory (adopted policy ≠ greedy), fills at a base rate otherwise. The flag is a feature of the learner's relation to its policy, not of the policy. The estimates chase each other and the policy oscillates; the verdict is an artifact of the exploration schedule. This is the policy-level echo of [newcomb-correction](newcomb-correction.md) and the 2017 "fair decision problem" clause that exploration-conditioned expectations equal unconditioned ones.
- **A slow Omega** — fills with probability the exponential moving average of past one-boxing. Round-to-round variation is fast relative to Omega's memory, the box looks policy-invariant, it is filed in $W$, the learner two-boxes and the box empties. The exogeneity finding is true at the timescale tested and false at Omega's; identifiability needs a class with lagged dependence and block visitation.

General diagnosis: when the round law is not a function of $(\pi_t, w_t)$ alone — an exploration flag, the agent's own estimate (the stricter troll), the agent's reasons, its source code beyond input–output — no partition is well-defined, and every consistent estimator of the policy's value is schedule-relative. **Policy-fairness** — the round law depends on the agent only through $\pi_t$ — is the policy-level form of the run's hypothesis H and of post 04's fairness clause, and every mis-partition found violates it. In IV terms (`iv-reading-of-decision-problems`): the instrument the learner manipulates is not the variable the environment reads.

## Costs

- **Composite shortcuts.** A bridge that is out as a fact about $E$ (provable from the troll's rule) is respected at once; one that is out only as a fact about the composite — this agent's code always trips the trigger — costs one crossing to learn. The learner trades the whole class of composite theorems for immunity to the Löbian one, and pays wherever a composite theorem was true and cheap.
- **Traps.** VOI opens a door iff the information value exceeds the expected catastrophe; the no-traps assumption is the price of every convergence statement (post 13; the Scary Door of post 07).
- **Determinism in the limit.** As exploration vanishes the learner sits at $\pi^\ast$ with a frozen $E$ and a frozen partition, correct iff the environment is stationary. In a regime-switch check its greedy verdict first moved 4400–6100 rounds after the switch [checked]. This is the exchange's "inherited from bounded predecessors' randomization" made concrete, and the doc's moral two applies to the *shadow* even where it does not apply to the verdict.
- **Definition 10 is only partly the right shadow** [derived]: it matches for uniform, label-read, independently-redrawn exploration; it does not express the learner's non-uniform exploration ray, the shared-seed predictor, or the fact that what is frozen is the response function $E$ — v2's $\mathrm{cf}_s$ — rather than a state. Proposal: a test-sequence limit along the learner's own ray with $\mathrm{cf}_s$ at null policies pinned to the inherited $E$ (`next-coherent-care`).

## Conjecture F

**Setting.** Rounds $t = 1, 2, \dots$; finite $\Pi$; round law $F(\pi_t, w_t)$ with $w_t$ i.i.d. over a finite observable exogenous set and possibly one fixed latent $w_0$ ($\mathrm{Incon}$); bounded payoffs; policy-fairness; discount $\gamma \to 1$; no-trap belief; a visitation hypothesis (the VOI rule adopts every policy infinitely often while posterior disagreement about its value exceeds any fixed threshold).

**Positive half** [guess; parts marked]. Almost surely: (i) $E_t(\pi, \cdot) \to F(\pi, \cdot)$ on $\Pi$ — provable (frequency convergence on infinitely-visited cells; for a logical-inductor implementation, calibration on an efficiently computable subsequence); (ii) the partition converges to the true one — provable from (i) and the test's Bayes-factor asymptotics; (iii) $\pi_t = \pi^\ast := \arg\max_\pi \mathbb{E}_{w}[F(\pi, w)]$ for all but finitely many rounds — the statistical part is a bandit-over-policies result, the *VOI* part is exactly the result post 13 ll. 84–86 asks for and does not have; (iv) $\mathrm{cf}_t(\pi) - E_t[U \mid \pi_t = \pi] \to 0$ — the FDT property, self-vindicating, provable from (i)–(ii); (v) for every $t$, $T \nvdash (\pi_t = \mathrm{cross} \to \Box\bot)$ — a syntactic fact about the code, Proposition 10 iterated, requiring the trigger to be a fact about $E$ and not about the agent's estimate.

**Negative half** [reconstructed from post 11 l. 172 and the doc's §7]. A proof-respecting-conditional learner — any rule with $\mathrm{cf}(\pi) = E[U \mid \pi_t = \pi]$ whose $P$ respects the theory — has a round after which the Löbian proof for that round sets $P_t(\Box\bot \mid \pi_t = \mathrm{cross}) = 1$, so it crosses only on forced-exploration rounds (which the exploring-agent troll punishes) or never, for linear regret; its record of earlier safe crossings does not help. The existence of that round is post 11's omitted proof; the needed fixed point between proof length and the round-$n$ agent's search bound is the step the doc's fixed-$M$ paragraph shows is not automatic (Löb fails for bounded provability). Recorded as a gap, not as evidence against.

**Open.** The VOI-exploration result; identifiability under lags; the bounded-proof fixed point; whether (v) survives a troll that reads the *statistics* of the agent's estimate rather than a theorem (the 2020 journal's "unjustified crossing" troll — expected to convert the theorem into a prior-dependent trap, [troll-variants](troll-variants.md)).
