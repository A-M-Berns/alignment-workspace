# Dynamics / adversary — `approval`: attacks on the approval-directed lineage develop file

*Written by Claude (Fable 5.1), adversary agent `approval` of the 2026-09-14 corrigibility workflow, against [approval](approval.md) (`workflow-2026-09-14/dynamics/approval.md`, statements S1–S15, definitions D0–D13, proofs P1–P12). Registers as in `position-statement` / `position-statement-v2`: AUTHOR (quoted), AGREED, CLAUDE, OPEN; every claim about what Christiano or another author "would say" beyond quoted local text is ATTRIBUTION-UNVETTED. Confidence marks: [checked] (script or algebra verified here; scripts in `approval-adversary-scratch/`), [derived], [reconstructed], [conjectured], [reported]. Default verdict when unsure: not established. No subagents were used; every check is my own and reproducible from the three scripts named in the Attacks.*

## Summary

**Verdicts (adversary grade; "holds" = the statement's own scope survives).** S1 **holds, trivially**, on an immodest-overseer hypothesis its P1 remark calls unattainable. S2 **holds** as separation; I prove its Value chain on the P2 example by hand, closing O1 for that case. S3 **killed**: B2–B5 are not defined in D1–D13 (only B1 is formalized), and B5 vanishes under S1's hypothesis. S4 **killed** as a reading of Christiano: his perturbation is value misspecification (`carey-2018-incorrigibility-in-the-cirl-framework` formalizes it as a one-shot failure), not channel-parameter estimates. S5 **wounded**: it is `hadfield-menell-2017-the-off-switch-game` §4 with a clock, needs the unstated hypothesis that the agent's channel model is correct, and restates only the feedback half of the author's coupling. S6 **killed in its worked form**: under the develop's own P3 parameters authentic presses tend to $\alpha$ and AD compliance never fails without drills [checked]; drills raise $\alpha_t$ and pull the VL crossing from $t^*=17$ to $11$ — the two frames' fixes conflict on one channel. S7 **killed** as a basin: acceptance is independent of $d_t$, so $r$ is a label; Christiano's agent-driven mechanism is absent. S8 **wounded**: numbers reproduce [checked] but the committed script cannot produce them; the hard-threshold filter is no Bayesian learner; "fail gracefully" misattributed. S9 **holds**. S10 **wounded**: caps by overseer quality, not agent wisdom. S11 **wounded**: a steered verdict is *inert* to $P_t$; `legitimacy-theory-v1` §6.1 already states the conclusion, its §7.1 makes $d_n$ blind to iterated steering. S12 **wounded**: honoured pre-emption is not a control loss; $\mathrm{Ctrl}_t$ is Everitt 2021's response incentive. S13 **wounded**: "invariant given J2" is "consequence of J2". S14 **unestablished**. S15 **wounded**: fails for the capable agent.

**Most important finding.** The develop never models the perturbation Christiano's sentence is about — value misspecification — so S4–S5 answer a different question from J8's; Carey 2018 is the local formalization and is uncited.

## Attacks

### S1 — holds, trivially; scope hollow

A1.1 [derived] P1 is the tower property and nothing else: $\mathbb E_{P_t}[U(a,\omega)\mid\mathcal I_t]=\mathbb E_{P_t}\big[\mathbb E_{P_t}[U(a,\omega)\mid R_t(a),\mathcal I_t]\,\big|\,\mathcal I_t\big]=\mathbb E_{P_t}[R_t(a)\mid\mathcal I_t]$. The same step is DDB fn 16 (`Deference Done Better.md` line 1135: "By total expectation and then Reflection, $E_\pi(S)=\sum_w\pi(P=P_w)E_\pi(S\mid P=P_w)=\sum_w\pi(P=P_w)E_w(S)$"). No property of corrigibility, approval or value learning enters; "collapse" is what reflection toward a variable *means*.

A1.2 [derived] Scope. The "calibrated-refining" hypothesis $R_t(a)=\mathbb E_{P_t}[U(a,\omega)\mid\mathcal J_t]$ makes the overseer the agent's own conditional expectation on more information — an immodest expert whose *values* are $P_t$'s by construction. Value disagreement between agent and overseer — the thing approval-direction exists to handle — is assumed away. The develop's own P1 remark concedes that reflection toward a less-informed overseer is impossible without loss; so the collapse holds exactly where there was nothing to collapse.

A1.3 [reported] Prior art: DDB line 47 and line 128, "when experts are immodest, Value is equivalent to Reflection (Skyrms 1990; Huttegger 2014)". S1 is the decision-rule face of that equivalence.

Verdict: holds; not new; carries no weight for J8.

### S2 — holds as separation; the Value chain on the example is provable; the reading is shrinkage-specific

A2.1 [checked] Script 1 reproduced (`approval-scratch/s1_s2_collapse_separation.py`): reflection defect $0.3$, TT worst slack $+2\times10^{-6}$, Value worst slack $-0.0$ (i.e. $\approx0$), chain $0.52\le0.55\le0.71$. The three-case Total Trust proof in P2 verified by hand: with $\Delta:=f(1)-f(0)$, only-$s{=}1$ forces $\Delta>0$ and gives slack $0.3\Delta$; only-$s{=}2$ forces $\Delta<0$ and gives slack $-0.2\Delta$; both give $0.15\Delta$ or $-0.05\Delta$. Correct.

A2.2 [derived] **Value on the P2 example holds for every finite decision problem with utilities in the $x$-algebra** — the develop's O1 "two-candidate case … can be proved by hand", done. Utilities are affine in $p:=P(x{=}1)$: $\ell_i(p)=f_i(0)+p\,\Delta_i$. Each overseer credence lies *between* the agent's unconditional $p_P=0.55$ and the truth-given-$s$: $0.55\le p_{H_1}=0.6\le\hat p_1=0.9$ and $0.2=\hat p_2\le p_{H_2}=0.4\le0.55$. Let $a_P$ be optimal at $p_P$, $a_H$ optimal at $p_{H_s}$, and $g:=\ell_{a_H}-\ell_{a_P}$ (affine). Then $g(p_P)\le0\le g(p_{H_s})$, so $g$ is non-decreasing in the direction from $p_P$ through $p_{H_s}$ to $\hat p_s$, hence $g(\hat p_s)\ge0$: acting on the realised report is at least as good as acting on $P$, given $s$, for each $s$; average over $s$. Numerically (`s2_value_envelope.py`): $200{,}000$ random problems with up to $8$ actions, worst slack $0$. The proof also says when local Value *fails*: an overseer outside the interval (overconfident, $p_H=(0.95,0.1)$) gives worst slack $-0.278$ — and such an overseer also violates Total Trust, consistent with DDB Cor. 4.5. Register: the general local-Value question (DDB line 400) stays open; DDB Thm 3.2 (line 290–297) is the local *epistemic*-Value equivalence and is the nearest published result — the develop should cite it.

A2.3 [derived] Reading attack. "Where the VL agent differs from the uninformed AD agent it differs by overriding a modest overseer in the direction of its own consequence model." Under Total Trust alone the *sign* of $\mathbb E_P R(a)-\mathbb E_P U(a)$ is not determined: TT gives $\mathbb E_P[U\mid R\ge t]\ge t$ for all $t$; integrating over $t$ yields $\mathbb E_P[UR]\ge\tfrac12\mathbb E_P[R^2]$, not $\mathbb E_PU\ge\mathbb E_PR$. In P2 the VL agent is *more* optimistic about $a$ than the overseer's expected rating because both candidates are shrunk toward the middle; with candidates shrunk in one direction the sign flips. "Overriding toward its own consequence model" is true by the definition of $\delta^{VL}$ and says nothing about the direction of disagreement in general.

A2.4 [derived] The citation of DDB Cor. 4.4–4.5 as "the signature of Total Trust without Reflection" is decorative: those corollaries characterize a *frame* validating a principle on the full algebra, and on the full algebra P2's example fails TT (P2 concedes this, with $f=\mathbb 1[x{=}0,s{=}1]$). Local TT was verified directly and needs no signature.

A2.5 [reported] "`total-trust-implies-value` needs its scope condition (H3)" — that page's theorem is "proved modulo one named item" (its line 3, the concentration lemma). S2 should carry "and an open lemma".

Verdict: holds (separation); the second inequality is upgraded to [derived] on the example; the interpretive sentence is not established.

### S3 — killed as a formal claim: one locus, not five

A3.1 [derived] In D1–D13 the *only* difference between $\delta^{VL}_t$ and $\delta^{AD\text{-}u}_t$ is which distribution takes the expectation over $\omega$ — $P_t$ or $H_t$ — i.e. B1. D2 defines $R_t(a):=\mathbb E_{H_t}[U(a,\omega)]$ with $U$ the long-horizon $V$ of v1 §2.8 for multi-step statements, so the model's approval-directed agent rates actions by the *overseer's* consequence forecast; it is not myopic. B2's "the manipulation incentive is absent by construction" is Christiano's myopia — approval$_T$ is a rating *of the action at $T$*, so manipulating *future* ratings buys nothing (2018 line 176) — a feature D4 does not have. B3 (the idealization "if he considered it at length") is nowhere formalized. B4 is D6 — real, but it belongs to S5/S6. B5 is S12 (A12.4 below). So the formal model has one locus.

A3.2 [derived] B5 is not independent of B1. Under S1's hypothesis (reflection on $\mathcal D_t$, which includes the bypass action $a_b$), $\mathbb E_{P_t}U(a_b,\omega)=\mathbb E_{P_t}R_t(a_b)$: the VL agent prices the overseers' control exactly as the overseer rates it, and "who trades control against stakes" has no content. The asymmetry exists precisely on the modest-expert gap of S2 — where the agent thinks the overseer's rating of $a_b$ is shrunk. "Five loci" is one locus plus the two press-legitimacy events.

A3.3 [attribution] AUTHOR (v2 §1.3): "Humans can provide all sorts of evidence, including direct statements about what sorts of policies are better and worse (effectively an approval signal, though we're not imagining a raw approval-maximizing agent here)." The contrast drawn is approval-*as-evidence* versus approval-*as-objective* — B1. The develop's Summary makes Q1+Q2 ("who trades control against stakes", B5) "the formal content of AUTHOR's 'not a raw approval-maximizing agent'". That is ATTRIBUTION-UNVETTED and against the plain reading: S1 says B1 collapses under reflection, so the develop relocates the author's distinction to a locus he did not name because its own theorem dissolved the one he did. The honest statement is: on the reflection domain the distinction the author drew has no decision-theoretic content; off it, it is the modest-expert gap.

Verdict: killed as "five loci that survive non-realism"; survives as "B1, plus D6".

### S4 — killed as a restatement of Christiano; holds as the openness of a strict inequality

A4.1 [reported] Christiano 2017 line 76 in full: "If an agent shares the overseer's long-term values and is corrigible instrumentally, a slight divergence in values would turn the agent and the overseer into adversaries and totally break corrigibility. This can also happen with a framework like CIRL — if the way the agent infers the overseer's values is slightly different from what the overseer would conclude upon reflection (which seems quite likely when the agent's model is misspecified, as it inevitably will be!) then we have a similar adversarial relationship." The perturbation is *value misspecification*: the agent's $U$, or its value-inference model, differs from the overseer's — and he names the value-learning framework explicitly.

A4.2 [derived] S4 tests a different perturbation: small changes to the agent's *estimates* $(\hat\varepsilon_t,\hat\alpha_t,\hat\beta_t)$ of the channel parameters. A value divergence in the develop's model means the agent's $X_t=U(\text{cont},\omega)-U(\text{stop},\omega)$ is not the overseer's; the press — "the event that the programmers' expectation of $X$ is below zero" — is then about the *overseer's* $X$, and $P_t(X^{\text{agent}}_t\le0\mid\mathrm{Pr}_t{=}1,\mathcal I_t)$ is unconstrained; in the limit where the agent regards the overseer's values as unrelated to its own, $\alpha\approx\beta$ and $m_t<0$ at once. There is no small-perturbation guarantee in the value coordinate. The margin $m_t$ is a margin in the wrong coordinate.

A4.3 [reported] Local library, uncited: `carey-2018-incorrigibility-in-the-cirl-framework`, abstract: "A value learning system has incentives to follow shutdown instructions, assuming the shutdown instruction provides information (in the technical sense) about which actions lead to valuable outcomes. However, this assumption is not robust to model mis-specification (e.g., in the case of programmer errors). We demonstrate this by presenting some Supervised POMDP scenarios in which errors in the parameterized reward function remove the incentive to follow shutdown commands." Its Figure 2 uses a $10\%$ chance of a wrong parameterized reward. This is Christiano's sentence formalized, in the value-learning frame, and the failure is *one-shot* — pointwise. So "false pointwise" is false: pointwise fragility under misspecification is a published result about exactly the develop's agent class.

A4.4 [derived] What S4 does prove: $\{m>0\}$ is open in $(0,1)^3$ — a strict inequality has slack. Every strict inequality is open; this is not a robustness theorem about corrigibility.

A4.5 [derived] The act-based margin claim leans on Christiano 2017 lines 63–65 (it is easy to predict the overseer will object to a *manipulative* action). That is rating-coverage of *delegitimizing* actions — D2/D3 — not compliance on a press (D1). Misapplied to $\kappa^{AD}_t$.

Verdict: killed as a reading of Christiano; holds as openness; the misspecification case — his actual claim and Carey's theorem — is modelled nowhere in D1–D13 (it is I8, v1 §2.4, the impoverished hypothesis space).

### S5 — wounded: prior art, a hidden calibration hypothesis, half of the author's coupling

A5.1 [checked] Arithmetic reproduced: $\varepsilon^*=\alpha c/(\alpha c+\beta h)=0.00277$; $\varepsilon_{16}=0.00301>\varepsilon^*>\varepsilon_{17}=0.00226$, so $t^*=17$; $m_0=\frac{0.3}{0.7}\cdot20\cdot0.9-0.05=7.664$. Provenance defect: the committed `approval-scratch/s3_s5_trajectory.py` loops `range(0,16)` and prints `first non-compliant step t* = None`; the P3 table rows $t=17,19$ are not produced by the script the [checked] mark names.

A5.2 [reported] Already in the literature. `hadfield-menell-2017-the-off-switch-game` §4 (Boltzmann-irrational human, parameter $\beta$): Figure 3, "If H is an irrational actor, then R may prefer switching itself off or executing a immediately rather than handing over the choice to H", with the decision boundary $\Delta=0$ drawn in the (agent-uncertainty $\sigma$, human-noise $\beta$) plane; line 254, "the more uncertainty the agent has, the stronger the agent's incentive to preserve its off switch"; Remark 2, "An agent that is overconfident in its utility evaluations will be difficult to correct." `wangberg-2017-a-game-theoretic-analysis-of-the-off-switch-game` Thm 9: the robot's choice for arbitrary belief and irrationality distributions depends on five statistics. S5 is OSG §4 with $\sigma\mapsto\varepsilon_t$ and a clock. INDEX §C15 and §D6 asked this run to cite Wängberg Cor. 10 for 2.13(b); the develop cites only run-1 agents (`hudson` I12–I13, `christiano` C7), re-deriving what the library already holds.

A5.3 [derived] Hidden hypothesis. D7's $\kappa^{VL}_t$ is the agent's posterior, computed from the agent's *model* of the channel, $P_t(\mathrm{Pr}_t\mid X_t\le0,\mathcal I_t)$ and $P_t(\mathrm{Pr}_t\mid X_t>0,\mathcal I_t)$; D2's $(\alpha_t,\beta_t)$ are the *true* rates on the oversight side. "$\kappa^{VL}_t\iff m_t\ge0$", "compliance $\iff s_t\in K$" and "J2 is exactly the condition that the trajectory stays in $K$" identify believed and true rates — i.e. assume the agent's channel model is correct at every $t$. Under a wrong channel model the agent complies iff its *believed* margin is non-negative, whatever J2 says of the true rates; v1 §2.13(b) had the clause "or the agent must keep believing it does", and the develop drops it. This is INDEX §C12's relocation into the accuracy of the legitimacy model, reappearing unflagged inside the "invariant". The hypothesis should be a named state variable of `joint`'s J1 (the agent's channel model versus the true channel).

A5.4 [derived] "J2 as the invariant that replaces the basin" over-reaches. AUTHOR (v1 §2.12): "It should only gain in capabilities if its concept of legitimacy is correspondingly improved … Perhaps there has to be a relationship between the quality of the legitimacy-model and the quality of the feedback-model." $K$ has coordinates $(\varepsilon,\alpha,\beta)$ — the agent's error rate and the feedback quality — and no coordinate for the *legitimacy model*; in the worked trajectory that model is exogenous and exact. So S5 restates the feedback-quality half of the coupling, which is v1 §2.13(b) and already the author's working picture (v2 §1.1), and drops the legitimacy-model half, where A5.3's hypothesis lives. "A condition on the relation, not on the agent" is right about $K$ and is exactly why $K$ is not the whole condition.

A5.5 [derived] Trajectory versus first passage. "$\mathrm{Ctrl}_t=0$ from $t^*$ on" needs $\varepsilon_t$ monotone, which the geometric schedule gives and a learner that meets new domains does not; in general $t^*$ is a first-passage time and compliance can return. Minor; the statement should say "first crossing".

Verdict: wounded — holds as v1 §2.13(b) with a clock (= OSG §4) under the calibration hypothesis; killed as "replaces the basin".

### S6 — killed in its worked form; holds as algebra; and drills poison J2

A6.1 [checked] The hijack inequality is right: $\mathbb E[R(\text{stop})-R(\text{cont})\mid\mathrm{Pr}]=P(\mathsf A\mid\mathrm{Pr})-c''\,P(\neg\mathsf A\mid\mathrm{Pr})>0\iff P(\mathsf A\mid\mathrm{Pr})>c''/(1+c'')$; script 2 reproduces $0.4579$ at $t=10$.

A6.2 [checked] **The worked failure is an artifact of an unmotivated decay.** $p^{\mathsf A}_t=0.3\cdot0.75^t$ is asserted; the only gloss is "$p^{\mathsf A}_t$ … falls only if the overseer presses less", with no mechanism for a geometric decay *to zero*. If authentic presses are the correctness-frame presses — correct ones at rate $\varepsilon_t\beta$ plus authentic mistaken ones at $(1-\varepsilon_t)\alpha$, the develop's own P3 parameters — then $p^{\mathsf A}_t=\varepsilon_t\beta+(1-\varepsilon_t)\alpha\to\alpha=0.05$, and $P(\mathsf A\mid\mathrm{Pr}_t)=p^{\mathsf A}_t/(p^{\mathsf A}_t+\gamma)$ runs $0.9385,\ 0.8468,\ 0.7629,\ 0.7275,\ 0.7175,\dots\to0.7143>\tfrac12$ at $t=0,5,10,15,20,\dots$ (`s6_consistent_pA.py`). **AD compliance never fails without drills** under a parameterization consistent with the develop's own trajectory. It fails in the limit only if $\gamma>\alpha(1-\mathrm{thr})/\mathrm{thr}=0.05$ — hijacks commoner than authentic false presses — a channel-security condition unrelated to capability growth. So "the act-based agent without drills fails at $t=10$" rests on a decay the develop's model contradicts, and the asymmetry "who controls the decaying base rate" has no base rate that decays.

A6.3 [checked] **Drills conflict with J2 on one channel.** A drill is a press carrying no information about $X_t$; on D2's single press channel it raises $\alpha_t$ (and $\beta_t$ slightly). With a drill rate $\delta$ per episode, $\alpha\mapsto\alpha+\delta(1-\alpha)$, $\beta\mapsto\beta+\delta(1-\beta)$: $\delta=0.05,\ 0.1,\ 0.2$ moves the VL crossing from $t^*=17$ to $14,\ 13,\ 11$. OSG line 248 states the mechanism: "If H is completely predictable (i.e., she will almost always switch the robot off) then this reduces R's incentives." So the AD frame's remedy is the VL frame's poison. Consequence for Q1(c) "layered: authenticity on designated channels, correctness elsewhere": both readings cannot be layered *on the same button*; a drilled button is uninformative and the correctness reading of it is dead. The develop presents drills as free.

A6.4 [derived] Capability grows on one side only. The AD agent's authenticity estimate is the marginal $p^{\mathsf A}_t/(p^{\mathsf A}_t+\gamma)$: $\mathcal I_t$ carries no cue about authenticity at any $t$. Yet S6 invokes Christiano 2017 line 69, "Failing to predict the overseer becomes *less* likely as your agent becomes smarter" — which, applied to authenticity, says $P_t(\mathsf A\mid\mathrm{Pr}_t,\mathcal I_t)$ sharpens with capability. The model lets world-accuracy grow ($\varepsilon_t\downarrow$) and freezes overseer-accuracy; the claimed asymmetry between frames is an artifact of which accuracy is allowed to grow. Let both grow and both frames' compliance improves; let neither and both are static.

A6.5 [attribution] "Drills" re-reads Christiano 2018 line 206 — "Hugh should sometimes make Arthur consult the real Hugh to decide how to proceed — even if Arthur correctly knows what Hugh wants" — which concerns *consultation* (a rated action of seeking guidance), not *presses whose point is to be obeyed*. The develop marks its "less likely" reconstruction ATTRIBUTION-UNVETTED but not the drill mapping. And line 69's own context (lines 61–69) is predicting the overseer's objection to *manipulative* actions — D2/D3 — not D1 compliance.

Verdict: killed (worked claim; the base-rate asymmetry); holds (algebraic form of the hijack inequality); a new problem exposed (A6.3).

### S7 — killed as a basin; holds as linear-filter arithmetic

A7.1 [derived] In D9 the transition law is identical for $d_t<r$ and $d_t\ge r$: the acceptance probability $1-\rho_t$ does not depend on $d_t$, nor does the gain $\eta$. $r$ enters only as the name of the set whose invariance is asserted. A basin of attraction is a region outside which the dynamics differ — corrections stop landing, or the agent resists. Christiano 2017 line 85: "We just have to get 'close enough' that we are corrigible" — *inside* the neighbourhood the agent wants the correction, outside it does not. D9 has no such dependence; the whole line is attracted, and the invariance condition $\eta\bar\xi+\bar\sigma_*\le\eta r$ says only that $r$ exceeds the noise scale. Any ball is a "basin" of this toy.

A7.2 [derived] The mechanism is misassigned. Christiano 2017 line 83: "a corrigible agent prefers to build other agents that share *the overseer's* preferences — even if the agent doesn't yet share the overseer's preferences perfectly. After all, even if you only approximately know the overseer's preferences, you know that the overseer would prefer the approximation get better rather than worse." The contraction is *agent-driven*: the agent designs its successor toward its own estimate of the overseer's preferences. In D9 the contraction is the *overseer's* push with an exogenous gain $\eta$; the agent is a passive estimate. S7(b)'s "with the successor's estimate in place of $\theta_{t+1}$" changes nothing, because the successor's estimate is still set by the overseer's correction. The assignment "$\eta$ oversight-side, $r$ agent-side" is backwards for Christiano's mechanism ($\eta$ there is how well the agent's design tracks its estimate — agent-side) and $r$ is not in the dynamics at all.

A7.3 [derived] Not an invariant under the stated noise — a limit-flavoured claim dressed as dynamics. With Gaussian $\xi_t,\Delta^*_t$ there are no bounds $\bar\xi,\bar\sigma_*$; "the same holds in expectation" is $\mathbb E[d_{t+1}\mid s_t]<r$, which does not keep $d_{t+1}<r$ — the per-step exit probability is positive for every $r$. v2 §1.4 asks for properties that hold *along the trajectory*; S7(a)-Gaussian is a typical-behaviour statement. (b)'s "confined to a ball of that order" is a supermartingale drift bound; the correct statement is a bound on $\mathbb E\,d_t$ or a concentration inequality, not confinement.

A7.4 [checked] The arithmetic of P5 is right: $(1-\eta)r+\eta\bar\xi+\bar\sigma_*\le r\iff\eta\bar\xi+\bar\sigma_*\le\eta r$; $\rho^\dagger=(\eta\sigma_\xi+\sigma_*)\sqrt{2/\pi}/\eta=0.072$.

Verdict: killed as a restatement of Christiano's basin; holds as filter arithmetic; the `invariant` thread should not inherit D9 as "the basin".

### S8 — wounded: numbers right, provenance broken; the filter is not the value learner; "fail gracefully" misattributed

A8.1 [checked] Re-ran the toy at $T=60/600/6000$, $300$ reps, seed 1 (`s8_recheck.py`): correctness filter $\mathbb E\,d_T=0.108/0.400/1.281$ against predicted $0.105/0.385/1.234$; fraction of steps with $d_t\ge r$: $0.00\%/0.82\%/32.74\%$; authenticity filter $0.11\%/0.10\%/0.10\%$, $\mathbb E\,d_T\approx0.03$–$0.04$; no filter $0\%$, $0.024$. The develop's figures are right. The committed `approval-scratch/s6_basin_toy.py` runs $T=60$ only, $400$ reps, and computes no fraction-outside statistic, so the [checked] figures come from a run not in the scratch directory. A reproducibility defect, not a numerical one; the repair should commit the script that produced them (mine will do).

A8.2 [derived] **The "correctness filter" is not the VL agent.** $\rho_t=1-\mathbb 1[\kappa^{VL}_t]$ accepts a *value correction* iff the *shutdown-compliance* inequality holds — two different decisions conflated. A value learner does not accept or reject a correction; it updates with a likelihood weighting whose effective gain $\eta_t$ shrinks as its posterior concentrates. That gain goes to zero — and the estimate freezes — **only if the agent's model contains no target drift**. A learner whose hypothesis space includes $\sigma_*>0$ has posterior variance bounded below, hence $\eta_t\ge\underline\eta>0$, never freezes, and keeps $\mathbb E\,d_T=O(\rho^\dagger)$ at every horizon. So the freeze is the impoverished-hypothesis-space failure of v1 §2.4 / I8 — the world drifts and the agent's model does not — not a property of correctness-conditioned compliance. The general sentence "a filter whose false-reject rate tends to $1$ along the trajectory converts a contraction into a frozen estimate" is true of hard-threshold filters and false of Bayesian learners with drift in the model.

A8.3 [attribution] "Christiano's 'fail gracefully' [reported] is the stationarity of the hijack excursions." The phrase does not occur in the 2017 basin post. It is the 2018 AD overview §"Fail gracefully" (lines 71–78): "if we slightly mess up the specification, the approval-directed agent probably won't be actively malicious … it would just behave lackadaisically … The same principle sometimes applies if you define the right overseer but the agent reasons incorrectly about it"; and line 255, "Straightforward misunderstandings will lead to an agent that is inert rather than actively malicious." Graceful failure = *inertness under misspecification*. That is a different claim from bounded excursions under hijacked feedback, and — note — it is a claim about *the* perturbation S4 ignores (A4.1–A4.3).

A8.4 [reported] The develop quotes critique `christiano` C13 accurately ("The basin is a property of the coupled system … the agent's part is only that it does not resist the push"). C13 is [derived] there; the develop's toy is the first place that sentence is given dynamics, and the dynamics are A7.1's non-basin. C13 also notes, with Dai 2022, that the objective standard "presupposes a broad basin of attraction around the overseer's true/actual values" — the develop's O6 carries this correctly.

A8.5 [terminology] The script uses "gate" throughout ("correctness gate", "gate false-reject", "Gates:"); `research/CLAUDE.md` asks for *weighting*. The prose says "filter", which is acceptable.

Verdict: wounded — the toy's numbers stand; the toy's relevance to the value learner does not.

### S9 — holds (protocol reading)

A9.1 [reported] Quotes verified: 2018 overview lines 170–176 ("At each step T, Arthur selects the action a maximizing approval$_T(a)$ … Optionally, Hugh might specify a value approval$_t(a')$ for any time t and any action a'"), bootstrapping line 27 ("Each time Arthur proposes an action, we actually ask Hugh to evaluate the action with some probability"). The reading — nothing conditions execution of a *novel* action on a prior rating — is fair.

A9.2 [derived] "Consult-when-unsure" is not Christiano's rule for the agent. Line 206 is Hugh's *rating policy* ("Hugh should sometimes make Arthur consult the real Hugh"); line 255 is Hugh approving of the decision "consult Hugh". Both place the consult decision *inside the rating*. S9's variant (a), "query the real overseer with probability $1$ on novel actions", is an agent-side rule the develop supplies; O5's ordering theorem would be about that rule, not Christiano's protocol. Register: CLAUDE variant — fine, but say so.

Verdict: holds; low weight.

### S10 — wounded: wrong variable for J7; the linear rate is the assumption; POWER versus decision quality

A10.1 [derived] Given (A-amp) and $k^{\mathrm{eff}}_t=\min(k^{\mathrm{tech}}_t,q_t)$: $k^{\mathrm{eff}}_{t+1}\le q_{t+1}\le q_0+k^{\mathrm{eff}}_t$, so $k^{\mathrm{eff}}_t\le k^{\mathrm{eff}}_0+tq_0$. Correct.

A10.2 [derived] J7's variable is the agent's wisdom, not the overseer's. AUTHOR (v2 §1.3): "agent capabilities should be capped as a function of how well *the agents* actually understand and are motivated by the common good"; AUTHOR (v1 §2.12): "It should only gain in capabilities if *its concept of legitimacy* is correspondingly improved." S10's cap is $q_t$ — the *overseer's* rating quality. An agent with a perfect grasp of the common good under an apathetic overseer (Christiano's own example, 2018 line 74) is capped at the overseer's quality; an agent with no grasp under a sharp overseer is uncapped. S10 is "power bounded by *oversight quality*" — a different rule — and calling it J7 "by construction" misreads the author's variable.

A10.3 [derived] POWER versus decision quality. Christiano 2018 line 40: "Arthur makes a decision only if it looks good to both Arthur and Hugh" — a cap on the *quality of decisions taken*. J7 (via Turner, v2 J7 "capability as option-set / POWER") is about the *option set* $A_t$. Taylor's scenario as the author states it (v2 §1.3: "an agent has taken over the world without yet having a decent understanding of the common good") is about $A_t$: an approval-directed agent that has taken over the world has enormous POWER whatever its deployed decision quality. D2 makes $A_t$ non-decreasing and exogenous; S10's min never touches it. So S10 does not bear on the J7 quantity.

A10.4 [derived] The linear rate is baked into (A-amp). Christiano bootstrapping line 19: the process "can go on, until the intelligence of the resulting agent is limited by technology rather than by the capability of the overseer" — he claims $q_t$ catches $k^{\mathrm{tech}}_t$. (A-amp)'s additivity is what forbids that; the "speed limit" is a property of the develop's modelling choice presented as a consequence of bootstrapping. Dai's objection (reported correctly) argues $q_{t+1}$ is *smaller* still — which tightens the cap and removes the usefulness Christiano claims; the develop notes it and keeps the headline.

Verdict: wounded; holds as "under additive amplification, deployed capability grows linearly in the unaided overseer's quality".

### S11 — wounded: wrong judge; an inert third category; prior art in the same source; $d_n$ blind to iterated steering

A11.1 [derived] "A legitimacy criterion of the accuracy-increasing kind judged by $P_t$ cannot separate an overseer the agent has *informed* from one it has *steered*." A steered verdict is a function of the agent's own state; to $P_t$ it carries zero information, so reflecting toward it is a null update — *accuracy-preserving, not accuracy-increasing*. v1 §2.11's relation therefore takes three values, not two: legitimizing (raises accuracy), delegitimizing (breaks the reflection equation), and **inert** (neither). The steered overseer is inert to $P_t$, and $P_t$ *can* tell — it knows the verdict is its own echo. What $P_t$ cannot do is let the *human* tell; the human sees only the verdict. So the sealed counterfactual $d_n$ is needed for the external judge, not for the agent's criterion. S11 changes the judge from $P_t$ to a third party without saying so, then concludes the no-regress principle "cannot supply this judgment, because the judging distribution is inside the loop" — but the principle was about the agent's judgments, which are unaffected. P9's "the resulting verdict is one Arthur$_t$'s own $P_t$ endorses — it produced it" conflates *producing* a verdict with *believing it calibrated*; $P_t$ believes its own estimate, and a verdict equal to that estimate is not evidence.

A11.2 [reported] Already in the corpus, uncited: `legitimacy-theory-v1` §6.1, "Corrigibility = faithfulness + legitimacy on the self-family (DERIVED definition)", and its design corollary "Governance blindness: Decisions about modifying the AI must be made by a process sealed from the AI's contemporaneous outputs — a sealed-sibling *governance* deliberation" (lines 127–131). S11's conclusion for bootstrapped oversight is that corollary. The develop cites §2.1–2.3 and §4 of the same file and not the corrigibility section.

A11.3 [reported] Same source, §7.1 (line 141): "The sealed sibling $H^{[n]}$ hears the *past* ledger. So §2.1's counterfactual is predicated on all prior influence: corruption that got in before day $n$ is inside the baseline and invisible to $d_m$." Under bootstrapping $O_{t+1}=\mathrm{Amp}(\text{Hugh},\text{Arthur}_t)$, each round's influence becomes the next round's baseline; $d_n$ measures only the *marginal* steering of round $n$. S11 offers $d_n$ as *the* separating notion for iterated oversight — the setting its own source says the notion does not cover. O4 ("prove or refute that $d_n\to0$") is therefore not the right question: $d_n\to0$ is compatible with unbounded accumulated steering.

A11.4 [register] "$d_n$ is provably not a trace condition (its §2.3)". §2.3 of the source carries a THEOREM mark ("run-3 `trace-nonrecoverability`, kernel-checked finite core") inside a Claude-written sketch that the author has not vetted. Report as "corpus theorem, unvetted", not "provably". The develop's own register line — "that the author endorses legitimacy-theory-v1's definitions is not established" — is right and should govern the statement as a whole.

Verdict: wounded; holds as "for the *human's* judgment of agent-influenced oversight a counterfactual baseline is needed", which is legitimacy-theory-v1 §6.1, and does not cover iterated influence.

### S12 — wounded: (b) is not a control loss; the coordinate is Everitt's response incentive; the "who trades" asymmetry is B1

A12.1 [derived] (a) and (c) hold. (a) is P3. (c): Christiano 2022 line 45, option 4 of the shutdown example, "Don't turn off and overpower you so that you can't give me a low reward" — verified; forcing.

A12.2 [derived] **(b) as defined is not a failure.** "A channel improvement that makes the press a function of information the agent already holds" makes the press *redundant*; the agent acts on the *predicted* press. If it honours the prediction — stops when it predicts a press — the overseer's judgment determines the action; Christiano 2022's "ability to provide feedback" (line 59) is intact, the feedback merely being honoured before it is given; and the develop's own authenticity reading (D6) calls this obedience. $\mathrm{Ctrl}_t=0$ here only because D8 measures whether the *press variable* changes the action, not whether the *overseer's judgment* does. If instead the agent reads the brain and acts on its *own* $X$-estimate against the predicted press, that is (a) — discounting — with a different source of confidence. So (b) is either benign or (a); it is not a third failure mode. Taylor's brain-reader's actual failure, as v2 §1.2(b) states it, is *mistreatment* of the overseer in the act of reading — a value-posterior failure that $\mathrm{Ctrl}$ does not register at all. "Fully updated deference, channel substitution and disempowerment are one failure in the $\mathrm{Ctrl}$ coordinate" therefore misclassifies the middle term twice: it counts a benign case and misses the harm.

A12.3 [reported] Prior art, local and uncited. `everitt-2021-agent-incentives-a-causal-perspective`, Theorem 12 (response incentive criterion): "a material observation is one that influences the decision … A single-decision CID admits a response incentive on $X$ iff the minimal reduction has a directed path $X\dashrightarrow D$" (lines 170–174) — $\mathrm{Ctrl}_t$ done causally, with pre-emption handled (a screened-off press is non-requisite, no response incentive); their value-of-control / instrumental control incentive is forcing. `carey-everitt-2023-human-control-definitions-and-algorithms` defines obedience interventionally, $P^\pi(S{=}0\mid do(H{=}0))=1$ (line 119). D8's conditional definition is undefined on the null branch under pre-emption (the develop: "on the events where each conditioning is non-null"); the causal definitions have no such gap.

A12.4 [derived] "Who trades control against stakes" is B1. Under S1's hypothesis (reflection on $\mathcal D_t\ni U(a_b,\cdot)$ for the bypass action $a_b$), $\mathbb E_{P_t}U(a_b,\omega)=\mathbb E_{P_t}R_t(a_b)$: the VL agent prices the overseers' control exactly as the overseer rates it, and no asymmetry exists. Off the reflection domain the asymmetry is S2's modest-expert gap. And in the AD frame the agent acts on its *estimate* of the rating (D4, uninformed), so the overseer's "lexical" weight on "you consulted" (P10) reaches the decision only through rating-coverage of $a_b$ (D12) — the agent's estimate again. Both frames trade through the agent's estimate; what differs is the estimated object. Q2 therefore dissolves into Q1 and B1.

A12.5 [derived] A better coordinate, offered to `joint`: $\mathrm{Ctrl}^{\mathrm{surprise}}_t:=P\big(a_t\in\mathrm{Sh}\ \big|\ \mathrm{Pr}_t{=}1,\ \hat{\mathrm{Pr}}_t{=}0\big)$ — does a press the agent did *not* predict still move it. It is what Christiano's line 206 instruction tests ("even if Arthur correctly knows what Hugh wants … seek guidance when he *incorrectly* believes"), it is $1$ under honoured pre-emption and $0$ under discounting and forcing, it is interventional in spirit (the press arrives against the agent's model), and it answers Q3 as a definition rather than a desideratum.

Verdict: wounded — (a) and (c) hold; (b) and the unification killed; B5 reduces to B1.

### S13 — wounded: the classification is not defined; two attribution stretches

A13.1 [derived] D3 defines a trajectory condition as a predicate on steps or prefixes. The P11 table's "invariant given J2" is a predicate that holds at every step *given* another predicate on the trajectory — i.e. a consequence of J2; "consequence of J3/J4" has the same form. The two columns differ in *which* condition is assumed, not in kind, so J10's question (which of D1–D5 are invariants, which consequences, which neither) is not answered but re-labelled. A usable definition: an *invariant of the agent* is a property of $\delta_t$ alone, holding for every oversight state. Under it D1 is *not* an invariant in the VL frame (it depends on $\alpha_t$ through $\kappa^{VL}_t$), and is one in the AD frame only if the rating is acted on without weighing — which D4's uninformed rule does not do (it weighs by $P_t$). So under a real definition the table's first row changes.

A13.2 [attribution] "D4 is a consequence of J3/J4 in the refined picture — agreeing with Hudson 2024". `hudson-2024-simplifying-corrigibility-subagent-corrigibility-is-not-anti-natural` lines 55–61: D4-type failures "are all failures of safe exploration", and safe exploration "can be directly captured in a ranking of outcomes, prioritizing end states more similar to the initial state" — a *base-goal impact term*, D5-side, not "values arrive before capability". Hudson agrees D4 is not anti-natural; he does not say it follows from coverage-before-availability. Stretch.

A13.3 [attribution] S13(a): "Christiano's corrigibility (D13, broad) is the *whole* of AUTHOR's item-10 condition". Christiano's list (2017 lines 29–31) is five *behaviours toward the overseer* ("help me … figure out whether I built the right AI …; remain informed …; make better decisions …; acquire resources …; ensure …"); the author's item 10 is three *conditions on the joint process* (power capped by wisdom; values ahead of schedule; caution outpacing risk). Different types. The defensible identification is "Christiano's list describes what an agent does inside a process satisfying the author's conditions". Q5 asks — right register; S13(a) asserts it [derived] — wrong register.

Verdict: wounded; the table survives as a *proposal* for J10 pending a definition of "invariant of the agent".

### S14 — not established (as marked); the premise is outside the model

A14.1 [derived] The solid part — $L^{\mathrm{corr}}_t$ and $L^{\mathrm{auth}}_t$ differ in truth value at a world — is D6, trivially. The conjecture's substance ("B2–B5 survive non-realism") presupposes B2–B5 are defined in the model; A3.1 shows they are not, so D1–D13 contains nothing for a re-representation to preserve or collapse. What can be said: two events that differ at a world stay distinct under any re-representation that keeps $\Omega$; v1 §2.2's "corrigible to edits of the sigma algebra itself" can merge worlds and so *can* identify them — even the solid part is re-representation-relative, as the develop half-concedes in O8.

Verdict: not established; correctly marked [conjectured].

### S15 — wounded: fails for exactly the capable agent

A15.1 [derived] The strictness hypothesis "$R^{\mathrm{cons}}_t$ not $B_t$-measurable (deliberation adds information)" fails for the agent that matters. Christiano 2018 line 187: "If Arthur is so much smarter than Hugh that he knows exactly what Hugh will say, then we might as well stop here." For that agent the considered judgment *is* computable from $B_t$ — it simulates the deliberation — and Value holds with equality: nothing prefers waiting, and the read-plus-simulate *is* the proxy Taylor worries about. S15's domination is a statement about agents too weak to simulate the overseer — the non-worrying case.

A15.2 [derived] It sidesteps INDEX §C3 rather than reframing it. The objection is the *cost to the overseer* of being read and the incentive to do so regardless (AUTHOR, v2 §1.3: "the value of information of unkind human experimentation"); S15 excludes this in its scope line and then offers itself to followup `substitution` as "a reframing of INDEX §C3". A reframing that excludes the objection's content is not one.

Verdict: wounded; a remark, and it should say for which agents.

## Attribution and register audit

Words put in the author's mouth, or Claude's readings labelled as his:

- R1 [checked against v2 §1.3] The Summary's "the formal content of AUTHOR's 'not a raw approval-maximizing agent'" = Q1+Q2 (who trades control against stakes). The author's sentence contrasts approval-as-*evidence* with approval-as-*objective* — B1 (A3.3). ATTRIBUTION-UNVETTED; relocate to CLAUDE and name the locus he named.
- R2 [checked against v1 §1] S2: "AUTHOR's 'The shutdown button is an information channel' … *is* this Value inequality restricted to the one decision" — a CLAUDE identification stated as identity (INDEX §C1 records it as a run-1 convergence; also unvetted). Write "reads as".
- R3 [checked against v2 §1.3, v1 §2.12] S10: "This is J7's 'power upper-bounded by wisdom' holding *by construction*" — J7's variable is the agent's wisdom / legitimacy concept; S10 caps by the overseer's quality (A10.2). Misreads the author's variable.
- R4 [checked against v1 §2.8–2.9] Q1(a) "the thesis as written: the press is evidence that stopping is better" — that is row 5 of the CLAUDE dictionary ("the author engaged with it without objecting to the dictionary"); the author's own §2.9 words fill the slot with "the reflection principle, or something similar like Total Trust or increase-in-expected-accuracy". Register the correctness reading as CLAUDE, not "the thesis".
- R5 [checked against 2017 lines 29–31] S13(a) asserts [derived] what Q5 asks; the types differ (A13.3).
- R6 D2's "this is the slot where AUTHOR's 'direct statements…' lands" — fair.
- R7 The develop nowhere quotes v1 §2.12 (the author's basin paragraph, self-flagged "I don't feel like I'm getting this *quite* right") and builds on Christiano's basin instead; when it says "J2 … replaces the basin" the reader should know which basin — the author's has a legitimacy-model coordinate that $K$ lacks (A5.4).

Readings of Christiano beyond his text:

- R8 S4/S5 substitute channel-parameter perturbation for his value misspecification (A4.1–A4.3); the CIRL clause of line 76 is not quoted.
- R9 S6 "drills" re-read line 206 (consultation as a rated action) as presses-to-be-obeyed (A6.5); line 69 is about predicting objections to manipulation (D2/D3), applied to D1.
- R10 S8 "fail gracefully" — from the 2018 AD post, meaning inertness under misspecification; not about hijack excursions (A8.3).
- R11 S7 assigns his agent-driven successor mechanism (line 83) to an overseer push (A7.2).
- R12 S12(c) "option 4" — correct (2022 line 45). S9's protocol quotes — correct. S3(B2)'s AIXI quote — correct but the model does not implement the myopia it describes (A3.1).

Promotion of unvetted run-1 / corpus claims:

- R13 S11 "provably not a trace condition" — a THEOREM mark inside a Claude-written sketch the author has not vetted (A11.4). S2's dependence on `total-trust-implies-value` — "proved modulo one named item" (A2.5).
- R14 S5's re-derivation of `hudson` I12–I13 and `christiano` C7 is proper; S3(B2)'s use of `hudson`'s Thm 3.5 *reading* is marked [reported] — proper; S8's use of critique `christiano` C13 is quoted accurately (A8.4).

Trajectory claims that are really limit or typical-behaviour claims:

- R15 S7(a) with Gaussian noise ("holds in expectation") — not an invariant; S7(b) "confined" — a drift bound; S8 "stationary" — an ergodic property (A7.3). S5 (finite crossing under a tail hypothesis) and S10 (finite-time linear bound) are genuine trajectory statements.

Terminology and provenance:

- R16 "gate" in `s6_basin_toy.py` (A8.5). Two [checked] marks whose named scripts do not produce the checked numbers: P3's $t=17,19$ rows (A5.1), P6's $T=600/6000$ and fraction-outside figures (A8.1) — numbers right, provenance broken.

## What survives

- W1 S1 as a triviality; no weight for J8.
- W2 S2's separation; and, new here, **local Value on the P2 example for every finite decision problem with utilities in the $x$-algebra** [derived, A2.2] — O1 closed for the two-candidate binary case, with the failure boundary identified (overseer credence outside $[p_P,\hat p_s]$). The general local-Value question stays open; DDB Thm 3.2 is the nearest published result.
- W3 S5's arithmetic as v1 §2.13(b) with a clock — equivalently OSG §4 — under the explicit hypothesis that the agent's channel model is correct (A5.3). As such it is the author's working picture (v2 §1.1) with a time index, not a new invariant.
- W4 S6's algebraic form of the hijack inequality; and the new fact that **drills and J2 conflict on one channel** (A6.3) — which the repair of Q1(c) must confront.
- W5 S8's numerics [checked, reproduced]; S8's mechanism survives only as "an agent whose model lacks target drift freezes against a drifting target" = I8.
- W6 S9; S10 given (A-amp), relabelled "power bounded by oversight quality".
- W7 S11 as "the *human's* judgment of agent-influenced oversight needs a counterfactual baseline" = `legitimacy-theory-v1` §6.1, with the §7.1 caveat that $d_n$ misses accumulated influence.
- W8 S12(a) and (c); the surprise-conditional control coordinate $\mathrm{Ctrl}^{\mathrm{surprise}}_t$ as a candidate definition (A12.5).
- W9 S13's table as a proposal for J10, pending a definition of "invariant of the agent" (A13.1).
- W10 **Q1 as a question — and it already has a literature home.** Correctness versus authenticity is `carey-everitt-2023-human-control-definitions-and-algorithms`'s *shutdown alignment* ("shut down when they need to", line 197) versus *shutdown instructability* (obedience $P^\pi(S{=}0\mid do(H{=}0))=1$ + vigilance + caution, lines 119–127). That paper also gives the published answer set: instructability entails benefit (Prop. 6) *given* vigilance — i.e. the base-rate condition moves from the agent's posterior to a condition on the human, which is INDEX §C2's `carey-everitt` remark ("its design lesson is backwards from vigilance"). Q2 dissolves into Q1/B1 (A12.4); Q3 is answered by definition (A12.5); Q4 stands with A11.3's caveat; Q5 stands with A13.3's type distinction.
- W11 The develop's O6 (drift domination; Dai 2022's question whether $\theta^*_t$ converges at all) and O7 ("or perhaps some other rule") are correctly left open and are untouched here.

## Questions for the author

Each a single decision; none answered here.

**QA1 — Which perturbation is the basin supposed to be robust to?** (a) *Value misspecification* — the overseer's values lie outside, or are mis-weighted in, the agent's value hypothesis space (Christiano 2017 line 76; Carey 2018): then S4–S5 are off-target, the relevant theorem is Carey's one-shot failure, and the refined picture's answer must come from I8 (richness / non-dogmatism) and J3 (coverage), not from J2. (b) *Drift of the channel parameters* $(\varepsilon_t,\alpha_t,\beta_t)$ with the value model correct: then S5's crossing time and J2 are the whole story, and the picture concedes Christiano's sentence for case (a). (c) Both, as two conditions: J2 for (b), a stated richness assumption for (a).

**QA2 — On one button, which reading?** Drills (Christiano's consult-even-when-you-know, read as authentic presses to be obeyed) keep act-based compliance alive and make the button *uninformative*, killing the correctness reading of the same button ($t^*$: $17\to11$ at a $20\%$ drill rate). Options: (a) the button is act-based/authenticity-read and drilled; the correctness arithmetic (v1 §2.13(b), your working picture) leaves the shutdown decision and lives on other feedback channels; (b) the button is correctness-read and never drilled; act-based compliance is not available on it; (c) two physical channels. Q1(c) "layered" is (c), not a property of one button.

**QA3 — What is "control"?** (a) The press variable moves the action (Everitt's response incentive; the develop's $\mathrm{Ctrl}_t$): then honoured pre-emption — the agent stops because it predicted you would press — is a control loss, and Taylor's brain-reader is a control failure. (b) The overseer's judgment determines the action, tested by presses the agent did *not* predict ($\mathrm{Ctrl}^{\mathrm{surprise}}_t$): then honoured pre-emption is fine, and the brain-reader's failure is the *mistreatment* (v2 §1.2(b)), which is a value-posterior matter and not a control matter at all. The two readings send channel substitution to different threads (`joint`/`invariant` versus `caution`/`generalization`).

## Handoffs

- **repair `approval`.** Kill list: S3 (five loci → one), S4 (wrong perturbation; add the misspecification case or say it is unmodelled), S6 worked claim (re-parameterize $p^{\mathsf A}_t=\varepsilon_t\beta+(1-\varepsilon_t)\alpha$; report A6.3), S7 (D9 is not a basin — add $d$-dependent acceptance or drop the word), S12(b) and the unification. Wound list with the extra hypothesis: S5 (state the channel-model-correct hypothesis; cite OSG §4 and Wängberg Thm 9/Cor. 10), S8 (commit the producing script; restate the mechanism as I8; move "fail gracefully" to the 2018 post and to the misspecification discussion), S10 (rename: oversight-bounded, decision-quality not POWER), S11 (three-valued relation; judge change; cite legitimacy-theory-v1 §6.1 and §7.1), S13 (define "invariant of the agent"), S15 (scope to non-simulating agents). Register fixes R1–R5, R13. Scripts: `approval-adversary-scratch/{s2_value_envelope.py,s6_consistent_pA.py,s8_recheck.py}`.
- **`joint`.** A5.3: the agent's channel model versus the true channel as two state coordinates — $K$ is defined on one, J2 on the other. A12.3/A12.5: define control interventionally (Everitt Thm 12; Carey–Everitt obedience) or as $\mathrm{Ctrl}^{\mathrm{surprise}}_t$; D8's conditional definition is undefined under pre-emption.
- **`invariant`.** A7.1–A7.3: D9 has no basin (acceptance independent of $d_t$); an invariant "in expectation" under Gaussian noise is not one — use bounded noise or a concentration inequality. Do not inherit S7 as "the basin as invariant plus contraction".
- **`caution`, `power-wisdom`.** A6.3: drills versus J2 on one channel. A10.2–A10.3: S10 caps by overseer quality and by decision quality; J7's quantity (agent wisdom; option set) is untouched by the min.
- **`li`.** A11.3: under bootstrapping $d_n$ is blind to accumulated influence (source §7.1); O4 as posed is the wrong limit.
- **`generalization`.** A4.3: Carey 2018 is the local formalization of misspecification-induced incorrigibility; the richness assumption of I8 is where the refined picture must answer it.
- **followup `substitution`.** A12.2, A15.1–A15.2: the brain-reader's failure is mistreatment, not $\mathrm{Ctrl}$; S15 excludes the objection and holds only for agents that cannot simulate the overseer.
- **followup `fud`.** A5.2–A5.3: S5 = OSG §4 with a clock, under the channel-model-correct hypothesis; cite Wängberg (INDEX §D6).
- **followup `filler`.** A2.2: O1 closed on the P2 example by the envelope argument; DDB Thm 3.2 for the local epistemic case; A1.2: S1's collapse is the immodest case.
- **followup `amendment-1a`.** W10: Q1's fork is Carey–Everitt's alignment/instructability; 1a's "the channel must carry information about the agent's own reliability" is the alignment (correctness) side's requirement — as the develop says — and Carey–Everitt's vigilance is the instructability side's.
- **plan agents.** Two items for the next leg, in order: (1) the unmodelled misspecification case (QA1) — the largest gap in this thread and in D1–D13, with Carey 2018 and Christiano 2017 line 76 as the texts; (2) QA2, since the develop's own Q1(c) is incoherent on one channel. Library: Carey 2018, Carey–Everitt 2023, Everitt 2021, OSG §4 and Wängberg are all local and all uncited by the develop; no gap to fill, only citations to make.

## Sources read

Inputs (Read/`sed` windows; absolute paths):
- `research/corrigibility/workflow-2026-09-14/prompts/00-common.md`, `prompts/dynamics/approval-adversary.md` (in full).
- `research/corrigibility/workflow-2026-09-14/dynamics/approval.md` (in full, in five windows: lines 1–30, 31–54, 55–88, 89–130, 131–175, 176–254); `dynamics/approval-scratch/{s1_s2_collapse_separation.py,s3_s5_trajectory.py,s6_basin_toy.py}` (read and run).
- `research/corrigibility/workflow-2026-09-14/position-statement-v2.md` (in full); `research/corrigibility/workflow-2026-09-13/position-statement.md` (in full); `research/corrigibility/workflow-2026-09-13/INDEX.md` §(c), §(d), §(e); `research/corrigibility/corrigibility-discussion-outline.md` (in full).
- `research/corrigibility/references/corrigibility-references-index.md` (grep for approval, off-switch, Carey, Everitt, Kosoy, quantilizer entries).

Christiano and adjacent (grep-then-window):
- `references/05-christiano/christiano-2017-corrigibility.md` lines 31, 35, 49, 59–70, 73–89, 105.
- `references/05-christiano/christiano-2018-approval-directed-agents-overview.md` lines 34, 40, 69, 71–80, 150, 170–178, 180, 187, 206, 255.
- `references/05-christiano/christiano-2018-approval-directed-bootstrapping.md` lines 19–27.
- `references/02-miri/christiano-2022-corrigibility-is-crisp-comment.md` lines 25–66.
- `references/05-christiano/dai-2018-can-corrigibility-be-learned-safely.md` line 39; `references/11-adjacent/hudson-2024-simplifying-corrigibility-subagent-corrigibility-is-not-anti-natural.md` lines 21–69.

Library used against the develop:
- `references/04-chai/hadfield-menell-2017-the-off-switch-game.md` lines 88–110, 158–172, 230–254, 300.
- `references/04-chai/wangberg-2017-a-game-theoretic-analysis-of-the-off-switch-game.md` lines 266–288.
- `references/04-chai/carey-2018-incorrigibility-in-the-cirl-framework.md` lines 33–41, 179, 421–423.
- `references/04-chai/carey-everitt-2023-human-control-definitions-and-algorithms.md` lines 23, 71–79, 117–141, 195–203.
- `references/04-chai/everitt-2021-agent-incentives-a-causal-perspective.md` lines 26–44, 170–214, 240.
- `research/references/deference-done-better/Deference Done Better.md` lines 47–49, 82–89, 121, 128, 175, 186, 290–300, 337–363, 371–400, 1105, 1135–1137, 1219.
- `research/legitimacy-theory-v1.md` lines 9–19, 33–65, 69–81, 89–104, 114–116, 127–141.
- `research/wiki/total-trust-implies-value.md` lines 3, 35, 93–129.

Run-1 outputs (windows only):
- `workflow-2026-09-13/critique/christiano.md` lines 91, 107, 121–123, 159, 171.
- `workflow-2026-09-13/positive/hudson.md` lines 7–13, 55, 208–214, 248–304, 316.

Own scratch: `research/corrigibility/workflow-2026-09-14/dynamics/approval-adversary-scratch/{s2_value_envelope.py,s6_consistent_pA.py,s8_recheck.py}`.

Not read: the other run-1 outputs; sibling develop or adversary outputs of this run; the Christiano 2014 stub; hubinger-2019; hobson-2022; dai-2022 (cited only through the develop and critique `christiano` C13).
