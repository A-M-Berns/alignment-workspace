# The updateless self-game: UDT1.0 that believes it is UDT1.1 (T2a–T2d)

*Claude (Smithy, [scrubbed]), 2026-08-24, round 1 of `AGENDA` thread T2. Target: the founding sketch [00-founding-sketches](../notes/00-founding-sketches.md) §3 and the author's proposed theorem in [summer-research-plan-2026--research-ideas-may-2026](../../01-primary/summer-research-plan-2026--research-ideas-may-2026.md) §Updatelessness ("if a UDT1.0 agent $(1-\delta)$-believes that its policy is UDT1.1, then it is $\varepsilon$-optimal"). Every headline carries its register per `conventions-and-status-labels`. Machine artifacts: `updateless_self_game.py` (exact rationals, all assertions pass) and `UpdatelessTrustBound.lean` (KERNEL-CHECKED, output in §5.4). Claims about what the author *means* by the theorem are ATTRIBUTION-UNVETTED throughout; I state what each formalization says and let the readings stand side by side.*

## 0. Headlines

1. **REFUTED (machine-verified).** In the pointwise formalization (§1), the proposed theorem is false, and the loss does not vanish as $\delta\to0$: for every $\delta\in(0,1)$ there is an instance with $|S|=2$, $|A|=2$, $|\operatorname{supp}P_o|=2$, $\pi^*$ the unique optimum, a strict argmax at every situation, the trust bound holding at every situation, and $U(\pi^*)-U(\text{realized})=1$. (§2)
2. **REFUTED (machine-verified).** The founding sketch's claim "two situations cannot do this" is wrong: the exhaustive $|S|=2$ search finds total loss at every $\delta$ on the grid, and the analytic family above is the minimal counterexample. The sketch's error: it assumed the loss requires two deviations; one deviation onto an off-support (or low-conditional-weight) policy suffices. (§3)
3. **PROVED (prose).** Support-1 $P_o$ never produces a strict-argmax loss; with a tie and adversarial tie-breaking it produces total loss. The three zero-probability conventions differ only in tie-breaking; every counterexample here is convention-free. (§3.3)
4. **PROVED (prose).** Fixed-instance margin theorem: for fixed $(U,P_o)$ with $P_o$-margin $m>0$, the realized policy is exactly $\pi^*$ once $\delta<m/U^*$. So the refutation is a statement about the order of quantifiers: $\sup_{(U,P_o)}\text{loss}=1$ at every $\delta$, but each margin-positive instance is exact for small $\delta$. (§4)
5. **PROVED (prose) + KERNEL-CHECKED algebraic core.** The repaired theorem: at any (pure or mixed) self-consistent fixed point where the trust bound holds at one situation, $U(\pi)\ \ge\ U(\pi^*)-\dfrac{\delta}{1-\delta}$. This is tighter than the sketch's $\delta(1+\tfrac1{1-\delta})$, needs no $|A|$ factor even for mixed fixed points, and coincides numerically with the earlier lab's Prop 1 bound. (§5)
6. **Search + CONJECTURE.** The bound is nearly tight: families achieve gap $\delta/(1-\delta+\delta^2)$ (trust bound at one situation) and $\delta$ (trust bound at every situation). Conjecture: these are the extremal values. (§5.5)
7. **REFUTED (machine-verified).** "The self-game always has a pure fixed point" — about 1–2% of random instances have none (plain and floored agents alike). A mixed fixed point exists in the instance examined (exploratory float scan). Mixed existence in general: CONJECTURE. (§6)
8. **PROVED (prose) for pure fixed points; machine-verified.** Every pure fixed point of the floored agent is within $\delta/(1-\delta)$ of optimal; in the Stag Hunt the floor removes the trap exactly when the trap violates the trust bound. Existence is the caveat (item 7). (§7)
9. **PROVED (prose) + machine-verified.** Chosen-vs-enacted, reading C1 (belief = independently corrupted $\pi^*$): margin $m_s>2\,(1-(1-\delta)^{|S|-1})$ at every $s$ ⇒ the chosen policy is exactly $\pi^*$; without margin, a near-tie instance loses $1-\varepsilon$ at every $\delta$. Reading C2 (belief on the chosen policy, independent enactment noise): the enactment noise factors out and the counterexample of item 1 survives. (§8)
10. **INTERPRETATION.** What does the work is self-consistency of the self-model plus the trust bound as equilibrium selection. Belief-in-$\pi^*$ without self-consistency does nothing; the trust bound holds *automatically* under belief-in-$\pi^*$ (Lean `self_evidence`), which is why it cannot rescue the original statement. The earlier lab's R1 model presupposes the conclusion; its R2/Prop 1 bound survives only as the repaired theorem. (§9)

## 1. Definitions

**Decision problem.** Finite situations $S$, finite actions $A$, policies $\pi\in A^S$, utility $U:A^S\to[0,1]$, $\pi^*\in\arg\max U$, $U^*:=U(\pi^*)$. All examples normalize $U^*=1$; the theorems keep $U^*\le1$ explicit.

**UDT1.0 with a belief $\mu\in\Delta(A^S)$.** At situation $s$ the agent plays
$$\pi_\mu(s)\ \in\ \arg\max_{a\in A}\ \mathbb E_{\pi'\sim\mu}\big[U(\pi')\ \big|\ \pi'(s)=a\big].$$
There is no history and no updating; each situation conditions on its own action only. **Zero-probability actions**: an action $a$ with $\mu(\pi'(s)=a)=0$ has an undefined conditional. Default convention: such an action is *unavailable* at $s$. Alternatives considered: assign it value $0$, or the unconditional value $\mathbb E_\mu[U]$. Under all three, a zero-probability action is never a strict argmax ($\mathbb E_\mu[U]$ is a convex combination of the available conditionals), so the conventions differ only when ties are broken; the Python checks this on every instance of the exhaustive search. **Ties**: the realized policy is any element of the product of argmax sets; "strict" means every argmax set is a singleton. The **realized policy** is $\pi_\mu$; the **loss** is $U^*-U(\pi_\mu)$.

**"$(1-\delta)$-believes it is UDT1.1"** (the founding sketch's formalization):
$$\mu\ =\ (1-\delta)\,\delta_{\pi^*}\ +\ \delta\,P_o,\qquad P_o\in\Delta(A^S)\ \text{arbitrary}.$$

**Trust bound at $s$** (the updateless form of $(\mathrm{TB}_h)$ in [audit-revised-theorem-1](../../audit-revised-theorem-1.md) §3):
$$(\mathrm{TB}_s):\qquad \max_{a}\ \mathbb E_{\pi'\sim\mu}\big[U(\pi')\ \big|\ \pi'(s)=a\big]\ \ge\ (1-\delta)\,U(\pi^*).$$

**Self-consistent belief / fixed point** (the repaired setting). The belief is $\mu_\pi=(1-\delta)\delta_\pi+\delta P_o$ with $\pi$ the agent's *own* policy, and $\pi$ is a **pure fixed point** if $\pi(s)\in\arg\max_a\mathbb E_{\mu_\pi}[U(\pi')\mid\pi'(s)=a]$ for every $s$. A **mixed policy** $\sigma=(\sigma_s)_{s\in S}$ has self-hypothesis the product measure $\sigma^{\otimes}$ on $A^S$, belief $\mu_\sigma=(1-\delta)\sigma^{\otimes}+\delta P_o$, value $U(\sigma):=\mathbb E_{\sigma^\otimes}[U]$, and is a fixed point if $\operatorname{supp}\sigma_s\subseteq\arg\max_a\mathbb E_{\mu_\sigma}[U(\pi')\mid\pi'(s)=a]$ for every $s$.

**Floored agent** (the T1b floor, updateless): at $s$, if $\max_a\mathbb E_{\mu}[U\mid\pi'(s)=a]<(1-\delta)U^*$ play $\pi^*(s)$; if $>$ play an argmax; at equality either (mixing allowed). Its fixed points are defined with $\mu=\mu_\pi$ as above.

**Chosen-vs-enacted models** are defined in §8.

## 2. The proposed theorem is false in the pointwise formalization (REFUTED, machine-verified)

**Theorem A.** For every $\delta\in(0,1)$ there exist $S$ with $|S|=2$, $A=\{a,b\}$, $U:A^S\to[0,1]$ with unique maximizer $\pi^*=(a,a)$, $U(\pi^*)=1$, and $P_o$ with $|\operatorname{supp}P_o|=2$, such that under $\mu=(1-\delta)\delta_{\pi^*}+\delta P_o$: the argmax is strict at both situations, $(\mathrm{TB}_s)$ holds at both situations, and the realized policy has $U=0$.

*Proof (exact arithmetic in `updateless_self_game.py` §(ii), every $\delta$ in $\{1/2,1/10,1/100,10^{-6},10^{-9}\}$; the algebra below is for general $\delta$).* Take $U(aa)=1$, $U(ab)=U(ba)=0$, $U(bb)=1-\eta$ with $\eta=\delta/(2(2-\delta))$, and $P_o=\tfrac12\delta_{ab}+\tfrac12\delta_{bb}$. Then $\mu(aa)=1-\delta$, $\mu(ab)=\mu(bb)=\delta/2$, $\mu(ba)=0$.
At $s_0$: $\mathbb E_\mu[U(\pi')\mid\pi'(s_0)=a]=\dfrac{(1-\delta)\cdot1+(\delta/2)\cdot0}{1-\delta+\delta/2}=\dfrac{1-\delta}{1-\delta/2}=1-\dfrac{\delta}{2-\delta}$, while $\mathbb E_\mu[U(\pi')\mid\pi'(s_0)=b]=U(bb)=1-\eta>1-\dfrac{\delta}{2-\delta}$. The agent plays $b$.
At $s_1$: $\mathbb E_\mu[U(\pi')\mid\pi'(s_1)=a]=U(aa)=1$ (only $aa$ plays $a$ there), while $\mathbb E_\mu[U(\pi')\mid\pi'(s_1)=b]=\tfrac12\big(U(ab)+U(bb)\big)=\tfrac12(1-\eta)<1$. The agent plays $a$.
Realized policy $(b,a)$ with $U(ba)=0$; loss $=1$. Trust bound: at $s_0$ the max is $1-\eta\ge1-\delta$; at $s_1$ it is $1$. $\square$

**Mechanism (prose).** Conditioning on the deviation $b$ at $s_0$ discards the self-mass $(1-\delta)\delta_{\pi^*}$ entirely — the "conditioning out of self-trust" / 5&10 phenomenon noted in [planning-to-write-about-coles-theorem](../../01-primary/planning-to-write-about-coles-theorem.md) and predicted as brittleness in [audit-revised-theorem-1](../../audit-revised-theorem-1.md) §6.2 — so the value of $b$ is computed by $P_o$ alone, and $P_o$ puts its $b$-at-$s_0$ mass on a near-optimal policy. Meanwhile the value of $a$ at $s_0$ is *polluted* by the $P_o$-mass on $ab$ (which agrees with $\pi^*$ at $s_0$ and is worthless). At $s_1$ the roles flip: $a$ is supported purely by $\pi^*$. Each action is "explained" by a different hypothesis, and the realized policy $(b,a)$ has belief mass zero. Nothing about $\delta$ being small helps: the deviation at $s_0$ only needs $U(bb)$ within $\delta/(2-\delta)$ of $1$, which is an open condition on $U$.

**The founding sketch's 3-situation instance** ($\pi^*=aaa$, $U(bbb)=0.99$, $P_o=\tfrac12\delta_{bbb}+\tfrac12\delta_{aab}$, $\delta=1/10$) verifies exactly as stated: conditionals $18/19$ vs $99/100$ at $s_1,s_2$ (play $b$), $1$ vs $99/200$ at $s_3$ (play $a$), realized $bba$, $U=0$, trust bound $\{99/100,\,99/100,\,1\}\ge9/10$ at every situation, identical under all three conventions; and the family $\eta=\delta R/(2(1-\delta+\delta R))$ gives loss $1$ down to $\delta=10^{-9}$ (Python §(i)). It is not minimal (§3).

**Register.** REFUTED in the pointwise formalization; the refutation is uniform in $\delta$; and it is robust to the convention for zero-probability actions (every action has positive belief mass at every situation in the witnesses).

**Why the trust bound cannot help (KERNEL-CHECKED as `self_evidence`).** Under $\mu=(1-\delta)\delta_{\pi^*}+\delta P_o$, with $p:=P_o(\pi'(s)=\pi^*(s))$ and $V:=\mathbb E_{P_o}[U\mid\pi'(s)=\pi^*(s)]\in[0,1]$,
$$\mathbb E_{\pi'\sim\mu}\big[U(\pi')\ \big|\ \pi'(s)=\pi^*(s)\big]\ =\ \frac{(1-\delta)U^*+\delta pV}{(1-\delta)+\delta p}\ \ge\ (1-\delta)\,U^*,$$
so $(\mathrm{TB}_s)$ holds at every $s$ for every $P_o$. The trust bound is a consequence of believing in $\pi^*$, not an extra hypothesis — which is exactly [audit-revised-theorem-1](../../audit-revised-theorem-1.md) §6.1's observation, now seen from the other side: it is why the audit's "the one-line bound does not transfer" (§6.2) is the whole story.

## 3. The $|S|=2$ question (REFUTED: two situations suffice)

**3.1 Exhaustive search** (`updateless_self_game.py` §(ii)): $|S|=|A|=2$, $U(\pi^*)=1$, the other three $U$-values in $\{0,\tfrac14,\tfrac12,\tfrac34,1\}$ ($125$ utilities), $P_o$ weights over the four policies in multiples of $\tfrac18$ ($165$ compositions), $\delta\in\{\tfrac1{10},\tfrac14,\tfrac12\}$; $20{,}625$ instances per $\delta$.

| $\delta$ | worst gap, strict argmax everywhere | instances with positive gap | worst gap by $\lvert\operatorname{supp}P_o\rvert$ ($1,2,3,4$) | worst gap, adversarial ties | convention violations |
|---|---|---|---|---|---|
| $1/10$ | $1$ | $896$ | $0,\ 1,\ 1,\ 0$ | $1$ | $0$ |
| $1/4$ | $1$ | $956$ | $0,\ 1,\ 1,\ 1/4$ | $1$ | $0$ |
| $1/2$ | $1$ | $1516$ | $0,\ 1,\ 1,\ 3/4$ | $1$ | $0$ |

Witness at $\delta=1/10$: $U=\{aa{:}1,\ ab{:}0,\ ba{:}0,\ bb{:}1\}$, $P_o=\{ba{:}\tfrac18,\ bb{:}\tfrac78\}$, realized $ab$ — the mirror image of Theorem A's family ($P_o$'s $b$-mass supports $b$ at $s_1$; its $ba$-mass pollutes $a$ at $s_1$; at $s_0$ only $\pi^*$ plays $a$). With $\pi^*$ the *unique* optimum the grid finds total loss at $\delta=1/2$ ($U(bb)=3/4$, $P_o=\{ba{:}\tfrac38,bb{:}\tfrac58\}$) and none at $\delta\le1/4$ — a grid artifact: the deviation needs $U(bb)>\mathbb E_\mu[U\mid\pi'(s_0)=a]\ge\frac{1-\delta}{1-\delta+7\delta/8}=\frac{24}{31}$ at $\delta=\tfrac14$, above the grid's $\tfrac34$. The analytic family of Theorem A (finer $U(bb)$) has a unique optimum at every $\delta$. Convention violations $=0$ means: at every instance and situation, the default convention's argmax set is contained in the other two conventions' argmax sets, and no zero-probability action is ever a strict argmax under them.

**3.2 What the sketch got wrong.** [00-founding-sketches](../notes/00-founding-sketches.md) §3 argued: "with $|S|=2$ any near-optimal supporter of a deviation at $s_1$ agrees with $\pi^*$ at $s_2$ and hence supports agreement there…, blocking the second deviation". Both halves fail. The supporter $bb$ of the deviation at $s_0$ *disagrees* with $\pi^*$ at $s_1$ — nothing forces agreement; and no second deviation is needed, because the loss comes from landing on the off-support policy $(b,a)$, not from deviating twice. A single deviation is always enough when the realized policy has small conditional weight under $\mu$.

**3.3 Support one (PROVED, prose).** If $P_o=\delta_{\pi_o}$: at $s$ with $\pi_o(s)=\pi^*(s)$ only one action is available; at $s$ with $\pi_o(s)\ne\pi^*(s)$, $\mathbb E_\mu[U\mid\pi'(s)=\pi^*(s)]=U^*$ and $\mathbb E_\mu[U\mid\pi'(s)=\pi_o(s)]=U(\pi_o)\le U^*$. So with strict argmaxes the realized policy is $\pi^*$ (loss $0$); the only way to lose is a tie $U(\pi_o)=U^*$, and then adversarial tie-breaking on two situations where $\pi_o\ne\pi^*$ realizes a mixed-up policy with arbitrary $U$ (e.g. $U(aa)=U(bb)=1$, $U(ab)=U(ba)=0$, $P_o=\delta_{bb}$: argmax sets $\{a,b\}$ at both situations, adversarial realized $ab$ with $U=0$; uniform tie-breaking gives expected $U=\tfrac12$). Verified in Python §(iii). Hence the minimal counterexample without ties has $|\operatorname{supp}P_o|=2$, and $2$ is also the minimum found by the random search at every $\delta$.

**3.4 Random search, $|S|=3$** (Python §(iii), $6{,}000$ instances per $\delta$, $U$ on the grid $\tfrac18\mathbb Z\cap[0,1]\cup\{1-\delta/4,1-\delta/8\}$, $|\operatorname{supp}P_o|\le4$): worst strict-argmax gap $=1$ at every $\delta\in\{\tfrac12,\tfrac14,\tfrac1{10},\tfrac1{100},\tfrac1{1000},10^{-6}\}$, also with $\pi^*$ the unique optimum; smallest support with gap $\ge\tfrac12$ is $2$ at every $\delta$; the trust bound holds at every situation in every witness. **The worst gap does not scale with $\delta$ at all; it is exactly $1$ for every $\delta>0$.**

## 4. The fixed-instance margin theorem (PROVED, prose) — the refutation as a quantifier-order fact

Define the **$P_o$-margin** of an instance: $m:=\min\big\{U^*-\mathbb E_{P_o}[U(\pi')\mid\pi'(s)=a']\ :\ s\in S,\ a'\ne\pi^*(s),\ P_o(\pi'(s)=a')>0\big\}$ (and $m:=+\infty$ if no such $(s,a')$).

**Theorem B.** If $m>0$ and $\delta<m/U^*$, then under $\mu=(1-\delta)\delta_{\pi^*}+\delta P_o$ the realized policy is exactly $\pi^*$ (strict argmax at every situation).

*Proof.* At $s$: $\mathbb E_\mu[U\mid\pi'(s)=\pi^*(s)]\ge(1-\delta)U^*$ (self-evidence, §2). For available $a'\ne\pi^*(s)$ the conditional is a pure $P_o$-conditional (the self-mass plays $\pi^*(s)$), so $\mathbb E_\mu[U\mid\pi'(s)=a']=\mathbb E_{P_o}[U\mid\pi'(s)=a']\le U^*-m<(1-\delta)U^*$. $\square$

*Converse.* If $m=0$ at $(s,a')$ — i.e. all $P_o$-mass playing $a'$ at $s$ sits on optimal policies — then $a'$ ties $\pi^*(s)$ for every $\delta>0$, and beats it strictly whenever $P_o$ also has mass on a *suboptimal* policy agreeing with $\pi^*$ at $s$. Theorem A's family has $m=0$ ($bb$ is optimal in the $\eta\to0$ limit) or $m=\eta$ with $\eta$ chosen below $\delta/(2-\delta)$; either way the instance is tuned to $\delta$. Python §(iii) checks Theorem B on $10{,}191$ (instance, $\delta$) pairs and exhibits $476$ margin-zero instances that deviate or tie at $\delta=10^{-6}$.

**Reading.** "$\varepsilon(\delta)\to0$ uniformly over instances" is REFUTED (Theorem A); "for each instance with positive $P_o$-margin, $\varepsilon=0$ for $\delta$ small enough" is PROVED (Theorem B). The proposed theorem, read as a uniform statement, is false; read with an instance-dependent margin, it is true but is then a margin theorem rather than a belief theorem. Which reading is intended is ATTRIBUTION-UNVETTED.

## 5. The repaired theorem (PROVED prose; algebraic core KERNEL-CHECKED)

**Theorem C (pure fixed points).** Let $\pi$ be a pure fixed point of the self-consistent agent with belief $\mu_\pi=(1-\delta)\delta_\pi+\delta P_o$, $0\le\delta<1$, and suppose $(\mathrm{TB}_{s_0})$ holds at some situation $s_0$. Write $p:=P_o(\pi'(s_0)=\pi(s_0))$ and $V_o:=\mathbb E_{P_o}[U(\pi')\mid\pi'(s_0)=\pi(s_0)]\in[0,1]$ (anything in $[0,1]$ if $p=0$). Then
$$U(\pi)\ \ge\ U(\pi^*)\,\big((1-\delta)+\delta p\big)\ -\ \frac{\delta p}{1-\delta}\qquad\text{and hence}\qquad U(\pi)\ \ge\ U(\pi^*)-\frac{\delta}{1-\delta}.$$

*Proof.* Since $\pi(s_0)$ is an argmax, $(\mathrm{TB}_{s_0})$ says $(1-\delta)U^*\le\mathbb E_{\mu_\pi}[U(\pi')\mid\pi'(s_0)=\pi(s_0)]$. The self-posterior identity (the only computation): the policies playing $\pi(s_0)$ at $s_0$ are $\pi$ itself, with $\mu_\pi$-mass $(1-\delta)+\delta P_o(\pi)$, and the rest of $P_o$'s $\pi(s_0)$-mass; collecting,
$$\mathbb E_{\pi'\sim\mu_\pi}\big[U(\pi')\ \big|\ \pi'(s_0)=\pi(s_0)\big]\ =\ \frac{(1-\delta)\,U(\pi)+\delta\,p\,V_o}{(1-\delta)+\delta p}.$$
Clearing the (positive) denominator: $(1-\delta)U^*\big((1-\delta)+\delta p\big)\le(1-\delta)U(\pi)+\delta pV_o\le(1-\delta)U(\pi)+\delta p$. Divide by $1-\delta>0$: the $p$-dependent bound. It is affine in $p$ with slope $\delta\big(U^*-\tfrac1{1-\delta}\big)\le0$, so its minimum over $p\in[0,1]$ is at $p=1$: $U^*-\delta/(1-\delta)$. $\square$

The Lean file proves exactly the two displayed inequalities from the cleared-denominator hypothesis (`trust_bound_main`, `trust_bound_clean`), plus the sketch's weaker form $U^*-\delta(1+\tfrac1{1-\delta})$ (`trust_bound_sketch`) and the $\delta=0$ corner $U^*\le U(\pi)$ (`exact_of_certain`). Note the improvement over the sketch: the term $U^*(1-\delta+\delta p)\ge U^*-\delta$ was bounded separately there, losing a $\delta$; keeping it affine in $p$ recovers $\delta/(1-\delta)$.

**Theorem C′ (mixed fixed points; PROVED, prose, not in Lean).** Let $\sigma$ be a mixed fixed point (product self-hypothesis, §1) with $(\mathrm{TB}_{s_0})$. Then $U(\sigma)\ge U(\pi^*)-\dfrac{\delta}{1-\delta}$ — the same bound, with no factor $|A|$ or $k$.

*Proof.* For $a\in\operatorname{supp}\sigma_{s_0}$ write $q_a:=\sigma_{s_0}(a)>0$, $U_a:=\mathbb E_{\sigma^\otimes}[U(\pi')\mid\pi'(s_0)=a]$ (a product measure conditioned on one coordinate is the product with that coordinate fixed, so $U_a=\mathbb E_{\sigma_{-s_0}^\otimes}[U(a,\pi'_{-s_0})]$), $p_a:=P_o(\pi'(s_0)=a)$, $V_a:=\mathbb E_{P_o}[U\mid\pi'(s_0)=a]$. Then $\mathbb E_{\mu_\sigma}[U(\pi')\mid\pi'(s_0)=a]=\dfrac{(1-\delta)q_aU_a+\delta p_aV_a}{(1-\delta)q_a+\delta p_a}$, and every $a$ in the support attains the maximum, which is $\ge(1-\delta)U^*$ by $(\mathrm{TB}_{s_0})$. Clearing denominators and using $V_a\le1$: $(1-\delta)q_aU_a\ \ge\ (1-\delta)^2U^*q_a-\delta p_a\big(1-(1-\delta)U^*\big)$. Sum over $a\in\operatorname{supp}\sigma_{s_0}$, using $\sum_aq_a=1$, $\sum_aq_aU_a=U(\sigma)$, $\sum_ap_a\le1$ and $1-(1-\delta)U^*\ge0$: $(1-\delta)U(\sigma)\ge(1-\delta)^2U^*-\delta\big(1-(1-\delta)U^*\big)$, i.e. $U(\sigma)\ge U^*-\delta/(1-\delta)$. $\square$

The sketch's "extra factor $k\le|A|$ if $\pi$ randomizes among $k$ ties" is therefore unnecessary: the per-action losses are weighted by $p_a$, and $\sum_ap_a\le1$ absorbs the multiplicity.

**5.1 Without the trust bound: the Stag Hunt trap** (Python §(iv)). $U(SS)=1$, $U(HH)=\tfrac34$, $U(SH)=U(HS)=\tfrac38$ ($b=4$, $c=3$, sum of payoffs over $2b$), $P_o=\tfrac12\delta_{SH}+\tfrac12\delta_{HS}$. Both $SS$ and $HH$ are pure fixed points for *every* $\delta$ (so are the miscoordinated $SH$, $HS$, via ties: at $SH$ both actions at $s_0$ have conditional value $\tfrac38$). $SS$ satisfies the trust bound for every $\delta$. $HH$ violates it iff $\dfrac{(1-\delta)\tfrac34+\tfrac\delta2\cdot\tfrac38}{1-\delta/2}<1-\delta$, i.e. iff $8\delta^2-15\delta+4>0$, i.e. iff $\delta<\dfrac{15-\sqrt{97}}{16}\approx0.322$. The sketch's threshold "$1-\delta>c/b$" ($\delta<\tfrac14$) neglects the $P_o$ term in the conditional; the exact threshold depends on $P_o$. Above the threshold $HH$ satisfies the trust bound, but the bound $U^*-\delta/(1-\delta)\le\tfrac12$ is then satisfied by $U(HH)=\tfrac34$ — the theorem is true and uninformative, as it should be.

**5.2 The counterexample instance as a self-game.** With $P_o=\tfrac12\delta_{bbb}+\tfrac12\delta_{aab}$, $\delta=\tfrac1{10}$: the *only* pure fixed point is $bbb$ ($U=0.99$, trust bound holds, bound $8/9$). Neither $\pi^*=aaa$ nor the original realized policy $bba$ is self-consistent. So the self-consistent agent with the same $P_o$ is within $0.01$ of optimal; the original agent lost everything by believing something false about itself.

**5.3 Random instances** (Python §(iv), $3{,}000$ per $\delta$, $|S|=3$): the bound held at every trust-bound fixed point (Theorem C and the $p$-dependent form, both asserted). Worst observed gaps at trust-bound fixed points: $\tfrac58$ at $\delta=\tfrac12$ (bound $1$), $\tfrac14$ at $\delta=\tfrac14$ (bound $\tfrac13$), $0$ at $\delta\le\tfrac1{10}$ (the $\tfrac18$-grid cannot represent a positive gap below the bound). $\pi^*$ itself fails to be a fixed point in $7$–$18\%$ of instances.

**5.4 Lean: `UpdatelessTrustBound.lean` — KERNEL-CHECKED.** Command: `bash unbounded-embedded/unbounded-embedded-lab/lean/check.sh research/unbounded-embedded/unbounded-embedded-lab/lean/UpdatelessTrustBound.lean`. Exact output (exit code 0, no errors, no warnings, no `sorryAx`):
```
'UpdatelessTrustBound.trust_bound_main' depends on axioms: [propext, Classical.choice, Quot.sound]
'UpdatelessTrustBound.trust_bound_clean' depends on axioms: [propext, Classical.choice, Quot.sound]
'UpdatelessTrustBound.trust_bound_sketch' depends on axioms: [propext, Classical.choice, Quot.sound]
'UpdatelessTrustBound.exact_of_certain' depends on axioms: [propext, Classical.choice, Quot.sound]
'UpdatelessTrustBound.self_evidence' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(A first compile failed only because `ring` was used without `import Mathlib.Tactic.Ring`; the import was added and the second compile is the one above. Lean `v4.27.0`, Mathlib `v4.27.0`, targeted imports only.)

| Lean theorem | informal claim | what it does NOT capture |
|---|---|---|
| `selfCond δ p Vo Uπ` | the self-posterior identity's right-hand side | that it *is* $\mathbb E_{\mu_\pi}[U\mid\pi'(s_0)=\pi(s_0)]$ — a two-line computation above, checked on instances in Python |
| `trust_bound_main` | Theorem C, $p$-dependent form, from $(1-\delta)U^*\le$ `selfCond` | policies, situations, the argmax, the mixture |
| `trust_bound_clean` | Theorem C, $U^*-\delta/(1-\delta)\le U(\pi)$ | same |
| `trust_bound_sketch` | the sketch's weaker $U^*-\delta(1+\tfrac1{1-\delta})$ | same |
| `exact_of_certain` | $\delta=0$: the trust bound is $U^*\le U(\pi)$ | same |
| `self_evidence` | $(1-\delta)U^*\le$ `selfCond δ p Vo U*` for $V_o\ge0$, $U^*\ge0$, $p\le1$ | that this is the conditional of $\pi^*$'s own action (§2) |
| — | existence of fixed points; Theorem C′ (mixed); the floored agent; Theorems A, B, D | not formalized |

Per the Lean honesty caveat of `conventions-and-status-labels`: the kernel certifies the arithmetic from the hypothesis `htb`; it does not certify that a fixed point exists or that `htb` is the right rendering of the trust bound.

**5.5 Tightness (search; CONJECTURE for extremality).** Two exact families (Python §(iv)):
- **T1**, trust bound at $s_0$ only, $|S|=2$: $\pi=(a,b)$, $P_o=(1-\theta)\delta_{aa}+\theta\delta_{ba}$, $U(aa)=1$, $U(ba)=U(bb)=0$, $U(ab)=1-g$, with $g=\theta=\dfrac{\delta}{1-\delta+\delta^2}$. Then $\pi$ is a pure fixed point (tie at $s_1$; strict for $g<\theta$), $(\mathrm{TB}_{s_0})$ holds with equality ($p=1-\theta$, $V_o=1$), and $(\mathrm{TB}_{s_1})$ fails for every $\delta\in(0,1)$ (its max is $1-g$, and $g>\delta$). Gap $\dfrac{\delta}{1-\delta+\delta^2}$ vs bound $\dfrac{\delta}{1-\delta}$: ratio $1-\delta+\delta^2\to1$.
- **T2**, trust bound at every situation, $|S|=3$: $\pi=(a,b,a)$, $P_o=(1-\delta)\delta_{aaa}+\delta\delta_{aab}$, $U(aaa)=1$, $U(aab)=0$, $U(aba)=1-\delta$. Fixed point (with a tie at $s_1$), trust bound everywhere, gap exactly $\delta$.

The obstruction to reaching $\delta/(1-\delta)$: that needs $pV_o\to1$, i.e. $P_o$ concentrated on optimal policies agreeing with $\pi$ at $s_0$; but at any situation where $\pi$ deviates from those policies their action must be made unattractive by polluting $P_o$-mass, which costs either $V_o$ (if the polluters agree with $\pi$ at $s_0$) or $p$ (if they do not); the second option gives T1. **Conjecture:** $\sup$ gap $=\delta/(1-\delta+\delta^2)$ with the trust bound at one situation and $=\delta$ with it at all situations. Not proved.

## 6. Existence of fixed points (REFUTED for pure; CONJECTURE for mixed)

Random search (Python §(iv)–(v)): $52/3000$ instances at $\delta=\tfrac12$, $47$ at $\tfrac14$, $30$ at $\tfrac1{10}$, $21$ at $\tfrac1{100}$ have **no pure fixed point** of the self-consistent agent; on the same instances the floored agent has slightly more ($55$, $59$, $38$, $33$ — the floor can destroy a plain fixed point at which $(\mathrm{TB}_s)$ fails and $\pi(s)\ne\pi^*(s)$); the counts are the same under all three zero-probability conventions. A concrete instance ($\delta=\tfrac1{10}$): $U(aaa)=U(aba)=U(bbb)=1$, $U(aab)=\tfrac34$, $U(bab)=\tfrac12$, $U(baa)=U(bba)=\tfrac38$, $U(abb)=\tfrac18$, $P_o$ uniform on $\{aaa,aba,abb,bbb\}$. At $\pi=aaa$, situation $s_0$ deviates to $b$ ($\mathbb E[U\mid b]=1$ from $bbb$ alone, vs $\mathbb E[U\mid a]=305/312$, polluted by $abb$); at $\pi=baa$, $s_0$ deviates back ($\mathbb E[U\mid a]=17/24$ vs $\mathbb E[U\mid b]=29/74$, now polluted by the self-mass on $baa$). The self-hypothesis makes the payoff of an action depend discontinuously on whether the agent itself plays it — the EDT analogue of the audit's Gap 1.

An exploratory float scan (not a deliverable, so not asserted) finds a **mixed** fixed point of this instance: mix $\approx(0.999,0.001)$ at $s_0$, pure $a$ at $s_1,s_2$, with $U(\sigma)\approx0.9994$ and the trust bound satisfied ($0.978\ge0.9$) — inside Theorem C′'s bound. The sketch's "existence by Kakutani/Nash" is SKETCHED at best: with the default convention the best-response correspondence does not have a closed graph (an action available along a sequence $\sigma^n$ can become unavailable in the limit), so Kakutani does not apply verbatim; with the continuous extension ($\mathbb E_{\mu_\sigma}[U\mid\pi'(s)=a]:=U_a$ when $\sigma_s(a)=0=P_o(\pi'(s)=a)$, the limit as $\sigma_s(a)\downarrow0$) the conditionals are continuous in $\sigma$ and Kakutani should go through. CONJECTURE: mixed fixed points exist for every instance under the continuous extension. Open for round 2.

## 7. The floored agent (PROVED prose for pure fixed points; machine-verified)

**Theorem D.** Every pure fixed point $\pi$ of the floored agent satisfies $U(\pi)\ge U(\pi^*)-\dfrac{\delta}{1-\delta}$.

*Proof.* If at some $s$ the agent is in the argmax branch or in the equality branch playing an argmax action, then $\max_a\mathbb E_{\mu_\pi}[U\mid\pi'(s)=a]\ge(1-\delta)U^*$ and $\pi(s)$ attains it, so Theorem C applies at $s_0=s$. Otherwise every situation plays $\pi^*(s)$, so $\pi=\pi^*$ and the gap is $0$. $\square$

The sketch's contradiction step ("all reset is impossible because then TB holds everywhere") is not needed: all-reset simply means $\pi=\pi^*$, which is fine. The mixed version follows from Theorem C′ in the same way (at any $s$ where some support action is in the argmax branch). Machine checks (Python §(v)): every pure floored fixed point in $12{,}000$ random instances is within the bound; in the Stag Hunt the floor's fixed points are $\{SS\}$ for $\delta\le0.3$ and $\{SS,HH\}$ at $\delta=\tfrac12$ — exactly "$HH$ survives iff it satisfies the trust bound"; on the counterexample instance the floored agent's only pure fixed point is $bbb$.

**Caveat (adversarial).** Theorem D is vacuous on instances without pure fixed points (§6); the floored agent has none there either. "The floored agent is always near-optimal" therefore needs mixed existence, which is CONJECTURE. The floor slightly worsens pure existence (§6: $55$–$33$ vs $52$–$21$ instances without a pure fixed point on the same random instances).

## 8. Chosen versus enacted (two readings; both machine-verified)

The journal line ([2026-03-26](../../03-journals/2026-03-26.md)): "it believes the *chosen* policy = udt 1.1, not the *enacted* policy; it knows that its actions don't always conform to its decision procedure". Two formalizations; which is intended is ATTRIBUTION-UNVETTED.

**Reading C1 — belief about the enacted policy, independent corruption.** $\mu=\bigotimes_{s\in S}\big[(1-\delta)\delta_{\pi^*(s)}+\delta\,\mathrm{Unif}(A\setminus\{\pi^*(s)\})\big]$ on $A^S$; the agent conditions on its *enacted* action. Because $\mu$ is a product, $\mathbb E_{\pi'\sim\mu}[U(\pi')\mid\pi'(s)=a]=\mathbb E_{\pi'_{-s}\sim\mu_{-s}}\big[U(a,\pi'_{-s})\big]$ — the evidential conditional collapses to an interventional one, and the chosen policy is $\arg\max_a$ of that.

**Theorem E (margin; PROVED, prose).** Let $\rho:=1-(1-\delta)^{|S|-1}$ and $m_s:=U(\pi^*)-\max_{a\ne\pi^*(s)}U(a,\pi^*_{-s})$. If $m_s>2\rho$ for every $s$, the chosen policy is exactly $\pi^*$.

*Proof.* $\mu_{-s}(\pi'_{-s}\ne\pi^*_{-s})=\rho$ and $U\in[0,1]$, so $\big|\mathbb E_{\mu_{-s}}[U(a,\pi'_{-s})]-U(a,\pi^*_{-s})\big|\le\rho$ for every $a$. Hence the value of $\pi^*(s)$ is $\ge U^*-\rho>U^*-m_s+\rho\ge$ the value of any $a\ne\pi^*(s)$. $\square$ Since $\rho\le(|S|-1)\delta$, margin $>2(|S|-1)\delta$ suffices — horizon-dependent, as [audit-revised-theorem-1](../../audit-revised-theorem-1.md) §6.2 anticipated; no $|A|$ dependence. Verified on $1{,}138$ random margin-satisfying instances (Python §(vi)).

**Near-tie counterexample (machine-verified).** $|S|=3$, $U\equiv1$ except $U(aab)=0$ and $U(bba)=\varepsilon$; base ties $U(baa)=U(aba)=U(aaa)=1$. At $s_0$: $\mathbb E[U(b,\cdot)]-\mathbb E[U(a,\cdot)]=\delta(1-\delta)\varepsilon>0$ (playing $b$ hedges against corruption at $s_1$ costing $1-\varepsilon$, playing $a$ hedges against corruption at $s_2$ costing $1$); symmetrically at $s_1$; at $s_2$, $a$ wins by $(1-\delta)^2-\delta^2(1-\varepsilon)$. Chosen policy $bba$, $U=\varepsilon$, for every $\delta<\tfrac12$ (checked at $\delta\in\{\tfrac14,\tfrac1{10},\tfrac1{100},10^{-6}\}$, $\varepsilon\in\{10^{-2},10^{-6}\}$). Each situation hedges separately; the hedges jointly land on the worst policy. The loss is real in the *believed* problem too: with $\tilde U(\pi):=\mathbb E[U(\text{corrupt}_\delta(\pi))]$, $\tilde U(bba)\approx\varepsilon$ while $\max_\pi\tilde U\approx1$ for small $\delta$. So under C1 the proposed theorem holds *with* a margin hypothesis and fails without one — a margin theorem, again.

**Reading C2 — belief about the chosen policy, enactment noise on top.** Belief $\mu=(1-\delta)\delta_{\pi^*}+\delta P_o$ over chosen policies; the enacted policy is the chosen one corrupted independently at rate $\nu$; the agent conditions on its *chosen* action. Independence makes the noise factor out: $\mathbb E[U(\text{enacted})\mid\text{chosen}(s)=a]=\mathbb E_{\pi'\sim\mu}[\tilde U_\nu(\pi')\mid\pi'(s)=a]$ with $\tilde U_\nu(\pi):=\mathbb E[U(\text{corrupt}_\nu(\pi))]$. This is the pointwise model of §1 with $U$ replaced by $\tilde U_\nu$, and Theorem A's strict inequalities are open conditions, so the counterexample survives small $\nu$: the founding-sketch instance still chooses $bba$ at $\nu\in\{10^{-3},10^{-2},\tfrac1{20}\}$ (Python §(vi)). Under C2 the chosen-vs-enacted distinction changes nothing.

**Reading C0 (degenerate).** If the belief is "chosen policy $=\pi^*$ with probability $1$" and the agent conditions on its chosen action, every deviation is a zero-probability event: unavailable under the default convention, so the agent chooses $\pi^*$ trivially — a $\delta=0$ statement with no content.

## 9. Relation to the earlier lab's Props 1–3 and the R1/R2 dispute (T2d)

The earlier lab ([models--unbounded-embedded-agency-model](../../04-deference-trust-lab/models--unbounded-embedded-agency-model.md), `redteam--unbounded-embedded-agency-redteam`) used two formalizations, neither of which is the pointwise model:
- **R2 / Prop 1**: a *whole-policy* chooser maximizing a mixture of value maps $\mathrm{Bel}=(1-\delta)V_\star+\delta V_{\text{other}}$; bound $\frac{\delta}{1-\delta}\cdot\text{range}$.
- **R1** (the redteam's "natural reading"): the agent *plays* $\pi^*$ with probability $1-\delta$ and anything otherwise; bound $\delta\cdot\text{range}$.
The pointwise model differs from both: the belief is a distribution over *policies* (not value maps); the choice is per situation; the conditional is evidential and self-locating, so conditioning on a deviation discards the self-mass; and nothing is assumed about what the agent enacts.

| earlier claim | status under the pointwise model |
|---|---|
| Prop 1 (whole-policy mixture bound) | PROVED as algebra, but its hypothesis `hsel` ("the agent maximizes Bel") is exactly what the pointwise agent does *not* do (Theorem A). Its bound $\frac{\delta}{1-\delta}$ reappears as Theorem C's bound — with the self-hypothesis $\delta_\pi$ in place of $V_\star$ and the trust bound in place of `hsel`. INTERPRETATION: Theorem C is the pointwise-honest form of Prop 1. |
| Prop 2 (Stag-Hunt threshold $\delta\le1-c/b$) | The threshold arises from an *interventional* computation ("if I play Stag, my partner plays Stag w.p. $1-\delta$"), which is reading C1's conditional (product belief), not the EDT conditional. Under the EDT conditional with $P_o$ on the miscoordinated profiles, Stag is chosen at $\pi^*$ for every $\delta$ (playing Stag is evidence of being the coordinated self), and the trap $HH$ is a fixed point for every $\delta$ — selection is by the trust bound (§5.1), with a $P_o$-dependent threshold, not by the belief. Prop 2's threshold survives as the C1 margin condition of Theorem E, not as a fact about belief-in-$\pi^*$. |
| Prop 2★ (general Stag-Hunt closure, CONJECTURE) | REFUTED as stated for the EDT pointwise agent: "$(1-\delta)$-believes every other situation plays $\pi^*$" does not give $O(\delta)$ (Theorem A). Its surviving form is Theorem E (C1 + margin) or Theorem C (self-consistency + trust bound). |
| Prop 3 (bound depends on behavioural $\delta_b$, not substrate $\delta_m$; "place the belief on the realized policy") | Sharpened rather than refuted: it is not enough that the belief be *about* the realized policy's identity — the belief must be *correct about the agent's own policy* (self-consistency). Belief $(1-\delta)\delta_{\pi^*}$ when the realized policy is not $\pi^*$ is a belief about the realized policy that is simply false, and Theorem A shows it buys nothing. |
| Redteam R1: "under the natural reading the principal's $\delta\cdot$range is right" | R1 presupposes its conclusion: it assumes the agent enacts $\pi^*$ with probability $1-\delta$, so the decision rule plays no role. The pointwise agent with the *same belief* enacts a policy of $\mu$-mass zero (Theorem A). R1's bound is about a hypothetical enactor, not about UDT1.0. |
| Redteam R2 critique ("the $1/(1-\delta)$ is an artifact of the mixture-of-value-maps model") | Under self-consistency the $\frac{\delta}{1-\delta}$ is not an artifact: family T1 (§5.5) achieves $\frac{\delta}{1-\delta+\delta^2}$ at a trust-bound fixed point, so the true worst case is within a factor $1-\delta+\delta^2$ of $\frac{\delta}{1-\delta}$, strictly above $\delta$. |
| Micro-example Part C ("the whole-policy bound holds but is slack for the trapped agent") | Reproduced exactly: $HH$ satisfies the bound only when it satisfies the trust bound, i.e. when the bound is vacuous (§5.1). |

**On the audit's §6.3 conjecture** ("a robust version probably is Cole's revised theorem with $V^*$ read updatelessly, the trust bound as equilibrium selection, and 'believing you are UDT1.1' the name of the selected equilibrium"): Theorem C is that statement in the finite updateless model, and Theorem A is the demonstration that the alternative (a static belief in UDT1.1) fails. The "chosen vs enacted" distinction does not change this under C2, and under C1 it converts the theorem into a margin theorem whose constant grows with $|S|$.

## 10. Status table

| item | statement | register |
|---|---|---|
| A | proposed theorem false in the pointwise model; loss $=1$ at every $\delta$; $\lvert S\rvert=\lvert A\rvert=\lvert\operatorname{supp}P_o\rvert=2$; convention-free | REFUTED, machine-verified (exact rationals) |
| — | sketch's "$\lvert S\rvert=2$ cannot do this" | REFUTED, exhaustive search |
| — | support-1 $P_o$: no strict loss; total loss with adversarial ties | PROVED (prose), machine-verified |
| B | fixed-instance margin theorem, $\delta<m/U^*\Rightarrow$ realized $=\pi^*$ | PROVED (prose), machine-verified |
| — | self-evidence: trust bound automatic under belief-in-$\pi^*$ | KERNEL-CHECKED (`self_evidence`) |
| C | self-consistent pure fixed point + $(\mathrm{TB}_{s_0})\Rightarrow U(\pi)\ge U^*-\frac{\delta}{1-\delta}$ | PROVED (prose); algebraic core KERNEL-CHECKED |
| C′ | mixed fixed points, same bound, no $\lvert A\rvert$ factor | PROVED (prose) |
| — | Stag Hunt: both pure equilibria at every $\delta$; trust bound rejects $HH$ iff $\delta<(15-\sqrt{97})/16$ | machine-verified |
| — | tightness: gaps $\delta/(1-\delta+\delta^2)$ and $\delta$ achieved; extremal | search / CONJECTURE |
| — | pure fixed points always exist (plain or floored) | REFUTED (instances) |
| — | mixed fixed points always exist (continuous extension) | CONJECTURE (one instance checked, floats) |
| D | floored agent: every pure fixed point within $\frac{\delta}{1-\delta}$ | PROVED (prose), machine-verified |
| E | C1 margin theorem $m_s>2(1-(1-\delta)^{\lvert S\rvert-1})\Rightarrow$ chosen $=\pi^*$ | PROVED (prose), machine-verified |
| — | C1 near-tie instance, loss $1-\varepsilon$ at every $\delta<\tfrac12$ | machine-verified |
| — | C2 reduces to the pointwise model with $\tilde U_\nu$; Theorem A survives | PROVED (prose), machine-verified |
| — | which reading (C1/C2/pointwise) the author intends | ATTRIBUTION-UNVETTED |
| — | Theorem C is the pointwise-honest form of Prop 1; R1 presupposes its conclusion | INTERPRETATION |

## File map

| Link | Path |
|---|---|
| this note | `research/unbounded-embedded/unbounded-embedded-lab/models/updateless-self-game.md` |
| `updateless_self_game.py` | `research/unbounded-embedded/unbounded-embedded-lab/models/updateless_self_game.py` (run: `python3 updateless_self_game.py`; ends with `ALL ASSERTIONS PASSED`; ≈10 s) |
| `UpdatelessTrustBound.lean` | `research/unbounded-embedded/unbounded-embedded-lab/lean/UpdatelessTrustBound.lean` (check: `lean/check.sh`) |
| [00-founding-sketches](../notes/00-founding-sketches.md) | `research/unbounded-embedded/unbounded-embedded-lab/notes/00-founding-sketches.md` |
| `AGENDA` | `research/unbounded-embedded/unbounded-embedded-lab/AGENDA.md` |
| [summer-research-plan-2026--research-ideas-may-2026](../../01-primary/summer-research-plan-2026--research-ideas-may-2026.md) | `research/unbounded-embedded/01-primary/summer-research-plan-2026--research-ideas-may-2026.md` (§Updatelessness) |
| [2026-03-26](../../03-journals/2026-03-26.md) | `research/unbounded-embedded/03-journals/2026-03-26.md` (chosen vs enacted bullet) |
| [audit-revised-theorem-1](../../audit-revised-theorem-1.md) | `research/unbounded-embedded/audit-revised-theorem-1.md` (§6 brittleness) |
| [planning-to-write-about-coles-theorem](../../01-primary/planning-to-write-about-coles-theorem.md) | `research/unbounded-embedded/01-primary/planning-to-write-about-coles-theorem.md` |
| [models--unbounded-embedded-agency-model](../../04-deference-trust-lab/models--unbounded-embedded-agency-model.md) | `research/unbounded-embedded/04-deference-trust-lab/models--unbounded-embedded-agency-model.md` (Props 1–3) |
| `redteam--unbounded-embedded-agency-redteam` | `research/unbounded-embedded/04-deference-trust-lab/redteam--unbounded-embedded-agency-redteam.md` (R1/R2) |
| `UDT11Belief` (earlier lab's Lean, house style) | `research/deference-trust-lab/lean/UDT11Belief.lean` |
| `conventions-and-status-labels` | `research/wiki/conventions-and-status-labels.md` |
