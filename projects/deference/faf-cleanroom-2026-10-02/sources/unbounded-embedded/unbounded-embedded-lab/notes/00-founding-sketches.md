# Founding sketches (round 0)

*Claude (Smithy), 2026-08-24. Derivations made while orienting on the corpus, before any subagent work. Everything here is **SKETCHED** unless marked otherwise — the point of round 1 is to prove, machine-verify, or refute each item. Registers per `conventions-and-status-labels`. Notation follows [audit-revised-theorem-1](../../audit-revised-theorem-1.md) §1 ($\xi$, $\xi^{\pi_S}$, $Q_\xi$, $V^*_\xi$, the trust bound $(\mathrm{TB}_h)$, facts F1/F2, Lemma A).*

---

## 1. Sink-or-swim as a two-fixed-point self-game (T1a)

**Setting (the finite shadow of Cole's rOSI agent).** Deterministic environment with two steps. At the island the agent chooses `stay` (reward $c$, episode ends) or `jump`; after `jump` it chooses `swim` (reward $b>c>0$) or `sink` (reward $0$). Rewards normalized so $b\le1$. Hypothesis class over *joint* action/percept histories (percepts are deterministic, so hypotheses differ only in action conditionals):
- $H_{\mathrm{self}}$: "I am $\pi$" — actions from the agent's own policy $\pi$ (a fixed point, to be determined). Prior weight $1-\delta$.
- $H_{\mathrm{sink}}$: jumps w.p. 1, then sinks. Prior weight $\delta s$.
- $H_{\mathrm{swim}}$: jumps w.p. 1, then swims. Prior weight $\delta(1-s)$.
The agent is $\pi(h)\in\arg\max_a Q_\xi(h,a)$ with $Q_\xi(h,a)=\mathbb E_\xi[\text{return}\mid ha]$, $\xi=$ the mixture; ties broken by randomization. A **fixed point** is a $\pi$ such that $\pi$ is an argmax policy for the $\xi$ built from $\pi$ (the finite analogue of a reflective oracle being consistent about $\pi_S$).

**After `jump`, $\pi$ swims** at every fixed point: the last step's $Q$ is the immediate reward, independent of the self-model. So only the island decision is self-referential. Write $j:=\pi(\text{jump}\mid\text{island})$.

**Posterior after `jump`** is proportional to $(1-\delta)j,\ \delta s,\ \delta(1-s)$ (all three hypotheses' `jump`-probability times prior). Hence
$$Q_\xi(\text{island},\text{jump})\;=\;b\cdot\frac{(1-\delta)j+\delta(1-s)}{(1-\delta)j+\delta}\,,\qquad Q_\xi(\text{island},\text{stay})=c.$$

**Fixed points.**
- *Trapped* ($j=0$): $Q(\text{jump})=b(1-s)$. Self-consistent iff $b(1-s)\le c$, i.e. $\boxed{s\ge 1-c/b}$. **Independent of $\delta$**: however much prior mass the self-hypothesis has, if the *off-policy* residue is mostly sinkers the trap is a fixed point. This is [scrubbed] made exact.
- *Good* ($j=1$): $Q(\text{jump})=b(1-\delta s)$. Self-consistent iff $b(1-\delta s)\ge c$, i.e. $\boxed{\delta s\le 1-c/b}$.
- *Mixed* ($0<j<1$): requires $Q(\text{jump})=c$ exactly; solving gives a unique $j^*\in(0,1)$ when both pure fixed points exist. (Kakutani's third equilibrium.)

So for $\delta<1-c/b$ and $s\ge 1-c/b$ **both** pure fixed points exist for the same prior. This is the oracle-sourced trap of `comparison-mupi-vs-uea` §3, exhibited.

**Premise and conclusion of the revised Theorem 1 at the trap.** At the island, $w(\text{self}\mid\epsilon)=1-\delta>1-\delta$ — premise holds (take any $\delta'>\delta$). $V^{\pi}_\xi=c$; $V^*_\xi=b$ (optimal for $\xi$'s percept model: jump then swim). Conclusion fails by $b-c$, which does not shrink with $\delta$. **So the "there is a reflective oracle" existential in the live theorem is essential, and [scrubbed] is this.**

**The trust bound separates them.** $(\mathrm{TB}_{\text{island}})$: $\max_a Q_\xi\ge w V^*=(1-\delta)b$. At the trap: $\max=c$; violated iff $\delta<1-c/b$. At the good point: $\max=b(1-\delta s)\ge(1-\delta)b$ ✓ always. So TB selects the good fixed point exactly in the regime where the good point exists.

**Connection to the deference-trust-lab Stag Hunt.** The good-point condition $\delta s\le 1-c/b$ at $s=1$ is *literally* the Stag-Hunt threshold $\delta\le 1-c/b$ of [models--unbounded-embedded-agency-model](../../04-deference-trust-lab/models--unbounded-embedded-agency-model.md) Prop 2. Sink-or-swim is a Stag Hunt between the agent-at-the-island and the agent-in-the-water; the "partner plays Stag" belief is $j$. (INTERPRETATION, but the arithmetic is identical.)

**Open for round 1.** Verify with exact rational arithmetic; do the mixed fixed point; generalize to an arbitrary finite-horizon tree with a finite hypothesis class (existence of fixed points by Kakutani on the product of simplices; the trust-bound refinement).

## 2. The agent-side floor, current-node-only version (T1b)

The audit §5 proposes $\pi_S^\dagger$: at $h$, if some prefix $h'\preceq h$ has $\max_aQ_\xi(h',a)<w(\text{self}\mid h')V^*_\xi(h')$, play $\pi^*_\xi(h)$, else the EDT argmax. Problem noticed while orienting: the prefix comparisons are *oracle calls*, so at an equality node they randomize, and independent oracle calls at $h'$ and at its children give *inconsistent* reset decisions — the "reset subtree" is not a subtree. Fix: check only the **current** node.

**Definition ($\pi^\dagger$, current-node floor).** At $h$: if $\max_aQ_\xi(h,a)<w(\text{self}\mid h)\,V^*_\xi(h)$ play $\pi^*_\xi(h)$; if $>$ play the EDT argmax; at equality, mix (oracle-decided). The self-hypothesis is "I am $\pi^\dagger$".

**Claim (SKETCHED): at any fixed point, $\varepsilon(h):=V^*_\xi(h)-V^{\pi^\dagger}_\xi(h)\le C\cdot\delta_h/(1-\delta_h)$ with $\delta_h:=1-w(\text{self}\mid h)$ and $C=O(|A|)$, horizon-free.**
- *Reset branch at $h$* (probability $\lambda_h$): the agent plays $\pi^*(h)$ and continues as $\pi^\dagger$; since $\pi^*(h)$ is optimal at $h$, $\varepsilon$ contributes only through children: $\varepsilon(h)\mid_{\text{reset}}=\gamma\,\mathbb E[\varepsilon(\text{child})]$. Zero loss at this node.
- *Non-reset branch* ($1-\lambda_h$): $\max_aQ_\xi(h,a)\ge w_hV^*(h)$, and Lemma A (upper half) on the chosen $a$ gives $Q^{\pi^\dagger}(h,a)\ge V^*(h)-O(|A|)\delta_h$ (F2 bounds the posterior drop at ties). Loss $O(|A|\delta_h)$ at this node, **no dependence on children**.
- Unrolling: $\varepsilon(h)\le C\cdot\mathbb E[\delta_{h_\tau}\gamma^\tau]$ where $\tau$ is the first non-reset node along the $\pi^*$-driven path. Since $1-w_t$ is a $\xi$-martingale (audit §3.3), optional stopping gives $\mathbb E_\xi[\delta_{h_\tau}]=\delta_h$; changing measure to the self-hypothesis costs a factor $\le 1/w_h$. Hence the claim.
- Unlike the subtree version, the reset *can* fire at a fixed point (no contradiction argument is available for the current-node version), but it fires harmlessly.

**Consequence if the claim holds (CONJECTURE).** *For every reflective oracle*, $\pi^\dagger$ satisfies $w(\xi^{\pi^\dagger}\mid h)>1-\delta\Rightarrow V^{\pi^\dagger}_\xi(h)>V^*_\xi(h)-C\delta$. Cole's $\exists O$ becomes $\forall O$, at the price of replacing $\pi_S$ by $\pi_S$-with-a-floor. The floor is CDT-flavoured (it plays the *planning* optimum $\pi^*$ when the *evidential* self-assessment falls below the self-trust level) — worth flagging for the T4 thread. (ATTRIBUTION-UNVETTED that Cole would accept this as a repair rather than a change of agent.)

**Open for round 1.** Prove the claim in the finite-horizon finite-hypothesis model with all constants explicit; check the measure-change step; check whether the $\pi^*$-driven path measure is really dominated by the self-hypothesis's path measure (the reset branch is $\pi^\dagger$'s own action, so yes, but write it out).

## 3. The author's UDT1.0 ⊨ UDT1.1 theorem: a counterexample and the repaired statement (T2a, T2b)

**Setting (finite, updateless).** Situations $S$ (finite), actions $A$, policies $\pi\in A^S$, utility $U:A^S\to[0,1]$, $\pi^*\in\arg\max U$. A **UDT1.0 agent with self-uncertainty** has a belief $\mu$ over policies and at situation $s$ plays $\arg\max_a\ \mathbb E_\mu[U(\pi)\mid \pi(s)=a]$ (pointwise EDT conditional on "my action at $s$ is $a$"; no history, no updating). "$(1-\delta)$-believes it is UDT1.1" $:=$ $\mu=(1-\delta)\,\delta_{\pi^*}+\delta\,P_o$ with $P_o$ arbitrary.

**Counterexample (checked by hand; needs machine verification).** $S=\{1,2,3\}$, $A=\{a,b\}$, $\pi^*=(a,a,a)$, $U(a,a,a)=1$, $U(b,b,b)=1-\eta$, $U(a,a,b)=0$, $U(b,b,a)=0$, all other $U=0$. $\delta=0.1$, $P_o=\tfrac12\delta_{(b,b,b)}+\tfrac12\delta_{(a,a,b)}$, $\eta=0.01$.
- $s_1$: $\mathbb E[U\mid a]=(0.9\cdot1+0.05\cdot0)/0.95\approx0.947$; $\mathbb E[U\mid b]=0.99$. Plays $b$.
- $s_2$: identical. Plays $b$.
- $s_3$: $\mathbb E[U\mid a]=0.9/0.9=1$; $\mathbb E[U\mid b]=(0.05\cdot0.99+0.05\cdot0)/0.1\approx0.495$. Plays $a$.
- Realized policy $(b,b,a)$, $U=0$. The agent $0.9$-believes it is the optimal policy; the trust bound $\max_a\mathbb E[U\mid a]\ge(1-\delta)U(\pi^*)$ holds at every situation; the loss is total. Scaling: the construction works for every $\delta>0$ with $\eta<\delta R/(1-\delta+\delta R)$, so $\varepsilon\not\to0$ as $\delta\to0$.
- *Mechanism.* Conditioning on the deviation $b$ at $s_1$ discards the self-mass entirely (5&10 / "conditioning out of self-trust", the author's note in [planning-to-write-about-coles-theorem](../../01-primary/planning-to-write-about-coles-theorem.md)); the near-optimal hypothesis $(b,b,b)$ then makes $b$ look good at $s_1$ and $s_2$ separately, while at $s_3$ the self-mass makes $a$ look good. The realized policy is outside the support of the belief — the belief is not self-consistent, and each action is "explained" by a different hypothesis.
- *Why two situations cannot do this (SKETCHED):* with $|S|=2$ any near-optimal supporter of a deviation at $s_1$ agrees with $\pi^*$ at $s_2$ and hence supports agreement there with near-optimal value, blocking the second deviation; the algebra shows for $w>1/2$ the double-deviation conditions are jointly unsatisfiable. To be verified (an exhaustive search over small rational instances would settle it).

**Register: the proposed theorem is REFUTED in this formalization (pending machine check), and the refutation is robust in $\delta$.**

**The repaired statement (SKETCHED).** Replace "believes it is $\pi^*$" by **self-consistency**: $\mu=(1-\delta)\delta_{\pi}+\delta P_o$ where $\pi$ is the agent's *own* realized policy (a fixed point: $\pi(s)\in\arg\max_a\mathbb E_\mu[U\mid\pi'(s)=a]$ for all $s$). Add the **trust bound at one situation** $s_0$: $\max_a\mathbb E_\mu[U\mid \pi'(s_0)=a]\ \ge\ (1-\delta)\,U(\pi^*)$. Then
$$U(\pi)\ \ge\ U(\pi^*)-\delta\Big(1+\tfrac{1}{1-\delta}\Big)\quad(\text{for deterministic }\pi\text{ at }s_0;\ \text{an extra factor }k\le|A|\text{ if }\pi\text{ randomizes among }k\text{ ties}).$$
*Proof.* $\mathbb E_\mu[U\mid\pi'(s_0)=\pi(s_0)]=\dfrac{(1-\delta)U(\pi)+\delta p\,\mathbb E_o[U\mid\pi(s_0)]}{(1-\delta)+\delta p}\le\dfrac{(1-\delta)U(\pi)+\delta p}{(1-\delta)+\delta p}$ with $p=P_o(\pi'(s_0)=\pi(s_0))$; combine with the trust bound and $U\le1$. $\square$ (This is the audit's Lemma A in the updateless setting: the self-hypothesis's "continuation" is the whole policy $U(\pi)$, so the bound is horizon-free and needs only one situation.)
- Without the trust bound: the Stag Hunt trap $(H,H)$ is a self-consistent fixed point for every $\delta$ (with $P_o$ on the two miscoordinated profiles), and violates TB iff $1-\delta>c/b$.
- **Floored UDT1.0** (the T1b floor, updateless): at $s$, if $\max_a\mathbb E_\mu[U\mid a]<(1-\delta)U(\pi^*)$ play $\pi^*(s)$, else argmax. Claim: every fixed point of the floored agent is within $\approx2\delta$ of optimal (if some situation is non-reset, the bound above applies; if all are reset, $\pi=\pi^*$ — but then TB holds at every situation and nothing resets, so "all reset" is impossible; the equality/mixed case goes through because the argmax branch's conditional value is exactly $(1-\delta)U(\pi^*)$). Existence of a fixed point by Kakutani/Nash on the finite self-game.

**Interpretation (INTERPRETATION register).** The author's sentence "belief that you're UDT1.1 does the work that Cole's constructed oracle does" is half right: what does the work is (i) self-consistency of the self-model plus (ii) the trust bound as an equilibrium-selection condition relative to UDT1.1's value. Belief in UDT1.1 *without* self-consistency (a static, miscalibrated belief) does not do it, and can do arbitrarily badly. This sharpens [audit-revised-theorem-1](../../audit-revised-theorem-1.md) §6.2–6.3 into a theorem + counterexample pair.

**Open for round 1.** Machine-verify the counterexample and the repaired theorem (exact rationals), exhaustively search $|S|=2$ for a counterexample (expect none), prove the floored-agent claim, and write the Lean for the one-situation bound (pure real arithmetic — a good Lean target).

## 4. Smaller observations (all SKETCHED)

- **Lemma A's lower half with the "right" action.** The audit's §4.1 uses an $a^*\in\operatorname{supp}\pi^*(h)$ with $\xi(a^*\mid h)\le\pi_S(a^*\mid h)$. In the finite models this is where "the self-hypothesis's posterior does not fall when I do what I would do" enters; write it as a named lemma (call it the *self-evidence lemma*, F2 in the audit) since T1a, T1b and T2b all use it.
- **The $|A|$ factor.** In T2b (updateless, deterministic at $s_0$) there is no $|A|$ factor because conditioning on one's own deterministic action *raises* the self-posterior. In Cole's sequential setting the factor comes only from ties. So a "no-ties" version of the revised theorem has $\varepsilon=\delta(1+1/(1-\delta))$, matching the 2025 theorem's "only one action is Bayes-optimal" clause.
- **Relation to mupi Prop 4.29.** Their "any deterministic policy is a subjective embedded equilibrium for some beliefs" is the *prior-sourced* statement; §1 above is the *oracle-sourced* one (fixed prior, two equilibria). Both traps have the same behaviour; the difference is what a trust bound can do about them (everything vs nothing).

## File map
| Link | Path |
|---|---|
| [audit-revised-theorem-1](../../audit-revised-theorem-1.md) | `research/unbounded-embedded/audit-revised-theorem-1.md` |
| `comparison-mupi-vs-uea` | `research/unbounded-embedded/comparison-mupi-vs-uea.md` |
| [models--unbounded-embedded-agency-model](../../04-deference-trust-lab/models--unbounded-embedded-agency-model.md) | `research/unbounded-embedded/04-deference-trust-lab/models--unbounded-embedded-agency-model.md` |
| [planning-to-write-about-coles-theorem](../../01-primary/planning-to-write-about-coles-theorem.md) | `research/unbounded-embedded/01-primary/planning-to-write-about-coles-theorem.md` |
| `conventions-and-status-labels` | `research/wiki/conventions-and-status-labels.md` |
| `AGENDA` | `research/unbounded-embedded/unbounded-embedded-lab/AGENDA.md` |
