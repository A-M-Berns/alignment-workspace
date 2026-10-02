# The interleaved-conditionals artifact, located precisely (T4a sketch)

*Claude (Smithy), 2026-08-24, written while round 1 ran. Register: **SKETCHED** throughout; the finite-model computations are to be machine-checked in round 2. Source claim: [summer-research-plan-2026--research-ideas-may-2026](../../01-primary/summer-research-plan-2026--research-ideas-may-2026.md) §Updatelessness, third bullet — Cole's notion of $\varepsilon$-optimality "simulates the consequences of a policy by interleaving conditional probabilities … an action can only have an impact after it actually occurs … this method evaluates consequences as if Omega cannot accurately predict what you'll do (even if you do believe Omega can predict you!)". Notation: [audit-revised-theorem-1](../../audit-revised-theorem-1.md) §1.*

## 1. The structural fact

For any policy $\pi$, Cole's policy value $V^\pi_\xi(h)$ is the value of $\pi$ in the **induced environment** $\nu_\xi(e\mid h a):=\xi(e\mid h a)$ — one fixed percept kernel, the same for every candidate $\pi$. Policy-dependence of percepts can enter $V^\pi_\xi$ only through *past actions already in the history*. Consequently $V^*_\xi(h)=\sup_\pi V^\pi_\xi(h)$ is the Bayes-optimal value of a fixed (history-dependent) environment: an *updateful* optimality notion, in the precise sense that a percept already emitted is exogenous to the policy being evaluated. (Verified reading of the definitions; the sentence is just what "interleaving" means.)

Two consequences follow, and they pull in opposite directions from the summer plan's one-line summary.

## 2. Opaque Newcomb: the interleaving is *not* an artifact

Action first, percept second: $h=a_1e_1$, $e_1\in\{\$1\mathrm M,\$0\}$ is the (previously hidden) content of the opaque box, revealed after the choice. Suppose the hypothesis class contains "Omega-accurate" universes $T_{1}$ ("I one-box and the box holds \$1M") and $T_{2}$ ("I two-box and the box holds \$0"), each a joint kernel over action and percept. By F1 the self-hypothesis borrows $\xi$'s own percept conditional, and by the unwinding in [audit-revised-theorem-1](../../audit-revised-theorem-1.md) §1, $\xi(e_1\mid a_1)$ is determined entirely by the **non-self** hypotheses' posteriors after $a_1$. Conditioning on $a_1=$ one-box drives $T_2$'s posterior to $\approx0$, so $\xi(\$1\mathrm M\mid\text{one-box})\approx1$ and $\xi(\$1\mathrm M\mid\text{two-box})\approx0$.
Then both $\pi_S$ (EDT: $Q_\xi(\epsilon,\text{one-box})\approx\$1\mathrm M$) and $\pi^*_\xi$ (Bayes-optimal in $\nu_\xi$: same kernel) **one-box**. The evidential correlation lives in $\xi(e_1\mid a_1)$ and the interleaving preserves it. Headline (SKETCHED): *in opaque Newcomb Cole's optimality notion and Cole's agent both one-box, and the correlation comes from uncertainty over deterministic self-hypotheses, exactly as the summer plan's second bullet says it must ("correlations … must result from uncertainty about decision procedures").* So "evaluates consequences as if Omega cannot predict you" is not right for this case.

## 3. Transparent Newcomb: the artifact, exactly

Percept first: $h=e_0a_1e_1$ with $e_0\in\{\$1\mathrm M,\$0\}$ the visible content, filled by Omega according to a prediction of the agent's *policy* (one-box-on-seeing-\$1M vs not). Now:
- $\nu_\xi(e_0\mid\epsilon)=\xi(e_0)=\sum_T w(T)\,T(e_0)$ is a **fixed number**, independent of the candidate $\pi$. So $V^\pi_\xi(\epsilon)=\sum_{e_0}\xi(e_0)\,V^\pi_\xi(e_0)$ ranks policies with the box contents held fixed.
- At $e_0=\$1\mathrm M$: two-boxing yields $\$1\mathrm M{+}\$1000$ in $\nu_\xi$ (the money is there), one-boxing $\$1\mathrm M$. At $e_0=\$0$: $\$1000$ vs $\$0$. So $\pi^*_\xi=$ always-two-box and $V^*_\xi(\epsilon)=\xi(\$1\mathrm M)(\$1\mathrm M{+}\$1000)+\xi(\$0)\cdot\$1000$.
- $\pi_S$ at $e_0=\$1\mathrm M$ also two-boxes (EDT conditioned on the visible \$1M: no hypothesis consistent with $e_0=\$1\mathrm M$ takes the money away). So at the fixed point $\pi_S$ two-boxes, Omega-accurate hypotheses predict $e_0=\$0$, hence $\xi(\$1\mathrm M)\approx0$ and $V^*_\xi(\epsilon)\approx\$1000$.
- The UDT policy "one-box iff I see \$1M" actually receives $\$1\mathrm M$ against an accurate Omega. Cole's theorem's conclusion "$V^{\pi_S}_\xi\ge V^*_\xi-\varepsilon$" is satisfied — $\pi_S$ is $\varepsilon$-optimal by the theorem's yardstick — while the yardstick itself sits at $\$1000$ against an achievable $\$1\mathrm M$.

Headline (SKETCHED): **the interleaving artifact is exactly the updateful/updateless distinction, and it bites iff a policy-dependent prediction manifests in the percept stream before the action it predicts.** The summer plan's "an action can only have an impact after it actually occurs" is the right diagnosis; "as if Omega cannot predict you" is right for the transparent case only.

## 4. What this says about the plan's "two interchangeable fixes"

The plan: fix either (i) the oracle (allow correlated oracle calls) or (ii) the optimality notion; "I'm not sure which angle is most promising."
- For §3 the binding constraint is (ii): however Omega's prediction is *generated* (independent oracle sample, correlated oracle, direct simulation), $V^\pi_\xi(\epsilon)$ samples $e_0$ from $\xi(e_0)$ without feeding $\pi$ in. A correlated oracle changes $\xi$ (hence what $\pi_S$ *does* at its fixed point), not the definition of $V^*_\xi$. So (i) alone cannot make the theorem's conclusion mean updateless optimality. (SKETCHED; this is a claim about the definition, not about any oracle.)
- Where (i) matters: the *equilibrium*. With independent oracle calls, an Omega that predicts a *randomizing* $\pi_S$ by querying the oracle gets an independent sample, so Omega is only as accurate as $\pi_S$ is deterministic; with a correlated oracle Omega's sample and the agent's action coincide. This changes $\xi(e\mid h a)$ at the fixed point and hence $\pi_S$'s choice — it is the "independence of oracle calls" objection, and it is *separate* from the interleaving artifact. (INTERPRETATION.)

## 5. The updateless replacement, and why it lands on T2

The obvious replacement for $V^\pi_\xi$ is the **policy-conditioned value** $V^\pi_{\mathrm{upd}}:=\sum_T w(T\mid \text{policy}(T)=\pi)\,\mathbb E_T[\text{return}]$ — evaluate $\pi$ under the prior *conditioned on the hypothesis that I am $\pi$*, so that Omega-accurate universes paired with $\pi$ carry $\pi$'s prediction into $e_0$. In the finite model of [00-founding-sketches](00-founding-sketches.md) §3 (hypotheses = (environment kernel, policy kernel) pairs) this is well-typed, and on transparent Newcomb it gives $V^{\text{1box-on-\$1M}}_{\mathrm{upd}}=\$1\mathrm M$, $V^{\text{2box}}_{\mathrm{upd}}=\$1000$.
But conditioning on "I am $\pi$" for $\pi\ne$ the agent's own fixed-point policy has **no self-hypothesis mass** (F2: the self-hypothesis is the agent). That is precisely the static "I am UDT1.1" belief structure whose failure mode is the 3-situation counterexample of [00-founding-sketches](00-founding-sketches.md) §3: each candidate policy is evaluated by *other* hypotheses' opinions of it. The T2b repair (self-consistency + trust bound against $U(\pi^*)$) is therefore the finite answer to T4b: *the updateless version of Cole's theorem is "a self-consistent updateless equilibrium that satisfies the trust bound relative to the policy-conditioned optimum is near that optimum"*, and the trust bound is again doing equilibrium selection. (CONJECTURE; the sequential updateless version — histories, discounting, the self-hypothesis's percept kernel — is not written down.)

## 6. Round-2 targets
1. Machine-check §2–§3 in the sequential finite model (transparent and opaque Newcomb as two-step trees; hypothesis class $\{T_1,T_2,\text{self}\}$; compute $\pi^*_\xi$, $V^*_\xi(\epsilon)$, $\pi_S$'s fixed point, and the actual value of the UDT policy against the Omega-accurate universes).
2. Define $V_{\mathrm{upd}}$ in the sequential finite model and state the updateless trust-bound theorem; check whether the T1b floor with $V^*$ replaced by $V_{\mathrm{upd}}$ gives near-updateless-optimal fixed points, and what it does on transparent Newcomb (expected: it one-boxes-on-\$1M iff the self-posterior after seeing \$1M is still high — which it is not at the two-boxing fixed point, so the floor may *not* rescue it; this is the interesting case).
3. Record what this does to the summer plan's "trust→optimality compares a CDT view to an EDT view" sentence (`research-plan--research-plan-md`): the comparison is between EDT-with-history ($\pi_S$) and Bayes-optimal-in-$\nu_\xi$ ($\pi^*_\xi$), which coincide in opaque Newcomb and both two-box in transparent Newcomb — so it is not CDT vs EDT, it is updateful-EDT vs updateful-planning. (INTERPRETATION; ATTRIBUTION-UNVETTED as a reading of the author's sentence.)

## File map
| Link | Path |
|---|---|
| [summer-research-plan-2026--research-ideas-may-2026](../../01-primary/summer-research-plan-2026--research-ideas-may-2026.md) | `research/unbounded-embedded/01-primary/summer-research-plan-2026--research-ideas-may-2026.md` |
| [audit-revised-theorem-1](../../audit-revised-theorem-1.md) | `research/unbounded-embedded/audit-revised-theorem-1.md` |
| [00-founding-sketches](00-founding-sketches.md) | `research/unbounded-embedded/unbounded-embedded-lab/notes/00-founding-sketches.md` |
| `research-plan--research-plan-md` | `research/unbounded-embedded/01-primary/research-plan--research-plan-md.md` |
