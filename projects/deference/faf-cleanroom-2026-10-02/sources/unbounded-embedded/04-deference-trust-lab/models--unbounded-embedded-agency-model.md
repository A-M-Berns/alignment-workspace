# A toy formal model: "UDT1.0 that believes it is UDT1.1 ⇒ ε-optimal"

*Thread: AGENDA "Unbounded Embedded Agency" (Cole Wyeth) — Interpretational Issues /
Updatelessness. This note develops the top pick of `findings/unbounded-embedded-agency-ideate.md`
(Idea 1, toward Ideas 2 and 4) into a precise toy model with every hypothesis stated, one fully
worked micro-example (machine-run: `../unbounded_embedded_agency_micro.py`, all assertions pass),
a candidate Lean file (`../lean/unbounded-embedded-agency.lean`, UNCHECKED), and an explicit map of
what is PROVED / SKETCHED / CONJECTURE, where it is Vingean, and how it relates to tiling.*

Every claim is flagged **PROVED** / **SKETCHED** / **CONJECTURE** / **INTERPRETATION**.

---

## 0. The claim in one sentence, and the correction it forces

The principal's proposed theorem (AGENDA): *"if a UDT1.0 agent `(1-δ)`-believes its policy is
UDT1.1, then it is `ε`-optimal."* This note makes "UDT1.0", "UDT1.1", "believes", and "optimal"
precise; proves the algebraic core; and **corrects the bound**: the honest, provable inequality is

$$(1-\delta)\big(V_\star(p_\star)-V_\star(s)\big)\ \le\ \delta\,(hi-lo),
\qquad\text{i.e.}\qquad V_\star(p_\star)-V_\star(s)\ \le\ \tfrac{\delta}{1-\delta}\,(hi-lo),$$

so $\varepsilon(\delta)=\frac{\delta}{1-\delta}\,\mathrm{range}$ — clean $2\delta\,\mathrm{range}$
for $\delta\le\tfrac12$, exactly $0$ at $\delta=0$, and **blowing up as $\delta\to1$**. The naive
$\varepsilon=\delta\,\mathrm{range}$ is only the first-order term; the $1/(1-\delta)$ is real because
the bad $\delta$-world is weighed against the $(1-\delta)$ good-world *mass*, not against $1$. The
micro-example (§5) exhibits a concrete $\delta$ at which the naive bound **undershoots the true gap**.

This is the *decision-theoretic* sibling of the lab's epistemic deference result (v2: endorsing the
expert's beliefs ⇒ deference). Here: *believing the optimal whole-policy coordinator authored your
policy* ⇒ near-optimal decisions. The belief is the **trust-warrant**, and the bound makes it
quantitative.

---

## 1. The objects

We work in the finite **multi-situation decision problem** of `udt-representation-theorem/
formal-single-agent.md`, the deliberately LI-free / oracle-free *shadow* (cf. how
`LeanDeference.value_of_CM` is the $\delta=0$ shadow of the LI §3 chain).

- **Situations** $S$ (finite): decision points the agent might face — times, copies, observations.
- **Actions** $A$ (finite), available at each situation.
- A **policy** $\pi\in\mathrm{Pol}:=A^S$ assigns an action to each situation.
- A **utility** $U:\mathrm{Pol}\to\mathbb R$ on whole policies. (Writing $U$ on *policies*, not on
  $S\times A$, is what lets the environment depend on the action *pattern* — "cross-situation
  dependence", `formal-single-agent.md` §"Pattern Dependence". Without it split = unified.)
- **Bounded utility:** $U(\mathrm{Pol})\subseteq[lo,hi]$. (The §6/Coin hygiene condition; without
  it the $\delta$-world is unbounded and no $\varepsilon$ bound is possible — Weatherson's Coin.)

**UDT1.1** = the *whole-policy* optimizer: $\pi_\star\in\arg\max_{\pi}U(\pi)$, value
$V_\star:=U$. By definition $\pi_\star$ is optimal, so UDT1.1 is *trivially* $0$-optimal **when the
agent knows its source code** (it just is the argmax). This is the "unified model".

**UDT1.0** = the *pointwise / per-situation* optimizer: at each $s$ independently it chooses
$\arg\max_a \mathbb E[U\mid \text{my action at }s=a]$ under some belief about its actions
*elsewhere*. This is the "split model" / EDT-style best response. UDT1.0 is **not** automatically
optimal: it can sit in a bad fixed point (a Stag-Hunt trap — §3) that no single-situation deviation
escapes.

**The belief.** "The UDT1.0 agent $(1-\delta)$-believes its policy is UDT1.1" is modeled as a belief
about *who authored its decisions*: a $(1-\delta)/\delta$ mixture,

$$\mathrm{Bel}(\sigma)\ =\ (1-\delta)\,V_\star(\sigma)\ +\ \delta\,V_{\mathrm{other}}(\sigma),$$

where $V_{\mathrm{other}}:\mathrm{Pol}\to[lo,hi]$ is an **arbitrary, possibly adversarial**
"some-other-code" value map. With probability $1-\delta$ the agent thinks the globally-coordinating
optimizer is in charge; with probability $\delta$ it thinks something else is, and we grant the
adversary a free hand within the utility bounds.

**The optimality notion.** The agent **commits** to a $\mathrm{Bel}$-maximizer $s$ and we score it by
the **true** map $V_\star$. "$\varepsilon$-optimal" $:=$ $V_\star(p_\star)-V_\star(s)\le\varepsilon$.
(This is exactly UDT's own currency — expected value of the policy — applied at the empty history, as
the AGENDA's "Updatelessness" paragraph asks.)

---

## 2. The central claim (whole-policy view)

> **Proposition 1 (PROVED, finite algebra; Lean candidate `epsilon_optimal_of_belief`).**
> Let $\mathrm{Pol}$ be any type, $V_\star,V_{\mathrm{other}}:\mathrm{Pol}\to\mathbb R$ with
> $lo\le V_{\mathrm{other}}\le hi$ pointwise, $0\le\delta$, and let $s$ maximize
> $\mathrm{Bel}=(1-\delta)V_\star+\delta V_{\mathrm{other}}$. Then for **every** $p_\star$,
> $$(1-\delta)\big(V_\star(p_\star)-V_\star(s)\big)\ \le\ \delta\,(hi-lo).$$

*Proof (five lines, machine-checkable).* $\mathrm{Bel}(p_\star)\le\mathrm{Bel}(s)$ by choice of $s$.
Expand: $(1-\delta)V_\star(p_\star)+\delta V_{\mathrm{other}}(p_\star)\le
(1-\delta)V_\star(s)+\delta V_{\mathrm{other}}(s)$. Hence
$(1-\delta)(V_\star(p_\star)-V_\star(s))\le \delta(V_{\mathrm{other}}(s)-V_{\mathrm{other}}(p_\star))
\le\delta(hi-lo)$, the last step from $V_{\mathrm{other}}(s)\le hi$,
$V_{\mathrm{other}}(p_\star)\ge lo$. $\square$

**Status of the Lean.** `../lean/unbounded-embedded-agency.lean` states this as
`epsilon_optimal_of_belief` (proof: `nlinarith`), with the $\delta\le\tfrac12$ corollary form folded
into the prose and the $\delta=0$ corner as `optimal_of_certain`. **UNCHECKED — for the Lean-verify
agent.** It does NOT `import Mathlib` (targeted imports only). The faithfulness audit is in §6.

**Three honest caveats (these are the model, not bugs):**

1. **Concentration ≠ correctness.** The bound delivers closeness to $V_\star$, *the map the agent
   believes in*. If $V_\star$ is not really optimal, "$\varepsilon$-optimal" is "$\varepsilon$-optimal
   by the agent's own lights." The theorem is about the belief being *concentrated* on UDT1.1, not
   *accurate*. For the trust reading this is load-bearing: a human's warrant to trust the agent
   requires *both* that the agent's self-belief be concentrated *and* that what it is concentrated on
   ($V_\star$) really be the optimal coordinator.
2. **$1/(1-\delta)$ blow-up.** You can be arbitrarily bad if you barely believe you are UDT1.1.
3. **The whole-policy / pointwise gap.** Prop 1 models a chooser over *whole policies*. A genuine
   UDT1.0 agent chooses *actions pointwise*. The reduction "pointwise UDT1.0 believing it is UDT1.1
   $\Rightarrow$ effectively picks the believed UDT1.1 policy" is **assumed** in Prop 1 (it is the
   "$s$ maximizes $\mathrm{Bel}$" hypothesis). §3 is where that gap is the actual content.

---

## 3. Where the work is: the Stag-Hunt self-miscoordination, and how $(1-\delta)$ dissolves it

Prop 1 hides the entire difficulty in "$s$ maximizes $\mathrm{Bel}$." A pointwise agent does **not**
get to choose a whole policy; it chooses each $\pi(s)$ against a belief about the *other* situations.
The danger is a **bad equilibrium**: a whole policy that is jointly suboptimal yet *locally stable*
under single-situation deviations. This is a **Stag Hunt the agent plays with itself** (situations =
players, payoff = the agent's global utility).

### 3.1 The mechanism (SKETCHED; micro-example machine-verified, §5)

Take two situations (two copies/two times) and a symmetric Stag Hunt with $b>c>0$: Stag against a
Stag-partner pays $b$; Stag against a Hare-partner pays $0$; Hare pays $c$ regardless. Global utility
of a profile = sum of the two payoffs.

- **(S,S)** = $2b$ is the optimum (UDT1.1 picks this).
- **(H,H)** = $2c$ is a *second* fixed point of pointwise best response.

**Pointwise UDT1.0 has two self-consistent profiles** (§5 Part B1): both (S,S) and (H,H). The bad one
$\,$(H,H) is a genuine trap — a unilateral switch to Stag against a Hare-partner pays $0<c$, so no
single-situation improvement escapes it. *This is exactly why UDT1.0 is not trivially optimal and why
Prop 1's hypothesis is non-trivial.*

**The $(1-\delta)$-belief breaks the trap.** Suppose each copy $(1-\delta)$-believes the *other* plays
the UDT1.1 action (Stag). Worst case (all $\delta$-mass on "other plays Hare") gives belief
$q=1-\delta$ that the partner is Stag, so

$$\mathbb E[\text{Stag}]=(1-\delta)\,b,\qquad \mathbb E[\text{Hare}]=c.$$

Stag is the best response **iff** $(1-\delta)b\ge c$ **iff** $\boxed{\delta\le 1-\tfrac{c}{b}}$. Below
this threshold the belief makes *every* copy choose Stag, so the realized profile is the optimum
(S,S). **The $(1-\delta)$-belief is a correlation device that points all situation-copies at the same
(optimal) policy** — precisely the job the AGENDA says Cole Wyeth's hand-built reflective oracle does.

### 3.2 The discharged bridge, and its hidden hypothesis (PROVED in the toy game)

> **Proposition 2 (PROVED for the symmetric 2-action 2-situation game; Lean `stag_hunt_select`).**
> In the Stag Hunt above, if $\delta\le 1-c/b$ then pointwise best response under the
> $(1-\delta)$-belief that the partner plays Stag yields Stag. Conversely (Lean `stag_hunt_trap`), if
> $(1-\delta)b<c$ then Stag's worst-case value is strictly below Hare's, so the trap can persist.

This is the **honest payoff of developing Idea 1 toward Idea 2**: the smuggled hypothesis "$s$
maximizes $\mathrm{Bel}$" of Prop 1 is, in the toy game, *derived* from the belief — but it costs an
**extra hypothesis the whole-policy view hides**: $\delta\le 1-c/b$, i.e. the self-belief must be
strong *relative to the game's Stag-Hunt gap*. The whole-policy bound (Prop 1) is silent on this; the
pointwise reality (Prop 2) makes it explicit.

> **Proposition 2★ (CONJECTURE — the general Stag-Hunt closure, Idea 2).** In a general finite
> self-coordination game, a pointwise UDT1.0 agent that $(1-\delta)$-believes every other situation
> plays $\pi_\star$ realizes a profile within $O(\delta)$ value of $\pi_\star$, and *exactly* $\pi_\star$
> when $\pi_\star$ is the unique $(1-\delta)$-robust equilibrium. **Gap:** ruling out multiple bad
> equilibria surviving the perturbation needs a uniqueness/smoothness hypothesis — which is the
> general analog of "$\delta\le 1-c/b$" and the real content. This is the constructive twin of v2
> §10.4's open characterization (see §7).

---

## 4. Separating self-knowledge from environmental modification (Idea 4 — rescuing the interpretation)

The AGENDA's sharpest critique: Cole's "$(1-\delta)$-confidence in my source code" **covertly bans
self-modification**, because "I mechanically work like *this* (my initial code)" gets low probability
in any environment where modifying yourself is rational — so the "self-knowledge" hypothesis secretly
restricts the *environment class* and muddies the optimality reading. The fix is to split the single
confidence into two **independent** parameters.

> **Definition (the split).**
> - **Behavioural self-knowledge $1-\delta_b$:** confidence about *which policy you realize* — the
>   extensional map $(\text{history})\mapsto(\text{action-distribution})$. This is confidence about
>   $\sigma\in\mathrm{Pol}$, NOT about code.
> - **Substrate stability $1-\delta_m$:** confidence that this policy is *not modified* (by the
>   environment or by the agent itself) over the horizon.

"Confidence in my source code" bundles both ($\delta_b$ and $\delta_m$ together): knowing the code
pins behaviour *and* immutability. Once split:

> **Proposition 3 (PROVED, by re-indexing; Lean `epsilon_optimal_split`).** Prop 1's bound needs only
> $\delta_b$ small and is **agnostic to $\delta_m$** — formally, the believed-value mixture and the
> conclusion mention only $\delta_b$; a substrate parameter $\delta_m$ can be carried in the signature
> and is *genuinely unused*. The trick that makes this honest: **place the belief on the *realized*
> (post-modification) policy.** Then an environment that *rewards* self-modification has small
> $\delta_m$ yet can still have small $\delta_b$ *for the realized policy*, and the optimality
> certificate survives.

The Lean witness `epsilon_optimal_split` literally takes a `δm` argument and never touches it, proving
the bound from `δb` alone (its proof is `epsilon_optimal_of_belief` at `δ:=δb`). **The unusedness of
`δm` is the formal content** — see the §6 fidelity note (this is the one place the verify agent must
confirm we are not cheating: an unused argument is not a smuggled conclusion, it is the claim).

**Why this matters for the optimality reading** (resolving the AGENDA's worry): the objection
"self-knowledge rules out interesting (self-mod-rewarding) environments" becomes "self-knowledge *of
code* does; self-knowledge *of realized behaviour* need not." The optimality theorem, stated about the
*realized* policy with $\delta:=\delta_b$, no longer covertly bans self-modification. What it *cannot*
do is certify the *pre-modification* commitment if $\delta_b$ for the realized policy is large — and
that is correct: if you cannot predict what policy you will end up running, you have no warrant.

**The remaining open piece (CONJECTURE):** characterizing *when $\delta_b$ can be kept small across a
self-modification*. That is "Vingean self-trust across the mod" and sits in the tiling register
(§8) — you do not predict the new code, only trust the realized behaviour is still near-$\pi_\star$.

---

## 5. The fully worked micro-example (machine-run, all assertions pass)

`../unbounded_embedded_agency_micro.py` (exact rational arithmetic, no float slop). Output reproduced
in-repo; the load-bearing rows:

**Part A — the bound and the correction.** Menu $V_\star=\{a{:}0,b{:}1,c{:}\tfrac34,d{:}\tfrac12\}$
(so $p_\star=b$), adversarial $V_{\mathrm{other}}=\{a{:}\tfrac12,b{:}0,c{:}1,d{:}\tfrac12\}$,
$[lo,hi]=[0,1]$:

| $\delta$ | chosen $s$ | $(1-\delta)\Delta$ | $\le\delta\cdot\mathrm{range}$? | true $\Delta$ | $\delta\cdot\mathrm{range}$ | naive bounds true gap? |
|---|---|---|---|---|---|---|
| $0$ | $b$ | $0$ | ✓ | $0$ | $0$ | ✓ |
| $1/4$ | $c$ | $0.1875$ | ✓ | $0.25$ | $0.25$ | ✓ (tight) |
| $2/3$ | $c$ | $0.083$ | ✓ | $\mathbf{1.0}$ | $\mathbf{0.667}$ | **✗ — naive undershoots** |
| $9/10$ | $c$ | $0.025$ | ✓ | $1.0$ | $0.9$ | ✗ |

The PROVED inequality $(1-\delta)\Delta\le\delta\cdot\mathrm{range}$ holds at every row; the **naive**
$\varepsilon=\delta\cdot\mathrm{range}$ **fails** to bound the true gap at $\delta=2/3$ (true gap $1.0$
vs $0.667$). The honest $\varepsilon=\frac{\delta}{1-\delta}\mathrm{range}$ holds everywhere. *This is
the concrete witness that the correction is real.*

**Part B — the Stag Hunt** ($b=4,c=3$, threshold $1-c/b=1/4$):
- B1: both (S,S) and (H,H) are pointwise fixed points (the trap is real).
- B2: $(1-\delta)$-belief that the partner is Stag selects Stag for all $\delta\le 1/4$ and flips to
  Hare at $\delta=1/3$ — matching the closed form exactly.

**Part C — tying them together:** the realized pointwise agent lands on (S,S) (gap $0$) for
$\delta\le 1/4$ and on (H,H) (gap $0.25$) at $\delta=1/3$; in *both* cases the realized gap stays
inside the honest whole-policy bound $\frac{\delta}{1-\delta}$. **Caveat surfaced by Part C:** at
$\delta=1/3$ the whole-policy bound (0.5) still *holds* for the trapped agent but is now a *slack,
non-informative* certificate — the actual failure is that the bridge hypothesis ($hsel$ / Prop 2)
breaks past $\delta^\*=1/4$. So Prop 1 certifies the pointwise agent **only on the $\delta$-range where
the Stag-Hunt trap is dissolved**; outside it the certificate is vacuously safe but the agent is not
actually choosing the believed optimum.

---

## 6. Lean correspondence audit (UNCHECKED file `../lean/unbounded-embedded-agency.lean`)

Five theorems. For each: informal claim → does the Lean say it? → gaps.

| Lean theorem | informal claim | faithful? |
|---|---|---|
| `epsilon_optimal_of_belief` | Prop 1 headline bound | **Faithful & strong.** Proves it for *arbitrary* `pstar` (not assumed optimal) — the strongest form: "$s$ beats any `pstar` up to $\delta$-slack". `Vother` arbitrary in $[lo,hi]$ (the strength). Hyp `hsel` is the believed-argmax = the *commitment*, correctly a hypothesis. |
| `epsilon_optimal_split` | Prop 3: bound depends on $\delta_b$, NOT $\delta_m$ | **Faithful, with one thing to verify.** It carries an *unused* `δm`. An unused argument is **not** a smuggled conclusion — it is exactly the claim "optimality is $\delta_m$-agnostic". Verify agent: confirm `δm` appears in *no* hypothesis and *no* step (it should appear only in the binder). NON-VACUOUS: it is `epsilon_optimal_of_belief` at `δ:=δb`, not `True`. |
| `optimal_of_certain` | $\delta=0$ ⇒ exact optimality | Faithful; the $\delta=0$ corner. |
| `stag_hunt_select` | Prop 2: $\delta\le 1-c/b$ ⇒ Stag is BR (worst case) | **Faithful but narrow.** Conclusion `c ≤ (1-δ)*b` *is* "$\mathbb E[\text{Hare}]\le\mathbb E[\text{Stag}]$" (best-response comparison) on the worst-case belief $q=1-\delta$. Gap: ONLY the symmetric 2-action 2-situation game — NOT the general Idea-2 claim. The hypothesis is stated as `(1-δ)*b ≥ c` (= `δ≤1-c/b`, division-free). `hb,hc` unused (non-degeneracy prose only). |
| `stag_hunt_trap` | Prop 2 converse: weak belief ⇒ trap can persist | Faithful; witnesses that the `δ≤1-c/b` hypothesis is load-bearing, not slack. |

**The single biggest fidelity gap (flag).** Theorems 1–3 are about a *whole-policy* chooser; the
pointwise→whole-policy bridge is proved (theorem `stag_hunt_select`) **only** in the toy Stag Hunt.
In general it is ASSUMED (Prop 1's `hsel`) or CONJECTURED (Prop 2★). The Lean does **not** smuggle a
general bridge; it honestly proves the toy instance and assumes the rest. *A reader who takes
`epsilon_optimal_of_belief` as "pointwise UDT1.0 believing UDT1.1 ⇒ ε-optimal in any game" would be
over-reading it — the `hsel` hypothesis is doing that work, and §3/§5 show it can fail past
$\delta^\*$.*

---

## 7. The sharp cross-connect: this **is** v2 §10.4's open characterization

The single most important structural observation (carried over and sharpened from the ideation):

> **INTERPRETATION (well-argued).** v2 §10.4's genuinely-open question — *"when does inductor $N$
> LUV-Total-Trust inductor $M$?"* (the cross-agent premise that is **not** free between distinct
> inductors, unlike the self-directed `ccee`) — is, with $M=\pi_\star$, *literally* the question
> **"when may a UDT1.0 inductor justifiably believe it is UDT1.1?"** The decision-theoretic thread
> (this note) and the epistemic-deference thread (v2 §10) **share one open characterization.**

Concretely: in the LI rendering (Idea 6), "the agent $(1-\delta)$-believes its realized policy is
$\pi_\star$" is the soft future-state weight $w_n:=\mathrm{Ind}_\delta(\mathbb P_{f(n)}(\text{"policy}=
\pi_\star\text{"}))$ plugged into the conditional martingale `ccee` (4.12.3) — exactly the §10
machinery, with the *expert* being "$\pi_\star$, the optimal coordinator". v2 §10's audit shows lines
2/4/5 are free; only the self-endorsement-of-$\pi_\star$ premise (= LUV-Total-Trust toward $\pi_\star$)
must be supplied. So **closing v2 §10.4 closes the Stag-Hunt selection question, and vice versa.**
(Whether "policy $=\pi_\star$" is even a well-typed market-generable event for an embedded inductor is
the diagonal problem of v2 §1.2 / AGENDA "Representational Issues"; if it is paradox-prone, the *soft*
$\mathrm{Ind}_\delta$ self-belief is the surviving form — a satisfying unification with §5.2's
false-hard/true-soft asymmetry.) This is CONJECTURE / future work; the present note's proved content
is the finite shadow (Props 1–3).

---

## 8. Where this is **Vingean**, and how it relates to tiling

**Vingean = trust by general principle, not by prediction** (AGENDA: watching a chess master, you
predict the *win*, not the *move*). This model is Vingean in two distinct places, and crucially *not*
in a third:

1. **Trusting UDT1.1 (the belief itself) is Vingean.** The agent does **not** predict $\pi_\star$
   action-by-action — Prop 1 never computes $\pi_\star$; it only believes "*whatever* the optimal
   coordinator does, an optimal coordinator is doing it" (the mass $1-\delta$ on $V_\star$). The
   warrant is *general* ("the whole-policy optimizer is in charge") not *predictive* ("it will play
   Stag at $s_3$"). Indeed if the agent could predict $\pi_\star$ pointwise it would not *need* the
   belief — it would just play $\pi_\star$. The belief is doing Vingean work precisely because it
   substitutes a general-principle trust for an impossible self-prediction. *This is the same epistemic
   posture as v2's deference to the future self: trust the more-thought-out verdict without
   re-deriving it.*

2. **The self/env split (§4) is where the Vingean point bites hardest.** Behavioural self-knowledge
   $1-\delta_b$ is *Vingean self-knowledge*: confidence about *what you will do* (you will win),
   **not** about *your code* (how you win). The AGENDA's whole complaint is that "confidence in source
   code" is the **non-Vingean** version, and it is the one that breaks (bans self-mod). Switching to
   behavioural confidence on the *realized* policy is exactly switching to the Vingean register — and
   §4 shows that is the version under which the optimality theorem survives.

3. **Where it is NOT Vingean (and must not pretend to be):** the *adversary's* $V_{\mathrm{other}}$ is
   not trusted at all — it is bounded and otherwise arbitrary. The $(1-\delta)$ mass, not any
   prediction of the bad world, carries the bound. Good: a trust certificate that relied on predicting
   the failure mode would be self-undermining.

**Relation to tiling.** Cole's theorem is *not* a tiling theorem, but the AGENDA hoped it was "a close
relative" — the bridge from *syntactic self-knowledge* to *high-value strategy* is what a no-intentional-
self-modification (tiling) proof wants. The split (§4) is the formal hook:

- A **tiling** statement wants: *the current agent endorses its successor (the post-modification
  policy) as still near-$\pi_\star$.* In this model that is exactly **"$\delta_b$ stays small across the
  modification"** — Vingean trust in the realized successor's *behaviour*, not its code. Conflating
  trustworthiness with $\delta_m=0$ (frozen code) is the anti-corrigible mistake; the split lets a
  *corrigible* agent have small $\delta_b$ **and** small $\delta_m$ toward *legitimate* modification
  (AGENDA "Modeling Legitimacy"): you expect to be changed and endorse the realized result.
- So the model converts "Cole's self-knowledge ⇒ optimality, but it bans self-mod" into: **"behavioural
  (Vingean) self-trust on the realized policy ⇒ optimality, and it permits self-mod exactly when the
  realized policy is still Vingean-trusted (near-$\pi_\star$)."** The open conjecture of §4 — when can
  $\delta_b$ be kept small across a mod — is the genuine tiling content, and it lands in the same
  Vingean-reflection register as v2 §10.4 (§7). **Tiling = the dynamic, across-modification version of
  the static belief Prop 1 takes as given.**

---

## 9. Status summary

| Result | Statement | Status |
|---|---|---|
| Prop 1 | whole-policy mixture bound $(1-\delta)\Delta\le\delta\,\mathrm{range}$ | **PROVED** (finite algebra; Lean `epsilon_optimal_of_belief`, UNCHECKED) |
| Bound correction | honest $\varepsilon=\frac{\delta}{1-\delta}\mathrm{range}$, not $\delta\,\mathrm{range}$ | **PROVED** (micro-example exhibits naive bound failing) |
| Prop 2 | Stag-Hunt selection in the 2×2 toy game, with threshold $\delta\le 1-c/b$ | **PROVED** (Lean `stag_hunt_select`/`stag_hunt_trap`, UNCHECKED; Python-verified) |
| Prop 2★ | general Stag-Hunt closure (pointwise⇒whole-policy) | **CONJECTURE** (gap: equilibrium-uniqueness hypothesis) |
| Prop 3 | optimality depends on $\delta_b$, not $\delta_m$ (self/env split) | **PROVED** by re-indexing (Lean `epsilon_optimal_split`, UNCHECKED) |
| §7 | "believe you're UDT1.1" $\equiv$ v2 §10.4 cross-agent LUV-Total-Trust | **INTERPRETATION** (well-argued) |
| §8 | tiling = across-modification Vingean self-trust ($\delta_b$ small across mod) | **CONJECTURE / INTERPRETATION** |

**Central claim:** *A UDT1.0 agent that $(1-\delta)$-believes (on its realized policy) that it is
UDT1.1 is $\varepsilon$-optimal with $\varepsilon=\frac{\delta}{1-\delta}\cdot\mathrm{range}$* —
**PROVED** at the finite-algebra level (Lean candidate UNCHECKED), with the pointwise→whole-policy
bridge **PROVED in a toy Stag Hunt** (threshold $\delta\le 1-c/b$) and **CONJECTURED** in general, and
with the self-knowledge hypothesis cleanly **split** so it no longer bans self-modification (optimality
needs only behavioural $\delta_b$, not substrate $\delta_m$).
