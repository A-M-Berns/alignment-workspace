# The amplifier counterexample

*A secondary but instructive obstruction: the one-parameter family $g(e_0) = (1+2c)e_0 - c$ passes every **parallel** threshold-trust cut on a single bet while differing from the identity — so parallel cuts alone cannot pin the tower. Its scope is exactly the complement of the gap-bet argument: it constrains only settings whose bet class cannot mention the expert.*

## Setting and role

Measure model of the abstract single-expert setting ([[setting-and-notation]]): $e := E^\ast(X)$ with distribution $\mu$ on $[0,1]$ (here $\mu = \mathrm{Unif}[0,1]$), and $g(e_0) := E_\pi(X \mid e = e_0)$ the novice's layer-wise expectation; the tower ([[deference-notions]]) says $g = \mathrm{id}$ $\mu$-a.e. Source: deference-v6 §1.6 (L245).

**Scope (read this first).** The amplifier refutes one specific route to Mart: *parallel* cuts $\{e > t\}$, $\{e \le t\}$ of a **single fixed bet** $X$. It does **not** survive Total Trust over a gap-closed bet class — see the computation below and [[total-trust-implies-mart]], where Mart follows in two lines once bets may mention the expert's estimates. So the amplifier's continuing interest is for **restricted domains**: DDB frames (not world-measurable), domain-restricted Total Trust such as the forced faithful-acceleration family ([[faithful-acceleration-result]]), and any setting where expert-referencing bets are illegal. There it remains *the* witness that the inequality face (threshold trust) genuinely underdetermines the equality face (the tower).

## The counterexample

For $\mu = \mathrm{Unif}[0,1]$ and any $c > 0$: $g(e_0) = (1+2c)e_0 - c$ — fixed point $g(\tfrac12) = \tfrac12$, slope $1 + 2c > 1$; a novice that systematically *amplifies* the expert's deviations from $\tfrac12$.

**Upper cut** at $t$:
$$E_\pi(X\cdot\mathbb{1}[e > t]) - t\,P_\pi(e > t) = \int_t^1 g(e)\,de - t(1-t) = (1-t)\Big[\tfrac{1-t}{2} + ct\Big] \ \ge 0 .$$

**Lower cut** at $t$:
$$t\,P_\pi(e \le t) - E_\pi(X\cdot\mathbb{1}[e \le t]) = t\Big[c + \tfrac{t(1-2c)}{2}\Big] \ \ge 0$$
(for $c \le \tfrac12$ both factors nonnegative; for $c > \tfrac12$ the bracket is minimized at $t=1$, value $\tfrac12$).

**Soft cuts come free**: $\operatorname{Ind}_\delta(e > t) = \tfrac1\delta \int_t^{t+\delta} \mathbb{1}[e > u]\,du$, and for $u \ge t$, $(X-t)\mathbb{1}[e>u] \ge (X-u)\mathbb{1}[e>u]$ pointwise — so passing all hard cuts implies passing all soft cuts.

**Marginal identity too**: $\int_0^1 g\,d\mu = \tfrac12 = \int_0^1 e\,d\mu$, so even the bare tower-on-this-one-bet ($E_\pi(X) = E_\pi(E^\ast(X))$) holds. The failure is strictly in the conditional/layer-wise content.

**What kills it**: boundedness at the extremes — $g(0) = -c < 0$ and $g(1) = 1 + c > 1$ are impossible for a conditional expectation of a $[0,1]$-bet. If the expert's estimate attains neighborhoods of $0$ and $1$, $c = 0$ is forced; if $e$ stays interior, the amplifier survives all parallel cuts.

**Why it dies under gap-bets** ([[total-trust-implies-mart]]): for $Z = X\cdot\mathbb{1}[e \in [a,b]]$,
$$E_\pi\big(Z - E^\ast(Z)\big) = \int_a^b (g(e) - e)\,de = c\,(b-a)(a+b-1) \ne 0 \quad (c > 0,\ a+b \ne 1),$$
so the gap-bet cuts detect it immediately. The amplifier can misprice only *within-layer* structure, and gap-bets probe exactly that.

## Two places the amplifier's residue still matters

1. **The near-threshold layer in the telescoping proof.** With soft weights, nothing in threshold trust lower-bounds $E^H_n\big(D \cdot \mathbb{1}[0 < E^\ast(D) \le \delta]\big)$; that thin slice is the amplifier's surviving degree of freedom, and it is precisely the term separating the δ-hedged followed strategy from the argmax strategy itself — see the wedge section of [[keep-or-switch-telescope]]. (When the bet class *is* gap-closed, [[total-trust-implies-mart]] + [[mart-implies-value]] recover Value itself anyway; and ⚠ [[provable-bound-respect]] (unvetted) recovers it from the full threshold family even below gap-closure — the residue then matters only for the threshold-$0$ fragment.)
2. **Restricted-domain deference.** On the faithful-acceleration domain the forced Total-Trust family is a sparse, gate-weighted set of instances — nowhere near gap-closed — so amplifier-like novices are live there, and Value$_\mathcal{D}$ ⟺ TT$_\mathcal{D}$ with Mart strictly stronger is the honest picture (deference-v6 §5.11; [[trichotomy-where-value-sits]]).

## Status

**KERNEL-CHECKED** (cut computations): `Frozen.amp_upper_cut_nonneg`, `amp_lower_cut_nonpos`, `amp_boundedness_forces_id` (`FrozenDeliberation.lean`; the Lean checks the closed-form integral arithmetic — the measure-model reading is prose; honesty caveat at [[conventions-and-status-labels]]). The gap-bet kill computation: **PROVED (prose, this page)**, elementary.

## Related

- [[total-trust-implies-mart]] — the argument that confines this page to secondary status
- [[value-iff-mart]] — the assembled lattice and where separations survive
- [[keep-or-switch-telescope]] — the near-threshold residue (the wedge); [[provable-bound-respect]] — the provably-full cuts that close it (unvetted)
- [[reversal-of-difficulty-vs-ddb]] — DDB frames as the natural home of the surviving obstruction

*Source: deference-v6 §1.6 (`deference-in-logical-induction-v6.md` L232–289); scope reframing 2026-07-21 with [[total-trust-implies-mart]].*
