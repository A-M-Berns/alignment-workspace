# edt-node-value — EDT-derived node-value: killing the argmax tautology

**TODO id:** `edt-node-value`  ·  **Modality:** LEAN-CORE  ·  **Status:** PROVED (kernel-checked, sorry-free, axioms clean)
**Artifact:** `deference-trust-lab/run2/lean/edt-node-value.lean`
**Compile:** `bash …/lean/check.sh …/run2/lean/edt-node-value.lean` → exit 0; all 19 `#print axioms` report `[propext, Classical.choice, Quot.sound]` (no `sorryAx`). Only two cosmetic linter warnings (an unused section variable on `vNode_decoupled_eq`; a `<;>` style note).

> **Round-2 honesty note (the one subtlety I had to fix).** An earlier draft of this file built the
> coupled near-miss with a *separable* `U π = (−100·[π₀=pay]) + (10000·[π₁=pay])` and then declared the
> "global UDT optimum" to be the *diagonal* policy `(pay,pay)=9900` "by the coherence constraint."
> That was a disguised shadow: that `U` is in fact **separable** (interaction term 0), so the EDT-argmax
> kernel — when computed at **both** nodes — picks `(refuse, pay)=10000`, which is the *unrestricted*
> optimum, and there is **no divergence**. The divergence only appeared because the draft computed the
> EDT-argmax at node 0 alone and then **projected onto the diagonal by hand** — the round-1 sin in new
> clothes. The shipped file fixes this: `U` is **genuinely non-separable** (matched-pay reward), so
> `(pay,pay)` is the *unrestricted* maximizer, the EDT-argmax is computed at **both** nodes with no
> hand-projection, and the divergence is real. `not_separable` proves `Separable U p u` fails on the
> instance, certifying the coupling is in `U`, not in a fiat constraint.

---

## 1. What round 1 did wrong, and what this fixes

Round 1 (`UpdatelessDeference{,2}.lean`, off-limits) defined "A updatelessly-defers to u" through a
per-node valuation `node_value : S → A → ℝ` that was a **FREE INPUT, never tied to the utility `U`**.
The discrimination between a mugging-caver and a non-caver was supplied by the *modeler's* hand-chosen
`node_value` (CRITIQUE §3; redteam Probes 1/3/5/6); the kernel-checked Lean was "argmax of a separable U
is globally optimal" — a tautology, with the discriminator hand-fed and the kernel inert.

This file **removes the free input**. The per-node value is DERIVED, as a genuine EDT conditional of the
*same* utility `U`, routed entirely through an explicit self-prediction / reachability kernel `κ`:

```
vNode U κ s a  :=  U (κ s a)         -- E_p[U(π) | reach s, play a at s]
```

`κ s a : S → A` is the agent's self-model: *conditioned on the local event "(reach s, play a)", which
whole policy do I expect to be running?* `vNode` is `U ∘ κ`. **The kernel is literally inside the
definition, not a relabel.** Two different κ give two different node-values and hence two different EDT
argmaxes — which is exactly the near-miss (§4).

A structural choice that makes κ matter: `U : (S → A) → ℝ` is the **coupled** type (utility of the
*whole* policy). Round 1 used `U : S → A → ℝ`, which is separable *by construction* — so the kernel had
nothing to do. The coupled type can express acausal coupling, and only then does the EDT conditional
differ from the global optimum.

## 2. The decoupled-coincidence theorem (clause i) — PROVED

`Separable U p u :⇔ ∀ π, U π = ∑ s, p s · u s (π s)` (structural: a coupled U fails this — proved
non-vacuously in §4). `Decoupled κ base :⇔ ∀ s a, κ s a = Function.update (base s) s a` (κ plays `a` at
`s` and a FIXED off-`s` policy `base s`, **independent of `a`** — "reach s and the local action do not
couple to actions elsewhere").

**The load-bearing new lemma `vNode_decoupled_eq`** (clean axioms): under separability + decoupling,

```
vNode U κ s a  =  p s · u s a  +  ∑_{t ≠ s} p t · u t (base s t).
```

The proof *unfolds `U (κ s a)` THROUGH separability* and splits off the `s`-term; the `a`-dependence is
carried EXACTLY by `p s · u s a`, and the off-`s` mass is κ's prediction `base s` — an `a`-constant. This
is the precise sense in which "the EDT conditional through κ collapses to the local argmax **only** in the
decoupled case." It is NOT definitional: it is forced by the structure of κ AND of `U`.

**Main theorem `edt_decoupled_globally_optimal`:** let `π★` pick, at each `s`, a maximizer of the
*EDT-derived* node value `vNode U κ s ·` (its ONLY spec is
`hEDT : ∀ s a, vNode U κ s a ≤ vNode U κ s (π★ s)` — **not** a free valuation, **not** the local argmax of
`U` by fiat). Then under separability + decoupling, `∀ π, policyValue U π ≤ policyValue U π★`.

The proof DERIVES the local `u`-argmax property of `π★` from `hEDT` via `vNode_decoupled_eq` (cancelling
the common off-`s` mass), then dominates termwise. (Honest note: `p ≥ 0` turns out to be *unused* — the
EDT ranking already transfers to `p s · u s`, so the result is marginally more general than the regime
spec; `hp` is kept as `_hp`.)

**Why this is not the off-limits `split_eq_global`:** `split_eq_global` took the per-node optimality as a
*free* `Finset.le_sup'` over a hand-fed `splitOptimum`, with the local argmax assumed. Here the per-node
optimality is *derived* from the EDT-node-value argmax through κ; the new content is `vNode_decoupled_eq`
+ `vNode_argmax_of_u_argmax`. The final `Finset.sum_le_sum` is generic monotonicity plumbing, not a
re-skin of the named theorem.

## 3. Non-vacuity witness (decoupled) — PROVED by `decide`/`norm_num`

`Decoupled.*`: `S = A = Fin 2`, `p ≡ 1`, separable `u` (best action 1 at s=0, action 0 at s=1),
`base ≡ 0`, `κ s a = update (base s) s a`. Checked:
- `vNode_via_kappa`: `vNode U κ 0 1 = U (update (base 0) 0 1)` by `rfl` — κ is in the value.
- `edt_ranks_s0 : vNode U κ 0 0 < vNode U κ 0 1` (5 < 7) and `edt_ranks_s1` — the EDT node value,
  computed through κ with the off-`s` base mass, ranks the actions.
- `edtPolicy_is_edt_argmax`: `edtPolicy = (0↦1, 1↦0)` maximizes `vNode U κ s ·` at every `(s,a)`.
- `edt_attains_global`: by the main theorem, `edtPolicy` dominates **every** policy. Global optimum value
  7 (`global_opt_value`), strictly beating the all-0 policy 5 (`all_zero_strictly_worse`) — non-trivial.

## 4. MANDATORY near-miss: coupled divergence = the acausal payoff — PROVED (honest, non-separable)

`Mugging.*` is a counterfactual-mugging / Twin structure with **two nodes**, and the coupling lives in a
**genuinely non-separable `U`** so the divergence is real (no diagonal-by-fiat):
- node 0 = `self`, node 1 = `twin` (the predicted / correlated copy); `A = {refuse=0, pay=1}`.
- `U π = (−100 if π 0 = pay) + (+10000 if π 0 = pay AND π 1 = pay)`. The +10000 fires **only on the
  matched-pay diagonal** — the acausal correlation (Omega rewards you in the counterfactual where the
  predicted copy does what you do). The four policy values are `(0,0)↦0, (0,1)↦0, (1,0)↦−100, (1,1)↦9900`.
- **`not_separable`** (PROVED): no `(p,u)` witnesses `Separable U p u` — separability would force the
  interaction `U(0,0)+U(1,1) = U(0,1)+U(1,0)` (i.e. `9900 = −100`), false. So the decoupled-coincidence
  theorem **genuinely does not apply** here; the coupling is in `U`, not a fiat constraint.
- **`global_opt_dominates_all`** (PROVED): `globalOpt = (pay,pay) = 9900` is the **UNRESTRICTED** maximizer
  over all four policies — there is **no off-diagonal free lunch** (the would-be `(refuse,pay)` gives 0).
- The **severing kernel** `κ s a = update (fun _ ↦ 0) s a`: at *each* node, the EDT self predicts the
  *other* node frozen at refuse, so the matched-pay reward never fires. Hence the EDT-argmax is **refuse**
  at node 0 (`edt_argmax_is_refuse_s0`) **and** at node 1 (`edt_argmax_is_refuse_s1`); `edtPolicy =
  (refuse,refuse)` is the EDT-node-value maximizer at **both** nodes (`edtPolicy_is_edt_argmax`) — computed,
  not hand-projected.

**`mugging_edt_misses : U edtPolicy < U globalOpt`** (0 < 9900) — the EDT-conditional argmax (computed at
both nodes) STRICTLY diverges from the **unrestricted** global UDT optimum.
**`gap_is_acausal_payoff`**: `U globalOpt − U edtPolicy = 9900` **and** `U globalOpt − vNode 0 1 = 10000`
(the severed matched-pay reward the EDT self at node 0 failed to count, net of the −100 it did count).
**`correlated_kappa_agrees`**: with the *correlated* kernel `κcorr s a = fun _ ↦ a` (twin copies the
action), the matched-pay reward FIRES, so the EDT node value through the SAME `U` ranks PAY above refuse,
AGREEING with the optimum. So the divergence is caused **precisely by κ's severance — κ is load-bearing,
not inert.**
**`separability_load_bearing`** (the LEAN-CORE near-miss in the spec's "weaker hypothesis ⇒ FALSE" form):
dropping `Separable` (which `not_separable` shows fails here), `edt_decoupled_globally_optimal`'s conclusion
`∀ π, policyValue U π ≤ policyValue U edtPolicy` is **FALSE** — `globalOpt` strictly beats `edtPolicy`, and
`edtPolicy` genuinely IS the EDT-argmax at both nodes. So the decoupled hypothesis is load-bearing.

## 5. Shadow-test self-audit (each fake pattern, and why this isn't it)

- (a) *free per-node valuation re-introduced?* **No** — `vNode := U∘κ`; there is no free `node_value`.
- (b) *`split_eq_global`/`split_achieved` re-proved under a new name?* **No** — the new content is the
  κ-collapse `vNode_decoupled_eq`; the per-node optimality is derived from the EDT argmax, not assumed.
- (c) *`vNode` defined to definitionally equal the local argmax of `U` (κ inert)?* **No** — `vNode_via_kappa`
  shows κ in the value by `rfl`; `vNode_decoupled_eq` shows the off-`s` mass is κ's prediction; and the
  coupled `correlated_kappa_agrees` vs the severing κ give *different* argmaxes for the SAME `U`, proving κ
  changes the answer. Independently checked in `work/edt-node-value-sanity.py` (enumeration of all policies).
- (d) *only the decoupled case shipped?* **No** — the coupled near-miss `mugging_edt_misses` compiles with
  a strict gap equal to the acausal payoff, and the divergence is over the **unrestricted** optimum
  (`global_opt_dominates_all`), not a hand-projected diagonal.
- **Hypothesis-laundering ban:** the target objects — the EDT conditional `vNode` and the global UDT
  optimum `policyValue` — are **DEFINED** (`U∘κ`, `U`) and **CONCLUDED** about; neither is a hypothesis.
  No LI theorem, no asymptotic `≂ₙ`, no cross-agent martingale appears anywhere.

## 6. What this does and does NOT establish

**DID (kernel-checked, finite, real-algebra):**
1. A faithful EDT node-value `vNode = U∘κ` derived through an explicit kernel — no free input.
2. `vNode_decoupled_eq`: the κ-collapse showing the conditional reduces to the local `u`-argmax *only*
   under separability+decoupling, with κ's prediction supplying the (inert-for-argmax) off-`s` mass.
3. `edt_decoupled_globally_optimal`: the EDT-derived argmax policy attains the global UDT optimum in the
   decoupled regime — node_value DERIVED, inputs only `U` and `κ` (with structural witnesses naming the
   decoupling).
4. The mandatory coupled near-miss on a **genuinely non-separable** `U` (proved non-separable): a
   Twin/mugging instance where the SAME `U` with a severing κ makes the EDT argmax (computed at both nodes)
   provably miss the **unrestricted** UDT optimum, the gap = the acausal payoff; plus a correlated κ that
   agrees, certifying κ is load-bearing; plus the "weaker-hypothesis-⇒-FALSE" near-miss.

**Did NOT (out of scope / not claimed):**
- No claim about *which* κ is "correct" — κ is an explicit modeling input (the agent's self-prediction);
  the result is conditional on κ. (This is the honest content: deference reduces to whether the agent's
  self-model κ severs the relevant coupling. "Mugging-caver fails to defer" is now a **theorem about `U`
  and κ** — `mugging_edt_misses` — not a hand-fed verdict.)
- No LI / asymptotic / logical-uncertainty content; no `≂ₙ`; no cross-agent object. Pure finite shadow,
  exactly the agreed boundary.
- No biconditional with an independent "endorsement" predicate beyond the Value/optimality inequality.

**Bearing on the agenda (INTERPRETATION):** the round-1 D4 relation was "a wrapper around argmax with a
hand-fed discriminator." This file relocates the discriminator into an *explicit, inspectable* object —
the self-prediction kernel κ — and proves the EDT/UDT split is exactly the question of whether κ severs the
acausal coupling. The decoupled coincidence (updateful = updateless where κ severs nothing) and the coupled
divergence (mugging, where κ's severance costs exactly the acausal payoff) are both now machine theorems
about `(U, κ)`, not modeler choices.

## 7. Theorem inventory (all axioms `[propext, Classical.choice, Quot.sound]`)

`EDTNodeValue`: `vNode_decoupled_eq`, `vNode_argmax_of_u_argmax`, `edt_decoupled_globally_optimal`.
`EDTNodeValue.Decoupled` (non-vacuity witness): `edt_attains_global`, `vNode_via_kappa`, `edt_ranks_s0`,
`edtPolicy_is_edt_argmax`, `global_opt_value`, `all_zero_strictly_worse`.
`EDTNodeValue.Mugging` (coupled near-miss): `not_separable`, `edt_argmax_is_refuse_s0`,
`edt_argmax_is_refuse_s1`, `edtPolicy_is_edt_argmax`, `action_cases`, `global_opt_dominates_all`,
`mugging_edt_misses`, `gap_is_acausal_payoff`, `correlated_kappa_agrees`, `separability_load_bearing`.
