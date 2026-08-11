# Faithfulness-gate verdict — TODO `edt-node-value`

**Role:** independent skeptic (success metric = finding fakeness). **Modality:** LEAN-CORE.
**VERDICT: REAL** — faithful to the informal claim, non-vacuous, target objects not assumed; both
the decoupled-coincidence theorem and the mandatory coupled near-miss are kernel-checked, and an
independent hypothesis-inertness battery confirms every load-bearing hypothesis (including κ's
*decoupling structure*) is genuinely load-bearing and κ is not inert.

Deliverable under attack:
- `run2/lean/edt-node-value.lean` (19 theorems).
- `run2/work/edt-node-value.md` (writeup).
- `run2/work/edt-node-value-sanity.py` (independent enumeration).
Attack file: `run2/verify/edt-node-value-attack.lean` (5 attack theorems, all kernel-checked clean).

---

## 1. Baseline reproduction — executor's report is ACCURATE

`bash lean/check.sh run2/lean/edt-node-value.lean` → **EXIT 0**, sorry-free. All 19 `#print axioms`
report `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`**. Only two cosmetic linter
warnings (an unused section variable on `vNode_decoupled_eq`; a `<;>` style note). Matches the report
exactly (19 theorems, clean axioms).

Python `edt-node-value-sanity.py` → **all assertions pass**, PYEXIT 0. Independent enumeration of all
four policies for both instances reproduces every number: decoupled EDT-argmax `(1,0)` attains global
optimum 7 (gap 0); mugging severing-κ EDT-argmax `(refuse,refuse)=0` misses the unrestricted optimum
`(pay,pay)=9900` (gap 9900); correlated-κ argmax `(pay,pay)` agrees; and the same-U argmax FLIPS
between κ's (`(0,0)` vs `(1,1)`).

## 2. The target objects are DEFINED, not assumed (no hypothesis-laundering)

- `vNode U κ s a := U (κ s a)` — the EDT-conditional is **defined** as `U∘κ`, κ literally inside.
- `policyValue U π := U π` — the global UDT objective is **defined**.
- Both theorems **conclude** about these objects. Neither `vNode`, `policyValue`, nor any LI /
  asymptotic / cross-agent object appears as a hypothesis. The banned target objects are absent.
- `vNode_via_kappa : vNode U κ 0 1 = U (Function.update (base 0) 0 1)` holds by `rfl` — κ is in the
  value definitionally, confirmed.

## 3. HYPOTHESIS-INERTNESS battery (`edt-node-value-attack.lean`, EXIT 0, all axioms clean)

The headline decoupled theorem `edt_decoupled_globally_optimal` has four hypotheses: `hSep`
(Separable), `hDec` (Decoupled κ), `_hp` (p ≥ 0, author already flags as unused), and `hEDT` (π★ is an
EDT-node-value argmax). I built concrete counter-instances satisfying ALL-BUT-ONE and showed the
conclusion FAILS — each kernel-checked.

- **`A1_hDec_load_bearing` (the decisive κ-structure test).** A separable `U`, but a **non-decoupled**
  "deceiving" kernel `κbad s a = update (allRefuse) s (flip a)` that reports the policy playing the
  *flipped* action at s. Proven `κbad_not_decoupled : ¬∃ base, Decoupled κbad base`. This instance
  satisfies `hSep`, `hp`, AND `hEDT` (`edtPolicyBad=(0,1)` genuinely maximizes `vNode U κbad`), yet
  the conclusion `∀ π, policyValue U π ≤ policyValue U edtPolicyBad` is **FALSE** (global opt `(1,0)=7`
  beats `edtPolicyBad`=3). ⇒ **`hDec` (the decoupling STRUCTURE of κ) is load-bearing**, not just κ's
  presence. This is the strongest possible refutation of "κ inert / vNode = relabel of local argmax":
  a different κ on the SAME separable U flips the EDT-argmax to the wrong action.
- **`A2_hSep_load_bearing`.** The non-separable mugging `U` with a decoupled κ (so `hDec` holds, `hSep`
  fails): `hDec` + `hEDT` hold, conclusion FALSE (`globalOpt=(pay,pay)=9900` beats `edtPolicy=0`).
  ⇒ `hSep` load-bearing. (Re-confirms the original `separability_load_bearing` independently.)
- **`A3_hEDT_load_bearing`.** A separable U with an arbitrary BAD π★ (not an EDT-argmax): `hSep`, `hp`
  hold, conclusion FALSE. ⇒ `hEDT` load-bearing (no free pass).
- **`conclusion_not_trivial`.** Exhibits `(U, π★)` with `¬ ∀ π, policyValue U π ≤ policyValue U π★`.
  ⇒ the conclusion is NOT a triviality provable with no/weak hypotheses (CONCLUSION-TRIVIALITY attack
  defeated).
- **`KInert.kappa_changes_argmax`.** SAME `U`, severing κ ranks refuse > pay at node 0
  (`vNode 0 1 < vNode 0 0`), correlated κ ranks pay > refuse (`vNode 0 0 < vNode 0 1`). κ flips the
  per-node argmax. ⇒ κ is NOT inert; `vNode` is not a κ-independent relabel of any fixed local argmax
  of U (shadow-test (c) defeated).

`_hp` (p ≥ 0) is genuinely unused — the author discloses this honestly in both the Lean comment and
the writeup §2. Not a defect: a marginally-more-general theorem, transparently flagged.

## 4. Shadow-test checklist (the four patterns the spec warns about)

- **(a) free per-node valuation re-introduced?** NO. `vNode := U∘κ`; there is no free `node_value`
  anywhere. The round-1 sin (CRITIQUE §3: "node_value a free input never tied to U") is removed; this
  file implements exactly the fix the critique recommended ("derive node_value as the EDT-conditional
  of U").
- **(b) `split_eq_global`/`split_achieved` re-proved under a new name?** NO. Compared to round-1
  `UpdatelessDeference.lean`: round-1 uses the **decoupled type** `U : S → A → ℝ` with
  `policyValue := ∑ s, p s · U s (π s)` and proves dominance by `Finset.le_sup'` over a **hand-fed
  local argmax**. Run-2 uses the **coupled type** `U : (S→A) → ℝ`, `policyValue := U`, and DERIVES the
  local-optimality of π★ from the `vNode`-argmax THROUGH κ via the new lemma `vNode_decoupled_eq` (the
  κ-collapse — absent in round-1). The final `Finset.sum_le_sum` is generic monotonicity plumbing, not
  a re-skin; the genuinely new content is `vNode_decoupled_eq` + `vNode_argmax_of_u_argmax`.
- **(c) `vNode` definitionally = local argmax of U (κ inert)?** NO. Defeated by
  `KInert.kappa_changes_argmax` AND `A1_hDec_load_bearing` (a structurally different κ flips the
  argmax on the SAME U).
- **(d) only the decoupled case shipped (no coupled near-miss)?** NO. The mandatory coupled near-miss
  `mugging_edt_misses : U edtPolicy < U globalOpt` (0 < 9900) compiles, on a **genuinely non-separable**
  U (`not_separable` PROVED: separability would force `9900 = −100`), with `globalOpt` the
  **unrestricted** maximizer over all four policies (`global_opt_dominates_all`) — NOT a
  diagonal-by-fiat — and the EDT-argmax computed at BOTH nodes (`edtPolicy_is_edt_argmax`), no
  hand-projection.

## 5. The round-1-sin-in-disguise the executor caught and fixed — VERIFIED genuine

The writeup's honesty note (§ top, and §4) documents that an earlier draft used a **separable**
`U = −100·[π₀=pay] + 10000·[π₁=pay]` and declared the optimum to be the diagonal "by coherence" — a
hand-projection shadow (the real unrestricted argmax of that separable U is `(refuse,pay)=10000`, no
divergence). The shipped file replaces it with a **non-separable matched-pay** U so `(pay,pay)` is the
genuine unrestricted maximizer. I CONFIRMED this is real: `Mugging.not_separable` is kernel-checked
(interaction term 10000 ≠ 0), `global_opt_dominates_all` is kernel-checked over all four policies, and
my independent A2 attack reproduces the strict miss. The fix is genuine, not cosmetic. This is exactly
the kind of self-caught fake the round-2 gate wants to see eliminated — and it was.

## 6. Faithfulness of the "gap = acausal payoff" framing (minor, fully disclosed)

`gap_is_acausal_payoff` proves TWO numbers: the policy-value gap `U globalOpt − U edtPolicy = 9900`
AND the severed reward `U globalOpt − vNode 0 1 = 10000`. The raw acausal reward in U is `+10000`; the
policy-value gap is `9900 = 10000 − 100` (the own-cost the optimum also pays). The spec phrase "gap
being exactly the acausal payoff" is satisfied in structure (the divergence is caused by, and equal up
to the disclosed own-cost to, the severed acausal term), and BOTH numbers are exposed with the
relationship spelled out in the writeup. `correlated_kappa_agrees` closes the loop (restore the
correlation → divergence vanishes). Honest disclosure, not laundering. Not a fakeness finding.

## 7. What is REAL vs. what is NOT established (honest boundary)

**REAL (kernel-checked, finite, real-algebra):**
1. A faithful EDT node-value `vNode = U∘κ` routed through an explicit, inspectable self-prediction
   kernel — the round-1 free `node_value` is genuinely removed.
2. `vNode_decoupled_eq` — the κ-collapse (new content; the off-s mass is κ's prediction `base s`).
3. `edt_decoupled_globally_optimal` — EDT-derived argmax attains the global UDT optimum in the
   decoupled regime, with κ (and its decoupling structure) verifiably load-bearing.
4. The mandatory coupled near-miss on a genuinely non-separable U: strict divergence = the severed
   acausal payoff, with a correlated κ that agrees, proving κ load-bearing.

**NOT established (correctly out of scope, and the executor says so):**
- No claim about WHICH κ is "correct" — κ is an explicit modeling input; results are conditional on κ.
  (This is the honest reframing: "mugging-caver fails to defer" is now a *theorem about (U, κ)*, not a
  hand-fed verdict — a genuine advance over round-1's tautology.)
- No LI / asymptotic `≂ₙ` / cross-agent-martingale content — none claimed, none smuggled. Pure finite
  shadow, the agreed LEAN-CORE boundary.
- The correlated-κ "agreement" is proved only at node 0 (`correlated_kappa_agrees`), not as a full
  whole-policy optimality theorem; the Python confirms the full agreement but the Lean states the
  weaker node-0 ranking. This is a slight under-claim, not an over-claim — fine.

## VERDICT: **REAL**

Faithful to the informal claim (EDT-conditional derived through κ, decoupled coincidence + mandatory
coupled near-miss), non-vacuous (concrete `decide`/`norm_num` witnesses both sides), target objects
defined-and-concluded-about (not hypotheses), and every load-bearing hypothesis — crucially including
κ's decoupling STRUCTURE, not merely κ's presence — independently confirmed load-bearing by a
kernel-checked counter-instance battery. The settling attack: a SEPARABLE U with a non-decoupled
"deceiving" κ (proven `¬∃base, Decoupled`) satisfies every other hypothesis yet drives the EDT-argmax
to the wrong action, so the conclusion fails — κ is doing real work and `vNode` is not a relabel of the
local argmax. No shadow, no laundering, no diagonal-by-fiat (the disguised shadow was caught and
genuinely removed by the executor).
