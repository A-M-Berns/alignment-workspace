# Red-team verdict: "Unbounded embedded agency / UDT1.0-believes-UDT1.1 ⇒ ε-optimal"

Target: `models/unbounded-embedded-agency-model.md`, `lean/unbounded-embedded-agency.lean`,
`unbounded_embedded_agency_micro.py`. All read; Python run (passes); Lean read, **not** compiled.

## Verdict: **SALVAGEABLE** (one honest fix). The math is correct; the *headline rhetoric* over-claims.

The algebraic core is **SOLID** and the Lean almost certainly type-checks. The one real defect is
**interpretive, not algebraic**: the celebrated "principal's naive bound undershoots; the honest
bound is `δ/(1-δ)·range`" claim is **contingent on a modelling choice (R2) that is not the most
natural reading of the principal's phrase**, and under the natural reading (R1) the principal's
`δ·range` is *correct*. The doc presents the correction as if it refutes the principal; it only
refutes one of two formalizations.

---

### (a) Is the central claim TRUE? — YES algebraically; the "correction" is formalization-dependent.

- **Prop 1 / `epsilon_optimal_of_belief` is robustly true.** 400k random trials, no violation — and
  it holds even *outside* the stated regime: `δ>1` (Lean only assumes `0≤δ`) and `Vstar` wildly
  unbounded (Lean only bounds `Vother`) both preserve the inequality, because the proof is pure
  linear algebra from `Bel(pstar)≤Bel(s)` + `δ·lo≤δ·Vother(pstar)` + `δ·Vother(s)≤δ·hi`. **The bound
  is asymptotically tight** (constructed a menu where `(1-δ)Δ → δ·range` from below), so it is
  **non-vacuous**. No counterexample exists.

- **But the "1/(1-δ) correction" is an artifact of the R2 belief model, and is the sharpest stress
  point.** The doc models "the agent (1-δ)-believes its policy is UDT1.1" as
  **R2: maximize a mixture of *value maps* `Bel=(1-δ)Vstar+δVother`** with adversarial `Vother`.
  The principal's phrase reads more naturally as **R1: with prob 1-δ my *realized policy* equals
  π_star**. These are different objects:
  - Under **R2**, an adversarial `Vother` can **pull the argmax onto a decoy** `s≠π_star` (in the
    doc's own micro-example at δ=¼ the chooser picks `c`, *not* π_star=`b`!), and the gap genuinely
    inflates to `δ/(1-δ)·range`.
  - Under **R1** (commit to whatever you believe π_star is; play π_star w.p. ≥1-δ, else anything),
    `E[gap] ≤ δ(V_star(π_star)-lo) ≤ δ·range` — **the principal's "naive" `δ·range` is exactly
    right** (verified, 100k trials, no `1/(1-δ)`).

  So the dramatic "naive bound undershoots at δ=2/3" result **does not show the principal was
  wrong**; it shows that *if* you adopt the contaminated-objective model R2, the bound is worse. The
  doc's §0 does describe R2 ("belief about who authored your decisions"), so the model is
  **internally consistent** — but the abstract/§9 rhetoric ("the principal's naive δ·range
  undershoots", "the correction is real") is **over-stated**: it silently presupposes R2.

### (b) Does a hypothesis smuggle the conclusion? — NO for Prop 1; near-trivial for Prop 2.

- `hsel` ("s maximizes `Bel`") does **not** smuggle the conclusion: the conclusion is about `Vstar`,
  `hsel` is about `Bel`, and the whole content is *how far* a Bel-maximizer can be from Vstar-optimal.
  The doc is honest that the pointwise→whole-policy reduction lives entirely in `hsel` (caveat 3).
- `stag_hunt_select` is **algebraically near-trivial**: after `unfold`+`simp`, the goal is `c ≤
  (1-δ)*b` and the hypothesis `hgap` *is* `(1-δ)*b ≥ c` — `linarith` is essentially `exact hgap`.
  `hb,hc` are genuinely unused. **All the value is in the docstring interpretation** that `(1-δ)*b`
  and `c` are the two expected utilities; the Lean itself proves a rearrangement. Not a smuggle, but
  not substantive content either — the "discharged bridge" is one line of arithmetic.

### (c) Lean prediction (READ ONLY — for the Lean-verify agent).

Predicted: **all five theorems type-check, axioms clean** `[propext, Classical.choice, Quot.sound]`.
Imports (`Algebra.Order.Field.Basic`, `Tactic.Linarith`) are fine, no `import Mathlib`.
- `epsilon_optimal_of_belief`: goal = linear combo of `key + hδhiO + hδloO` after ring-normalization
  (coefficients 1,1,1). `nlinarith` will close it; `linarith` would too post-`ring_nf`. **✓**
- `epsilon_optimal_split`: literally `epsilon_optimal_of_belief` at `δ:=δb`; `δm` appears **only in
  the binder**, in no hypothesis/step. **Verify agent: confirm `δm` truly unused** — that unusedness
  *is* the claim (δm-agnosticism). Faithful, non-vacuous. **✓**
- `optimal_of_certain`: `simp only [sub_zero,one_mul,zero_mul,add_zero]` should reduce `Bel 0` to
  `Vstar`, then `exact key`. **Minor risk**: if simp's normal form isn't exactly `Vstar pstar ≤
  Vstar s`, `exact` fails. **Recommend `linarith [key]` instead of `exact key`** as a robust fallback
  (cheap, removes the only fragile step). **✓ likely.**
- `stag_hunt_select` / `stag_hunt_trap`: `unfold`+`simp only [if_true]`+`linarith`. **✓** (the prompt's
  own note about `≥`/`≤` orientation is correct — `linarith` handles it.)

**Faithfulness flags for verify agent:** (i) `stag_hunt_select` drops the `δ*payoffStag b false`
term from EU_S — sound *only* because `payoffStag b false = 0`; the "Stag-vs-Hare pays 0"
assumption is encoded by omission, not stated. (ii) The conclusion captures "EU_H ≤ EU_S" only under
the worst-case belief `q=1-δ`; that `q=1-δ` is the worst case is argued in prose, not in Lean. (iii)
None of the Lean theorems mention `δ≤1-c/b` symbolically — that framing is docstring-only.

### (d) Smallest change to fix.

**Add one paragraph (and soften §0/§9) stating that the `δ/(1-δ)` correction is specific to the
R2 "mixture-of-value-maps / adversarial author" model, and that under the R1 "believe-my-policy-is-
π_star" reading the principal's `δ·range` is correct.** That single disclosure converts an
over-claim into a genuine and *interesting* result: *which formalization of "believe you're UDT1.1"
you pick determines whether self-belief is cheap (R1) or adversarially exploitable (R2)* — and the
gap between them is itself the trust-relevant content (an agent that optimizes a belief-contaminated
objective can be steered onto a decoy). Optionally swap `exact key`→`linarith [key]` in
`optimal_of_certain` for robustness.

### Single most valuable next step.

**Formalize R1 as a second Lean theorem** (`E[Vstar(s)] ≥ (1-δ)Vstar(π_star)+δ·lo ⇒ gap ≤ δ·range`)
right beside `epsilon_optimal_of_belief`, and state the **R1-vs-R2 contrast as the headline result**.
The lab's payoff is precisely this dichotomy: it pinpoints that justified human→AI trust depends on
*whether the AI's self-belief is a belief-about-its-own-policy (safe) or an objective it optimizes
against an adversarial alternative (exploitable)* — a sharper claim than the current "the bound is
δ/(1-δ)".
