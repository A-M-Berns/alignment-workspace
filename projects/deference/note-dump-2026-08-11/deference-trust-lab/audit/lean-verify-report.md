# Lean-verify report — candidate files under `deference-trust-lab/lean/`

*Author: the dedicated Lean-verify agent (the ONLY agent permitted to run Lean). Each file
compiled SERIALLY (one at a time) via `lean/check.sh` against the prebuilt Mathlib in
`../lean-deference` (Lean v4.27.0). The pre-existing `lean-deference/LeanDeference.lean` was NOT
recompiled (treated as established `sorry`-free per v2 §9). Machine RAM ~7 GB; never ran two checks
concurrently; peak per-check load comfortably under budget.*

**Bottom line: ALL 11 candidate files now COMPILE cleanly (exit 0), every theorem in every file
depends ONLY on `[propext, Classical.choice, Quot.sound]` — NO `sorryAx` anywhere, NO `sorry`/`admit`
in any source.** The only change I made to any file was **adding missing imports** (the proofs were
already correct); I changed no statement and no proof body. Below: per-file verdict + the
faithfulness audit (does the checked Lean actually mean the informal claim?).

---

## What was wrong, and the one fix applied

Every failure was the **same class of bug: missing imports**, never a broken proof.

- Files using the `ℝ` notation (`merging-inductors`, `weak-endorsement`, `weak-endorsement-deference`,
  `UDT11Belief`, `unbounded-embedded-agency`, `updateless-deference`, `UpdatelessDeference`,
  `lateral-dtype`) imported only algebra/field modules, which do **not** transitively define `ℝ`. The
  symptom was a cascade of `failed to synthesize HMul ℝ ℝ`, `OfNat ℝ 1`, `LE ℝ` — i.e. `ℝ` was an
  uninterpreted type. **Fix:** add `import Mathlib.Data.Real.Basic`.
- Files generic over `[CommRing R]` (`legitimacy`, `legitimacy-corrigibility`) lacked the ring-class
  and tactic modules: `[CommRing R]` gave "type is not a class instance", and `ring`/`linarith` were
  "unknown tactic". **Fix:** add `Mathlib.Algebra.Order.Ring.Defs`, `Mathlib.Tactic.Ring`,
  `Mathlib.Tactic.Linarith`.

These are exactly the "Mathlib module paths" / targeted-import hazard the Template warns about. No
proof was altered. (Caveat for downstream: I edited only the `import` lines of the candidate files.
If a future run re-checks, the files are now self-contained and should pass as-is.)

---

## Per-file verdict

Legend: **COMPILES** = `check.sh` exit 0, no errors. **Axioms** = `#print axioms` output.
**Faithful?** = my INTERPRETATION of whether the kernel-checked statement means the informal claim
in the motivating model/findings file (the load-bearing column).

### 1. `merging-inductors.lean` — Fast-Student/Slow-Teacher merge (v2 §10, idea 3/4)
- **COMPILES:** yes (after adding `Real.Basic`). **Axioms:** all 3 thms `[propext, Classical.choice, Quot.sound]`.
- Theorems: `S_eq` (algebraic rewrite), `bias_only_hurts`, `unbiased_dominates`, `reversal_when_mu_small`.
- **Faithful? YES, and honestly scoped.** Claim: in the 2-option merge menu, the realized return
  `S μ σ = (1−μ)+σ(2μ−1)` is **monotone nondecreasing in the selector weight σ** when `μ ≥ 1/2`, so a
  downward feedback bias can only lower the deferred return. The Lean proves exactly this; `μ ≥ 1/2`
  is genuinely load-bearing (`reversal_when_mu_small` exhibits the sign flip at `μ=0`, so the
  statement is non-vacuous and no sign is smuggled). **Correctly does NOT claim:** that `B` is a
  logical inductor, the cross-agent martingale (idea 3 "Hop 2", the real open step), or any
  asymptotic `≂ₙ`. It isolates the orthogonal finite fact "bias only hurts" — faithful and modest.

### 2. `legitimacy.lean` — drug/addiction = anticipated deference failure (idea L2)
- **COMPILES:** yes (after adding ring/order/tactic imports). **Axioms:** both thms standard.
- Theorems: `legitimacy_defect_decomp` (linearity), `drug_defect_sign`.
- **Faithful? YES.** (1) is the legitimacy analog of `Deference.decomposition`: universal in a
  `CommRing`, no frame hypothesis — strong & faithful. (2): if the drugged expert pointwise overstates
  the target (`θ_x ≤ Eθ_x`) on nonnegative novice mass/weight, the legitimacy defect is `≤ 0`. The
  hypothesis is **pointwise**, the conclusion is the **signed weighted sum** — a genuine monotonicity
  step, not a restatement; non-vacuous. Correctly flags it does NOT model the LI asymptotic
  "anticipation" nor no-Dutch-book abstention.

### 3. `legitimacy-corrigibility.lean` — drug (L2) + corrigibility-as-endorsement (L3)
- **COMPILES:** yes (same import fix). **Axioms:** all 5 thms standard.
- Theorems: `defect_decomp`, `wirehead_declined`, `comply_iff_endorsed`, `endorsed_signal_complies`,
  `adversarial_signal_resists`.
- **Faithful? YES, with the encoding caveat the file itself flags.** The corrigibility pivot
  `complyAdv = Σ π_x s_x (2 d_x − 1)` is exact linearity. `endorsed_signal_complies` (fires only on
  danger ⇒ comply preferred) and `adversarial_signal_resists` (fires only on safety ⇒ resist
  preferred) are **duals via `d ↔ 1−d`**, each non-vacuous (opposite hypothesis makes the conclusion
  false). This is the **most valuable structural content**: the SAME weighted-sum machinery flips
  sign on a non-endorsed shutdown — the formal limit of corrigibility-as-endorsement. Honest caveat
  (in-file): "signal is endorsement-faithful" is a *modeling encoding* (`s·(2d−1) ≥ 0` pointwise),
  not derived from a cross-martingale; same honesty boundary as `LeanDeference.lean`.

### 4. `weak-endorsement.lean` — equality endorsement ⇒ immodesty (idea 1; S5/Gödel pivot)
- **COMPILES:** yes (added `Real.Basic` + `Linarith`). **Axioms:** both thms standard.
- Theorems: `equality_endorsement_implies_immodest`, `immodest_satisfies_immodesty`.
- **Faithful? YES.** This is the lab's **independent re-proof** of `DeferenceExtra.CM_implies_immodest`
  (v2 §5.2's one-line tail), restated in the lab namespace with fast imports. `hCM` (∀ X, expert
  credence = novice conditional on its own fiber) is the hard conditional-martingale identity; the
  conclusion `Σ P_w v · 1[fiber]=1` (immodesty) is obtained by *instantiating* `hCM` at the fiber
  indicator (idempotence collapses the quotient), not assumed. `hw : 0 < π w` makes the denominator
  positive (the load-bearing "w sees itself"). Lemma (B) supplies a non-vacuity witness (an immodest
  probability vector attains `=1`; a modest one gives `<1`). **Correctly does NOT** formalize the
  soft⇒hard spectral-gap reduction — the actual infinite-frame impossibility content, prose only
  (same gap as the confirmed file, decl 8).

### 5. `weak-endorsement-deference.lean` — soft vs hard liar split (LI §4.12, eq. 2118)
- **COMPILES:** yes (added `Real.Basic`). **Axioms:** all 4 thms standard.
- Theorems: `hard_endorsement_liar_unsat` (⇒ `False`), `soft_endorsement_liar_sat`, two numeric witnesses.
- **Faithful? YES — and this is one of the crispest results.** (A): the four scalars
  `0<t`, `0<Ew`, `Exw=0` (disprovable conjunction), `Exw=t·Ew` (HARD two-sided endorsement) are
  **jointly inconsistent**. The proof genuinely USES `hw : 0 < Ew` (it derives `Ew=0` and clashes),
  so it is non-vacuous: dropping `hw` makes the system consistent (`0=t·0`). This faithfully renders
  "hard endorsement + the probabilistic liar ⇒ contradiction". (B) + witnesses show the SOFT (`≥`,
  Self-Trust shape) relaxation is satisfiable on the SAME data — so the impossibility is a property
  of the **equality `=`**, not of the liar. **Correctly INPUTS** (does not re-derive) the LI facts
  `Exw=0` and `0<Ew`; no diagonal lemma, no LUVs. Honest finite/algebraic skeleton of the wall.

### 6. `UDT11Belief.lean` — "UDT1.0 believes it's UDT1.1 ⇒ ε-optimal" (algebraic core)
- **COMPILES:** yes (added `Real.Basic`). **Axioms:** all 3 thms standard.
- Theorems: `epsilon_optimal_of_belief`, `epsilon_optimal_clean` (δ≤1/2 ⇒ 2δ·range form), `optimal_of_certain`.
- **Faithful? YES, and the bound is the *corrected* honest one.** Conclusion
  `(1−δ)(Vstar pstar − Vstar s) ≤ δ(hi−lo)` keeps the `(1−δ)` factor on the LHS — i.e. it does NOT
  assert the naive `δ·range` gap (the model doc §0/§5 shows the naive bound genuinely fails at
  δ=2/3). Proved for **arbitrary** `pstar` (not assumed optimal) — the strongest form; `hsel` (s
  maximizes believed value) is correctly a hypothesis, and `Vother` is arbitrary in `[lo,hi]` (that
  arbitrariness IS the strength). **Honest boundary (in-file + model §6):** the pointwise→whole-policy
  reduction is ASSUMED in `hsel`; this file is the whole-policy shadow, not the embedded theorem.

### 7. `unbounded-embedded-agency.lean` — same core + self/env split + Stag-Hunt bridge
- **COMPILES:** yes (added `Real.Basic`). **Axioms:** all 5 thms standard. (Compiler emitted only
  *unused-variable warnings*, which are non-fatal and are themselves load-bearing — see below.)
- Theorems: `epsilon_optimal_of_belief`, `epsilon_optimal_split`, `optimal_of_certain`,
  `stag_hunt_select`, `stag_hunt_trap`.
- **Faithful? YES — and two warnings CONFIRM the claimed fidelity rather than undermining it:**
  - `epsilon_optimal_split` carries an **unused `δm`** (substrate-stability parameter). The compiler's
    `unused variable δm` warning is exactly the **formal content** the model doc §4/§6 claims: the
    optimality certificate is δm-AGNOSTIC (depends only on behavioural self-knowledge δb). An unused
    binder is not a smuggled conclusion; it is the claim. **Verified: `δm` appears only in the
    signature, in no hypothesis and no proof step.**
  - `stag_hunt_select` has **unused `hb : 0<b`, `hc : 0≤c`**: the proof closes by `linarith [hgap]`
    alone. So the non-degeneracy hypotheses are *inert* (the conclusion `c ≤ (1−δ)·b` follows from
    `hgap : (1−δ)·b ≥ c` directly). This is harmless (`hb`/`hc` are prose scaffolding) and the model
    §6 already flags them as "non-degeneracy prose only" — faithful, but a reader should know the
    checked statement is the bare inequality `hgap ⇒ c ≤ (1−δ)b`, true for any `b,c`.
  - `stag_hunt_trap` (converse: `(1−δ)b < c` ⇒ Stag strictly worse) is faithful and witnesses that
    the gap hypothesis is load-bearing, not slack.
  - **Honest boundary:** theorems 1–2 are whole-policy choosers; the pointwise→whole-policy bridge is
    proved ONLY in the symmetric 2×2 Stag Hunt (theorem 3) and CONJECTURED in general. The Lean does
    not smuggle a general bridge.

### 8. `updateless-deference.lean` (namespace `UpdatelessDeference2`) — separable ⇒ updateless=updateful
- **COMPILES:** yes (added `Real.Basic`). **Axioms:** both thms standard.
- Theorems: `defers_of_local_argmax`, `endorsement_reduction`.
- **Faithful? YES.** With a **separable** utility `U : S → A → ℝ` (the structural encoding of "no
  cross-situation coupling" — a coupled problem would need `U : (S→A) → ℝ`), a per-node argmax
  `nodeChoice` dominates every policy in the global expectation. `nodeChoice` is constrained to be a
  per-node argmax by `hLoc`; it is NOT assumed a global argmax — that is the conclusion. Non-vacuous:
  fails for coupled `U` (the mugging/Newcomb witness, in the `.py` checker, not here). Correctly does
  NOT prove the coupled (non-deference) direction.

### 9. `UpdatelessDeference.lean` (namespace `UpdatelessDeference`) — split optimum = global optimum
- **COMPILES:** yes (added `Real.Basic`). **Axioms:** both thms standard. **The flagged `sup'`
  proof-irrelevance defeq spot (line 111, `Finset.le_sup'`) checked successfully** — no repair needed.
- Theorems: `split_eq_global` (split optimum dominates every policy), `split_achieved` (a local-argmax
  policy attains it).
- **Faithful? YES.** Companion to #8 using `Finset.sup'`: separability ⇒ the per-situation-max
  aggregate is both an upper bound on every policy value AND achieved. Genuinely "global = sum of
  locals" for decoupled utility; would fail for a coupled `U`. Non-vacuous.

### 10. `lateral-dtype.lean` — "why ain'cha rich" / systematized-winning face of CM ⇒ Value
- **COMPILES:** yes (added `Real.Basic`). **Axioms:** all 3 thms standard.
- Theorems: `WAR_of_martingale`, `WIN_of_argmax`, `WAR_of_argmax`.
- **Faithful? YES.** A re-skin of the δ=0 `value_of_CM` content in optimality language: under CM
  (`Ediag = Σ α_j Eo_j`), UM (`Eopt = Eo`), and WIN (α-weighted verdict dominates each verdict), the
  realized return beats every fixed option (`∀ i, Eopt i ≤ Ediag`). The proof chain
  `Eopt i =(UM) Eo i ≤(WIN) Σα Eo =(CM) Ediag` shows WIN does the work and none of CM/UM/WIN IS the
  conclusion (no smuggling). `WIN_of_argmax` discharges WIN for the hard-argmax (point-mass) selector
  via `Finset.sum_ite_eq'` — the flagged `simp` collapse worked. Non-vacuous (`Eo=(1,0)`, `α=(1,0)`
  gives a strict inequality). Correctly the δ=0 idealization; says nothing about the −δ log k slack or
  asymptotics.

---

## What is now machine-checked vs still informal — honest overall statement

**Machine-checked (kernel-verified, standard axioms only):** the **finite, exact, real-arithmetic /
ring-algebraic CORES** of every model thread the lab produced this run:

- the **softmax-bias monotonicity** ("bias only hurts") of the inductor merge (#1);
- the **legitimacy-defect decomposition** and its **sign under a drug/over-stating expert** (#2,#3);
- the **corrigibility sign-flip duality** (endorsed-signal ⇒ comply / adversarial-signal ⇒ resist),
  the crispest *limit* result — corrigibility-as-endorsement cannot be unconditional (#3);
- **equality-endorsement ⇒ immodesty** (independent re-proof of the v2 §5.2 tail) (#4);
- the **hard-liar contradiction vs soft-liar satisfiability** split — equality endorsement collides
  with the probabilistic liar, the one-sided Self-Trust form does not (#5);
- the **"believe-you're-UDT1.1 ⇒ ε-optimal" bound** with the *corrected* `δ/(1−δ)·range` constant,
  the **δm-agnostic self/env split**, and the **2×2 Stag-Hunt selection bridge + its converse**
  (#6,#7);
- **separable ⇒ updateless = updateful** (two independent formulations) — the coherence half of the
  Geometric-UDT split (#8,#9);
- the **"why-ain'cha-rich"/optimality re-skin** of conditional-martingale ⇒ Value (#10).

**NOT machine-checked (remains informal / prose / Python-only), as each file honestly states:**

- **No logical-induction machinery is formalized anywhere.** All LI theorems (`ccee`, `cee`, `loe`,
  `expprovind`, recurring-unbiasedness, the diagonal lemma) enter, where relevant, as **named
  hypotheses or scalar inputs** — never proved. Same boundary as the confirmed `LeanDeference.lean`.
- The **soft⇒hard "no spectral gap" reduction** (v2 §5.2) — the actual infinite-frame *impossibility*
  content and the only place finiteness is forced — is prose in #4 (as in the confirmed decl 8).
- The **cross-agent martingale** `E^H_t(X·w) ≂ E^H_t(B·w)` (merge "Hop 2", #1) and the **coupled**
  (mugging/Newcomb) non-deference direction (#8/#9) are by-hand / Python-checked, not Lean.
- The **pointwise→whole-policy bridge** in general games (#6/#7) is CONJECTURE; proved only in the toy
  Stag Hunt.
- The **asymptotic `≂ₙ`/`≳ₙ` layer** is not touched by any new candidate (it lives in the confirmed
  `LeanDeference.value_asymptotic`).

**Two fidelity items a reader must keep in mind (not bugs, but real):**
1. `unbounded-embedded-agency.stag_hunt_select`'s `hb`/`hc` are **inert** — the checked statement is
   the bare `hgap ⇒ c ≤ (1−δ)b`. Faithful to the worst-case best-response comparison, but the
   non-degeneracy framing is prose, not enforced by the kernel.
2. Every "endorsed/adversarial/separable/drug" hypothesis is a **structural or pointwise encoding** of
   the informal condition, integrated by elementary monotonicity — faithful and non-vacuous, but it is
   the *finite shadow* of the LI/asymptotic statement, never the LI statement itself. This is the
   uniform honesty boundary across the lab, identical to `LeanDeference.lean`.

**Net:** the lab's new Lean corpus is now, like the original, **fully kernel-checked and `sorry`-free
on the standard axiom base**, and each checked theorem **faithfully captures the finite algebraic core**
of its model — with the LI / asymptotic / impossibility content correctly left as flagged
hypotheses-and-prose, exactly as the source files claim.
