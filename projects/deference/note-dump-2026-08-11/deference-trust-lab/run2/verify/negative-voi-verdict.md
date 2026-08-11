# Faithfulness-gate verdict — TODO `negative-voi`

**Verdict: REAL** (faithful to the informal claim, non-vacuous, target object not assumed).

Independent skeptic attack on `run2/lean/negative-voi.lean` (+ `work/negative-voi.py`,
`work/negative-voi.md`). Success metric for this gate = *finding fakeness*. I did not find any;
the example is a genuine build of Weatherson's 3-world VoI-tightness frame.

---

## 0. What the claim is, and what would make it fake

CLAIM: a finite 3-world prior frame with two S4 experts E1 (finer) and E2 (coarser, **non-
partitional**) and a menu O, such that with **recommended strategy = genuine argmax of the
expert's own posterior** for BOTH, (i) `Value E1 < Value E2` STRICTLY (negative VoI), and
(ii) a NEAR-MISS: replacing E2 by a partitional anchor Q (E1 still refines it) restores
`Value E1 ≥ Value Q` (Blackwell–Geanakoplos). This is the "cited-but-unbuilt" example in
v2 §1.1 (confirmed: `deference-in-logical-induction-v2.md:241` — "a 3-world example where both
experiments are reflexive-transitive-nested (with E₂ non-partitional) and the less informative
one has higher expected return"). Modality LEAN-CORE: a finite decidable ℚ fact.

Ways it could be fake (from the spec's shadow_test):
- (a) `recOpt` defined adversarially / not as argmax-of-own-posterior (so the gap is a
  hand-tuned artifact, not an information effect);
- (b) "E2 better" smuggled in as a hypothesis;
- (c) only the strict inequality shipped, no near-miss ⇒ looks like an arithmetic artifact.

The headline `negative_VoI : Value E1 < Value E2` has **NO hypotheses** — it is a closed ℚ
computation over the concrete `π, O, E1, E2, recOpt`. So classic hypothesis-LAUNDERING
(assuming the hard object) is *structurally impossible* here: there is nothing to delete. The
live attack surface is therefore (a) "is recOpt honest?" and (c) "does the near-miss really
flip the sign / is the gap an artifact?". I attacked both, hard.

---

## 1. Baseline — the ORIGINAL file is genuinely kernel-checked

`bash lean/check.sh run2/lean/negative-voi.lean` → **exit 0**, 0 `sorryAx`, 0 errors (only
style linter warnings). Every theorem's axiom report ⊆ `[propext, Classical.choice,
Quot.sound]`; the `decide`-proved structural lemmas use only `[propext]`. Not a fake compile.

`python3 work/negative-voi.py` → reproduces V(E1)=4/9, V(E2)=5/9, V(Q)=4/9; `ALL CHECKS PASS`
(72 strict negative-VoI instances, 0 with partitional coarser, 0 refine-a-partition losses).

---

## 2. HYPOTHESIS-INERTNESS / CONCLUSION-TRIVIALITY attack

Attack file: `run2/verify/negative-voi-attack.lean` → **exit 0, 0 sorryAx, axioms clean**
(`[propext]` / `[propext, Classical.choice, Quot.sound]` per lemma). It re-implements an
INDEPENDENT, menu-parameterized recOpt (`recOptM M E w`) and re-derives every load-bearing fact
about the SAME objects, *without* trusting the author's lemmas:

- **A3 (recOpt is FORCED, not hand-tuned).** `A3_recOpt_E1/E2/Q` re-prove the per-world choices
  recOpt(E1)=[1,0,1], recOpt(E2)=[1,0,0], recOpt(Q)=[1,0,1] straight from the argmax rule on the
  original menu. They match the author's. → the recommended choices are computed, not asserted.
- **A1/A2 (recOpt is genuinely DATA-DRIVEN).** Feed the SAME rule an adversarial menu where
  option 1 dominates everywhere: `A1_E1_all_one / A1_E2_all_one` ⇒ recOpt = 1 at every world.
  Feed a menu where option 0 dominates: `A2_*_all_zero` ⇒ recOpt = 0 everywhere. So recOpt is
  NOT a constant returning the cherry-picked answer — it tracks the menu. **Shadow-(a) defeated**
  beyond the author's own `recOpt_eq_posterior_argmax` (which I also confirmed compiles in the
  original: numerator-argmax = normalized-posterior-argmax, justified by `condMass_pos`).
- **A4 / A5 (CONCLUSION-TRIVIALITY — the gap is NOT a payoff tautology).**
  `A4_partitional_destroys_gap : ¬ (Value E1 < Value Q)` **compiles** — i.e. when the coarser
  expert is the PARTITIONAL anchor Q (E1 still refines it, SAME π, SAME menu), the strict gap
  *vanishes* (4/9 < 4/9 is false). The inequality is therefore caused specifically by E2's
  non-partitionality, not by the payoffs. **Shadow-(c) defeated.**
  `A4_nonpartitional_beats_partition : Value Q < Value E2` also compiles — the non-partitional
  E2 strictly beats the partition on the same menu, giving `Value Q ≤ Value E1 < Value E2`.
- **A6 (preconditions are real, comparison non-degenerate).** Re-decided `S4 E1/E2/Q`,
  `¬ Partitional E2`, `Partitional Q`, `Refines E1 E2`, `Refines E1 Q`, and additionally
  `A6_E1_ne_E2 : E1 ≠ E2` (the comparison is genuinely two *different* experts, not E-vs-itself).
  All by `decide`. So the witness really is an instance of the spec's hypotheses, not a
  degenerate one.

**Target-object check.** I grepped the headline and its dependencies: no LI theorem, martingale,
or asymptotic `≂ₙ` object appears anywhere — not as a hypothesis, not as an encoding. The whole
file is finite ℚ arithmetic over `Fin 3`. No hypothesis-laundering.

**Non-vacuity witness + near-miss both COMPILE** (the whole point of the gate): the strict
inequality is a `norm_num` conclusion from explicit rationals, and the mandatory partitional
near-miss compiles and *flips the sign*. Confirmed in both the original and my attack file.

---

## 3. EXEC extension — independent adversarial search (harder than the author's)

I re-implemented the model from scratch (`/tmp/nvoi_adv.py`) and extended the search:

- Reproduces the witness (V(E1)=4/9 < V(E2)=5/9; V(Q)=4/9; near-miss holds).
- **Finer menu grid** {0,¼,½,¾,1}³ for both options (author used {0,½,1}³): over **1,106,954**
  strict-argmax refinement pairs on all 26 S4 experiments, **6,804** negative-VoI instances,
  **0** with a partitional coarser expert (Geanakoplos violations).
- **0** refinements of any partition that lose value.
- Crucially I also ran the **tie-break code path** (tie → option 0, not just strict argmax):
  28,431 refine-a-partition checks, **0** value-losing violations. The author only tested
  strict-argmax pairs; the claim survives ties too.

I could not produce a counterexample to either (i) or (ii). The negative sign genuinely
*requires* non-partitionality, exactly as the Lean near-miss certifies on the concrete witness.

---

## 4. Caveats (honest scope — not defects)

- The near-miss for this particular Q is the **equality** 4/9 = 4/9, not a strict `>`. That is
  fine and is what the spec asks (`Value E1 ≥ Value Q`); the *strict* separation tracking
  partitionality is carried by `Value Q < Value E2`. Both compile.
- This is only the **finite static VoI** comparison. It does NOT prove Geanakoplos in general,
  nor any LI/martingale/asymptotic content — and it correctly does not pretend to. No off-limits
  result (Geanakoplos-as-theorem, `value_of_CM`, `AntiExpert`, v2 §1.1 prose) was re-skinned;
  this is a genuinely new two-expert construction.

---

## Verdict

**REAL.** The example is faithful to v2 §1.1's cited-but-unbuilt Weatherson tightness claim;
the strict gap is the CONCLUSION of a closed ℚ computation (no hypothesis to launder); `recOpt`
is the genuine, data-driven argmax-of-own-posterior (re-derived independently and shown
menu-sensitive); and the mandatory partitional near-miss both compiles and, in adversarial form
(`¬ (Value E1 < Value Q)`), shows the negative sign is caused by non-partitionality rather than
the payoffs. Independent EXEC search over >1.1M cases (finer grid + tie-break path) found zero
Geanakoplos violations. Kernel-clean axioms throughout.
