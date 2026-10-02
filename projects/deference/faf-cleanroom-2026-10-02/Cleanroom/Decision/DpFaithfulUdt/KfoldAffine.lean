import Cleanroom.Decision.DpFaithfulUdt.Kfold

/-!
# The affine-coupling conjecture on the 2-fold mugging: the unnormalized statement refuted, the
normalized `k = 2` characterization proved (T18(a); repair round 1)

`faithful.md` Open 1 conjectures that on the `k`-fold mugging "a faithful set exists for `a` iff
the deviation law `μ_{δ_a}` is a conditional of `μ_{C'}` on a union of leaves for all `q'`, which
on nested fibers forces the coupling to be affine in the number of paying draws". The round-1
audits refuted the biconditional as the package had stated it (for *both* acts, every coupling
`b : ℕ → ℚ` with `0 ≤ b_j ≤ 1`), already at `k = 2`, in both directions:

* `⇒` fails: `halfB = (0, ½, ½)` is not affine on `0..2`, yet faithful sets exist for both acts
  for every full-support self-model (`halfB_faithful_both`): the *first-draw* sets.
* `⇐` fails: `b4 = (0, ¼, ½)` is affine on `0..2`, yet at `q' = ¼` no leaf-set is law-faithful
  for pay (`no_pay_faithful_quarter`).

Both counterexamples have `b_2 ≠ 1`: the deviation `δ_pay` then transfers with probability
`b_2 < 1` and the conjecture's bookkeeping changes. For **normalized** couplings (`b_0 = 0`,
`b_k = 1`: no transfer under unanimous refusal, transfer under unanimous payment — as `linearB`,
`concaveB`, `convexB` all are, and as Open 1's couplings implicitly are) the conjecture survives
at `k = 2`, and the characterization is sharper than "affine":

* pay-faithful sets exist for every `q'` iff `b_1 ∈ {½, 1}` (`kfold2_norm_pay_faithful_iff`);
* refuse-faithful sets exist for every `q'` iff `b_1 ∈ {0, ½}` (`kfold2_norm_refuse_faithful_iff`);
* both iff `b_1 = ½`, i.e. iff `b` is affine on `0..2` (`kfold2_norm_faithful_both_iff_affine`).

The mechanism: the *first-draw set* (the `T`-leaf of the act plus every `H`-leaf whose first
simulated draw is that act) is faithful iff the coupling does not see the second draw (`b_1 = b_2`
for pay, `b_1 = b_0` for refuse; `kfold2_firstDraw_pay_faithful`,
`kfold2_firstDraw_refuse_faithful`, for *any* `b`), and the *payoff-class set* is faithful iff
the coupling is affine (`kfold2_payClass_faithful`, `kfold2_refuseClass_faithful`); at `q' = ½`
nothing else works (`kfold2_norm_pay_necessary`, `kfold2_norm_refuse_necessary`: a case split over
the leaves' membership). The general-`k` normalized statement is restated OPEN in `Open.lean`
(`kfold_faithful_iff_affine_normalized_open`), with the route.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

/-! ### The `(coin, r)` labelling for any `k` -/

section labK

/-- The coin coordinate of a run of the `k`-fold mugging (`0` = `T`, `1` = `H`), any `k`.
Source: `faithful.md` FA-8, Open 1
Kind: D -/
def coinOfK (k : ℕ) (x y : ℚ) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) :
    (kfold k x y b hb).Leaves → Fin 2
  | ⟨i, _⟩ => i

/-- The labelling `(coin, r)` of the `k`-fold mugging's runs, any `k`.
Source: `faithful.md` FA-8, Open 1
Kind: D -/
def kfLabK (k : ℕ) (x y : ℚ) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1)
    (ℓ : (kfold k x y b hb).Leaves) : Fin 2 × ℚ :=
  (coinOfK k x y b hb ℓ, payoff _ ℓ)

/-- `kfLabK 2` is `Kfold.lean`'s `kfLab`. Source: none: infrastructure. Kind: L -/
theorem kfLabK_two (x y : ℚ) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) :
    kfLabK 2 x y b hb = kfLab x y b hb := by
  funext ℓ
  rcases ℓ with ⟨i, r⟩
  rfl

end labK

/-! ### The first-draw sets: faithful iff the coupling does not see the second draw -/

section firstDraw

variable (x y : ℚ) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) (q' : ℚ) (h0 : 0 < q') (h1 : q' < 1)

/-- The first-draw set for pay: the `T`-pay leaf and every `H`-leaf whose *first* simulated draw
is pay (both transfer outcomes, both second draws).
Source: audit r1 (fidelity) probe `OpenAffineRefuted.lean` (`hPayE`); `faithful.md` FA-8
Kind: D -/
def firstDrawPayE : Finset (kfold 2 x y b hb).Leaves :=
  Finset.univ.filter fun ℓ =>
    draws _ ℓ = [⟨(), Act2.a⟩] ∨ draws _ ℓ = [⟨(), Act2.a⟩, ⟨(), Act2.a⟩] ∨
      draws _ ℓ = [⟨(), Act2.a⟩, ⟨(), Act2.b⟩]

/-- The first-draw set for refuse: the `T`-refuse leaf and every `H`-leaf whose *first* simulated
draw is refuse.
Source: none: infrastructure (the mirror of `firstDrawPayE`)
Kind: D -/
def firstDrawRefuseE : Finset (kfold 2 x y b hb).Leaves :=
  Finset.univ.filter fun ℓ =>
    draws _ ℓ = [⟨(), Act2.b⟩] ∨ draws _ ℓ = [⟨(), Act2.b⟩, ⟨(), Act2.a⟩] ∨
      draws _ ℓ = [⟨(), Act2.b⟩, ⟨(), Act2.b⟩]

/-- **The first-draw set is law-faithful for pay whenever `b_1 = b_2`** (any `b_0`, every
full-support self-model): its `C'`-mass is `q'/2 + q'²/2 + q'(1−q')/2 = q'`, and its transfer
mass `½q'(q' + (1−q')) b_2 = ½ q' b_2` is the deviation's. This is the mechanism behind the
`⇒`-refutation of the unnormalized affine conjecture (`halfB`).
Source: audit r1 (fidelity) probe `OpenAffineRefuted.lean`; `faithful.md` FA-8, Open 1
Kind: P
Fidelity: n/a (a construction; the hypothesis `b_1 = b_2` is the exact condition for this set;
no condition on `x, y` — the set is cut by draws, not by payoffs)
Hyps: (a) `0 < q' < 1`; (a) `b 1 = b 2` -/
theorem kfold2_firstDraw_pay_faithful (h12 : b 1 = b 2) :
    LeafLawFaithfulWrt (kfold 2 x y b hb) (kfLab x y b hb) (procQ q' h0.le h1.le) () .a
      (firstDrawPayE x y b hb) := by
  have hocc := kfold2_occ x y b hb
  have hE : mass (procQ q' h0.le h1.le) (kfold 2 x y b hb) (firstDrawPayE x y b hb) = q' := by
    rw [kfold2_mass]
    simp [firstDrawPayE, draws_tLeaf, draws_hLeaf, Act2.sum_univ, payCount, procQ]
    ring
  refine ⟨by rw [hE]; exact h0, fun X => ?_⟩
  rw [hocc, Finset.inter_univ, mass_univ, mul_one, kfold2_mass_labEv_inter, kfold2_mass_labEv, hE]
  simp [firstDrawPayE, draws_tLeaf, draws_hLeaf, Act2.sum_univ, payCount, procQ,
    Proc.deviatePure, FinDistr.pure_w, h12]
  split_ifs <;> ring

/-- **The first-draw set is law-faithful for refuse whenever `b_1 = b_0`** (any `b_2`, every
full-support self-model): the mirror of `kfold2_firstDraw_pay_faithful`.
Source: none: infrastructure (mirror); `faithful.md` FA-8, Open 1
Kind: P
Fidelity: n/a (a construction; `b_1 = b_0` is the exact condition for this set; no condition on
`x, y`)
Hyps: (a) `0 < q' < 1`; (a) `b 1 = b 0` -/
theorem kfold2_firstDraw_refuse_faithful (h10 : b 1 = b 0) :
    LeafLawFaithfulWrt (kfold 2 x y b hb) (kfLab x y b hb) (procQ q' h0.le h1.le) () .b
      (firstDrawRefuseE x y b hb) := by
  have hocc := kfold2_occ x y b hb
  have hE : mass (procQ q' h0.le h1.le) (kfold 2 x y b hb) (firstDrawRefuseE x y b hb) =
      1 - q' := by
    rw [kfold2_mass]
    simp [firstDrawRefuseE, draws_tLeaf, draws_hLeaf, Act2.sum_univ, payCount, procQ]
    ring
  refine ⟨by rw [hE]; linarith, fun X => ?_⟩
  rw [hocc, Finset.inter_univ, mass_univ, mul_one, kfold2_mass_labEv_inter, kfold2_mass_labEv, hE]
  simp [firstDrawRefuseE, draws_tLeaf, draws_hLeaf, Act2.sum_univ, payCount, procQ,
    Proc.deviatePure, FinDistr.pure_w, h10]
  split_ifs <;> ring

end firstDraw

/-! ### Normalized couplings at `k = 2`: the payoff-class sets at `b_1 = ½` -/

section normHalf

variable (x y : ℚ) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1) (q' : ℚ) (h0 : 0 < q') (h1 : q' < 1)

/-- The payoff-class set for pay on `kfold 2 x y b`: the leaves of payoff `−x` or `y` (`linearPayE`
for an arbitrary coupling). Source: `faithful.md` FA-8. Kind: D -/
def payClassE : Finset (kfold 2 x y b hb).Leaves :=
  labEv _ (kfLab x y b hb) {((0 : Fin 2), -x), ((1 : Fin 2), y)}

/-- The payoff-class set for refuse: the leaves of payoff `0` (`linearRefuseE` for an arbitrary
coupling). Source: `faithful.md` FA-8. Kind: D -/
def refuseClassE : Finset (kfold 2 x y b hb).Leaves :=
  labEv _ (kfLab x y b hb) {((0 : Fin 2), (0 : ℚ)), ((1 : Fin 2), (0 : ℚ))}

/-- **The payoff-class set is law-faithful for pay on every normalized coupling with `b_1 = ½`**
(the affine one), for every full-support self-model.
Source: `faithful.md` FA-8 ("`k=2` linear coupling: faithful sets exist under Definition 6")
Kind: P
Fidelity: n/a (a construction, `kfold2_linear_pay_faithful` with the coupling's three values as
hypotheses)
Hyps: (a) `0 < x`, `0 < y`; (a) `0 < q' < 1`; (a) `b 0 = 0`, `b 1 = ½`, `b 2 = 1` -/
theorem kfold2_payClass_faithful (hx : 0 < x) (hy : 0 < y) (hb0 : b 0 = 0) (hb1 : b 1 = 1 / 2)
    (hb2 : b 2 = 1) :
    LeafLawFaithfulWrt (kfold 2 x y b hb) (kfLab x y b hb) (procQ q' h0.le h1.le) () .a
      (payClassE x y b hb) := by
  have hocc := kfold2_occ x y b hb
  obtain ⟨f10, f01⟩ := fin2_facts
  have hE : mass (procQ q' h0.le h1.le) (kfold 2 x y b hb) (payClassE x y b hb) = q' := by
    rw [payClassE, kfold2_mass_labEv]
    simp [Act2.sum_univ, payCount, hb0, hb1, hb2, procQ, hx.ne, hx.ne', hy.ne, hy.ne', f10, f01]
    ring
  refine ⟨by rw [hE]; exact h0, fun X => ?_⟩
  rw [hocc, Finset.inter_univ, mass_univ, mul_one, kfold2_mass_labEv_inter, kfold2_mass_labEv, hE]
  simp [payClassE, kfLab_tLeaf, kfLab_hLeaf, Act2.sum_univ, payCount, hb0, hb1, hb2, procQ,
    hx.ne, hx.ne', hy.ne, hy.ne', f10, f01, Proc.deviatePure, FinDistr.pure_w]
  split_ifs <;> ring

/-- **The payoff-class set is law-faithful for refuse on every normalized coupling with
`b_1 = ½`**, for every full-support self-model.
Source: `faithful.md` FA-8
Kind: P
Fidelity: n/a (a construction, `kfold2_linear_refuse_faithful` with the coupling's three values
as hypotheses)
Hyps: (a) `0 < x`, `0 < y`; (a) `0 < q' < 1`; (a) `b 0 = 0`, `b 1 = ½`, `b 2 = 1` -/
theorem kfold2_refuseClass_faithful (hx : 0 < x) (hy : 0 < y) (hb0 : b 0 = 0) (hb1 : b 1 = 1 / 2)
    (hb2 : b 2 = 1) :
    LeafLawFaithfulWrt (kfold 2 x y b hb) (kfLab x y b hb) (procQ q' h0.le h1.le) () .b
      (refuseClassE x y b hb) := by
  have hocc := kfold2_occ x y b hb
  obtain ⟨f10, f01⟩ := fin2_facts
  have hE : mass (procQ q' h0.le h1.le) (kfold 2 x y b hb) (refuseClassE x y b hb) = 1 - q' := by
    rw [refuseClassE, kfold2_mass_labEv]
    simp [Act2.sum_univ, payCount, hb0, hb1, hb2, procQ, hx.ne, hx.ne', hy.ne, hy.ne', f10, f01]
    ring
  refine ⟨by rw [hE]; linarith, fun X => ?_⟩
  rw [hocc, Finset.inter_univ, mass_univ, mul_one, kfold2_mass_labEv_inter, kfold2_mass_labEv, hE]
  simp [refuseClassE, kfLab_tLeaf, kfLab_hLeaf, Act2.sum_univ, payCount, hb0, hb1, hb2, procQ,
    hx.ne, hx.ne', hy.ne, hy.ne', f10, f01, Proc.deviatePure, FinDistr.pure_w]
  split_ifs <;> ring

end normHalf

/-! ### Normalized couplings at `k = 2`: necessity, read off at `q' = ½` -/

section necessary

variable (x y : ℚ) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1)

/-- **At `q' = ½`, a pay-faithful leaf-set on a normalized coupling forces `b_1 ∈ {½, 1}`.**
Pay-faithfulness puts the `T`-pay leaf in `E` with `μ_{C'}(E) = q' = ½`, excludes every
positive-mass no-transfer leaf, and asks the transfer leaves in `E` — masses `⅛`, `⅛ b_1`,
`⅛ b_1` — for total `¼`: `⅛ + ⅛ b_1 + ⅛ b_1` needs `b_1 = ½`, `⅛ + ⅛ b_1` or `⅛ b_1 + ⅛ b_1` need
`b_1 = 1`, and nothing else sums to `¼`. (Only the `(T, −x)` and `(H, y)` clauses are needed: the
first fixes `μ_{C'}(E) = ½`, the second is then a case split over the three transfer leaves of
positive mass.)
Source: `faithful.md` Open 1 (the "settling calculation": "write the leaf-set faithfulness
conditions as polynomial identities in `q'` … and solve for the couplings admitting a solution")
Kind: P
Fidelity: n/a (the necessity half of `kfold2_norm_pay_faithful_iff`)
Hyps: (a) `0 < x`, `0 < y`; (a) `b 0 = 0`, `b 2 = 1` -/
theorem kfold2_norm_pay_necessary (hx : 0 < x) (hy : 0 < y) (hb0 : b 0 = 0) (hb2 : b 2 = 1)
    (E : Finset (kfold 2 x y b hb).Leaves)
    (hE : LeafLawFaithfulWrt (kfold 2 x y b hb) (kfLab x y b hb)
      (procQ (1 / 2) (by norm_num) (by norm_num)) () .a E) :
    b 1 = 1 / 2 ∨ b 1 = 1 := by
  obtain ⟨hpos, hX⟩ := hE
  obtain ⟨hb1l, hb1u⟩ := hb 1
  have hocc := kfold2_occ x y b hb
  have hA := hX {((0 : Fin 2), -x)}
  have hC := hX {((1 : Fin 2), y)}
  rw [hocc, Finset.inter_univ, mass_univ, mul_one, kfold2_mass_labEv_inter,
    kfold2_mass_labEv] at hA hC
  obtain ⟨f10, f01⟩ := fin2_facts
  simp only [Act2.sum_univ, payCount, hb0, hb2, procQ, FinDistr.act2_a, FinDistr.act2_b,
    Proc.deviatePure, Proc.deviate_same, FinDistr.pure_w] at hA hC
  simp [hx.ne, hx.ne', hy.ne, hy.ne', f10, f01] at hA hC
  by_cases hT : tLeaf x y b hb .a ∈ E
  · rcases em (hLeaf x y b hb .a .a 0 ∈ E) with h1 | h1 <;>
    rcases em (hLeaf x y b hb .a .b 0 ∈ E) with h2 | h2 <;>
    rcases em (hLeaf x y b hb .b .a 0 ∈ E) with h3 | h3 <;>
    simp [hT, h1, h2, h3] at hA hC <;>
    first
    | (exfalso; linarith)
    | (left; linarith)
    | (right; linarith)
  · simp [hT] at hA
    linarith

/-- **At `q' = ½`, a refuse-faithful leaf-set on a normalized coupling forces `b_1 ∈ {0, ½}`.**
The mirror of `kfold2_norm_pay_necessary`: the `T`-refuse leaf is in `E` with `μ_{C'}(E) = ½`,
every positive-mass transfer leaf is excluded, and the no-transfer leaves in `E` — masses
`⅛(1 − b_1)`, `⅛(1 − b_1)`, `⅛` — must total `¼`.
Source: `faithful.md` Open 1 (the "settling calculation")
Kind: P
Fidelity: n/a (the necessity half of `kfold2_norm_refuse_faithful_iff`)
Hyps: (a) `0 < x`, `0 < y`; (a) `b 0 = 0`, `b 2 = 1` -/
theorem kfold2_norm_refuse_necessary (hx : 0 < x) (hy : 0 < y) (hb0 : b 0 = 0) (hb2 : b 2 = 1)
    (E : Finset (kfold 2 x y b hb).Leaves)
    (hE : LeafLawFaithfulWrt (kfold 2 x y b hb) (kfLab x y b hb)
      (procQ (1 / 2) (by norm_num) (by norm_num)) () .b E) :
    b 1 = 0 ∨ b 1 = 1 / 2 := by
  obtain ⟨hpos, hX⟩ := hE
  obtain ⟨hb1l, hb1u⟩ := hb 1
  have hocc := kfold2_occ x y b hb
  have hB := hX {((0 : Fin 2), (0 : ℚ))}
  have hD := hX {((1 : Fin 2), (0 : ℚ))}
  rw [hocc, Finset.inter_univ, mass_univ, mul_one, kfold2_mass_labEv_inter,
    kfold2_mass_labEv] at hB hD
  obtain ⟨f10, f01⟩ := fin2_facts
  simp only [Act2.sum_univ, payCount, hb0, hb2, procQ, FinDistr.act2_a, FinDistr.act2_b,
    Proc.deviatePure, Proc.deviate_same, FinDistr.pure_w] at hB hD
  simp [hx.ne, hx.ne', hy.ne, hy.ne', f10, f01] at hB hD
  by_cases hT : tLeaf x y b hb .b ∈ E
  · rcases em (hLeaf x y b hb .a .b 1 ∈ E) with h1 | h1 <;>
    rcases em (hLeaf x y b hb .b .a 1 ∈ E) with h2 | h2 <;>
    rcases em (hLeaf x y b hb .b .b 1 ∈ E) with h3 | h3 <;>
    simp [hT, h1, h2, h3] at hB hD <;>
    first
    | (exfalso; linarith)
    | (left; linarith)
    | (right; linarith)
  · simp [hT] at hB
    linarith

end necessary


/-! ### Normalized couplings at `k = 2`: the characterizations -/

section characterization

variable (x y : ℚ) (b : ℕ → ℚ) (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1)

/-- **Pay-faithful sets exist for every full-support self-model iff `b_1 ∈ {½, 1}`** on the 2-fold
mugging with a normalized coupling (`b_0 = 0`, `b_2 = 1`), `x, y > 0`: the payoff-class set at
`b_1 = ½`, the first-draw set at `b_1 = 1`, and nothing at any other `b_1` (already at `q' = ½`).
Source: `faithful.md` Open 1 ("a faithful set exists for `a` iff …"), FA-8; dp-cf-153
Kind: P
Fidelity: variant: Open 1's per-act form at `k = 2` on normalized couplings — the answer is the
two-point locus `{½, 1}`, not "affine"
Hyps: (a) `0 < x`, `0 < y`; (a) `b 0 = 0`, `b 2 = 1` -/
theorem kfold2_norm_pay_faithful_iff (hx : 0 < x) (hy : 0 < y) (hb0 : b 0 = 0) (hb2 : b 2 = 1) :
    (∀ q' (h0 : 0 < q') (h1 : q' < 1), ∃ E : Finset (kfold 2 x y b hb).Leaves,
      LeafLawFaithfulWrt (kfold 2 x y b hb) (kfLab x y b hb) (procQ q' h0.le h1.le) () .a E) ↔
    (b 1 = 1 / 2 ∨ b 1 = 1) := by
  constructor
  · intro h
    obtain ⟨E, hE⟩ := h (1 / 2) (by norm_num) (by norm_num)
    exact kfold2_norm_pay_necessary x y b hb hx hy hb0 hb2 E hE
  · rintro (h | h) q' h0 h1
    · exact ⟨_, kfold2_payClass_faithful x y b hb q' h0 h1 hx hy hb0 h hb2⟩
    · exact ⟨_, kfold2_firstDraw_pay_faithful x y b hb q' h0 h1 (h.trans hb2.symm)⟩

/-- **Refuse-faithful sets exist for every full-support self-model iff `b_1 ∈ {0, ½}`** on the
2-fold mugging with a normalized coupling, `x, y > 0`: the first-draw set at `b_1 = 0`, the
payoff-class set at `b_1 = ½`, and nothing otherwise (already at `q' = ½`). The mirror of
`kfold2_norm_pay_faithful_iff`; the concave coupling (`b_1 = 1`) is the proved instance of
"nothing" (`kfold2_concave_no_refuse_faithful`).
Source: `faithful.md` Open 1, FA-8 ("none for refuse"); dp-cf-153, dp-cf-2-006
Kind: P
Fidelity: variant: Open 1's per-act form at `k = 2` on normalized couplings — the locus `{0, ½}`
Hyps: (a) `0 < x`, `0 < y`; (a) `b 0 = 0`, `b 2 = 1` -/
theorem kfold2_norm_refuse_faithful_iff (hx : 0 < x) (hy : 0 < y) (hb0 : b 0 = 0)
    (hb2 : b 2 = 1) :
    (∀ q' (h0 : 0 < q') (h1 : q' < 1), ∃ E : Finset (kfold 2 x y b hb).Leaves,
      LeafLawFaithfulWrt (kfold 2 x y b hb) (kfLab x y b hb) (procQ q' h0.le h1.le) () .b E) ↔
    (b 1 = 0 ∨ b 1 = 1 / 2) := by
  constructor
  · intro h
    obtain ⟨E, hE⟩ := h (1 / 2) (by norm_num) (by norm_num)
    exact kfold2_norm_refuse_necessary x y b hb hx hy hb0 hb2 E hE
  · rintro (h | h) q' h0 h1
    · exact ⟨_, kfold2_firstDraw_refuse_faithful x y b hb q' h0 h1 (h.trans hb0.symm)⟩
    · exact ⟨_, kfold2_refuseClass_faithful x y b hb q' h0 h1 hx hy hb0 h hb2⟩

/-- **T18(a) at `k = 2`, normalized — faithful sets for both acts exist for every full-support
self-model iff the coupling is affine.** On the 2-fold mugging with `b_0 = 0`, `b_2 = 1` and
`x, y > 0`: both loci `{½, 1}` and `{0, ½}` meet only at `b_1 = ½`, i.e. `b_j = j/2`. The `k = 2`
instance of the normalized OPEN row `kfold_faithful_iff_affine_normalized_open` (`Open.lean`).
Source: `faithful.md` Open 1 ("… which on nested fibers forces the coupling to be affine in the
number of paying draws"); dp-cf-153, dp-core-056
Kind: P
Fidelity: variant: Open 1's conjecture for both acts, at `k = 2`, restricted to normalized
couplings — without normalization it is false in both directions
(`kfold_faithful_iff_affine_refuted`)
Hyps: (a) `0 < x`, `0 < y`; (a) `b 0 = 0`, `b 2 = 1` -/
theorem kfold2_norm_faithful_both_iff_affine (hx : 0 < x) (hy : 0 < y) (hb0 : b 0 = 0)
    (hb2 : b 2 = 1) :
    (∀ q' (h0 : 0 < q') (h1 : q' < 1), ∀ a : Act2, ∃ E : Finset (kfold 2 x y b hb).Leaves,
      LeafLawFaithfulWrt (kfold 2 x y b hb) (kfLabK 2 x y b hb) (procQ q' h0.le h1.le) () a E) ↔
    ∃ α β : ℚ, ∀ j ≤ 2, b j = α * j + β := by
  rw [kfLabK_two]
  constructor
  · intro h
    have hp := (kfold2_norm_pay_faithful_iff x y b hb hx hy hb0 hb2).mp
      fun q' h0 h1 => h q' h0 h1 .a
    have hr := (kfold2_norm_refuse_faithful_iff x y b hb hx hy hb0 hb2).mp
      fun q' h0 h1 => h q' h0 h1 .b
    have h1 : b 1 = 1 / 2 := by
      rcases hp with hp | hp <;> rcases hr with hr | hr <;> linarith
    refine ⟨1 / 2, 0, fun j hj => ?_⟩
    rcases j with _ | _ | _ | j
    · norm_num [hb0]
    · norm_num [h1]
    · norm_num [hb2]
    · omega
  · rintro ⟨α, β, hab⟩ q' h0 h1 a
    have e0 := hab 0 (by norm_num)
    have e1 := hab 1 (by norm_num)
    have e2 := hab 2 (by norm_num)
    norm_num at e0 e1 e2
    have hb1 : b 1 = 1 / 2 := by
      rw [hb0] at e0
      rw [hb2] at e2
      linarith
    cases a
    · exact ⟨_, kfold2_payClass_faithful x y b hb q' h0 h1 hx hy hb0 hb1 hb2⟩
    · exact ⟨_, kfold2_refuseClass_faithful x y b hb q' h0 h1 hx hy hb0 hb1 hb2⟩

end characterization

/-! ### The unnormalized conjecture is false in both directions (audit round 1, B1) -/

section refuted

/-- The coupling `b_0 = 0`, `b_1 = b_2 = ½` ("one payer transfers with probability ½, two payers
likewise"): not normalized (`b_2 ≠ 1`), not affine on `0..2`.
Source: audit r1 (fidelity) probe `OpenAffineRefuted.lean`
Kind: D -/
def halfB (j : ℕ) : ℚ := if j = 0 then 0 else 1 / 2

/-- `halfB` is a probability. Source: none: infrastructure. Kind: L -/
theorem halfB_bounds (j : ℕ) : 0 ≤ halfB j ∧ halfB j ≤ 1 := by
  unfold halfB; split_ifs <;> norm_num

/-- `halfB`'s three values. Source: none: infrastructure. Kind: L -/
theorem halfB_vals : halfB 0 = 0 ∧ halfB 1 = 1 / 2 ∧ halfB 2 = 1 / 2 := by
  simp [halfB]

/-- `halfB` is not affine on `0..2`: `b_1 − b_0 = ½ ≠ 0 = b_2 − b_1`. Source: none: infrastructure.
Kind: L -/
theorem halfB_not_affine : ¬ ∃ α β : ℚ, ∀ j ≤ 2, halfB j = α * (j : ℚ) + β := by
  rintro ⟨α, β, h⟩
  have h0 := h 0 (by norm_num)
  have h1 := h 1 (by norm_num)
  have h2 := h 2 (by norm_num)
  simp [halfB] at h0 h1 h2
  linarith

/-- The refuse-faithful set for `halfB`: the `T`-refuse leaf and the no-transfer `H`-leaves not
below two pays (`(a,b,1)`, `(b,a,1)`, `(b,b,1)`), of mass `(1−q')/2 + q'(1−q')/2 + (1−q')²/2 = 1−q'`.
Source: audit r1 (fidelity) probe `OpenAffineRefuted.lean` (`hRefuseE`)
Kind: D -/
def halfRefuseE (x y : ℚ) : Finset (kfold 2 x y halfB halfB_bounds).Leaves :=
  (labEv _ (kfLab x y halfB halfB_bounds) {((0 : Fin 2), (0 : ℚ)), ((1 : Fin 2), (0 : ℚ))}).filter
    fun ℓ => draws _ ℓ ≠ [⟨(), Act2.a⟩, ⟨(), Act2.a⟩]

/-- `halfRefuseE` is law-faithful for refuse on `kfold 2 x y halfB`, every full-support self-model.
Source: audit r1 (fidelity) probe `OpenAffineRefuted.lean` (`hRefuseE_faithful`)
Kind: P
Fidelity: n/a (a construction)
Hyps: (a) `0 < x`, `0 < y`; (a) `0 < q' < 1` -/
theorem halfB_refuse_faithful (x y : ℚ) (hx : 0 < x) (hy : 0 < y) (q' : ℚ) (h0 : 0 < q')
    (h1 : q' < 1) :
    LeafLawFaithfulWrt (kfold 2 x y halfB halfB_bounds) (kfLab x y halfB halfB_bounds)
      (procQ q' h0.le h1.le) () .b (halfRefuseE x y) := by
  have hocc := kfold2_occ x y halfB halfB_bounds
  obtain ⟨c0, c1, c2⟩ := halfB_vals
  obtain ⟨f10, f01⟩ := fin2_facts
  have hE : mass (procQ q' h0.le h1.le) (kfold 2 x y halfB halfB_bounds) (halfRefuseE x y) =
      1 - q' := by
    rw [kfold2_mass]
    simp [halfRefuseE, kfLab_tLeaf, kfLab_hLeaf, draws_tLeaf, draws_hLeaf, Act2.sum_univ,
      payCount, c0, c1, c2, procQ, hx.ne, hx.ne', hy.ne, hy.ne', f10, f01]
    ring
  refine ⟨by rw [hE]; linarith, fun X => ?_⟩
  rw [hocc, Finset.inter_univ, mass_univ, mul_one, kfold2_mass_labEv_inter, kfold2_mass_labEv, hE]
  simp [halfRefuseE, kfLab_tLeaf, kfLab_hLeaf, draws_tLeaf, draws_hLeaf, Act2.sum_univ,
    payCount, c0, c1, c2, procQ, hx.ne, hx.ne', hy.ne, hy.ne', f10, f01, Proc.deviatePure,
    FinDistr.pure_w]
  split_ifs <;> ring

/-- **`⇒` of the unnormalized conjecture fails**: on `halfB` faithful sets exist for both acts
for every full-support self-model — pay by the first-draw set (`b_1 = b_2`), refuse by
`halfRefuseE` — yet `halfB` is not affine on `0..2`.
Source: audit r1 (fidelity) B1; `faithful.md` Open 1
Kind: N+ (refutation witness)
Fidelity: exact (the left-hand side of the round-0 OPEN row at `k = 2`, with its right-hand side
false)
Hyps: (a) `0 < x`, `0 < y` -/
theorem halfB_faithful_both_not_affine (x y : ℚ) (hx : 0 < x) (hy : 0 < y) :
    (∀ q' (h0 : 0 < q') (h1 : q' < 1), ∀ a : Act2,
      ∃ E : Finset (kfold 2 x y halfB halfB_bounds).Leaves,
        LeafLawFaithfulWrt (kfold 2 x y halfB halfB_bounds) (kfLabK 2 x y halfB halfB_bounds)
          (procQ q' h0.le h1.le) () a E) ∧
    ¬ ∃ α β : ℚ, ∀ j ≤ 2, halfB j = α * (j : ℚ) + β := by
  refine ⟨fun q' h0 h1 a => ?_, halfB_not_affine⟩
  rw [kfLabK_two]
  cases a
  · exact ⟨_, kfold2_firstDraw_pay_faithful x y halfB halfB_bounds q' h0 h1 (by simp [halfB])⟩
  · exact ⟨_, halfB_refuse_faithful x y hx hy q' h0 h1⟩

/-- The affine, non-normalized coupling `b_j = j/4` (clamped at `1`; only `j ≤ 2` is reached):
`(0, ¼, ½)`.
Source: audit r1 (adversarial) probe `OpenAffineFalse.lean`
Kind: D -/
def b4 : ℕ → ℚ := fun j => min ((j : ℚ) / 4) 1

/-- `b4` is a probability. Source: none: infrastructure. Kind: L -/
theorem b4_bounds : ∀ j, 0 ≤ b4 j ∧ b4 j ≤ 1 := fun j =>
  ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩

/-- `b4`'s three values. Source: none: infrastructure. Kind: L -/
theorem b4_vals : b4 0 = 0 ∧ b4 1 = 1 / 4 ∧ b4 2 = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [b4]

/-- `b4` is affine on `0..2` (`α = ¼`, `β = 0`). Source: none: infrastructure. Kind: L -/
theorem b4_affine : ∃ α β : ℚ, ∀ j ≤ 2, b4 j = α * j + β := by
  refine ⟨1 / 4, 0, fun j hj => ?_⟩
  rcases j with _ | _ | _ | j
  · norm_num [b4]
  · norm_num [b4]
  · norm_num [b4]
  · omega

/-- **At `q' = ¼` no leaf-set is law-faithful for pay on `kfold 2 x y b4`** (`x, y > 0`):
pay-faithfulness forces the `T`-pay leaf into `E` with `μ_{C'}(E) = q'`, so the no-transfer
`H`-leaves in `E` must carry `C'`-mass `q'(1 − b_2)/2 = 1/16`; the four candidates have masses
`1/64, 9/128, 9/128, 36/128`, no subset of which sums to `8/128`.
Source: audit r1 (adversarial) probe `OpenAffineFalse.lean`
Kind: P (refutation of existence)
Fidelity: n/a
Hyps: (a) `0 < x`, `0 < y` -/
theorem no_pay_faithful_quarter (x y : ℚ) (hx : 0 < x) (hy : 0 < y)
    (E : Finset (kfold 2 x y b4 b4_bounds).Leaves) :
    ¬ LeafLawFaithfulWrt (kfold 2 x y b4 b4_bounds) (kfLab x y b4 b4_bounds)
      (procQ (1 / 4) (by norm_num) (by norm_num)) () .a E := by
  rintro ⟨hpos, hX⟩
  have hocc := kfold2_occ x y b4 b4_bounds
  have hA := hX {((0 : Fin 2), -x)}
  have hB := hX {((1 : Fin 2), (0 : ℚ))}
  rw [hocc, Finset.inter_univ, mass_univ, mul_one, kfold2_mass_labEv_inter,
    kfold2_mass_labEv] at hA hB
  obtain ⟨c0, c1, c2⟩ := b4_vals
  obtain ⟨f10, f01⟩ := fin2_facts
  simp only [Act2.sum_univ, payCount, c0, c1, c2, procQ, FinDistr.act2_a, FinDistr.act2_b,
    Proc.deviatePure, Proc.deviate_same, FinDistr.pure_w] at hA hB
  simp [hx.ne', hy.ne', f10, f01] at hA hB
  by_cases hT : tLeaf x y b4 b4_bounds .a ∈ E
  · rcases em (hLeaf x y b4 b4_bounds .a .a 1 ∈ E) with h1 | h1 <;>
    rcases em (hLeaf x y b4 b4_bounds .a .b 1 ∈ E) with h2 | h2 <;>
    rcases em (hLeaf x y b4 b4_bounds .b .a 1 ∈ E) with h3 | h3 <;>
    rcases em (hLeaf x y b4 b4_bounds .b .b 1 ∈ E) with h4 | h4 <;>
    simp [hT, h1, h2, h3, h4] at hA hB <;>
    first
    | linarith
    | (rcases hB with hB | hB <;> linarith)
  · simp [hT] at hA
    linarith

/-- **`⇐` of the unnormalized conjecture fails**: `b4` is affine on `0..2`, yet at `q' = ¼` no
leaf-set is law-faithful for pay — so the left-hand side (both acts, every `q'`) fails.
Source: audit r1 (adversarial) B1; `faithful.md` Open 1
Kind: N+ (refutation witness)
Fidelity: exact (the right-hand side of the round-0 OPEN row at `k = 2`, with its left-hand side
false)
Hyps: (a) `0 < x`, `0 < y` -/
theorem b4_affine_not_faithful (x y : ℚ) (hx : 0 < x) (hy : 0 < y) :
    (∃ α β : ℚ, ∀ j ≤ 2, b4 j = α * j + β) ∧
    ¬ (∀ q' (h0 : 0 < q') (h1 : q' < 1), ∀ a : Act2,
      ∃ E : Finset (kfold 2 x y b4 b4_bounds).Leaves,
        LeafLawFaithfulWrt (kfold 2 x y b4 b4_bounds) (kfLabK 2 x y b4 b4_bounds)
          (procQ q' h0.le h1.le) () a E) := by
  refine ⟨b4_affine, fun h => ?_⟩
  obtain ⟨E, hE⟩ := h (1 / 4) (by norm_num) (by norm_num) .a
  rw [kfLabK_two] at hE
  exact no_pay_faithful_quarter x y hx hy E hE

/-- **The round-0 OPEN row `kfold_faithful_iff_affine_open` is refuted**: its universally
quantified statement is false — at `k = 2`, `x = y = 1`, `b = b4` the right-hand side holds and the
left-hand side fails (`halfB` fails it the other way). Ledger status `refuted`; the normalized
restatement is OPEN (`kfold_faithful_iff_affine_normalized_open`, `Open.lean`), proved at `k = 2`
(`kfold2_norm_faithful_both_iff_affine`).
Source: `faithful.md` Open 1 (the conjecture as the package stated it in round 0: "for both acts",
every coupling with `0 ≤ b_j ≤ 1`); audit r1 B1 (both lenses)
Kind: N+ (refutation)
Fidelity: exact (the literal negation of the round-0 statement)
Hyps: none -/
theorem kfold_faithful_iff_affine_refuted :
    ¬ ∀ (k : ℕ) (_ : 2 ≤ k) (x y : ℚ) (_ : 0 < x) (_ : 0 < y) (b : ℕ → ℚ)
        (hb : ∀ j, 0 ≤ b j ∧ b j ≤ 1),
      ((∀ q' (h0 : 0 < q') (h1 : q' < 1), ∀ act : Act2, ∃ E : Finset (kfold k x y b hb).Leaves,
        LeafLawFaithfulWrt (kfold k x y b hb) (kfLabK k x y b hb) (procQ q' h0.le h1.le) () act E) ↔
      ∃ α β : ℚ, ∀ j ≤ k, b j = α * j + β) := by
  intro h
  have hiff := h 2 le_rfl 1 1 one_pos one_pos b4 b4_bounds
  exact (b4_affine_not_faithful 1 1 one_pos one_pos).2 (hiff.mpr b4_affine)

end refuted

end Cleanroom.Decision.DpFaithfulUdt
