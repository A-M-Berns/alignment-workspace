import Cleanroom.Deference.DefArgmaxValue.Concentration
import Cleanroom.Deference.DefArgmaxValue.Witness
import Cleanroom.Deference.DefSelfTrust.GateCollapse

/-!
# `def-argmax-value` · Characterize: H3 is the self-endorsement instance, written without `S`
(repair round 1; audit r1 fidelity item 3)

For an inductor-expert with a selection package on a valued menu, conditional-stability
`CondStableOn M pkg` is **equivalent** to the one-sided self-endorsement instance
`E*(S_n) ≳ₙ M_n` for a (every) follower `S` of the argmax on `M`:

* forward (`endorse_of_concentrates`, `Endorse.lean`) costs the concentration lemma — `(a)` for
  the self-expert (`concentrates_self`), from the `(c)` fold clause in general;
* converse (`condStableOn_of_selfEndorseGE_instance`, here) is three lines from Step 1 and
  exhaustivity: `Σ_j E*(Q^j) ≈ₙ E*(S) ≳ₙ M_n ≈ₙ M_n · Σ_j E*(I^j) ≥ Σ_j E*(I^j) · m^j`, and needs
  **no** concentration.

So H3 is exactly "the expert one-sidedly endorses its own selection on this menu", stated without
mentioning any follower — which is what makes it a *menu* condition a novice can state, and why
`scoped_value` is a composition rather than a squeeze only because the forward direction costs
concentration (which is proved). Two consequences recorded in the report: (i) the register of the
scoped theorem sharpens to "Lemma 1 applied to the self-endorsement instance, with H3 the
selection-free criterion for that instance"; (ii) any menu on which the instance holds for a reason
other than eventual decisiveness would be an H3 witness in the interior-mass regime — the package
has none (open problem 3), and the two forced-oscillation menus it has (the probe, the punishing
menu) violate the instance.

Single process (the expert's own); no deference hypothesis anywhere in this file.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

variable {DP : DeductiveProcess}

/-- **Conditional-stability from the self-endorsement instance** (the converse of Lemma 2, no
concentration needed): for an inductor-expert with a selection package on a valued menu, if some
follower `S` of the argmax has `E*(S_n) ≳ₙ M_n`, then `CondStableOn M pkg`. Proof:
`Σ_j E*(Q^j) ≈ₙ E*(S)` (Step 1), `≳ₙ M_n`, `M_n ≈ₙ M_n · Σ_j E*(I^j)` (exhaustivity, `M_n` bounded),
and `Σ_j E*(I^j) · m^j ≤ M_n · Σ_j E*(I^j)` (masses nonnegative, `m^j ≤ M_n`).
Source: audit r1 fidelity item 3 (new finding); [[total-trust-implies-value]] §Hypotheses (H3)
Kind: C
Fidelity: exact
Hyps: (a); `hf`; `hSE` the instance for one follower -/
theorem condStableOn_of_selfEndorseGE_instance {E : Expert DP} [IsLogicalInductor E.A DP]
    (hf : StrictlyIncreasingDeferral E.f) {k : ℕ} {M : Menu k} (hM : M.Valued DP)
    {I Q : Fin (k + 1) → ℕ → LUV} (pkg : SelectionPackage DP E M I Q)
    {S : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S) (hfol : Follows DP E M S)
    (hSE : (fun n => E.estimate S n) ≳ₙ (fun n => M.maxQuote E n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) : CondStableOn M pkg := by
  have h1 := endorse_step1 hf hM pkg hS hfol hworld
  have hsum := sum_estimate_I hf pkg hworld
  -- M_n · Σ_j E*(I^j) ≈ₙ M_n
  have hMb : ∀ n, |M.maxQuote E n| ≤ 1 := fun n => by
    rw [abs_le]
    have h0 := (E.estimate_mem_Icc (M.O 0) n).1
    have hle := M.quote_le_maxQuote E 0 n
    have hM1 : M.maxQuote E n ≤ 1 := by
      unfold Menu.maxQuote
      exact Finset.sup'_le _ _ (fun j _ => (E.estimate_mem_Icc _ _).2)
    simp only [Menu.quote] at hle
    constructor <;> linarith
  have hMsum : (fun n => M.maxQuote E n * ∑ j, E.estimate (I j) n) ≈ₙ
      (fun n => M.maxQuote E n) := by
    have := asympEq_mul_left_of_bounded hMb hsum
    unfold AsympEq at this ⊢
    refine (tendsto_congr (fun n => ?_)).mp this
    ring
  -- Σ_j E*(I^j) m^j ≤ M_n Σ_j E*(I^j)
  have hdom : ∀ n, ∑ j, E.estimate (I j) n * M.quote E j n ≤
      M.maxQuote E n * ∑ j, E.estimate (I j) n := by
    intro n
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [mul_comm (M.maxQuote E n)]
    exact mul_le_mul_of_nonneg_left (M.quote_le_maxQuote E j n) (E.estimate_mem_Icc _ _).1
  -- assemble
  unfold CondStableOn
  intro ε hε
  have hA := asympEq_eventually_abs_le h1 (show (0 : ℝ) < ε / 3 by linarith)
  have hB := hSE (ε / 3) (by linarith)
  have hC := asympEq_eventually_abs_le hMsum (show (0 : ℝ) < ε / 3 by linarith)
  filter_upwards [hA, hB, hC] with n hn1 hn2 hn3
  rw [abs_le] at hn1 hn3
  have := hdom n
  linarith [hn1.1, hn1.2, hn3.1, hn3.2]

/-- **H3 ⟺ the self-endorsement instance**, for an inductor-expert with concentration on the
menu: `CondStableOn M pkg ↔ E*(S_n) ≳ₙ M_n` for any fixed follower `S`. Forward is Lemma 2
(`endorse_of_concentrates`); the converse needs no concentration.
Source: audit r1 fidelity item 3; [[total-trust-implies-value]] §Lemma 2
Kind: C
Fidelity: exact
Hyps: (a); `hf`; `hconc : Concentrates E M I` ((a) for the self-expert, from the `(c)` fold clause
in general — used by the forward direction only) -/
theorem condStableOn_iff_selfEndorseGE_instance {E : Expert DP} [IsLogicalInductor E.A DP]
    (hf : StrictlyIncreasingDeferral E.f) {k : ℕ} {M : Menu k} (hM : M.Valued DP)
    {I Q : Fin (k + 1) → ℕ → LUV} (pkg : SelectionPackage DP E M I Q)
    (hconc : Concentrates E M I)
    {S : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S) (hfol : Follows DP E M S)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    CondStableOn M pkg ↔ (fun n => E.estimate S n) ≳ₙ (fun n => M.maxQuote E n) :=
  ⟨fun h3 => endorse_of_concentrates hf hM pkg h3 hconc hS hfol hworld,
   fun hSE => condStableOn_of_selfEndorseGE_instance hf hM pkg hS hfol hSE hworld⟩

/-- **Consequence: the self-endorsement instance is follower-independent** on a menu with
concentration — if one follower of the argmax satisfies `E*(S_n) ≳ₙ M_n`, every follower does
(through H3, which mentions no follower).
Source: audit r1 fidelity item 3
Kind: C
Fidelity: exact
Hyps: (a); `hf`; `hconc` -/
theorem selfEndorseGE_instance_follower_indep {E : Expert DP} [IsLogicalInductor E.A DP]
    (hf : StrictlyIncreasingDeferral E.f) {k : ℕ} {M : Menu k} (hM : M.Valued DP)
    {I Q : Fin (k + 1) → ℕ → LUV} (pkg : SelectionPackage DP E M I Q)
    (hconc : Concentrates E M I)
    {S S' : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S) (hfol : Follows DP E M S)
    (hS' : LUV.MachineThresholdCodeSeq S') (hfol' : Follows DP E M S')
    (hSE : (fun n => E.estimate S n) ≳ₙ (fun n => M.maxQuote E n))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => E.estimate S' n) ≳ₙ (fun n => M.maxQuote E n) :=
  (condStableOn_iff_selfEndorseGE_instance hf hM pkg hconc hS' hfol' hworld).1
    ((condStableOn_iff_selfEndorseGE_instance hf hM pkg hconc hS hfol hworld).2 hSE)

/-- **`CondStableOn` is package-independent on a menu with concentration** (audit r2 fidelity N4):
two selection packages on the same menu, each with concentration, are conditionally stable
together or not at all — both are equivalent to the follower-independent self-endorsement
instance. Lets every inhabitant and refutation of H3 be read at the level of the menu.
Source: audit r2 fidelity N4
Kind: C
Fidelity: exact
Hyps: (a); `hf`; `hconc`, `hconc'` ((a) self) -/
theorem condStableOn_iff_of_packages {E : Expert DP} [IsLogicalInductor E.A DP]
    (hf : StrictlyIncreasingDeferral E.f) {k : ℕ} {M : Menu k} (hM : M.Valued DP)
    {I Q I' Q' : Fin (k + 1) → ℕ → LUV} (pkg : SelectionPackage DP E M I Q)
    (pkg' : SelectionPackage DP E M I' Q') (hconc : Concentrates E M I)
    (hconc' : Concentrates E M I') {S : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S)
    (hfol : Follows DP E M S) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    CondStableOn M pkg ↔ CondStableOn M pkg' :=
  (condStableOn_iff_selfEndorseGE_instance hf hM pkg hconc hS hfol hworld).trans
    (condStableOn_iff_selfEndorseGE_instance hf hM pkg' hconc' hS hfol hworld).symm

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **H3 ⟺ the self-endorsement instance, for the self-expert at grade (a)**: on every valued
e.c. menu with the self-expert's own package, `CondStableOn M (selectionPackage_self T f M) ↔
E*(S_n) ≳ₙ M_n` for any follower `S`; concentration is `concentrates_self`.
Source: audit r1 fidelity item 3; [[total-trust-implies-value]] §Lemma 2
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem condStableOn_iff_selfEndorseGE_instance_self (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) {k : ℕ} (M : Menu k) (hM : M.Valued (paperDP T))
    {S : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S)
    (hfol : Follows (paperDP T) (selfExpert T f) M S) :
    CondStableOn M (selectionPackage_self T f M) ↔
      (fun n => (selfExpert T f).estimate S n) ≳ₙ (fun n => M.maxQuote (selfExpert T f) n) :=
  condStableOn_iff_selfEndorseGE_instance hf hM (selectionPackage_self T f M)
    (concentrates_self T f hf M (selectionPackage_self T f M)) hS hfol (paperDP_hworld T)

/-- **For the self-expert, `CondStableOn` is package-independent on every valued e.c. menu**
(given a follower): concentration is `concentrates_self` for any package.
Source: audit r2 fidelity N4
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem condStableOn_iff_of_packages_self (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) {k : ℕ} (M : Menu k) (hM : M.Valued (paperDP T))
    {I Q I' Q' : Fin (k + 1) → ℕ → LUV}
    (pkg : SelectionPackage (paperDP T) (selfExpert T f) M I Q)
    (pkg' : SelectionPackage (paperDP T) (selfExpert T f) M I' Q')
    {S : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S)
    (hfol : Follows (paperDP T) (selfExpert T f) M S) :
    CondStableOn M pkg ↔ CondStableOn M pkg' :=
  condStableOn_iff_of_packages hf hM pkg pkg' (concentrates_self T f hf M pkg)
    (concentrates_self T f hf M pkg') hS hfol (paperDP_hworld T)

end

end Cleanroom.Deference.DefArgmaxValue
