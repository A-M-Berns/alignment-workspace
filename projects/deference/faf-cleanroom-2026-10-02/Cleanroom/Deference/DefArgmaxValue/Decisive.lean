import Cleanroom.Deference.DefArgmaxValue.Hedged
import Cleanroom.Deference.DefArgmaxValue.Instance
import Cleanroom.Found.LiAsympCalc.WeightedAverage

/-!
# `def-argmax-value` · Decisive: Value on eventually-decisive menus, pointwise and averaged (2-018; OP17's margins case)

Two corollaries of target 9 that the first formalizer's handoff left (items 4 and 2):

* **2-018 at the novice level** (`value_instance_of_decisive`): on a menu whose argmax eventually
  leads the runner-up by a fixed margin `η`, Total Trust plus blended quotes (with their
  composites and ramp quotes) at every width `δ < η/2` give the **hard** argmax follower
  `E^P_n(S_n) ≳ₙ E^P_n(O^i_n)` — `def-lattice`'s `Value` instance on that menu, with no
  conditional-stability hypothesis. Route: `hedgedValue_of_totalTrust` at width `δ` gives
  `E^P(T_δ) ≳ₙ E^P(O^i) − 2δ`; on decisive days the blend is the hard selection
  (`rampBlend_eq_of_decisive`), so `S_n` and `T_δ,n` are valued equal within the quote's slack and
  the novice's provind gives `E^P(S) ≈ₙ E^P(T_δ)`; `δ` is chosen below `ε/4` for each `ε`.
* **OP17, the margins case** (`averaged_value_of_decisive`): the same conclusion at the averaged
  grade, for every nonnegative non-summable weighting — because `≳ₙ` transports through weighted
  averages (`weightedAverage_asympGE`, a real-sequence lemma proved here: the negative part of
  `a − b` is eventually within `ε/2`, and `abs_weightedAverage_le_of_tail` washes out the finite
  prefix). This is the *margins* repair of vq-wiki-065 §8's refuted general-menu conjecture
  (`Averaged.lean`): what averaging cannot launder (the probe's one-signed deficit) a decisive
  margin removes. The lookahead-conditional-stability form of OP17 is not attempted.

The blended quotes and composites remain data `(c)` (findings F13); the margin hypothesis has its
N+ on the witness menu (`witnessMenu_decisive_margin`: `η = ⅛`).
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond
open Cleanroom.Found.LiAsympCalc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-! ## The data a width needs -/

/-- **The blended quote at a width, with its composite and ramp quotes** — the data of
`hedgedValue_of_totalTrust` at one `δ`, packaged: the blended LUV `T_δ` (`BlendQuote` for
`rampBlend δ`), its generable weights at rank `f n`, the composite `½(T_δ − O^i + 1)` and the
ramp quotes on it over the novice's process. Data `(c)` for every expert (findings F13).
Source: mandate target 9c–9d; [[soft-self-endorsement]]
Kind: D
Fidelity: exact (the hypotheses of `hedgedValue_of_totalTrust` at one width) -/
structure DecisiveData (DPE DPH : DeductiveProcess) (E : Expert DPE) {k : ℕ} (M : Menu k)
    (δ : ℚ) (i : Fin (k + 1)) where
  /-- the blended strategy -/
  Tδ : ℕ → LUV
  /-- its blend quote for the ramp blend at width `δ` -/
  q : BlendQuote DPE E M (rampBlend δ) Tδ
  /-- the rational blend weights -/
  θ : Fin (k + 1) → ℕ → ℚ
  /-- generable at the expert's market -/
  hθ : ∀ j, PGenerableRat E.A (θ j)
  /-- in `[0,1]` -/
  hθmem : ∀ j m, 0 ≤ θ j m ∧ θ j m ≤ 1
  /-- at the deferred day they are the ramp blend of the quotes -/
  hθcast : ∀ j n, ((θ j (E.f n) : ℚ) : ℝ) = rampBlend δ (fun i => M.quote E i n) j
  /-- the composite against option `i` -/
  comp : Composite DPE Tδ (M.O i)
  /-- ramp quotes on the composite over the novice's process -/
  hramp : RampQuotesAvailable DPH (E.recast DPH) comp.D

/-! ## 2-018 at the novice level -/

/-- **Value's instance on an eventually-decisive menu** (2-018, novice level): if the argmax
eventually leads every other option by `η > 0`, and blended quotes with composites and ramp
quotes exist at every width below `η/2`, then under Total Trust the hard argmax follower has
`E^P_n(S_n) ≳ₙ E^P_n(O^i_n)` — `Value`'s instance on this menu, with no conditional-stability
hypothesis (a margin condition replaces H3, as the margins corollary replaces it on the expert's
side). Two processes as `scoped_value`.
Source: 2-018 ("hedged and hard Value coincide on eventually-decisive menus");
[[soft-self-endorsement]] (the margins remark); mandate target 9d
Kind: C
Fidelity: exact (the hard follower; the conclusion is the exact `≳ₙ`)
Hyps: (a) 9b–9d and the novice's provind; `hf`, `hext`; (c) `hTT` (deference), `hdata` (the
blended quotes, composites and ramp quotes at every small width — the rich ledger); `hdec` is
the scope condition (its N+: `witnessMenu_decisive_margin`) -/
theorem value_instance_of_decisive {DPE DPH : DeductiveProcess}
    (hext : ∀ v : PCWorld, v.ConsistentWithTheory DPH → v.ConsistentWithTheory DPE)
    {E : Expert DPE} [IsLogicalInductor E.A DPE] (hf : StrictlyIncreasingDeferral E.f)
    {P : History} [IsLogicalInductor P DPH] {k : ℕ} {M : Menu k} (hM : M.Valued DPE)
    {η : ℝ} (hη : 0 < η)
    (hdec : ∀ᶠ n in atTop, ∀ j, j ≠ M.argmax E n →
      M.quote E j n + η ≤ M.quote E (M.argmax E n) n)
    (i : Fin (k + 1))
    (hdata : ∀ δ : ℚ, 0 < δ → 2 * (δ : ℝ) < η → Nonempty (DecisiveData DPE DPH E M δ i))
    (hTT : TotalTrust P DPH (E.recast DPH))
    {S : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S) (hfol : Follows DPE E M S)
    (hworldE : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPE.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) :
    (fun n => (S n).expect P n) ≳ₙ (fun n => (M.O i n).expect P n) := by
  intro ε hε
  obtain ⟨δ, hδ0, hδε⟩ := exists_rat_btwn (show (0 : ℝ) < min (ε / 4) (η / 4) by positivity)
  have hδ : 0 < δ := by exact_mod_cast hδ0
  have hδε' : (δ : ℝ) < ε / 4 := lt_of_lt_of_le hδε (min_le_left _ _)
  have hδη : 2 * (δ : ℝ) < η := by
    have := lt_of_lt_of_le hδε (min_le_right _ _); linarith
  obtain ⟨d⟩ := hdata δ hδ hδη
  have hhedge := hedgedValue_of_totalTrust hext hf hM δ hδ d.q d.θ d.hθ d.hθmem d.hθcast i d.comp
    hTT d.hramp hworldE hworldH
  have hSv : Valued DPE S := follows_valued hM hfol
  have hTv : Valued DPE d.Tδ := fun n v hv => by
    choose x hx using fun j => hM j n v hv
    obtain ⟨z, hz, -⟩ := d.q.reflected n v hv x hx
    exact ⟨z, hz⟩
  -- the novice's same-day provind: S and T_δ are valued equal within slack on decisive days
  set ts : List (ℚ × (ℕ → LUV)) := [(1, S), (-1, d.Tδ)] with hts
  have hagree : (fun n => (listComb (fun _ => (0 : ℚ)) ts n).expect P n) ≈ₙ
      (fun _ => (0 : ℝ)) := by
    refine expect_listComb_eq_of_eventually (P := P) (DP := DPH) (constStream_splice 0)
      (B := 0) (fun _ => by simp) (ts := ts) ?_ ?_ 0 ?_ hworldH
    · intro p hp
      simp only [hts, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hS
      · exact d.q.codes
    · exact listComb_worldValued _ (fun p hp => by
        simp only [hts, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact fun n v hv => hSv n v (hext v hv)
        · exact fun n v hv => hTv n v (hext v hv))
    · intro ε' hε'
      filter_upwards [hdec, (tendsto_order.1 d.q.slack_tendsto).2 ε' hε'] with n hn hs v hv ν hν
      have hv' := hext v hv
      choose x hx using fun j => hM j n v hv'
      obtain ⟨z, hz, hb⟩ := d.q.reflected n v hv' x hx
      have e1 := (listComb_valuesAt_mem hν (p := (1, S)) (by simp [hts])).eq
        (hfol n v hv' _ (hx _))
      have e2 := (listComb_valuesAt_mem hν (p := (-1, d.Tδ)) (by simp [hts])).eq hz
      obtain ⟨h1, h0⟩ := rampBlend_eq_of_decisive δ hδ (fun j => M.quote E j n) (M.argmax E n)
        hδη hn
      have hblend : ∑ j, rampBlend δ (fun j => M.quote E j n) j * x j = x (M.argmax E n) := by
        rw [Finset.sum_eq_single (M.argmax E n) (fun j _ hj => by rw [h0 j hj, zero_mul])
          (fun h => absurd (Finset.mem_univ _) h), h1, one_mul]
      rw [hblend] at hb
      rw [listComb_value]
      simp only [hts, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e1, e2]
      push_cast
      have key : (0 : ℝ) + (1 * x (M.argmax E n) + (-1 * z + 0)) - 0 =
          -(z - x (M.argmax E n)) := by ring
      rw [key, abs_neg]
      exact hb.trans hs.le
  have hE : (fun n => (listComb (fun _ => (0 : ℚ)) ts n).expect P n) =
      fun n => (S n).expect P n - (d.Tδ n).expect P n := by
    funext n
    rw [listComb_expect]
    simp only [hts, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring
  rw [hE] at hagree
  have h1 := hhedge (ε / 4) (by linarith)
  have h2 := asympEq_eventually_abs_le hagree (show (0 : ℝ) < ε / 4 by linarith)
  filter_upwards [h1, h2] with n hn1 hn2
  rw [abs_le] at hn2
  linarith [hn2.1, hn2.2, hδε']

/-! ## `≳ₙ` transports through weighted averages -/

/-- Weighted averages are monotone in the averaged sequence (nonnegative weights, positive mass).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem weightedAverage_le_weightedAverage {w r s : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) {n : ℕ}
    (hn : 0 < prefixSum w n) (hrs : ∀ i, r i ≤ s i) :
    weightedAverage w r n ≤ weightedAverage w s n := by
  rw [weightedAverage_eq_div hn.ne', weightedAverage_eq_div hn.ne']
  apply div_le_div_of_nonneg_right _ hn.le
  unfold prefixSum
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (hrs i) (hw i)

/-- **`≳ₙ` transports through nonnegative divergent weighted averages**: `a ≳ₙ b` gives
`avg_w a ≳ₙ avg_w b`. The negative part `min (a − b) 0` is eventually within `ε/2` of `0`, so its
average is (`abs_weightedAverage_le_of_tail` washes out the finite prefix), and
`avg_w a − avg_w b = avg_w (a − b) ≥ avg_w (min (a − b) 0)`.
Source: [[weak-loop-and-value-transport]] §1 (averaging and one-signed deficits); none: infrastructure
Kind: P
Fidelity: exact
Hyps: (a) `w` nonnegative, non-summable -/
theorem weightedAverage_asympGE {w a b : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hdiv : Tendsto (prefixSum w) atTop atTop) (h : a ≳ₙ b) :
    weightedAverage w a ≳ₙ weightedAverage w b := by
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (h (ε / 2) (by linarith))
  set t : ℕ → ℝ := fun i => min (a i - b i) 0 with ht
  have htb : ∀ i, N ≤ i → |t i| ≤ ε / 2 := fun i hi => by
    have := hN i hi
    rw [abs_le]
    constructor
    · simp only [ht]
      exact le_min (by linarith) (by linarith)
    · simp only [ht]
      exact (min_le_right _ _).trans (by linarith)
  have hlim : Tendsto (fun n => (∑ i ∈ Finset.range N, w i * |t i|) / prefixSum w n) atTop
      (𝓝 0) := hdiv.const_div_atTop _
  filter_upwards [eventually_prefixSum_pos hdiv,
    hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))] with n hpos hsmall
  have h1 : |weightedAverage w t n| ≤
      (∑ i ∈ Finset.range N, w i * |t i|) / prefixSum w n + ε / 2 :=
    abs_weightedAverage_le_of_tail hw htb hpos
  have h2 : weightedAverage w t n ≤ weightedAverage w (fun i => a i - b i) n :=
    weightedAverage_le_weightedAverage hw hpos (fun i => min_le_left _ _)
  rw [weightedAverage_sub w a b hpos.ne'] at h2
  have h3 := (abs_le.1 h1).1
  linarith

/-! ## OP17, the margins case -/

/-- **Scheduled averaged argmax Value under decisive quote-margins** (OP17's margins case): under
the hypotheses of `value_instance_of_decisive`, for every nonnegative non-summable weighting `w`,
`avg_w E^P_i(S_i) ≳ₙ avg_w E^P_i(O^j_i)`. The pointwise instance averaged
(`weightedAverage_asympGE`). What averaging cannot launder — the one-signed deficit of the liar
probe (`averaged_value_probe_refuted`) — a decisive margin removes. The lookahead
conditional-stability form of OP17 is not attempted.
Source: [[theorem-ss-streamlined]] §8 (OP17); [[weak-loop-and-value-transport]] §1; mandate
target 11b ("attempt the margins case first")
Kind: C
Fidelity: variant: the margins case of OP17, not its lookahead form
Hyps: as `value_instance_of_decisive`; (a) `w` nonnegative, non-summable -/
theorem averaged_value_of_decisive {DPE DPH : DeductiveProcess}
    (hext : ∀ v : PCWorld, v.ConsistentWithTheory DPH → v.ConsistentWithTheory DPE)
    {E : Expert DPE} [IsLogicalInductor E.A DPE] (hf : StrictlyIncreasingDeferral E.f)
    {P : History} [IsLogicalInductor P DPH] {k : ℕ} {M : Menu k} (hM : M.Valued DPE)
    {η : ℝ} (hη : 0 < η)
    (hdec : ∀ᶠ n in atTop, ∀ j, j ≠ M.argmax E n →
      M.quote E j n + η ≤ M.quote E (M.argmax E n) n)
    (i : Fin (k + 1))
    (hdata : ∀ δ : ℚ, 0 < δ → 2 * (δ : ℝ) < η → Nonempty (DecisiveData DPE DPH E M δ i))
    (hTT : TotalTrust P DPH (E.recast DPH))
    {S : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S) (hfol : Follows DPE E M S)
    (hworldE : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPE.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (hdiv : Tendsto (prefixSum w) atTop atTop) :
    weightedAverage w (fun n => (S n).expect P n) ≳ₙ
      weightedAverage w (fun n => (M.O i n).expect P n) :=
  weightedAverage_asympGE hw hdiv
    (value_instance_of_decisive hext hf hM hη hdec i hdata hTT hS hfol hworldE hworldH)

/-! ## The margin hypothesis is inhabited -/

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **The witness menu is eventually decisive with margin `⅛`**: `E*(G) → ½`, `E*(K_½) → ¼`
(the pinned undecided liar against the constant). The N+ of `hdec`.
Source: mandate target 4c (N+); 2-018
Kind: N+
Fidelity: exact
Hyps: (a); `hf` -/
theorem witnessMenu_decisive_margin (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    ∀ᶠ n in atTop, ∀ j, j ≠ (witnessMenu T f).argmax (selfExpert T f) n →
      (witnessMenu T f).quote (selfExpert T f) j n + (1 / 8 : ℝ) ≤
        (witnessMenu T f).quote (selfExpert T f) ((witnessMenu T f).argmax (selfExpert T f) n) n := by
  have hG : Tendsto (fun n => (witnessMenu T f).quote (selfExpert T f) 0 n) atTop
      (𝓝 ((1 / 2 : ℚ) : ℝ)) := by
    have := liarPrice_tendsto_s T f (1 / 2) hf (by norm_num) (by norm_num)
    refine (tendsto_congr (fun n => ?_)).mp this
    simp [witnessMenu, twoOptionMenu, Menu.quote, witnessG, literalIndicator_expect]
  have hK : Tendsto (fun n => (witnessMenu T f).quote (selfExpert T f) 1 n) atTop
      (𝓝 (((1 - 1 / 2) / 2 : ℚ) : ℝ)) := by
    have := tendsto_of_asympEq_const (asympEq_comp_deferral (expect_constLUV_asympEq
      (P := liaHistory (paperDP T)) (DP := paperDP T) (probeConst_mem (ε := 1 / 2) (by norm_num)
        (by norm_num)) (paperDP_hworld T)) f)
    refine (tendsto_congr (fun n => ?_)).mp this
    simp [witnessMenu, twoOptionMenu, Menu.quote, probeConst]
  have h1 := (tendsto_order.1 hG).1 ((7 / 16 : ℚ) : ℝ) (by norm_num)
  have h2 := (tendsto_order.1 hK).2 ((5 / 16 : ℚ) : ℝ) (by norm_num)
  filter_upwards [h1, h2] with n hn1 hn2
  push_cast at hn1 hn2
  have hsel : (witnessMenu T f).argmax (selfExpert T f) n = 0 := by
    rw [Menu.argmax_two, if_pos (by linarith)]
  rw [hsel]
  refine Fin.forall_fin_two.2 ⟨fun hj => absurd rfl hj, fun _ => ?_⟩
  linarith

/-! ## Repair round 1: the eventually-constant stratum, with its N+ (audit r1 N5, B1) -/

/-- **Value's instance on a menu whose selection is eventually constant** (2-018, the
eventually-constant stratum; audit r1 N5): if the argmax is eventually the fixed index `j*`, then
with a composite of the hard follower against `O^i`, ramp quotes on it and Total Trust, the novice
has `E^P_n(S_n) ≳ₙ E^P_n(O^i_n)`. No blended quotes, no conditional-stability, no fold: the
self-endorsement instance `E*(S) ≳ₙ M_n` is deferred provind on `S − O^{j*}` (eventually valued
`0` in every world), and Lemma 1 on the composite (`value_of_selfEndorse_instance`) finishes.
This is the stratum in which every known H3 witness lives (`scoped_value_witness`'s register);
the moving-argmax margin form is `value_instance_of_decisive`, which needs the blended quotes
because the family `n ↦ O^{argmax_n}_n` is not an e.c. family for a general expert.
Source: 2-018; audit r1 N5; mandate target 9d
Kind: C
Fidelity: exact (the hard follower; exact `≳ₙ`)
Hyps: (a) provind, Lemma 1; `hf`, `hext`; (c) `hTT` (deference), `hramp`, `comp`; `hconst` the
scope condition (N+: `witness_argmax_eventually_zero`) -/
theorem value_instance_of_eventually_constant {DPE DPH : DeductiveProcess}
    (hext : ∀ v : PCWorld, v.ConsistentWithTheory DPH → v.ConsistentWithTheory DPE)
    {E : Expert DPE} [IsLogicalInductor E.A DPE] (hf : StrictlyIncreasingDeferral E.f)
    {P : History} [IsLogicalInductor P DPH] {k : ℕ} {M : Menu k} (hM : M.Valued DPE)
    {j : Fin (k + 1)} (hconst : ∀ᶠ n in atTop, M.argmax E n = j)
    {S : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S) (hfol : Follows DPE E M S)
    (i : Fin (k + 1)) (comp : Composite DPE S (M.O i))
    (hTT : TotalTrust P DPH (E.recast DPH))
    (hramp : RampQuotesAvailable DPH (E.recast DPH) comp.D)
    (hworldE : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPE.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n)) :
    (fun n => (S n).expect P n) ≳ₙ (fun n => (M.O i n).expect P n) := by
  have hSv : Valued DPE S := follows_valued hM hfol
  -- E*(S) ≈ₙ E*(O^{j*}): deferred provind on S − O^{j*}, eventually valued 0
  have hagree : (fun n => E.estimate S n) ≈ₙ (fun n => E.estimate (M.O j) n) := by
    have h := expect_deferred_asympEq_zero_of_eventually_abs_le (P := E.A) (DP := DPE) E.f hf
      (c₀ := fun _ => EF.const 0) (constWeighting 0)
      (terms := [((fun _ => EF.const 1), S), ((fun _ => EF.const (-1)), M.O j)])
      (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> exact constWeighting _)
      (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact hS
        · exact M.codes j)
      (fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact hSv
        · exact hM j)
      (B := 2) (by norm_num) (fun m => by simp [EF.denote_const]; try norm_num)
      (fun ε hε => by
        filter_upwards [hconst] with n hn v hv ν hν
        obtain ⟨x, hx⟩ := hM j n v hv
        have hxS : v.ValuesAt (S n) x := hfol n v hv x (by rw [hn]; exact hx)
        have e1 : ν (S n) = x := (hν ((fun _ => EF.const 1), S) (by simp)).eq hxS
        have e2 : ν (M.O j n) = x := (hν ((fun _ => EF.const (-1)), M.O j) (by simp)).eq hx
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const,
          e1, e2]
        push_cast
        have : (0 : ℝ) + (1 * x + (-1 * x + 0)) = 0 := by ring
        rw [this, abs_zero]
        exact hε.le) hworldE
    have hE : deferredExpect E.A E.f (fun _ => EF.const 0)
        [((fun _ => EF.const 1), S), ((fun _ => EF.const (-1)), M.O j)] =
        fun n => E.estimate S n - E.estimate (M.O j) n := by
      funext n
      simp [deferredExpect, EF.denote_const, Expert.estimate]
      try ring
    rw [hE] at h
    unfold AsympEq at h ⊢
    simpa using h
  -- hence E*(S) ≳ₙ M_n (eventually m^{j*} = M_n)
  have hSE : (fun n => E.estimate S n) ≳ₙ (fun n => M.maxQuote E n) := by
    intro ε hε
    filter_upwards [asympEq_eventually_abs_le hagree hε, hconst] with n hn1 hn2
    rw [abs_le] at hn1
    have hatt := M.argmax_attains E n
    rw [hn2] at hatt
    simp only [Menu.quote] at hatt
    linarith [hn1.1, hn1.2]
  exact value_of_selfEndorse_instance hext hf hM hS hSv hSE i comp hTT hramp hworldE hworldH

/-- The witness menu's selection is eventually the constant `0` (audit r1 probe
`WitnessDecisive.lean`, adopted): the register fact behind `scoped_value_witness`.
Source: audit r1 B1
Kind: L
Fidelity: exact
Hyps: (a); `hf` -/
theorem witness_argmax_eventually_zero (f : DeferralFunction) (hf : StrictlyIncreasingDeferral f) :
    ∀ᶠ n in atTop, (witnessMenu T f).argmax (selfExpert T f) n = 0 :=
  (witnessMenu_decisive T f hf).mono (fun n hn => by rw [Menu.argmax_two, if_pos hn.le])

/-- **The eventually-constant instance, fully inhabited on the witness menu** (N+ for joint
satisfiability of `value_instance_of_eventually_constant`, audit r1 N5): every hypothesis is a
theorem — the constant selection (`witness_argmax_eventually_zero`), the follower, the composites
(`probeComposite_zero/one`), ramp quotes, Total Trust — for both `i`. Same register as
`scoped_value_witness`: the conclusion also follows from the pins alone
(`witness_value_one_without_hypotheses`).
Source: audit r1 N5, B1
Kind: N+
Fidelity: exact
Hyps: (a) none; `hf` -/
theorem value_witness_of_eventually_constant (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) (i : Fin 2) :
    (fun n => (witnessS T f n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun n => ((witnessMenu T f).O i n).expect (liaHistory (paperDP T)) n) := by
  have hTT : TotalTrust (liaHistory (paperDP T)) (paperDP T) ((selfExpert T f).recast (paperDP T)) :=
    selfTotalTrust T f hf.injective
  fin_cases i
  · exact value_instance_of_eventually_constant (DPE := paperDP T) (DPH := paperDP T)
      (fun _ hv => hv) hf (witnessMenu_valued T f) (witness_argmax_eventually_zero T f hf)
      (witnessS_codes T f) (witnessS_follows T f) 0 (probeComposite_zero T f) hTT
      (paperExpert_rampQuotesAvailable T f (extendsBase_self T) hf.injective
        (probeComposite_zero T f).codes ((probeComposite_zero T f).valued
          (follows_valued (witnessMenu_valued T f) (witnessS_follows T f))
          (witnessMenu_valued T f 0)))
      (paperDP_hworld T) (paperDP_hworld T)
  · exact value_instance_of_eventually_constant (DPE := paperDP T) (DPH := paperDP T)
      (fun _ hv => hv) hf (witnessMenu_valued T f) (witness_argmax_eventually_zero T f hf)
      (witnessS_codes T f) (witnessS_follows T f) 1 (probeComposite_one T f) hTT
      (paperExpert_rampQuotesAvailable T f (extendsBase_self T) hf.injective
        (probeComposite_one T f).codes ((probeComposite_one T f).valued
          (follows_valued (witnessMenu_valued T f) (witnessS_follows T f))
          (witnessMenu_valued T f 1)))
      (paperDP_hworld T) (paperDP_hworld T)

/-- **The `i = 1` conclusion of `scoped_value_witness`, from the pins alone** (audit r1 probe
`WitnessDecisive.lean`, adopted): `E^P(S) → ½` (same-day provind on `S − G`, eventually valued
`0`, plus `P_n(θ_n) → ½`) and `E^P(K_½) → ¼`. No Total Trust, no fold, no `CondStableOn` — the
machine-checked reason the witness is N− for the content of the scoped theorem.
Source: audit r1 B1
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem witness_value_one_without_hypotheses (f : DeferralFunction)
    (hf : StrictlyIncreasingDeferral f) :
    (fun n => (witnessS T f n).expect (liaHistory (paperDP T)) n) ≳ₙ
      (fun n => ((witnessMenu T f).O 1 n).expect (liaHistory (paperDP T)) n) := by
  -- the follower is eventually valued as G in every world
  have hσ : ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) →
      v.Holds (witnessσ T f n) := by
    refine (witnessMenu_decisive T f hf).mono (fun n hn v hv => ?_)
    rw [witnessσ, followSentence_holds_iff T f _ _ n v hv]
    have e0 : (witnessG T f n).expect (liaHistory (paperDP T)) (f n) =
        (((paperMarketComputation T).expectQuoteAt (witnessG T f) n (f n) : ℚ) : ℝ) :=
      (paperMarketComputation T).expectQuoteAt_cast (witnessG T f) n (f n)
    have e1 : (probeConst (1 / 2) n).expect (liaHistory (paperDP T)) (f n) =
        (((paperMarketComputation T).expectQuoteAt (probeConst (1 / 2)) n (f n) : ℚ) : ℝ) :=
      (paperMarketComputation T).expectQuoteAt_cast (probeConst (1 / 2)) n (f n)
    have hn' : (((paperMarketComputation T).expectQuoteAt (probeConst (1 / 2)) n (f n) : ℚ) : ℝ) <
        (((paperMarketComputation T).expectQuoteAt (witnessG T f) n (f n) : ℚ) : ℝ) := by
      rw [← e0, ← e1]
      exact hn
    exact_mod_cast hn'.le
  have hSG : ∀ᶠ n in atTop, ∀ v : PCWorld, v.ConsistentWithTheory (paperDP T) →
      v.ValuesAt (witnessS T f n) (v.payout (liarSentence T f (1 / 2) (by norm_num) n)) := by
    refine hσ.mono (fun n hn v hv => ?_)
    have h := witnessS_valuesAt T f n v hv
    rwa [if_pos (hn v hv)] at h
  -- same-day provind: E^P(S) ≈ₙ P_n(θ_n)
  have hS : (fun n => (witnessS T f n).expect (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (liaHistory (paperDP T)) n (liarSentence T f (1 / 2) (by norm_num) n)) := by
    set ts : List (ℚ × (ℕ → LUV)) := [(1, witnessS T f), (-1, witnessG T f)] with hts
    have hSv : Valued (paperDP T) (witnessS T f) :=
      follows_valued (witnessMenu_valued T f) (witnessS_follows T f)
    have h := expect_listComb_eq_of_eventually (P := liaHistory (paperDP T)) (DP := paperDP T)
      (constStream_splice 0) (B := 1) (fun _ => by norm_num) (ts := ts)
      (fun p hp => by
        simp only [hts, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact witnessS_codes T f
        · exact witnessG_codes T f)
      (listComb_worldValued _ (fun p hp => by
        simp only [hts, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact hSv
        · exact witnessG_valued T f))
      0 (fun ε hε => by
        refine hSG.mono (fun n hn v hv ν hν => ?_)
        have e1 := (listComb_valuesAt_mem hν (p := (1, witnessS T f)) (by simp [hts])).eq (hn v hv)
        have e2 := (listComb_valuesAt_mem hν (p := (-1, witnessG T f)) (by simp [hts])).eq
          (literalIndicator_valuesAt _ (paperDP T) hv)
        rw [listComb_value]
        simp only [hts, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e1, e2]
        push_cast
        rw [abs_le]
        constructor <;> linarith)
      (paperDP_hworld T)
    have hE : (fun n => (listComb (fun _ => (0 : ℚ)) ts n).expect (liaHistory (paperDP T)) n) =
        fun n => (witnessS T f n).expect (liaHistory (paperDP T)) n -
          (liaHistory (paperDP T)) n (liarSentence T f (1 / 2) (by norm_num) n) := by
      funext n
      rw [listComb_expect]
      simp only [hts, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, witnessG,
        literalIndicator_expect]
      push_cast
      ring
    rw [hE] at h
    unfold AsympEq at h ⊢
    simpa using h
  have hp := liarPresentPrice_tendsto_s T f (1 / 2) hf (by norm_num) (by norm_num)
  have hK : Tendsto (fun n => ((witnessMenu T f).O 1 n).expect (liaHistory (paperDP T)) n) atTop
      (𝓝 (((1 - 1 / 2) / 2 : ℚ) : ℝ)) := by
    have := tendsto_of_asympEq_const (expect_constLUV_asympEq (P := liaHistory (paperDP T))
      (DP := paperDP T) (probeConst_mem (ε := 1 / 2) (by norm_num) (by norm_num))
      (paperDP_hworld T))
    refine (tendsto_congr (fun n => ?_)).mp this
    simp [witnessMenu, twoOptionMenu, probeConst]
  have hSlim : Tendsto (fun n => (witnessS T f n).expect (liaHistory (paperDP T)) n) atTop
      (𝓝 ((1 / 2 : ℚ) : ℝ)) := by
    unfold AsympEq at hS
    have := hS.add hp
    refine (tendsto_congr (fun n => ?_)).mp (by simpa using this)
    ring
  have hdiff := hSlim.sub hK
  have hpos : (0 : ℝ) < ((1 / 2 : ℚ) : ℝ) - (((1 - 1 / 2) / 2 : ℚ) : ℝ) := by norm_num
  have hev := (tendsto_order.1 hdiff).1 0 hpos
  intro ε hε
  filter_upwards [hev] with n hn
  linarith

end

end Cleanroom.Deference.DefArgmaxValue
