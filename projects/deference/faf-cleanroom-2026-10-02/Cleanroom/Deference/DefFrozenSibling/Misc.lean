import Cleanroom.Deference.DefFrozenSibling.Engine
import Cleanroom.Found.LiAsympCalc.Amplifier

/-!
# `def-frozen-sibling` · Misc: T6 (calibration on `G` is degenerate), T12 (the ratio gate), T13
(horizon monotonicity of the decided clause), and the F5/F6 lemmas

* **T6** (anson-022; root-deference-043): on `G'`, binning by quote value is the diagonal
  *because the bins sit at `{0,1}`* — every interior bin `|a_n − v| ≤ δ` with `v ∈ (0,1)` is
  eventually empty on `G'` (`calibration_onG_degenerate`, kind L over `engineA_truth`, N− by the
  sources' own admission: no headline row). The amplifier `amp c e = (1+2c)e − c` of
  `li-asymp-calc` / `def-lattice-arrows` (`soft_upper_cut_nonneg`, `soft_lower_cut_nonneg`: it
  passes every threshold-trust inequality) survives off `G`: `amp_ne_id_of_ne_half` records that
  it is not the identity — **except at `e = 1/2`, its fixed point** (`amp_half`); the mandate's
  suggested `amp_ne_id_interior : 0 < e → e < 1 → amp c e ≠ e` is false there, findings F12.
* **T12** (anson-2-012): the non-removable gate on real sequences — `x ≳ₙ p·y` and `y` eventually
  bounded below by `c > 0` give `x/y ≳ₙ p` (`ratio_asympGE_of_denom_bdd`), and the N− witness that
  it fails when `y → 0` (`ratio_fails_of_denom_tendsto_zero`).
* **T13** (root-fa-2-011 (ii)): the decided clause is monotone in the horizon
  (`decidedBy_mono`); the tolerance clause is not known to be, and the negative existence is OPEN
  of record for FAF's pinned LIA family (`timely_not_mono_open`, `OffG.lean` §F, restated in
  repair round 1); over the free carrier the tolerance clause is not a function of the horizon at
  all (`timely_not_horizon_only`, `OnG.lean` §F; findings F8).
* **F5** (anson-025): a contract widened to a ledger literal is never decided in a base free of the
  ledger family, so it is never timely and T3 is untouched (`ledgerLiteral_not_mem_of_tagFree`).
* **F6** (anson-2-013): on a two-point space, `E[X] ≥ s` does not survive multiplication by a
  correlated indicator (`twoPoint_indicator_breaks_inequality`, N−).
-/

namespace Cleanroom.Deference.DefFrozenSibling

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefTrackingPin
open Filter Topology

/-! ## A. T6: calibration on `G'` is the diagonal because the bins sit at `{0,1}` -/

/-- **T6 — the interior bins are eventually empty on `G'`**: for `v ∈ (0,1)` and
`0 < δ < min v (1 − v)`, eventually on `G'` the quote is farther than `δ` from `v`. From
`engineA_truth` (`a_n ≈ truthAt n ∈ {0,1}` along `G'`). "Calibration on `G` is the diagonal"
because every bin that could witness a non-diagonal curve is empty — N− by the sources' own
admission ("the on-`G` statement is a T/near-vacuity risk"); no headline row.
Source: [[frozen-deliberation-deference-v6]] T6 (lines 120–124; anson-022); [[deference-in-logical-induction-v6]] §5.5 T6 (root-deference-043)
Kind: L
Fidelity: exact (the source's "bins sit at the extremes", made precise)
Hyps: (c) `hz` through T1; all else (a) -/
theorem calibration_onG_degenerate (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ}
    (hG : ∀ n, t n = 0 → Timely S ε n) (zhat : ℕ → ℚ) (hz : PGenerableRat S.A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0)) (v : ℝ) (hv0 : 0 < v)
    (hv1 : v < 1) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ < min v (1 - v)) :
    ∀ᶠ n in atTop, t n = 0 → δ < |(S.a n : ℝ) - v| := by
  have hη : (0 : ℝ) < (min v (1 - v) - δ) / 2 := by linarith
  filter_upwards [engineA_truth S ε hε hG zhat hz hlim _ hη] with n hn h0
  have h := hn h0
  have hmin1 := min_le_left v (1 - v)
  have hmin2 := min_le_right v (1 - v)
  have htv : min v (1 - v) ≤ |(truthAt S n : ℝ) - v| := by
    rcases truthAt_eq_zero_or_one S n with hz0 | ho
    · rw [hz0]; push_cast
      rw [zero_sub, abs_neg, abs_of_pos hv0]; exact hmin1
    · rw [ho]; push_cast
      rw [abs_of_pos (by linarith)]; exact hmin2
  have htri : |(truthAt S n : ℝ) - v| ≤ |(S.a n : ℝ) - truthAt S n| + |(S.a n : ℝ) - v| := by
    calc |(truthAt S n : ℝ) - v| = |((truthAt S n : ℝ) - S.a n) + ((S.a n : ℝ) - v)| := by ring_nf
      _ ≤ |(truthAt S n : ℝ) - S.a n| + |(S.a n : ℝ) - v| := abs_add_le _ _
      _ = |(S.a n : ℝ) - truthAt S n| + |(S.a n : ℝ) - v| := by rw [abs_sub_comm]
  linarith

/-- The amplifier fixes `1/2`: `amp c (1/2) = 1/2` for every `c`.
Source: none: infrastructure (correcting the mandate's `amp_ne_id_interior`, findings F12)
Kind: L
Fidelity: n/a -/
theorem amp_half (c : ℝ) : amp c (1 / 2) = 1 / 2 := by
  unfold amp; ring

/-- **The amplifier survives off `G`**: for `c > 0` it is not the identity anywhere but at its
fixed point `1/2` — `amp c e ≠ e` for `e ≠ 1/2`. It passes every threshold-trust inequality
(`def-lattice-arrows`' `soft_upper_cut_nonneg`, `soft_lower_cut_nonneg`; `li-asymp-calc`'s
`amp_upper_cut`, `amp_lower_cut`), so threshold trust alone cannot pin the calibration curve to the
diagonal; on `G` it is excluded by `calibration_onG_degenerate`, not by a sharper squeeze.
Source: [[frozen-deliberation-deference-v6]] T6 ("the amplifier … is not the identity"); anson-022
Kind: L
Fidelity: exact (with the fixed point at `1/2` made explicit)
Hyps: (a) none -/
theorem amp_ne_id_of_ne_half {c e : ℝ} (hc : 0 < c) (he : e ≠ 1 / 2) : amp c e ≠ e := by
  unfold amp
  intro h
  apply he
  have : 2 * c * e = c := by linarith
  have hc' : c ≠ 0 := hc.ne'
  field_simp
  nlinarith

/-! ## B. T12: the non-removable gate on real sequences -/

/-- **T12 — the ratio inequality needs the denominator bounded away from `0`**: if `x ≳ₙ p·y`,
`y ≥ 0`, and eventually `y ≥ c > 0`, then `x/y ≳ₙ p`. The gate `c` cannot be removed
(`ratio_fails_of_denom_tendsto_zero`).
Source: anson-2-012 (the averaged proof spine's division step)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ratio_asympGE_of_denom_bdd {x y : ℕ → ℝ} {p : ℝ} (h : x ≳ₙ fun n => p * y n)
    {c : ℝ} (hc : 0 < c) (hb : ∀ᶠ n in atTop, c ≤ y n) :
    (fun n => x n / y n) ≳ₙ fun _ => p := by
  intro ε hε
  filter_upwards [h (ε * c) (mul_pos hε hc), hb] with n hn hcn
  have hy : 0 < y n := lt_of_lt_of_le hc hcn
  have h1 : ε * c ≤ ε * y n := mul_le_mul_of_nonneg_left hcn hε.le
  rw [show x n / y n + ε = (x n + ε * y n) / y n by field_simp, le_div_iff₀ hy]
  linarith

/-- **The gate is non-removable (N−)**: with `y → 0` the hypothesis `x ≳ₙ 1·y` holds while
`x/y ≳ₙ 1` fails (`x_n = 1/(n+1)²`, `y_n = 1/(n+1)`).
Source: anson-2-012
Kind: N-
Fidelity: n/a
Hyps: (a) none -/
theorem ratio_fails_of_denom_tendsto_zero :
    ∃ x y : ℕ → ℝ, (∀ n, 0 ≤ y n) ∧ (x ≳ₙ fun n => 1 * y n) ∧
      Tendsto y atTop (𝓝 0) ∧ ¬ ((fun n => x n / y n) ≳ₙ fun _ => 1) := by
  refine ⟨fun n => 1 / ((n : ℝ) + 1) ^ 2, fun n => 1 / ((n : ℝ) + 1), fun n => by positivity,
    ?_, tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  · intro ε hε
    have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hlim.eventually (eventually_le_nhds hε)] with n hn
    have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) ^ 2 := by positivity
    linarith
  · intro hcon
    have h := hcon (1 / 2) (by norm_num)
    rw [Filter.eventually_atTop] at h
    obtain ⟨N, hN⟩ := h
    have := hN (max N 3) (le_max_left _ _)
    have h3 : (3 : ℝ) ≤ ((max N 3 : ℕ) : ℝ) := by exact_mod_cast le_max_right N 3
    have hpos : (0 : ℝ) < ((max N 3 : ℕ) : ℝ) + 1 := by linarith
    have hq : (1 / (((max N 3 : ℕ) : ℝ) + 1) ^ 2) / (1 / (((max N 3 : ℕ) : ℝ) + 1)) =
        1 / (((max N 3 : ℕ) : ℝ) + 1) := by
      field_simp
    dsimp only at this
    rw [hq] at this
    have h4 : 1 / (((max N 3 : ℕ) : ℝ) + 1) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ hpos (by norm_num)]
      linarith
    linarith

/-! ## C. T13: the decided clause is monotone in the horizon -/

/-- **T13 — the decided clause is monotone in the horizon**: for two systems with the same shared
process and contract family and horizons `F ≤ F'`, `DecidedBy S n → DecidedBy S' n` (stages are
nested). The tolerance clause of `Timely` is **not** covered: `S'.Y n` is a different sibling's
verdict at a later day, and nothing here says it is closer to the decided value (findings F8;
`timely_not_mono_open`, `OffG.lean` §F, for FAF's pinned LIA family at a strictly later horizon;
over the free carrier the clause is not a function of the horizon at all —
`timely_not_horizon_only`, `OnG.lean` §F).
Source: root-fa-2-011 (ii); [[legitimacy-theory-v1]] §7.2 ("grow `G`")
Kind: L
Fidelity: exact (decided clause only)
Hyps: (a) none -/
theorem decidedBy_mono (S S' : FrozenSystem) (hb : S'.base = S.base)
    (hc : S'.contract = S.contract) (hF : ∀ n, S.F.f n ≤ S'.F.f n) (n : ℕ)
    (h : DecidedBy S n) : DecidedBy S' n := by
  unfold DecidedBy at h ⊢
  rw [hb, hc]
  rcases h with h | h
  · exact Or.inl (S.base.mono_le (hF n) h)
  · exact Or.inr (S.base.mono_le (hF n) h)

/-! ## D. F5: a ledger literal is never decided in a ledger-free base -/

/-- **F5 — a contract widened to a ledger literal is never decided in the shared process** when
that process is free of the ledger family (as every base of record is): neither
`⌜α_{j,n} > r⌝` nor its negation lies in any stage. So such a contract is never timely, and T3 is
untouched — the anti-inductive contract anson-025 flags cannot be written in the base language.
Source: anson-025 (flag: "v6 §5 restricts `P^{(n)}` to base-language quantities"); mandate F5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem ledgerLiteral_not_mem_of_tagFree {DP : DeductiveProcess}
    (hfree : TagFreeProcess (cleanroomBaseTag + ledgerFamily) DP) (j n : ℕ) (r : ℚ) (k : ℕ) :
    (ledgerLuv j n).gt r ∉ DP.D k ∧ ∼((ledgerLuv j n).gt r) ∉ DP.D k := by
  constructor
  · intro hmem
    have h := hfree k _ hmem
    rw [ledgerLuv_gt] at h
    exact (h.freshAtomCode_notMem (ledgerPayload j n (Encodable.encode r))) (by simp)
  · intro hmem
    have h := hfree k _ hmem
    rw [ledgerLuv_gt] at h
    have h' : TagFreeSentence (cleanroomBaseTag + ledgerFamily)
        (freshAtom ledgerFamily (ledgerPayload j n (Encodable.encode r))) := by
      intro a ha
      exact h a (by simpa using ha)
    exact (h'.freshAtomCode_notMem (ledgerPayload j n (Encodable.encode r))) (by simp)

/-! ## E. F6: an expectation inequality does not survive a correlated indicator -/

/-- **F6 — the two-point N− example** (anson-2-013's "multiply by `Cert_n`" is a non-sequitur):
on the uniform two-point space, `X = (1, 0)`, `C = (0, 1)`, `s = 1/2`: `E[X] = 1/2 ≥ s`, yet
`E[X·C] = 0 < 1/4 = s·E[C]`.
Source: anson-2-013 (chat 05 L10771–10790)
Kind: N-
Fidelity: n/a
Hyps: (a) none -/
theorem twoPoint_indicator_breaks_inequality :
    ∃ (X C : Fin 2 → ℝ) (s : ℝ), (∀ i, 0 ≤ C i ∧ C i ≤ 1) ∧
      s ≤ (∑ i, X i) / 2 ∧ (∑ i, X i * C i) / 2 < s * ((∑ i, C i) / 2) := by
  refine ⟨fun i => if i = 0 then 1 else 0, fun i => if i = 0 then 0 else 1, 1 / 2, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0 <;> simp [hi]
  · norm_num [Fin.sum_univ_two]
  · norm_num [Fin.sum_univ_two]

end Cleanroom.Deference.DefFrozenSibling
