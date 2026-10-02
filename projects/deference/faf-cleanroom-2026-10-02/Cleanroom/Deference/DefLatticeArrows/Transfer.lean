import Cleanroom.Deference.DefLatticeArrows.Packages

/-!
# T6 — Bounds transfer: soft Total Trust lifts the expert's lower bound to the novice

Package `def-lattice-arrows`, file 2. [[total-trust-implies-value]] §Lemma 1 and PDF slide 19
("TT implies `E^A_n(V_n) ≳ₙ v ⟹ E^H_n(V_n) ≳ₙ v`"; the slide's `s − ε` is `v − ε`,
root-deference-016), in the true LI setting over `def-lattice`'s objects:

* `transfer_instance` — one ramp `WeightQuote` at threshold `v − ε` and width `δ < ε`, its
  soft Total-Trust instance, and the expert's asymptotic lower bound `hA` give
  `E^H_n(X_n) ≳ₙ v − ε`. The ramp is used through **saturation only** (it is eventually
  exactly `1` in every consistent world, `ctsInd_eq_one_iff`); its slope never enters — the
  point of Lemma 1, "in this lemma the ramp is machinery, not slack".
* `expert_bound_transfer` — the headline: a package for every rational `ε > 0` gives
  `E^H_n(X_n) ≳ₙ v` (diagonalizing `ε`, `asympGE_of_forall_rat_sub`).
* `expert_bound_transfer_of_totalTrust` — the predicate-level corollary from `TotalTrust` and an
  existence clause for the ramp quotes (`RampQuotesAvailable`, `(c)` for a general expert).

The width condition is `δ < ε` (Lemma 1 asks `δ < ε/2`; the halving is spent only in its
threshold-zero remark, which translates the bet by a rational constant and is not
formalized here — it needs the translate as a LUV, an affine-image package).
-/

namespace Cleanroom.Deference.DefLatticeArrows

open LogicalInduction Filter Topology Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc

noncomputable section

variable {P : History} {DP : DeductiveProcess}

/-- **Saturation**: under `E*(X_n) ≳ₙ v` and `δ < ε`, the above-ramp at threshold `v − ε` of the
expert's estimate is eventually exactly `1` (Lemma 1 (b)).
Source: [[total-trust-implies-value]] §Lemma 1 (b); li-asymp-calc `ctsInd_eq_one_iff`
Kind: L
Fidelity: exact -/
theorem ramp_eventually_one {E : Expert DP} {X : ℕ → LUV} {v ε δ : ℚ} (hδ : 0 < δ)
    (hδε : δ < ε) (hA : (fun n => E.estimate X n) ≳ₙ (fun _ => (v : ℝ))) :
    ∀ᶠ n in atTop, rampAbove δ (v - ε) (E.estimate X n) = 1 := by
  have hpos : (0 : ℝ) < ε - δ := by
    have : (δ : ℝ) < ε := by exact_mod_cast hδε
    linarith
  filter_upwards [hA ((ε : ℝ) - δ) hpos] with n hn
  simp only [rampAbove]
  rw [ctsInd_eq_one_iff hδ]
  push_cast
  linarith

/-- The weight quote's expectation tends to `1` once the ramp saturates: `W_n` is valued
exactly `1` in every consistent world from some day on, and the ε-outside pattern (T0) carries
it through `E^H_n`.
Source: [[total-trust-implies-value]] §Lemma 1, third step ("provability induction drives
`E^H_n(w_n) → 1`")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem expect_weight_asympEq_one [IsLogicalInductor P DP] {E : Expert DP}
    {X W XW : ℕ → LUV} {wt : ℝ → ℝ} (q : WeightQuote DP E X wt W XW)
    (hone : ∀ᶠ n in atTop, wt (E.estimate X n) = 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (W n).expect P n) ≈ₙ (fun _ => (1 : ℝ)) := by
  have h := expect_listComb_eq_of_eventually (P := P) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp) (ts := [(1, W)])
    (fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact q.weight_codes)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_singleton] at hp; subst hp
      exact fun n v hv => ⟨_, q.weight_reflected n v hv⟩))
    (1 : ℝ) (fun ε hε => by
      filter_upwards [hone] with n hn v hv ν hν
      have hW := listComb_valuesAt_mem hν (p := (1, W)) (List.mem_singleton_self _)
      rw [listComb_value]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hW.eq (q.weight_reflected n v hv), hn]
      simpa using hε.le) hworld
  refine (tendsto_congr (fun n => ?_)).mp h
  simp [listComb_expect]

/-- The product quote's expectation tracks the source's once the ramp saturates: `XW_n` is
valued within `slack n` of `x · 1 = x` where `X_n` is valued `x`.
Source: [[total-trust-implies-value]] §Lemma 1, first step (`Γ ⊢ X_n w_n = X_n` for `n ≥ N`,
here within FAF's `dd:mesh` slack)
Kind: C
Fidelity: exact (within slack)
Hyps: (a) -/
theorem expect_product_asympEq_source [IsLogicalInductor P DP] {E : Expert DP}
    {X W XW : ℕ → LUV} {wt : ℝ → ℝ} (hX : LUV.MachineThresholdCodeSeq X)
    (q : WeightQuote DP E X wt W XW)
    (hone : ∀ᶠ n in atTop, wt (E.estimate X n) = 1)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (XW n).expect P n) ≈ₙ (fun n => (X n).expect P n) := by
  have h := expect_listComb_eq_of_eventually (P := P) (DP := DP) (constStream_splice 0)
    (B := 0) (fun _ => by simp) (ts := [(1, XW), (-1, X)])
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact q.product_codes
      · exact hX)
    (listComb_worldValued _ (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · intro n v hv
        obtain ⟨x, hx⟩ := q.source_valued n v hv
        obtain ⟨z, hz, -⟩ := q.product_reflected n v hv x hx
        exact ⟨z, hz⟩
      · exact q.source_valued))
    (0 : ℝ) (fun ε hε => by
      filter_upwards [hone, q.slack_tendsto.eventually (gt_mem_nhds hε)] with n hn hsl v hv ν hν
      have hXv := listComb_valuesAt_mem hν (p := (-1, X)) (by simp)
      have hXWv := listComb_valuesAt_mem hν (p := (1, XW)) (by simp)
      obtain ⟨z, hz, hzx⟩ := q.product_reflected n v hv _ hXv
      rw [listComb_value]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [hXWv.eq hz, hn] at *
      rw [hn, mul_one] at hzx
      have : ((0 : ℚ) : ℝ) + (((1 : ℚ) : ℝ) * z + (((-1 : ℚ) : ℝ) * ν (X n) + 0)) - 0 =
          z - ν (X n) := by push_cast; ring
      rw [this]
      exact hzx.trans hsl.le) hworld
  have h' : (fun n => (XW n).expect P n - (X n).expect P n) ≈ₙ (fun _ => (0 : ℝ)) := by
    refine (tendsto_congr (fun n => ?_)).mp h
    simp [listComb_expect, sub_eq_add_neg]
  exact asympEq_sub_zero_iff.mp h'

/-- **Bounds transfer, per instance (T6).** Given a ramp `WeightQuote` for `X` at threshold
`v − ε` and width `0 < δ < ε`, the soft Total-Trust instance on it (product form), and the
expert's asymptotic lower bound `E*(X_n) ≳ₙ v`, the novice's expectation is asymptotically at
least `v − ε`: `E^H_n(X_n) ≈ₙ E^H_n(XW_n) ≳ₙ (v − ε)·E^H_n(W_n) ≈ₙ v − ε`. The ramp is used
through saturation only (`ramp_eventually_one`); its slope never enters.
Source: [[total-trust-implies-value]] §Lemma 1; PDF slide 19 (root-deference-016; the slide's
`s − ε` read as `v − ε`); vq-wiki-012
Kind: C
Fidelity: exact (width condition `δ < ε` rather than the page's `δ < ε/2`, which is spent only
in the threshold-zero remark)
Hyps: (a) — the TT instance `hTT` and the package `q` are data (for the self-expert on a
literal-indicator source both are FAF's closed `st` package: `Witness.lean`); `hA` is the
expert-side premise; `hworld` (FAF endpoint premise) -/
theorem transfer_instance [IsLogicalInductor P DP] {E : Expert DP} {X W XW : ℕ → LUV}
    {v ε δ : ℚ} (hδ : 0 < δ) (hδε : δ < ε) (hX : LUV.MachineThresholdCodeSeq X)
    (q : WeightQuote DP E X (rampAbove δ (v - ε)) W XW)
    (hTT : (fun n => (XW n).expect P n - ((v - ε : ℚ) : ℝ) * (W n).expect P n) ≳ₙ
      (fun _ => (0 : ℝ)))
    (hA : (fun n => E.estimate X n) ≳ₙ (fun _ => (v : ℝ)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (X n).expect P n) ≳ₙ (fun _ => ((v - ε : ℚ) : ℝ)) := by
  have hone := ramp_eventually_one hδ hδε hA
  have hW := expect_weight_asympEq_one (P := P) q hone hworld
  have hXW := expect_product_asympEq_source (P := P) hX q hone hworld
  have hTT' := (soft_above_iff_unnormalized P (v - ε) W XW).mp hTT
  -- `(v − ε) ≈ₙ (v − ε)·E(W) ≲ₙ E(XW) ≈ₙ E(X)`
  have h1 : (fun _ => ((v - ε : ℚ) : ℝ)) ≈ₙ (fun n => ((v - ε : ℚ) : ℝ) * (W n).expect P n) := by
    have := (hW.const_mul ((v - ε : ℚ) : ℝ)).symm
    simpa using this
  exact (h1.trans_asympLE hTT').trans_asympEq hXW

/-- **Bounds transfer (T6, the headline).** If for every rational `0 < ε ≤ η` (some fixed
`η > 0`) there is a ramp package at threshold `v − ε` (some width `0 < δ < ε`, a `WeightQuote`
and its soft Total-Trust instance), then the expert's lower bound `E*(X_n) ≳ₙ v` lifts to the
novice: `E^H_n(X_n) ≳ₙ v`. Composition: `transfer_instance` at every small `ε`, then the
diagonal `asympGE_of_forall_rat_sub_le`. The bound `η` lets a caller stay inside the
threshold range `[0,1]` (T5, T11 use `v = 1/2`, `η = 1/2`); a caller with packages at every
`ε` passes `η = 1`.
Source: PDF slide 19 (root-deference-016); [[total-trust-implies-value]] §Lemma 1
Kind: C
Fidelity: exact
Hyps: (a) at the instance level (the packages and TT instances are data; for the self-expert
on a provable literal-indicator family every one is an FAF conclusion — `Witness.lean`
`transfer_witness`); `hworld` -/
theorem expert_bound_transfer [IsLogicalInductor P DP] {E : Expert DP} {X : ℕ → LUV}
    {v : ℚ} (hX : LUV.MachineThresholdCodeSeq X) {η : ℚ} (hη : 0 < η)
    (hpack : ∀ ε : ℚ, 0 < ε → ε ≤ η → ∃ δ : ℚ, 0 < δ ∧ δ < ε ∧ ∃ W XW : ℕ → LUV,
      ∃ _q : WeightQuote DP E X (rampAbove δ (v - ε)) W XW,
        (fun n => (XW n).expect P n - ((v - ε : ℚ) : ℝ) * (W n).expect P n) ≳ₙ
          (fun _ => (0 : ℝ)))
    (hA : (fun n => E.estimate X n) ≳ₙ (fun _ => (v : ℝ)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (X n).expect P n) ≳ₙ (fun _ => (v : ℝ)) := by
  refine asympGE_of_forall_rat_sub_le hη (fun ε hε hεη => ?_)
  obtain ⟨δ, hδ, hδε, W, XW, q, hTT⟩ := hpack ε hε hεη
  have := transfer_instance (P := P) hδ hδε hX q hTT hA hworld
  push_cast at this
  exact this

/-- **Existence of above-ramp quotes for a source** — the channel clause of the corpus: for
every rational threshold and positive width, some e.c. pair `(W, XW)` is a `WeightQuote` of `X`
at the above-ramp. `(c)` for a general expert (`li-quote-lane`'s ledger process); for the
self-expert on a literal-indicator source it is FAF's closed `st` package
(`Witness.lean`).
Source: [[value-implies-tower]] §What the theorem costs ("Channel"); mandate T6
Kind: D
Fidelity: exact (an existence clause, disclosed) -/
def RampQuotesAvailable (DP : DeductiveProcess) (E : Expert DP) (X : ℕ → LUV) : Prop :=
  ∀ s δ : ℚ, 0 < δ → ∃ W XW : ℕ → LUV, Nonempty (WeightQuote DP E X (rampAbove δ s) W XW)

/-- **Bounds transfer from the predicate `TotalTrust`** (predicate-level corollary): with soft
Total Trust and above-ramp quotes available for `X`, `E*(X_n) ≳ₙ v ⟹ E^H_n(X_n) ≳ₙ v`.
Source: PDF slide 19; [[total-trust-implies-value]] §Lemma 1
Kind: L
Fidelity: exact
Hyps: (c) `RampQuotesAvailable` for a general expert (existence of the ramp quotes);
`TotalTrust` is the deference hypothesis; `hworld` -/
theorem expert_bound_transfer_of_totalTrust [IsLogicalInductor P DP] {E : Expert DP}
    (hT : TotalTrust P DP E) {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    (hq : RampQuotesAvailable DP E X) {v : ℚ}
    (hA : (fun n => E.estimate X n) ≳ₙ (fun _ => (v : ℝ)))
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => (X n).expect P n) ≳ₙ (fun _ => (v : ℝ)) := by
  refine expert_bound_transfer hX one_pos (fun ε hε _ => ⟨ε / 2, by positivity, by linarith, ?_⟩)
    hA hworld
  obtain ⟨W, XW, ⟨q⟩⟩ := hq (v - ε) (ε / 2) (by positivity)
  exact ⟨W, XW, q, hT.above P DP (v - ε) (ε / 2) (by positivity) X W XW hX q⟩

end

end Cleanroom.Deference.DefLatticeArrows
