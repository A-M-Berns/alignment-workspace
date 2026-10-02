import Cleanroom.Deference.DefArgmaxValue.Calc
import Cleanroom.Deference.DefArgmaxValue.CondStable
import Cleanroom.Deference.DefLatticeArrows.ArgmaxValue

/-!
# `def-argmax-value` · Endorse: Lemma 2 — mass-weighted self-endorsement (target 6)

[[total-trust-implies-value]] §Lemma 2, for an **inductor-expert** (`E.A` a logical inductor
over `DP`, deferral strictly increasing), on a valued menu with a selection package and an
e.c. follower `S`:

* **Step 1** (`endorse_step1`, no hypothesis beyond the package): `E*(S_n) ≈ₙ Σ_j E*(Q^j_n)` —
  `S_n` and `Σ_j Q^j_n` are valued equal (within the package's slack) in every world, because
  exactly one indicator is `1` and `S` takes the selected option's value; deferred-day
  `thm:expprovind` on the unit-coefficient combination `S − Σ_j Q^j` closes it. **Finding
  (2-027):** this is *not* `thm:loe` with decided-indicator coefficients — the products are
  ordinary LUVs and the coefficients are `±1`; FAF's `lic_linearity_of_expectation_seq` (two
  terms, `EF` coefficients) is not what is used.
* **Step 2** (`endorse_step2`): `+ CondStableOn ⟹ E*(S_n) ≳ₙ Σ_j E*(I^j_n)·m^j_n`.
* **The masses are exhaustive** (`sum_estimate_I`): `Σ_j E*(I^j_n) ≈ₙ 1` (provind on the
  indicators' exclusivity, which the reflection clause forces).
* **The real-number lemma under Step 3** (`massWeighted_asympGE_max`): nonnegative masses
  summing to `≈ₙ 1`, quotes in `[0,1]` with maximum `Mx`, and concentration
  (`mass_j · 1[m_j ≤ Mx − ε] → 0` for every `ε > 0`) give `Σ_j mass_j m_j ≳ₙ Mx`.
* **Step 3 assembled** (`endorse_of_concentrates`): Step 2 + exhaustivity + concentration give
  `E*(S_n) ≳ₙ M_n` — the `SelfEndorsesGE` *instance* on `M`, never the predicate (refuted,
  `Refuted.lean`).

The concentration hypothesis `Concentrates` is defined here and discharged in
`Concentration.lean` (from the fold, (a) for the self-expert). Not construction-facing.
-/

namespace Cleanroom.Deference.DefArgmaxValue

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefLatticeArrows
open Cleanroom.Deference.DefSelfTrust Cleanroom.Deference.DefSqueezeDiamond

noncomputable section

variable {DP : DeductiveProcess}

/-! ## The concentration predicate -/

/-- **Introspective concentration** on a menu: for every gap `ε > 0` and index `j`, the mass the
expert puts on selecting `j` vanishes along the days on which `j` is quoted `ε` below the
maximum — `E*(I^j_n) · 1[m^j_n ≤ M_n − ε] → 0`. The sharp form; the ramp form
`E*(I^j_n) · Ind_δ(M_n − m^j_n > ε) → 0` follows (`Concentration.lean`).
Source: [[total-trust-implies-value]] §Lemma 2 Step 3 ("`P^A_n(sel_n = j) → 0` whenever
`m^j_n ≤ M_n − ε`"); vq-wiki-016 (open-problems item 1); mandate target 7
Kind: D
Fidelity: exact (the page's statement, with the mass as `E*(I^j)`) -/
def Concentrates {k : ℕ} (E : Expert DP) (M : Menu k) (I : Fin (k + 1) → ℕ → LUV) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ j, Tendsto (fun n => E.estimate (I j) n *
    (if M.quote E j n ≤ M.maxQuote E n - ε then 1 else 0)) atTop (𝓝 0)

/-! ## Steps 1–2 -/

section Steps

variable {E : Expert DP} [IsLogicalInductor E.A DP]

/-- **Lemma 2, Step 1 (decomposition)**: `E*(S_n) ≈ₙ Σ_j E*(Q^j_n)` for every follower of the
argmax on a valued menu with a selection package — a world-value identity within the slack,
carried by deferred-day `thm:expprovind` on the unit-coefficient combination `S − Σ_j Q^j`
(**not** `thm:loe` with indicator coefficients: finding 2-027).
Source: [[total-trust-implies-value]] §Lemma 2 Step 1; lean-deference-068; 2-027
Kind: C
Fidelity: exact (asymptotic; the package's products within their slack)
Hyps: (a); `hf`; the package as data -/
theorem endorse_step1 (hf : StrictlyIncreasingDeferral E.f) {k : ℕ} {M : Menu k}
    (hM : M.Valued DP) {I Q : Fin (k + 1) → ℕ → LUV} (pkg : SelectionPackage DP E M I Q)
    {S : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S) (hfol : Follows DP E M S)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => E.estimate S n) ≈ₙ (fun n => ∑ j, E.estimate (Q j) n) := by
  set terms : List ((ℕ → EF) × (ℕ → LUV)) :=
    ((fun _ => EF.const 1), S) :: List.ofFn (fun j : Fin (k + 1) => ((fun _ => EF.const (-1)), Q j))
    with hterms
  have hmem : ∀ p ∈ terms, p = ((fun _ => EF.const 1), S) ∨
      ∃ j, p = ((fun _ => EF.const (-1)), Q j) := fun p hp => by
    simp only [hterms, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact Or.inl rfl
    · obtain ⟨j, hj⟩ := List.mem_ofFn.1 hp
      exact Or.inr ⟨j, hj.symm⟩
  have hSv : Valued DP S := follows_valued hM hfol
  have h := expect_deferred_asympEq_zero_of_slack (P := E.A) (DP := DP) E.f hf
    (c₀ := fun _ => EF.const 0) (constWeighting 0) (terms := terms)
    (fun p hp => by
      rcases hmem p hp with rfl | ⟨j, rfl⟩
      · exact constWeighting 1
      · exact constWeighting (-1))
    (fun p hp => by
      rcases hmem p hp with rfl | ⟨j, rfl⟩
      · exact hS
      · exact pkg.codes_Q j)
    (fun p hp => by
      rcases hmem p hp with rfl | ⟨j, rfl⟩
      · exact hSv
      · exact pkg.valued_Q hM j)
    (B := (k : ℝ) + 2) (by positivity)
    (fun m => by
      simp only [hterms, List.map_cons, List.map_ofFn, Function.comp_def, EF.denote_const,
        List.sum_cons, List.sum_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      push_cast
      simp [abs_of_nonneg]
      try linarith)
    (fun n => ((k : ℝ) + 1) * pkg.slack n)
    (by simpa using pkg.slack_tendsto.const_mul ((k : ℝ) + 1))
    (fun n v hv ν hν => by
      choose x hx using fun j => hM j n v hv
      choose z hz hzb using fun j => pkg.reflected_Q j n v hv (x j) (hx j)
      have hνS : ν (S n) = x (M.argmax E n) :=
        (hν _ (List.mem_cons_self ..)).eq (hfol n v hv _ (hx _))
      have hνQ : ∀ j, ν (Q j n) = z j := fun j =>
        (hν _ (List.mem_cons_of_mem _ (List.mem_ofFn.2 ⟨j, rfl⟩))).eq (hz j)
      simp only [hterms, List.map_cons, List.map_ofFn, Function.comp_def, EF.denote_const,
        List.sum_cons, List.sum_ofFn, hνS, hνQ]
      push_cast
      have hsel : ∑ j, x j * (if M.argmax E n = j then (1 : ℝ) else 0) = x (M.argmax E n) := by
        simp [mul_ite, Finset.sum_ite_eq]
      have e : (0 : ℝ) + (1 * x (M.argmax E n) + ∑ j, -1 * z j) =
          ∑ j, (x j * (if M.argmax E n = j then (1 : ℝ) else 0) - z j) := by
        rw [Finset.sum_sub_distrib, hsel]
        simp only [neg_one_mul, Finset.sum_neg_distrib]
        ring
      rw [e]
      calc |∑ j, (x j * (if M.argmax E n = j then (1 : ℝ) else 0) - z j)|
          ≤ ∑ j, |x j * (if M.argmax E n = j then (1 : ℝ) else 0) - z j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin (k + 1), pkg.slack n := Finset.sum_le_sum (fun j _ => by
            rw [abs_sub_comm]; exact hzb j)
        _ = ((k : ℝ) + 1) * pkg.slack n := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]) hworld
  have hE : deferredExpect E.A E.f (fun _ => EF.const 0) terms =
      fun n => E.estimate S n - ∑ j, E.estimate (Q j) n := by
    funext n
    simp only [deferredExpect, hterms, List.map_cons, List.map_ofFn, Function.comp_def,
      EF.denote_const, List.sum_cons, List.sum_ofFn, Expert.estimate]
    push_cast
    simp [Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [hE] at h
  unfold AsympEq at h ⊢
  simpa using h

/-- **Lemma 2, Step 2**: with conditional-stability, `E*(S_n) ≳ₙ Σ_j E*(I^j_n) · m^j_n`.
Source: [[total-trust-implies-value]] §Lemma 2 Step 2
Kind: L
Fidelity: exact
Hyps: (a); `hf`; `h3 : CondStableOn M pkg` (the scope condition) -/
theorem endorse_step2 (hf : StrictlyIncreasingDeferral E.f) {k : ℕ} {M : Menu k}
    (hM : M.Valued DP) {I Q : Fin (k + 1) → ℕ → LUV} (pkg : SelectionPackage DP E M I Q)
    (h3 : CondStableOn M pkg) {S : ℕ → LUV} (hS : LUV.MachineThresholdCodeSeq S)
    (hfol : Follows DP E M S) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => E.estimate S n) ≳ₙ (fun n => ∑ j, E.estimate (I j) n * M.quote E j n) := by
  have h1 := endorse_step1 hf hM pkg hS hfol hworld
  exact asympGE_iff.2 ((asympGE_iff.1 h3).trans_asympEq h1.symm)

/-- **The masses are exhaustive**: `Σ_j E*(I^j_n) ≈ₙ 1` (deferred provind on `Σ_j I^j − 1`, valued
`0` in every world since exactly one indicator is `1`).
Source: mandate target 6 trap list ("`Σ_j E*(I j) = 1` … it is `≈ₙ`, by provind on the atoms'
exclusivity")
Kind: C
Fidelity: exact
Hyps: (a); `hf` -/
theorem sum_estimate_I (hf : StrictlyIncreasingDeferral E.f) {k : ℕ} {M : Menu k}
    {I Q : Fin (k + 1) → ℕ → LUV} (pkg : SelectionPackage DP E M I Q)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => ∑ j, E.estimate (I j) n) ≈ₙ (fun _ => (1 : ℝ)) := by
  set terms : List ((ℕ → EF) × (ℕ → LUV)) :=
    List.ofFn (fun j : Fin (k + 1) => ((fun _ => EF.const 1), I j)) with hterms
  have hmem : ∀ p ∈ terms, ∃ j, p = ((fun _ => EF.const 1), I j) := fun p hp => by
    obtain ⟨j, hj⟩ := List.mem_ofFn.1 hp
    exact ⟨j, hj.symm⟩
  have h := expect_deferred_asympEq_zero_of_slack (P := E.A) (DP := DP) E.f hf
    (c₀ := fun _ => EF.const (-1)) (constWeighting (-1)) (terms := terms)
    (fun p hp => by obtain ⟨j, rfl⟩ := hmem p hp; exact constWeighting 1)
    (fun p hp => by obtain ⟨j, rfl⟩ := hmem p hp; exact pkg.codes_I j)
    (fun p hp => by obtain ⟨j, rfl⟩ := hmem p hp; exact pkg.valued_I j)
    (B := (k : ℝ) + 2) (by positivity)
    (fun m => by
      simp only [hterms, List.map_ofFn, Function.comp_def, EF.denote_const, List.sum_ofFn,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      push_cast
      simp [abs_of_nonneg]
      try linarith)
    (fun _ => 0) tendsto_const_nhds
    (fun n v hv ν hν => by
      have hνI : ∀ j, ν (I j n) = (if M.argmax E n = j then 1 else 0) := fun j =>
        (hν _ (List.mem_ofFn.2 ⟨j, rfl⟩)).eq (pkg.reflected_I j n v hv)
      simp only [hterms, List.map_ofFn, Function.comp_def, EF.denote_const, List.sum_ofFn, hνI]
      push_cast
      simp [Finset.sum_ite_eq]) hworld
  have hE : deferredExpect E.A E.f (fun _ => EF.const (-1)) terms =
      fun n => (∑ j, E.estimate (I j) n) - 1 := by
    funext n
    simp only [deferredExpect, hterms, List.map_ofFn, Function.comp_def, EF.denote_const,
      List.sum_ofFn, Expert.estimate]
    push_cast
    ring
  rw [hE] at h
  unfold AsympEq at h ⊢
  simpa using h

end Steps

/-! ## The real-number lemma under Step 3 -/

/-- **Mass-weighted average versus the maximum** (the page's split at `ε`, with `ε` outside):
nonnegative masses with `Σ_j mass_j ≈ₙ 1`, quotes in `[0,1]` dominated by `Mx ≤ 1`, and
`mass_j · 1[m_j ≤ Mx − ε] → 0` for every `ε > 0` and `j`, give `Σ_j mass_j · m_j ≳ₙ Mx`.
Pointwise, `mass_j m_j ≥ (Mx − ε) mass_j − (Mx − ε) mass_j 1[m_j ≤ Mx − ε]`; summing and
letting the two error terms vanish gives `≥ Mx − 3ε` eventually.
Source: [[total-trust-implies-value]] §Lemma 2 Step 3 ("split the sum at `ε`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem massWeighted_asympGE_max {k : ℕ} (mass m : ℕ → Fin (k + 1) → ℝ) (Mx : ℕ → ℝ)
    (hmass0 : ∀ n j, 0 ≤ mass n j) (hmass1 : (fun n => ∑ j, mass n j) ≈ₙ (fun _ => (1 : ℝ)))
    (hm0 : ∀ n j, 0 ≤ m n j) (hMx : ∀ n j, m n j ≤ Mx n) (hMx1 : ∀ n, Mx n ≤ 1)
    (hconc : ∀ ε : ℝ, 0 < ε → ∀ j, Tendsto (fun n => mass n j *
      (if m n j ≤ Mx n - ε then 1 else 0)) atTop (𝓝 0)) :
    (fun n => ∑ j, mass n j * m n j) ≳ₙ Mx := by
  intro η hη
  set ε : ℝ := min (η / 3) (1 / 2) with hε
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by linarith) (by norm_num)
  have hε3 : 3 * ε ≤ η := by
    have : ε ≤ η / 3 := min_le_left _ _
    linarith
  have hε1 : ε ≤ 1 / 2 := min_le_right _ _
  have h1 : ∀ᶠ n in atTop, |(∑ j, mass n j) - 1| < ε := by
    have := hmass1
    unfold AsympEq at this
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 this ε hεpos
    exact Filter.eventually_atTop.2 ⟨N, fun n hn => by
      have := hN n hn; rwa [Real.dist_eq, sub_zero] at this⟩
  have h2 : ∀ᶠ n in atTop, ∀ j, mass n j * (if m n j ≤ Mx n - ε then 1 else 0) < ε / (k + 1) := by
    rw [Filter.eventually_all]
    intro j
    exact (tendsto_order.1 (hconc ε hεpos j)).2 _ (div_pos hεpos (by positivity))
  filter_upwards [h1, h2] with n hn1 hn2
  -- pointwise bound
  have hpt : ∀ j, (Mx n - ε) * mass n j -
      (Mx n - ε) * (mass n j * (if m n j ≤ Mx n - ε then 1 else 0)) ≤ mass n j * m n j := by
    intro j
    by_cases hc : m n j ≤ Mx n - ε
    · rw [if_pos hc]
      have := mul_nonneg (hmass0 n j) (hm0 n j)
      linarith
    · rw [if_neg hc]
      push Not at hc
      have := mul_le_mul_of_nonneg_left hc.le (hmass0 n j)
      linarith
  have hsum : ∑ j, ((Mx n - ε) * mass n j -
      (Mx n - ε) * (mass n j * (if m n j ≤ Mx n - ε then 1 else 0))) ≤
      ∑ j, mass n j * m n j := Finset.sum_le_sum (fun j _ => hpt j)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have habs : |Mx n - ε| ≤ 1 := by
    rw [abs_le]
    have := hMx n 0
    have := hm0 n 0
    constructor <;> linarith [hMx1 n]
  have hA : (Mx n - ε) - ε ≤ (Mx n - ε) * ∑ j, mass n j := by
    have : (Mx n - ε) * ∑ j, mass n j - (Mx n - ε) = (Mx n - ε) * ((∑ j, mass n j) - 1) := by
      ring
    have hb : |(Mx n - ε) * ((∑ j, mass n j) - 1)| ≤ ε := by
      rw [abs_mul]
      calc |Mx n - ε| * |(∑ j, mass n j) - 1| ≤ 1 * ε :=
            mul_le_mul habs hn1.le (abs_nonneg _) zero_le_one
        _ = ε := one_mul ε
    have := (abs_le.1 hb).1
    linarith
  have hB : (Mx n - ε) * ∑ j, mass n j * (if m n j ≤ Mx n - ε then 1 else 0) ≤ ε := by
    have hs : ∑ j, mass n j * (if m n j ≤ Mx n - ε then 1 else 0) ≤ ε := by
      calc ∑ j, mass n j * (if m n j ≤ Mx n - ε then 1 else 0)
          ≤ ∑ _j : Fin (k + 1), ε / (k + 1) := Finset.sum_le_sum (fun j _ => (hn2 j).le)
        _ = ε := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            field_simp
    have hs0 : 0 ≤ ∑ j, mass n j * (if m n j ≤ Mx n - ε then 1 else 0) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hmass0 n j) (by split_ifs <;> norm_num))
    calc (Mx n - ε) * ∑ j, mass n j * (if m n j ≤ Mx n - ε then 1 else 0)
        ≤ |Mx n - ε| * ∑ j, mass n j * (if m n j ≤ Mx n - ε then 1 else 0) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hs0
      _ ≤ 1 * ε := mul_le_mul habs hs hs0 zero_le_one
      _ = ε := one_mul ε
  linarith

/-! ## Step 3 assembled -/

/-- **Lemma 2 (Steps 1–3): the one-sided self-endorsement instance on a conditionally-stable
menu** — `E*(S_n) ≳ₙ M_n` for an inductor-expert, from the selection package, conditional-stability
(H3) and concentration (the fold's consequence, `Concentration.lean`). The *instance* on `M`,
never the predicate `SelfEndorsesGE` (false, `Refuted.lean`).
Source: [[total-trust-implies-value]] §Lemma 2; lean-deference-068; vq-wiki-013
Kind: C
Fidelity: exact (one-sided, as the page)
Hyps: (a); `hf`; `h3 : CondStableOn M pkg` (H3); `hconc : Concentrates E M I` (derived from the
fold in `Concentration.lean`, (a) for the self-expert, from a `(c)` fold clause in general) -/
theorem endorse_of_concentrates {E : Expert DP} [IsLogicalInductor E.A DP]
    (hf : StrictlyIncreasingDeferral E.f) {k : ℕ} {M : Menu k} (hM : M.Valued DP)
    {I Q : Fin (k + 1) → ℕ → LUV} (pkg : SelectionPackage DP E M I Q)
    (h3 : CondStableOn M pkg) (hconc : Concentrates E M I) {S : ℕ → LUV}
    (hS : LUV.MachineThresholdCodeSeq S) (hfol : Follows DP E M S)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (fun n => E.estimate S n) ≳ₙ (fun n => M.maxQuote E n) := by
  have h2 := endorse_step2 hf hM pkg h3 hS hfol hworld
  have hreal := massWeighted_asympGE_max (fun n j => E.estimate (I j) n) (fun n j => M.quote E j n)
    (fun n => M.maxQuote E n) (fun n j => (E.estimate_mem_Icc _ _).1) (sum_estimate_I hf pkg hworld)
    (fun n j => (E.estimate_mem_Icc _ _).1) (fun n j => M.quote_le_maxQuote E j n)
    (fun n => by
      unfold Menu.maxQuote
      exact Finset.sup'_le _ _ (fun j _ => (E.estimate_mem_Icc _ _).2))
    hconc
  exact asympGE_iff.2 ((asympGE_iff.1 hreal).trans (asympGE_iff.1 h2))

end

end Cleanroom.Deference.DefArgmaxValue
