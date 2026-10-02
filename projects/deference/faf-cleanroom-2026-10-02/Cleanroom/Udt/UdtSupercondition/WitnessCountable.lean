import Cleanroom.Udt.UdtSupercondition.Landscape
import Cleanroom.Udt.UdtSupercondition.WitnessesB
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Countable witnesses

* T5 `sameOntology_unbounded_witness`: on `ℕ`, the geometric pair `P n = 3 · 4⁻⁽ⁿ⁺¹⁾`,
  `P′ n = 2⁻⁽ⁿ⁺¹⁾` has `P′ ≪ P` with unbounded density ratio `2ⁿ⁺¹/3`, so no same-ontology
  conditioning model exists: the bound in Diaconis–Zabell is needed, and the finite corollary is
  not the only witness (N+, as the mandate requires).
* T20 (a) `jeffrey_not_evidenceCI_witness`: the same pair with `a = id` is a Jeffrey update
  (weights `P′`) with no CI-evidence model — the density bound in `jeffrey_iff_evidenceCI` is
  necessary. **N−** (repair round 1): with the finest partition both `JeffreyOnA` and `EvidenceCI`
  are vacuous, so this is the T5 witness relabelled.
* T20 (a) `pairJeffrey_not_evidenceCI_witness` (N+, repair round 1): on the pair partition
  `a n = n / 2`, `pairP′ = ∑_k 2⁻⁽ᵏ⁺¹⁾ · P(· | {2k, 2k+1})` is a genuine Jeffrey update of
  `geomP` (density constant on each two-point atom, `4/5 : 1/5` matching `P(2k) : P(2k+1) = 4 : 1`),
  its density `(4/15) · 2^{3k+1}` on the even points is unbounded, and no same-ontology model —
  a fortiori no CI-evidence model — exists.

Package: `Cleanroom.Udt.UdtSupercondition` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtSupercondition

open scoped ENNReal
open Set

/-- `1 − 4⁻¹ = 3 · 4⁻¹` in `ℝ≥0∞`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem one_sub_inv_four : (1 : ℝ≥0∞) - 4⁻¹ = 3 * 4⁻¹ := by
  refine ENNReal.sub_eq_of_eq_add (ENNReal.inv_ne_top.2 (by norm_num)) ?_
  calc (1 : ℝ≥0∞) = 4 * 4⁻¹ := (ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofNat_ne_top).symm
    _ = (3 + 1) * 4⁻¹ := by norm_num
    _ = 3 * 4⁻¹ + 4⁻¹ := by rw [add_mul, one_mul]

/-- The geometric prior `P n = 3 · 4⁻⁽ⁿ⁺¹⁾` on `ℕ`.
Source: mandate T5 (countable witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def geomP : PMF ℕ :=
  ⟨fun n => 3 * (4⁻¹ : ℝ≥0∞) ^ (n + 1), by
    rw [ENNReal.summable.hasSum_iff, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one,
      one_sub_inv_four, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl ENNReal.ofNat_ne_top),
      inv_inv]
    calc (3 : ℝ≥0∞) * (4⁻¹ * (3⁻¹ * 4)) = (3 * 3⁻¹) * (4⁻¹ * 4) := by ring
      _ = 1 := by
        rw [ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofNat_ne_top,
          ENNReal.inv_mul_cancel (by norm_num) ENNReal.ofNat_ne_top, one_mul]⟩

/-- The geometric posterior `P′ n = 2⁻⁽ⁿ⁺¹⁾` on `ℕ`.
Source: mandate T5 (countable witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def geomP' : PMF ℕ :=
  ⟨fun n => (2⁻¹ : ℝ≥0∞) ^ (n + 1), by
    rw [ENNReal.summable.hasSum_iff, ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two,
      inv_inv, ENNReal.inv_mul_cancel (by norm_num) ENNReal.ofNat_ne_top]⟩

/-- The mass functions.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem geomP_apply (n : ℕ) : geomP n = 3 * (4⁻¹ : ℝ≥0∞) ^ (n + 1) := rfl

/-- The mass functions.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem geomP'_apply (n : ℕ) : geomP' n = (2⁻¹ : ℝ≥0∞) ^ (n + 1) := rfl

/-- `4⁻¹ ^ k = 2⁻¹ ^ k * 2⁻¹ ^ k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem inv_four_pow (k : ℕ) : (4⁻¹ : ℝ≥0∞) ^ k = (2⁻¹ : ℝ≥0∞) ^ k * (2⁻¹ : ℝ≥0∞) ^ k := by
  rw [← mul_pow, ← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl ENNReal.ofNat_ne_top)]
  norm_num

/-- **The density ratio is unbounded:** for every finite `B`, `BoundedDensity geomP′ geomP B`
fails — at `n` with `3B < 2ⁿ⁺¹`.
Source: mandate T5 (countable witness: "exhibiting `x` with ratio `> B` for each `B`")
Kind: P
Fidelity: n/a
Hyps: (a) all -/
theorem geomP'_not_boundedDensity (B : ℝ≥0∞) (hB : B ≠ ⊤) : ¬ BoundedDensity geomP' geomP B := by
  intro h
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt (show 3 * B ≠ ⊤ from ENNReal.mul_ne_top ENNReal.ofNat_ne_top hB)
  have hq0 : (2⁻¹ : ℝ≥0∞) ^ (k + 1) ≠ 0 := pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
  have hqt : (2⁻¹ : ℝ≥0∞) ^ (k + 1) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (by norm_num))
  have h1 := h k
  rw [geomP'_apply, geomP_apply, inv_four_pow] at h1
  -- q ≤ B * (3 * (q * q))  ⟹  1 ≤ 3 * B * q
  have h2 : (1 : ℝ≥0∞) ≤ 3 * B * (2⁻¹ : ℝ≥0∞) ^ (k + 1) := by
    have h3 : (2⁻¹ : ℝ≥0∞) ^ (k + 1) ≤
        (2⁻¹ : ℝ≥0∞) ^ (k + 1) * (3 * B * (2⁻¹ : ℝ≥0∞) ^ (k + 1)) := by
      calc (2⁻¹ : ℝ≥0∞) ^ (k + 1)
          ≤ B * (3 * ((2⁻¹ : ℝ≥0∞) ^ (k + 1) * (2⁻¹ : ℝ≥0∞) ^ (k + 1))) := h1
        _ = (2⁻¹ : ℝ≥0∞) ^ (k + 1) * (3 * B * (2⁻¹ : ℝ≥0∞) ^ (k + 1)) := by ring
    calc (1 : ℝ≥0∞) = ((2⁻¹ : ℝ≥0∞) ^ (k + 1))⁻¹ * (2⁻¹ : ℝ≥0∞) ^ (k + 1) :=
          (ENNReal.inv_mul_cancel hq0 hqt).symm
      _ ≤ ((2⁻¹ : ℝ≥0∞) ^ (k + 1))⁻¹ *
          ((2⁻¹ : ℝ≥0∞) ^ (k + 1) * (3 * B * (2⁻¹ : ℝ≥0∞) ^ (k + 1))) := mul_le_mul' le_rfl h3
      _ = (((2⁻¹ : ℝ≥0∞) ^ (k + 1))⁻¹ * (2⁻¹ : ℝ≥0∞) ^ (k + 1)) *
          (3 * B * (2⁻¹ : ℝ≥0∞) ^ (k + 1)) := by ring
      _ = 3 * B * (2⁻¹ : ℝ≥0∞) ^ (k + 1) := by rw [ENNReal.inv_mul_cancel hq0 hqt, one_mul]
  -- 1 ≤ 3B · 2⁻⁽ᵏ⁺¹⁾  ⟹  2ᵏ⁺¹ ≤ 3B
  have h4 : ((2 : ℝ≥0∞) ^ (k + 1)) ≤ 3 * B := by
    have h5 : (2⁻¹ : ℝ≥0∞) ^ (k + 1) = ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ := ENNReal.inv_pow.symm
    rw [h5] at h2
    have hp0 : (2 : ℝ≥0∞) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hpt : (2 : ℝ≥0∞) ^ (k + 1) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
    calc (2 : ℝ≥0∞) ^ (k + 1) = (2 : ℝ≥0∞) ^ (k + 1) * 1 := (mul_one _).symm
      _ ≤ (2 : ℝ≥0∞) ^ (k + 1) * (3 * B * ((2 : ℝ≥0∞) ^ (k + 1))⁻¹) := mul_le_mul' le_rfl h2
      _ = 3 * B * ((2 : ℝ≥0∞) ^ (k + 1) * ((2 : ℝ≥0∞) ^ (k + 1))⁻¹) := by ring
      _ = 3 * B := by rw [ENNReal.mul_inv_cancel hp0 hpt, mul_one]
  -- but k < 2^k < 2^(k+1)
  have h6 : (k : ℝ≥0∞) < (2 : ℝ≥0∞) ^ (k + 1) := by
    have : k < 2 ^ (k + 1) := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))
    exact_mod_cast this
  exact absurd (lt_of_lt_of_le (hk.trans h6) h4) (lt_irrefl _)

/-- **Diaconis–Zabell needs the bound (countable N+ witness):** `geomP′ ≪ geomP` (both have full
support), the density ratio is unbounded, and no same-ontology conditioning model exists.
Source: [[superconditioning-mismatched-ontologies]] §2.6 Remark 2.5 | udt-rep-056 (necessity
witness) | mandate T5
Kind: N+
Fidelity: n/a (a countable carrier; the finite corollary is not the only witness)
Hyps: (a) -/
theorem sameOntology_unbounded_witness :
    (∀ n, geomP n = 0 → geomP' n = 0) ∧ (∀ B, B ≠ ⊤ → ¬ BoundedDensity geomP' geomP B) ∧
      ¬ Nonempty (SameOntologyModel geomP geomP') := by
  refine ⟨fun n h => ?_, geomP'_not_boundedDensity, fun hne => ?_⟩
  · exfalso
    rw [geomP_apply] at h
    exact (mul_ne_zero (by norm_num) (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top))) h
  · obtain ⟨B, hB, h⟩ := (sameOntology_condModel_iff geomP geomP').1 hne
    exact geomP'_not_boundedDensity B hB h

/-- **The density bound in T20 (a) is necessary — finest-partition instance (N−):** with `a = id`,
`geomP′` is a Jeffrey update of `geomP` (weights `geomP′` itself), but no same-ontology model — a
fortiori no CI-evidence model — exists. Degenerate: with `a = id`, `JeffreyOnA P id P′` is just
`P′ ≪ P` and `EvidenceCI m id` holds for every same-ontology model, so the second conjunct is
literally `¬ Nonempty (SameOntologyModel geomP geomP′)` (`sameOntology_unbounded_witness`); what
it shows is only that the bound is needed. The N+ witness on a two-point-per-atom partition is
`pairJeffrey_not_evidenceCI_witness`.
Source: mandate T20 (a) | [[superconditioning-mismatched-ontologies]] §6.2 | audit r1
(adversarial B2)
Kind: N-
Fidelity: n/a (degenerate: finest partition)
Hyps: (a) -/
theorem jeffrey_not_evidenceCI_witness :
    JeffreyOnA geomP id geomP' ∧ ¬ ∃ m : SameOntologyModel geomP geomP', EvidenceCI m id := by
  constructor
  · refine (jeffreyOnA_iff_density_const geomP geomP' id).2 ⟨sameOntology_unbounded_witness.1, ?_⟩
    intro x y hxy
    have : x = y := hxy
    subst this
    rfl
  · rintro ⟨m, -⟩
    exact sameOntology_unbounded_witness.2.2 ⟨m⟩

/-! ### T20 (a): a non-degenerate countable witness on the pair partition -/

/-- The pair partition `a n = n / 2` on `ℕ`: atoms `{2k, 2k + 1}`.
Source: audit r1 (adversarial B2) | mandate T20 (a)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pairOf : ℕ → ℕ := fun n => n / 2

/-- The two-point kernel of pair `k`: mass `4/5` on `2k`, `1/5` on `2k + 1` — the conditional of
`geomP` on the pair, since `geomP (2k) : geomP (2k+1) = 4 : 1`.
Source: audit r1 (adversarial B2)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def pairKernel (k : ℕ) : PMF ℕ :=
  PMF.map (fun b => bif b then 2 * k else 2 * k + 1) (pmfBool (4/5) (by norm_num) (by norm_num))

/-- The Jeffrey update of `geomP` on the pair partition with weight `2⁻⁽ᵏ⁺¹⁾` on pair `k`:
`P′(2k) = 2⁻⁽ᵏ⁺¹⁾ · 4/5`, `P′(2k+1) = 2⁻⁽ᵏ⁺¹⁾ · 1/5`.
Source: audit r1 (adversarial B2)
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def pairP' : PMF ℕ := geomP'.bind pairKernel

/-- `pairKernel k (2k) = 4/5`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pairKernel_apply_even (k : ℕ) : pairKernel k (2 * k) = ENNReal.ofReal (4/5) := by
  rw [pairKernel, PMF.map_apply, tsum_eq_single true]
  · simp [pmfBool_true]
  · intro b hb
    cases b
    · simp
    · exact absurd rfl hb

/-- `pairKernel k (2k+1) = 1/5`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pairKernel_apply_odd (k : ℕ) : pairKernel k (2 * k + 1) = ENNReal.ofReal (1/5) := by
  rw [pairKernel, PMF.map_apply, tsum_eq_single false]
  · simp only [Bool.cond_false, if_true, pmfBool_false]
    norm_num
  · intro b hb
    cases b
    · exact absurd rfl hb
    · simp

/-- `pairKernel k` vanishes off the pair `{2k, 2k+1}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pairKernel_apply_of_ne (k n : ℕ) (hn : n / 2 ≠ k) : pairKernel k n = 0 := by
  rw [pairKernel, PMF.map_apply, ENNReal.tsum_eq_zero]
  intro b
  cases b
  · exact if_neg fun e => hn (by simp only [Bool.cond_false] at e; omega)
  · exact if_neg fun e => hn (by simp only [Bool.cond_true] at e; omega)

/-- The mass function of `pairP′`: only the pair of `n` contributes.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pairP'_apply (n : ℕ) : pairP' n = geomP' (n / 2) * pairKernel (n / 2) n := by
  rw [pairP', PMF.bind_apply]
  exact tsum_eq_single (n / 2) fun k hk => by
    rw [pairKernel_apply_of_ne k n (Ne.symm hk), mul_zero]

/-- `pairP′ (2k) = 2⁻⁽ᵏ⁺¹⁾ · 4/5`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pairP'_even (k : ℕ) : pairP' (2 * k) = (2⁻¹ : ℝ≥0∞) ^ (k + 1) * ENNReal.ofReal (4/5) := by
  rw [pairP'_apply, show 2 * k / 2 = k by omega, pairKernel_apply_even, geomP'_apply]

/-- `pairP′ (2k+1) = 2⁻⁽ᵏ⁺¹⁾ · 1/5`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pairP'_odd (k : ℕ) :
    pairP' (2 * k + 1) = (2⁻¹ : ℝ≥0∞) ^ (k + 1) * ENNReal.ofReal (1/5) := by
  rw [pairP'_apply, show (2 * k + 1) / 2 = k by omega, pairKernel_apply_odd, geomP'_apply]

/-- `4⁻¹ = ofReal (1/4)` in `ℝ≥0∞`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem inv_four_eq_ofReal : (4⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1/4) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]

/-- `2⁻¹ = ofReal (1/2)` in `ℝ≥0∞`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem inv_two_eq_ofReal : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1/2) := by
  rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]

/-- The density identity on a pair: `(4/5) · (r · 4⁻¹) = (1/5) · r`, with the common factors.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pair_density_eq (A r : ℝ≥0∞) :
    A * ENNReal.ofReal (4/5) * (3 * (r * 4⁻¹)) = A * ENNReal.ofReal (1/5) * (3 * r) := by
  have key : ENNReal.ofReal (4/5) * (4⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1/5) := by
    rw [inv_four_eq_ofReal]; exact ofReal_mul_eq (by norm_num) (by norm_num)
  calc A * ENNReal.ofReal (4/5) * (3 * (r * 4⁻¹))
      = A * (ENNReal.ofReal (4/5) * 4⁻¹) * (3 * r) := by ring
    _ = A * ENNReal.ofReal (1/5) * (3 * r) := by rw [key]

/-- `geomP` has full support.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem geomP_ne_zero (n : ℕ) : geomP n ≠ 0 := by
  rw [geomP_apply]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top))

/-- **`pairP′` is a Jeffrey update of `geomP` on the pair partition:** `pairP′ ≪ geomP` and the
density is constant on each pair (`jeffreyOnA_iff_density_const`).
Source: audit r1 (adversarial B2) | [[superconditioning-mismatched-ontologies]] §4.6
Kind: P
Fidelity: n/a
Hyps: (a) all -/
theorem pairP'_jeffrey : JeffreyOnA geomP pairOf pairP' := by
  refine (jeffreyOnA_iff_density_const geomP pairP' pairOf).2
    ⟨fun n h => absurd h (geomP_ne_zero n), fun x y hxy => ?_⟩
  have hc : x = y ∨ (x = 2 * (x / 2) ∧ y = 2 * (x / 2) + 1) ∨
      (y = 2 * (x / 2) ∧ x = 2 * (x / 2) + 1) := by
    change x / 2 = y / 2 at hxy
    omega
  rcases hc with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h; rfl
  · generalize x / 2 = k at h1 h2
    subst h1
    subst h2
    rw [pairP'_even, pairP'_odd, geomP_apply, geomP_apply, pow_succ (4⁻¹ : ℝ≥0∞) (2 * k + 1)]
    exact pair_density_eq _ _
  · generalize x / 2 = k at h1 h2
    subst h1
    subst h2
    rw [pairP'_odd, pairP'_even, geomP_apply, geomP_apply, pow_succ (4⁻¹ : ℝ≥0∞) (2 * k + 1)]
    exact (pair_density_eq _ _).symm

/-- **The density of `pairP′` w.r.t. `geomP` is unbounded:** for every finite `B`,
`BoundedDensity pairP′ geomP B` fails at the even point `2k` with `6B < k`.
Source: audit r1 (adversarial B2) | mandate T5 pattern
Kind: P
Fidelity: n/a
Hyps: (a) all -/
theorem pairP'_not_boundedDensity (B : ℝ≥0∞) (hB : B ≠ ⊤) : ¬ BoundedDensity pairP' geomP B := by
  intro h
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt
    (show 6 * B ≠ ⊤ from ENNReal.mul_ne_top ENNReal.ofNat_ne_top hB)
  have hq0 : (2⁻¹ : ℝ≥0∞) ^ (k + 1) ≠ 0 :=
    pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)
  have hqt : (2⁻¹ : ℝ≥0∞) ^ (k + 1) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (by norm_num))
  have h1 := h (2 * k)
  rw [pairP'_even, geomP_apply] at h1
  have h4 : (4⁻¹ : ℝ≥0∞) ^ (2 * k + 1) ≤ (2⁻¹ : ℝ≥0∞) ^ (k + 1) * (2⁻¹ : ℝ≥0∞) ^ (k + 1) := by
    rw [← inv_four_pow]
    exact pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.2 (by norm_num)) (by omega)
  have hhalf : (2⁻¹ : ℝ≥0∞) ≤ ENNReal.ofReal (4/5) := by
    rw [inv_two_eq_ofReal]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have h2 : (2⁻¹ : ℝ≥0∞) ^ (k + 1) * 2⁻¹ ≤
      B * (3 * ((2⁻¹ : ℝ≥0∞) ^ (k + 1) * (2⁻¹ : ℝ≥0∞) ^ (k + 1))) :=
    (mul_le_mul' le_rfl hhalf).trans (h1.trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl h4)))
  have h3 : (2⁻¹ : ℝ≥0∞) ≤ 3 * B * (2⁻¹ : ℝ≥0∞) ^ (k + 1) := by
    calc (2⁻¹ : ℝ≥0∞) = ((2⁻¹ : ℝ≥0∞) ^ (k + 1))⁻¹ * ((2⁻¹ : ℝ≥0∞) ^ (k + 1) * 2⁻¹) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hq0 hqt, one_mul]
      _ ≤ ((2⁻¹ : ℝ≥0∞) ^ (k + 1))⁻¹ *
          (B * (3 * ((2⁻¹ : ℝ≥0∞) ^ (k + 1) * (2⁻¹ : ℝ≥0∞) ^ (k + 1)))) := mul_le_mul' le_rfl h2
      _ = (((2⁻¹ : ℝ≥0∞) ^ (k + 1))⁻¹ * (2⁻¹ : ℝ≥0∞) ^ (k + 1)) *
          (3 * B * (2⁻¹ : ℝ≥0∞) ^ (k + 1)) := by ring
      _ = 3 * B * (2⁻¹ : ℝ≥0∞) ^ (k + 1) := by rw [ENNReal.inv_mul_cancel hq0 hqt, one_mul]
  have h5 : (1 : ℝ≥0∞) ≤ 6 * B * (2⁻¹ : ℝ≥0∞) ^ (k + 1) := by
    calc (1 : ℝ≥0∞) = 2 * 2⁻¹ := (ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofNat_ne_top).symm
      _ ≤ 2 * (3 * B * (2⁻¹ : ℝ≥0∞) ^ (k + 1)) := mul_le_mul' le_rfl h3
      _ = 6 * B * (2⁻¹ : ℝ≥0∞) ^ (k + 1) := by ring
  have h6 : ((2 : ℝ≥0∞) ^ (k + 1)) ≤ 6 * B := by
    have h7 : (2⁻¹ : ℝ≥0∞) ^ (k + 1) = ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ := ENNReal.inv_pow.symm
    rw [h7] at h5
    have hp0 : (2 : ℝ≥0∞) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hpt : (2 : ℝ≥0∞) ^ (k + 1) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
    calc (2 : ℝ≥0∞) ^ (k + 1) = (2 : ℝ≥0∞) ^ (k + 1) * 1 := (mul_one _).symm
      _ ≤ (2 : ℝ≥0∞) ^ (k + 1) * (6 * B * ((2 : ℝ≥0∞) ^ (k + 1))⁻¹) := mul_le_mul' le_rfl h5
      _ = 6 * B * ((2 : ℝ≥0∞) ^ (k + 1) * ((2 : ℝ≥0∞) ^ (k + 1))⁻¹) := by ring
      _ = 6 * B := by rw [ENNReal.mul_inv_cancel hp0 hpt, mul_one]
  have h8 : (k : ℝ≥0∞) < (2 : ℝ≥0∞) ^ (k + 1) := by
    have : k < 2 ^ (k + 1) :=
      lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))
    exact_mod_cast this
  exact absurd (lt_of_lt_of_le (hk.trans h8) h6) (lt_irrefl _)

/-- **The density bound in T20 (a) is necessary (countable N+ witness):** on the pair partition
`pairOf` (two points per atom: `pairOf 0 = pairOf 1`, `pairOf 0 ≠ pairOf 2`), `pairP′` is a
genuine Jeffrey update of `geomP` (weights `2⁻⁽ᵏ⁺¹⁾`, the conditional `4/5 : 1/5` on each pair),
its density w.r.t. `geomP` is unbounded, and no same-ontology model — a fortiori no CI-evidence
model — exists. Unlike `jeffrey_not_evidenceCI_witness` (`a = id`), neither `JeffreyOnA` nor
`EvidenceCI` is vacuous here.
Source: mandate T20 (a) | [[superconditioning-mismatched-ontologies]] §6.2 | audit r1
(adversarial B2)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem pairJeffrey_not_evidenceCI_witness :
    JeffreyOnA geomP pairOf pairP' ∧ pairOf 0 = pairOf 1 ∧ pairOf 0 ≠ pairOf 2 ∧
      (∀ B, B ≠ ⊤ → ¬ BoundedDensity pairP' geomP B) ∧
      ¬ ∃ m : SameOntologyModel geomP pairP', EvidenceCI m pairOf :=
  ⟨pairP'_jeffrey, rfl, by decide, pairP'_not_boundedDensity, fun ⟨m, _⟩ =>
    let ⟨B, hB, h⟩ := (sameOntology_condModel_iff geomP pairP').1 ⟨m⟩
    pairP'_not_boundedDensity B hB h⟩

end Cleanroom.Udt.UdtSupercondition
