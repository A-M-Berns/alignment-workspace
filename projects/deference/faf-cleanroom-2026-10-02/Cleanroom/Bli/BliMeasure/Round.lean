import Cleanroom.Bli.BliMeasure.Grid
import Cleanroom.Bli.BliFinite.Actual

/-!
# `bli-measure` · Round: the abstract coherent base, world rounding of the exposed measure, the
denominator mesh (target 0, target 2's `E1x` mesh)

* `CoherentBase DP` — the abstract base of the mandate: a rational history `Q` together with
  exposed world measures `w n` on `FiniteWorld (B n)` (nonnegative, mass one, supported on
  `DP.D n`-consistent worlds) whose marginals are `Q n` on `smallSet n`, plus the atom bounds
  (`AtomBounds`) and `B_stage` (the stage lies within the day's atom bound, as `pcAtoms` does).
  Over the recursion of record the fields are discharged in `Base.lean` from `bli-coherent-mm`'s
  `pcOverlaySmall_coherent`/`pcAtoms_bound` under `hcons`.
* `measureRound base 𝓜 n` — `remainderRound` of the **exposed** measure (never `worldRound`,
  whose classical choice of a measure would silently replace `w n`; mandate Known issue 9).
* `roundedTable` — its marginal table on `wIndex B`, a `cgrid` member (`roundedTable_mem_cgrid`),
  with the error bound `roundedTable_err` and `measureRound_eq_of_grid` (exactness on a mesh the
  measure already lies on).
* `denomMesh base` — the denominator mesh `d m := ∏_{k ≤ m} ∏_u (w k u).den` (nested by
  construction; noncomputable in the base, disclosed), on which `measureRound = w`.
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction LO.Propositional Finset BoolPCWorld Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliFound

/-! ## The abstract coherent base -/

/-- **The abstract coherent base** of [[bli-measure-mandate]] target 0: a rational history `Q`
with exposed world measures `w n` on `FiniteWorld (B n)`, supported on `DP.D n`-consistent worlds,
whose marginals are `Q n` on `smallSet n`; with the atom bounds and the stage within the bound.
Source: [[bli-measure-mandate]] target 0 (abstract base: `Q`, `w`, `hw`, `hQ`, atom-bound data)
Kind: D
Fidelity: exact (fields `w_nonneg`/`w_sum`/`w_supp` are `IsWorldMeasure (w n) (DP.D n)`,
`Q_eq` is `hQ`; instantiated in `Base.lean`) -/
structure CoherentBase (DP : DeductiveProcess) where
  /-- The atom bounds. -/
  𝔅 : AtomBounds
  /-- The base's rational history. -/
  Q : RatHistory
  /-- The exposed day-`n` world measure. -/
  w : ∀ n, FiniteWorld (𝔅.B n) → ℚ
  /-- Nonnegative. -/
  w_nonneg : ∀ n u, 0 ≤ w n u
  /-- Mass one. -/
  w_sum : ∀ n, ∑ u, w n u = 1
  /-- Supported on the stage's consistent worlds. -/
  w_supp : ∀ n u, w n u ≠ 0 → (worldOf u).ConsistentWith (DP.D n)
  /-- The base prices every day-`n` small sentence by the day-`n` measure. -/
  Q_eq : ∀ n, ∀ φ ∈ smallSet n, Q n φ = wMarginal (w n) φ
  /-- The stage lies within the day's atom bound. -/
  B_stage : ∀ n, ∀ φ ∈ DP.D n, atomBound φ ≤ 𝔅.B n

variable {DP : DeductiveProcess} (base : CoherentBase DP) (𝓜 : Mesh)

/-- The exposed measure is a `WMeasure` relative to the stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma CoherentBase.wMeasure (n : ℕ) : WMeasure (base.w n) (DP.D n) :=
  ⟨base.w_nonneg n, base.w_sum n, base.w_supp n⟩

/-- The base's prices are in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma CoherentBase.Q_range (n : ℕ) {φ : Sentence} (hφ : φ ∈ smallSet n) :
    0 ≤ base.Q n φ ∧ base.Q n φ ≤ 1 := by
  rw [base.Q_eq n φ hφ]
  exact ⟨wMarginal_nonneg (base.w_nonneg n) φ, wMarginal_le_one (base.w_nonneg n) (base.w_sum n) φ⟩

/-- **The base respects its stage on priced sentences**: a day-`n` small sentence in the stage is
priced `1` (bli-soto-a-039's "respects `D̄`" for the base of record, through `w_supp`; the
mandate's target 5 clause that was cited, now stated).
Source: bli-soto-a-039; [[bli-measure-mandate]] target 5
Kind: L
Fidelity: exact -/
lemma CoherentBase.Q_eq_one_of_mem (n : ℕ) {φ : Sentence} (hφ : φ ∈ smallSet n) (hD : φ ∈ DP.D n) :
    base.Q n φ = 1 := by
  rw [base.Q_eq n φ hφ]
  exact (base.wMeasure n).wMarginal_of_mem hD

/-! ## World rounding of the exposed measure -/

/-- **World rounding of the exposed measure**: `remainderRound` of `w n` to `(1/𝓜.d n)·ℕ`.
Source: [[bli-measure-mandate]] target 0 (`measureRound`); bli-paper-033 (world-measure rounding)
Kind: D
Fidelity: exact (on the exposed measure, not `worldRound`) -/
noncomputable def measureRound (n : ℕ) : FiniteWorld (base.𝔅.B n) → ℚ :=
  remainderRound (𝓜.d_pos n) (base.w n) (base.w_nonneg n) (base.w_sum n)

/-- The rounded measure is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma measureRound_nonneg (n : ℕ) (u : FiniteWorld (base.𝔅.B n)) : 0 ≤ measureRound base 𝓜 n u :=
  remainderRound_nonneg _ _ _ _ u

/-- The rounded measure has mass one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma measureRound_sum (n : ℕ) : ∑ u, measureRound base 𝓜 n u = 1 :=
  remainderRound_sum_one _ _ _ _

/-- The rounded measure lies on the mesh.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma measureRound_grid (n : ℕ) (u : FiniteWorld (base.𝔅.B n)) :
    ∃ k : ℕ, measureRound base 𝓜 n u = (k : ℚ) / 𝓜.d n :=
  remainderRound_mem _ _ _ _ u

/-- A world charged by the rounded measure is charged by the exposed measure.
Source: none: infrastructure (`remainderRound_support_subset`)
Kind: L
Fidelity: n/a -/
lemma w_ne_zero_of_measureRound_ne_zero (n : ℕ) {u : FiniteWorld (base.𝔅.B n)}
    (h : measureRound base 𝓜 n u ≠ 0) : base.w n u ≠ 0 :=
  fun h0 => h (remainderRound_support_subset _ _ _ _ u h0)

/-- The rounded measure is a `WMeasure` relative to the stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma measureRound_wMeasure (n : ℕ) : WMeasure (measureRound base 𝓜 n) (DP.D n) :=
  ⟨measureRound_nonneg base 𝓜 n, measureRound_sum base 𝓜 n,
    fun u hu => base.w_supp n u (w_ne_zero_of_measureRound_ne_zero base 𝓜 n hu)⟩

/-- **The rounded table**: the marginal table of the rounded measure on the world-vector index.
Source: [[bli-measure-mandate]] target 0 (`roundedTable`)
Kind: D
Fidelity: exact -/
noncomputable def roundedTable (n : ℕ) : Table (wIndex base.𝔅.B) n :=
  fun φ => wMarginal (measureRound base 𝓜 n) φ.1

/-- The rounded table is a grid table.
Source: [[bli-measure-mandate]] target 0 ("a `cgrid n` member")
Kind: L
Fidelity: exact -/
theorem roundedTable_mem_cgrid (n : ℕ) : roundedTable base 𝓜 n ∈ cgrid base.𝔅 𝓜 n :=
  mem_cgrid_of_vec base.𝔅 𝓜 _ (measureRound_nonneg base 𝓜 n) (measureRound_sum base 𝓜 n)
    (measureRound_grid base 𝓜 n)

/-- The vector of the rounded table is the rounded measure.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma vecOf_roundedTable (n : ℕ) : vecOf (roundedTable base 𝓜 n) = measureRound base 𝓜 n := by
  funext u
  exact wMarginal_worldConj _ u

/-- **The rounding error on sentence marginals**: `|roundedTable n φ − Q n φ| ≤ 2^(B n) / d n` for
every sentence (in particular on `smallSet n`, where the exposed marginal is `Q n φ`).
Source: [[bli-measure-mandate]] target 0 (`roundedTable_err`); `bli-finite` `remainderRound_l1_le`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem measureRound_err (n : ℕ) (φ : Sentence) :
    |wMarginal (measureRound base 𝓜 n) φ - wMarginal (base.w n) φ| ≤
      (2 : ℚ) ^ base.𝔅.B n / 𝓜.d n := by
  unfold wMarginal
  rw [← Finset.sum_sub_distrib]
  calc |∑ u, (measureRound base 𝓜 n u * u.payoutRat φ - base.w n u * u.payoutRat φ)|
      ≤ ∑ u, |measureRound base 𝓜 n u * u.payoutRat φ - base.w n u * u.payoutRat φ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u, |measureRound base 𝓜 n u - base.w n u| := by
        apply Finset.sum_le_sum
        intro u _
        rw [← sub_mul, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _)
          (by rw [abs_of_nonneg (payoutRat_nonneg u φ)]; exact payoutRat_le_one u φ)
    _ ≤ (Fintype.card (FiniteWorld (base.𝔅.B n)) : ℚ) / 𝓜.d n :=
        remainderRound_l1_le _ _ _ _
    _ = (2 : ℚ) ^ base.𝔅.B n / 𝓜.d n := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        push_cast; rfl

/-- The rounding error on small sentences, against the base's price.
Source: [[bli-measure-mandate]] target 2 (`E1r` with the error)
Kind: L
Fidelity: exact -/
theorem roundedTable_err (n : ℕ) {φ : Sentence} (hφ : φ ∈ smallSet n) :
    |wMarginal (measureRound base 𝓜 n) φ - base.Q n φ| ≤ (2 : ℚ) ^ base.𝔅.B n / 𝓜.d n := by
  rw [base.Q_eq n φ hφ]
  exact measureRound_err base 𝓜 n φ

/-- Two points of `(1/d)·ℕ` strictly within `1/d` of each other coincide.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma grid_eq_of_abs_sub_lt {d : ℕ} (hd : 0 < d) {k k' : ℕ}
    (h : |((k : ℚ) / d) - ((k' : ℚ) / d)| < 1 / d) : k = k' := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  rw [← sub_div, abs_div, abs_of_pos hdq, div_lt_div_iff_of_pos_right hdq] at h
  have : |((k : ℤ) : ℚ) - ((k' : ℤ) : ℚ)| < 1 := by push_cast; exact h
  rw [← Int.cast_sub, ← Int.cast_abs] at this
  have h1 : |(k : ℤ) - k'| < 1 := by exact_mod_cast this
  have h2 : |(k : ℤ) - k'| = 0 := by
    have := abs_nonneg ((k : ℤ) - k')
    omega
  rw [abs_eq_zero, sub_eq_zero] at h2
  exact_mod_cast h2

/-- **Exactness on the mesh**: if the exposed measure already lies on `(1/d n)·ℕ`, rounding
changes nothing (two grid points strictly within `1/d` coincide).
Source: [[bli-measure-mandate]] target 0 (`measureRound_eq_of_grid`)
Kind: P
Fidelity: exact
Hyps: (a) `hgrid` -/
theorem measureRound_eq_of_grid (n : ℕ)
    (hgrid : ∀ u, ∃ k : ℕ, base.w n u = (k : ℚ) / 𝓜.d n) :
    measureRound base 𝓜 n = base.w n := by
  funext u
  obtain ⟨k, hk⟩ := measureRound_grid base 𝓜 n u
  obtain ⟨k', hk'⟩ := hgrid u
  have hlt := remainderRound_abs_sub_lt (𝓜.d_pos n) (base.w n) (base.w_nonneg n) (base.w_sum n) u
  change |measureRound base 𝓜 n u - base.w n u| < 1 / 𝓜.d n at hlt
  rw [hk, hk'] at hlt
  rw [hk, hk', grid_eq_of_abs_sub_lt (𝓜.d_pos n) hlt]

/-! ## The denominator mesh -/

/-- A nonnegative rational whose denominator divides `d > 0` is `k / d` for a natural `k`.
Source: none: infrastructure (`bli-trajectory` `mem_gridVals_of_den_dvd`, without the `≤ 1` clause)
Kind: L
Fidelity: n/a -/
lemma exists_nat_div_of_den_dvd {q : ℚ} (h0 : 0 ≤ q) {d : ℕ} (hd : 0 < d) (hdvd : q.den ∣ d) :
    ∃ k : ℕ, q = (k : ℚ) / d := by
  obtain ⟨c, hc⟩ := hdvd
  have hden : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hq : (q.num : ℚ) / q.den = q := Rat.num_div_den q
  have hnum0 : 0 ≤ q.num := Rat.num_nonneg.mpr h0
  refine ⟨q.num.toNat * c, ?_⟩
  have htn : ((q.num.toNat : ℕ) : ℚ) = (q.num : ℚ) := by
    have := Int.toNat_of_nonneg hnum0
    exact_mod_cast this
  have hdq : (d : ℚ) = (q.den : ℚ) * c := by rw [hc]; push_cast; ring
  have hc0 : (c : ℚ) ≠ 0 := by
    intro h
    have : c = 0 := by exact_mod_cast h
    rw [this, mul_zero] at hc
    exact hd.ne' hc
  push_cast
  rw [htn, hdq, mul_div_mul_right _ _ hc0, hq]

/-- **The denominator mesh of a base**: `d m := ∏_{k ≤ m} ∏_u (w k u).den`, nested by
construction. Noncomputable in the base (the denominators of `w`), disclosed.
Source: [[bli-measure-mandate]] target 2 (`pcDenominatorMesh`); `bli-trajectory` `denominatorMesh`
Kind: D
Fidelity: exact -/
noncomputable def denomMesh : Mesh where
  d n := ∏ k ∈ Finset.range (n + 1), ∏ u : FiniteWorld (base.𝔅.B k), (base.w k u).den
  d_pos _ := Finset.prod_pos fun k _ => Finset.prod_pos fun u _ => (base.w k u).den_pos
  d_dvd n := Dvd.intro _
    (Finset.prod_range_succ (fun k => ∏ u : FiniteWorld (base.𝔅.B k), (base.w k u).den) (n + 1)).symm

/-- The denominator of a day-`n` weight divides the day-`n` denominator.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma den_dvd_denomMesh (n : ℕ) (u : FiniteWorld (base.𝔅.B n)) :
    (base.w n u).den ∣ (denomMesh base).d n := by
  show (base.w n u).den ∣ ∏ k ∈ Finset.range (n + 1), ∏ v : FiniteWorld (base.𝔅.B k), (base.w k v).den
  exact (Finset.dvd_prod_of_mem (fun v => (base.w n v).den) (Finset.mem_univ u)).trans
    (Finset.dvd_prod_of_mem (fun k => ∏ v : FiniteWorld (base.𝔅.B k), (base.w k v).den)
      (Finset.mem_range.mpr (Nat.lt_succ_self n)))

/-- The exposed measure lies on its denominator mesh.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma w_grid_denomMesh (n : ℕ) (u : FiniteWorld (base.𝔅.B n)) :
    ∃ k : ℕ, base.w n u = (k : ℚ) / (denomMesh base).d n :=
  exists_nat_div_of_den_dvd (base.w_nonneg n u) ((denomMesh base).d_pos n) (den_dvd_denomMesh base n u)

/-- **On the denominator mesh, rounding is the identity.**
Source: [[bli-measure-mandate]] target 2 (`E1x` on the denominator mesh)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem measureRound_denomMesh (n : ℕ) : measureRound base (denomMesh base) n = base.w n :=
  measureRound_eq_of_grid base (denomMesh base) n (w_grid_denomMesh base n)

end Cleanroom.Bli.BliMeasure
