import Cleanroom.Found.LiAsympCalc.Luv
import LogicalInduction.Framework.Compactness

/-!
# `def-tracking-pin` · Defs: settlement facts, the mesh error, and the T7 plumbing

The package's vocabulary is `li-asymp-calc`'s `LUV.DeterminedVia X DP y` ("every world
consistent with every stage of `DP` values `X` at `y`") — the FAF rendering of the corpus's
"the contract settles to `v_n`". It is **time-free**: the corpus's settlement stage `σ(n)` never
appears, because `DeterminedVia` quantifies over completed-theory worlds and "decided by stage
`σ(n)`" implies it (`li-quote-lane`'s `ledgerLuv_decided_by` is the stage form). This file holds
what every headline of the package reads off a settled LUV:

* `determinedVia_mem_Icc`: a settled value lies in `[0,1]` once some world is consistent with every
  stage (FAF's compactness `DeductiveProcess.exists_consistentWithTheory` turns the per-stage
  `hworld` into one such world) — so the headlines carry `hworld` and no separate range hypothesis;
* `determinedVia_expectApprox_near` (T8 (i), the mesh error): in every completed-theory world the
  precision-`k` threshold mesh of a settled LUV is within `1/k` of the settled value (FAF's
  `lem:conluvapprox`, `PCWorld.expectApprox_near_ofGrid`);
* `expectAffineSeq_boundedPrices`: the diagonal mesh family of any LUV family has prices in `[0,1]`
  at any inductor (the `BoundedAffinePrices` input of FAF's affine provability induction);
* T7 (`abs_sub_le_of_abs_le_of_abs_le`, `asympEq_restrict_of_near`): the per-`n` triangle inequality
  and its asymptotic form restricted to a free predicate `G` — plumbing, kind L, nothing is
  called a theorem about `G` here.

Roles: `P` is always the **reader** (the inductor whose day-`n` expectation is forced); in the
deference story this is `A`, the predictor whose process `D_A` adjoins the settlement. Scope:
one-way.
-/

namespace Cleanroom.Deference.DefTrackingPin

open LogicalInduction Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## Settlement facts -/

/-- **A settled value lies in `[0,1]`**, once some world is consistent with every stage of the
process: FAF's compactness (`DeductiveProcess.exists_consistentWithTheory`) produces one from the
per-stage `hworld`, and `PCWorld.ValuesAt` carries the range. Without `hworld`, `DeterminedVia` is
vacuous and says nothing about `y`; this is why every headline of the package carries `hworld` and
no separate range hypothesis on the target. Reader-side fact; one-way.
Source: none: infrastructure (FAF `PCWorld.ValuesAt`, `DeductiveProcess.exists_consistentWithTheory`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem determinedVia_mem_Icc {X : LUV} {DP : DeductiveProcess} {y : ℝ}
    (hdet : LUV.DeterminedVia X DP y)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) : 0 ≤ y ∧ y ≤ 1 := by
  obtain ⟨v, hv⟩ := DeductiveProcess.exists_consistentWithTheory DP hworld
  exact ⟨(hdet v hv).1, (hdet v hv).2.1⟩

/-- A settled LUV is valued by every completed-theory world — the `hval` input of FAF's
`LUV.expect_converges` / `LUV.expectInf` (`thm:ec`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem determinedVia_exists_valuesAt {X : LUV} {DP : DeductiveProcess} {y : ℝ}
    (hdet : LUV.DeterminedVia X DP y) :
    ∀ v : PCWorld, v.ConsistentWithTheory DP → ∃ x : ℝ, v.ValuesAt X x :=
  fun v hv => ⟨y, hdet v hv⟩

/-- **T8 (i), the mesh error of a settled LUV**: in every world consistent with every stage of
`DP`, the precision-`k` approximate expectation `𝔼_k^W(X) = (1/k) Σ_{i<k} W(⌜X > i/k⌝)` of a LUV
settled at `y` is within `1/k` of `y`. This is the corpus's "`|val_W(C_n) − m*_n/n| ≤ 1/n`" with
the contract `C_n = (1/n) Σ_k θ_{n,k}` read as FAF's precision-`n` threshold mesh `LUV.expectAffine
X n` (its completed-world value is exactly `expectApprox`, `LUV.expectAffine_value`), and the
settling profile read as `DeterminedVia`. FAF's `lem:conluvapprox` at the settled value; the
`li-asymp-calc` bridge `DeterminedVia.approxDetermined_mesh_ofLUV` is the same fact at the diagonal
precision `n + 1` in `ApproxDeterminedViaTheory` form. One-way (reader-side).
Source: anson-2-021 (chat 05 L10380–10420, `val^α_W(n)`; chat 08 L921–991, `|m*_n/n − Y_n| ≤ 1/2n`); FAF `PCWorld.expectApprox_near_ofGrid`
Kind: L
Fidelity: stronger: FAF's LUV has thresholds at every rational, so the corpus's grid-rounding of the target (`m*_n = round(n·Y_n)`) does not occur — the error is the mesh's `1/k` alone
Hyps: (a) none -/
theorem determinedVia_expectApprox_near {X : LUV} {DP : DeductiveProcess} {y : ℝ}
    (hdet : LUV.DeterminedVia X DP y) {k : ℕ} (hk : 0 < k) (v : PCWorld)
    (hv : v.ConsistentWithTheory DP) :
    |X.expectApprox v.payout k - y| ≤ 1 / k := by
  have hval := hdet v hv
  have hgrid : ∀ i : ℕ, i < k →
      (((i : ℝ) / k < y → v.Holds (X.gt ((i : ℚ) / (k : ℚ)))) ∧
        (y < (i : ℝ) / k → ¬ v.Holds (X.gt ((i : ℚ) / (k : ℚ))))) := by
    intro i _
    have hc : (((i : ℚ) / (k : ℚ) : ℚ) : ℝ) = (i : ℝ) / (k : ℝ) := by
      push_cast
      ring
    have := hval.2.2 ((i : ℚ) / (k : ℚ))
    rw [hc] at this
    exact this
  exact PCWorld.expectApprox_near_ofGrid hval.1 hval.2.1 hk hgrid

/-! ## The diagonal mesh family at an inductor -/

/-- The diagonal threshold-mesh family `n ↦ mesh_{n+1}(X_n)` of any LUV family has all its
cross-day prices in `[0,1]` at any inductor — the `BoundedAffinePrices` input of FAF's affine
provability induction (`PolySequence.affine_provind_theory_*`).
Source: none: infrastructure (FAF `IsLogicalInductor.price_mem_Icc`, `LUV.expectApprox_le_one`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem expectAffineSeq_boundedPrices (X : ℕ → LUV) (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] :
    BoundedAffinePrices (fun n => (X n).expectAffine (n + 1)) P := by
  have hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1 := fun n φ =>
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) n φ
  refine ⟨1, zero_le_one, fun n m => ?_⟩
  rw [AffineCombination.price, LUV.expectAffine_value, abs_le]
  exact ⟨by linarith [(X n).expectApprox_nonneg (P m) (n + 1) (fun s => (hP m s).1)],
    (X n).expectApprox_le_one (P m) (n + 1) (fun s => (hP m s).2)⟩

/-! ## T7: on the settled-and-correct days the quote is early-revealed truth (plumbing) -/

/-- **T7, per-`n` form** (root-deference-040's "`a_n ≈ Y_n ≈ 𝟙(P^{(n)})` on `G`", one day at a
time): if the reader's price is within `τ` of the settled value and the settled value is within
`ε` of a third quantity `t` (the corpus's truth value), the price is within `τ + ε` of `t`. A
triangle inequality, stated per `n` and **not** over a parameter set; kind L — it is what
`def-frozen-sibling` instantiates on its ledger-defined days, and nothing here is a theorem about
such a set. One-way.
Source: root-deference-040 ([[deference-in-logical-induction-v6]] §5.5 line 588, Lean block 644–646; `FrozenDeliberation.quote_is_truth_on_G`, [[AUDIT]] §3.3)
Kind: L
Fidelity: exact (the triangle step the source's "composition" consists of; the forcing of `|a_n − Y_n| → 0` is T1, not this lemma)
Hyps: (a) none -/
theorem abs_sub_le_of_abs_le_of_abs_le {x v t τ ε : ℝ} (h1 : |x - v| ≤ τ) (h2 : |v - t| ≤ ε) :
    |x - t| ≤ τ + ε :=
  (abs_sub_le x v t).trans (add_le_add h1 h2)

/-- **T7, asymptotic form on a free predicate `G`**: if `x ≈ₙ v` (T1's conclusion) and on the days
of `G` the settled value `v` is within `ε_n → 0` of `t`, then on the days of `G` the reader's price
is eventually within any `δ > 0` of `t` — rendered as `∀ δ > 0, ∀ᶠ n, n ∈ G → |x n − t n| ≤ δ`.
`G` is a free predicate in a plumbing lemma, not a parameter of a theorem about the deference
construction (the plan forbids the latter in `def-frozen-sibling`; the ledger-defined `G` is that
package's). One-way.
Source: root-deference-040 ([[deference-in-logical-induction-v6]] §5.5 line 588); lean-deference-022 (`quote_is_truth_on_G`, [[AUDIT]] §3.3)
Kind: L
Fidelity: exact (asymptotic restriction form)
Hyps: (a) none (`hx` is T1's conclusion, supplied by the caller; `hG` is the on-`G` closeness the caller defines `G` by) -/
theorem asympEq_restrict_of_near {x v t ε : ℕ → ℝ} (G : Set ℕ) (hx : x ≈ₙ v)
    (hG : ∀ n ∈ G, |v n - t n| ≤ ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ δ > 0, ∀ᶠ n in atTop, n ∈ G → |x n - t n| ≤ δ := by
  intro δ hδ
  have h1 := asympEq_iff_eventuallyWithin.1 hx (δ / 2) (half_pos hδ)
  have h2 : ∀ᶠ n in atTop, |ε n| ≤ δ / 2 := by
    have := hε.abs
    rw [abs_zero] at this
    exact this.eventually (eventually_le_nhds (half_pos hδ))
  filter_upwards [h1, h2] with n hn1 hn2 hnG
  have h3 := hG n hnG
  have h4 : ε n ≤ |ε n| := le_abs_self _
  calc |x n - t n| ≤ |x n - v n| + |v n - t n| := abs_sub_le _ _ _
    _ ≤ δ / 2 + ε n := add_le_add hn1 h3
    _ ≤ δ / 2 + δ / 2 := by linarith
    _ = δ := by ring

end Cleanroom.Deference.DefTrackingPin
