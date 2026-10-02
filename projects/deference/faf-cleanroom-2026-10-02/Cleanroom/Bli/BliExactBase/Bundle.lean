import Cleanroom.Bli.BliExactBase.Obstruction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Rat.BigOperators

/-!
# `bli-exact-base` — bli-soto-b-025: the `n = 1` bundle market, its two "by definition" claims and
its three findings

**The object** (`BundleMarket m`): a distribution `β` over the `m` interval sentences
`I_r = "Q_{k+1}(φ) ∈ cell r"` of one coordinate, with representatives `rep r`;
`Q_k(φ) := ∑_r rep r · β r` and `Q_k(φ ∧ I_r) := rep r · β r`. The source's two "by definition"
claims are definitional: **reflection/self-trust in cell form** (`BundleMarket.faith`) and the
identity `Q_k(φ) = ∑_r rep r · Q_k(I_r)`, which is `D_NNUcell` at one coordinate
(`BundleMarket.nnucell`).

**Findings** (findings F8–F10):

1. **Midpoint slack** (`midpoint_slack`, `midpoint_slack_strict`): with `rep` the cell midpoint,
   `Q_k(φ | I_r) = rep r` differs from the realized `Q_{k+1}(φ) = x ∈ I_r` by up to half a cell
   width `1/(2m)`, and is exact only when `x` is the representative — "epistemic self-trust by
   definition" is self-trust up to `2^{-(k+2)}` at the source's grid.
2. **Coherence across coordinates is not inherited** (`cross_coordinate_incoherent`): two bundle
   markets for `φ` and `∼φ` with the same cells have `Q_k(φ) + Q_k(∼φ) = 1/2`. The source's
   "propositional coherence by marginalization" needs a *joint* law over the interval sentences
   of all coordinates — K7d's coherent-carrier requirement.
3. **The implicit LIC claim** (route β, `Open.bundleMarket_LI_exists`): the bundle market's
   world-price vector lies in the constrained set of `Obstruction.lean`
   (`worldPrice_constrained`), so by the obstruction theorem **it is never market-maker
   acceptable against its own bundle trade** when some cell has `rep r₀ < 1`
   (`bundleMarket_not_acceptable`): an LI with the bundle market's prices cannot come from a
   per-day acceptance search at these prices.
-/

namespace Cleanroom.Bli.BliExactBase.Bundle

open Finset Cleanroom.Bli.BliExactBase.Obstruction

/-- **The `n = 1` bundle market** over `m` cells: a distribution over the interval sentences of one
coordinate, with representatives.
Source: bli-soto-b-025; mandate § 8
Kind: D
Fidelity: exact -/
structure BundleMarket (m : ℕ) where
  /-- The price of the interval sentence `I_r`. -/
  β : Fin m → ℚ
  /-- Prices are nonnegative. -/
  nonneg : ∀ r, 0 ≤ β r
  /-- The interval sentences are priced as a partition. -/
  sum_one : ∑ r, β r = 1
  /-- The representative of cell `r`. -/
  rep : Fin m → ℚ

namespace BundleMarket

variable {m : ℕ}

/-- `Q_k(I_r)`.
Source: bli-soto-b-025
Kind: D
Fidelity: exact -/
def priceLit (M : BundleMarket m) (r : Fin m) : ℚ := M.β r

/-- `Q_k(φ) := ∑_r rep r · Q_k(I_r)` — the object-level share as the bundle.
Source: bli-soto-b-025
Kind: D
Fidelity: exact -/
def priceCoord (M : BundleMarket m) : ℚ := ∑ r, M.rep r * M.β r

/-- `Q_k(φ ∧ I_r) := rep r · Q_k(I_r)`.
Source: bli-soto-b-025
Kind: D
Fidelity: exact -/
def priceConj (M : BundleMarket m) (r : Fin m) : ℚ := M.rep r * M.β r

/-- **"Self-trust by definition"**: `Q_k(φ ∧ I_r) = rep r · Q_k(I_r)` — faith at the representative
(the per-candidate form of `bli-linkage`'s `E2xσIdx` at one coordinate).
Source: bli-soto-b-025 ("Reflection and self-trust hold by definition")
Kind: L
Fidelity: exact (self-trust at the *representative*, not at the realized price; `midpoint_slack`)-/
theorem faith (M : BundleMarket m) (r : Fin m) : M.priceConj r = M.rep r * M.priceLit r := rfl

/-- **The no-net-update identity by definition**: `Q_k(φ) = ∑_r rep r · Q_k(I_r)` — `D_NNUcell` at
one coordinate.
Source: bli-soto-b-025; bli-linkage `D_NNUcell`
Kind: L
Fidelity: exact -/
theorem nnucell (M : BundleMarket m) : M.priceCoord = ∑ r, M.rep r * M.priceLit r := rfl

/-- The bundle price is in `[0, 1]` when the representatives are.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem priceCoord_mem_Icc (M : BundleMarket m) (h : ∀ r, 0 ≤ M.rep r ∧ M.rep r ≤ 1) :
    0 ≤ M.priceCoord ∧ M.priceCoord ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun r _ => mul_nonneg (h r).1 (M.nonneg r)
  · calc M.priceCoord ≤ ∑ r, 1 * M.β r :=
          Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (h r).2 (M.nonneg r)
      _ = 1 := by simp [M.sum_one]

/-! ### The bundle market as a point of the constrained set -/

/-- **The bundle market's world-price vector**: mass `rep r · β r` on `(φ true, I_r)` and
`(1 − rep r) · β r` on `(φ false, I_r)` — the joint law over the plausible worlds whose marginals
are the bundle market's prices.
Source: bli-soto-b-025; mandate § 7–8
Kind: D
Fidelity: exact -/
noncomputable def worldPrice (M : BundleMarket m) : Bool × Fin m → ℝ :=
  fun w => if w.1 then (M.rep w.2 : ℝ) * M.β w.2 else (1 - M.rep w.2) * M.β w.2

/-- The induced price of `φ` is the bundle price.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem induced_worldPrice_none (M : BundleMarket m) :
    induced (cellPay m) M.worldPrice none = (M.priceCoord : ℝ) := by
  simp only [priceCoord]
  push_cast
  simp [induced, worldPrice, cellPay, Fintype.sum_prod_type]

/-- The induced price of `I_r` is `β r`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem induced_worldPrice_some (M : BundleMarket m) (r : Fin m) :
    induced (cellPay m) M.worldPrice (some r) = (M.β r : ℝ) := by
  simp only [induced, worldPrice, cellPay, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ]
  ring

/-- **The bundle market is a constrained price**: its world-price vector lies on the simplex and
satisfies `∑_r rep r · p(I_r) = p(φ)`.
Source: bli-soto-b-025; mandate § 7 (`K`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem worldPrice_constrained (M : BundleMarket m) (h : ∀ r, 0 ≤ M.rep r ∧ M.rep r ≤ 1) :
    M.worldPrice ∈ Constrained fun r => (M.rep r : ℝ) := by
  refine ⟨⟨fun w => ?_, ?_⟩, ?_⟩
  · unfold worldPrice
    have h0 := (h w.2).1
    have h1 := (h w.2).2
    have hb := M.nonneg w.2
    split_ifs
    · exact mul_nonneg (by exact_mod_cast h0) (by exact_mod_cast hb)
    · exact mul_nonneg (by linarith [(show (M.rep w.2 : ℝ) ≤ 1 by exact_mod_cast h1)])
        (by exact_mod_cast hb)
  · simp only [worldPrice, Fintype.sum_prod_type, Fintype.sum_bool, if_true, Bool.false_eq_true,
      if_false]
    rw [← Finset.sum_add_distrib]
    have : ∀ r : Fin m, (M.rep r : ℝ) * M.β r + (1 - M.rep r) * M.β r = (M.β r : ℝ) := by
      intro r; ring
    simp only [this]
    rw [← Rat.cast_sum, M.sum_one, Rat.cast_one]
  · simp only [induced_worldPrice_none, induced_worldPrice_some, priceCoord, Rat.cast_sum,
      Rat.cast_mul]

/-- **The bundle market is never market-maker acceptable against its own bundle trade** when some
cell has `rep r₀ < 1`: the obstruction theorem at the bundle market's prices.
Source: bli-soto-b-025 (the implicit LIC claim); bli-soto-a-058; mandate § 8 (iii)
Kind: C
Fidelity: exact (acceptance over the plausible worlds at slack `0`, `Obstruction.Acceptable`)
Hyps: (a) -/
theorem bundleMarket_not_acceptable (M : BundleMarket m) (h : ∀ r, 0 ≤ M.rep r ∧ M.rep r ≤ 1)
    {r₀ : Fin m} (hr : M.rep r₀ < 1) :
    ¬ Acceptable (cellPay m) (bundleTrade fun r => (M.rep r : ℝ)) M.worldPrice :=
  obstruction _ (worldPrice_constrained M h) (by exact_mod_cast hr)

end BundleMarket

/-! ## The midpoint cells of the source -/

/-- The lower end of cell `r` of `m` equal cells of `[0, 1]`.
Source: bli-soto-b-025 (`(m/2^{k+1}, (m+1)/2^{k+1}]`)
Kind: D
Fidelity: exact -/
def cellLo (m : ℕ) (r : Fin m) : ℚ := (r : ℚ) / m

/-- The upper end of cell `r`.
Source: bli-soto-b-025
Kind: D
Fidelity: exact -/
def cellHi (m : ℕ) (r : Fin m) : ℚ := ((r : ℚ) + 1) / m

/-- The midpoint representative `(r + 1/2) / m`.
Source: bli-soto-b-025 (`(m + 0.5)/2^{k+1}`)
Kind: D
Fidelity: exact -/
def midRep (m : ℕ) (r : Fin m) : ℚ := ((r : ℚ) + 1 / 2) / m

/-- **Midpoint slack**: a realized price in cell `r` is within half a cell width of the midpoint
representative (one-line interval arithmetic).
Source: bli-soto-b-025 (inventory flag: "self-trust up to `2^{-(k+2)}`"); mandate § 8 (i)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem midpoint_slack {m : ℕ} (hm : 0 < m) (r : Fin m) {x : ℚ}
    (hx : cellLo m r ≤ x ∧ x ≤ cellHi m r) : |x - midRep m r| ≤ 1 / (2 * m) := by
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  have h1 : midRep m r = cellLo m r + 1 / (2 * m) := by
    unfold midRep cellLo; field_simp
  have h2 : cellHi m r = cellLo m r + 1 / m := by
    unfold cellHi cellLo; field_simp
  have h3 : (1 : ℚ) / m = 2 * (1 / (2 * m)) := by field_simp
  rw [abs_le, h1]
  constructor <;> linarith [hx.1, hx.2, h2, h3]

/-- **Self-trust is exact only at the representative**: the lower end of every cell is a legal
realized price different from the midpoint.
Source: bli-soto-b-025 (inventory flag); mandate § 8 (i)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem midpoint_slack_strict {m : ℕ} (hm : 0 < m) (r : Fin m) :
    ∃ x, cellLo m r ≤ x ∧ x ≤ cellHi m r ∧ x ≠ midRep m r := by
  have hm' : (0 : ℚ) < m := by exact_mod_cast hm
  refine ⟨cellLo m r, le_refl _, ?_, ?_⟩
  · unfold cellLo cellHi
    exact div_le_div_of_nonneg_right (by linarith) hm'.le
  · unfold cellLo midRep
    intro h
    rw [div_left_inj' hm'.ne'] at h
    linarith

/-- **Coherence across coordinates is not inherited without a joint law**: two bundle markets at
the source's two-cell midpoint grid (`1/4`, `3/4`), one for `φ` and one for `∼φ`, both putting all
mass on the lower cell — the *same* one-coordinate market `M` used twice — price `φ` and `∼φ` at
`1/4` each: `Q_k(φ) + Q_k(∼φ) = 1/2 ≠ 1`. This is the case the source's hypothesis ("from
coherence of each possible `Q_{k+1}`", a joint law over coherent next-day tables) excludes: the
gap is that the `n = 1` construction supplies no such joint law (findings F9, regraded in repair
round 1 from "local error" to "gap").
Source: bli-soto-b-025 (inventory flag: "depends on the joint distribution over interval
sentences, which the source does not constrain"); mandate § 8 (ii)
Kind: P
Fidelity: exact (two independent per-coordinate markets, the case outside the source's hypothesis)
Hyps: (a) -/
theorem cross_coordinate_incoherent :
    ∃ Mφ Mnφ : BundleMarket 2, Mφ.rep = midRep 2 ∧ Mnφ.rep = midRep 2 ∧
      Mφ.priceCoord + Mnφ.priceCoord ≠ 1 := by
  let M : BundleMarket 2 :=
    { β := ![1, 0]
      nonneg := fun r => by fin_cases r <;> norm_num
      sum_one := by simp [Fin.sum_univ_two]
      rep := midRep 2 }
  refine ⟨M, M, rfl, rfl, ?_⟩
  simp [M, BundleMarket.priceCoord, Fin.sum_univ_two, midRep]

end Cleanroom.Bli.BliExactBase.Bundle
