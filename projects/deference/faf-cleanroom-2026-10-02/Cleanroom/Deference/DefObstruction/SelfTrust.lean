import Cleanroom.Deference.DefObstruction.Tracking
import Cleanroom.Found.DefLattice.Expert
import Cleanroom.Found.LiAsympCalc.Ramp

/-!
# `def-obstruction` · SelfTrust: externalized self-trust, conditional on Tracking (T12)

[[self-referential-settlement-target]] §5.1 (Theorem 5.1): with the one-sided ramp
`I⁺_n := Ind_δ(R_n > p_n)` on the recorded quote and `B⁺_n := I⁺_n · (𝟙 P^{(n)} − p_n)`, **if**
Tracking `a_n − Y_n → 0` holds then `𝔼^H_n(B⁺_n) ≳ₙ 0`. Its proof has three steps: a `cee`-type
step (`𝔼^H_n(B⁺_n) ≈ₙ 𝔼^H_n(⌜𝔼^H_{F n}(B⁺_n)⌝)`, then the quote read off), the **resale step**
(`𝔼^H_{F n}(B⁺_n) ≈ₙ i⁺_n (Y_n − p_n)`, exact only on the dropped measure substrate, approximate
over a plain inductor — anson-2-001), and the **one-sided lower bound**
`i⁺_n (Y_n − p_n) ≥ −|a_n − Y_n|` (pure algebra). Over FAF the first two are hypothesis packages
whose closed forms exist only for `paperDP T` and do not cover the product LUV `B⁺_n` over the
ledger process; they are carried here as **(c) packages** (`hcee`, `hQ`, `hres`), and the row is
`partial: product-LUV package`. What is proved outright is the algebra (`resale_lb`,
`resale_lb_ramp`) and the composition (`externalized_self_trust_of_packages`,
`externalized_self_trust`) — kind L over the packages, **not a headline**.

**The hypothesis of record is Tracking**, which 2a kills on the diagonal (`Tracking.lean`): the
theorem is non-vacuous only on families where Tracking holds, and it does not transfer to the
autonomous target as written (there `Y_n = 𝔼^{H₀}_{F n}` is not the reader's own deferred
credence, so the resale identity's right side is a different market's expectation; findings
F-Transfer).

Scope: one-way (the reader's own market; the packages are its).
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction LO.Propositional Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.DefLattice Cleanroom.Li.LiDiagonal
open Filter Topology

/-- **The resale lower bound (one-sided indicator)**: for a settled indicator value `i ∈ [0,1]`
with the one-sided property `0 < i → p < r`, the resale `i · (Y − p)` is at least `−|r − Y|`.
Scope: real numbers.
Source: [[self-referential-settlement-target]] §5.1 (proof, "Lower bound"); `SelfReferentialTarget.lean:resale_lb` (anson-007)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem resale_lb (i p r Y : ℝ) (hi0 : 0 ≤ i) (hi1 : i ≤ 1) (hone : 0 < i → p < r) :
    -|r - Y| ≤ i * (Y - p) := by
  rcases eq_or_lt_of_le hi0 with h | h
  · rw [← h, zero_mul]
    exact neg_nonpos.mpr (abs_nonneg _)
  · have hpr := hone h
    rcases le_or_gt 0 (Y - p) with hY | hY
    · have : 0 ≤ i * (Y - p) := mul_nonneg hi0 hY
      linarith [abs_nonneg (r - Y)]
    · have h1 : Y - p ≤ i * (Y - p) := by nlinarith
      have h2 : r - Y ≤ |r - Y| := le_abs_self _
      linarith

/-- **The resale lower bound at `def-lattice`'s one-sided ramp** `rampAbove δ p r = Ind_δ(r > p)`
(FAF's `ctsInd`): `−|r − Y| ≤ rampAbove δ p r · (Y − p)`.
Scope: real numbers.
Source: [[self-referential-settlement-target]] §5.1 (the one-sided indicator "lands the conclusion at exactly `p_n`"); anson-007
Kind: L
Fidelity: exact (FAF's ramp)
Hyps: (a) none -/
theorem resale_lb_ramp {δ : ℚ} (hδ : 0 < δ) (p : ℚ) (r Y : ℝ) :
    -|r - Y| ≤ rampAbove δ p r * (Y - p) :=
  resale_lb _ p r Y (ctsInd_nonneg δ r p) (ctsInd_le_one δ r p)
    (fun h => (ctsInd_pos_iff hδ r p).mp h)

/-- **Externalized self-trust as a composition of packages** (real sequences): if the present
value `present_n` of the position is asymptotically its deferred value `deferred_n` (the `cee` step
and the quote read-off), the deferred value is asymptotically the resale `i_n (Y_n − p_n)` (the
resale step), the settled indicator is one-sided against the quote `a_n`, and Tracking holds, then
`present ≳ₙ 0`.
Scope: real sequences.
Source: [[self-referential-settlement-target]] §5.1 Theorem 5.1 (anson-007); anson-2-001 (the approximate resale step); `SelfReferentialTarget.lean:externalized_self_trust`
Kind: L (over the packages)
Fidelity: variant: approximate resale step (anson-2-001); the `cee`/read-off/resale steps as hypotheses
Hyps: (c) `hcee` (the `cee` + read-off package), (c) `hres` (the resale package), (c) `hT` (Tracking — dead on the diagonal, T2) -/
theorem externalized_self_trust_of_packages (present deferred i p a Y : ℕ → ℝ)
    (hcee : present ≈ₙ deferred)
    (hres : deferred ≈ₙ fun n => i n * (Y n - p n))
    (hi : ∀ n, 0 ≤ i n ∧ i n ≤ 1) (hone : ∀ n, 0 < i n → p n < a n)
    (hT : Tendsto (fun n => a n - Y n) atTop (𝓝 0)) :
    present ≳ₙ fun _ => (0 : ℝ) := by
  have h := hcee.trans hres
  unfold AsympEq at h
  have hT' : Tendsto (fun n => |a n - Y n|) atTop (𝓝 0) := by simpa using hT.abs
  intro ε hε
  filter_upwards [h.eventually (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε)),
    hT'.eventually (Iio_mem_nhds (half_pos hε))] with n hn1 hn2
  have hn1' : |present n - i n * (Y n - p n)| < ε / 2 := by
    simpa [Real.dist_eq] using hn1
  have hn2' : |a n - Y n| < ε / 2 := hn2
  have hlb := resale_lb (i n) (p n) (a n) (Y n) (hi n).1 (hi n).2 (hone n)
  have h3 := (abs_lt.mp hn1').1
  linarith

/-- **Externalized self-trust over the carrier, conditional on Tracking** (T12): for a LUV
family `B` standing in for the source's product position `B⁺_n = I⁺_n·(𝟙P^{(n)} − p_n)`, its quote
family `Q` (`⌜𝔼^H_{F n}(B_n)⌝`), the contract family `X`, the threshold stream `p` and the ramp
width `δ`: under the `cee` package `hcee`, the quote read-off `hQ`, the resale package `hres`
(with the settled indicator `rampAbove δ (p n) (a 0 n)`), and Tracking
`a 0 n − 𝔼^H_{F n}(X_n) → 0`, the reader's present expectation of the position is asymptotically
nonnegative: `𝔼^H_n(B_n) ≳ₙ 0`. **`B` is unconstrained** (audit r2 N4): the statement ties `B` to
`X`, `p`, `δ` only through `hres`; the product shape of the source's `B⁺_n` lives in the unbuilt
resale package, not in this theorem — it is `externalized_self_trust_of_packages` with FAF's
names. The Tracking antecedent `hT` is inhabited on the benign family (`BlindWitness.lean`,
`adjPair_tracks_obsFamily`: `X n := 𝟙 (obsFamily n)` over `adjPair` at `succDeferral`); the three
packages are not.
Scope: one-way.
Source: [[self-referential-settlement-target]] §5.1 Theorem 5.1 (anson-007); [[deference-in-logical-induction-v6]] §4.5; root-deference-028; lean-deference-016; mandate T12
Kind: L (over the packages; the LI content is in `hcee`, `hQ`, `hres`)
Fidelity: variant: product-LUV, `cee` and resale steps as (c) packages; approximate resale (anson-2-001)
Hyps: (c) `hcee`, `hQ`, `hres` — FAF's closed `cee`/product forms do not cover the ledger process; (c) Tracking `hT` (dead on the diagonal) -/
theorem externalized_self_trust (T : TablePair) (F : DeferralFunction) (B Q X : ℕ → LUV)
    (p : ℕ → ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hcee : (fun n => (B n).expect T.H n) ≈ₙ (fun n => (Q n).expect T.H n))
    (hQ : (fun n => (Q n).expect T.H n) ≈ₙ (fun n => (B n).expect T.H (F n)))
    (hres : (fun n => (B n).expect T.H (F n)) ≈ₙ
      (fun n => rampAbove δ (p n) (T.a 0 n) * ((X n).expect T.H (F n) - p n)))
    (hT : Tendsto (fun n => (T.a 0 n : ℝ) - (X n).expect T.H (F n)) atTop (𝓝 0)) :
    (fun n => (B n).expect T.H n) ≳ₙ fun _ => (0 : ℝ) :=
  externalized_self_trust_of_packages _ _ (fun n => rampAbove δ (p n) (T.a 0 n))
    (fun n => (p n : ℝ)) (fun n => (T.a 0 n : ℝ)) (fun n => (X n).expect T.H (F n))
    (hcee.trans hQ) hres
    (fun _ => ⟨ctsInd_nonneg δ _ _, ctsInd_le_one δ _ _⟩)
    (fun _ h => (ctsInd_pos_iff hδ _ _).mp h) hT

end Cleanroom.Deference.DefObstruction
