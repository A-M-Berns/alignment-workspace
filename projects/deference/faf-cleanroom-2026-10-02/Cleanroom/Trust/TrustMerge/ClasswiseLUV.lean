import Cleanroom.Trust.TrustMerge.Classwise
import Cleanroom.Trust.TrustMerge.Defs
import Cleanroom.Found.DefLattice.TwoOptionLUV

/-!
# `trust-merge` · ClasswiseLUV: classwise hedged Value on two-option menus (T6, LUV instance)

The LUV instance of `Classwise.lean` over the hedged two-option menus of `def-lattice`
(`twoOptionComb s XW W n = s + XW_n − s·W_n`, the followed strategy `X·w + s(1 − w)` with `W`
the weight quote and `XW` the product quote of a `WeightQuoteEst`). Per menu the Value gap is
**exactly** `𝔼^H_n(XW_n) − s·𝔼^H_n(W_n)` (`twoOptionComb_expect`, linearity of
`LUVCombination.expect`), so classwise hedged Value over the class indexed by the realized gate
mass `g_n := 𝔼^H_n(W_n)` **is** the classwise product-form inequality
(`classwiseValue_twoOption_iff`) — the source's Corollary display
`Σ_n g_n 𝔼_n(X_n) / Σ_n g_n ≳ t` with `g_n 𝔼_n(X_n)` read as the product quote's price
`𝔼_n(XW_n)` (the reflection step "the decided scalar pulls out", `𝔼_n(XW_n) ≈ g_n 𝔼_n(X_n)`, is
the per-day slack of `Classwise.lean`'s `e_n`; its gate-negligibility is the hypothesis the
commutation needs, not a free fact).
-/

namespace Cleanroom.Trust.TrustMerge

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Found.LiAsympCalc

noncomputable section

/-- **Classwise hedged Value on two-option menus is the classwise product form** (T6, LUV
instance): over the class indexed by the realized gate mass `g_n = 𝔼^H_n(W_n)`, the classwise
mean of the hedged strategy's Value gap `𝔼^H_n(twoOptionComb s XW W n) − s` is the classwise
mean of the product form `𝔼^H_n(XW_n) − s·𝔼^H_n(W_n)` — exactly, by `twoOptionComb_expect`.
Grade: averaged (classwise). Weight class: the realized gate.
Source: root-fa-039; [[faithful-acceleration]] §5 l. 161 (the Corollary, read at the product
quote); `def-lattice` `twoOptionComb_expect`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem classwiseValue_twoOption_iff (H : History) (s : ℚ) (W XW : ℕ → LUV) :
    ClasswiseValue (fun n => (W n).expect H n)
        (fun n => (twoOptionComb s XW W n).expect H n) s ↔
      classwiseMean (fun n => (W n).expect H n)
        (fun n => (XW n).expect H n - (s : ℝ) * (W n).expect H n) ≳ₙ (fun _ => (0 : ℝ)) := by
  unfold ClasswiseValue
  have : (fun n => (twoOptionComb s XW W n).expect H n - (s : ℝ)) =
      fun n => (XW n).expect H n - (s : ℝ) * (W n).expect H n := by
    funext n
    rw [twoOptionComb_expect]
    ring
  rw [this]

/-- **Classwise hedged Value from the averaged inequality on the price of `X`**, when the
product quote's price is the gated price of `X` up to a gate-negligible slack
(`e_n := 𝔼_n(XW_n) − 𝔼_n(W_n) 𝔼_n(X_n)`, the "decided scalar pulls out" residual): the LUV
instance of `classwiseValue_of_averaged_of_negligible`.
Source: root-fa-039; [[faithful-acceleration]] §5 ("`g_n` is decided by day `n` … so the decided
scalar pulls out of the expectation"); mandate T6
Kind: C
Fidelity: variant: the reflection step carried as the slack hypothesis `hneg`
Hyps: (c) `hneg` — the source's "the decided scalar pulls out" step
(`𝔼_n(XW_n) − 𝔼_n(W_n)·𝔼_n(X_n)` gate-negligible), a carried modelling hypothesis, neither
derived here nor a paper theorem (`classwise_slack_counterexample` shows it is needed; audit r1
adversarial N2); all else (a) -/
theorem classwiseValue_twoOption_of_averaged (H : History) (s : ℚ) (X W XW : ℕ → LUV)
    (hdiv : Tendsto (prefixSum (fun n => (W n).expect H n)) atTop atTop)
    (hneg : Tendsto (classwiseMean (fun n => (W n).expect H n)
      (fun n => (XW n).expect H n - (W n).expect H n * (X n).expect H n)) atTop (𝓝 0))
    (h : weightedAverage (fun n => (W n).expect H n) (fun n => (X n).expect H n - (s : ℝ)) ≳ₙ
      (fun _ => (0 : ℝ))) :
    ClasswiseValue (fun n => (W n).expect H n)
      (fun n => (twoOptionComb s XW W n).expect H n) s :=
  classwiseValue_of_averaged_of_negligible (fun n => (W n).expect H n)
    (fun n => (X n).expect H n) _ _ (s : ℝ)
    (fun n => by rw [twoOptionComb_expect]; ring) hdiv hneg h

end

end Cleanroom.Trust.TrustMerge
