import Cleanroom.Li.LiDiagonal.Defs
import Cleanroom.Found.LiAsympCalc.Ramp
import LogicalInduction.Properties.Pseudorandomness

/-!
# `li-diagonal` · Legality: the legality audit of the scope-note cluster (T7c)

The verdicts of [[faithful-acceleration-scope]] §4's repair (trust-lab-056/057), over FAF's own
definitions:

* **(i)** the hard gate on *yesterday's* price is no `EF` (`hardGate_yesterday_not_ef`:
  `li-asymp-calc`'s `not_exists_ef_hardIndicator` at index `n − 1`), hence never the denotation of a
  `PGenerableWeighting` — so the "repaired dichotomy" (T7b) is a fact about real sequences against
  a hard gate, not about inductors; the inductor-level content is T2 with soft gates (K6).
* **(iii)** `f n = 2^n` **is** a `DeferralFunction` in FAF: `doublingDeferral` (`Properties/SelfTrust.lean`),
  with its `Complexity.FP` graph witness. The mandate's "may be expensive" is moot and the FAF API
  request is withdrawn (`twoPowDeferral_f`).
* **(iv)** the weighting with weight `1` every day is **not** `2^n`-patient
  (`const_one_not_doublingPatient`: the window `[n, 2^n]` has `2^n + 1 − n ≥ n + 1` days).
* **(v)** `2^n` is a `StrictlyIncreasingDeferral` (`doublingDeferral_strictlyIncreasing`), the
  clause `lic_wub`/`lic_wubaff` need (the inventory's "feedback in before the next weighted term").

* **(ii)** the legality of the soft ramp on yesterday's price is written in `PastPrice.lean`
  (`priceRampBelow_yesterday_pgenerable`, repair round 1: the `priceRampBelow_pgenerable` spine at
  the ruler `n − 1`).

Not written: the supported-on-the-image clause `WeightingSupportedOnDeferralImage` for `2^n`.

Scope: single-market (legality is a property of one market's feature language).
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO.Propositional Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- **T7c(i).** The hard gate `𝟙[t < P_{n−1}(φ)]` on yesterday's price is no expressible feature.
Scope: single-market.
Source: [[trust-lab-inventory]] 056, 057 (K6); `li-asymp-calc` `not_exists_ef_hardIndicator`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem hardGate_yesterday_not_ef (t : ℝ) (n : ℕ) (φ : Sentence) :
    ¬ ∃ e : EF, ∀ V : History, e.denote V = if t < V (n - 1) φ then 1 else 0 :=
  not_exists_ef_hardIndicator t (n - 1) φ

/-- **T7c(iii).** FAF's `doublingDeferral` is the deferral `n ↦ 2^n`.
Scope: single-market.
Source: [[trust-lab-inventory]] 056 (K6); FAF `doublingDeferral`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem twoPowDeferral_f (n : ℕ) : doublingDeferral n = 2 ^ n := rfl

/-- **T7c(v).** `2^n` is a strictly increasing deferral.
Scope: single-market.
Source: [[trust-lab-inventory]] 057; FAF `StrictlyIncreasingDeferral`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem doublingDeferral_strictlyIncreasing : StrictlyIncreasingDeferral doublingDeferral :=
  fun _ _ h => Nat.pow_lt_pow_right (by norm_num) h

/-- **T7c(iv).** The weighting with weight `1` every day is not `2^n`-patient: the window
`[n, 2^n]` carries `2^n + 1 − n ≥ n + 1` units.
Scope: single-market.
Source: [[trust-lab-inventory]] 057 (K6); [[li-diagonal-mandate]] T7c(iv)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem const_one_not_doublingPatient (P : History) :
    ¬ DeferralPatient doublingDeferral (fun _ => EF.const 1) P := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have h := hC (n + 1)
  simp only [EF.denote_const, Rat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [twoPowDeferral_f, Nat.card_Icc] at h
  have hpow : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  have hpow2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have hn' : n < 2 ^ n := Nat.lt_two_pow_self
  have hcard : n + 2 ≤ 2 ^ (n + 1) + 1 - (n + 1) := by omega
  have hle : ((n + 2 : ℕ) : ℝ) ≤ ((2 ^ (n + 1) + 1 - (n + 1) : ℕ) : ℝ) := Nat.cast_le.mpr hcard
  rw [Nat.cast_add, Nat.cast_ofNat] at hle
  linarith

end Cleanroom.Li.LiDiagonal
