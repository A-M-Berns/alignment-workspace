import Cleanroom.Fa.FaAdaptiveJoint.Theorem2

/-!
# `fa-adaptive-joint` · ValueGap: "value gap is pure arbitrage" re-examined (T8)

[[fa-adaptive-joint-mandate]] T8; lean-deference-011. `research/lean-deference/LeanDeference.lean:688–696`
(`DeferenceTrader.round_profit_ge_gap`, `gap_pos_imp_profit_pos`) proves `a ≤ a + b` for `b ≥ 0`
and calls it the novice-trades-in-expert's-market arbitrage (v6 §3.1). Over FAF the content of
that claim is the dependency's T3/T4 under (L): a trader on `H`'s market whose gate reads `A`'s
quote is `LegibleOn H (quoteSeq Y A)` (the one-way direction `li-quote-lane` ships), and a
persistent gap `a_n − h_n ≥ c` on a divergent legible gate contradicts
`theoremSS_limitPoint_general` — the "round profit ≥ gap" arithmetic being `bundle_price_self`
(the trader pays `𝔼^H_n(X_n)` for the day-`n` mesh) plus the squeeze. What the stub conflates:
the *quote gap* `a_n − h_n` and the *realized profit* `Y_n − h_n` differ by `a_n − Y_n`, whose
average has a limit point `0` only on a generable divergent gate (`quote_unbiased`) — that is the
`A`-side engine, not arithmetic. The v6 claim's `J`-indexed option form (`argmax` over options) is
reduced here to the single-LUV form (`def-lattice`'s LUV-level names), with the loss recorded:
nothing about an `argmax` survives the reduction, only the fixed family `X`.

Findings F7: the stub is Kind T; the claim needs (L), not joint clearing — contrary to the
inventory's "depends on 047".
-/

namespace Cleanroom.Fa.FaAdaptiveJoint

open LogicalInduction Cleanroom.Fa.FaForcingTrader Cleanroom.Fa.FaTheoremA
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Filter Topology
open Cleanroom.Fa.FaForcingTrader.A (theoremSS_limitPoint_general)

/-- **The round-trip arithmetic of the stub, honestly**: the per-unit cash of buying the day-`n`
threshold mesh of `X_n` on `H`'s market at day `n` and selling at day `f n` is
`price^H_{f n}(bundle X n) − 𝔼^H_n(X_n)` (`bundle_price_self`): the purchase price *is* the
expert's expectation, and the sale price is a later market price — not the novice's quote `a_n`.
The stub's "profit ≥ gap" needs `a_n − Y_n` controlled, which is `quote_unbiased`, not arithmetic.
Source: lean-deference-011 (`round_profit_ge_gap`); `fa-forcing-trader` `bundle_price_self`
Kind: L
Fidelity: variant: the stub's `a ≤ a + b` replaced by the actual cash identity
Hyps: (a) none -/
theorem roundTrip_cash (X : ℕ → LUV) (H : History) (f : DeferralFunction) (n : ℕ) :
    (bundle X n).price H (f.f n) - (bundle X n).price H n =
      (bundle X n).price H (f.f n) - (X n).expect H n := by
  rw [bundle_price_self]

/-- **T8 (headline). No persistent value gap on a divergent legible gate** (one-way, under (L)):
for inductors `A`, `H`, a quote package, a window-disjoint schedule `d`, an `A`-generable
weighting `G` supported on `im d`, legible on `H` (`hL`, the corpus's (L): the gate reads only
`A`'s quote), and divergent in `A`'s prices, it is **not** the case that
`𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) − 𝔼^H_n(X_n) ≥ c` on every day the gate is positive, for any `c > 0`.
This is lean-deference-011's claim with its content located: the dependency's
`theoremSS_limitPoint_general` (the `A`-side `quote_unbiased` plus the `H`-side `hSideBridge`,
FAF's own Kelly round trip) gives a limit point `0` of the gate-weighted bias, against the gap.
Scope: one-way (`H` reads `A`'s quote through `hL`; `A` never reads `H`). e.c. family `X`.
Schedule: window-disjoint `DeferralFunction`. Grade: limit point. The two-way version — the gate
reading `h_n` as well — is `v3Theorem2_gate_of_bridge` under `hjoint`.
Source: lean-deference-011; [[deference-in-logical-induction-v6]] §3.1; [[fa-adaptive-joint-mandate]] § T8
Kind: C
Fidelity: variant: the single-LUV form of v6's `J`-indexed option claim (the `argmax` is lost in the reduction)
Hyps: (a) `hcode`, `hworldA`, `hworldH`, `hval`, `hwd`, `hG`, `hsupp`, `hdiv`, `hc`; (c) `pkg.reflected`; (c) `hL` (the corpus's (L)). -/
theorem valueGap_not_persistent {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d)
    {G : ℕ → EF} (hG : PGenerableWeighting G)
    (hsupp : ∀ n, (G n).denote A ≠ 0 → ∃ k, d.f k = n)
    (hL : LegibleOn H (fun n => (G n).denote A))
    (hdiv : DivergentWeighting G A) {c : ℝ} (hc : 0 < c) :
    ¬ ∀ n, 0 < (G n).denote A → c ≤ quoteSeq Y A n - (X n).expect H n := by
  intro hgap
  have hlp := theoremSS_limitPoint_general pkg hcode hworldA hworldH hval hwd hG hsupp hL hdiv
  rw [hasLimitPoint_zero_iff] at hlp
  have hev : ∀ᶠ n in atTop, 0 < prefixSum (fun n => (G n).denote A) n :=
    hdiv.2.eventually (eventually_gt_atTop 0)
  obtain ⟨n, h1, h2⟩ := ((hlp c hc).and_eventually hev).exists
  have hge : c ≤ weightedAverage (fun n => (G n).denote A)
      (fun i => quoteSeq Y A i - (X i).expect H i) n :=
    le_weightedAverage_of_support (fun i => (hdiv.1 i).1) hgap h2
  rw [weightedBias, abs_lt] at h1
  linarith [h1.2]

end Cleanroom.Fa.FaAdaptiveJoint
