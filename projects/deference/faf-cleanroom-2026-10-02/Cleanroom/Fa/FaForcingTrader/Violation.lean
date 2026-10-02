import Cleanroom.Fa.FaForcingTrader.A.Violation

/-!
# `fa-forcing-trader` · Violation: v3 Theorem 1 of record (T3)

Main module of the reconciled package ([[fa-forcing-trader-mandate]] T3). Only angle A attacked
T3 (angle B's report § T3: the `H` side of T3 is a wealth argument on a trader, not a citation of
4.8.16); its theorem is restated here verbatim and proved `:= A.…`. The two corollaries are
re-exported.

T3 is the package's one **two-way** target and ships at `partial: over the OPEN pair` for the
reason both angles record (mandate K3, findings F-A2): v3's joint clearing (A1) reads
`𝔼^H_n(X_n)` at `A`'s day `n`, which no FAF carrier supplies — not even li-coupled-pair's
`TwoWayPair`, which publishes `H`'s day-`f n` expectation after `f n`. The joint legibility
`hjoint` is therefore a (c) about the real sequence `violW`, inhabited only at `A = H`
(`A.v3Theorem1_paper_self`: N+ for the package, N− for content).

(Angle A's declarations are referenced fully qualified, `_root_.Cleanroom.Fa.FaForcingTrader.A.…`,
wherever a theorem binds a market named `A`: the variable would otherwise shadow the namespace.)
-/
namespace Cleanroom.Fa.FaForcingTrader

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Filter Topology

export A (v3Theorem1_summable v3Theorem1_fixed)

/-- **T3 (headline, of record). v3 Theorem 1, violation-weight form, under joint legibility.** For
inductors `A`, `H`, a quote package, a window-disjoint schedule `d` for `f`, rationals `t`,
`ε > 0`, `δ > 0`, and the violation weight
`violW_n = 1[n ∈ im d] · Ind_δ(𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) > t) · Ind_δ(𝔼^H_n(X_n) < t − ε)` legible on
*both* markets (`hjoint`, v3's (A1) in the only form FAF can state): the mass `∑_{i≤n} violW_i`
does **not** diverge. Angle A's theorem, restated: `theoremSS_limitPoint_general` on the
`A`-legible copy of `violW`, which on its support has `a_n > t` and `h_n < t − ε`, so its average
bias is `≥ ε` wherever the mass is positive — contradicting the limit point `0`.
Scope: **two-way** (partial: over the OPEN pair — li-coupled-pair's `twoWayPair_exists` — and K3:
even that pair does not supply `hjoint`). e.d. family `X`. Schedule: window-disjoint
`DeferralFunction`. Grade: limit point on the `A` side, full limit on the `H` side; the
conclusion is finiteness.
The LI content enters only through FAF's criterion: no `hbias`, `hbdd`, `hNoExp`, `hMirror`.
`hjoint` is about the *real sequence* `violW`, never about the `A`-denotation of a feature pricing
`H`'s sentences on `A`'s market; orientation by `dsWeight_pos_imp` (K7); `0 < δ` in the statement.
Content region: for `t − ε ≤ 0` the lower ramp is empty on `h ∈ [0,1]`, `violW ≡ 0`, `hjoint`
holds on any two markets (the constant-`0` feature) and the conclusion is trivial (audit r1
adversarial P4); the content lives in `0 < ε < t < 1`.
Source: root-fa-019 (the complete proof); lean-deference-042; root-deference-050 (the v6 original); root-fa-2-004; [[fa-positive-results-corrected-v3]] §3
Kind: C
Fidelity: variant: joint legibility of the real violation sequence on each market's own `PGenerableWeighting` class (`hjoint`) in place of v3's joint clearing (K2, K3) — no ledger object appears in the package; schedules are `DeferralFunction`s (K1)
Hyps: (a) `hcode`, `hworldA`, `hworldH`, `hval`, `hwd`, `hδ`, `hε`; (c) `pkg.reflected` (Σ₁-completeness of `Γ_A` about `H` — li-quote-lane); (c) `hjoint` (joint legibility, v3's (A1); no two-market inhabitant, K3). -/
theorem v3Theorem1_of_jointLegible {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    {d : DeferralFunction} (hwd : WindowDisjoint f d) (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (hε : 0 < ε)
    (hjoint : LegibleOn A (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ) ∧
      LegibleOn H (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ)) :
    ¬ Tendsto (prefixSum (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ))
      atTop atTop :=
  _root_.Cleanroom.Fa.FaForcingTrader.A.v3Theorem1_of_jointLegible
    pkg hcode hworldA hworldH hval hwd t ε hδ hε hjoint

end Cleanroom.Fa.FaForcingTrader
