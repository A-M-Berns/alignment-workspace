import Cleanroom.Trust.LegitLiRegister.Defs
import Cleanroom.Li.LiDiagonal.Defs
import Cleanroom.Deference.DefTrackingPin.Atoms
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Construction.Quotation.DeferralFibre

/-!
# `legit-li-register` · Diagonal: Claim 1 — the quote-referencing diagonal is quantitatively
illegitimate (Target 4)

[[legitimacy-theory-v1]] §3 Claim 1 (root-fa-042): on the 2a family `g_n ↔ (a_n ≤ ½)`, "the
coupled verdict is a function of the quote, so the sealed and coupled runs are driven apart by
construction — `d_n ≥ ½ − o(1)`"; §8 item 1 calls it "the cheapest test of the whole framing".

Over FAF, with the diagonal contract `gDiag n = ∼⌜α_{0,n} > ½⌝` (`li-diagonal`'s definition of
record, relative to the advised reasoner's **own** ledger item `0`, the quote `a n`), stated over
the relaxed carrier `FrozenSystemL` (the contract is a ledger literal, which `FrozenSystem`
forbids):

* **The arithmetic core** (L, real numbers): `|𝟙[a ≤ ½] − a| ≥ ½` for every `a`, hence
  `½ − δ ≤ |𝟙[a_n ≤ ½] − Y_n|` eventually whenever `a ≈ₙ Y`. The inventory's suspicion
  (root-fa-042: "the bound needs the sealed sibling's credence to stay bounded away from the
  coupled verdict") is misdirected: the sibling's price is irrelevant, only `a ≈ₙ Y` (T1) and the
  coupled verdict enter. (`def-obstruction`, which owns "no exact quote", has not been launched;
  the one-liner is proved here as infrastructure and cross-referenced for consolidation.)
* **The coupled verdict is the decided literal — under an `H`-side read certificate**
  (`hplus_horizon_gDiag_ofPattern`, C): past the quote's publication day every completed-theory
  world of `Hplus`'s process holds `⌜α_{0,n} > ½⌝` iff `½ < a n` (`li-quote-lane`'s
  `ledgerLuv_decided_by`, through `def-tracking-pin`'s `ledgerLuv_gt_holds_iff`; ties → true for
  the literal, so `gDiag` is true at `a n = ½`, disclosure (β)), so the payout of `gDiag n` is
  `𝟙[a n ≤ ½]`; provability induction for `Hplus` on the two polarity subfamilies of the
  reindexed family then gives the horizon price — **if those subfamilies are e.c.** (`hpat₁`,
  `hpat₀`). As in `Idle.lean`, the certificate is load-bearing: the pattern `{n | a n ≤ ½}` is a
  feature of `A`'s market, not of `Hplus`'s, and without the certificate the advised reasoner's
  horizon price of the decided literal is not forced (the mandate's "from T1 alone" is therefore
  not available; findings F3).
* **Claim 1** (`defect_ge_half_diagonal`, C): `∀ δ > 0, ∀ᶠ n, ½ − δ ≤ d_n` — T1 over the relaxed
  carrier (`trackingL`, `hz`) composed with the two facts above. Two-way, with no inhabitant with
  a diagonal contract in the run: `partial: over li-coupled-pair's sealedSystem_exists`.

The "second half" of Claim 1 ("corrupt ⊋ inadmissible"): inadmissible ⟹ illegitimate is this
theorem on the diagonal — one instance, not the general arrow; the converse failure is the finite
steering witness `LegitFiniteDefect.Trace.S2` (`d = ½` with perfect apparent tracking, cited in
the report) and, at the LI register, Target 15 (OPEN).
-/

namespace Cleanroom.Trust.LegitLiRegister

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefFrozenSibling Cleanroom.Li.LiDiagonal
  Cleanroom.Deference.DefTrackingPin
open Filter Topology

/-! ## A. The arithmetic core -/

/-- **`|𝟙[a ≤ ½] − a| ≥ ½` for every real `a`.** The whole quantitative content of Claim 1 given
T1: a `{0,1}` verdict that flips exactly at `½` is never closer than `½` to the number it reads.
(`def-obstruction`'s "no exact quote" one-liner, proved here since that package is not launched.)
Source: [[legitimacy-theory-v1]] §3 (Claim 1); root-fa-042; mandate Target 4 (arithmetic core)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem abs_indicator_half_sub_ge_half (a : ℝ) :
    (1 / 2 : ℝ) ≤ |(if a ≤ 1 / 2 then (1 : ℝ) else 0) - a| := by
  split_ifs with h
  · rw [abs_of_nonneg (by linarith)]
    linarith
  · have h' : 1 / 2 < a := not_le.1 h
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- The `½` threshold commutes with the cast `ℚ → ℝ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rat_le_half_iff (q : ℚ) : ((q : ℝ) ≤ 1 / 2) ↔ (q ≤ 1 / 2) := by
  rw [show (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) by norm_num]
  exact Rat.cast_le

/-- **Eventually `½ − δ ≤ |𝟙[a_n ≤ ½] − Y_n|` whenever `a ≈ₙ Y`** (the triangle inequality on the
previous lemma). Real sequences only; the headline is its instance over the carrier.
Source: [[legitimacy-theory-v1]] §3 (Claim 1, "`liminf d_n ≥ ½`"); mandate Target 4
Kind: L
Fidelity: exact (the eventual `½ − δ` form of `liminf ≥ ½`)
Hyps: (a) none -/
theorem eventually_half_sub_le_of_asympEq {a Y : ℕ → ℝ} (h : a ≈ₙ Y) :
    ∀ δ > 0, ∀ᶠ n in atTop,
      (1 / 2 : ℝ) - δ ≤ |(if a n ≤ 1 / 2 then (1 : ℝ) else 0) - Y n| := by
  intro δ hδ
  filter_upwards [asympEq_iff_eventuallyWithin.1 h δ hδ] with n hn
  have h1 := abs_indicator_half_sub_ge_half (a n)
  have h2 : |(if a n ≤ 1 / 2 then (1 : ℝ) else 0) - a n| ≤
      |(if a n ≤ 1 / 2 then (1 : ℝ) else 0) - Y n| + |Y n - a n| := abs_sub_le _ _ _
  rw [abs_sub_comm (Y n)] at h2
  linarith

/-! ## B. The coupled verdict is the decided literal -/

/-- The reindexed diagonal family on the days the quote is at most `½`: `gDiag (F⁻¹ m)` at image
days with `a (F⁻¹ m) ≤ ½`, the filler `⊤` elsewhere.
Source: mandate Target 4 (the coupled verdict); `Idle.lean` (the `H`-side pattern shape)
Kind: D
Fidelity: n/a -/
def diagFamilyLe (S : FrozenSystemL) (m : ℕ) : Sentence :=
  if deferralImageFlag S.F m = 1 ∧ S.a (deferralPreimage S.F m) ≤ 1 / 2 then
    gDiag (deferralPreimage S.F m) else ⊤

/-- The reindexed diagonal family on the days the quote exceeds `½`, with the refutable filler.
Source: as `diagFamilyLe`
Kind: D
Fidelity: n/a -/
def diagFamilyGt (S : FrozenSystemL) (m : ℕ) : Sentence :=
  if deferralImageFlag S.F m = 1 ∧ 1 / 2 < S.a (deferralPreimage S.F m) then
    gDiag (deferralPreimage S.F m) else ∼(⊤ : Sentence)

/-- In every completed-theory world of the advised reasoner's process, `gDiag n` holds iff
`a n ≤ ½` (`ledgerLuv_gt_holds_iff` at item `0`, the quote; ties → true).
Source: `li-quote-lane` `ledgerLuv_decided_by` (disclosure (β)); mandate Target 4
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem holds_gDiag_iff (S : FrozenSystemL) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory S.processH) : v.Holds (gDiag n) ↔ S.a n ≤ 1 / 2 := by
  rw [gDiag_eq, PCWorld.holds_neg,
    ledgerLuv_gt_holds_iff S.base (frozenTable S.a S.Y) (frozenSched S.eq S.eY) 0 n (1 / 2) v hv,
    frozenTable_zero, not_lt]

/-- **The coupled verdict at the horizon is the decided literal, under an `H`-side read
certificate**: `Hplus (F n) (gDiag n) ≈ₙ 𝟙[a n ≤ ½]`. The literal's payout in every
completed-theory world is the indicator (`holds_gDiag_iff`); FAF's provability induction for
`Hplus` on the two e.c. polarity subfamilies (`hpat₁`, `hpat₀`) gives the horizon price; read
back at `m = F n` (`hinj`). **Not taken as a hypothesis** (that would make the headline a
squeeze); **not free either**: the certificate is the read-cheap clause of checklist row 4 for
the diagonal literal, and the polarity pattern `{n | a n ≤ ½}` is `A`'s, not `Hplus`'s (findings
F3). Two-way (`A` reads the sibling's verdict on a sentence that reads `A`'s quote):
`partial: over li-coupled-pair's sealedSystem_exists`.
Source: mandate Target 4 (`hplus_horizon_gDiag`), at the grade it has; root-fa-042
Kind: C
Fidelity: variant: polarity pattern as e.c. sentence families (plain trader class); ties → true
Hyps: (c) `hpat₁`, `hpat₀` — e.c. certificates of the pattern `{n | a n ≤ ½}` reindexed along `F` (checklist row 4); all else (a) -/
theorem hplus_horizon_gDiag_ofPattern (S : FrozenSystemL) (hinj : Function.Injective S.F.f)
    (hpat₁ : MachineSentenceCodes (diagFamilyLe S))
    (hpat₀ : MachineSentenceCodes (diagFamilyGt S)) :
    (fun n => S.Hplus (S.F.f n) (gDiag n)) ≈ₙ
      (fun n => if S.a n ≤ 1 / 2 then (1 : ℝ) else 0) := by
  haveI := S.Hplus_inductor
  have h1 := lic_provind_true S.Hplus S.processH _ hpat₁ (fun m v hv => by
    unfold diagFamilyLe
    by_cases hc : deferralImageFlag S.F m = 1 ∧ S.a (deferralPreimage S.F m) ≤ 1 / 2
    · rw [if_pos hc]
      exact (holds_gDiag_iff S _ v hv).2 hc.2
    · rw [if_neg hc]
      exact PCWorld.holds_top v) S.hworldH
  have h0 := lic_provind_false S.Hplus S.processH _ hpat₀ (fun m v hv => by
    unfold diagFamilyGt
    by_cases hc : deferralImageFlag S.F m = 1 ∧ 1 / 2 < S.a (deferralPreimage S.F m)
    · rw [if_pos hc, PCWorld.holds_neg, holds_gDiag_iff S _ v hv, not_le]
      exact hc.2
    · rw [if_neg hc, PCWorld.holds_neg, PCWorld.holds_neg, not_not]
      exact PCWorld.holds_top v) S.hworldH
  rw [asympEq_iff_eventuallyWithin]
  intro δ hδ
  have hev : ∀ᶠ m in atTop, |S.Hplus m (diagFamilyLe S m) - 1| ≤ δ ∧
      |S.Hplus m (diagFamilyGt S m) - 0| ≤ δ := by
    filter_upwards [asympEq_iff_eventuallyWithin.1 h1 δ hδ,
      asympEq_iff_eventuallyWithin.1 h0 δ hδ] with m hm1 hm0
    exact ⟨hm1, hm0⟩
  filter_upwards [S.F.tendsto_atTop.eventually hev] with n hn
  have hpre : deferralPreimage S.F (S.F.f n) = n := deferralPreimage_at S.F hinj n
  by_cases ha : S.a n ≤ 1 / 2
  · have hfam : diagFamilyLe S (S.F.f n) = gDiag n := by
      unfold diagFamilyLe
      rw [hpre, if_pos ⟨deferralImageFlag_at S.F n, ha⟩]
    rw [hfam] at hn
    rw [if_pos ha]
    exact hn.1
  · have hfam : diagFamilyGt S (S.F.f n) = gDiag n := by
      unfold diagFamilyGt
      rw [hpre, if_pos ⟨deferralImageFlag_at S.F n, not_le.1 ha⟩]
    rw [hfam] at hn
    rw [if_neg ha]
    exact hn.2

/-! ## C. Claim 1 -/

/-- **Claim 1 — the diagonal is quantitatively illegitimate** (headline): over the relaxed
carrier with the diagonal contract `P^{(n)} = gDiag n = ∼⌜a_n > ½⌝`, for every `δ > 0`,
eventually `½ − δ ≤ d_n` — the eventual form of `liminf d_n ≥ ½`. Composition: T1 over the relaxed
carrier (`trackingL`, `a ≈ₙ Y`, costing `hz`), the coupled verdict `Hplus (F n) (gDiag n) ≈ₙ
𝟙[a n ≤ ½]` (`hplus_horizon_gDiag_ofPattern`, costing the `H`-side read certificate), and the
arithmetic core. The sibling's price enters only through `Y` and is otherwise unconstrained (the
inventory's suspicion is answered: no bound on it is needed). **Two-way**: `A` reads the sibling's
verdict on a sentence that reads `A`'s quote; no inhabitant of `FrozenSystemL` with a diagonal
contract exists in the run — `partial: over li-coupled-pair's sealedSystem_exists`. The
`hz`-free variant through a polarity certificate for `A` is not available: the polarity is `A`'s
own threshold, the thing that is not e.c.; so T1's `hz` is load-bearing for Claim 1 (and the
`H`-side certificate is load-bearing on top of it — the honest cost is both, findings F3).
Inadmissible ⟹ illegitimate on the diagonal is this theorem (one instance, not the general arrow).
On the strength of `hpat` (audit round 1 N7): the certificate asks the pattern `{n | a_n ≤ ½}` of
`A`'s own quotes, reindexed along `F`, to be e.c. — the mandate's own words for the `A`-side are
that this polarity "is the thing not e.c." The package is nonetheless plausibly inhabitable
without contradicting `A_inductor` and `hz`: with the pattern *eventually constant* (say `a_n ≤ ½`
from some day on, so both certificates are `ifZero`s on a threshold ruler), `hz` forces `Y ≈ a`,
and `Y n` is the sibling's price of a literal it never hears, pinned in `(0,1)` by non-dogmatism;
a sibling with `Y n ≈ a_n ≤ ½` and `d_n ≈ |Y_n − 1| ≥ ½` is consistent. No such inhabitant is
built (two-way existence is the dependency's OPEN pair).
Source: [[legitimacy-theory-v1]] §3 Claim 1, §8 item 1 (root-fa-042); 2-013's negative half; 2-041 (ii)
Kind: C
Fidelity: exact for the quantitative half (eventual `½ − δ` for `liminf ≥ ½`); the "2a family" rendered as `gDiag` relative to `Hplus`'s own ledger (not `li-diagonal`'s `DiagonalPair`, whose `A` reads `H` through a `CrossQuotePackage`)
Hyps: (c) `hz` through T1 (checklist row 6); (c) `hpat₁`, `hpat₀` (row 4, read-cheap for the diagonal literal — a strong (c): the pattern is `A`'s threshold); all else (a) -/
theorem defect_ge_half_diagonal (S : FrozenSystemL) (hc : ∀ n, S.contract n = gDiag n)
    (hinj : Function.Injective S.F.f)
    (hpat₁ : MachineSentenceCodes (diagFamilyLe S))
    (hpat₀ : MachineSentenceCodes (diagFamilyGt S))
    (zhat : ℕ → ℚ) (hz : PGenerableRat S.A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0)) :
    ∀ δ > 0, ∀ᶠ n in atTop, (1 / 2 : ℝ) - δ ≤ S.defect n := by
  have ha := S.trackingL zhat hz hlim
  have hH := hplus_horizon_gDiag_ofPattern S hinj hpat₁ hpat₀
  intro δ hδ
  filter_upwards [asympEq_iff_eventuallyWithin.1 ha (δ / 2) (half_pos hδ),
    asympEq_iff_eventuallyWithin.1 hH (δ / 2) (half_pos hδ)] with n hn1 hn2
  unfold FrozenSystemL.defect
  rw [hc]
  set I : ℝ := if S.a n ≤ 1 / 2 then (1 : ℝ) else 0 with hI
  set H : ℝ := S.Hplus (S.F.f n) (gDiag n) with hHdef
  have hcore : (1 / 2 : ℝ) ≤ |I - (S.a n : ℝ)| := by
    rw [hI, if_congr (rat_le_half_iff (S.a n)).symm rfl rfl]
    exact abs_indicator_half_sub_ge_half _
  have h3 : |I - (S.a n : ℝ)| ≤ |I - H| + |H - (S.Y n : ℝ)| + |(S.Y n : ℝ) - S.a n| :=
    calc |I - (S.a n : ℝ)| ≤ |I - (S.Y n : ℝ)| + |(S.Y n : ℝ) - S.a n| := abs_sub_le _ _ _
      _ ≤ (|I - H| + |H - (S.Y n : ℝ)|) + |(S.Y n : ℝ) - S.a n| :=
          add_le_add (abs_sub_le _ _ _) le_rfl
  have e1 : |H - I| = |I - H| := abs_sub_comm _ _
  have e2 : |(S.a n : ℝ) - S.Y n| = |(S.Y n : ℝ) - S.a n| := abs_sub_comm _ _
  have e3 : |(S.Y n : ℝ) - H| = |H - (S.Y n : ℝ)| := abs_sub_comm _ _
  rw [e3]
  linarith

end Cleanroom.Trust.LegitLiRegister
