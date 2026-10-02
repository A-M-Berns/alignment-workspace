import Cleanroom.Fa.FaAdaptiveJoint.Theorem2
import Cleanroom.Fa.FaForcingTrader.Schedule

/-!
# `fa-adaptive-joint` · Witnesses (T5)

[[fa-adaptive-joint-mandate]] T5. (i) T1's N+ witness: on the constant feature `w ≡ 1` with the
lookahead `f n = 2n + 2` (`linearSchedule 0`) the machine fires on days `0, 2, 6, 14, …`
(`2^{k+1} − 2`) and on no odd day — a genuine on/off pattern produced by `open` (day `1` is quiet
*because* piece `0` is open), through the mass-conservation law of the saturated ramp
(`FireRec.bounce_of_injective`: `fire (f m) = fire m`); and the price-reading instance on the
quote ramp. (ii) T3's full package at the same market `A = H`: joint legibility is discharged for
*every* inductor and e.c. families (`legibleOn_viol_self`: both ramps are ramps of same-market
quotes), so `v3Theorem2_self_of_bridge` has no (c) left but `pkg.reflected` — N+ for the package,
N− for the content (same market). The paper-market inhabitant of `pkg`/`hcode`/`hworld` is the
dependency's `theoremSS_paper_self_top` data, compiler-facing and not imported here.
(iii) T2's instance (a firing sequence that is summable and non-zero) and T4's: a one-position
weighting positive on *every* day (`w ≡ ¾`, `θ = 1`), hence supported on no schedule — so the
OPEN `adaptiveBridge` is not a restatement of `hSideBridge`.
-/

namespace Cleanroom.Fa.FaAdaptiveJoint

open LogicalInduction Cleanroom.Fa.FaForcingTrader Cleanroom.Fa.FaTheoremA
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice
  Filter Topology

/-! ## A. The saturated ramp: mass conservation and the bounce law -/

/-- When `w_n ≥ θ` on every day the ramp is `1`, and `fire n + open n = 1`: the unit of mass is
always either flat or open.
Source: [[fa-adaptive-joint-mandate]] § T5 (i)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem FireRec.add_openMass_eq_one {f : ℕ → ℕ} {θ : ℚ} (hθ : 0 < θ) {w u : ℕ → ℝ}
    (h : FireRec f θ w u) (hw : ∀ n, (θ : ℝ) ≤ w n) (n : ℕ) : u n + openMass f u n = 1 := by
  rw [h n, ctsInd_eq_one_of_le_sub _ _ _ (half_pos hθ) (by push_cast; linarith [hw n])]
  ring

/-- **The bounce law of the saturated machine**: `fire 0 = 1`, and `fire (n+1)` is exactly the mass
of the pieces closing on day `n+1` (from the additive update and mass conservation).
Source: [[fa-adaptive-joint-mandate]] § T5 (i)
Kind: L
Fidelity: n/a
Hyps: (a) `hf` -/
theorem FireRec.succ_eq_closing {f : ℕ → ℕ} (hf : ∀ n, n < f n) {θ : ℚ} (hθ : 0 < θ)
    {w u : ℕ → ℝ} (h : FireRec f θ w u) (hw : ∀ n, (θ : ℝ) ≤ w n) (n : ℕ) :
    u (n + 1) = ∑ m ∈ Finset.range (n + 1), (if f m = n + 1 then u m else 0) := by
  have h1 := h.add_openMass_eq_one hθ hw (n + 1)
  have h2 := h.add_openMass_eq_one hθ hw n
  have h3 := openMass_succ f u n (hf n)
  linarith

/-- `fire 0 = 1` for the saturated machine.
Source: [[fa-adaptive-joint-mandate]] § T5 (i)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem FireRec.zero_eq_one {f : ℕ → ℕ} {θ : ℚ} (hθ : 0 < θ) {w u : ℕ → ℝ} (h : FireRec f θ w u)
    (hw : ∀ n, (θ : ℝ) ≤ w n) : u 0 = 1 := by
  have := h.add_openMass_eq_one hθ hw 0
  simp [openMass] at this
  exact this

/-- For an injective lookahead the mass bounces along `f`: `fire (f m) = fire m`.
Source: [[fa-adaptive-joint-mandate]] § T5 (i)
Kind: L
Fidelity: n/a
Hyps: (a) `hf`, `hinj` -/
theorem FireRec.bounce_of_injective {f : ℕ → ℕ} (hf : ∀ n, n < f n) (hinj : Function.Injective f)
    {θ : ℚ} (hθ : 0 < θ) {w u : ℕ → ℝ} (h : FireRec f θ w u) (hw : ∀ n, (θ : ℝ) ≤ w n) (m : ℕ) :
    u (f m) = u m := by
  obtain ⟨n, hn⟩ : ∃ n, f m = n + 1 := ⟨f m - 1, by have := hf m; omega⟩
  rw [hn, h.succ_eq_closing hf hθ hw n]
  have hmem : m ∈ Finset.range (n + 1) := Finset.mem_range.2 (by have := hf m; omega)
  rw [Finset.sum_eq_single m]
  · rw [if_pos hn]
  · intro b _ hb
    rw [if_neg (fun hfb => hb (hinj (hfb.trans hn.symm)))]
  · intro hm
    exact absurd hmem hm

/-- A day `n + 1` on which no piece closes is quiet: `fire (n+1) = 0`.
Source: [[fa-adaptive-joint-mandate]] § T5 (i)
Kind: L
Fidelity: n/a
Hyps: (a) `hf` -/
theorem FireRec.succ_eq_zero_of_no_closing {f : ℕ → ℕ} (hf : ∀ n, n < f n) {θ : ℚ} (hθ : 0 < θ)
    {w u : ℕ → ℝ} (h : FireRec f θ w u) (hw : ∀ n, (θ : ℝ) ≤ w n) (n : ℕ)
    (hno : ∀ m, f m ≠ n + 1) : u (n + 1) = 0 := by
  rw [h.succ_eq_closing hf hθ hw n]
  exact Finset.sum_eq_zero (fun m _ => if_neg (hno m))

/-! ## B. T1's N+ witness: `w ≡ 1`, `f n = 2n + 2` -/

/-- The lookahead `f n = 2n + 2` (the dependency's `linearSchedule 0`) as a plain function.
Source: [[fa-adaptive-joint-mandate]] § T5 (i)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem linearSchedule_zero_apply (n : ℕ) : (linearSchedule 0).f n = 2 * n + 2 := by
  rw [linearSchedule_apply]

/-- **T5 (i) — T1's N+ witness, the firing pattern.** With `w ≡ 1`, `θ = 1`, `f n = 2n + 2`, the
firing sequence is `1` on day `0`, `0` on day `1` (piece `0` is open), `1` on every day
`2^{k+1} − 2` (`0, 2, 6, 14, …`: the unit of mass bounces along `f`), and `0` on every odd day.
Non-constant, fires infinitely often, and exercises `open`.
Source: [[fa-adaptive-joint-mandate]] § T5 (i) ("a genuine on/off pattern with reopenings")
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem fireSeq_pattern :
    let u := fireSeq (fun n => 2 * n + 2) 1 (fun _ => (1 : ℝ))
    u 0 = 1 ∧ u 1 = 0 ∧ (∀ k, u (2 ^ (k + 1) - 2) = 1) ∧ ∀ j, u (2 * j + 1) = 0 := by
  intro u
  have hf : ∀ n, n < 2 * n + 2 := fun n => by omega
  have hinj : Function.Injective (fun n => 2 * n + 2) := fun a b hab => by
    simp only at hab; omega
  have hθ : (0 : ℚ) < 1 := one_pos
  have hw : ∀ n : ℕ, ((1 : ℚ) : ℝ) ≤ (fun _ : ℕ => (1 : ℝ)) n := fun _ => by norm_num
  have hrec : FireRec (fun n => 2 * n + 2) 1 (fun _ => (1 : ℝ)) u := fireSeq_fireRec _ _ _
  have h0 : u 0 = 1 := hrec.zero_eq_one hθ hw
  refine ⟨h0, ?_, ?_, ?_⟩
  · exact hrec.succ_eq_zero_of_no_closing hf hθ hw 0 (fun m => by omega)
  · intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
        have hpow : 2 ^ (k + 1 + 1) - 2 = 2 * (2 ^ (k + 1) - 2) + 2 := by
          have : 2 ≤ 2 ^ (k + 1) := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          rw [pow_succ]
          omega
        rw [hpow]
        exact (hrec.bounce_of_injective hf hinj hθ hw (2 ^ (k + 1) - 2)).trans ih
  · intro j
    exact hrec.succ_eq_zero_of_no_closing hf hθ hw (2 * j) (fun m => by omega)

/-- **T5 (i) as a feature**: `adaptFire (const 1) (linearSchedule 0) 1` is a `PGenerableWeighting`
(T1) whose denotation on *every* market is the pattern above.
Source: [[fa-adaptive-joint-mandate]] § T5 (i)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem adaptFire_const_one_pattern (V : History) :
    PGenerableWeighting (adaptFire (fun _ => EF.const 1) (linearSchedule 0) 1) ∧
      (fun n => (adaptFire (fun _ => EF.const 1) (linearSchedule 0) 1 n).denote V) =
        fireSeq (fun n => 2 * n + 2) 1 (fun _ => (1 : ℝ)) := by
  refine ⟨adaptFire_pgenerable (pgenerableWeighting_const 1) _ _, ?_⟩
  funext n
  rw [adaptFire_denote_fireSeq (pgenerableWeighting_const 1) _ one_pos]
  have hfun : (linearSchedule 0).f = fun n => 2 * n + 2 := funext linearSchedule_zero_apply
  rw [hfun]
  congr 1
  funext m
  simp

/-- **T5 (i), the price-reading instance**: the machine on the quote ramp
`Ind_δ(𝔼^A_n(⌜𝔼^H_{f n}(X_n)⌝) > t)` of an e.c. family is a legal feature progression (T1 on
`quoteRampAbove_pgenerable`). Its firing pattern depends on the market and is not computed here
(N− for the pattern, N+ for the reading: the feature reads prices).
Source: [[fa-adaptive-joint-mandate]] § T5 (i) ("the price-reading instance")
Kind: N+
Fidelity: n/a
Hyps: (a) `hY` -/
theorem adaptFire_quoteRamp_pgenerable (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y)
    (t δ : ℚ) (f : DeferralFunction) (θ : ℚ) :
    PGenerableWeighting (adaptFire (quoteRampAbove Y t δ) f θ) :=
  adaptFire_pgenerable (quoteRampAbove_pgenerable Y hY t δ) f θ

/-! ## C. T2's and T4's real-sequence instances -/

/-- **T5 (iii) — T2's instance**: `w = 1, 1, 1, 0, 0, …` with `f n = 2n + 2`, `θ = 1`: the firing
sequence is `1, 0, 1, 0, 0, …` (day `1` quiet because piece `0` is open, day `2` firing because
piece `0` closed at `2` and piece `1` fired `0`) — summable, not identically zero, and `w_n < θ`
from day `3` on. Repair round 1 added `u 1 = 0 ∧ u 2 = 1` to the statement (audit r1 N8).
Source: [[fa-adaptive-joint-mandate]] § T5 (iii)
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem fireSeq_summable_instance :
    let w : ℕ → ℝ := fun n => if n < 3 then 1 else 0
    let u := fireSeq (fun n => 2 * n + 2) 1 w
    Summable u ∧ u 0 = 1 ∧ u 1 = 0 ∧ u 2 = 1 ∧ (∀ n, 3 ≤ n → u n = 0) ∧
      ∀ᶠ n in atTop, w n < (1 : ℚ) := by
  intro w u
  have hrec : FireRec (fun n => 2 * n + 2) 1 w u := fireSeq_fireRec _ _ _
  have hzero : ∀ n, 3 ≤ n → u n = 0 := by
    intro n hn
    rw [hrec n]
    have hw : w n = 0 := by simp [w, show ¬ n < 3 by omega]
    rw [hw, ctsInd_eq_zero_of_le _ _ _ (by norm_num) (by norm_num), mul_zero]
  have hu0 : u 0 = 1 := by
    rw [hrec 0]
    simp [openMass, w]
    exact ctsInd_eq_one_of_le_sub _ _ _ (by norm_num) (by norm_num)
  have hu1 : u 1 = 0 := by
    rw [hrec 1]
    simp [openMass, hu0]
  have hu2 : u 2 = 1 := by
    rw [hrec 2]
    simp [openMass, Finset.sum_range_succ, hu1, w]
    exact ctsInd_eq_one_of_le_sub _ _ _ (by norm_num) (by norm_num)
  refine ⟨?_, hu0, hu1, hu2, hzero, ?_⟩
  · exact summable_of_ne_finset_zero (s := Finset.range 3)
      (fun n hn => hzero n (by simpa [Finset.mem_range, not_lt] using hn))
  · filter_upwards [eventually_ge_atTop 3] with n hn
    simp [w, show ¬ n < 3 by omega]

/-- **T5 (iii) — T4's instance: a one-position weighting positive on every day**, hence supported
on no schedule (so `AdaptiveBridgeHolds` is not the dependency's `hSideBridge`): `w ≡ ¾`, `θ = 1`,
`f n = 2n + 2` gives the ramp `½` and `fire n = (1 − open n)/2 > 0` since `open n < 1` on every
day. The no-schedule clause is in the statement (repair round 1, audit r1 N9): every
`DeferralFunction d` has `d k > k ≥ 0`, so day `0`, where `u 0 > 0`, is in no schedule's image.
Source: [[fa-adaptive-joint-mandate]] § T5 (iii) ("a `OnePosition` weighting that is *not* schedule-supported")
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem onePosition_positive_everywhere :
    ∃ u : ℕ → ℝ, OnePosition (linearSchedule 0) u ∧ (∀ n, 0 < u n) ∧
      ∀ d : DeferralFunction, ¬ (∀ n, u n ≠ 0 → ∃ k, d.f k = n) := by
  set f : ℕ → ℕ := fun n => 2 * n + 2 with hfdef
  set u := fireSeq f 1 (fun _ => (3 / 4 : ℝ)) with hu
  have hrec : FireRec f 1 (fun _ => (3 / 4 : ℝ)) u := fireSeq_fireRec _ _ _
  have hramp : ctsInd (1 / 2) (3 / 4 : ℝ) (((1 : ℚ) / 2 : ℚ) : ℝ) = 1 / 2 := by
    unfold ctsInd
    norm_num
  have hval : ∀ n, u n = (1 - openMass f u n) / 2 := by
    intro n
    rw [hrec n]
    simp only [hramp]
    ring
  have hnn : ∀ n, 0 ≤ u n := fun n => (hrec.nonneg_openMass_le_one n).1
  have hopen : ∀ n, openMass f u n < 1 := by
    intro n
    induction n with
    | zero => simp [openMass]
    | succ n ih =>
        have h1 := openMass_succ f u n (by show n < 2 * n + 2; omega)
        have h2 : 0 ≤ ∑ m ∈ Finset.range (n + 1), (if f m = n + 1 then u m else 0) :=
          Finset.sum_nonneg (fun m _ => by split_ifs <;> [exact hnn m; exact le_rfl])
        have h3 := hval n
        linarith
  have hpos : ∀ n, 0 < u n := fun n => by
    rw [hval n]
    linarith [hopen n]
  refine ⟨u, ?_, hpos, fun d hd => ?_⟩
  · have hfun : (linearSchedule 0).f = f := funext linearSchedule_zero_apply
    show ∀ n, 0 ≤ u n ∧ openMass (linearSchedule 0).f u n ≤ 1
    rw [hfun]
    exact hrec.nonneg_openMass_le_one
  · obtain ⟨k, hk⟩ := hd 0 (hpos 0).ne'
    have := d.lt k
    omega

/-! ## D. T3's package at the same market -/

/-- **Joint legibility holds at the same market, for every inductor and e.c. families** (the
mandate's (ii)): on `A = H` the violation weight `Ind_δ(𝔼^A_n(Y_n) > t) · Ind_δ(𝔼^A_n(X_n) < t − ε)`
is a product of ramps of two same-market quotes, legible by `legibleOn_quote_self` and the
closure lemmas of the dependency.
Source: [[fa-adaptive-joint-mandate]] § T5 (ii); `fa-forcing-trader` `v3Theorem1_paper_self`
Kind: N+
Fidelity: n/a (the (c) `hjoint` discharged at `A = H`)
Hyps: (a) `hX`, `hY`, `hδ` -/
theorem legibleOn_viol_self {A : History} {X Y : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    (hY : LUV.MachineThresholdCodeSeq Y) (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ) :
    LegibleOn A (viol (fun n => (X n).expect A n) (quoteSeq Y A) t ε δ) := by
  have h1 : LegibleOn A (quoteSeq Y A) := legibleOn_quote_self Y hY A
  have h2 : LegibleOn A (quoteSeq X A) := legibleOn_quote_self X hX A
  refine ((h1.rampAbove t hδ).mul (h2.rampBelow (t - ε) hδ)).congr (fun n => ?_)
  simp only [viol, dsWeight, rampAbove, rampBelow, quoteSeq]
  push_cast
  rfl

/-- **T5 (ii) — T3's package inhabited at the same market `A = H`**: Theorem 2 with every (c) but
`pkg.reflected` discharged. N+ for the hypothesis package (both legibility clauses are theorems
here), N− for the content (one inductor pricing both families; the realized value and the quote
are the same market's expectations, so there is no cross-market deference being tested). The
paper-market inhabitant of `pkg`, `hcode`, `hworld`, `hval` (`X ≡ 𝟙(⊤)`, `t + δ < 1`) is the
dependency's `theoremSS_paper_self_top` data, in its compiler-facing `Witnesses.lean`, not
imported here (mandate: nothing here imports the compiler).
Source: [[fa-adaptive-joint-mandate]] § T5 (ii)
Kind: N+
Fidelity: n/a
Hyps: (a) `hcode`, `hworldA`, `hval`, `hδ`, `hε`; (c) `pkg.reflected`; `hbridge` (T4, OPEN). -/
theorem v3Theorem2_self_of_bridge {A : History} {DPA : DeductiveProcess} [IsLogicalInductor A DPA]
    {f : DeferralFunction} {X Y : ℕ → LUV} (pkg : CrossQuotePackage A DPA f X Y)
    (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPA → ∃ x : ℝ, v.ValuesAt (X n) x)
    (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ) (hε : 0 < ε) (hbridge : AdaptiveBridgeHolds A f X) :
    Tendsto (viol (fun n => (X n).expect A n) (quoteSeq Y A) t ε δ) atTop (𝓝 0) :=
  v3Theorem2_of_bridge pkg hcode hworldA hworldA hval t ε hδ hε
    ⟨legibleOn_viol_self hcode pkg.quote_codes t ε hδ,
      legibleOn_viol_self hcode pkg.quote_codes t ε hδ⟩ hbridge

end Cleanroom.Fa.FaAdaptiveJoint
