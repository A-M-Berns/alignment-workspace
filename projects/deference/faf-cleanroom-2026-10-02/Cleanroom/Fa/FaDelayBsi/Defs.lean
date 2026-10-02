import Cleanroom.Fa.FaTheoremA.Defs
import Cleanroom.Found.LiAsympCalc.Ramp
import Cleanroom.Found.LiAsympCalc.Compactness
import LogicalInduction.Properties.SelfTrust
import LogicalInduction.Properties.Calibration
import LogicalInduction.Framework.Expectations

/-!
# `fa-delay-bsi` · Definitions of record

The objects of the delay/BSI package ([[fa-delay-bsi-mandate]] § Definitions of record):

* `violWeight`, `frozenWeight` — BSI §1's per-day violation weight and §5's frozen-credence
  weight, as real functions of the day's quote and credence (FAF's `ctsInd`);
* `FreezeSchedule`, `blockOf`, `ClosesWithinBlocks`, `withinFreezeUpdate` — the block structure
  and the human's within-freeze update mass (sequence-level / `LUV.expect`-level; no FAF object
  for a "freeze" exists);
* `DeckTrustQuote`, `DeckTT`, `DeckTTConst` — the deck's Total Trust with the expert *inside*
  the gate ([[delay-program]] §5, root-fa-034), for every reflecting LUV pair and (in `DeckTT`)
  the full generable threshold family; **no `affine` field** (that is FAF's certificate, not
  part of the notion);
* `accelerator` — the bridge: the deck's expert is `fa-theorem-a`'s quote `𝔼^{A'}_n(Y_n)`;
* `AnticipatedQuote` — the "H reads A's *future* quote" package of T8.

Every arithmetic headline carries `0 < δ`, `0 < ε`: `ctsInd` at `δ ≤ 0` is a junk value
(`fa-theorem-a` records `not_divergent_zero_width`).
-/

namespace Cleanroom.Fa.FaDelayBsi

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Cleanroom.Fa.FaTheoremA
open Filter Topology

/-! ## A. The per-day weights -/

/-- **BSI's violation weight at one day**: `w := Ind_δ(a > t) · Ind_δ(c < t − ε)`, as a function
of the day's quote `a` and the live credence `c` (FAF's `ctsInd`; `Ind_δ(c < s)` is
`ctsInd δ s c`). Applied day by day to `quoteSeq Y A n` and `(X (k n)).expect H n`.
Source: BSI §1 line 35 (`w_n := Ind_δ(quote_n > t)·Ind_δ(ℙ^H_n(X_{k(n)}) < t − ε)`; lean-deference-054); [[delay-program]] §5 (FA-format `w_n`)
Kind: D
Fidelity: exact (`li-asymp-calc`'s `dsWeight`/`viol` at one day; `violWeight_eq_viol`)
Hyps: n/a -/
noncomputable def violWeight (t ε δ : ℚ) (a c : ℝ) : ℝ :=
  ctsInd δ a (t : ℝ) * ctsInd δ ((t : ℝ) - ε) c

/-- **BSI's frozen-credence weight at one day**: the live credence replaced by the last-freeze
credence `F`, at margin `ε/2`: `w^{frozen} := Ind_δ(a > t) · Ind_δ(F < t − ε/2)`.
Source: BSI §5 line 96 ("replacing, in `w_n`, the human's current credence with its credence at the last freeze … at margin `ε/2`"; lean-deference-054)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def frozenWeight (t ε δ : ℚ) (a F : ℝ) : ℝ :=
  ctsInd δ a (t : ℝ) * ctsInd δ ((t : ℝ) - ε / 2) F

/-- `violWeight` at a day is `li-asymp-calc`'s `viol` (hence `fa-theorem-a`'s packaging applies).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem violWeight_eq_viol (e a : ℕ → ℝ) (t ε δ : ℚ) (n : ℕ) :
    violWeight t ε δ (a n) (e n) = viol e a t ε δ n := rfl

/-- `0 ≤ violWeight`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem violWeight_nonneg (t ε δ : ℚ) (a c : ℝ) : 0 ≤ violWeight t ε δ a c :=
  mul_nonneg (ctsInd_nonneg _ _ _) (ctsInd_nonneg _ _ _)

/-- `violWeight ≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem violWeight_le_one (t ε δ : ℚ) (a c : ℝ) : violWeight t ε δ a c ≤ 1 :=
  mul_le_one₀ (ctsInd_le_one _ _ _) (ctsInd_nonneg _ _ _) (ctsInd_le_one _ _ _)

/-- `0 ≤ frozenWeight`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem frozenWeight_nonneg (t ε δ : ℚ) (a F : ℝ) : 0 ≤ frozenWeight t ε δ a F :=
  mul_nonneg (ctsInd_nonneg _ _ _) (ctsInd_nonneg _ _ _)

/-- `frozenWeight ≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem frozenWeight_le_one (t ε δ : ℚ) (a F : ℝ) : frozenWeight t ε δ a F ≤ 1 :=
  mul_le_one₀ (ctsInd_le_one _ _ _) (ctsInd_nonneg _ _ _) (ctsInd_le_one _ _ _)

/-- For a positive width the violation weight is positive exactly when the quote is strictly
above `t` and the credence strictly below `t − ε` (the "support" reading of the gate).
Source: BSI §1; root-fa-004 (`ctsInd_pos_iff`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem violWeight_pos_iff {δ : ℚ} (hδ : 0 < δ) (t ε : ℚ) (a c : ℝ) :
    0 < violWeight t ε δ a c ↔ (t : ℝ) < a ∧ c < (t : ℝ) - ε := by
  unfold violWeight
  constructor
  · intro h
    have h1 : 0 < ctsInd δ a (t : ℝ) := by
      rcases (ctsInd_nonneg δ a t).lt_or_eq with h1 | h1
      · exact h1
      · rw [← h1, zero_mul] at h; exact absurd h (lt_irrefl 0)
    have h2 : 0 < ctsInd δ ((t : ℝ) - ε) c := by
      rcases (ctsInd_nonneg δ ((t : ℝ) - ε) c).lt_or_eq with h2 | h2
      · exact h2
      · rw [← h2, mul_zero] at h; exact absurd h (lt_irrefl 0)
    exact ⟨(ctsInd_pos_iff hδ _ _).1 h1, (ctsInd_pos_iff hδ _ _).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact mul_pos ((ctsInd_pos_iff hδ _ _).2 h1) ((ctsInd_pos_iff hδ _ _).2 h2)

/-- For a positive width the violation weight is `1` exactly when both ramps saturate: quote
`≥ t + δ`, credence `≤ t − ε − δ`.
Source: BSI §4 Lemma 4 (the saturation reading); root-fa-004
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem violWeight_eq_one_iff {δ : ℚ} (hδ : 0 < δ) (t ε : ℚ) (a c : ℝ) :
    violWeight t ε δ a c = 1 ↔ (t : ℝ) + δ ≤ a ∧ c ≤ (t : ℝ) - ε - δ := by
  unfold violWeight
  have h1 := ctsInd_mem_Icc δ a (t : ℝ)
  have h2 := ctsInd_mem_Icc δ ((t : ℝ) - ε) c
  constructor
  · intro h
    have hx : ctsInd δ a (t : ℝ) = 1 := by
      by_contra hne
      have hlt : ctsInd δ a (t : ℝ) < 1 := lt_of_le_of_ne h1.2 hne
      have : ctsInd δ a (t : ℝ) * ctsInd δ ((t : ℝ) - ε) c < 1 :=
        calc ctsInd δ a (t : ℝ) * ctsInd δ ((t : ℝ) - ε) c
            ≤ ctsInd δ a (t : ℝ) * 1 := mul_le_mul_of_nonneg_left h2.2 h1.1
          _ < 1 := by linarith
      linarith
    have hy : ctsInd δ ((t : ℝ) - ε) c = 1 := by
      rw [hx, one_mul] at h; exact h
    refine ⟨?_, ?_⟩
    · have := (ctsInd_eq_one_iff hδ _ _).1 hx; linarith
    · have := (ctsInd_eq_one_iff hδ _ _).1 hy; linarith
  · rintro ⟨ha, hc⟩
    rw [(ctsInd_eq_one_iff hδ _ _).2 (by linarith), (ctsInd_eq_one_iff hδ _ _).2 (by linarith),
      one_mul]

/-- For a positive width the frozen weight is `1` exactly when quote `≥ t + δ` and frozen
credence `≤ t − ε/2 − δ`.
Source: BSI §5; root-fa-004
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem frozenWeight_eq_one_iff {δ : ℚ} (hδ : 0 < δ) (t ε : ℚ) (a F : ℝ) :
    frozenWeight t ε δ a F = 1 ↔ (t : ℝ) + δ ≤ a ∧ F ≤ (t : ℝ) - ε / 2 - δ := by
  unfold frozenWeight
  have h1 := ctsInd_mem_Icc δ a (t : ℝ)
  have h2 := ctsInd_mem_Icc δ ((t : ℝ) - ε / 2) F
  constructor
  · intro h
    have hx : ctsInd δ a (t : ℝ) = 1 := by
      by_contra hne
      have hlt : ctsInd δ a (t : ℝ) < 1 := lt_of_le_of_ne h1.2 hne
      have : ctsInd δ a (t : ℝ) * ctsInd δ ((t : ℝ) - ε / 2) F < 1 :=
        calc ctsInd δ a (t : ℝ) * ctsInd δ ((t : ℝ) - ε / 2) F
            ≤ ctsInd δ a (t : ℝ) * 1 := mul_le_mul_of_nonneg_left h2.2 h1.1
          _ < 1 := by linarith
      linarith
    have hy : ctsInd δ ((t : ℝ) - ε / 2) F = 1 := by
      rw [hx, one_mul] at h; exact h
    refine ⟨?_, ?_⟩
    · have := (ctsInd_eq_one_iff hδ _ _).1 hx; linarith
    · have := (ctsInd_eq_one_iff hδ _ _).1 hy; linarith
  · rintro ⟨ha, hF⟩
    rw [(ctsInd_eq_one_iff hδ _ _).2 (by linarith), (ctsInd_eq_one_iff hδ _ _).2 (by linarith),
      one_mul]

/-! ## B. Blocks and the freeze schedule -/

/-- **A freeze schedule**: block boundaries `T 0 = 0 < T 1 < T 2 < …`; block `k` is the days
`[T k, T (k+1))`. BSI's `T_k = 4k` is `bsiSchedule`. Sequence-level: no FAF object models a
freeze (the freeze is a fact about *which* prices a process may carry, `li-quote-lane`'s ledger
schedules), and the arithmetic headlines below need only the block map.
Source: BSI §1 line 27 ("constant block length `L = 4`: `T_k = 4k`, mid-block day `m_k := 4k+2`"); [[delay-program]] §6 T6
Kind: D
Fidelity: exact (any strictly increasing boundary sequence starting at `0`)
Hyps: n/a -/
structure FreezeSchedule where
  /-- The block boundaries. -/
  T : ℕ → ℕ
  /-- Strictly increasing. -/
  strictMono : StrictMono T
  /-- The first block starts on day `0`. -/
  zero : T 0 = 0

namespace FreezeSchedule

/-- `k ≤ T k`: a strictly increasing map on `ℕ` dominates the identity.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem le_T (S : FreezeSchedule) (k : ℕ) : k ≤ S.T k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (S.strictMono (Nat.lt_succ_self k)))

/-- **The block of a day**: the greatest `k ≤ n` with `T k ≤ n` (BSI's `k(n)`).
Source: BSI §1 ("Write `k(n)` for the block containing day `n`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def blockOf (S : FreezeSchedule) (n : ℕ) : ℕ := Nat.findGreatest (fun k => S.T k ≤ n) n

/-- `T (blockOf n) ≤ n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem T_blockOf_le (S : FreezeSchedule) (n : ℕ) : S.T (S.blockOf n) ≤ n :=
  Nat.findGreatest_spec (P := fun k => S.T k ≤ n) (m := 0) (Nat.zero_le n)
    (by show S.T 0 ≤ n; rw [S.zero]; exact Nat.zero_le n)

/-- `n < T (blockOf n + 1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem lt_T_blockOf_succ (S : FreezeSchedule) (n : ℕ) : n < S.T (S.blockOf n + 1) := by
  by_contra h
  rw [not_lt] at h
  have hle : S.blockOf n + 1 ≤ n := (S.le_T _).trans h
  have := Nat.le_findGreatest (P := fun k => S.T k ≤ n) hle h
  unfold blockOf at this
  omega

/-- `blockOf n = k` iff `T k ≤ n < T (k+1)`.
Source: BSI §1 (`k(n)`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem blockOf_eq_iff (S : FreezeSchedule) (n k : ℕ) :
    S.blockOf n = k ↔ S.T k ≤ n ∧ n < S.T (k + 1) := by
  constructor
  · rintro rfl
    exact ⟨S.T_blockOf_le n, S.lt_T_blockOf_succ n⟩
  · rintro ⟨h1, h2⟩
    have hb1 := S.T_blockOf_le n
    have hb2 := S.lt_T_blockOf_succ n
    have hlt1 : k < S.blockOf n + 1 := S.strictMono.lt_iff_lt.1 (lt_of_le_of_lt h1 hb2)
    have hlt2 : S.blockOf n < k + 1 := S.strictMono.lt_iff_lt.1 (lt_of_le_of_lt hb1 h2)
    omega

/-- `blockOf` is monotone.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem blockOf_mono (S : FreezeSchedule) : Monotone S.blockOf := by
  intro m n hmn
  have h1 := S.T_blockOf_le m
  have h2 := S.lt_T_blockOf_succ n
  exact Nat.lt_succ_iff.1 (S.strictMono.lt_iff_lt.1 (lt_of_le_of_lt (h1.trans hmn) h2))

/-- `blockOf (T k) = k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem blockOf_T (S : FreezeSchedule) (k : ℕ) : S.blockOf (S.T k) = k :=
  (S.blockOf_eq_iff _ _).2 ⟨le_rfl, S.strictMono (Nat.lt_succ_self k)⟩

end FreezeSchedule

/-- **BSI's schedule**: `T_k = 4k` (block length `4`).
Source: BSI §1 line 27
Kind: D
Fidelity: exact
Hyps: n/a -/
def bsiSchedule : FreezeSchedule where
  T k := 4 * k
  strictMono := fun a b h => by show 4 * a < 4 * b; omega
  zero := rfl

/-- **BSI's mid-block day** `m_k := 4k + 2`, which lies inside block `k`.
Source: BSI §1 line 27
Kind: D
Fidelity: exact
Hyps: n/a -/
def bsiMid (k : ℕ) : ℕ := 4 * k + 2

/-- BSI's mid-block day lies in block `k`: `blockOf (4k+2) = k`.
Source: BSI §1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bsiSchedule_blockOf_mid (k : ℕ) : bsiSchedule.blockOf (bsiMid k) = k :=
  (bsiSchedule.blockOf_eq_iff _ _).2 ⟨by simp [bsiSchedule, bsiMid], by
    show 4 * k + 2 < 4 * (k + 1); omega⟩

/-- **A schedule closes strictly within blocks**: every round-trip window `[d k, f (d k)]` of the
schedule `d` (lookahead `f`) stays inside the block of `d k`, horizon included. This is the
*strict* reading of BSI's "round-trip windows close within the current block": under the
half-open convention `[T k, T (k+1))`, BSI's own horizon `T_{k(d)+1}` is the first day of the
*next* block and is **excluded** here (`not_closesWithinBlocks_of_horizon_T`; audit r1 adversarial
B2, probe `BsiHorizon.lean`) — BSI's two clauses ("within the current block" and "horizon
`= T_{k(d)+1}`") conflict, which is the off-by-one [[delay-and-visibility]] §3 reports. The
inclusive reading that admits BSI's horizon is `ClosesByBoundary`; `deficit_bound_open` takes
that one. The e.c.-in-the-index reading of "schedule" is empty (root-fa-2-003), so both are
`DeferralFunction`s. `fa-forcing-trader` has `WindowDisjoint f d` (its `Defs.lean`) for the
disjointness half, which this package cannot import — duplication recorded for consolidation.
Source: BSI §5 line 94 ("a window-disjoint schedule `d̄` whose round-trip windows close within the current block (horizon `= T_{k(d)+1}`)"); root-fa-2-003 (i)
Kind: D
Fidelity: variant: deferral-function schedule; the within-block clause only, strict (BSI's horizon `T_{k(d)+1}` excluded; see `ClosesByBoundary`)
Hyps: n/a -/
def ClosesWithinBlocks (S : FreezeSchedule) (f d : DeferralFunction) : Prop :=
  ∀ k, S.blockOf (f.f (d.f k)) = S.blockOf (d.f k)

/-- Under `ClosesWithinBlocks`, every day of the window `[d k, f (d k)]` is in the block of `d k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem ClosesWithinBlocks.blockOf_eq {S : FreezeSchedule} {f d : DeferralFunction}
    (h : ClosesWithinBlocks S f d) (k m : ℕ) (hm1 : d.f k ≤ m) (hm2 : m ≤ f.f (d.f k)) :
    S.blockOf m = S.blockOf (d.f k) :=
  le_antisymm (by rw [← h k]; exact S.blockOf_mono hm2) (S.blockOf_mono hm1)

/-- **A schedule closes by the block boundary** (the inclusive reading): every horizon `f (d k)` is
at most the first day of the next block, `T_{k(d k)+1}`. This is the clause that admits BSI's own
horizon (`closesByBoundary_of_horizon_T`), which the strict `ClosesWithinBlocks` excludes; every
strictly-within-block schedule satisfies it (`ClosesWithinBlocks.toByBoundary`). Strictly before
the horizon the scheduled question is still current (`ClosesByBoundary.blockOf_eq_of_lt`); *at* a
boundary horizon it has retired, and the realized credence `𝔼^H_{T_{k+1}}(X_k)` is the end-of-block
credence of the scheduled question, not `liveCredence` on that day.
Source: BSI §5 line 94 ("horizon `= T_{k(d)+1}`"); BSI §1 line 33 (the quote target `ℙ^H_{T_{k(n)+1}}(X_{k(n)})`); audit r1 adversarial B2 / fidelity non-blocking 2
Kind: D
Fidelity: exact (BSI's horizon clause, inclusive; disjointness is `fa-forcing-trader`'s `WindowDisjoint`)
Hyps: n/a -/
def ClosesByBoundary (S : FreezeSchedule) (f d : DeferralFunction) : Prop :=
  ∀ k, f.f (d.f k) ≤ S.T (S.blockOf (d.f k) + 1)

/-- Strictly within blocks implies by the boundary.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem ClosesWithinBlocks.toByBoundary {S : FreezeSchedule} {f d : DeferralFunction}
    (h : ClosesWithinBlocks S f d) : ClosesByBoundary S f d := fun k => by
  have := S.lt_T_blockOf_succ (f.f (d.f k))
  rw [h k] at this
  exact this.le

/-- BSI's horizon `f (d k) = T_{k(d k)+1}` closes by the boundary.
Source: BSI §5 line 94; BSI §1 line 33
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem closesByBoundary_of_horizon_T {S : FreezeSchedule} {f d : DeferralFunction}
    (hk : ∀ k, f.f (d.f k) = S.T (S.blockOf (d.f k) + 1)) : ClosesByBoundary S f d :=
  fun k => (hk k).le

/-- BSI's horizon on even one scheduled day is **not** strictly within the block: the boundary day
`T (k+1)` is the first day of block `k+1` (`blockOf_T`). The off-by-one of [[delay-and-visibility]]
§3, in the Lean (audit r1 adversarial probe `BsiHorizon.lean`, adopted).
Source: [[delay-and-visibility]] §3 last paragraph (vq-wiki-036); audit r1 adversarial B2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem not_closesWithinBlocks_of_horizon_T {S : FreezeSchedule} {f d : DeferralFunction} (k : ℕ)
    (hk : f.f (d.f k) = S.T (S.blockOf (d.f k) + 1)) : ¬ ClosesWithinBlocks S f d := by
  intro h
  have h1 := h k
  rw [hk, S.blockOf_T] at h1
  omega

/-- Under `ClosesByBoundary`, every day of the window strictly before the horizon is in the block
of `d k`: the scheduled question is current until the horizon.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem ClosesByBoundary.blockOf_eq_of_lt {S : FreezeSchedule} {f d : DeferralFunction}
    (h : ClosesByBoundary S f d) (k m : ℕ) (hm1 : d.f k ≤ m) (hm2 : m < f.f (d.f k)) :
    S.blockOf m = S.blockOf (d.f k) :=
  (S.blockOf_eq_iff _ _).2 ⟨(S.T_blockOf_le _).trans hm1, lt_of_lt_of_le hm2 (h k)⟩

/-- **The human's within-freeze update mass on day `n`** for the current question:
`|𝔼^H_n(X_{k(n)}) − 𝔼^H_{T_{k(n)}}(X_{k(n)})|` — the bounding quantity of the deficit bound T6,
in `H`'s own instrument class.
Source: [[delay-program]] §6 T6 lines 252–260 (root-fa-029 (Bound)); [[delay-and-visibility]] §5 (vq-wiki-039 (b)); BSI §5 (the displacement term)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def withinFreezeUpdate (S : FreezeSchedule) (H : History) (X : ℕ → LUV) (n : ℕ) :
    ℝ :=
  |(X (S.blockOf n)).expect H n - (X (S.blockOf n)).expect H (S.T (S.blockOf n))|

/-! ## C. Deck-TT: the expert inside the gate -/

/-- **The LUV side of deck-TT.** For an expert sequence `expert : ℕ → ℝ` (the deck's
`𝔼^A_n(V_n)`, a real number per day), a value family `V`, thresholds `v` and widths `δ`: `B n` is
valued in every completed-theory world of `DPH` at the gate `ctsInd (δ n) (expert n) (v n)`
(`Ind_δ(𝔼^A_n(V_n) > v)`), `A n` at `x · gate` whenever `V n` is valued at `x`; `V`, `A`, `B` e.c.
(`MachineThresholdCodeSeq`); every world values `V n` (FAF's `thm:ec` boundary, (c) per FAF);
`0 < δ n`, `δ` machine-codeable, `v ∈ [0,1]` and `ℙ^H`-generable (the full threshold family of
FAF's `thm:st`, which lets `p` be `PGenerableRat`; constants are the instance
`PGenerableRat.ofMachineRatCodes (MachineRatCodes.const _)`). **No `affine` field**: FAF's
`AffineQuoteGE` is the *certificate* FAF's `thm:st` carries, not part of the notion; carrying it
would make `DeckTT` a squeeze of `lic_self_trust` (kind `S`). It enters only on the FAF side of
the self-trust instance (`SelfInstance.lean`).
Source: [[delay-program]] §5 lines 188–190 (root-fa-034: deck-TT for every e.d. LUV sequence and the full threshold family); FAF `SelfTrustQuote` (`Properties/SelfTrust.lean:420`, the `confidence_reflected`/`product_reflected` shape)
Kind: D
Fidelity: variant: the expert is a real sequence (the bridge `accelerator` names it); the deck's "e.d." is FAF's `MachineThresholdCodeSeq`; `v` is `PGenerableRat` (FAF's `thm:st` class), `δ` machine-codeable
Hyps: n/a (a structure; `source_valued` is (c) per FAF wherever it is assumed) -/
structure DeckTrustQuote (H : History) (DPH : DeductiveProcess) (expert : ℕ → ℝ) (V : ℕ → LUV)
    (v δ : ℕ → ℚ) (A B : ℕ → LUV) : Prop where
  /-- Positive widths. -/
  delta_pos : ∀ n, 0 < δ n
  /-- The widths are machine-codeable (FAF's `thm:st` closed form needs `MachineRatCodes δ`). -/
  delta_codes : MachineRatCodes δ
  /-- Thresholds in `[0,1]`. -/
  threshold_mem : ∀ n, 0 ≤ v n ∧ v n ≤ 1
  /-- The threshold family is `ℙ^H`-generable (FAF's `thm:st` class). -/
  threshold_generable : PGenerableRat H v
  /-- The value family is e.c. -/
  value_codes : LUV.MachineThresholdCodeSeq V
  /-- The product family is e.c. -/
  product_codes : LUV.MachineThresholdCodeSeq A
  /-- The gate family is e.c. -/
  confidence_codes : LUV.MachineThresholdCodeSeq B
  /-- Every completed-theory world values `V n` (FAF's `thm:ec` boundary). -/
  source_valued : ∀ n (w : PCWorld), w.ConsistentWithTheory DPH → ∃ x, w.ValuesAt (V n) x
  /-- `B n` is valued at the gate `Ind_{δ n}(expert n > v n)` in every completed-theory world. -/
  confidence_reflected : ∀ n (w : PCWorld), w.ConsistentWithTheory DPH →
    w.ValuesAt (B n) (ctsInd (δ n) (expert n) (v n))
  /-- `A n` is valued at `x · gate` whenever `V n` is valued at `x`. -/
  product_reflected : ∀ n (w : PCWorld), w.ConsistentWithTheory DPH →
    ∀ x, w.ValuesAt (V n) x → w.ValuesAt (A n) (x * ctsInd (δ n) (expert n) (v n))

/-- **Deck-TT (the definition of record).** `H` totally trusts the expert on the family `V` in the
deck's sense: for the full generable threshold family `v`, every machine-codeable positive width
`δ` and every reflecting pair `(A, B)`,
`𝔼^H_n(V_n · Ind_δ(expert_n > v_n)) ≳ₙ v_n · 𝔼^H_n(Ind_δ(expert_n > v_n))`. Quantifying over all
reflecting pairs is justified by `deckTT_robust` (`DeckTT.lean`): any two pairs have asymptotically
equal expectations. Choice recorded: `v` ranges over `PGenerableRat H` (FAF's `thm:st` class),
not constants only — so the self-trust instance inhabits the *full* family the deck states; the
constant-threshold restriction is `DeckTTConst`.
Source: [[delay-program]] §5 lines 188–190 (root-fa-034)
Kind: D
Fidelity: variant: as `DeckTrustQuote`
Hyps: n/a -/
def DeckTT (H : History) (DPH : DeductiveProcess) (expert : ℕ → ℝ) (V : ℕ → LUV) : Prop :=
  ∀ (v δ : ℕ → ℚ) (A B : ℕ → LUV), DeckTrustQuote H DPH expert V v δ A B →
    AsympGE (fun n => (A n).expect H n) (fun n => (v n : ℝ) * (B n).expect H n)

/-- **Deck-TT at constant thresholds and widths**: the restriction of `DeckTT` to constant `v`,
`δ`. The constant-`V` accelerator instance (T7) reaches this form; `DeckTT.toConst` relates them.
Source: [[delay-program]] §5 (root-fa-034); [[delay-program]] §6 T7 (root-fa-033)
Kind: D
Fidelity: weaker: constant thresholds and widths only
Hyps: n/a -/
def DeckTTConst (H : History) (DPH : DeductiveProcess) (expert : ℕ → ℝ) (V : ℕ → LUV) : Prop :=
  ∀ (v δ : ℚ) (A B : ℕ → LUV), DeckTrustQuote H DPH expert V (fun _ => v) (fun _ => δ) A B →
    AsympGE (fun n => (A n).expect H n) (fun n => (v : ℝ) * (B n).expect H n)

/-- Full deck-TT implies its constant-threshold restriction.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem DeckTT.toConst {H : History} {DPH : DeductiveProcess} {expert : ℕ → ℝ} {V : ℕ → LUV}
    (h : DeckTT H DPH expert V) : DeckTTConst H DPH expert V :=
  fun v δ A B hq => h (fun _ => v) (fun _ => δ) A B hq

/-- **The bridge: the deck's expert is the accelerator.** `accelerator Y A' n :=
𝔼^{A'}_n(Y_n) = 𝔼^{A'}_n(⌜𝔼^H_{f(n)}(V_n)⌝)` when `Y` is a quote family for `V` along `f`
(`CrossQuotePackage`). An `abbrev` over `fa-theorem-a`'s `quoteSeq`; the identification is the
content of the bridge (`accelerator_eq`), which puts the FA-format results and the deck on one
object.
Source: [[delay-program]] §5 lines 193–194 ("define the deck's expert as the accelerator, `𝔼^A_n(V_n) := 𝔼^{A'}_n 𝔼^H_{f(n)}(V_n)`"; root-fa-034)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable abbrev accelerator (Y : ℕ → LUV) (A' : History) : ℕ → ℝ := quoteSeq Y A'

/-- **The bridge identity**: the deck's expert built from the accelerator is `fa-theorem-a`'s quote
`𝔼^{A'}_n(Y_n)` (definitionally). Deck-TT with `expert := accelerator Y A'` is therefore a
statement about the FA-format family's object.
Source: [[delay-program]] §5 line 194 (root-fa-034)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem accelerator_eq (Y : ℕ → LUV) (A' : History) (n : ℕ) :
    accelerator Y A' n = (Y n).expect A' n := rfl

/-! ## D. Anticipated deference: `H` reads `A`'s future quote -/

/-- **The anticipated-quote package** (T8): a LUV family `Q` of `H`'s language, e.c., with `Q n`
determined in `H`'s completed theory at `A`'s *future* quote `quoteSeq Y A (g n)` — the
"`H` reads `A`" direction, two-way with `CrossQuotePackage` (which is "`A` reads `H`").
Source: FA-critique msg 43 line 3040 (lean-deference-056: "compare the human's current credence in `X` … with its current *expectation of* that future quote"); `li-quote-lane` `CrossQuotePackage` (the mirror shape)
Kind: D
Fidelity: exact (the family `Q n = ⌜quote_{g(n)}⌝` as a determinacy package)
Hyps: n/a (a structure; `reflected` is the two-way (c) wherever it is assumed) -/
structure AnticipatedQuote (H : History) (DPH : DeductiveProcess) (Y : ℕ → LUV) (A : History)
    (g : DeferralFunction) (Q : ℕ → LUV) : Prop where
  /-- The family is e.c. -/
  quote_codes : LUV.MachineThresholdCodeSeq Q
  /-- `Q n` is determined in `H`'s completed theory at `A`'s day-`g n` quote. -/
  reflected : ∀ n, LUV.DeterminedVia (Q n) DPH (quoteSeq Y A (g.f n))

end Cleanroom.Fa.FaDelayBsi
