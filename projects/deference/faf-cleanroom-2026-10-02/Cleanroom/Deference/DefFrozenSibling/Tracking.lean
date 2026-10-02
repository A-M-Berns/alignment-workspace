import Cleanroom.Deference.DefFrozenSibling.Gated
import Cleanroom.Deference.DefTrackingPin.Pin
import Cleanroom.Deference.DefTrackingPin.Atoms

/-!
# `def-frozen-sibling` · Tracking: T1 faithful tracking and T2 earned meta-trust

**T1** ([[frozen-deliberation-deference-v6]] T1, anson-018; root-deference-038; lean-deference-020):
`a_n ≈ₙ Y_n` on every `n` — `def-tracking-pin`'s pinning lemma `pinning_ofApprox` at the contract
LUV `C_n = ledgerLuv 0 n` in the predictor's process, with `determinedA` from the carrier (the
ledger construction) and the published quote `a n = 𝔼^A_n(C_n)` by `a_eq`. The one non-(a)
hypothesis is `hz`, the H-class clause (checklist row 6): a `A`-generable rational approximant of
the target. **Not** the [[AUDIT]] §3.3 squeeze: no bound on `a − Y` is assumed; the settlement is an
FAF fact (`determinedA`) and the forcing is FAF's affine provability induction inside
`pinning_ofApprox`. Two-way at `S : FrozenSystem` (`partial: over the OPEN pair` —
`frozenSystem_exists`, where `hz` has no discharge: the diagonal is a sibling-LIA run and no
generable approximant of it is claimed); the one-way N+
is `tracking_onG` (`OnG.lean` §E: FAF's LIA at `onGSystem` with the generable alternating table as
`ẑ`); `def-tracking-pin`'s `deferred_tracking_any` is the cross-reference over its own carrier.
The source's "timely (uniform at settlement)" clause of T1 — a resource-bounded rate — is not
rendered: the `≈ₙ` is the asymptotic half.

**T2** (v6 T2, anson-019; root-deference-039; lean-deference-021): the advised reasoner learns the
track record. The calibration sentence `calSentence ε₀ n` is a finite Boolean combination of the
threshold literals of the two `H`-side ledger items (the quote and the settled value) over the grid
`k·ε₀/2`, true in every completed-theory world of `Hplus`'s process iff the two settled values are
within one grid step: `|a_n − Y_n| ≤ ε₀/2` makes it a theorem, and it being a theorem gives
`|a_n − Y_n| ≤ ε₀` (exact constants, `calSentence_holds_of_close`, `close_of_calSentence_holds`).
T2b: `Hplus n (calSentence ε₀ n) → 1`, from T1 and `def-tracking-pin`'s `provind_eventually_true`.
This is **trust in a record**, root-deference-039's correction: `H⁺` does not prove T1, it learns
an e.c. sequence of decided calibration facts. T2a: the expectation form `𝔼^{H}_n(α_{0,n}) −
𝔼^{H}_n(α_{1,n}) → 0` (the two settled ledger items), by the two-mesh engine. Finding F2 (v6's
`ε_n → 0` form is unsupported over FAF) is in [[def-frozen-sibling-findings]].
-/

namespace Cleanroom.Deference.DefFrozenSibling

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefTrackingPin
open Filter Topology AffineCombination

/-! ## A. T1: faithful tracking -/

/-- **T1 — faithful tracking** (headline). The published quote tracks the sibling's verdict,
`a_n ≈ₙ Y_n`, for any `A`-generable rational approximant `ẑ` of the target (`hz`, with
`ẑ_n − Y_n → 0`). Instance of `def-tracking-pin`'s `pinning_ofApprox` at `X n := ledgerLuv 0 n`
(the contract LUV of the predictor's language), `hdet := determinedA` (settlement, from the ledger
construction — not a hypothesis-bounded real sequence), `hworld := hworldA`, the e.c. certificate
`li-quote-lane`'s `ledgerLuv_thresholdCodes 0`; `a_eq` identifies `𝔼^A_n(C_n)` with `a n`. Roles:
`A` the predictor (reader), `sib n` the sibling whose day-`F n` verdict settles the contract.
**Two-way** (`A_inductor` over a ledger settled to the sibling's verdict): `partial: over the OPEN
pair` at `S`; the one-way N+ instance is `tracking_onG` (`OnG.lean` §E); cross-reference
`def-tracking-pin`'s `deferred_tracking_any` (same `hz`, its own carrier). Not rendered: the
source's "timely (uniform at settlement when `σ(n) ≥ c·R_H(F(n))`)" rate clause (no FAF carrier).
Source: [[frozen-deliberation-deference-v6]] T1 (lines 82–86; anson-018); [[deference-in-logical-induction-v6]] §5.4 T1 line 582 (root-deference-038, the L variant); lean-deference-020 (`faithful_tracking`, [[AUDIT]] §3.3 — the squeeze this replaces)
Kind: L (instance of `def-tracking-pin`'s `pinning_ofApprox`, Kind C)
Fidelity: variant: plain trader class; `hz` for the source's (A4) power; settlement rendered as `DeterminedVia` (time-free); exact rational contract
Hyps: (c) `hz` — generability of the approximant at the predictor, FAF's one trader class standing in for the corpus's `𝒞_A`-computability of `Y_n` (checklist row 6); all else (a) -/
theorem tracking (S : FrozenSystem) (zhat : ℕ → ℚ) (hz : PGenerableRat S.A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0)) :
    (fun n => (S.a n : ℝ)) ≈ₙ (fun n => (S.Y n : ℝ)) := by
  haveI := S.A_inductor
  have h := pinning_ofApprox (P := S.A) (DP := S.processA) (ledgerLuv_thresholdCodes 0)
    S.hworldA (v := fun n => (S.Y n : ℝ)) S.determinedA zhat hz hlim
  have he : (fun n => (S.a n : ℝ)) = fun n => (ledgerLuv 0 n).expect S.A n := funext S.a_eq
  rw [he]
  exact h

/-- **T1, exact approximant**: if the target table `Y` is itself `A`-generable, `a_n ≈ₙ Y_n`
(`pinning_exact`). Same (c).
Source: root-deference-038 (the L variant: "if the target is e.c.")
Kind: L
Fidelity: variant: plain trader class
Hyps: (c) `hz`; all else (a) -/
theorem tracking_exact (S : FrozenSystem) (hz : PGenerableRat S.A S.Y) :
    (fun n => (S.a n : ℝ)) ≈ₙ (fun n => (S.Y n : ℝ)) :=
  tracking S S.Y hz (by simp only [sub_self]; exact tendsto_const_nhds)

/-- **T1, convergent target, no `hz`** (`pinning_ofTendsto`): if `Y_n → L`, then `a_n ≈ₙ Y_n`
with no generability clause. **Idle for the construction**: on `G` the verdict `Y_n` is within
`ε_n` of a decided value in `{0,1}`, which does not converge unless the polarity does; the theorem
is recorded because it is the only `hz`-free form of T1 FAF supplies.
Source: anson-030 (via `def-tracking-pin` T3); mandate T1 ("note it is idle for the construction")
Kind: L
Fidelity: exact (the convergent case)
Hyps: (a) none -/
theorem tracking_ofTendsto (S : FrozenSystem) {L : ℝ}
    (hconv : Tendsto (fun n => (S.Y n : ℝ)) atTop (𝓝 L)) :
    (fun n => (S.a n : ℝ)) ≈ₙ (fun n => (S.Y n : ℝ)) := by
  haveI := S.A_inductor
  have h := pinning_ofTendsto (P := S.A) (DP := S.processA) (ledgerLuv_thresholdCodes 0)
    S.hworldA (v := fun n => (S.Y n : ℝ)) S.determinedA hconv
  have he : (fun n => (S.a n : ℝ)) = fun n => (ledgerLuv 0 n).expect S.A n := funext S.a_eq
  rw [he]
  exact h

/-! ## B. The calibration sentence -/

/-- The grid point `k·ε₀/2`.
Source: mandate T2
Kind: D
Fidelity: n/a -/
def grid (ε₀ : ℚ) (k : ℕ) : ℚ := k * (ε₀ / 2)

/-- The number of grid steps: `⌈2/ε₀⌉ + 1`, so that the last grid point exceeds `1`.
Source: mandate T2
Kind: D
Fidelity: n/a -/
def gridSize (ε₀ : ℚ) : ℕ := ⌈2 / ε₀⌉₊ + 1

/-- The `k`-th calibration clause at day `n`: "if the quote exceeds grid point `k+1` then the
settled value exceeds grid point `k`, and symmetrically" — two implications, each written as
`∼(φ ⋏ ∼ψ)`, over the ledger literals of items `0` (quote) and `1` (settled value).
Source: mandate T2 ("a finite Boolean combination of the threshold literals")
Kind: D
Fidelity: n/a -/
def calClause (ε₀ : ℚ) (k n : ℕ) : Sentence :=
  ∼((ledgerLuv 0 n).gt (grid ε₀ (k + 1)) ⋏ ∼((ledgerLuv 1 n).gt (grid ε₀ k))) ⋏
    ∼((ledgerLuv 1 n).gt (grid ε₀ (k + 1)) ⋏ ∼((ledgerLuv 0 n).gt (grid ε₀ k)))

/-- The conjunction of the first `K` clauses (recursive, so that its e.c. certificate is `K`
applications of FAF's `MachineSentenceCodes.and`).
Source: mandate T2
Kind: D
Fidelity: n/a -/
def calConj (ε₀ : ℚ) : ℕ → ℕ → Sentence
  | 0, _ => ⊤
  | K + 1, n => calConj ε₀ K n ⋏ calClause ε₀ K n

/-- **The calibration sentence** `cal ε₀ n`: "the quote `a_n` and the settled value `Y_n` are
within one grid step of each other", as the conjunction of the `gridSize ε₀` clauses.
Source: [[frozen-deliberation-deference-v6]] T2 (`𝟙[|a_n − Y_n| ≤ εₙ]`, at a fixed `ε₀`); mandate T2
Kind: D
Fidelity: variant: fixed `ε₀` (the source's `ε_n → 0` form is unsupported over FAF, findings F2); one-grid-step closeness in place of a sharp `|a − Y| ≤ ε₀` (the exact constants are the two lemmas below)
Hyps: n/a -/
def calSentence (ε₀ : ℚ) (n : ℕ) : Sentence := calConj ε₀ (gridSize ε₀) n

/-- `calClause_codes`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem calClause_codes (ε₀ : ℚ) (k : ℕ) : MachineSentenceCodes (calClause ε₀ k) :=
  ((ledgerLuv_gt_sentenceCodes 0 (grid ε₀ (k + 1))).and
    (ledgerLuv_gt_sentenceCodes 1 (grid ε₀ k)).neg).neg.and
    ((ledgerLuv_gt_sentenceCodes 1 (grid ε₀ (k + 1))).and
      (ledgerLuv_gt_sentenceCodes 0 (grid ε₀ k)).neg).neg

/-- `calConj_codes`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem calConj_codes (ε₀ : ℚ) : ∀ K, MachineSentenceCodes (calConj ε₀ K)
  | 0 => MachineSentenceCodes.const ⊤
  | K + 1 => (calConj_codes ε₀ K).and (calClause_codes ε₀ K)

/-- The calibration sentence family is e.c. (`cal_codes` of the mandate).
Source: mandate T2
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem calSentence_codes (ε₀ : ℚ) : MachineSentenceCodes (calSentence ε₀) :=
  calConj_codes ε₀ (gridSize ε₀)

/-- `holds_calConj_iff`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem holds_calConj_iff (ε₀ : ℚ) (w : PCWorld) (n : ℕ) :
    ∀ K, w.Holds (calConj ε₀ K n) ↔ ∀ k < K, w.Holds (calClause ε₀ k n)
  | 0 => by simp [calConj, PCWorld.holds_top]
  | K + 1 => by
    rw [calConj, PCWorld.holds_and, holds_calConj_iff ε₀ w n K]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h1 k hk
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h K (Nat.lt_succ_self K)⟩

/-- In a completed-theory world of the advised reasoner's process, the `k`-th clause holds iff the
two implications hold of the numbers `a_n`, `Y_n` (the ledger literals are decided at the table,
`def-tracking-pin`'s `ledgerLuv_gt_holds_iff`; strict polarity, disclosure (β)).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem holds_calClause_iff (S : FrozenSystem) (ε₀ : ℚ) (k n : ℕ) (w : PCWorld)
    (hw : w.ConsistentWithTheory S.processH) :
    w.Holds (calClause ε₀ k n) ↔
      (grid ε₀ (k + 1) < S.a n → grid ε₀ k < S.Y n) ∧
        (grid ε₀ (k + 1) < S.Y n → grid ε₀ k < S.a n) := by
  have h0 : ∀ q, w.Holds ((ledgerLuv 0 n).gt q) ↔ q < S.a n := fun q => by
    rw [ledgerLuv_gt_holds_iff S.base (frozenTable S.a S.Y) (frozenSched S.eq S.eY) 0 n q w hw]
    rfl
  have h1 : ∀ q, w.Holds ((ledgerLuv 1 n).gt q) ↔ q < S.Y n := fun q => by
    rw [ledgerLuv_gt_holds_iff S.base (frozenTable S.a S.Y) (frozenSched S.eq S.eY) 1 n q w hw]
    rfl
  simp only [calClause, PCWorld.holds_and, PCWorld.holds_neg, h0, h1]
  tauto

/-- **Direction 1 (exact constant)**: if `|a_n − Y_n| ≤ ε₀/2` then every clause holds.
Source: mandate T2 ("`|a_n − Y_n| ≤ ε₀/2 → theorem`")
Kind: L
Fidelity: n/a -/
theorem calSentence_holds_of_close (S : FrozenSystem) {ε₀ : ℚ} (n : ℕ)
    (hclose : |S.a n - S.Y n| ≤ ε₀ / 2) (w : PCWorld)
    (hw : w.ConsistentWithTheory S.processH) : w.Holds (calSentence ε₀ n) := by
  rw [calSentence, holds_calConj_iff]
  intro k _
  rw [holds_calClause_iff S ε₀ k n w hw]
  have hg : grid ε₀ (k + 1) = grid ε₀ k + ε₀ / 2 := by
    simp only [grid]; push_cast; ring
  obtain ⟨hl, hr⟩ := abs_le.1 hclose
  constructor <;> intro h <;> linarith

/-- **Direction 2 (exact constant)**: if every clause holds then `|a_n − Y_n| ≤ ε₀` (for
`ε₀ > 0`; the values are in `[0,1]`, `Y_mem_Icc`, `a_mem_Icc`). Proof: were `a_n > Y_n + ε₀`,
the grid point `k+2` with `k = ⌊Y_n/(ε₀/2)⌋` lies strictly between `Y_n + ε₀/2` and `a_n`, and
clause `k+1` forces `Y_n > ` grid point `k+1`, against the choice of `k`; symmetrically.
Source: mandate T2 ("`theorem → |a_n − Y_n| ≤ …`"; the mandate's `3ε₀/2` is improved to `ε₀`)
Kind: L
Fidelity: n/a -/
theorem close_of_calSentence_holds (S : FrozenSystem) {ε₀ : ℚ} (hε₀ : 0 < ε₀) (n : ℕ)
    (w : PCWorld) (hw : w.ConsistentWithTheory S.processH) (h : w.Holds (calSentence ε₀ n)) :
    |S.a n - S.Y n| ≤ ε₀ := by
  rw [calSentence, holds_calConj_iff] at h
  have hcl : ∀ k < gridSize ε₀,
      (grid ε₀ (k + 1) < S.a n → grid ε₀ k < S.Y n) ∧
        (grid ε₀ (k + 1) < S.Y n → grid ε₀ k < S.a n) :=
    fun k hk => (holds_calClause_iff S ε₀ k n w hw).1 (h k hk)
  obtain ⟨hY0, hY1⟩ := S.Y_mem_Icc n
  obtain ⟨ha0, ha1⟩ := S.a_mem_Icc n
  have hstep : 0 < ε₀ / 2 := by linarith
  have hgrid : ∀ k, grid ε₀ (k + 1) = grid ε₀ k + ε₀ / 2 := fun k => by
    simp only [grid]; push_cast; ring
  -- the last grid point exceeds `1`
  have hlast : (1 : ℚ) < grid ε₀ (gridSize ε₀) := by
    simp only [grid, gridSize]
    push_cast
    have h1 : (2 / ε₀ : ℚ) ≤ ⌈2 / ε₀⌉₊ := Nat.le_ceil _
    have h2 : (2 / ε₀ : ℚ) * (ε₀ / 2) = 1 := by field_simp
    nlinarith
  -- a generic one-sided step: `x + ε₀ < z`, both in `[0,1]`, contradicts the clauses
  have key : ∀ x z : ℚ, 0 ≤ x → z ≤ 1 → x + ε₀ < z →
      (∀ k < gridSize ε₀, grid ε₀ (k + 1) < z → grid ε₀ k < x) → False := by
    intro x z hx hz hxz hc
    set k := ⌊x / (ε₀ / 2)⌋₊ with hk
    have hk1 : grid ε₀ k ≤ x := by
      have := Nat.floor_le (div_nonneg hx hstep.le)
      rw [← hk] at this
      simp only [grid]
      calc (k : ℚ) * (ε₀ / 2) ≤ x / (ε₀ / 2) * (ε₀ / 2) := by gcongr
        _ = x := by field_simp
    have hk2 : x < grid ε₀ (k + 1) := by
      have := Nat.lt_floor_add_one (x / (ε₀ / 2))
      rw [← hk] at this
      simp only [grid]
      push_cast
      calc x = x / (ε₀ / 2) * (ε₀ / 2) := by field_simp
        _ < ((k : ℚ) + 1) * (ε₀ / 2) := by gcongr
    have hk3 : grid ε₀ (k + 2) < z := by
      rw [show k + 2 = (k + 1) + 1 from rfl, hgrid, hgrid]
      linarith
    have hkK : k + 1 < gridSize ε₀ := by
      by_contra hcon
      push_neg at hcon
      have hmono : grid ε₀ (gridSize ε₀) ≤ grid ε₀ (k + 2) := by
        simp only [grid]
        gcongr
        omega
      linarith
    have := (hc (k + 1) hkK) hk3
    linarith
  rw [abs_le]
  constructor
  · -- `Y − a ≤ ε₀`, i.e. not `a + ε₀ < Y`
    by_contra hcon
    push_neg at hcon
    exact key (S.a n) (S.Y n) ha0 hY1 (by linarith) (fun k hk => (hcl k hk).2)
  · -- `a − Y ≤ ε₀`, i.e. not `Y + ε₀ < a`
    by_contra hcon
    push_neg at hcon
    exact key (S.Y n) (S.a n) hY0 ha1 (by linarith) (fun k hk => (hcl k hk).1)

/-! ## C. T2b: earned meta-trust -/

/-- **T2b — earned meta-trust** (headline): the advised reasoner's price of the day-`n` calibration
sentence tends to `1`: `Hplus n (calSentence ε₀ n) ≈ₙ 1`, for every fixed `ε₀ > 0`. From T1
(`a_n − Y_n → 0`, so eventually `|a_n − Y_n| ≤ ε₀/2` and the calibration sentence is a theorem of
`Hplus`'s completed theory, `calSentence_holds_of_close`) and `def-tracking-pin`'s
`provind_eventually_true` at the e.c. family `calSentence ε₀`. **Trust in a record**
(root-deference-039): `H⁺` does not prove T1 — it learns the e.c. sequence of decided calibration
facts, which the ledger makes theorems of its own process. Roles: `Hplus` the advised reasoner,
`A` the predictor (through T1). **Two-way** through T1's `A_inductor`: `partial: over the OPEN
pair`.
Source: [[frozen-deliberation-deference-v6]] T2 (lines 88–92; anson-019); [[deference-in-logical-induction-v6]] §5.4 T2 (root-deference-039, "trust in a record"); lean-deference-021
Kind: C
Fidelity: variant: fixed `ε₀` sentence form (the source's `ε_n → 0` indicator form is unsupported over FAF, findings F2); plain trader class
Hyps: (c) `hz` through T1 (checklist row 6); all else (a) -/
theorem metaTrust (S : FrozenSystem) {ε₀ : ℚ} (hε₀ : 0 < ε₀) (zhat : ℕ → ℚ)
    (hz : PGenerableRat S.A zhat) (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0)) :
    (fun n => S.Hplus n (calSentence ε₀ n)) ≈ₙ fun _ => 1 := by
  haveI := S.Hplus_inductor
  have hT1 := tracking S zhat hz hlim
  have hev : ∀ᶠ n in atTop, |S.a n - S.Y n| ≤ ε₀ / 2 := by
    have h := asympEq_iff_eventuallyWithin.1 hT1 ((ε₀ : ℝ) / 2) (by positivity)
    filter_upwards [h] with n hn
    exact_mod_cast hn
  refine provind_eventually_true S.Hplus S.processH (calSentence ε₀) (calSentence_codes ε₀)
    ?_ S.hworldH
  filter_upwards [hev] with n hn w hw
  exact calSentence_holds_of_close S n hn w hw

/-! ## D. T2a: the expectation form, by the two-mesh engine -/

/-- The difference of the day-`n` meshes of two LUV families.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def meshDiff (X Z : ℕ → LUV) (n : ℕ) : AffineCombination :=
  ((X n).expectAffine (n + 1)).add ((Z n).expectAffine (n + 1)).neg

/-- `meshDiff_polySequence`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
noncomputable def meshDiff_polySequence {X Z : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X)
    (hZ : LUV.MachineThresholdCodeSeq Z) : PolySequence (meshDiff X Z) :=
  (LUV.expectAffineSeq_polySequence X hX).add (LUV.expectAffineSeq_polySequence Z hZ).neg

/-- **Two-mesh pinning**: two e.c. LUV families settled at `x n`, `z n` with `x_n − z_n → 0`
have `𝔼^P_n(X_n) − 𝔼^P_n(Z_n) → 0` — no generability of either target (the difference enters
only through world values). Reader `P`; one-way.
Source: mandate T2a (the route through `pin_tendsto_of_polySequence` on the difference combination)
Kind: C
Fidelity: n/a (infrastructure)
Hyps: (a) none -/
theorem mesh_pair_pin (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {X Z : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X) (hZ : LUV.MachineThresholdCodeSeq Z)
    (x z : ℕ → ℝ) (hdx : ∀ n, LUV.DeterminedVia (X n) DP (x n))
    (hdz : ∀ n, LUV.DeterminedVia (Z n) DP (z n))
    (hlim : Tendsto (fun n => x n - z n) atTop (𝓝 0)) :
    (fun n => (X n).expect P n) ≈ₙ (fun n => (Z n).expect P n) := by
  have hP : ∀ m ψ, 0 ≤ P m ψ ∧ P m ψ ≤ 1 := fun m ψ =>
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP) m ψ
  have hpoly := meshDiff_polySequence hX hZ
  have hprice : ∀ n, (meshDiff X Z n).price P n = (X n).expect P n - (Z n).expect P n := by
    intro n
    rw [meshDiff, add_price, neg_price, LUV.expectAffine_price, LUV.expectAffine_price]
    ring
  have hbounded : BoundedAffinePrices (meshDiff X Z) P := by
    refine ⟨2, by norm_num, fun n m => ?_⟩
    rw [meshDiff, add_price, neg_price, price, price, LUV.expectAffine_value,
      LUV.expectAffine_value]
    have h0 := (X n).expectApprox_nonneg (P m) (n + 1) (fun s => (hP m s).1)
    have h1 := (X n).expectApprox_le_one (P m) (n + 1) (fun s => (hP m s).2)
    have h2 := (Z n).expectApprox_nonneg (P m) (n + 1) (fun s => (hP m s).1)
    have h3 := (Z n).expectApprox_le_one (P m) (n + 1) (fun s => (hP m s).2)
    rw [abs_le]
    constructor <;> linarith
  have hmag : ∃ C : ℝ, ∀ n, (meshDiff X Z n).magnitude P ≤ C := by
    refine ⟨2, fun n => ?_⟩
    rw [meshDiff, add_magnitude, neg_magnitude]
    linarith [(X n).expectAffine_magnitude_le_one P (n + 1),
      (Z n).expectAffine_magnitude_le_one P (n + 1)]
  have hval : ∀ ε > 0, ∀ᶠ n in atTop, ∀ w : PCWorld,
      w.ConsistentWithTheory DP → |(meshDiff X Z n).value P w.payout| ≤ ε := by
    intro ε hε
    have hlim1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim2 : Tendsto (fun n => |x n - z n|) atTop (𝓝 0) := by
      have := hlim.abs
      rwa [abs_zero] at this
    filter_upwards [hlim1.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < ε / 4)),
      hlim2.eventually (eventually_le_nhds (half_pos hε))] with n hn1 hn2 w hw
    rw [meshDiff, add_value, neg_value, LUV.expectAffine_value, LUV.expectAffine_value]
    have hk : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) = 1 / ((n : ℝ) + 1) := by push_cast; rfl
    have hx := valuesAt_expectApprox_near (hdx n w hw) (Nat.succ_pos n)
    have hz' := valuesAt_expectApprox_near (hdz n w hw) (Nat.succ_pos n)
    rw [hk] at hx hz'
    calc |(X n).expectApprox w.payout (n + 1) + -(Z n).expectApprox w.payout (n + 1)|
        = |((X n).expectApprox w.payout (n + 1) - x n) + (x n - z n) +
            (z n - (Z n).expectApprox w.payout (n + 1))| := by congr 1; ring
      _ ≤ |(X n).expectApprox w.payout (n + 1) - x n| + |x n - z n| +
            |z n - (Z n).expectApprox w.payout (n + 1)| := by
          refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ ε / 4 + ε / 2 + ε / 4 := by
          refine add_le_add (add_le_add (hx.trans hn1) hn2) ?_
          rw [abs_sub_comm]
          exact hz'.trans hn1
      _ = ε := by ring
  have hlim0 := hpoly.affine_provind_theory_tendsto_zero P DP hbounded hmag hworld hval
  unfold AsympEq at hlim0 ⊢
  refine hlim0.congr fun n => ?_
  dsimp only
  rw [hprice, sub_zero]

/-- **T2a — the expectation form**: the advised reasoner's day-`n` expectations of the two settled
ledger items (the quote `α_{0,n}` and the settled value `α_{1,n}`) agree asymptotically,
`𝔼^{H}_n(α_{0,n}) − 𝔼^{H}_n(α_{1,n}) → 0`. From T1 (`a_n − Y_n → 0`) and `mesh_pair_pin` at
`determinedH`. The cheaper, LUV-level reading of "`H⁺` learns that `A` tracks the target".
Roles: `Hplus` the advised reasoner. **Two-way** through T1: `partial: over the OPEN pair`
(`frozenSystem_exists`) and `hz` there.
Source: [[frozen-deliberation-deference-v6]] T2 (anson-019), expectation reading; mandate T2a
Kind: C
Fidelity: variant: expectations of the two settled items in place of the indicator of their closeness
Hyps: (c) `hz` through T1; all else (a) -/
theorem metaTrust_expect (S : FrozenSystem) (zhat : ℕ → ℚ) (hz : PGenerableRat S.A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0)) :
    (fun n => (ledgerLuv 0 n).expect S.Hplus n) ≈ₙ (fun n => (ledgerLuv 1 n).expect S.Hplus n) := by
  haveI := S.Hplus_inductor
  have hT1 := tracking S zhat hz hlim
  exact mesh_pair_pin S.Hplus S.processH S.hworldH (ledgerLuv_thresholdCodes 0)
    (ledgerLuv_thresholdCodes 1) (fun n => (S.a n : ℝ)) (fun n => (S.Y n : ℝ))
    (fun n => S.determinedH 0 n) (fun n => S.determinedH 1 n) hT1

end Cleanroom.Deference.DefFrozenSibling
