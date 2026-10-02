import Cleanroom.Decision.DpDevicesCatalog.Values
import Cleanroom.Decision.DpCalibration.Miniature
import Cleanroom.Decision.DpCalibration.MiniDevices

set_option autoImplicit false

/-!
# `dp-devices-catalog` — T6(a)–(c): Remark 4.3's miniature

Two different devices hide under the one word "exploration" (sequence-map A1; dp-cf-135 ZO-18),
named apart here and never called `trembleEdt` bare:

* (a) **the fixed-`ε` tie device** (`FixedEpsTie ε q`): the miniature's act values at the
  trembled label `q_ε = (1−ε)q + ε/2` are `2(1−q_ε)` and `q_ε` (derived from
  `calibratedState (tremble (procQ q) ε) miniature ⊤` via `miniState_V_*`); they tie iff
  `q = qstar ε := (4 − 3ε)/(6(1−ε))`, which lies in `[2/3, 1]` for `ε ≤ ½` and is injective
  in `ε` (no label ties at two tremble sizes). The faithful no-fixed-`q` statement is
  `miniature_not_eventTremble` (dp-calibration), cited.
* (b) **P05's `ε`-floor device** (`FloorRatifiable ε q`, Selten's `ε`-perfection): best
  response at the floored label itself, non-maximisers allowed only at their floor. For
  `ε ≤ 1/3` the ratifiable label is exactly `2/3`; for `1/3 < ε ≤ ½` it is exactly the corner
  `1 − ε` (dp-sl-2-014's UNREVIEWED detail, **confirmed**).
* (c) **equilibrium, not optimum** (ZO-16): `V(2/3) = 2/3 < 3/4 = V(1/2)`; `procQ (2/3)` is not
  Theorem-1-ratifiable (`Φ(a) = 1 < 2 = Φ(b)`, i.e. `V'(2/3) = −1`), not mixed-Def-22-coherent,
  and pure-Def-22-coherent (`0 ≤ 2/3` for both pure deviations).

Cited from dp-calibration, not restated: `miniState_V_a/b`, CA-13′'s approved set
(`miniature_tEdt_pure_a/b`, `miniature_tie_approved`), `miniature_not_eventTremble` (D2 empty),
`miniature_adviceEdt_iff` (D4 = `{2/3}`).
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

/-! ## (a) The fixed-`ε` tie device -/

/-- The trembled label `q_ε := (1−ε) q + ε/2`.
Source: `calibration.md` CA-14′
Kind: D -/
def qeps (q ε : ℚ) : ℚ := (1 - ε) * q + ε / 2

/-- **The trembled act values on the miniature**, derived from the strict state of the trembled
procedure at `⊤`: `V(a) = 2(1 − q_ε)`, `V(b) = q_ε`, for `0 < ε < 1`.
Source: `calibration.md` CA-14′ (`v_ε(a) = 2(1−q_ε)`, `v_ε(b) = q_ε`); `P05.md` P05-5′
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q ≤ 1`, `0 < ε < 1` -/
theorem miniature_tremble_act_values (q ε : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h0 : 0 < ε)
    (h1 : ε < 1) :
    (calibratedState (tremble (procQ q hq0 hq1) ε h0.le h1.le) miniature Finset.univ
        (nu_univ_pos _ _)).V (miniActEv () .a) = 2 * (1 - qeps q ε) ∧
    (calibratedState (tremble (procQ q hq0 hq1) ε h0.le h1.le) miniature Finset.univ
        (nu_univ_pos _ _)).V (miniActEv () .b) = qeps q ε := by
  obtain ⟨hi0, hi1⟩ := qeps_interior q ε hq0 hq1 h0 h1
  rw [tremble_procQ]
  exact ⟨miniState_V_a _ hi0 hi1.le, miniState_V_b _ hi0.le hi1⟩

/-- **The fixed-`ε` tie device** on the miniature: the two trembled act values tie at the label
`q` (SE-18′(a)'s per-`ε` best-response fixed point, *not* Remark 3.12's device). Stated on the
closed forms `2(1 − q_ε)`, `q_ε`; the tree enters through `miniature_tremble_act_values`, and
the state-level statement (the calibrated state of `C^ε` at `⊤` values the two acts equally)
is `miniature_fixedEps_tie_state_iff`.
Source: `P05.md` P05-5′ ("a best-response fixed point on `Δ_ε`, not Remark 3.12's
tremble-consistency"); mandate T6(a)
Kind: D
Fidelity: variant: on the closed forms (the state-level tie is the theorem below) -/
def FixedEpsTie (ε q : ℚ) : Prop := 2 * (1 - qeps q ε) = qeps q ε

/-- `q*(ε) := (4 − 3ε)/(6(1−ε))`, the unique label at which the fixed-`ε` device ties.
Source: mandate T6(a)
Kind: D -/
def qstar (ε : ℚ) : ℚ := (4 - 3 * ε) / (6 * (1 - ε))

/-- **The fixed-`ε` device ties exactly at `q*(ε)`**: `2(1 − q_ε) = q_ε ↔ q = (4 − 3ε)/(6(1−ε))`.
Source: mandate T6(a) (`miniature_fixedEps_tie_iff`)
Kind: P
Fidelity: exact
Hyps: (a) `0 < ε < 1` -/
theorem miniature_fixedEps_tie_iff (ε q : ℚ) (h0 : 0 < ε) (h1 : ε < 1) :
    FixedEpsTie ε q ↔ q = qstar ε := by
  unfold FixedEpsTie qeps qstar
  have hne : (6 * (1 - ε)) ≠ 0 := by
    have : (0 : ℚ) < 1 - ε := by linarith
    positivity
  rw [eq_div_iff hne]
  constructor <;> intro h <;> linarith

/-- **The fixed-`ε` tie at the state level**: the calibrated state of the trembled procedure
`C^ε` at `⊤` values `a` and `b` equally iff `q = q*(ε)` — the tree-level statement of which
`FixedEpsTie` is the closed form.
Source: `calibration.md` CA-14′; `P05.md` P05-5′; mandate T6(a)
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q ≤ 1`, `0 < ε < 1` -/
theorem miniature_fixedEps_tie_state_iff (q ε : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h0 : 0 < ε)
    (h1 : ε < 1) :
    (calibratedState (tremble (procQ q hq0 hq1) ε h0.le h1.le) miniature Finset.univ
        (nu_univ_pos _ _)).V (miniActEv () .a) =
      (calibratedState (tremble (procQ q hq0 hq1) ε h0.le h1.le) miniature Finset.univ
        (nu_univ_pos _ _)).V (miniActEv () .b) ↔ q = qstar ε := by
  obtain ⟨ha, hb⟩ := miniature_tremble_act_values q ε hq0 hq1 h0 h1
  rw [ha, hb]
  exact miniature_fixedEps_tie_iff ε q h0 h1

/-- `q*(ε) ∈ [2/3, 1]` for `0 < ε ≤ ½`; `q*(1/3) = 3/4`, `q*(1/2) = 5/6`.
Source: mandate T6(a) (`qstar_mem`; "recompute the range")
Kind: P
Fidelity: exact
Hyps: (a) `0 < ε ≤ ½` -/
theorem qstar_mem (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 2) :
    2 / 3 ≤ qstar ε ∧ qstar ε ≤ 1 := by
  unfold qstar
  have hpos : (0 : ℚ) < 6 * (1 - ε) := by linarith
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; linarith

/-- The two named values. Source: mandate T6(a). Kind: N+ -/
theorem qstar_values : qstar (1/3) = 3/4 ∧ qstar (1/2) = 5/6 := by
  unfold qstar; norm_num

/-- **No label ties at two tremble sizes**: `q*` is injective on `(0, 1)` (it is strictly
increasing: `q*(ε₂) − q*(ε₁) = (ε₂ − ε₁)/(6(1−ε₁)(1−ε₂))`).
Source: mandate T6(a) (`qstar_injective`)
Kind: P
Fidelity: exact
Hyps: (a) both sizes in `(0, 1)` -/
theorem qstar_injective (ε₁ ε₂ : ℚ) (h10 : 0 < ε₁) (h11 : ε₁ < 1) (h20 : 0 < ε₂) (h21 : ε₂ < 1)
    (h : qstar ε₁ = qstar ε₂) : ε₁ = ε₂ := by
  unfold qstar at h
  have hn1 : (6 * (1 - ε₁)) ≠ 0 := by have : (0 : ℚ) < 1 - ε₁ := by linarith
                                      positivity
  have hn2 : (6 * (1 - ε₂)) ≠ 0 := by have : (0 : ℚ) < 1 - ε₂ := by linarith
                                      positivity
  rw [div_eq_div_iff hn1 hn2] at h
  linarith

/-! ## (b) P05's `ε`-floor device -/

/-- **P05's `ε`-floor ratifiability on the miniature** (Selten's `ε`-perfection): the label
`q` respects the floors (`ε ≤ q ≤ 1 − ε`), and is a best response to the state calibrated to
itself — act values `V(a) = 2(1−q)`, `V(b) = q` — except that an act at its floor may be a
non-maximiser: if `a` is above its floor (`ε < q`) then `V(b) ≤ V(a)`; if `b` is above its floor
(`q < 1 − ε`) then `V(a) ≤ V(b)`. Stated on the miniature's two act values (the general
`argmaxPlus` form would need a floored-label state assignment; not needed for the verdicts).
Source: `P05.md` P05-5′ ("P05's constraints 1–3 fix *one* `ε` and evaluate the expectations at
the floored label `d*` itself"); mandate T6(b)
Kind: D
Fidelity: variant: on the miniature's act values `2(1−q)`, `q` -/
def FloorRatifiable (ε q : ℚ) : Prop :=
  ε ≤ q ∧ q ≤ 1 - ε ∧ (q < 1 - ε → 2 * (1 - q) ≤ q) ∧ (ε < q → q ≤ 2 * (1 - q))

/-- **For `0 < ε ≤ 1/3` the floor-ratifiable label is exactly `2/3`**.
Source: `P05.md` P05-5′ ("for every `ε ≤ 1/3` the P05-ratifiable set is exactly `{2/3}`")
Kind: P
Fidelity: exact
Hyps: (a) `0 < ε ≤ 1/3` -/
theorem floorRatifiable_iff_small (ε q : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1 / 3) :
    FloorRatifiable ε q ↔ q = 2 / 3 := by
  unfold FloorRatifiable
  constructor
  · rintro ⟨hlo, hhi, hA, hB⟩
    rcases lt_or_eq_of_le hhi with hlt | heq
    · rcases lt_or_eq_of_le hlo with hgt | heq'
      · have := hA hlt; have := hB hgt; linarith
      · subst heq'; have := hA hlt; linarith
    · rcases lt_or_eq_of_le hlo with hgt | heq'
      · have := hB hgt; linarith
      · linarith
  · rintro rfl
    refine ⟨by linarith, by linarith, fun _ => by norm_num, fun _ => by norm_num⟩

/-- **For `1/3 < ε ≤ ½` the floor-ratifiable label is exactly the corner `1 − ε`** (at `ε = ½`
the floors meet and the corner is `½`). dp-sl-2-014's UNREVIEWED detail, confirmed.
Source: `P05.md` P05-5′ (UNREVIEWED: "for `ε ∈ (1/3, 1/2]` the P05-ratifiable label on the
miniature is the corner `1 − ε`"); mandate T6(b)
Kind: P
Fidelity: exact
Hyps: (a) `1/3 < ε ≤ ½` -/
theorem floorRatifiable_iff_corner (ε q : ℚ) (h0 : 1 / 3 < ε) (h1 : ε ≤ 1 / 2) :
    FloorRatifiable ε q ↔ q = 1 - ε := by
  unfold FloorRatifiable
  constructor
  · rintro ⟨hlo, hhi, hA, hB⟩
    rcases lt_or_eq_of_le hhi with hlt | heq
    · rcases lt_or_eq_of_le hlo with hgt | heq'
      · have := hA hlt; have := hB hgt; linarith
      · subst heq'; have := hA hlt; linarith
    · exact heq
  · rintro rfl
    refine ⟨by linarith, le_rfl, fun h => absurd h (lt_irrefl _), fun _ => by linarith⟩

/-- **The range is closed**: above `ε = ½` the floors cross and nothing is floor-ratifiable (no
junk selection), and at `ε = ½` the unique label is `½`; with `floorRatifiable_iff_small` and
`floorRatifiable_iff_corner` this settles every `ε > 0`.
Source: none: infrastructure (audit round 1, adversarial §3.8)
Kind: L -/
theorem floorRatifiable_boundary :
    (∀ ε q : ℚ, 1 / 2 < ε → ¬ FloorRatifiable ε q) ∧
      ∀ q : ℚ, FloorRatifiable (1 / 2) q ↔ q = 1 / 2 := by
  refine ⟨fun ε q h => ?_, fun q => ?_⟩
  · rintro ⟨h1, h2, -, -⟩; linarith
  · rw [floorRatifiable_iff_corner _ _ (by norm_num) (by norm_num)]; norm_num

/-- The N+ instance: at `ε = 2/5` the unique floor-ratifiable label is `3/5`.
Source: `P05.md` P05-5′ ("at `ε = 2/5` the corner `1 − ε = 3/5` is the unique solution")
Kind: N+ -/
theorem floorRatifiable_instance :
    FloorRatifiable (2/5) (3/5) ∧ ∀ q, FloorRatifiable (2/5) q → q = 3/5 := by
  constructor
  · rw [floorRatifiable_iff_corner _ _ (by norm_num) (by norm_num)]; norm_num
  · intro q h
    rw [floorRatifiable_iff_corner _ _ (by norm_num) (by norm_num)] at h
    rw [h]; norm_num

/-- **The two devices differ**: at `ε = 1/3` the fixed-`ε` tie device selects `q* = 3/4` and the
floor device selects `2/3`; at `ε = 2/5` they select `qstar (2/5) = 7/9` and `3/5`.
Source: mandate T6 ("these are two different devices under the one word 'exploration'")
Kind: N+ -/
theorem two_devices_differ :
    (∀ q, FixedEpsTie (1/3) q ↔ q = 3/4) ∧ (∀ q, FloorRatifiable (1/3) q ↔ q = 2/3) ∧
    (∀ q, FixedEpsTie (2/5) q ↔ q = 7/9) ∧ (∀ q, FloorRatifiable (2/5) q ↔ q = 3/5) := by
  refine ⟨fun q => ?_, fun q => floorRatifiable_iff_small (1/3) q (by norm_num) (by norm_num),
    fun q => ?_, fun q => by
      rw [floorRatifiable_iff_corner (2/5) q (by norm_num) (by norm_num)]; norm_num⟩
  · rw [miniature_fixedEps_tie_iff _ _ (by norm_num) (by norm_num)]; unfold qstar; norm_num
  · rw [miniature_fixedEps_tie_iff _ _ (by norm_num) (by norm_num)]; unfold qstar; norm_num

/-! ## (c) Equilibrium, not optimum (ZO-16) -/

/-- **Theorem 1's functional on the miniature**: `Φ(a) = 3(1 − q)`, `Φ(b) = 3q`; their
difference `3 − 6q` is `V'(q)` for `V = 3q(1−q)`.
Source: `zoo.md` ZO-16 ("Theorem-1-unratifiable, `V'(2/3) = −1`")
Kind: P
Fidelity: exact -/
theorem miniature_siaSum (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    siaSum (procQ q h0 h1) miniature () .a = 3 * (1 - q) ∧
    siaSum (procQ q h0 h1) miniature () .b = 3 * q := by
  constructor <;>
  · simp [miniature, Act2.sum_univ, value_decision, value_leaf, procQ, miniPay]
    ring

/-- **ZO-16: the calibrated tie `2/3` is an equilibrium, not an optimum**:
`V(2/3) = 2/3 < 3/4 = V(1/2)`; `procQ (2/3)` is not Theorem-1-ratifiable (`Φ(a) = 1 < 2 = Φ(b)`
while `a` is played), not mixed-Definition-22-coherent (the deviation to `½` improves), and
pure-Definition-22-coherent (both pure deviations give `0 ≤ 2/3`).
Source: `zoo.md` ZO-16 ("Remark 4.3's calibrated tie is an equilibrium, not an optimum")
Kind: N+
Fidelity: exact -/
theorem miniature_tie_equilibrium_not_optimum :
    value (procQ (2/3) (by norm_num) (by norm_num)) miniature = 2/3 ∧
    value (procQ (1/2) (by norm_num) (by norm_num)) miniature = 3/4 ∧
    ¬ Thm1At (procQ (2/3) (by norm_num) (by norm_num)) miniature () ∧
    ¬ CoherentAt (procQ (2/3) (by norm_num) (by norm_num)) miniature () ∧
    CoherentPureAt (procQ (2/3) (by norm_num) (by norm_num)) miniature () := by
  refine ⟨by rw [miniature_value]; norm_num, by rw [miniature_value]; norm_num, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨ha, hb⟩ := miniature_siaSum (2/3) (by norm_num) (by norm_num)
    have := h .a (by simp [procQ]) .b
    rw [ha, hb] at this
    norm_num at this
  · intro h
    rw [coherentAt_procQ_iff] at h
    have := h (1/2) (by norm_num) (by norm_num)
    rw [miniature_value, miniature_value] at this
    norm_num at this
  · rw [coherentPureAt_procQ_iff, miniature_value, miniature_value, miniature_value]
    norm_num

end Cleanroom.Decision.DpDevicesCatalog
