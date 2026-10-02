import Cleanroom.Decision.DpDevicesCatalog.Devices
import Cleanroom.Decision.DpCalibration.Chain
import Cleanroom.Decision.DpCalibration.MiniDevices
import Cleanroom.Decision.DpLocalOpt.AmdWitness

set_option autoImplicit false

/-!
# `dp-devices-catalog` — T8, the AMD column of the device table (CA-20′), encoding-named

The AMD appears under three action-event encodings (dp-cf-047; dp-calibration findings F10):
**last-draw** (`amdActEvLast`: `a := {sa, sba}`, `b := {sbb}`), **first-draw** (`amdActEvFirst`:
`a := {sa}`, `b := {sba, sbb}`), and the grid's unrecorded encoding (`Grid.lean`). Every cell
here names its encoding; every "none" cell is a universal over `q ∈ [0,1]` and small `ε` (CA-14′
checked four sample points; known issue 4).

| device | last-draw | first-draw | declaration |
|---|---|---|---|
| D2 | none (`∀ q`) | `δ_b` only | `amd_last_not_eventTremble`, `amd_first_eventTremble_iff` |
| D3 (`ε > 0`) | none (`∀ q`; encoding-free) | — | `amd_not_occTremble`, `amd_d3_at_hundredth` |
| D3⁰, Dev pure, Dev mixed, opt | `⅓`, `[0, ⅔]`, `⅓`, `⅓` (encoding-free) | — | `amd_thm1At_iff`, `amd_coherentPureAt_iff`, `amd_coherentAt_iff`, `amd_isOptimal_iff` (dp-local-opt, cited) |

D4 on the AMD (last-draw `⅔`, first-draw `δ_b`) is not shipped: at the boundary labels the
tremble-limit values need the second-order coefficients of `nuPoly`/`payPoly` (the report
records the gap).
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

/-! ## Infrastructure on the AMD -/

/-- `𝔼[r 1_X]` on the AMD: `sa` pays `0`, `sba` pays `4`, `sbb` pays `1`.
Source: none: infrastructure. Kind: L -/
theorem amd_paySum (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset AmdW) :
    paySum C amd X =
      (if AmdW.sba ∈ X then (C ()).w .b * (C ()).w .a * 4 else 0) +
      (if AmdW.sbb ∈ X then (C ()).w .b * (C ()).w .b else 0) := by
  rw [paySum_eq_sum_ite, amd_sum]
  simp [amd, leafLaw_decision, world_decision, payoff_decision]

/-- The point is queried. Source: none: infrastructure. Kind: L -/
theorem amd_queried_mem : () ∈ queried amd := by
  unfold amd; simp [queried_decision]

/-- `⊤` is tremble-realizable on the AMD. Source: none: infrastructure. Kind: L -/
theorem amd_nuPoly_obs_ne_zero (C : Proc Unit (fun _ => Act2) ℚ) :
    nuPoly C amd (amdObs ()) ≠ 0 := by
  rw [nuPoly_ne_zero_iff]
  refine ⟨⟨.a, ()⟩, by simp [amdObs], ?_⟩
  unfold amd; simp [chanceWeight]

/-! ## Last-draw events -/

/-- **The last-draw act-conditional values under `procQ r`**, `0 < r < 1`:
`v(a) = 4(1−r)/(2−r)`, `v(b) = 1`.
Source: `calibration.md` CA-14′ ("AMD **with last-draw action events**: `v_ε(a) =
4(1−q_ε)/(2−q_ε)` vs `v_ε(b) = 1`")
Kind: P
Fidelity: exact -/
theorem amd_last_condExp (r : ℚ) (h0 : 0 < r) (h1 : r < 1) :
    condExp (procQ r h0.le h1.le) amd (amdActEvLast () .a ∩ amdObs ()) = 4 * (1 - r) / (2 - r) ∧
    condExp (procQ r h0.le h1.le) amd (amdActEvLast () .b ∩ amdObs ()) = 1 := by
  simp only [condExp, amdObs, Finset.inter_univ, amd_nu, amd_paySum, amdActEvLast, procQ,
    FinDistr.act2_a, FinDistr.act2_b]
  simp
  have h2 : (0 : ℚ) < 2 - r := by linarith
  have h1' : (0 : ℚ) < 1 - r := by linarith
  constructor
  · rw [div_eq_div_iff (by nlinarith) h2.ne']; ring
  · exact h1'.ne'

/-- Both last-draw act events are realized under `procQ r` for interior `r`.
Source: none: infrastructure. Kind: L -/
theorem amd_last_nu_pos (r : ℚ) (h0 : 0 < r) (h1 : r < 1) (a : Act2) :
    0 < nu (procQ r h0.le h1.le) amd (amdActEvLast () a ∩ amdObs ()) := by
  rw [amdObs, Finset.inter_univ, amd_nu]
  cases a <;> simp [amdActEvLast, procQ] <;> nlinarith

/-- The last-draw comparison at label `r ∈ (0,1)`: `v(b) ≤ v(a) ↔ r ≤ 2/3`, `v(a) ≤ v(b) ↔ 2/3 ≤ r`.
Source: `calibration.md` CA-14′ ("tie only at `q_ε = 2/3`"). Kind: L -/
theorem amd_last_compare (r : ℚ) (h0 : 0 < r) (h1 : r < 1) :
    (1 ≤ 4 * (1 - r) / (2 - r) ↔ r ≤ 2 / 3) ∧ (4 * (1 - r) / (2 - r) ≤ 1 ↔ 2 / 3 ≤ r) := by
  have h2 : (0 : ℚ) < 2 - r := by linarith
  constructor
  · rw [le_div_iff₀ h2]; constructor <;> intro h <;> linarith
  · rw [div_le_iff₀ h2]; constructor <;> intro h <;> linarith

/-- **D2 on the AMD with last-draw events is empty, for every `q ∈ [0,1]`**: a mixed label
would tie at `q_ε = 2/3` for two tremble sizes (forcing `q = ½`), `δ_a` needs `1 − ε/2 ≤ 2/3`,
`δ_b` needs `2/3 ≤ ε/2` — all false for small `ε`.
Source: `calibration.md` CA-14′ ("tie only at `q_ε = 2/3`, impossible for all `ε`: D2 = ∅"),
CA-20′ (D2 row, AMD: "none"); dp-cf-047; known issue 4 (universal, not four sample points)
Kind: P
Fidelity: exact (last-draw encoding, named; universal in `q`)
Hyps: (a) `0 ≤ q ≤ 1` -/
theorem amd_last_not_eventTremble (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ¬ EventTrembleEdtConsistent amdObs amdActEvLast (procQ q hq0 hq1) amd := by
  rintro ⟨ε₀, hε₀, hD2⟩
  have key : ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε < 1), ε < ε₀ → ∀ a, 0 < (procQ q hq0 hq1 ()).w a →
      ∀ b, condExp (tremble (procQ q hq0 hq1) ε h0.le h1.le) amd (amdActEvLast () b ∩ amdObs ()) ≤
        condExp (tremble (procQ q hq0 hq1) ε h0.le h1.le) amd (amdActEvLast () a ∩ amdObs ()) := by
    intro ε h0 h1 hlt a ha b
    obtain ⟨hi0, hi1⟩ := qeps_interior q ε hq0 hq1 h0 h1
    have hlive : ∀ b, 0 < nu (tremble (procQ q hq0 hq1) ε h0.le h1.le) amd
        (amdActEvLast () b ∩ amdObs ()) := by
      intro b; rw [tremble_procQ]; exact amd_last_nu_pos _ hi0 hi1 b
    obtain ⟨-, hcmp⟩ := hD2 ε h0 h1.le hlt () amd_queried_mem (amd_nuPoly_obs_ne_zero _)
      ⟨.a, hlive .a⟩ a ha
    exact hcmp b (hlive b)
  have vals : ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε < 1),
      condExp (tremble (procQ q hq0 hq1) ε h0.le h1.le) amd (amdActEvLast () .a ∩ amdObs ()) =
        4 * (1 - ((1 - ε) * q + ε / 2)) / (2 - ((1 - ε) * q + ε / 2)) ∧
      condExp (tremble (procQ q hq0 hq1) ε h0.le h1.le) amd (amdActEvLast () .b ∩ amdObs ()) = 1 := by
    intro ε h0 h1
    rw [tremble_procQ]
    obtain ⟨hi0, hi1⟩ := qeps_interior q ε hq0 hq1 h0 h1
    exact amd_last_condExp _ hi0 hi1
  set ε₁ : ℚ := min ε₀ 1 / 4 with hε₁
  set ε₂ : ℚ := min ε₀ 1 / 8 with hε₂
  have hmin0 : 0 < min ε₀ 1 := lt_min hε₀ one_pos
  have hmin1 : min ε₀ 1 ≤ 1 := min_le_right _ _
  have hmin2 : min ε₀ 1 ≤ ε₀ := min_le_left _ _
  have h10 : 0 < ε₁ := by rw [hε₁]; linarith
  have h11 : ε₁ < 1 := by rw [hε₁]; linarith
  have h1lt : ε₁ < ε₀ := by rw [hε₁]; linarith
  have h20 : 0 < ε₂ := by rw [hε₂]; linarith
  have h21 : ε₂ < 1 := by rw [hε₂]; linarith
  have h2lt : ε₂ < ε₀ := by rw [hε₂]; linarith
  have hne : ε₁ ≠ ε₂ := by rw [hε₁, hε₂]; intro h; linarith
  obtain ⟨va1, vb1⟩ := vals ε₁ h10 h11
  obtain ⟨va2, vb2⟩ := vals ε₂ h20 h21
  obtain ⟨c1a, c1b⟩ := amd_last_compare _ (qeps_interior q ε₁ hq0 hq1 h10 h11).1
    (qeps_interior q ε₁ hq0 hq1 h10 h11).2
  obtain ⟨c2a, c2b⟩ := amd_last_compare _ (qeps_interior q ε₂ hq0 hq1 h20 h21).1
    (qeps_interior q ε₂ hq0 hq1 h20 h21).2
  rcases (lt_or_eq_of_le hq0) with hpos | hzero
  · rcases (lt_or_eq_of_le hq1) with hlt1 | hone
    · have ha1 := key ε₁ h10 h11 h1lt .a (by simp [procQ, hpos]) .b
      have hb1 := key ε₁ h10 h11 h1lt .b (by simp [procQ]; linarith) .a
      have ha2 := key ε₂ h20 h21 h2lt .a (by simp [procQ, hpos]) .b
      have hb2 := key ε₂ h20 h21 h2lt .b (by simp [procQ]; linarith) .a
      rw [va1, vb1] at ha1 hb1
      rw [va2, vb2] at ha2 hb2
      have t1 : (1 - ε₁) * q + ε₁ / 2 = 2 / 3 := le_antisymm (c1a.mp ha1) (c1b.mp hb1)
      have t2 : (1 - ε₂) * q + ε₂ / 2 = 2 / 3 := le_antisymm (c2a.mp ha2) (c2b.mp hb2)
      have hq : q = 1 / 2 := by
        have : (ε₂ - ε₁) * (q - 1 / 2) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd (by linarith : ε₁ = ε₂) hne
        · linarith
      rw [hq] at t1
      linarith
    · subst hone
      have ha1 := key ε₁ h10 h11 h1lt .a (by simp [procQ]) .b
      rw [va1, vb1] at ha1
      have := c1a.mp ha1
      linarith
  · subst hzero
    have hb1 := key ε₁ h10 h11 h1lt .b (by simp [procQ]) .a
    rw [va1, vb1] at hb1
    have := c1b.mp hb1
    linarith

/-! ## First-draw events -/

/-- **The first-draw act-conditional values under `procQ r`**, `0 < r < 1`: `v(a) = 0`,
`v(b) = 3r + 1`.
Source: `calibration.md` CA-14′ ("AMD **with first-draw action events**: `v_ε(a) = 0`,
`v_ε(b) = 3q_ε + 1`")
Kind: P
Fidelity: exact -/
theorem amd_first_condExp (r : ℚ) (h0 : 0 < r) (h1 : r < 1) :
    condExp (procQ r h0.le h1.le) amd (amdActEvFirst () .a ∩ amdObs ()) = 0 ∧
    condExp (procQ r h0.le h1.le) amd (amdActEvFirst () .b ∩ amdObs ()) = 3 * r + 1 := by
  simp only [condExp, amdObs, Finset.inter_univ, amd_nu, amd_paySum, amdActEvFirst, procQ,
    FinDistr.act2_a, FinDistr.act2_b]
  simp
  have h1' : (0 : ℚ) < 1 - r := by linarith
  rw [div_eq_iff (by nlinarith)]
  ring

/-- Both first-draw act events are realized for interior `r`. Source: none: infrastructure.
Kind: L -/
theorem amd_first_nu_pos (r : ℚ) (h0 : 0 < r) (h1 : r < 1) (a : Act2) :
    0 < nu (procQ r h0.le h1.le) amd (amdActEvFirst () a ∩ amdObs ()) := by
  rw [amdObs, Finset.inter_univ, amd_nu]
  cases a <;> simp [amdActEvFirst, procQ] <;> nlinarith

/-- **D2 on the AMD with first-draw events is exactly `δ_b`**: `v(b) = 3q_ε + 1 > 0 = v(a)` at
every tremble, so `a` may not be in the support.
Source: `calibration.md` CA-14′ ("AMD **with first-draw action events** … D2 = D4 = {δ_b}");
dp-cf-047
Kind: P
Fidelity: exact (first-draw encoding, named; universal in `q`)
Hyps: (a) `0 ≤ q ≤ 1` -/
theorem amd_first_eventTremble_iff (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    EventTrembleEdtConsistent amdObs amdActEvFirst (procQ q hq0 hq1) amd ↔ q = 0 := by
  constructor
  · rintro ⟨ε₀, hε₀, hD2⟩
    by_contra hq
    have hpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    have hmin0 : 0 < min ε₀ 1 := lt_min hε₀ one_pos
    have h0 : 0 < min ε₀ 1 / 2 := by linarith
    have h1 : min ε₀ 1 / 2 < 1 := by linarith [min_le_right ε₀ 1]
    have hlt : min ε₀ 1 / 2 < ε₀ := by linarith [min_le_left ε₀ 1]
    obtain ⟨hi0, hi1⟩ := qeps_interior q _ hq0 hq1 h0 h1
    have hlive : ∀ b, 0 < nu (tremble (procQ q hq0 hq1) _ h0.le h1.le) amd
        (amdActEvFirst () b ∩ amdObs ()) := by
      intro b; rw [tremble_procQ]; exact amd_first_nu_pos _ hi0 hi1 b
    obtain ⟨-, hcmp⟩ := hD2 _ h0 h1.le hlt () amd_queried_mem (amd_nuPoly_obs_ne_zero _)
      ⟨.a, hlive .a⟩ .a (by simp [procQ, hpos])
    have := hcmp .b (hlive .b)
    rw [tremble_procQ] at this
    obtain ⟨va, vb⟩ := amd_first_condExp _ hi0 hi1
    rw [va, vb] at this
    linarith
  · rintro rfl
    refine ⟨1/2, by norm_num, fun ε h0 h1 hlt d _ _ _ a ha => ?_⟩
    cases d
    have h1' : ε < 1 := by linarith
    obtain ⟨hi0, hi1⟩ := qeps_interior 0 ε hq0 hq1 h0 h1'
    have hlive : ∀ b, 0 < nu (tremble (procQ 0 hq0 hq1) ε h0.le h1) amd
        (amdActEvFirst () b ∩ amdObs ()) := by
      intro b; rw [tremble_procQ]; exact amd_first_nu_pos _ hi0 hi1 b
    cases a
    · simp [procQ] at ha
    · refine ⟨hlive .b, fun b _ => ?_⟩
      rw [tremble_procQ]
      obtain ⟨va, vb⟩ := amd_first_condExp _ hi0 hi1
      cases b
      · rw [va, vb]; linarith
      · exact le_rfl

/-! ## D3 with `ε > 0`: none, encoding-free -/

/-- **D3 (`ε > 0`) on the AMD is empty, for every `q ∈ [0,1]`**: Theorem 1's functional under
`procQ r` is `4(1−r)` vs `2 + 2r`, tying only at `r = ⅓`; a mixed label would tie at two tremble
sizes (forcing `q = ½`), `δ_a` needs `1 − ε/2 ≤ ⅓`, `δ_b` needs `⅓ ≤ ε/2`.
Source: `calibration.md` CA-20′ (D3 row, AMD: "none (`133/50` vs `267/100`)") — the source's
cell is one `ε`; this is the universal
Kind: P
Fidelity: exact (universal in `q`; encoding-free — D3 conditions on the draw)
Hyps: (a) `0 ≤ q ≤ 1` -/
theorem amd_not_occTremble (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ¬ OccTrembleEdtConsistent (procQ q hq0 hq1) amd := by
  rw [occTrembleEdtConsistent_iff]
  rintro ⟨ε₀, hε₀, h⟩
  have vals : ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε ≤ 1),
      siaSum (tremble (procQ q hq0 hq1) ε h0.le h1) amd () .a = 4 * (1 - ((1 - ε) * q + ε / 2)) ∧
      siaSum (tremble (procQ q hq0 hq1) ε h0.le h1) amd () .b = 2 + 2 * ((1 - ε) * q + ε / 2) := by
    intro ε h0 h1
    rw [tremble_procQ]
    exact ⟨amd_siaSum_a _ _ _, amd_siaSum_b _ _ _⟩
  set ε₁ : ℚ := min ε₀ 1 / 4 with hε₁
  set ε₂ : ℚ := min ε₀ 1 / 8 with hε₂
  have hmin0 : 0 < min ε₀ 1 := lt_min hε₀ one_pos
  have hmin1 : min ε₀ 1 ≤ 1 := min_le_right _ _
  have hmin2 : min ε₀ 1 ≤ ε₀ := min_le_left _ _
  have h10 : 0 < ε₁ := by rw [hε₁]; linarith
  have h11 : ε₁ ≤ 1 := by rw [hε₁]; linarith
  have h1lt : ε₁ < ε₀ := by rw [hε₁]; linarith
  have h20 : 0 < ε₂ := by rw [hε₂]; linarith
  have h21 : ε₂ ≤ 1 := by rw [hε₂]; linarith
  have h2lt : ε₂ < ε₀ := by rw [hε₂]; linarith
  have hne : ε₁ ≠ ε₂ := by rw [hε₁, hε₂]; intro h; linarith
  obtain ⟨va1, vb1⟩ := vals ε₁ h10 h11
  obtain ⟨va2, vb2⟩ := vals ε₂ h20 h21
  rcases (lt_or_eq_of_le hq0) with hpos | hzero
  · rcases (lt_or_eq_of_le hq1) with hlt1 | hone
    · have ha1 := h ε₁ h10 h11 h1lt () amd_queried_mem .a (by simp [procQ, hpos]) .b
      have hb1 := h ε₁ h10 h11 h1lt () amd_queried_mem .b (by simp [procQ]; linarith) .a
      have ha2 := h ε₂ h20 h21 h2lt () amd_queried_mem .a (by simp [procQ, hpos]) .b
      have hb2 := h ε₂ h20 h21 h2lt () amd_queried_mem .b (by simp [procQ]; linarith) .a
      rw [va1, vb1] at ha1 hb1
      rw [va2, vb2] at ha2 hb2
      have t1 : (1 - ε₁) * q + ε₁ / 2 = 1 / 3 := by linarith
      have t2 : (1 - ε₂) * q + ε₂ / 2 = 1 / 3 := by linarith
      have hq : q = 1 / 2 := by
        have : (ε₂ - ε₁) * (q - 1 / 2) = 0 := by linarith
        rcases mul_eq_zero.mp this with h' | h'
        · exact absurd (by linarith : ε₁ = ε₂) hne
        · linarith
      rw [hq] at t1
      linarith
    · subst hone
      have ha1 := h ε₁ h10 h11 h1lt () amd_queried_mem .a (by simp [procQ]) .b
      rw [va1, vb1] at ha1
      linarith
  · subst hzero
    have hb1 := h ε₁ h10 h11 h1lt () amd_queried_mem .b (by simp [procQ]) .a
    rw [va1, vb1] at hb1
    linarith

/-- The source's D3 cell at `q = ⅓`, `ε = 1/100`: `133/50` vs `267/100` — the untrembled tie
`8/3 = 8/3` is broken by the tremble (one `ε`; the universal is `amd_not_occTremble`).
Source: `calibration.md` CA-14′/CA-20′ ("`133/50` vs `267/100` at `ε = 1/100`")
Kind: N+ -/
theorem amd_d3_at_hundredth :
    siaSum (tremble (procQ (1/3) (by norm_num) (by norm_num)) (1/100) (by norm_num) (by norm_num))
      amd () .a = 133/50 ∧
    siaSum (tremble (procQ (1/3) (by norm_num) (by norm_num)) (1/100) (by norm_num) (by norm_num))
      amd () .b = 267/100 ∧
    siaSum (procQ (1/3) (by norm_num) (by norm_num)) amd () .a = 8/3 ∧
    siaSum (procQ (1/3) (by norm_num) (by norm_num)) amd () .b = 8/3 := by
  rw [tremble_procQ, amd_siaSum_a, amd_siaSum_b, amd_siaSum_a, amd_siaSum_b]
  norm_num

end Cleanroom.Decision.DpDevicesCatalog
