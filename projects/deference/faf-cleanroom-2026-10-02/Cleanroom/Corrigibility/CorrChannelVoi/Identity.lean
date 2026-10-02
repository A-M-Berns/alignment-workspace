import Cleanroom.Corrigibility.CorrChannelVoi.TwoStateForms

/-!
# `corr-channel-voi` — Identity: the channel identity (T2) and the bound made tight (E1)

**T2.** `VOI(perfect | k) + VOI(k) = E_μ[max(X, 0)] − max(E_μ[X], 0)` for every prior, stakes
and channel (`channel_identity_general`); on `twoState` the right side is `min(εh, (1−ε)c)`,
regime-free (`twoState_channel_identity`), with the source's `εh` / `(1−ε)c` as regime
corollaries, the heeded-regime form `VOI(scan | button) = (1−ε)αc + ε(1−β)h`, its vanishing
iff the button is perfect, and the exact evaluation at `ε = ε*`.

**E1.** On `twoState` the bound `VOI(k) ≤ min(εh, (1−ε)c)` (T3) is attained iff every signal of
`k` is supported in one world (`twoState_attains_iff`); a binary sensor attains it iff it is
perfect or perfectly inverted; a three-signal split of `right` attains it.
-/

namespace Cleanroom.Corrigibility.CorrChannelVoi

open Finset hiding expect
open FactoredSpaces
open Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Trust.TtFiniteFrames
open Cleanroom.Found.CorrThreeStep
open Cleanroom.Found.CorrThreeStep.ThreeStep

noncomputable section

set_option linter.unusedSectionVars false

variable {W S : Type} [Fintype W] [Fintype S]

/-! ## T2. The channel identity -/

/-- **T2, general form: the channel identity.** For every prior `μ`, stakes `X` and channel `k`,
`VOI(perfect | k) + VOI(k) = E_μ[max(X, 0)] − max(E_μ[X], 0)`: the perfect scan buys exactly the
residual the channel leaves, and the two together are worth the value of perfect information.
Regime-free; no two-state structure used.
Source: [[corr-wf14-inventory]] 037 item 7 ("the identity"), item 10 (the other regime); stated here for general `W`
Kind: C (telescoping over D2's Blackwell equivalence `sensorValue_prod_perfect` and `sensorValue_perfect`; regraded from P in audit r1 — the content is D2's equivalence and the two closed forms)
Fidelity: stronger: general prior and stakes, both regimes at once
Hyps: (a) none -/
theorem channel_identity_general [DecidableEq W] [DecidableEq S] (μ : Distr W) (k : Experiment W S)
    (X : W → ℝ) :
    voiGiven μ k perfectExp X + voiSensor μ k X =
      expect μ (fun w => max (X w) 0) - max (expect μ X) 0 := by
  rw [voiGiven, voiSensor, sensorValue_prod_perfect, sensorValue_perfect]; ring

section TwoState

variable (ε α β c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
  (hβ : β ∈ Set.Icc (0 : ℝ) 1)

/-- The two-state value of perfect information is `min(εh, (1−ε)c)` (for `c, h ≥ 0`).
Source: [[corr-wf14-inventory]] 037 items 7, 10
Kind: L
Fidelity: exact -/
theorem twoState_vopi (hc : 0 ≤ c) (hh : 0 ≤ h) :
    expect (twoPoint ε hε) (fun w => max (twoValue c h .cont w) 0) -
      max (expect (twoPoint ε hε) (twoValue c h .cont)) 0 = min (ε * h) ((1 - ε) * c) := by
  rw [twoPoint_expect_max_stakes ε c h hε hc hh, twoPoint_expect_stakes]
  rcases le_total ((1 - ε) * c - ε * h) 0 with h0 | h0
  · rw [max_eq_right h0, min_eq_right (by linarith)]; ring
  · rw [max_eq_left h0, min_eq_left (by linarith)]; ring

/-- **T3 on `twoState` (load-bearing 2), as one statement**: every finite experiment about the
two-state world, of any signal type `S`, is worth at most `min(εh, (1−ε)c)` (`c, h ≥ 0`). The
general bound `voiSensor_le_vopi` at the two-state VOPI; attained by `perfectExp`
(`voiSensor_perfect`, `Witnesses.w_perfect_attains`) and by exactly the experiments of E1.
Source: [[corr-wf14-inventory]] 037 item 9; 2-011(a); wentworth §2.4 ("every channel is worth at most `εh`")
Kind: C (T3 general + `twoState_vopi`)
Fidelity: exact
Hyps: (a) none beyond `c, h ≥ 0` -/
theorem twoState_voiSensor_le_min {S : Type} [Fintype S] [DecidableEq S] (hc : 0 ≤ c) (hh : 0 ≤ h)
    (k : Experiment World S) :
    voiSensor (twoPoint ε hε) k (twoValue c h .cont) ≤ min (ε * h) ((1 - ε) * c) := by
  have := voiSensor_le_vopi (twoPoint ε hε) k (twoValue c h .cont)
  rwa [twoState_vopi ε c h hε hc hh] at this

/-- **T2 (load-bearing 1). The channel identity on `twoState`, regime-free**:
`VOI(scan | button) + VOI(button) = min(εh, (1−ε)c)`, for `c, h ≥ 0`. The source's `εh` is the
continue-by-default regime (`twoState_channel_identity_of_le`) and its `(1−ε)c` the other
(`twoState_channel_identity_of_ge`).
Source: [[corr-wf14-inventory]] 037 items 7 and 10; substitution.md R2
Kind: C (the general identity plus the two-state closed forms)
Fidelity: stronger: one regime-free statement in place of the source's two regime forms
Hyps: (a) none beyond `c, h ≥ 0` -/
theorem twoState_channel_identity (hc : 0 ≤ c) (hh : 0 ≤ h) :
    voiGiven (twoPoint ε hε) (twoButton α β hα hβ) perfectExp (twoValue c h .cont) +
      voiSensor (twoPoint ε hε) (twoButton α β hα hβ) (twoValue c h .cont) =
        min (ε * h) ((1 - ε) * c) := by
  rw [channel_identity_general, twoState_vopi ε c h hε hc hh]

/-- **T2, continue-by-default corollary**: `εh ≤ (1−ε)c → VOI(scan | button) + VOI(button) = εh`.
Source: [[corr-wf14-inventory]] 037 item 7
Kind: L
Fidelity: exact -/
theorem twoState_channel_identity_of_le (hc : 0 ≤ c) (hh : 0 ≤ h) (hle : ε * h ≤ (1 - ε) * c) :
    voiGiven (twoPoint ε hε) (twoButton α β hα hβ) perfectExp (twoValue c h .cont) +
      voiSensor (twoPoint ε hε) (twoButton α β hα hβ) (twoValue c h .cont) = ε * h := by
  rw [twoState_channel_identity ε α β c h hε hα hβ hc hh, min_eq_left hle]

/-- **T2, shut-down-by-default corollary**: `(1−ε)c ≤ εh → VOI(scan | button) + VOI(button) = (1−ε)c`.
Source: [[corr-wf14-inventory]] 037 item 10
Kind: L
Fidelity: exact -/
theorem twoState_channel_identity_of_ge (hc : 0 ≤ c) (hh : 0 ≤ h) (hge : (1 - ε) * c ≤ ε * h) :
    voiGiven (twoPoint ε hε) (twoButton α β hα hβ) perfectExp (twoValue c h .cont) +
      voiSensor (twoPoint ε hε) (twoButton α β hα hβ) (twoValue c h .cont) = (1 - ε) * c := by
  rw [twoState_channel_identity ε α β c h hε hα hβ hc hh, min_eq_right hge]

/-- `VOI(scan | button)` on `twoState`, regime-free: `(1−ε)c − 𝒱(button)`.
Source: [[corr-wf14-inventory]] 037 item 6
Kind: L
Fidelity: exact -/
theorem twoState_voiGiven_perfect (hc : 0 ≤ c) (hh : 0 ≤ h) :
    voiGiven (twoPoint ε hε) (twoButton α β hα hβ) perfectExp (twoValue c h .cont) =
      (1 - ε) * c - (max ((1 - ε) * α * c - ε * β * h) 0 +
        max ((1 - ε) * (1 - α) * c - ε * (1 - β) * h) 0) := by
  rw [voiGiven, sensorValue_prod_perfect, twoState_sensorValue_perfect ε c h hε hc hh,
    twoState_sensorValue_button]

/-- **T2, the heeded regime**: under `Δ₋ ≥ 0 ∧ Δ₊ ≥ 0` (product form),
`VOI(scan | button) = (1−ε)αc + ε(1−β)h` — the false-press loss plus the missed-press loss.
Source: [[corr-wf14-inventory]] 037 item 6; legitimacy.md R3 item 1; armstrong.md §2 claim 2
Kind: C
Fidelity: exact
Hyps: (a) the regime named in product form -/
theorem twoState_voiGiven_heeded (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hminus : 0 ≤ ε * β * h - (1 - ε) * α * c)
    (hplus : 0 ≤ (1 - ε) * (1 - α) * c - ε * (1 - β) * h) :
    voiGiven (twoPoint ε hε) (twoButton α β hα hβ) perfectExp (twoValue c h .cont) =
      (1 - ε) * α * c + ε * (1 - β) * h := by
  rw [twoState_voiGiven_perfect ε α β c h hε hα hβ hc hh, max_eq_right (by linarith),
    max_eq_left hplus]
  ring

/-- **T2, the discounted regime**: under `Δ₋ ≤ 0` and `Δ₊ ≥ 0` (product form),
`VOI(scan | button) = εh` — the button is worth nothing and the scan is worth everything.
**Deviation from the mandate's shape:** the mandate names `Δ₋ ≤ 0 ∧ E[X] ≥ 0`; `E[X] ≥ 0` is
not needed (it follows: `−Δ₋ + Δ₊ = E[X]`), but `Δ₊ ≥ 0` is — without it the statement is false
(the inverted sensor `Δ₋ ≤ 0 ∧ Δ₊ < 0` has `VOI(button) = −Δ₊ > 0`). Under the source's
standing `α ≤ β`, `Δ₊ ≥ 0` follows from `E[X] ≥ 0` (`twoState_voiGiven_discounted_of_le`).
Source: [[corr-wf14-inventory]] 037 item 6 ("`εh` when it is discounted")
Kind: C
Fidelity: exact (with the hypothesis the source's `β > α` supplies)
Hyps: (a) the regime named in product form -/
theorem twoState_voiGiven_discounted (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hminus : ε * β * h - (1 - ε) * α * c ≤ 0)
    (hplus : 0 ≤ (1 - ε) * (1 - α) * c - ε * (1 - β) * h) :
    voiGiven (twoPoint ε hε) (twoButton α β hα hβ) perfectExp (twoValue c h .cont) = ε * h := by
  rw [twoState_voiGiven_perfect ε α β c h hε hα hβ hc hh, max_eq_left (by linarith),
    max_eq_left hplus]
  ring

include hε hα in
/-- Under `α ≤ β`, continue-by-default (`εh ≤ (1−ε)c`) gives `Δ₊ ≥ 0` in product form.
Source: [[corr-wf13-2-inventory]] 066 / wentworth.md §2.4 (`corr-three-step`'s `twoState_regime_of_threshold`, product form)
Kind: L
Fidelity: exact -/
theorem deltaPlus_nonneg_of_le (hαβ : α ≤ β) (hh : 0 ≤ h)
    (hprior : ε * h ≤ (1 - ε) * c) :
    0 ≤ (1 - ε) * (1 - α) * c - ε * (1 - β) * h := by
  have h1 : ε * (1 - β) * h ≤ ε * (1 - α) * h := by
    have := mul_nonneg hε.1 hh
    nlinarith
  have h2 : ε * (1 - α) * h ≤ (1 - ε) * (1 - α) * c := by
    have := sub_nonneg.mpr hα.2
    nlinarith
  linarith

/-- **T2, the discounted regime under the source's `α ≤ β`**: `Δ₋ ≤ 0 ∧ εh ≤ (1−ε)c → VOI(scan | button) = εh`.
Source: [[corr-wf14-inventory]] 037 item 6
Kind: C
Fidelity: exact -/
theorem twoState_voiGiven_discounted_of_le (hc : 0 ≤ c) (hh : 0 ≤ h) (hαβ : α ≤ β)
    (hminus : ε * β * h - (1 - ε) * α * c ≤ 0) (hprior : ε * h ≤ (1 - ε) * c) :
    voiGiven (twoPoint ε hε) (twoButton α β hα hβ) perfectExp (twoValue c h .cont) = ε * h :=
  twoState_voiGiven_discounted ε α β c h hε hα hβ hc hh hminus
    (deltaPlus_nonneg_of_le ε α β c h hε hα hαβ hh hprior)

/-- **T2, when the residual vanishes**: in the heeded regime with `0 < ε < 1` and `0 < c, h`,
`VOI(scan | button) = 0 ↔ α = 0 ∧ β = 1` — the scan adds nothing iff the button is perfect.
Source: [[corr-wf14-inventory]] 037 item 6 ("zero iff the button is perfect")
Kind: P
Fidelity: exact
Hyps: (a) the regime and the positivity named -/
theorem twoState_voiGiven_heeded_eq_zero_iff (hε0 : 0 < ε) (hε1 : ε < 1) (hc : 0 < c) (hh : 0 < h)
    (hminus : 0 ≤ ε * β * h - (1 - ε) * α * c)
    (hplus : 0 ≤ (1 - ε) * (1 - α) * c - ε * (1 - β) * h) :
    voiGiven (twoPoint ε hε) (twoButton α β hα hβ) perfectExp (twoValue c h .cont) = 0 ↔
      α = 0 ∧ β = 1 := by
  rw [twoState_voiGiven_heeded ε α β c h hε hα hβ hc.le hh.le hminus hplus]
  have h1 : 0 ≤ (1 - ε) * α * c := mul_nonneg (mul_nonneg (by linarith) hα.1) hc.le
  have h2 : 0 ≤ ε * (1 - β) * h := mul_nonneg (mul_nonneg hε0.le (by linarith [hβ.2])) hh.le
  have hk1 : 0 < (1 - ε) * c := mul_pos (by linarith) hc
  have hk2 : 0 < ε * h := mul_pos hε0 hh
  constructor
  · intro H
    have e1 : (1 - ε) * α * c = 0 := by linarith
    have e2 : ε * (1 - β) * h = 0 := by linarith
    constructor
    · have : (1 - ε) * c * α = 0 := by linarith [e1]
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hk1.ne'
      · exact h0
    · have : ε * h * (1 - β) = 0 := by linarith [e2]
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hk2.ne'
      · linarith
  · rintro ⟨rfl, rfl⟩; ring

/-- At `ε = ε*` the press half vanishes: `(1 − ε*)αc = ε*βh`.
Source: [[corr-wf13-inventory]] 004 (`ε*` as the boundary)
Kind: L
Fidelity: exact -/
theorem epsStar_balance (hpos : 0 < α * c + β * h) :
    (1 - epsStar α β c h) * α * c = epsStar α β c h * β * h := by
  unfold epsStar
  field_simp
  ring

/-- **T2, the boundary sentence as an exact evaluation**: at `ε = ε*` (`αc + βh > 0`, `α ≤ β`,
`α, β, c, h ≥ 0`), `VOI(button) = 0` and `VOI(scan | button) = ε*·h` — the source's "as `ε` falls
toward `ε*`, `VOI(button) → 0` while `VOI(scan | button) → ε*h`" holds at the point itself,
regime-free. (`α ≤ β` is what makes `ε*h ≤ (1−ε*)c`; with `β < α` the second value is
`(1−ε*)c` instead.)
Source: [[corr-wf14-inventory]] 037 item 7 (the limit sentence)
Kind: P
Fidelity: stronger: exact at the point, not a limit
Hyps: (a) as stated; `α ≤ β` is the source's standing assumption, named here -/
theorem twoState_at_epsStar (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hpos : 0 < α * c + β * h) (hαβ : α ≤ β) :
    voiSensor (twoPoint (epsStar α β c h) (epsStar_mem_Icc α β c h hα0 hβ0 hc hh hpos))
        (twoButton α β hα hβ) (twoValue c h .cont) = 0 ∧
      voiGiven (twoPoint (epsStar α β c h) (epsStar_mem_Icc α β c h hα0 hβ0 hc hh hpos))
        (twoButton α β hα hβ) perfectExp (twoValue c h .cont) = epsStar α β c h * h := by
  have hbal := epsStar_balance α β c h hpos
  set e := epsStar α β c h with he
  have hvoi : voiSensor (twoPoint e (epsStar_mem_Icc α β c h hα0 hβ0 hc hh hpos))
      (twoButton α β hα hβ) (twoValue c h .cont) = 0 := by
    rw [twoState_voiSensor_button]
    have e0 : (1 - e) * α * c - e * β * h = 0 := by linarith
    rw [e0, max_self]
    have e1 : (1 - e) * c - e * h = (1 - e) * (1 - α) * c - e * (1 - β) * h := by linarith
    rw [e1]; ring
  refine ⟨hvoi, ?_⟩
  have hid := twoState_channel_identity e α β c h (epsStar_mem_Icc α β c h hα0 hβ0 hc hh hpos)
    hα hβ hc hh
  rw [hvoi, add_zero] at hid
  rw [hid, min_eq_left]
  have hden : 0 < α * c + β * h := hpos
  have : e * h * (α * c + β * h) ≤ (1 - e) * c * (α * c + β * h) := by
    have hl : e * (α * c + β * h) = α * c := by
      rw [he, epsStar]; field_simp
    have hr : (1 - e) * (α * c + β * h) = β * h := by
      rw [he, epsStar]; field_simp; ring
    calc e * h * (α * c + β * h) = α * c * h := by rw [mul_right_comm e h, hl]
      _ ≤ β * h * c := by nlinarith [mul_nonneg hc hh]
      _ = (1 - e) * c * (α * c + β * h) := by
          rw [mul_right_comm (1 - e) c (α * c + β * h), hr]
  exact le_of_mul_le_mul_right this hden

end TwoState

/-! ## E1. The channel bound made tight -/

/-- `max(a − b, 0) = a ↔ a = 0 ∨ b = 0` for `a, b ≥ 0`.
Source: none: infrastructure (E1's per-signal step)
Kind: L
Fidelity: n/a -/
theorem max_sub_eq_self_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max (a - b) 0 = a ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    rcases le_total (a - b) 0 with h0 | h0
    · rw [max_eq_right h0] at h; exact Or.inl h.symm
    · rw [max_eq_left h0] at h; exact Or.inr (by linarith)
  · rintro (rfl | rfl)
    · rw [zero_sub, max_eq_right (neg_nonpos.mpr hb)]
    · rw [sub_zero, max_eq_left ha]

section Tight

variable (ε c h : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1)

/-- The right-world part of every signal gain: `𝒱(k) ≤ ∑ s, (1−ε)c·k right s = (1−ε)c`, with the
per-signal inequality `max((1−ε)c·k_R(s) − εh·k_W(s), 0) ≤ (1−ε)c·k_R(s)`.
Source: none: infrastructure (E1)
Kind: L
Fidelity: n/a -/
theorem twoState_signalGain_eq (k : Experiment World S) (s : S) :
    signalGain (twoPoint ε hε) k (twoValue c h .cont) s =
      (1 - ε) * c * k.k .right s - ε * h * k.k .wrong s := by
  simp only [signalGain, World.sum_eq, twoPoint_right, twoPoint_wrong, twoValue]; ring

/-- **E1 (the bound made tight).** On `twoState` with `0 < ε < 1`, `0 < c, h`, for every finite
experiment `k`: `𝒱(k) = (1−ε)c` (the perfect-information value) iff every signal of `k` is
supported in one world, `∀ s, k right s = 0 ∨ k wrong s = 0`.
Source: [[corr-channel-voi-mandate]] E1
Kind: P
Fidelity: exact
Hyps: (a) none beyond the positivity -/
theorem twoState_attains_iff [DecidableEq S] (hε0 : 0 < ε) (hε1 : ε < 1) (hc : 0 < c) (hh : 0 < h)
    (k : Experiment World S) :
    sensorValue (twoPoint ε hε) k (twoValue c h .cont) = (1 - ε) * c ↔
      ∀ s, k.k .right s = 0 ∨ k.k .wrong s = 0 := by
  have hA : 0 < (1 - ε) * c := mul_pos (by linarith) hc
  have hB : 0 < ε * h := mul_pos hε0 hh
  have hrow : ∑ s, (1 - ε) * c * k.k .right s = (1 - ε) * c := by
    rw [← Finset.mul_sum, (k.k_mem .right).2, mul_one]
  have hle : ∀ s ∈ (univ : Finset S), max (signalGain (twoPoint ε hε) k (twoValue c h .cont) s) 0 ≤
      (1 - ε) * c * k.k .right s := fun s _ => by
    rw [twoState_signalGain_eq]
    refine max_le (by linarith [mul_nonneg hB.le ((k.k_mem .wrong).1 s)])
      (mul_nonneg hA.le ((k.k_mem .right).1 s))
  rw [sensorValue_eq_sum_max, ← hrow, Finset.sum_eq_sum_iff_of_le hle]
  constructor
  · intro H s
    have := H s (mem_univ s)
    rw [twoState_signalGain_eq, max_sub_eq_self_iff (mul_nonneg hA.le ((k.k_mem .right).1 s))
      (mul_nonneg hB.le ((k.k_mem .wrong).1 s))] at this
    rcases this with h0 | h0
    · exact Or.inl ((mul_eq_zero.mp h0).resolve_left hA.ne')
    · exact Or.inr ((mul_eq_zero.mp h0).resolve_left hB.ne')
  · intro H s _
    rw [twoState_signalGain_eq, max_sub_eq_self_iff (mul_nonneg hA.le ((k.k_mem .right).1 s))
      (mul_nonneg hB.le ((k.k_mem .wrong).1 s))]
    rcases H s with h0 | h0
    · exact Or.inl (by rw [h0, mul_zero])
    · exact Or.inr (by rw [h0, mul_zero])

/-- **E1 in `VOI` form**: `VOI(k) = min(εh, (1−ε)c) ↔ 𝒱(k) = (1−ε)c` (for `c, h ≥ 0`), so the
T3 bound is attained exactly by the experiments of `twoState_attains_iff`.
Source: [[corr-channel-voi-mandate]] E1
Kind: L
Fidelity: exact -/
theorem twoState_voi_attains_iff [DecidableEq S] (hc : 0 ≤ c) (hh : 0 ≤ h) (k : Experiment World S) :
    voiSensor (twoPoint ε hε) k (twoValue c h .cont) = min (ε * h) ((1 - ε) * c) ↔
      sensorValue (twoPoint ε hε) k (twoValue c h .cont) = (1 - ε) * c := by
  rw [voiSensor, ← twoState_vopi ε c h hε hc hh, twoPoint_expect_max_stakes ε c h hε hc hh]
  constructor <;> intro H <;> linarith

/-- **E1, corollary: which binary sensors attain the bound.** With `0 < ε < 1`, `0 < c, h`, the
button `(α, β)` attains `𝒱 = (1−ε)c` iff it is perfect, `(α, β) = (0, 1)`, **or perfectly
inverted**, `(α, β) = (1, 0)` — so no *imperfect* binary sensor attains it, and the perfect
anti-button does (a finding the mandate's "no imperfect binary sensor" phrasing leaves implicit).
Source: [[corr-channel-voi-mandate]] E1 (corollary)
Kind: P
Fidelity: stronger: the inverted perfect sensor is included
Hyps: (a) none beyond the positivity -/
theorem twoButton_attains_iff (hε0 : 0 < ε) (hε1 : ε < 1) (hc : 0 < c) (hh : 0 < h) (α β : ℝ)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    sensorValue (twoPoint ε hε) (twoButton α β hα hβ) (twoValue c h .cont) = (1 - ε) * c ↔
      (α = 0 ∧ β = 1) ∨ (α = 1 ∧ β = 0) := by
  rw [twoState_attains_iff ε c h hε hε0 hε1 hc hh, Fin.forall_fin_two]
  simp only [twoButton_right_zero, twoButton_wrong_zero, twoButton_right_one, twoButton_wrong_one,
    sub_eq_zero]
  constructor
  · rintro ⟨h0 | h0, h1 | h1⟩
    · exact absurd (h1.trans h0) one_ne_zero
    · exact Or.inl ⟨h0, h1.symm⟩
    · exact Or.inr ⟨h1.symm, h0⟩
    · exact absurd (h1.trans h0) one_ne_zero
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Or.inl rfl, Or.inr rfl⟩
    · exact ⟨Or.inr rfl, Or.inl rfl⟩

/-- **A three-signal experiment attaining the bound** that is not `ofMap id`: signals `0, 1` split
the right world in half, signal `2` is sent exactly when wrong.
Source: [[corr-channel-voi-mandate]] E1 (corollary: "a three-signal split of `right`")
Kind: D
Fidelity: n/a (witness) -/
def splitScan : Experiment World (Fin 3) where
  k := fun w => match w with
    | .right => ![1 / 2, 1 / 2, 0]
    | .wrong => ![0, 0, 1]
  k_mem := fun w => by
    cases w
    · refine ⟨fun s => ?_, ?_⟩
      · fin_cases s <;> norm_num
      · simp [Fin.sum_univ_three]; norm_num
    · refine ⟨fun s => ?_, ?_⟩
      · fin_cases s <;> norm_num
      · simp [Fin.sum_univ_three]

/-- **E1, N+**: `splitScan` attains the bound (every signal supported in one world), so the
class of `twoState_attains_iff` contains experiments other than `ofMap id`.
Source: [[corr-channel-voi-mandate]] E1
Kind: N+
Fidelity: n/a -/
theorem splitScan_attains (hε0 : 0 < ε) (hε1 : ε < 1) (hc : 0 < c) (hh : 0 < h) :
    sensorValue (twoPoint ε hε) splitScan (twoValue c h .cont) = (1 - ε) * c := by
  rw [twoState_attains_iff ε c h hε hε0 hε1 hc hh]
  intro s
  fin_cases s <;> simp [splitScan]

end Tight

end

end Cleanroom.Corrigibility.CorrChannelVoi
