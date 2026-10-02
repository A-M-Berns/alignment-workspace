import Cleanroom.Decision.DpDevicesCatalog.Values
import Cleanroom.Decision.DpCalibration.Selection
import Cleanroom.Decision.DpCalibration.MiniDevices

set_option autoImplicit false

/-!
# `dp-devices-catalog` — T6(d): the selection-forcing tree

On `selTree = S_sel(−20, −20; 10, 5)` (dp-cf-001(b), dp-cf-2-056, CA-14′):

* the strictly-calibrated-and-`T_EDT`-approved labels are exactly `{7/11}` — both pure labels
  are rejected because `A⁺ = A` at every `q` (`sel_aPlus`), so there is no vacuity to hide in;
* **D2 is empty** for every `q ∈ [0,1]` (`selTree_not_eventTremble`): at the forced label
  `q = 7/11` the trembled difference `v_ε(a) − v_ε(b) = 1210ε/(3(12−ε)(10+ε)) > 0` (derived from
  the tree), so `a` is strictly preferred and the mixed label is rejected; the pure labels are
  rejected as on the miniature. D2's emptiness is not a self-succession phenomenon — `selTree`
  is almost fair.
* *Stretch*: on the symmetric variant `S_sel(−20, −20; 10, 10)` the tie sits at `q = ½` and D2
  is exactly `{½}` (`selSym_eventTremble_iff`): the uniform tremble fixes the uniform label.
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

/-! ## Statistics of the general selection-forcing tree -/

section general

variable (ua ub ra rb : ℚ)

/-- A sum over the leaves of `selectionForcing ua ub ra rb` as four terms.
Source: none: infrastructure. Kind: L -/
theorem selectionForcing_sum (f : (selectionForcing ua ub ra rb).Leaves → ℚ) :
    ∑ ℓ, f ℓ = f ⟨0, .a, ()⟩ + f ⟨0, .b, ()⟩ + f ⟨1, ()⟩ + f ⟨2, ()⟩ := by
  unfold selectionForcing at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_three]
  show (∑ ℓ : (Tree.decision () (fun | .a => .leaf SelW.realA ua | .b => .leaf SelW.realB ub) :
      Tree SelW Unit (fun _ => Act2) ℚ).Leaves, f ⟨0, ℓ⟩) +
    (∑ ℓ : (Tree.leaf SelW.fakeA ra : Tree SelW Unit (fun _ => Act2) ℚ).Leaves, f ⟨1, ℓ⟩) +
    (∑ ℓ : (Tree.leaf SelW.fakeB rb : Tree SelW Unit (fun _ => Act2) ℚ).Leaves, f ⟨2, ℓ⟩) = _
  rw [sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]

/-- `ν` on the general selection-forcing tree. Source: none: infrastructure. Kind: L -/
theorem selectionForcing_nu (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset SelW) :
    nu C (selectionForcing ua ub ra rb) X =
      (if SelW.realA ∈ X then (1/3 : ℚ) * (C ()).w .a else 0) +
      (if SelW.realB ∈ X then (1/3 : ℚ) * (C ()).w .b else 0) +
      (if SelW.fakeA ∈ X then (1/3 : ℚ) else 0) +
      (if SelW.fakeB ∈ X then (1/3 : ℚ) else 0) := by
  rw [nu_eq_sum, selectionForcing_sum]
  unfold selectionForcing
  simp [leafLaw_chance, leafLaw_decision, leafLaw_leaf, world_chance, world_decision, world_leaf,
    FinDistr.third]

/-- `𝔼[r · 1_X]` on the general selection-forcing tree. Source: none: infrastructure. Kind: L -/
theorem selectionForcing_paySum (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset SelW) :
    paySum C (selectionForcing ua ub ra rb) X =
      (if SelW.realA ∈ X then (1/3 : ℚ) * (C ()).w .a * ua else 0) +
      (if SelW.realB ∈ X then (1/3 : ℚ) * (C ()).w .b * ub else 0) +
      (if SelW.fakeA ∈ X then (1/3 : ℚ) * ra else 0) +
      (if SelW.fakeB ∈ X then (1/3 : ℚ) * rb else 0) := by
  rw [paySum_eq_sum_ite, selectionForcing_sum]
  unfold selectionForcing
  simp [leafLaw_chance, leafLaw_decision, leafLaw_leaf, world_chance, world_decision, world_leaf,
    payoff_chance, payoff_decision, payoff_leaf, FinDistr.third]

/-- The point is queried. Source: none: infrastructure. Kind: L -/
theorem selectionForcing_queried : () ∈ queried (selectionForcing ua ub ra rb) := by
  unfold selectionForcing
  simp [queried_chance, queried_decision, Fin.exists_fin_succ]

/-- `nuPoly ⊤ ≠ 0` (the fake leaves are chance-positive). Source: none: infrastructure. Kind: L -/
theorem selectionForcing_nuPoly_obs_ne_zero (C : Proc Unit (fun _ => Act2) ℚ) :
    nuPoly C (selectionForcing ua ub ra rb) (selObs ()) ≠ 0 := by
  rw [nuPoly_ne_zero_iff]
  refine ⟨⟨1, ()⟩, by simp [selObs], ?_⟩
  unfold selectionForcing; simp [chanceWeight, FinDistr.third]

/-- **The act-conditional values of `procQ r` on the general tree**: `V(a) = (r ua + ra)/(1 + r)`,
`V(b) = ((1−r) ub + rb)/(2 − r)` (both denominators positive on `[0,1]`).
Source: `calibration.md` CA-12′ (the default instance); mandate T6(d)
Kind: P
Fidelity: exact -/
theorem selectionForcing_condExp (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    condExp (procQ r h0 h1) (selectionForcing ua ub ra rb) (selActEv () .a ∩ selObs ()) =
      (r * ua + ra) / (1 + r) ∧
    condExp (procQ r h0 h1) (selectionForcing ua ub ra rb) (selActEv () .b ∩ selObs ()) =
      ((1 - r) * ub + rb) / (2 - r) := by
  have h2 : (0 : ℚ) < 2 - r := by linarith
  have h3 : (0 : ℚ) < 1 + r := by linarith
  simp only [condExp, selObs, Finset.inter_univ, selectionForcing_nu, selectionForcing_paySum,
    selActEv, procQ, FinDistr.act2_a, FinDistr.act2_b]
  simp
  constructor
  · rw [div_eq_div_iff (by linarith) h3.ne']; ring
  · rw [div_eq_div_iff (by linarith) h2.ne']; ring

/-- Both act events are realized within `O = ⊤` under every `procQ r` (the fake leaves).
Source: `calibration.md` CA-12′ ("the fake worlds carry mass")
Kind: L -/
theorem selectionForcing_nu_act_pos (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (a : Act2) :
    0 < nu (procQ r h0 h1) (selectionForcing ua ub ra rb) (selActEv () a ∩ selObs ()) := by
  rw [selObs, Finset.inter_univ, selectionForcing_nu]
  cases a <;> simp [selActEv, procQ] <;> linarith

end general

/-! ## `selTree = S_sel(−20, −20; 10, 5)` -/

/-- **The strictly-calibrated-and-approved labels of `selTree` are exactly `{7/11}`**: strict
calibration holds for every `q` (the state is the calibrated state at `⊤`) and `T_EDT` holds iff
both acts tie, since both are always subjectively possible (`sel_aPlus`); at `q < 7/11` the
played `b` is strictly worse, at `q > 7/11` the played `a` is. The state is fixed to
dp-calibration's calibrated state at `⊤`; this is without loss (`selTree_approved_iff_any`):
`ν(⊤) = 1 > 0`, so any strictly calibrated state agrees with it modulo junk
(`strictClausesAt_unique`), and `T_EDT` reads only `P_s` and `V_s` on the two act events,
both `P_s`-positive.
Source: `calibration.md` CA-12′/CA-14′ ("at the forced label `q = 7/11`"); mandate T6(d)
Kind: P
Fidelity: exact
Hyps: (a) `0 ≤ q ≤ 1` -/
theorem selTree_approved_iff (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (StrictOCAt (fun _ => selState q h0 h1) selObs (procQ q h0 h1) selTree () ∧
      TEdtAt (fun _ => selState q h0 h1) selActEv (procQ q h0 h1) ()) ↔ q = 7 / 11 := by
  obtain ⟨hcmp1, hcmp2⟩ := sel_compare q h0 h1
  have hA := sel_aPlus q h0 h1
  have hstrict : StrictOCAt (fun _ => selState q h0 h1) selObs (procQ q h0 h1) selTree () :=
    strictOCAt_calibratedState selObs _ selTree _ () _ rfl
  constructor
  · rintro ⟨-, hedt⟩
    have hne : (APlus (fun _ => selState q h0 h1) selActEv ()).Nonempty := by
      rw [hA]; exact ⟨.a, by simp⟩
    rcases lt_trichotomy q (7/11) with hlt | heq | hgt
    · -- `b` is played (`1 − q > 0`) but `V(a) > V(b)`
      have hb := hedt hne .b (by simp [procQ]; linarith)
      rw [mem_argmaxPlus, hA] at hb
      have := hb.2 .a (by simp)
      rw [hcmp2] at this
      linarith
    · exact heq
    · have ha := hedt hne .a (by simp [procQ]; linarith)
      rw [mem_argmaxPlus, hA] at ha
      have := ha.2 .b (by simp)
      rw [hcmp1] at this
      linarith
  · rintro rfl
    refine ⟨hstrict, fun _ a _ => ?_⟩
    rw [mem_argmaxPlus, hA]
    refine ⟨by simp, fun b _ => ?_⟩
    cases a <;> cases b
    · exact le_rfl
    · exact hcmp1.mpr le_rfl
    · exact hcmp2.mpr le_rfl
    · exact le_rfl

/-- **The same over every state assignment**: some state is strictly calibrated for `procQ q`
at `⊤` and `T_EDT`-approves it iff `q = 7/11`. (Any such state agrees with the calibrated state
modulo junk, and `T_EDT` only reads the act events, on which both agree.)
Source: `calibration.md` CA-12′/CA-14′; mandate T6(d) (audit round 1, fidelity N1)
Kind: P
Fidelity: exact (every state assignment)
Hyps: (a) `0 ≤ q ≤ 1` -/
theorem selTree_approved_iff_any (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (∃ s : Unit → State SelW ℚ, StrictOCAt s selObs (procQ q h0 h1) selTree () ∧
      TEdtAt s selActEv (procQ q h0 h1) ()) ↔ q = 7 / 11 := by
  constructor
  · rintro ⟨s, hs, hedt⟩
    have hpos : 0 < nu (procQ q h0 h1) selTree (selObs ()) := nu_univ_pos _ _
    have hcal : StrictClausesAt (fun _ => selState q h0 h1) selObs (procQ q h0 h1) selTree () :=
      strictClausesAt_calibratedState selObs _ selTree _ () hpos rfl
    have hag := strictClausesAt_unique selObs _ selTree s (fun _ => selState q h0 h1) () hpos
      (hs hpos) hcal
    have hA : APlus s selActEv () = APlus (fun _ => selState q h0 h1) selActEv () := by
      ext a; simp [APlus, State.pr, hag.1]
    have hV : ∀ a, (s ()).V (selActEv () a) = (selState q h0 h1).V (selActEv () a) := by
      intro a
      apply hag.2
      have : a ∈ APlus s selActEv () := by rw [hA, sel_aPlus]; cases a <;> simp
      simpa [APlus] using this
    have hedt' : TEdtAt (fun _ => selState q h0 h1) selActEv (procQ q h0 h1) () := by
      intro hne a ha
      have hmem := hedt (by rwa [hA]) a ha
      rw [mem_argmaxPlus, hA] at hmem
      rw [mem_argmaxPlus]
      refine ⟨hmem.1, fun b hb => ?_⟩
      have := hmem.2 b hb
      rwa [hV, hV] at this
    exact (selTree_approved_iff q h0 h1).1
      ⟨strictOCAt_calibratedState selObs _ selTree _ () _ rfl, hedt'⟩
  · rintro rfl
    exact ⟨fun _ => selState (7 / 11) h0 h1, (selTree_approved_iff _ h0 h1).2 rfl⟩

/-- **The trembled act values on `selTree`** at the label `q`: with `r = q_ε`,
`v_ε(a) = (10 − 20r)/(1 + r)`, `v_ε(b) = (20r − 15)/(2 − r)`.
Source: `calibration.md` CA-14′
Kind: P
Fidelity: exact -/
theorem selTree_tremble_condExp (q ε : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) :
    condExp (tremble (procQ q hq0 hq1) ε h0 h1) selTree (selActEv () .a ∩ selObs ()) =
      (10 - 20 * ((1 - ε) * q + ε / 2)) / (1 + ((1 - ε) * q + ε / 2)) ∧
    condExp (tremble (procQ q hq0 hq1) ε h0 h1) selTree (selActEv () .b ∩ selObs ()) =
      (20 * ((1 - ε) * q + ε / 2) - 15) / (2 - ((1 - ε) * q + ε / 2)) := by
  rw [tremble_procQ]
  obtain ⟨ha, hb⟩ := selectionForcing_condExp (-20) (-20) 10 5 _
    (qeps_mem q ε hq0 hq1 h0 h1).1 (qeps_mem q ε hq0 hq1 h0 h1).2
  unfold selTree
  rw [ha, hb]
  constructor <;> ring_nf

/-- **At the forced label `q = 7/11` the trembled difference is `1210ε/(3(12−ε)(10+ε))`**,
positive for `0 < ε ≤ 1` (indeed for `0 < ε < 12`): `a` is strictly preferred under every small
tremble.
Source: `calibration.md` CA-14′ ("the trembled difference is `−1210ε/(3(ε−12)(ε+10)) > 0`")
Kind: P
Fidelity: exact
Hyps: (a) `0 < ε ≤ 1` -/
theorem selTree_forced_tremble_diff (ε : ℚ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    condExp (tremble (procQ (7/11) (by norm_num) (by norm_num)) ε h0.le h1) selTree
        (selActEv () .a ∩ selObs ()) -
      condExp (tremble (procQ (7/11) (by norm_num) (by norm_num)) ε h0.le h1) selTree
        (selActEv () .b ∩ selObs ()) = 1210 * ε / (3 * (12 - ε) * (10 + ε)) ∧
    0 < 1210 * ε / (3 * (12 - ε) * (10 + ε)) := by
  obtain ⟨ha, hb⟩ := selTree_tremble_condExp (7/11) ε (by norm_num) (by norm_num) h0.le h1
  rw [ha, hb]
  have h12 : (0 : ℚ) < 12 - ε := by linarith
  have h10 : (0 : ℚ) < 10 + ε := by linarith
  have hA : (1 + ((1 - ε) * (7 / 11) + ε / 2)) ≠ 0 := by
    have : (0 : ℚ) < 1 + ((1 - ε) * (7 / 11) + ε / 2) := by nlinarith
    exact this.ne'
  have hB : (2 - ((1 - ε) * (7 / 11) + ε / 2)) ≠ 0 := by
    have : (0 : ℚ) < 2 - ((1 - ε) * (7 / 11) + ε / 2) := by nlinarith
    exact this.ne'
  have hC : (3 * (12 - ε) * (10 + ε)) ≠ 0 := by positivity
  constructor
  · rw [div_sub_div _ _ hA hB, div_eq_div_iff (mul_ne_zero hA hB) hC]
    ring
  · positivity

/-- The trembled comparison on `selTree` at label `r ∈ [0,1]`: `v(b) ≤ v(a) ↔ r ≤ 7/11` and
`v(a) ≤ v(b) ↔ 7/11 ≤ r`. Source: `calibration.md` CA-12′. Kind: L -/
theorem selTree_condExp_compare (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    ((20 * r - 15) / (2 - r) ≤ (10 - 20 * r) / (1 + r) ↔ r ≤ 7 / 11) ∧
    ((10 - 20 * r) / (1 + r) ≤ (20 * r - 15) / (2 - r) ↔ 7 / 11 ≤ r) := by
  have h2 : (0 : ℚ) < 2 - r := by linarith
  have h3 : (0 : ℚ) < 1 + r := by linarith
  constructor
  · rw [div_le_div_iff₀ h2 h3]; constructor <;> intro h <;> nlinarith
  · rw [div_le_div_iff₀ h3 h2]; constructor <;> intro h <;> nlinarith

/-- **D2 is empty on `selTree`, for every `q ∈ [0,1]`**: a mixed label would have to tie at
`q_ε = 7/11` for two tremble sizes, forcing `q = ½ ≠ 7/11`; `δ_a` needs `q_ε = 1 − ε/2 ≤ 7/11`,
`δ_b` needs `7/11 ≤ q_ε = ε/2`, both false for small `ε`. Not a self-succession phenomenon:
`selTree` is almost fair.
Source: `calibration.md` CA-14′ ("D2's emptiness is **not** a self-succession phenomenon: on
`S_sel(−20,−20;10,5)`, D2 is empty"); dp-cf-2-056
Kind: P
Fidelity: exact (universal in `q`; the faithful `∀ ε₀, ¬ ∀ ε < ε₀` form)
Hyps: (a) `0 ≤ q ≤ 1` -/
theorem selTree_not_eventTremble (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ¬ EventTrembleEdtConsistent selObs selActEv (procQ q hq0 hq1) selTree := by
  rintro ⟨ε₀, hε₀, hD2⟩
  have key : ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε < 1), ε < ε₀ → ∀ a, 0 < (procQ q hq0 hq1 ()).w a →
      ∀ b, condExp (tremble (procQ q hq0 hq1) ε h0.le h1.le) selTree (selActEv () b ∩ selObs ()) ≤
        condExp (tremble (procQ q hq0 hq1) ε h0.le h1.le) selTree (selActEv () a ∩ selObs ()) := by
    intro ε h0 h1 hlt a ha b
    have hlive : ∀ b, 0 < nu (tremble (procQ q hq0 hq1) ε h0.le h1.le) selTree
        (selActEv () b ∩ selObs ()) := by
      intro b
      rw [tremble_procQ]
      exact selectionForcing_nu_act_pos _ _ _ _ _ _ _ b
    obtain ⟨-, hcmp⟩ := hD2 ε h0 h1.le hlt () (selectionForcing_queried _ _ _ _)
      (selectionForcing_nuPoly_obs_ne_zero _ _ _ _ _) ⟨.a, hlive .a⟩ a ha
    exact hcmp b (hlive b)
  set ε₁ : ℚ := min ε₀ 1 / 2 with hε₁
  set ε₂ : ℚ := min ε₀ 1 / 4 with hε₂
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
  obtain ⟨va1, vb1⟩ := selTree_tremble_condExp q ε₁ hq0 hq1 h10.le h11.le
  obtain ⟨va2, vb2⟩ := selTree_tremble_condExp q ε₂ hq0 hq1 h20.le h21.le
  obtain ⟨c1a, c1b⟩ := selTree_condExp_compare _ (qeps_mem q ε₁ hq0 hq1 h10.le h11.le).1
    (qeps_mem q ε₁ hq0 hq1 h10.le h11.le).2
  obtain ⟨c2a, c2b⟩ := selTree_condExp_compare _ (qeps_mem q ε₂ hq0 hq1 h20.le h21.le).1
    (qeps_mem q ε₂ hq0 hq1 h20.le h21.le).2
  rcases (lt_or_eq_of_le hq0) with hpos | hzero
  · rcases (lt_or_eq_of_le hq1) with hlt1 | hone
    · have ha1 := key ε₁ h10 h11 h1lt .a (by simp [procQ, hpos]) .b
      have hb1 := key ε₁ h10 h11 h1lt .b (by simp [procQ]; linarith) .a
      have ha2 := key ε₂ h20 h21 h2lt .a (by simp [procQ, hpos]) .b
      have hb2 := key ε₂ h20 h21 h2lt .b (by simp [procQ]; linarith) .a
      rw [va1, vb1] at ha1 hb1
      rw [va2, vb2] at ha2 hb2
      have t1 : (1 - ε₁) * q + ε₁ / 2 = 7 / 11 := le_antisymm (c1a.mp ha1) (c1b.mp hb1)
      have t2 : (1 - ε₂) * q + ε₂ / 2 = 7 / 11 := le_antisymm (c2a.mp ha2) (c2b.mp hb2)
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

/-! ## The symmetric variant `S_sel(−20, −20; 10, 10)` (stretch) -/

/-- The symmetric selection-forcing tree. Source: `calibration.md` line 23 ("symmetric variant
`(−20,−20;10,10)`"). Kind: D -/
def selSym : Tree SelW Unit (fun _ => Act2) ℚ := selectionForcing (-20) (-20) 10 10

/-- The trembled act values on `selSym`: `v(a) = (10 − 20r)/(1+r)`, `v(b) = (20r − 10)/(2−r)`
with `r = q_ε`. Source: `calibration.md` CA-14′. Kind: L -/
theorem selSym_tremble_condExp (q ε : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) :
    condExp (tremble (procQ q hq0 hq1) ε h0 h1) selSym (selActEv () .a ∩ selObs ()) =
      (10 - 20 * ((1 - ε) * q + ε / 2)) / (1 + ((1 - ε) * q + ε / 2)) ∧
    condExp (tremble (procQ q hq0 hq1) ε h0 h1) selSym (selActEv () .b ∩ selObs ()) =
      (20 * ((1 - ε) * q + ε / 2) - 10) / (2 - ((1 - ε) * q + ε / 2)) := by
  rw [tremble_procQ]
  obtain ⟨ha, hb⟩ := selectionForcing_condExp (-20) (-20) 10 10 _
    (qeps_mem q ε hq0 hq1 h0 h1).1 (qeps_mem q ε hq0 hq1 h0 h1).2
  unfold selSym
  rw [ha, hb]
  constructor <;> ring_nf

/-- The comparison on `selSym`: `v(b) ≤ v(a) ↔ r ≤ ½`, `v(a) ≤ v(b) ↔ ½ ≤ r`.
Source: `calibration.md` CA-14′ ("the tie sits at `q = ½`"). Kind: L -/
theorem selSym_condExp_compare (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    ((20 * r - 10) / (2 - r) ≤ (10 - 20 * r) / (1 + r) ↔ r ≤ 1 / 2) ∧
    ((10 - 20 * r) / (1 + r) ≤ (20 * r - 10) / (2 - r) ↔ 1 / 2 ≤ r) := by
  have h2 : (0 : ℚ) < 2 - r := by linarith
  have h3 : (0 : ℚ) < 1 + r := by linarith
  constructor
  · rw [div_le_div_iff₀ h2 h3]; constructor <;> intro h <;> nlinarith
  · rw [div_le_div_iff₀ h3 h2]; constructor <;> intro h <;> nlinarith

/-- **D2 on the symmetric variant is exactly `{½}`**: the uniform tremble fixes the uniform
label (`q_ε = ½` for every `ε`, so the tie persists), and every other label fails as on
`selTree`.
Source: `calibration.md` CA-14′ ("on the symmetric variant `S_sel(−20,−20;10,10)` the tie sits
at `q = ½` and D2 `= {½}`")
Kind: P
Fidelity: exact (universal in `q`)
Hyps: (a) `0 ≤ q ≤ 1` -/
theorem selSym_eventTremble_iff (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    EventTrembleEdtConsistent selObs selActEv (procQ q hq0 hq1) selSym ↔ q = 1 / 2 := by
  constructor
  · rintro ⟨ε₀, hε₀, hD2⟩
    have key : ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε < 1), ε < ε₀ → ∀ a, 0 < (procQ q hq0 hq1 ()).w a →
        ∀ b, condExp (tremble (procQ q hq0 hq1) ε h0.le h1.le) selSym
            (selActEv () b ∩ selObs ()) ≤
          condExp (tremble (procQ q hq0 hq1) ε h0.le h1.le) selSym (selActEv () a ∩ selObs ()) := by
      intro ε h0 h1 hlt a ha b
      have hlive : ∀ b, 0 < nu (tremble (procQ q hq0 hq1) ε h0.le h1.le) selSym
          (selActEv () b ∩ selObs ()) := by
        intro b
        rw [tremble_procQ]
        exact selectionForcing_nu_act_pos _ _ _ _ _ _ _ b
      obtain ⟨-, hcmp⟩ := hD2 ε h0 h1.le hlt () (selectionForcing_queried _ _ _ _)
        (selectionForcing_nuPoly_obs_ne_zero _ _ _ _ _) ⟨.a, hlive .a⟩ a ha
      exact hcmp b (hlive b)
    set ε₁ : ℚ := min ε₀ 1 / 2 with hε₁
    have hmin0 : 0 < min ε₀ 1 := lt_min hε₀ one_pos
    have hmin1 : min ε₀ 1 ≤ 1 := min_le_right _ _
    have hmin2 : min ε₀ 1 ≤ ε₀ := min_le_left _ _
    have h10 : 0 < ε₁ := by rw [hε₁]; linarith
    have h11 : ε₁ < 1 := by rw [hε₁]; linarith
    have h1lt : ε₁ < ε₀ := by rw [hε₁]; linarith
    obtain ⟨va1, vb1⟩ := selSym_tremble_condExp q ε₁ hq0 hq1 h10.le h11.le
    obtain ⟨c1a, c1b⟩ := selSym_condExp_compare _ (qeps_mem q ε₁ hq0 hq1 h10.le h11.le).1
      (qeps_mem q ε₁ hq0 hq1 h10.le h11.le).2
    rcases (lt_or_eq_of_le hq0) with hpos | hzero
    · rcases (lt_or_eq_of_le hq1) with hlt1 | hone
      · have ha1 := key ε₁ h10 h11 h1lt .a (by simp [procQ, hpos]) .b
        have hb1 := key ε₁ h10 h11 h1lt .b (by simp [procQ]; linarith) .a
        rw [va1, vb1] at ha1 hb1
        have t1 : (1 - ε₁) * q + ε₁ / 2 = 1 / 2 := le_antisymm (c1a.mp ha1) (c1b.mp hb1)
        have : (1 - ε₁) * (q - 1 / 2) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · linarith
        · linarith
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
  · rintro rfl
    refine ⟨1, one_pos, fun ε h0 h1 _ d _ _ _ a _ => ?_⟩
    cases d
    have hlive : ∀ b, 0 < nu (tremble (procQ (1/2) hq0 hq1) ε h0.le h1) selSym
        (selActEv () b ∩ selObs ()) := by
      intro b
      rw [tremble_procQ]
      exact selectionForcing_nu_act_pos _ _ _ _ _ _ _ b
    obtain ⟨va, vb⟩ := selSym_tremble_condExp (1/2) ε hq0 hq1 h0.le h1
    have hr : (1 - ε) * (1 / 2) + ε / 2 = 1 / 2 := by ring
    rw [hr] at va vb
    refine ⟨hlive a, fun b _ => ?_⟩
    cases a <;> cases b <;> simp only [va, vb] <;> norm_num

end Cleanroom.Decision.DpDevicesCatalog
