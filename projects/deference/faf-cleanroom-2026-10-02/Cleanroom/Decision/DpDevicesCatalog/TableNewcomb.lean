import Cleanroom.Decision.DpDevicesCatalog.Devices
import Cleanroom.Decision.DpDevicesCatalog.TransparentNewcomb

set_option autoImplicit false

/-!
# `dp-devices-catalog` — T8, the TN-V2 column of the device table (CA-20′)

`tnV2 p L S` with `0 < p < 1`, `S > 0`; the source's column is at `(p, L, S) = (¾, 4, 1)` with
the three policies `(1,1)`, `(2,2)`, `(1,2)`. Rows:

| device | verdict | declaration |
|---|---|---|
| D2 event-tremble EDT | `(2,2)` only — **for every procedure**, at every `(p, L, S)` with `0 < p < 1`, `S > 0` | `tnV2_eventTremble_iff` |
| D4 advice EDT | `(2,2)` only, likewise universal | `tnV2_adviceEdt_iff` |
| D3⁰ Theorem 1 | `(1,1)` (`6` vs `19/4`; `3` vs `5/4`), `(2,2)` (`3` vs `13/4`; `2` vs `11/4`); not `(1,2)` (`11/4` vs `3` at `d_F`) | `tnV2_thm1_cells` |
| Dev mixed | `(1,1)`, `(2,2)`; not `(1,2)` | `tnV2_coherent_cells` |
| `V`-optimal | `(1,1)` only | `tnV2_isOptimal_cells` |

**The headline of the row**: the `V`-optimal one-boxer `(1,1)` is D2-*inconsistent* — D2
two-boxes at *both* boxes (`tnV2_optimum_d2_inconsistent`), FR-11's "without fairness" failure.
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

section newcomb

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)

/-! ## Infrastructure on V2 -/

/-- The payoff at a leaf of V2 is `tnPay` of its world. Source: none: infrastructure. Kind: L -/
theorem tnV2_payoff_world (ℓ : (tnV2 p h0 h1 L S).Leaves) :
    payoff (tnV2 p h0 h1 L S) ℓ = tnPay L S (world (tnV2 p h0 h1 L S) ℓ) := by
  unfold tnV2 tnReal at ℓ ⊢
  rcases ℓ with ⟨x, y, i, act, _⟩
  simp

/-- The worlds of the `(large, large)`-hypothetical leaves: full branch `(1, act)`, empty
branch `(0, act)`. Source: none: infrastructure. Kind: L -/
theorem tnV2_world_ll (act : Box) :
    world (tnV2 p h0 h1 L S) ⟨.large, .large, 0, act, ()⟩ = (true, act) ∧
    world (tnV2 p h0 h1 L S) ⟨.large, .large, 1, act, ()⟩ = (false, act) := by
  unfold tnV2 tnReal
  constructor <;> simp

/-- Their chance weights: `p` and `1 − p`. Source: none: infrastructure. Kind: L -/
theorem tnV2_chanceWeight_ll (act : Box) :
    chanceWeight (tnV2 p h0 h1 L S) ⟨.large, .large, 0, act, ()⟩ = p ∧
    chanceWeight (tnV2 p h0 h1 L S) ⟨.large, .large, 1, act, ()⟩ = 1 - p := by
  unfold tnV2 tnReal
  constructor <;> simp [FinDistr.coin]

/-- Leaf-worlds in `{a} ∧ O_F` pay `L + S·[a = both]`; in `{a} ∧ O_E` they pay `S·[a = both]`.
Source: none: infrastructure. Kind: L -/
theorem tnV2_actObs_payoff (a : Box) :
    (∀ ℓ, world (tnV2 p h0 h1 L S) ℓ ∈ tnActEv .F a ∩ tnObs .F →
      payoff (tnV2 p h0 h1 L S) ℓ = L + (if a = .both then S else 0)) ∧
    (∀ ℓ, world (tnV2 p h0 h1 L S) ℓ ∈ tnActEv .E a ∩ tnObs .E →
      payoff (tnV2 p h0 h1 L S) ℓ = (if a = .both then S else 0)) := by
  constructor <;> intro ℓ h <;> rw [tnV2_payoff_world] <;>
    simp only [tnActEv, tnObs, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
      true_and] at h <;> obtain ⟨h2, h1'⟩ := h <;>
    rcases hw : world (tnV2 p h0 h1 L S) ℓ with ⟨f, act⟩ <;> rw [hw] at h1' h2 <;>
    simp only at h1' h2 <;> subst h1' <;> subst h2 <;> simp [tnPay]

/-- Under a full-support procedure with `0 < p < 1`, every act event is realized within both
observations. Source: none: infrastructure. Kind: L -/
theorem tnV2_nu_actObs_pos {C : Proc TnPt (fun _ => Box) ℚ} (hC : C.FullSupport) (hp0 : 0 < p)
    (hp1 : p < 1) (a : Box) :
    0 < nu C (tnV2 p h0 h1 L S) (tnActEv .F a ∩ tnObs .F) ∧
    0 < nu C (tnV2 p h0 h1 L S) (tnActEv .E a ∩ tnObs .E) := by
  obtain ⟨w0, w1⟩ := tnV2_world_ll p h0 h1 L S a
  obtain ⟨c0, c1⟩ := tnV2_chanceWeight_ll p h0 h1 L S a
  constructor
  · exact nu_pos_of_leaf_fullSupport hC _ _ ⟨.large, .large, 0, a, ()⟩
      (by rw [w0]; simp [tnActEv, tnObs]) (by rw [c0]; exact hp0)
  · exact nu_pos_of_leaf_fullSupport hC _ _ ⟨.large, .large, 1, a, ()⟩
      (by rw [w1]; simp [tnActEv, tnObs]) (by rw [c1]; linarith)

/-- With `0 < p < 1` every act event within each observation is tremble-realizable.
Source: none: infrastructure. Kind: L -/
theorem tnV2_nuPoly_actObs_ne_zero (C : Proc TnPt (fun _ => Box) ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (a : Box) :
    nuPoly C (tnV2 p h0 h1 L S) (tnActEv .F a ∩ tnObs .F) ≠ 0 ∧
    nuPoly C (tnV2 p h0 h1 L S) (tnActEv .E a ∩ tnObs .E) ≠ 0 := by
  obtain ⟨w0, w1⟩ := tnV2_world_ll p h0 h1 L S a
  obtain ⟨c0, c1⟩ := tnV2_chanceWeight_ll p h0 h1 L S a
  constructor
  · exact nuPoly_ne_zero_of_leaf C _ _ ⟨.large, .large, 0, a, ()⟩
      (by rw [w0]; simp [tnActEv, tnObs]) (by rw [c0]; exact hp0)
  · exact nuPoly_ne_zero_of_leaf C _ _ ⟨.large, .large, 1, a, ()⟩
      (by rw [w1]; simp [tnActEv, tnObs]) (by rw [c1]; linarith)

/-- Both observations are tremble-realizable with `0 < p < 1`. Source: none: infrastructure.
Kind: L -/
theorem tnV2_nuPoly_obs_ne_zero (C : Proc TnPt (fun _ => Box) ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (d : TnPt) : nuPoly C (tnV2 p h0 h1 L S) (tnObs d) ≠ 0 := by
  obtain ⟨w0, w1⟩ := tnV2_world_ll p h0 h1 L S .large
  obtain ⟨c0, c1⟩ := tnV2_chanceWeight_ll p h0 h1 L S .large
  cases d
  · exact nuPoly_ne_zero_of_leaf C _ _ ⟨.large, .large, 0, .large, ()⟩
      (by rw [w0]; simp [tnObs]) (by rw [c0]; exact hp0)
  · exact nuPoly_ne_zero_of_leaf C _ _ ⟨.large, .large, 1, .large, ()⟩
      (by rw [w1]; simp [tnObs]) (by rw [c1]; linarith)

/-- **The act-conditional values under any tremble on V2**: at `d_F`, `L` (large) vs `L + S`
(both); at `d_E`, `0` vs `S` — the source's "`d_F`: `4` vs `5`; `d_E`: `0` vs `1`".
Source: `calibration.md` CA-20′ (D2 row, TN-V2: "`(2,2)` (`d_F`: `4` vs `5`; `d_E`: `0` vs
`1`)")
Kind: P
Fidelity: exact (every procedure, every `ε`) -/
theorem tnV2_tremble_condExp (C : Proc TnPt (fun _ => Box) ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (ε : ℚ) (e0 : 0 < ε) (e1 : ε ≤ 1) (a : Box) :
    condExp (tremble C ε e0.le e1) (tnV2 p h0 h1 L S) (tnActEv .F a ∩ tnObs .F) =
      L + (if a = .both then S else 0) ∧
    condExp (tremble C ε e0.le e1) (tnV2 p h0 h1 L S) (tnActEv .E a ∩ tnObs .E) =
      (if a = .both then S else 0) := by
  have hC := tremble_fullSupport C ε e0 e1
  obtain ⟨pF, pE⟩ := tnV2_actObs_payoff p h0 h1 L S a
  obtain ⟨nF, nE⟩ := tnV2_nu_actObs_pos p h0 h1 L S hC hp0 hp1 a
  exact ⟨condExp_const _ _ _ _ pF nF, condExp_const _ _ _ _ pE nE⟩

/-! ## D2 — event-tremble EDT: the two-boxer only, for every procedure -/

/-- **D2 on V2 approves exactly the two-boxer `(2,2)`**, for every procedure and every
`(p, L, S)` with `0 < p < 1`, `S > 0`: at both boxes the `both` event within the observation is
realized under every tremble and beats `large` by exactly `S`, so any procedure with `large` in
its support at either point is rejected at every `ε`.
Source: `calibration.md` CA-20′ (D2 row, TN-V2: "`(2,2)`"); dp-cf-049
Kind: P
Fidelity: stronger (every procedure, general parameters)
Hyps: (a) `0 < p < 1`, `0 < S` -/
theorem tnV2_eventTremble_iff (hp0 : 0 < p) (hp1 : p < 1) (hS : 0 < S)
    (C : Proc TnPt (fun _ => Box) ℚ) :
    EventTrembleEdtConsistent tnObs tnActEv C (tnV2 p h0 h1 L S) ↔ C = procBoth := by
  constructor
  · rintro ⟨ε₀, hε₀, h⟩
    have hmin0 : 0 < min ε₀ 1 := lt_min hε₀ one_pos
    have e0 : 0 < min ε₀ 1 / 2 := by linarith
    have e1 : min ε₀ 1 / 2 ≤ 1 := by linarith [min_le_right ε₀ 1]
    have hlt : min ε₀ 1 / 2 < ε₀ := by linarith [min_le_left ε₀ 1]
    have hfs := tremble_fullSupport C _ e0 e1
    -- at each point, `large` cannot be in the support
    have hF : (C .F).w .large = 0 := by
      by_contra hne
      have hpos : 0 < (C .F).w .large := lt_of_le_of_ne ((C .F).nonneg _) (Ne.symm hne)
      obtain ⟨-, hcmp⟩ := h _ e0 e1 hlt .F (tnV2_queried p h0 h1 L S .F)
        (tnV2_nuPoly_obs_ne_zero p h0 h1 L S C hp0 hp1 .F)
        ⟨.both, (tnV2_nu_actObs_pos p h0 h1 L S hfs hp0 hp1 .both).1⟩ .large hpos
      have := hcmp .both (tnV2_nu_actObs_pos p h0 h1 L S hfs hp0 hp1 .both).1
      rw [(tnV2_tremble_condExp p h0 h1 L S C hp0 hp1 _ e0 e1 .both).1,
        (tnV2_tremble_condExp p h0 h1 L S C hp0 hp1 _ e0 e1 .large).1] at this
      simp at this
      linarith
    have hE : (C .E).w .large = 0 := by
      by_contra hne
      have hpos : 0 < (C .E).w .large := lt_of_le_of_ne ((C .E).nonneg _) (Ne.symm hne)
      obtain ⟨-, hcmp⟩ := h _ e0 e1 hlt .E (tnV2_queried p h0 h1 L S .E)
        (tnV2_nuPoly_obs_ne_zero p h0 h1 L S C hp0 hp1 .E)
        ⟨.both, (tnV2_nu_actObs_pos p h0 h1 L S hfs hp0 hp1 .both).2⟩ .large hpos
      have := hcmp .both (tnV2_nu_actObs_pos p h0 h1 L S hfs hp0 hp1 .both).2
      rw [(tnV2_tremble_condExp p h0 h1 L S C hp0 hp1 _ e0 e1 .both).2,
        (tnV2_tremble_condExp p h0 h1 L S C hp0 hp1 _ e0 e1 .large).2] at this
      simp at this
      linarith
    have hFb : (C .F).w .both = 1 := by
      have := (C .F).sum_one; rw [Box.sum_univ] at this; linarith
    have hEb : (C .E).w .both = 1 := by
      have := (C .E).sum_one; rw [Box.sum_univ] at this; linarith
    funext d; apply FinDistr.ext'; intro a
    cases d <;> cases a <;> simp [procBoth, hF, hE, hFb, hEb]
  · rintro rfl
    refine ⟨1, one_pos, fun ε e0 e1 _ d _ _ _ a ha => ?_⟩
    have hfs := tremble_fullSupport procBoth ε e0 e1
    have ha' : a = .both := by
      by_contra hne; simp [procBoth, hne] at ha
    subst ha'
    cases d
    · refine ⟨(tnV2_nu_actObs_pos p h0 h1 L S hfs hp0 hp1 .both).1, fun b _ => ?_⟩
      rw [(tnV2_tremble_condExp p h0 h1 L S _ hp0 hp1 _ e0 e1 b).1,
        (tnV2_tremble_condExp p h0 h1 L S _ hp0 hp1 _ e0 e1 .both).1]
      cases b <;> simp <;> linarith
    · refine ⟨(tnV2_nu_actObs_pos p h0 h1 L S hfs hp0 hp1 .both).2, fun b _ => ?_⟩
      rw [(tnV2_tremble_condExp p h0 h1 L S _ hp0 hp1 _ e0 e1 b).2,
        (tnV2_tremble_condExp p h0 h1 L S _ hp0 hp1 _ e0 e1 .both).2]
      cases b <;> simp <;> linarith

/-- **The row's headline**: on V2 with `(2p−1)L > S` the `V`-optimal one-boxer is
D2-*inconsistent* — D2's verdict two-boxes at both boxes and rejects the good procedure
(FR-11's failure without fairness).
Source: `calibration.md` CA-20′ (TN-V2 column); mandate T8 ("state that as the row's headline
sentence")
Kind: C
Fidelity: exact
Hyps: (a) `0 < p < 1`, `½ ≤ p`, `0 < S`, `(2p−1)L > S` -/
theorem tnV2_optimum_d2_inconsistent (hp0 : 0 < p) (hp1 : p < 1) (hp : 1 / 2 ≤ p) (hS : 0 < S)
    (hopt : (2 * p - 1) * L > S) :
    IsOptimal procLarge (tnV2 p h0 h1 L S) ∧
    ¬ EventTrembleEdtConsistent tnObs tnActEv procLarge (tnV2 p h0 h1 L S) := by
  refine ⟨by rw [procLarge_eq]; exact tnV2_large_isOptimal p h0 h1 L S hS hp hopt, ?_⟩
  rw [tnV2_eventTremble_iff p h0 h1 L S hp0 hp1 hS]
  intro h
  have := congrArg (fun C => (C .F).w .large) h
  simp [procLarge, procBoth] at this

/-! ## D4 — advice EDT: the two-boxer only -/

/-- The tremble-limit act values on V2 (constant-payoff events): `L + S[both]` at `d_F`,
`S[both]` at `d_E`. Source: `calibration.md` CA-20′ (D4 row). Kind: L -/
theorem tnV2_limitVal (C : Proc TnPt (fun _ => Box) ℚ) (hp0 : 0 < p) (hp1 : p < 1) (a : Box) :
    limitVal C (tnV2 p h0 h1 L S) (tnActEv .F a ∩ tnObs .F) = L + (if a = .both then S else 0) ∧
    limitVal C (tnV2 p h0 h1 L S) (tnActEv .E a ∩ tnObs .E) = (if a = .both then S else 0) := by
  obtain ⟨pF, pE⟩ := tnV2_actObs_payoff p h0 h1 L S a
  obtain ⟨nF, nE⟩ := tnV2_nuPoly_actObs_ne_zero p h0 h1 L S C hp0 hp1 a
  exact ⟨limitVal_of_const _ _ _ _ pF nF, limitVal_of_const _ _ _ _ pE nE⟩

/-- **D4 on V2 approves exactly the two-boxer**, for every procedure.
Source: `calibration.md` CA-20′ (D4 row, TN-V2: "`(2,2)`")
Kind: P
Fidelity: stronger (every procedure, general parameters)
Hyps: (a) `0 < p < 1`, `0 < S` -/
theorem tnV2_adviceEdt_iff (hp0 : 0 < p) (hp1 : p < 1) (hS : 0 < S)
    (C : Proc TnPt (fun _ => Box) ℚ) :
    AdviceEdt tnObs tnActEv C (tnV2 p h0 h1 L S) ↔ C = procBoth := by
  constructor
  · intro h
    have hF : (C .F).w .large = 0 := by
      by_contra hne
      have hpos : 0 < (C .F).w .large := lt_of_le_of_ne ((C .F).nonneg _) (Ne.symm hne)
      have := (h .F (tnV2_queried p h0 h1 L S .F) (tnV2_nuPoly_obs_ne_zero p h0 h1 L S C hp0 hp1 .F)
        ⟨.both, (tnV2_nuPoly_actObs_ne_zero p h0 h1 L S C hp0 hp1 .both).1⟩ .large hpos).2 .both
        (tnV2_nuPoly_actObs_ne_zero p h0 h1 L S C hp0 hp1 .both).1
      rw [(tnV2_limitVal p h0 h1 L S C hp0 hp1 .both).1, (tnV2_limitVal p h0 h1 L S C hp0 hp1 .large).1]
        at this
      simp at this
      linarith
    have hE : (C .E).w .large = 0 := by
      by_contra hne
      have hpos : 0 < (C .E).w .large := lt_of_le_of_ne ((C .E).nonneg _) (Ne.symm hne)
      have := (h .E (tnV2_queried p h0 h1 L S .E) (tnV2_nuPoly_obs_ne_zero p h0 h1 L S C hp0 hp1 .E)
        ⟨.both, (tnV2_nuPoly_actObs_ne_zero p h0 h1 L S C hp0 hp1 .both).2⟩ .large hpos).2 .both
        (tnV2_nuPoly_actObs_ne_zero p h0 h1 L S C hp0 hp1 .both).2
      rw [(tnV2_limitVal p h0 h1 L S C hp0 hp1 .both).2, (tnV2_limitVal p h0 h1 L S C hp0 hp1 .large).2]
        at this
      simp at this
      linarith
    have hFb : (C .F).w .both = 1 := by
      have := (C .F).sum_one; rw [Box.sum_univ] at this; linarith
    have hEb : (C .E).w .both = 1 := by
      have := (C .E).sum_one; rw [Box.sum_univ] at this; linarith
    funext d; apply FinDistr.ext'; intro a
    cases d <;> cases a <;> simp [procBoth, hF, hE, hFb, hEb]
  · rintro rfl
    intro d _ _ _ a ha
    have ha' : a = .both := by
      by_contra hne; simp [procBoth, hne] at ha
    subst ha'
    cases d
    · refine ⟨(tnV2_nuPoly_actObs_ne_zero p h0 h1 L S _ hp0 hp1 .both).1, fun b _ => ?_⟩
      rw [(tnV2_limitVal p h0 h1 L S _ hp0 hp1 b).1, (tnV2_limitVal p h0 h1 L S _ hp0 hp1 .both).1]
      cases b <;> simp <;> linarith
    · refine ⟨(tnV2_nuPoly_actObs_ne_zero p h0 h1 L S _ hp0 hp1 .both).2, fun b _ => ?_⟩
      rw [(tnV2_limitVal p h0 h1 L S _ hp0 hp1 b).2, (tnV2_limitVal p h0 h1 L S _ hp0 hp1 .both).2]
      cases b <;> simp <;> linarith

/-! ## D3⁰ — Theorem 1's functional on V2 -/

/-- **Theorem 1's functional on V2 under `tnProc x y`**, from the tree: at `d_F`,
`Φ(large) = ν(O_F)·L + V(child_F(large))`, `Φ(both) = ν(O_F)·(L+S) + V(child_F(both))`; at
`d_E`, `Φ(large) = ∑_{x'} C(F)(x') V(chance(x', large))`, `Φ(both) = ν(O_E)·S + ∑_{x'} C(F)(x')
V(chance(x', both))`, with the branch values spelled out.
Source: [[decision-problems-v2]] §8 Theorem 1 on V2; `calibration.md` CA-20′ (D3⁰ row)
Kind: P
Fidelity: exact -/
theorem tnV2_siaSum (x y : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    siaSum (tnProc x y hx0 hx1 hy0 hy1) (tnV2 p h0 h1 L S) .F .large =
      (x * y * p + (1 - x * y) * (1 - p)) * L +
        (y * (p * (L + (1 - x) * S) + (1 - p) * ((1 - y) * S)) +
          (1 - y) * ((1 - p) * (L + (1 - x) * S) + p * ((1 - y) * S))) ∧
    siaSum (tnProc x y hx0 hx1 hy0 hy1) (tnV2 p h0 h1 L S) .F .both =
      (x * y * p + (1 - x * y) * (1 - p)) * (L + S) +
        ((1 - p) * (L + (1 - x) * S) + p * ((1 - y) * S)) ∧
    siaSum (tnProc x y hx0 hx1 hy0 hy1) (tnV2 p h0 h1 L S) .E .large =
      x * (p * (L + (1 - x) * S) + (1 - p) * ((1 - y) * S)) +
        (1 - x) * ((1 - p) * (L + (1 - x) * S) + p * ((1 - y) * S)) ∧
    siaSum (tnProc x y hx0 hx1 hy0 hy1) (tnV2 p h0 h1 L S) .E .both =
      (x * y * (1 - p) + (1 - x * y) * p) * S +
        (x * ((1 - p) * (L + (1 - x) * S) + p * ((1 - y) * S)) +
          (1 - x) * ((1 - p) * (L + (1 - x) * S) + p * ((1 - y) * S))) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tnV2, siaSum_decision, Box.sum_univ, Fin.sum_univ_two, tnProc_F, tnProc_E,
      FinDistr.box_large, FinDistr.box_both]
    simp [tnReal, siaSum_decision, siaSum_chance, value_decision, value_chance, value_leaf,
      Box.sum_univ, Fin.sum_univ_two, tnPay, FinDistr.coin]
    ring

/-- **D3⁰ cells at `(¾, 4, 1)`**: `(1,1)` (`6` vs `19/4` at `d_F`, `3` vs `5/4` at `d_E`) and
`(2,2)` (`3` vs `13/4`; `2` vs `11/4`) satisfy Theorem 1 at both points; `(1,2)` fails at
`d_F` (`11/4` vs `3` while `large` is played).
Source: `calibration.md` CA-20′ (D3⁰ row, TN-V2: "`(1,1)` (`6` vs `19/4`; `3` vs `5/4`),
`(2,2)` (`3` vs `13/4`; `2` vs `11/4`)")
Kind: N+
Fidelity: exact -/
theorem tnV2_thm1_cells :
    OccEdtConsistent (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) ∧
    OccEdtConsistent (tnProc 0 0 le_rfl zero_le_one le_rfl zero_le_one)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) ∧
    ¬ OccEdtConsistent (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) := by
  obtain ⟨a11, b11, c11, d11⟩ := tnV2_siaSum (3/4) (by norm_num) (by norm_num) 4 1 1 1
    zero_le_one le_rfl zero_le_one le_rfl
  obtain ⟨a22, b22, c22, d22⟩ := tnV2_siaSum (3/4) (by norm_num) (by norm_num) 4 1 0 0
    le_rfl zero_le_one le_rfl zero_le_one
  obtain ⟨a12, b12, -, -⟩ := tnV2_siaSum (3/4) (by norm_num) (by norm_num) 4 1 1 0
    zero_le_one le_rfl le_rfl zero_le_one
  norm_num at a11 b11 c11 d11 a22 b22 c22 d22 a12 b12
  simp only [occEdtConsistent_iff_thm1]
  refine ⟨fun d _ a ha b => ?_, fun d _ a ha b => ?_, fun h => ?_⟩
  · cases d <;> cases a <;> cases b <;> simp only [a11, b11, c11, d11] <;> norm_num <;>
      simp [tnProc] at ha
  · cases d <;> cases a <;> cases b <;> simp only [a22, b22, c22, d22] <;> norm_num <;>
      simp [tnProc] at ha
  · have := h .F (tnV2_queried _ _ _ _ _ .F) .large (by simp [tnProc]) .both
    rw [a12, b12] at this
    norm_num at this

/-! ## Dev, opt — the cells at `(¾, 4, 1)` -/

/-- **Dev-mixed cells at `(¾, 4, 1)`**: `(1,1)` and `(2,2)` are coherent (mixed Definition 22
at both points), `(1,2)` is not (at `d_F` the deviation to `both` gives `2 > 7/4`).
Source: `calibration.md` CA-20′ (Dev mixed row, TN-V2: "`(1,1)`, `(2,2)`")
Kind: N+
Fidelity: exact (mixed, A30) -/
theorem tnV2_coherent_cells :
    Coherent (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) ∧
    Coherent (tnProc 0 0 le_rfl zero_le_one le_rfl zero_le_one)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) ∧
    ¬ Coherent (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) := by
  refine ⟨IsOptimal.coherent _ _ (tnV2_large_isOptimal _ _ _ _ _ (by norm_num) (by norm_num)
    (by norm_num)), fun d _ m => ?_, fun h => ?_⟩
  · rw [FinDistr.eq_box m]
    cases d
    · rw [tnProc_deviate_F, tnV2_value, tnV2_value]
      have := m.nonneg .large; have := m.w_le_one .large
      nlinarith
    · rw [tnProc_deviate_E, tnV2_value, tnV2_value]
      have := m.nonneg .large; have := m.w_le_one .large
      nlinarith
  · have := h .F (tnV2_queried _ _ _ _ _ .F) (FinDistr.box 0 le_rfl zero_le_one)
    rw [tnProc_deviate_F, tnV2_value, tnV2_value] at this
    norm_num at this

/-- **`V`-optimal cells at `(¾, 4, 1)`**: `(1,1)` only (`3`); `(2,2)` (`2`) and `(1,2)` (`7/4`)
are not optimal.
Source: `calibration.md` CA-20′ (`V`-optimal row, TN-V2: "`(1,1)` (`3`)")
Kind: N+
Fidelity: exact -/
theorem tnV2_isOptimal_cells :
    IsOptimal (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) ∧
    ¬ IsOptimal (tnProc 0 0 le_rfl zero_le_one le_rfl zero_le_one)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) ∧
    ¬ IsOptimal (tnProc 1 0 zero_le_one le_rfl le_rfl zero_le_one)
      (tnV2 (3/4) (by norm_num) (by norm_num) 4 1) := by
  refine ⟨tnV2_large_isOptimal _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num),
    fun h => ?_, fun h => ?_⟩
  · have := h (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl)
    rw [tnV2_value, tnV2_value] at this; norm_num at this
  · have := h (tnProc 1 1 zero_le_one le_rfl zero_le_one le_rfl)
    rw [tnV2_value, tnV2_value] at this; norm_num at this

end newcomb

end Cleanroom.Decision.DpDevicesCatalog
