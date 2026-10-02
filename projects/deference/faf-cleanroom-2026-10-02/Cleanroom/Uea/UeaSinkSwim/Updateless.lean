import Cleanroom.Uea.UeaSinkSwim.NewcombTransparent

/-!
# `V_upd` facts, and the current-node floor with the constant yardstick is inert

Over `Transparent.model P`: `Vupd j := (∑_{i : pol i = pol j} wᵢ Q^{νᵢ}(root, look)) / (∑_{i : pol i = pol j} wᵢ)`
(junk `0` when the class mass on `pol j` is `0`); since the four policies are distinct the class of `pol j`
is `{j}` and `Vupd j = trueValue j` whenever `f j > 0`, policy-free (target 12 (i)). (ii) The argmax of
`Vupd` is `UDT` **iff** `q > 1000/1999`: the binding comparison is `UDT` vs `2box`
(`UDT - 2box = (1999 q - 1000)/1001`); the survey's "`q > 1/2`" is the `UDT`-vs-`worst` comparison
(`UDT - worst = 1000(2q - 1)/1001`), filed as a finding. (iii) `VupdSelf π j` adds `(1-δ) V^π(root)` to
both sums when `π` is `pol j` on the decision nodes; `VupdSelf 2box 2box` is the mandate's closed form.
(iv) The prefix-conditioned yardstick at `H_M` is `payoff(pol(M), M)`: its maximisers are `2box` and
`worst` (value `1`) while `UDT` has `MEG` — conditioning on the prefix restores updatefulness.

**Target 13**: `IsUpdFlooredFP U star π` is the floored map with the constant `U` in place of `V^*(h)` and a
fixed reset `star(h)` in place of `π⋆(h)`. On transparent Newcomb with any `U ≤ 1` and the `UDT` reset,
the floor never fires at `H_M` (`M(H_M) = 1 ≥ w U`), at `H_0` it fires iff `KILO < (1-δ) U` and prescribes
`two` either way, so **2box is the unique `Upd`-floored fixed point for all `q, δ, f`** — in particular for
`U = VupdStar`. A per-node floor compares a per-node quantity against a global yardstick and is defeated by
the last-level identity `Q_ξ = Q^*`; the sketch's round-2 target 2 does nothing.

Scope: finite shadow of rOSI ([[sequential-self-game]] §7). Namespace `Cleanroom.Uea.UeaSinkSwim.Updateless`
(faf-cleanroom run, `uea-sink-swim`, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSinkSwim

open Finset
open Cleanroom.Uea.UeaColeShadow

namespace Updateless

open Newcomb Transparent

/-! ### The generic `Upd`-floored fixed point -/

/-- **`Upd`-floored fixed point**: `IsFlooredFP` with the constant yardstick `U` in place of `V^*(h)` and the
fixed reset action `star(h)` in place of `π⋆(h)`: `r_h := M(h) - w_h U`; `r_h < 0 ⇒ supp = {star(h)}`;
`r_h > 0 ⇒ supp ⊆ 𝒜_h`; `r_h = 0 ⇒ supp ⊆ 𝒜_h ∪ {star(h)}`.
Source: `newcomb_interleaving.py` `is_upd_floored_fixed_point`; [[uea-2-inventory]] 2-005
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsUpdFlooredFP {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι) (U : ℝ)
    (star : (n : ℕ) → Hist A E n → A) (π : Policy A E) : Prop :=
  M.IsPolicy π ∧ ∀ n h, M.nonterminal n h →
    (M.Mx π n h - M.wS π n h * U < 0 → ∀ a, 0 < π n h a → a = star n h) ∧
    (0 < M.Mx π n h - M.wS π n h * U → ∀ a, 0 < π n h a → M.Qxi π n h a = M.Mx π n h) ∧
    (M.Mx π n h - M.wS π n h * U = 0 → ∀ a, 0 < π n h a → M.Qxi π n h a = M.Mx π n h ∨ a = star n h)

variable (P : TP)

/-! ### The policies as pure policies; `V_upd` -/

/-- The pure policy of index `j`: `look`, then `pol j` on the root percept (it is `νa j`). -/
noncomputable def detPol (j : Fin 4) : Policy (Fin 2) (Fin 2) := νa j

theorem detPol_root (j : Fin 4) (a : Fin 2) : detPol j 0 root a = if a = 0 then 1 else 0 := rfl
theorem detPol_H (j : Fin 4) (e a : Fin 2) : detPol j 1 (H e) a = if a = pol j e then 1 else 0 := rfl

theorem detPol_isPolicy (j : Fin 4) : (model P).IsPolicy (detPol j) := fun n h _ => νa_mem j n h

/-- `π` plays `pol j` on the decision nodes (`look` at the root, `pol j e` at `H e`). -/
def PolEq (π : Policy (Fin 2) (Fin 2)) (j : Fin 4) : Prop := π 0 root 0 = 1 ∧ ∀ e, π 1 (H e) (pol j e) = 1

theorem polEq_detPol (j : Fin 4) : PolEq (detPol j) j :=
  ⟨by simp [detPol_root], fun e => by simp [detPol_H]⟩

theorem pol_injective : ∀ i j : Fin 4, pol i = pol j → i = j := by decide

/-- The four policies are pairwise distinct, so the class of `pol j` is `{j}`. -/
theorem filter_pol_eq (j : Fin 4) : (univ.filter (fun i => pol i = pol j)) = {j} := by
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  exact ⟨fun h => pol_injective i j h, fun h => by rw [h]⟩

/-- `V_upd(pol j) := (∑_{i : pol i = pol j} wᵢ Q^{νᵢ}(root, look)) / (∑_{i : pol i = pol j} wᵢ)` — the class
average of the value of `pol j` in the hypotheses that act like `pol j`; junk `0` when the class has no mass
(disclosed).
Source: `newcomb_interleaving.py` `V_upd`; [[uea-2-inventory]] 2-004; [[uea-inventory]] 035
Kind: D
Fidelity: exact where the class mass is positive; junk `0` elsewhere (disclosed)
Hyps: n/a -/
noncomputable def Vupd (j : Fin 4) : ℝ :=
  (∑ i ∈ univ.filter (fun i => pol i = pol j), (model P).w i * (model P).Qnu i 0 root 0) /
    (∑ i ∈ univ.filter (fun i => pol i = pol j), (model P).w i)

/-- **`V_upd(pol) = trueValue pol` when `f_pol > 0`**, policy-free.
Source: [[uea-2-inventory]] 2-004 (target 12 (i))
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Vupd_eq {j : Fin 4} (hf : P.f j ≠ 0) : Vupd P j = trueValue P j := by
  unfold Vupd
  rw [filter_pol_eq, sum_singleton, sum_singleton]
  have : (model P).w j ≠ 0 := mul_ne_zero P.hδ.ne' hf
  rw [mul_div_cancel_left₀ _ this]
  rfl

theorem Vupd_of_f_eq_zero {j : Fin 4} (hf : P.f j = 0) : Vupd P j = 0 := by
  unfold Vupd
  rw [filter_pol_eq, sum_singleton, sum_singleton]
  simp [hf]

theorem Vupd_le_one (j : Fin 4) : Vupd P j ≤ 1 := by
  by_cases hf : P.f j = 0
  · rw [Vupd_of_f_eq_zero P hf]; exact zero_le_one
  · rw [Vupd_eq P hf]; exact (model P).Qnu_le_one j (by simp) root 0

theorem Vupd_nonneg (j : Fin 4) : 0 ≤ Vupd P j := by
  by_cases hf : P.f j = 0
  · rw [Vupd_of_f_eq_zero P hf]
  · rw [Vupd_eq P hf]; exact (model P).Qnu_nonneg j 0 root 0

/-- `V_upd^* := max_pol V_upd(pol)`. -/
noncomputable def VupdStar : ℝ := univ.sup' univ_nonempty (Vupd P)

theorem Vupd_le_VupdStar (j : Fin 4) : Vupd P j ≤ VupdStar P := le_sup' _ (mem_univ j)
theorem VupdStar_le_one : VupdStar P ≤ 1 := by
  unfold VupdStar; rw [Finset.sup'_le_iff]; intro j _; exact Vupd_le_one P j
theorem VupdStar_le_iff {c : ℝ} : VupdStar P ≤ c ↔ ∀ j, Vupd P j ≤ c := by
  unfold VupdStar; rw [Finset.sup'_le_iff]; simp

/-- `UDT - 2box = (1999 q - 1000)/1001` and `UDT - worst = 1000 (2q - 1)/1001`: the binding comparison for the
argmax is `UDT` vs `2box`, with threshold `1000/1999`, not the survey's `1/2` (which is `UDT` vs `worst`).
Source: [[uea-2-inventory]] 2-004 (the mandate writer's recomputation; finding)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem trueValue_diffs :
    trueValue P 0 - trueValue P 2 = (1999 * P.q - 1000) / 1001 ∧
    trueValue P 0 - trueValue P 3 = 1000 * (2 * P.q - 1) / 1001 ∧
    trueValue P 0 - trueValue P 1 = (1 - P.q) * KILO := by
  obtain ⟨h0, h1, h2, h3⟩ := trueValues P
  rw [h0, h1, h2, h3]
  unfold MEG KILO
  refine ⟨by ring, by ring, by ring⟩

/-- **The argmax of `V_upd` is `UDT` iff `q > 1000/1999`** (all four hypotheses present): `UDT` strictly beats
every other policy iff `q > 1000/1999`, and then `V_upd^* = q MEG + (1-q) KILO`.
Source: [[uea-2-inventory]] 2-004 (target 12 (ii), corrected threshold)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem argmax_Vupd_UDT_iff (hf : ∀ j, P.f j ≠ 0) :
    ((∀ j, j ≠ 0 → Vupd P j < Vupd P 0) ↔ 1000 / 1999 < P.q) ∧
    (1000 / 1999 < P.q → VupdStar P = P.q * MEG + (1 - P.q) * KILO) := by
  obtain ⟨d2, d3, d1⟩ := trueValue_diffs P
  have hV : ∀ j, Vupd P j = trueValue P j := fun j => Vupd_eq P (hf j)
  have hq1 := P.hq1
  have hK : 0 < KILO := by unfold KILO; norm_num
  have hK' := mul_pos (sub_pos.2 hq1) hK
  have h0 := (trueValues P).1
  constructor
  · constructor
    · intro H
      have := H 2 (by decide)
      rw [hV, hV] at this
      linarith
    · intro hq j hj
      rw [hV, hV]
      have hj' : j = 1 ∨ j = 2 ∨ j = 3 := by
        revert hj; revert j; decide
      rcases hj' with rfl | rfl | rfl
      · linarith
      · linarith
      · linarith
  · intro hq
    apply le_antisymm
    · rw [VupdStar_le_iff]
      intro j
      rw [hV]
      have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by revert j; decide
      rcases hj' with rfl | rfl | rfl | rfl
      · rw [(trueValues P).1]
      · linarith
      · linarith
      · linarith
    · rw [← (trueValues P).1, ← hV]
      exact Vupd_le_VupdStar P 0

/-! ### `V_upd` with self mass, and the prefix-conditioned yardstick -/

open Classical in
/-- `V_upd` with the self-hypothesis counted: when `π` plays `pol j` on the decision nodes, `(1-δ) V^π(root)` is
added to the numerator and `(1-δ)` to the denominator (F1: the self borrows `ξ`'s percept kernel).
Source: `newcomb_interleaving.py` `V_upd(include_self=True)`; [[uea-2-inventory]] 2-004
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def VupdSelf (π : Policy (Fin 2) (Fin 2)) (j : Fin 4) : ℝ :=
  ((∑ i ∈ univ.filter (fun i => pol i = pol j), (model P).w i * (model P).Qnu i 0 root 0) +
      (if PolEq π j then (1 - P.δ) * (model P).Vpi π 0 root else 0)) /
    ((∑ i ∈ univ.filter (fun i => pol i = pol j), (model P).w i) + (if PolEq π j then 1 - P.δ else 0))

theorem VupdSelf_of_not_polEq {π : Policy (Fin 2) (Fin 2)} {j : Fin 4} (h : ¬ PolEq π j) :
    VupdSelf P π j = Vupd P j := by
  unfold VupdSelf Vupd
  simp [h]

theorem detPol_two_isPlainFP : (model P).IsPlainFP (detPol 2) :=
  (isPlainFP_iff P _).2 ⟨detPol_isPolicy P 2, by simp [detPol_root], by simp [detPol_H, pol], by simp [detPol_H, pol]⟩

/-- **(iii)** `VupdSelf 2box 2box = ((1-δ)(ξ_M + (1-ξ_M) KILO) + δ f_2box trueValue(2box)) / ((1-δ) + δ f_2box)`.
Source: [[uea-2-inventory]] 2-004 (target 12 (iii))
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem VupdSelf_twoBox : VupdSelf P (detPol 2) 2 =
    ((1 - P.δ) * (xiM P + (1 - xiM P) * KILO) + P.δ * P.f 2 * trueValue P 2) / ((1 - P.δ) + P.δ * P.f 2) := by
  have hV : (model P).Vpi (detPol 2) 0 root = xiM P + (1 - xiM P) * KILO := by
    have := (gap_of_isPlainFP P (detPol_two_isPlainFP P)).1
    unfold Model.gap at this
    rw [Vstar_root] at this
    linarith
  unfold VupdSelf
  rw [filter_pol_eq, sum_singleton, sum_singleton, if_pos (polEq_detPol 2), if_pos (polEq_detPol 2), hV]
  show ((P.δ * P.f 2 * (model P).Qnu 2 0 root 0 + (1 - P.δ) * (xiM P + (1 - xiM P) * KILO)) /
    (P.δ * P.f 2 + (1 - P.δ))) = _
  unfold trueValue
  ring

/-- The prefix-conditioned yardstick at `H_e`: `pol j`'s value at `H_e` under its own hypothesis,
`Q^{ν_j}(H_e, pol j e)`.
Source: `newcomb_interleaving.py` `prefix_conditioned_check`; [[uea-2-inventory]] 2-004
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def VupdAt (j : Fin 4) (e : Fin 2) : ℝ := (model P).Qnu j 1 (H e) (pol j e)

theorem VupdAt_eq (j : Fin 4) (e : Fin 2) : VupdAt P j e = payoff (pol j e) e := Qnu_H P j e _

/-- **(iv)** Conditioning on the prefix restores updatefulness: at `H_M` the yardstick is `payoff(pol(M), M)`, so
its maximisers are `2box` and `worst` (value `1`) and `UDT` (and `1box`) have `MEG`.
Source: [[uea-2-inventory]] 2-004 (target 12 (iv))
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem VupdAt_M : VupdAt P 2 0 = 1 ∧ VupdAt P 3 0 = 1 ∧ VupdAt P 0 0 = MEG ∧ VupdAt P 1 0 = MEG := by
  simp [VupdAt_eq, pol, payoff_00, payoff_10]

/-! ### Target 13: the `Upd` floor is inert on transparent Newcomb -/

/-- The `UDT` reset: `look` at the root, `pol UDT` on the root percept below. -/
def starUDT : (n : ℕ) → Hist (Fin 2) (Fin 2) n → Fin 2
  | 0, _ => 0
  | _ + 1, h => pol 0 (h 0).2

theorem starUDT_H (e : Fin 2) : starUDT 1 (H e) = e := by simp [starUDT, pol]

/-- At `H_M` the floor never fires: `M(H_M) = 1 ≥ w U` for every `U ≤ 1` (strictly, by `δ`).
Source: [[uea-2-inventory]] 2-005
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem resid_HM_pos {π : Policy (Fin 2) (Fin 2)} (hlook : π 0 root 0 = 1) {U : ℝ} (hU : U ≤ 1) :
    0 < (model P).Mx π 1 (H 0) - (model P).wS π 1 (H 0) * U := by
  rw [Mx_H, wS_H P hlook, payoff_10]
  have := P.hδ; have := P.hδ1
  nlinarith

/-- At `H_0` the floor fires iff `KILO < (1-δ) U`.
Source: [[uea-2-inventory]] 2-005
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem resid_H0_neg_iff {π : Policy (Fin 2) (Fin 2)} (hlook : π 0 root 0 = 1) (U : ℝ) :
    (model P).Mx π 1 (H 1) - (model P).wS π 1 (H 1) * U < 0 ↔ KILO < (1 - P.δ) * U := by
  rw [Mx_H, wS_H P hlook, payoff_11]
  constructor <;> intro h <;> linarith

/-- **2box is the unique `Upd`-floored fixed point** for every `U ≤ 1` with the `UDT` reset, all `q, δ, f`: the
`Upd`-floored fixed points are exactly the plain ones (`look`, then `two` on both branches).
Source: [[uea-2-inventory]] 2-005 (target 13; the script tested specific values, this is the general statement)
Kind: P
Fidelity: stronger: every `U ≤ 1`, every `q ∈ (0,1)`, `δ`, `f`
Hyps: (a) -/
theorem isUpdFlooredFP_iff {U : ℝ} (hU : U ≤ 1) (π : Policy (Fin 2) (Fin 2)) :
    IsUpdFlooredFP (model P) U starUDT π ↔
      (model P).IsPolicy π ∧ π 0 root 0 = 1 ∧ π 1 (H 0) 1 = 1 ∧ π 1 (H 1) 1 = 1 := by
  constructor
  · rintro ⟨hπ, hfp⟩
    -- the root: every clause forces `look`
    have hlook : π 0 root 0 = 1 := by
      have hM : (model P).Mx π 0 root = (model P).Qxi π 0 root 0 := by
        rw [(model P).Mx_fin_two, Qxi_root_1]
        exact max_eq_left (Qxi_root_0_pos P π hπ).le
      have h1 : π 0 root 1 = 0 := by
        by_contra hne
        have hpos : 0 < π 0 root 1 := lt_of_le_of_ne (hπ.nonneg (nt_root P) 1) (Ne.symm hne)
        obtain ⟨c1, c2, c3⟩ := hfp 0 root (nt_root P)
        rcases lt_trichotomy ((model P).Mx π 0 root - (model P).wS π 0 root * U) 0 with hr | hr | hr
        · exact absurd (c1 hr 1 hpos) (by decide)
        · rcases c3 hr 1 hpos with h | h
          · rw [Qxi_root_1, hM] at h; linarith [Qxi_root_0_pos P π hπ]
          · exact absurd h (by decide)
        · have h := c2 hr 1 hpos
          rw [Qxi_root_1, hM] at h; linarith [Qxi_root_0_pos P π hπ]
      rw [hπ.fin_two_zero (nt_root P), h1, sub_zero]
    refine ⟨hπ, hlook, ?_, ?_⟩
    · -- `H_M`: the floor never fires, so the support is in the argmax `{two}`
      have h0 : π 1 (H 0) 0 = 0 := by
        by_contra hne
        have hpos : 0 < π 1 (H 0) 0 := lt_of_le_of_ne (hπ.nonneg (nt_H P 0) 0) (Ne.symm hne)
        have := (hfp 1 (H 0) (nt_H P 0)).2.1 (resid_HM_pos P hlook hU) 0 hpos
        rw [Qxi_H, Mx_H] at this
        exact absurd this (payoff_0_lt_1 0).ne
      have := hπ.fin_two_zero (nt_H P 0); rw [h0] at this; linarith
    · -- `H_0`: the floor prescribes `two` whether or not it fires
      have h0 : π 1 (H 1) 0 = 0 := by
        by_contra hne
        have hpos : 0 < π 1 (H 1) 0 := lt_of_le_of_ne (hπ.nonneg (nt_H P 1) 0) (Ne.symm hne)
        obtain ⟨c1, c2, c3⟩ := hfp 1 (H 1) (nt_H P 1)
        rcases lt_trichotomy ((model P).Mx π 1 (H 1) - (model P).wS π 1 (H 1) * U) 0 with hr | hr | hr
        · have := c1 hr 0 hpos; rw [starUDT_H] at this; exact absurd this (by decide)
        · rcases c3 hr 0 hpos with h | h
          · rw [Qxi_H, Mx_H] at h; exact absurd h (payoff_0_lt_1 1).ne
          · rw [starUDT_H] at h; exact absurd h (by decide)
        · have h := c2 hr 0 hpos
          rw [Qxi_H, Mx_H] at h; exact absurd h (payoff_0_lt_1 1).ne
      have := hπ.fin_two_zero (nt_H P 1); rw [h0] at this; linarith
  · rintro ⟨hπ, hlook, hM, h0⟩
    have hfp := (isPlainFP_iff P π).2 ⟨hπ, hlook, hM, h0⟩
    refine ⟨hπ, fun n h hnt => ?_⟩
    have hplain := hfp.2 n h hnt
    refine ⟨fun hr a ha => ?_, fun _ a ha => hplain a ha, fun _ a ha => Or.inl (hplain a ha)⟩
    -- when the floor fires the supported action is the reset action
    match n with
    | 0 =>
      rw [eq_root h] at ha ⊢
      have h1 : π 0 root 1 = 0 := by
        have := hπ.fin_two_zero (nt_root P); rw [hlook] at this; linarith
      fin_cases a
      · rfl
      · exact absurd ha (by show ¬ 0 < π 0 root 1; rw [h1]; exact lt_irrefl 0)
    | 1 =>
      rw [eq_H_of_nonterminal P h hnt] at ha hr ⊢
      have hH : ∀ e, π 1 (H e) 1 = 1 := Fin.forall_fin_two.2 ⟨hM, h0⟩
      have he0 : π 1 (H (h 0).2) 0 = 0 := by
        have := hπ.fin_two_zero (nt_H P (h 0).2); rw [hH] at this; linarith
      fin_cases a
      · exact absurd ha (by show ¬ 0 < π 1 (H (h 0).2) 0; rw [he0]; exact lt_irrefl 0)
      · show (1 : Fin 2) = starUDT 1 (H (h 0).2)
        rw [starUDT_H]
        have hx : (h 0).2 = 0 ∨ (h 0).2 = 1 := by generalize (h 0).2 = x; fin_cases x <;> simp
        rcases hx with hx | hx
        · exfalso
          rw [hx] at hr
          exact absurd hr (not_lt.2 (resid_HM_pos P hlook hU).le)
        · exact hx.symm
    | n + 2 => exact absurd hnt (not_nt_ge_two P (n + 2) (by omega) h)

end Updateless

end Cleanroom.Uea.UeaSinkSwim
