import Cleanroom.Uea.UeaSinkSwim.Updateless

/-!
# The policy-level floor: UDT, and the exact self-trap threshold

On transparent Newcomb with the class `{T_UDT (1-f), T_2box (f)}`, `f ∈ (0,1)`: the argmax policy of
`ξ[π]` is `2box` for every `π` (`piA_polEq`: the last-level values are the immediate payoffs and `look` beats
the dead action); the rule `polFloor π := if V_upd?(2box) < w_root · V_upd^* then UDT else 2box` with
`V_upd? = V_upd` (no self mass) or `VupdSelf π` (self mass); a fixed point is `π = polFloor π` — the rule's
outputs are pure, so every fixed point is pure.

**No self mass**: `UDT` is the unique fixed point iff `trueValue(2box) < (1-δ) V_upd^*`, i.e. (for
`q > 1000/1999`, where `V_upd^* = q MEG + (1-q) KILO`) iff `1001 - 1000 q < (1-δ)(999 q + 1)`; otherwise `2box`
is the unique fixed point — never both, never none. **With self mass**: `UDT` is a fixed point under the same
inequality; `2box` is a fixed point iff `g(f) ≥ 0`, with
`g(f) := (1-δ)(ξ_M + (1-ξ_M) KILO) + δ f trueValue(2box) - (1-δ) V_upd^* ((1-δ) + δ f)`,
`ξ_M = q(1-f) + (1-q) f`; `g` is affine in `f`, `g(0) > 0` always, and `g(1) < 0` iff the `UDT` inequality,
so then `2box` is a fixed point iff `f ≤ f* := -g(0)/(g(1) - g(0))` — **the self-trap** — an explicit rational
function of `(q, δ)` with `f*(q, 0) = q KILO / ((2q - 1) MEG)` as the algebraic identity at `δ = 0`.
N+: `q = 9/10, δ = 1/10`: `f* = 81819/790909`, with the theorem's hypotheses checked there
(`selfTrap_hyps_inhabited`); `q = 1`: `909/9899` is arithmetic on `fstar` only (`TP` needs `q < 1`). Without self
mass the rule is constant in `π` (`polFloor_const`), so `isPolFloorFP_iff` is bookkeeping (Kind L); the content is
`piA_polEq` and `twoClass_cond_iff`. Mechanism: the self borrows `ξ`'s percept
kernel (F1), so a two-boxing self "expects the money" when the class is dominated by one-boxers — the
transparent-Newcomb face of mupi's frozen self-posterior (target 3).

Scope: finite shadow of rOSI ([[sequential-self-game]] §7). Namespace `Cleanroom.Uea.UeaSinkSwim.PolicyFloor`
(faf-cleanroom run, `uea-sink-swim`, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSinkSwim

open Finset
open Cleanroom.Uea.UeaColeShadow

namespace PolicyFloor

open Newcomb Transparent Updateless

/-! ### The argmax policy of `ξ[π]` is 2box -/

variable (P : TP)

/-- The argmax policy of `ξ[π]`: at every history one fixed maximiser of `Q_ξ[π](h, ·)`, surely.
Source: `newcomb_interleaving.py` `argmax_policy`; [[uea-2-inventory]] 2-006
Kind: D
Fidelity: variant: a fixed choice of maximiser (disclosed; the maximiser is unique at every decision node here)
Hyps: n/a -/
noncomputable def piA (π : Policy (Fin 2) (Fin 2)) : Policy (Fin 2) (Fin 2) := fun n h a =>
  if a = Classical.choose (Finset.exists_mem_eq_sup' (univ_nonempty (α := Fin 2)) ((model P).Qxi π n h)) then 1 else 0

theorem fin_two_cases (b : Fin 2) : b = 0 ∨ b = 1 := by fin_cases b <;> simp

theorem piA_isPolicy (π : Policy (Fin 2) (Fin 2)) : (model P).IsPolicy (piA P π) := by
  intro n h _
  refine ⟨fun a => ?_, ?_⟩
  · show (0:ℝ) ≤ if a = Classical.choose (Finset.exists_mem_eq_sup' (univ_nonempty (α := Fin 2)) ((model P).Qxi π n h))
      then 1 else 0
    split_ifs <;> norm_num
  · show ∑ a, (if a = Classical.choose (Finset.exists_mem_eq_sup' (univ_nonempty (α := Fin 2)) ((model P).Qxi π n h))
      then (1:ℝ) else 0) = 1
    simp

/-- The chosen maximiser is the strict maximiser when there is one. -/
theorem choose_eq_of_strict (π : Policy (Fin 2) (Fin 2)) (n : ℕ) (h : Hist (Fin 2) (Fin 2) n) (m : Fin 2)
    (hm : ∀ b, b ≠ m → (model P).Qxi π n h b < (model P).Qxi π n h m) :
    Classical.choose (Finset.exists_mem_eq_sup' (univ_nonempty (α := Fin 2)) ((model P).Qxi π n h)) = m := by
  have hspec := Classical.choose_spec (Finset.exists_mem_eq_sup' (univ_nonempty (α := Fin 2)) ((model P).Qxi π n h))
  by_contra hne
  have h1 := hm _ hne
  have h2 : (model P).Qxi π n h m ≤ univ.sup' univ_nonempty ((model P).Qxi π n h) := le_sup' _ (mem_univ m)
  rw [hspec.2] at h2
  linarith

/-- **The argmax policy is 2box** for every policy `π`: `look` at the root (`Q_ξ(look) > 0 = Q_ξ(dead)`) and `two`
at `H_M`, `H_0` (the last-level values are the immediate payoffs).
Source: [[uea-2-inventory]] 2-006 ("prove it is 2box for every π")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem piA_polEq {π : Policy (Fin 2) (Fin 2)} (hπ : (model P).IsPolicy π) : PolEq (piA P π) 2 := by
  refine ⟨?_, fun e => ?_⟩
  · unfold piA
    rw [choose_eq_of_strict P π 0 root 0 (fun b hb => ?_)]
    · simp
    · rcases fin_two_cases b with rfl | rfl
      · exact absurd rfl hb
      · rw [Qxi_root_1]
        exact Qxi_root_0_pos P π hπ
  · unfold piA
    rw [choose_eq_of_strict P π 1 (H e) 1 (fun b hb => ?_)]
    · simp [pol]
    · rcases fin_two_cases b with rfl | rfl
      · rw [Qxi_H, Qxi_H]
        exact payoff_0_lt_1 e
      · exact absurd rfl hb

/-- A policy plays at most one of the four policies on the decision nodes. -/
theorem polEq_unique {π : Policy (Fin 2) (Fin 2)} (hπ : (model P).IsPolicy π) {j j' : Fin 4}
    (hj : PolEq π j) (hj' : PolEq π j') : j = j' := by
  apply pol_injective
  funext e
  by_contra hne
  have h1 := hj.2 e
  have h2 := hj'.2 e
  have hs := hπ.sum (nt_H P e)
  rw [Fin.sum_univ_two] at hs
  have h0 := hπ.nonneg (nt_H P e) 0
  have h1' := hπ.nonneg (nt_H P e) 1
  rcases fin_two_cases (pol j e) with ha | ha <;> rcases fin_two_cases (pol j' e) with hb | hb
  · exact hne (ha.trans hb.symm)
  · rw [ha] at h1; rw [hb] at h2; linarith
  · rw [ha] at h1; rw [hb] at h2; linarith
  · exact hne (ha.trans hb.symm)

theorem polEq_piA_iff {π : Policy (Fin 2) (Fin 2)} (hπ : (model P).IsPolicy π) (j : Fin 4) :
    PolEq (piA P π) j ↔ j = 2 :=
  ⟨fun hj => polEq_unique P (piA_isPolicy P π) hj (piA_polEq P hπ), fun hj => hj ▸ piA_polEq P hπ⟩

/-! ### The rules and their fixed points -/

/-- The index of `piA π` is `2` (`polEq_piA_iff`); the rule compares `V_upd?(2box)` against `w_root V_upd^*`. -/
noncomputable def cond : Prop := Vupd P 2 < (1 - P.δ) * VupdStar P

open Classical in
/-- **The policy-level floor, no self mass**: `polFloor π := if V_upd(piA π) < w_root V_upd^* then UDT else piA π`
(with `piA π = 2box` and `w_root = 1 - δ` for every `π`).
Source: `newcomb_interleaving.py` `self_trap_threshold`, `section3_report`; [[uea-2-inventory]] 2-006
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def polFloor (π : Policy (Fin 2) (Fin 2)) : Policy (Fin 2) (Fin 2) :=
  if Vupd P 2 < (model P).wS π 0 root * VupdStar P then detPol 0 else detPol 2

/-- A fixed point of the policy-level floor: `π = polFloor π` — equality of functions on all histories (so a
"unique fixed point" below is unique as a function). -/
def IsPolFloorFP (π : Policy (Fin 2) (Fin 2)) : Prop := π = polFloor P π

/-- **The no-self-mass rule is constant in `π`**: `w_root = 1 - δ` for every policy (`Transparent.wS_root`) and the
rule outputs the fixed function `detPol 2` (not `piA π`; the two agree on the three decision nodes by `piA_polEq`
and differ only at dead or terminal histories), so the test never mentions the candidate. Hence the fixed point of
`polFloor` is its constant value and `isPolFloorFP_iff` is an unfolding: without self mass the policy-level floor
on transparent Newcomb is not self-referential; self-reference enters only through `VupdSelf π 2` (the self-trap).
Source: finding F-8 (repair round 1; audit r1 N3)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem polFloor_const (π π' : Policy (Fin 2) (Fin 2)) : polFloor P π = polFloor P π' := by
  simp only [polFloor, wS_root]

open Classical in
/-- **The policy-level floor with self mass**: `V_upd` counts the self-hypothesis when `π` plays `piA π`'s policy. -/
noncomputable def polFloorSelf (π : Policy (Fin 2) (Fin 2)) : Policy (Fin 2) (Fin 2) :=
  if VupdSelf P π 2 < (model P).wS π 0 root * VupdStar P then detPol 0 else detPol 2

def IsPolFloorSelfFP (π : Policy (Fin 2) (Fin 2)) : Prop := π = polFloorSelf P π

theorem detPol_injective {i j : Fin 4} (h : detPol i = detPol j) : i = j := by
  apply pol_injective
  funext e
  have := congrFun (congrFun (congrFun h 1) (H e)) (pol i e)
  rw [detPol_H, detPol_H, if_pos rfl] at this
  by_contra hne
  rw [if_neg hne] at this
  norm_num at this

theorem detPol_isPure (j : Fin 4) : (model P).IsPure (detPol j) := fun n h _ => by
  match n with
  | 0 => exact ⟨0, by simp [detPol, νa]⟩
  | n + 1 => exact ⟨pol j (h 0).2, by simp [detPol, νa]⟩

/-- Every fixed point of either rule is pure (the rule's outputs are pure). -/
theorem isPure_of_fp {π : Policy (Fin 2) (Fin 2)} (h : IsPolFloorFP P π ∨ IsPolFloorSelfFP P π) :
    (model P).IsPure π := by
  rcases h with h | h
  · rw [h]; unfold polFloor; split_ifs <;> exact detPol_isPure P _
  · rw [h]; unfold polFloorSelf; split_ifs <;> exact detPol_isPure P _

/-- **No self mass**: `UDT` is the unique fixed point iff `trueValue(2box) < (1-δ) V_upd^*`; otherwise `2box` is the
unique fixed point. Never both, never none. Kind L, not P: `polFloor` is constant in `π` (`polFloor_const`), so this
is "the fixed point of a constant map is its value", with uniqueness as whole-function equality (`IsPolFloorFP`); the
content of target 14's no-self-mass half is `piA_polEq` (2box is the argmax policy for every `π`) and the explicit
inequality `twoClass_cond_iff`. Substitutions: the rule returns `detPol 2` in place of `piA π` (they agree on the
decision nodes, `piA_polEq`) and `w_root = 1 - δ` is used for every `π` (`wS_root`).
Source: [[uea-2-inventory]] 2-006 (target 14; the survey's "unique fixed point is UDT" holds in the first regime only)
Kind: L
Fidelity: exact (both regimes, every `q, δ, f`; regraded L in repair round 1)
Hyps: (a) -/
theorem isPolFloorFP_iff (hf2 : P.f 2 ≠ 0) (π : Policy (Fin 2) (Fin 2)) :
    IsPolFloorFP P π ↔
      (trueValue P 2 < (1 - P.δ) * VupdStar P ∧ π = detPol 0) ∨
      (¬ trueValue P 2 < (1 - P.δ) * VupdStar P ∧ π = detPol 2) := by
  unfold IsPolFloorFP polFloor
  rw [wS_root, Vupd_eq P hf2]
  by_cases hc : trueValue P 2 < (1 - P.δ) * VupdStar P
  · rw [if_pos hc]; simp [hc]
  · rw [if_neg hc]; simp [hc]

/-- The two-hypothesis class `{T_UDT (1-f), T_2box (f)}`. -/
noncomputable def twoClass (q δ f : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hδ : 0 < δ) (hδ1 : δ < 1) (hf0 : 0 < f)
    (hf1 : f < 1) : TP :=
  ⟨q, δ, fun i => if i = 0 then 1 - f else if i = 2 then f else 0, hq0, hq1, hδ, hδ1,
    fun i => by split_ifs <;> linarith,
    by show (1 - f) + 0 + f + 0 = 1; ring⟩

section TwoClass
variable (q δ f : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (hδ : 0 < δ) (hδ1 : δ < 1) (hf0 : 0 < f) (hf1 : f < 1)

local notation "P₂" => twoClass q δ f hq0 hq1 hδ hδ1 hf0 hf1

theorem twoClass_f : (P₂).f 0 = 1 - f ∧ (P₂).f 1 = 0 ∧ (P₂).f 2 = f ∧ (P₂).f 3 = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem twoClass_xiM : xiM P₂ = q * (1 - f) + (1 - q) * f := by
  unfold xiM
  rw [Fin.sum_univ_four]
  simp [twoClass, pM, pol]
  ring

/-- The true values in the two-hypothesis class: `tv0 = q MEG + (1-q) KILO`, `tv2 = (1-q) + q KILO`. -/
theorem twoClass_trueValues : trueValue P₂ 0 = q * MEG + (1 - q) * KILO ∧ trueValue P₂ 2 = (1 - q) + q * KILO :=
  ⟨(trueValues P₂).1, (trueValues P₂).2.2.1⟩

theorem twoClass_Vupd : Vupd P₂ 0 = q * MEG + (1 - q) * KILO ∧ Vupd P₂ 2 = (1 - q) + q * KILO ∧
    Vupd P₂ 1 = 0 ∧ Vupd P₂ 3 = 0 := by
  refine ⟨?_, ?_, Vupd_of_f_eq_zero _ rfl, Vupd_of_f_eq_zero _ rfl⟩
  · rw [Vupd_eq _ (show (P₂).f 0 ≠ 0 by show 1 - f ≠ 0; linarith)]; exact (twoClass_trueValues q δ f hq0 hq1 hδ hδ1 hf0 hf1).1
  · rw [Vupd_eq _ (show (P₂).f 2 ≠ 0 by show f ≠ 0; linarith)]; exact (twoClass_trueValues q δ f hq0 hq1 hδ hδ1 hf0 hf1).2

/-- `V_upd^* = max(tv0, tv2)` (the junk `0`s of the absent policies do not count). -/
theorem twoClass_VupdStar : VupdStar P₂ = max (q * MEG + (1 - q) * KILO) ((1 - q) + q * KILO) := by
  obtain ⟨v0, v2, v1, v3⟩ := twoClass_Vupd q δ f hq0 hq1 hδ hδ1 hf0 hf1
  have hK : 0 ≤ KILO := by unfold KILO; norm_num
  have hM : 0 ≤ MEG := by unfold MEG; norm_num
  apply le_antisymm
  · rw [VupdStar_le_iff]
    intro j
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by revert j; decide
    rcases hj' with rfl | rfl | rfl | rfl
    · rw [v0]; exact le_max_left _ _
    · rw [v1]; exact le_trans (by nlinarith) (le_max_right _ _)
    · rw [v2]; exact le_max_right _ _
    · rw [v3]; exact le_trans (by nlinarith) (le_max_right _ _)
  · exact max_le (by rw [← v0]; exact Vupd_le_VupdStar _ 0) (by rw [← v2]; exact Vupd_le_VupdStar _ 2)

theorem twoClass_VupdStar_eq (hq : 1000 / 1999 < q) : VupdStar P₂ = q * MEG + (1 - q) * KILO := by
  rw [twoClass_VupdStar]
  apply max_eq_left
  unfold MEG KILO
  nlinarith

/-- **No self mass, explicit** (`q > 1000/1999`): `UDT` is the unique fixed point iff
`1001 - 1000 q < (1-δ)(999 q + 1)`, else `2box`.
Source: [[uea-2-inventory]] 2-006 (target 14)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem twoClass_cond_iff (hq : 1000 / 1999 < q) :
    (trueValue P₂ 2 < (1 - δ) * VupdStar P₂) ↔ 1001 - 1000 * q < (1 - δ) * (999 * q + 1) := by
  rw [twoClass_VupdStar_eq q δ f hq0 hq1 hδ hδ1 hf0 hf1 hq, (twoClass_trueValues q δ f hq0 hq1 hδ hδ1 hf0 hf1).2]
  unfold MEG KILO
  constructor <;> intro h <;> nlinarith

/-! ### With self mass: the self-trap threshold -/

/-- `g(f) := (1-δ)(ξ_M + (1-ξ_M) KILO) + δ f tv2 - (1-δ) U ((1-δ) + δ f)` with `ξ_M = q(1-f) + (1-q) f`,
`tv2 = (1-q) + q KILO`, `U = q MEG + (1-q) KILO` (`V_upd^*` for `q > 1000/1999`); `2box` is a self-mass fixed
point iff `g(f) ≥ 0`.
Source: `newcomb_interleaving.py` `self_trap_threshold` (`g`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def g (q δ f : ℝ) : ℝ :=
  (1 - δ) * ((q * (1 - f) + (1 - q) * f) + (1 - (q * (1 - f) + (1 - q) * f)) * KILO) +
    δ * f * ((1 - q) + q * KILO) - (1 - δ) * (q * MEG + (1 - q) * KILO) * ((1 - δ) + δ * f)

/-- `f* := -g(0) / (g(1) - g(0))`. -/
noncomputable def fstar (q δ : ℝ) : ℝ := -g q δ 0 / (g q δ 1 - g q δ 0)

theorem g_affine (q δ f : ℝ) : g q δ f = g q δ 0 + f * (g q δ 1 - g q δ 0) := by
  unfold g; ring

theorem g_one_eq (q δ : ℝ) : g q δ 1 = ((1 - q) + q * KILO) - (1 - δ) * (q * MEG + (1 - q) * KILO) := by
  unfold g; ring

/-- `g(0) > 0` for every `q, δ ∈ (0,1)`: `g(0) = (1-δ)[q + (1-q) KILO - (1-δ) U]` and `U ≤ q + (1-q) KILO`. -/
theorem g_zero_pos (hq0 : 0 < q) (hq1 : q < 1) (hδ : 0 < δ) (hδ1 : δ < 1) : 0 < g q δ 0 := by
  have : g q δ 0 = (1 - δ) * (q + δ * (999 * q + 1)) / 1001 := by unfold g MEG KILO; ring
  rw [this]
  have h1 : 0 < 1 - δ := by linarith
  positivity

/-- `g(1) < 0` iff the `UDT` inequality `1001 - 1000 q < (1-δ)(999 q + 1)`. -/
theorem g_one_neg_iff : g q δ 1 < 0 ↔ 1001 - 1000 * q < (1 - δ) * (999 * q + 1) := by
  rw [g_one_eq]
  unfold MEG KILO
  constructor <;> intro h <;> nlinarith

/-- `UDT` is not `2box` on the decision nodes. -/
theorem not_polEq_detPol_zero_two : ¬ PolEq (detPol 0) 2 := by
  rintro ⟨_, h⟩
  have := h 0
  have h2 : pol 2 0 = 1 := rfl
  have h0 : pol 0 0 = 0 := rfl
  rw [h2, detPol_H, h0, if_neg (by decide)] at this
  norm_num at this

/-- **With self mass, UDT**: `UDT` is a fixed point of the self-mass rule under the same inequality as without self
mass (`UDT ≠ 2box`, so no self term enters).
Source: [[uea-2-inventory]] 2-006 (target 14)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem UDT_selfFP_iff (hf2 : P.f 2 ≠ 0) :
    IsPolFloorSelfFP P (detPol 0) ↔ trueValue P 2 < (1 - P.δ) * VupdStar P := by
  unfold IsPolFloorSelfFP polFloorSelf
  rw [wS_root, VupdSelf_of_not_polEq P not_polEq_detPol_zero_two, Vupd_eq P hf2]
  by_cases hc : trueValue P 2 < (1 - P.δ) * VupdStar P
  · rw [if_pos hc]; simp [hc]
  · rw [if_neg hc]
    refine ⟨fun h => absurd (detPol_injective h) (by decide), fun h => absurd h hc⟩

/-- **With self mass, 2box**: `2box` is a fixed point of the self-mass rule iff `g(f) ≥ 0`
(`q > 1000/1999`, so that `V_upd^* = q MEG + (1-q) KILO`).
Source: [[uea-2-inventory]] 2-006 (target 14)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem twoBox_selfFP_iff (hq : 1000 / 1999 < q) : IsPolFloorSelfFP P₂ (detPol 2) ↔ 0 ≤ g q δ f := by
  have hw : (model P₂).wS (detPol 2) 0 root = 1 - δ := wS_root _ _
  have hV : VupdSelf P₂ (detPol 2) 2 =
      ((1 - δ) * ((q * (1 - f) + (1 - q) * f) + (1 - (q * (1 - f) + (1 - q) * f)) * KILO) +
        δ * f * ((1 - q) + q * KILO)) / ((1 - δ) + δ * f) := by
    rw [VupdSelf_twoBox, twoClass_xiM, (twoClass_trueValues q δ f hq0 hq1 hδ hδ1 hf0 hf1).2]
    rfl
  have hU := twoClass_VupdStar_eq q δ f hq0 hq1 hδ hδ1 hf0 hf1 hq
  have hD : 0 < (1 - δ) + δ * f := by nlinarith
  have hne : detPol 2 ≠ detPol 0 := fun h => absurd (detPol_injective h) (by decide)
  unfold IsPolFloorSelfFP polFloorSelf
  rw [hw, hV, hU]
  split_ifs with hc
  · rw [div_lt_iff₀ hD] at hc
    exact ⟨fun h => absurd h hne, fun hg => by unfold g at hg; nlinarith⟩
  · rw [not_lt, le_div_iff₀ hD] at hc
    exact ⟨fun _ => by unfold g; nlinarith, fun _ => rfl⟩

/-- **The self-trap**: when `g(1) < 0` (the `UDT` inequality), `2box` is a self-mass fixed point iff `f ≤ f*`.
Source: [[uea-2-inventory]] 2-006 (target 14, "the self-trap")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem twoBox_selfFP_iff_le_fstar (hq : 1000 / 1999 < q) (h1 : g q δ 1 < 0) :
    IsPolFloorSelfFP P₂ (detPol 2) ↔ f ≤ fstar q δ := by
  rw [twoBox_selfFP_iff q δ f hq0 hq1 hδ hδ1 hf0 hf1 hq, g_affine]
  have h0 := g_zero_pos q δ hq0 hq1 hδ hδ1
  have hden : 0 < g q δ 0 - g q δ 1 := by linarith
  unfold fstar
  rw [neg_div, ← div_neg, neg_sub, le_div_iff₀ hden]
  constructor <;> intro h <;> nlinarith

/-- **`f*(q, 0) = q KILO / ((2q - 1) MEG)`** — the `δ → 0` limit as the algebraic identity at `δ = 0`.
Source: [[uea-2-inventory]] 2-006 (target 14)
Kind: P
Fidelity: exact (as an identity of rational functions at `δ = 0`; the bound `|f* - f*(q,0)| ≤ 3δ` is `stretch`, not done)
Hyps: (a) -/
theorem fstar_zero (q : ℝ) : fstar q 0 = q * KILO / ((2 * q - 1) * MEG) := by
  have e0 : g q 0 0 = q * KILO := by unfold g MEG KILO; ring
  have e1 : g q 0 1 - g q 0 0 = -((2 * q - 1) * MEG) := by unfold g MEG KILO; ring
  unfold fstar
  rw [e1, e0, neg_div_neg_eq]

/-- **N+ (the numbers)**: `f*(9/10, 1/10) = 81819/790909` and `f*(1, 1/10) = 909/9899`. Only the first is covered by
`twoBox_selfFP_iff_le_fstar` (see `selfTrap_hyps_inhabited`): `q = 1` is excluded by `TP` (`q < 1`), so the second
is arithmetic on the rational function `fstar` alone.
Source: [[uea-2-inventory]] 2-006 (`self_trap_threshold` at `q = 9/10, δ = 1/10`; `q = 1`)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem fstar_values : fstar (9 / 10) (1 / 10) = 81819 / 790909 ∧ fstar 1 (1 / 10) = 909 / 9899 := by
  constructor <;> (unfold fstar g MEG KILO; norm_num)

/-- **N+ (the hypothesis packages are inhabited)**: at `q = 9/10, δ = 1/10` the self-trap theorem's hypotheses hold
(`1000/1999 < 9/10` and `g(1) < 0`), so `twoBox_selfFP_iff_le_fstar` applies there and `f* = 81819/790909` is the
threshold the theorem is about; and the no-self-mass regime split `twoClass_cond_iff` is inhabited on both sides
(`q = 9/10, δ = 1/10` is the `UDT` regime; `q = 51/100, δ = 1/2` is the `2box` regime).
Source: [[uea-2-inventory]] 2-006 (target 14); audit r1 N4 (repair round 1)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem selfTrap_hyps_inhabited :
    (1000 : ℝ) / 1999 < 9 / 10 ∧ g (9 / 10) (1 / 10) 1 < 0 ∧
    (1001 - 1000 * (9 / 10 : ℝ) < (1 - 1 / 10) * (999 * (9 / 10) + 1)) ∧
    ¬ (1001 - 1000 * (51 / 100 : ℝ) < (1 - 1 / 2) * (999 * (51 / 100) + 1)) := by
  refine ⟨by norm_num, ?_, by norm_num, by norm_num⟩
  unfold g MEG KILO
  norm_num

end TwoClass

end PolicyFloor

end Cleanroom.Uea.UeaSinkSwim
