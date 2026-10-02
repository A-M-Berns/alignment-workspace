import Cleanroom.Udt.UdtHarmonyBargain.Harmony
import Cleanroom.Udt.UdtHarmonyBargain.Lex
import Cleanroom.Udt.UdtHarmonyBargain.Counting
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# `udt-harmony-bargain` — Theorem 11.1 is false as stated (T4)

**Quoted claim** ([[superconditioning-mismatched-ontologies]] §11, Theorem 11.1): "In the bargaining
game 𝒢 with a welfare selection rule, any trembling-hand equilibrium outcome is not subjectively
Pareto-dominated."

**Reading formalised** (the source's own definitions, no choice among readings): `THPE` of
`Perturbed.lean` (SC Def. 10.4: uniform floor, existential over the ε-sequence), a pure profile
`σ*`, its outcome `outcome sel σ*`, "not dominated" = FAF's `ParetoOptimalIn`.

**The instance** (HA-4′; dp-cf-003): two players, actions `a/b` (player 0) and `c/d` (player 1)
encoded as `false/true`; outcomes `ac, ad, bc, bd`; `U₁ = (3, 0, 2, 0)`, `U₂ = (0, 0, 1, 3)`;
`W = (3, 1/1000, 4 + 2/1000, 6 + 3/1000)` (injective, Pareto-consistent); `sel` the `W`-argmax
(`bd ≻ bc ≻ ac ≻ ad`); `σ* = ((a, {ac}), (d, {bd}))`: the acceptable sets are disjoint, the outcome
is the batna profile `ad` worth `(0, 0)`, strictly dominated by `bc` worth `(2, 1)`.

**Proof of THPE** via `uniform_thpe_of_lex`: (N) every proposal of either player pays `0` against
`σ*_{-i}` (a case split on the outcome rule); (L) the total `Tᵢ` against all 32 opponent proposals
is maximised at `σ*ᵢ` (`= 72`), by pointwise weak dominance (batna `a ≽ b`; inserting `ac`;
erasing `ad`; erasing `bd`) reducing every proposal to `(a, {ac})` or `(a, {ac, bc})`, whose totals
`72` and `68` are computed by grouping the opponent's acceptable sets by membership bits. The
proof's own deviation "add `bc`" ties at order `ε⁰` and loses exactly `4` at order `ε¹`.
No enumeration of proposals (plan rule 8); `decide` is used only on the 4-element outcome type.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtHarmonyBargain

namespace Thm111

open Finset SafeParetoImprovements StrategicGame

noncomputable section

/-- Two players, two actions each: `false` is `a` (player 0) / `c` (player 1), `true` is `b` / `d`.
Source: HA-4′; dp-cf-003
Kind: D -/
abbrev Act : Fin 2 → Type := fun _ => Bool

/-- Outcomes `Fin 2 → Bool`. Source: HA-4′. Kind: D -/
abbrev Out : Type := Outcome Act

/-- `ac`. Source: HA-4′. Kind: D -/
def ac : Out := ![false, false]
/-- `ad`. Source: HA-4′. Kind: D -/
def ad : Out := ![false, true]
/-- `bc`. Source: HA-4′. Kind: D -/
def bc : Out := ![true, false]
/-- `bd`. Source: HA-4′. Kind: D -/
def bd : Out := ![true, true]

/-- `U₁ : ac ↦ 3, ad ↦ 0, bc ↦ 2, bd ↦ 0` (integer form). Source: HA-4′. Kind: D -/
def u1z (O : Out) : ℤ := if O 1 then 0 else if O 0 then 2 else 3

/-- `U₂ : ac ↦ 0, ad ↦ 0, bc ↦ 1, bd ↦ 3` (integer form). Source: HA-4′. Kind: D -/
def u2z (O : Out) : ℤ := if O 0 then (if O 1 then 3 else 1) else 0

/-- `1000·W : ac ↦ 3000, ad ↦ 1, bc ↦ 4002, bd ↦ 6003`. Source: HA-4′. Kind: D -/
def wz (O : Out) : ℤ := if O 0 then (if O 1 then 6003 else 4002) else (if O 1 then 1 else 3000)

/-- The utilities as reals. Source: HA-4′. Kind: D -/
def Ureal : Fin 2 → Out → ℝ := ![fun O => (u1z O : ℝ), fun O => (u2z O : ℝ)]

/-- **The counterexample game** `Γ = utilGame Ureal`. Source: HA-4′; dp-cf-003. Kind: D -/
def Γ : Game (Fin 2) Act := utilGame Ureal

/-- `W = wz / 1000`. Source: HA-4′. Kind: D -/
def W (O : Out) : ℝ := (wz O : ℝ) / 1000

/-- The `W`-argmax selector, written out by the order `bd ≻ bc ≻ ac ≻ ad`.
Source: HA-4′; dp-cf-003 (`outcome_W_maximal`)
Kind: D -/
def selW (S : Finset Out) : Out :=
  if bd ∈ S then bd else if bc ∈ S then bc else if ac ∈ S then ac else ad

/-! ### Facts about the four outcomes (`decide` on a 4-element type) -/

theorem out_cases : ∀ O : Out, O = ac ∨ O = ad ∨ O = bc ∨ O = bd := by decide
theorem ac_ne_ad : ac ≠ ad := by decide
theorem ac_ne_bc : ac ≠ bc := by decide
theorem ac_ne_bd : ac ≠ bd := by decide
theorem ad_ne_bc : ad ≠ bc := by decide
theorem ad_ne_bd : ad ≠ bd := by decide
theorem bc_ne_bd : bc ≠ bd := by decide
theorem card_out : Fintype.card Out = 4 := by decide
theorem ad_ne_ac : ad ≠ ac := by decide
theorem bc_ne_ac : bc ≠ ac := by decide
theorem bd_ne_ac : bd ≠ ac := by decide
theorem bc_ne_ad : bc ≠ ad := by decide
theorem bd_ne_ad : bd ≠ ad := by decide
theorem bd_ne_bc : bd ≠ bc := by decide

theorem u1z_ac : u1z ac = 3 := by decide
theorem u1z_ad : u1z ad = 0 := by decide
theorem u1z_bc : u1z bc = 2 := by decide
theorem u1z_bd : u1z bd = 0 := by decide
theorem u1z_pair_false : ∀ b : Bool, u1z ![false, b] = if b then 0 else 3 := by decide
theorem u2z_ac : u2z ac = 0 := by decide
theorem u2z_ad : u2z ad = 0 := by decide
theorem u2z_bc : u2z bc = 1 := by decide
theorem u2z_bd : u2z bd = 3 := by decide
theorem u2z_pair_true : ∀ b : Bool, u2z ![b, true] = if b then 3 else 0 := by decide
theorem selW_singleton_ac : selW {ac} = ac := by decide
theorem selW_singleton_bc : selW {bc} = bc := by decide
theorem selW_singleton_bd : selW {bd} = bd := by decide
theorem selW_pair_ac_bc : selW {ac, bc} = bc := by decide
theorem selW_pair_bd_bc : selW {bd, bc} = bd := by decide

theorem u1z_le : ∀ O : Out, u1z O ≤ 3 := by decide
theorem u1z_nonneg : ∀ O : Out, 0 ≤ u1z O := by decide
theorem u1z_of_one : ∀ O : Out, O 1 = true → u1z O = 0 := by decide
theorem u2z_le : ∀ O : Out, u2z O ≤ 3 := by decide
theorem u2z_nonneg : ∀ O : Out, 0 ≤ u2z O := by decide
theorem u2z_of_zero : ∀ O : Out, O 0 = false → u2z O = 0 := by decide

theorem wz_pareto : ∀ O O' : Out, (u1z O ≤ u1z O' ∧ u2z O ≤ u2z O') →
    (u1z O < u1z O' ∨ u2z O < u2z O') → wz O < wz O' := by decide
theorem wz_injective : ∀ O O' : Out, wz O = wz O' → O = O' := by decide
theorem wz_le_bd : ∀ O : Out, wz O ≤ wz bd := by decide
theorem wz_le_bc : ∀ O : Out, O ≠ bd → wz O ≤ wz bc := by decide
theorem wz_le_ac : ∀ O : Out, O ≠ bd → O ≠ bc → wz O ≤ wz ac := by decide
theorem eq_ad_of_ne : ∀ O : Out, O ≠ bd → O ≠ bc → O ≠ ac → O = ad := by decide

@[simp] theorem Γ_u_zero (O : Out) : Γ.u O 0 = (u1z O : ℝ) := rfl
@[simp] theorem Γ_u_one (O : Out) : Γ.u O 1 = (u2z O : ℝ) := rfl

theorem W_mono {O O' : Out} (h : wz O ≤ wz O') : W O ≤ W O' := by
  unfold W
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num)

/-- `W` is Pareto-consistent for `Γ` (the only dominated pair is `ad ≺ bc`, and `W(ad)` is minimal).
Source: HA-4′
Kind: P -/
theorem paretoConsistent_W : ParetoConsistent Γ W := by
  intro O O' h
  rw [paretoDom_iff] at h
  obtain ⟨hle, hex⟩ := h
  have h0 := hle 0
  have h1 := hle 1
  rw [Γ_u_zero, Γ_u_zero, Int.cast_le] at h0
  rw [Γ_u_one, Γ_u_one, Int.cast_le] at h1
  rw [Fin.exists_fin_two, Γ_u_zero, Γ_u_zero, Γ_u_one, Γ_u_one, Int.cast_lt, Int.cast_lt] at hex
  unfold W
  rw [div_lt_div_iff_of_pos_right (by norm_num)]
  exact_mod_cast wz_pareto O O' ⟨h0, h1⟩ hex

/-- `W` is injective. Source: HA-4′. Kind: L -/
theorem W_injective : Function.Injective W := by
  intro O O' h
  unfold W at h
  rw [div_left_inj' (by norm_num : (1000 : ℝ) ≠ 0), Int.cast_inj] at h
  exact wz_injective O O' h

/-- **`selW` is a welfare selection rule** with welfare `W` (dp-cf-003's `outcome_W_maximal`
repair: the hard-coded order is the `W`-argmax).
Source: HA-4′; dp-cf-003
Kind: P -/
theorem isWelfareSel_selW : IsWelfareSel Γ selW W := by
  refine ⟨paretoConsistent_W, fun S hS => ?_⟩
  unfold selW
  split_ifs with h1 h2 h3
  · exact ⟨h1, fun O _ => W_mono (wz_le_bd O)⟩
  · exact ⟨h2, fun O hO => W_mono (wz_le_bc O fun h => h1 (h ▸ hO))⟩
  · exact ⟨h3, fun O hO => W_mono (wz_le_ac O (fun h => h1 (h ▸ hO)) fun h => h2 (h ▸ hO))⟩
  · obtain ⟨O, hO⟩ := hS
    have hOad : O = ad :=
      eq_ad_of_ne O (fun h => h1 (h ▸ hO)) (fun h => h2 (h ▸ hO)) fun h => h3 (h ▸ hO)
    refine ⟨hOad ▸ hO, fun O' hO' => ?_⟩
    have : O' = ad :=
      eq_ad_of_ne O' (fun h => h1 (h ▸ hO')) (fun h => h2 (h ▸ hO')) fun h => h3 (h ▸ hO')
    rw [this]

/-! ### The profile `σ*` -/

/-- Universe proposal profiles of the two-player game from a pair of proposals.
Source: none: infrastructure
Kind: D -/
def up (x y : Bool × Finset Out) : ∀ i : Fin 2, Proposal Act i := ![x, y]

@[simp] theorem up_zero (x y : Bool × Finset Out) : up x y 0 = x := rfl
@[simp] theorem up_one (x y : Bool × Finset Out) : up x y 1 = y := rfl

/-- The realised outcome of the proposal pair `(x, y)` under `selW`.
Source: none: infrastructure
Kind: D -/
def o (x y : Bool × Finset Out) : Out := outcome selW (up x y)

theorem o_eq (x y : Bool × Finset Out) :
    o x y = if (x.2 ∩ y.2).Nonempty then selW (x.2 ∩ y.2) else ![x.1, y.1] := by
  unfold o outcome
  rw [inter_two]
  simp only [up_zero, up_one]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **`σ* = ((a, {ac}), (d, {bd}))`**. Source: HA-4′; dp-cf-003 (`star1 = 1`, `star2 = 24`). Kind: D -/
def sStar : ∀ i : Fin 2, Proposal Act i := up (false, {ac}) (true, {bd})

/-- The outcome of `σ*` is the batna profile `ad` (the acceptable sets are disjoint).
Source: HA-4′; dp-cf-003 (`outcome_star`)
Kind: P -/
theorem outcome_sStar : outcome selW sStar = ad := by
  show o (false, {ac}) (true, {bd}) = ad
  rw [o_eq]
  have : ({ac} : Finset Out) ∩ {bd} = ∅ := by
    rw [singleton_inter_of_notMem]
    simp [ac_ne_bd]
  simp only [this]
  rw [if_neg (by simp)]
  rfl

/-- `bc` strictly dominates `ad` for **both** players (`2 > 0`, `1 > 0`).
Source: HA-4′; dp-cf-003 (`bc_dominates_ad`)
Kind: P -/
theorem ad_lt_bc_both : Γ.u ad 0 < Γ.u bc 0 ∧ Γ.u ad 1 < Γ.u bc 1 := by
  simp only [Γ_u_zero, Γ_u_one]
  constructor <;> exact_mod_cast (by decide : _)

/-- `bc` subjectively Pareto-dominates `ad`. Source: HA-4′. Kind: P -/
theorem paretoDom_ad_bc : ParetoDom Γ ad bc := by
  rw [paretoDom_iff]
  obtain ⟨h0, h1⟩ := ad_lt_bc_both
  refine ⟨?_, 0, h0⟩
  intro i
  fin_cases i
  · exact h0.le
  · exact h1.le

/-! ### Player 0: (N) and (L) -/

/-- (N) for player 0: every proposal pays `0` against `σ*₁ = (d, {bd})` — the outcome is `bd` or a
batna profile with second coordinate `d`.
Source: HA-4′; dp-cf-003 (`nash_player1`)
Kind: P -/
theorem N0 (x : Bool × Finset Out) : u1z (o x (true, {bd})) = 0 := by
  apply u1z_of_one
  unfold o
  rcases outcome_eq_sel_or_batna selW (up x (true, {bd})) with ⟨hne, h⟩ | ⟨-, h⟩
  · rw [h]
    have hmem := (isWelfareSel_selW.2 _ hne).1
    rw [mem_inter] at hmem
    have h1 := hmem 1
    simp only [up_one, mem_singleton] at h1
    rw [h1]
    rfl
  · rw [h]
    rfl

/-- Player 0's total against every opponent proposal (rational-valued for the counting lemmas).
Source: HA-4′; dp-cf-003 (`T1`)
Kind: D -/
def t0 (x : Bool × Finset Out) : ℚ := ∑ y : Bool × Finset Out, (u1z (o x y) : ℚ)

theorem t0_mono {x x' : Bool × Finset Out} (h : ∀ y, u1z (o x y) ≤ u1z (o x' y)) :
    t0 x ≤ t0 x' :=
  sum_le_sum fun y _ => by exact_mod_cast h y

theorem selW_insert_ac (I : Finset Out) :
    selW (insert ac I) = if bd ∈ I then bd else if bc ∈ I then bc else ac := by
  unfold selW
  simp [mem_insert, ac_ne_bd.symm, ac_ne_bc.symm]

theorem selW_erase_ad (I : Finset Out) : selW (I.erase ad) = selW I := by
  unfold selW
  simp [mem_erase, ac_ne_ad, ad_ne_bc.symm, ad_ne_bd.symm]

theorem selW_erase_bd (I : Finset Out) :
    selW (I.erase bd) = if bc ∈ I then bc else if ac ∈ I then ac else ad := by
  unfold selW
  simp [mem_erase, ac_ne_bd, bc_ne_bd]

theorem u1z_batna_le : ∀ b : Bool, u1z ![true, b] ≤ u1z ![false, b] := by decide

/-- (D1) batna `a` weakly dominates `b` pointwise. Source: mandate T4. Kind: P -/
theorem D0_batna (𝒜 : Finset Out) (y : Bool × Finset Out) :
    u1z (o (true, 𝒜) y) ≤ u1z (o (false, 𝒜) y) := by
  rw [o_eq, o_eq]
  simp only
  split_ifs
  · exact le_refl _
  · exact u1z_batna_le y.1

/-- (D2) inserting `ac` never lowers player 0's payoff pointwise. Source: mandate T4. Kind: P -/
theorem D0_insert_ac (𝒜 : Finset Out) (y : Bool × Finset Out) :
    u1z (o (false, 𝒜) y) ≤ u1z (o (false, insert ac 𝒜) y) := by
  rw [o_eq, o_eq]
  simp only
  by_cases hac : ac ∈ y.2
  · rw [insert_inter_of_mem hac, if_pos (insert_nonempty _ _), selW_insert_ac]
    by_cases hbd : bd ∈ 𝒜 ∩ y.2
    · rw [if_pos hbd, if_pos ⟨bd, hbd⟩]
      unfold selW
      rw [if_pos hbd]
    · rw [if_neg hbd]
      by_cases hbc : bc ∈ 𝒜 ∩ y.2
      · rw [if_pos hbc, if_pos ⟨bc, hbc⟩]
        unfold selW
        rw [if_neg hbd, if_pos hbc]
      · rw [if_neg hbc]
        exact le_trans (u1z_le _) (by decide)
  · rw [insert_inter_of_notMem hac]

theorem erase_inter' (s t : Finset Out) (a : Out) : s.erase a ∩ t = (s ∩ t).erase a := by
  ext z
  simp only [Finset.mem_erase, Finset.mem_inter]
  tauto

/-- (D3) erasing `ad` never lowers player 0's payoff pointwise. Source: mandate T4. Kind: P -/
theorem D0_erase_ad (𝒜 : Finset Out) (y : Bool × Finset Out) :
    u1z (o (false, 𝒜) y) ≤ u1z (o (false, 𝒜.erase ad) y) := by
  rw [o_eq, o_eq]
  simp only
  rw [erase_inter', selW_erase_ad]
  by_cases hne : ((𝒜 ∩ y.2).erase ad).Nonempty
  · rw [if_pos hne, if_pos (hne.mono (erase_subset _ _))]
  · rw [if_neg hne]
    split_ifs with h
    · -- the intersection is `{ad}`: the old outcome is `ad`, worth `0`
      have hsub : 𝒜 ∩ y.2 ⊆ {ad} := by
        intro z hz
        rw [mem_singleton]
        by_contra hz'
        exact hne ⟨z, mem_erase.mpr ⟨hz', hz⟩⟩
      have hI : 𝒜 ∩ y.2 = {ad} := (subset_singleton_iff.mp hsub).resolve_left h.ne_empty
      rw [hI]
      unfold selW
      rw [if_neg (by simp [ad_ne_bd.symm]), if_neg (by simp [ad_ne_bc.symm]),
        if_neg (by simp [ac_ne_ad])]
      exact le_trans (by decide) (u1z_nonneg _)
    · exact le_refl _

/-- (D4) erasing `bd` never lowers player 0's payoff pointwise. Source: mandate T4. Kind: P -/
theorem D0_erase_bd (𝒜 : Finset Out) (y : Bool × Finset Out) :
    u1z (o (false, 𝒜) y) ≤ u1z (o (false, 𝒜.erase bd) y) := by
  rw [o_eq, o_eq]
  simp only
  rw [erase_inter']
  by_cases hbd : bd ∈ 𝒜 ∩ y.2
  · rw [if_pos ⟨bd, hbd⟩]
    have : selW (𝒜 ∩ y.2) = bd := by unfold selW; rw [if_pos hbd]
    rw [this]
    exact le_trans (by decide) (u1z_nonneg _)
  · rw [erase_eq_of_notMem hbd]

/-- After the three moves, the acceptable set is `{ac}` or `{ac, bc}`.
Source: mandate T4
Kind: L -/
theorem reduced_set (𝒜 : Finset Out) :
    ((insert ac 𝒜).erase ad).erase bd = {ac} ∨ ((insert ac 𝒜).erase ad).erase bd = {ac, bc} := by
  set S := ((insert ac 𝒜).erase ad).erase bd with hS
  have hac : ac ∈ S := by simp [hS, ac_ne_ad, ac_ne_bd]
  have had : ad ∉ S := by simp [hS]
  have hbd : bd ∉ S := by simp [hS]
  by_cases hbc : bc ∈ S
  · right
    ext O
    rcases out_cases O with rfl | rfl | rfl | rfl <;>
      simp [hac, had, hbd, hbc, ac_ne_ad, ac_ne_bc, ac_ne_bd, ad_ne_bc, ad_ne_bd, bc_ne_bd,
        ad_ne_ac, bc_ne_ac, bd_ne_ac, bc_ne_ad, bd_ne_ad, bd_ne_bc]
  · left
    ext O
    rcases out_cases O with rfl | rfl | rfl | rfl <;>
      simp [hac, had, hbd, hbc, ac_ne_ad, ac_ne_bc, ac_ne_bd, ad_ne_bc, ad_ne_bd, bc_ne_bd,
        ad_ne_ac, bc_ne_ac, bd_ne_ac, bc_ne_ad, bd_ne_ad, bd_ne_bc]

/-- Every proposal is dominated in `t0` by `(a, {ac})` or `(a, {ac, bc})`.
Source: mandate T4 (the dominance chain)
Kind: C -/
theorem t0_le_candidates (x : Bool × Finset Out) :
    t0 x ≤ t0 (false, {ac}) ∨ t0 x ≤ t0 (false, {ac, bc}) := by
  obtain ⟨b, 𝒜⟩ := x
  have h1 : t0 (b, 𝒜) ≤ t0 (false, 𝒜) := by
    cases b
    · exact le_refl _
    · exact t0_mono (D0_batna 𝒜)
  have h2 : t0 (false, 𝒜) ≤ t0 (false, insert ac 𝒜) := t0_mono (D0_insert_ac 𝒜)
  have h3 : t0 (false, insert ac 𝒜) ≤ t0 (false, (insert ac 𝒜).erase ad) :=
    t0_mono (D0_erase_ad _)
  have h4 : t0 (false, (insert ac 𝒜).erase ad) ≤ t0 (false, ((insert ac 𝒜).erase ad).erase bd) :=
    t0_mono (D0_erase_bd _)
  rcases reduced_set 𝒜 with h | h
  · left; rw [h] at h4; linarith
  · right; rw [h] at h4; linarith

/-! ### The two totals: `72` and `68` -/

theorem sum_prod_bool (f : Bool × Finset Out → ℚ) :
    ∑ y, f y = ∑ S, f (false, S) + ∑ S, f (true, S) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool, add_comm]

/-- The one-bit value table of `(a, {ac})`. Source: mandate T4. Kind: D -/
def F0 (b : Bool) (bit : Bool) : ℚ := if bit then 3 else if b then 0 else 3

/-- `u1z (o (a, {ac}) (b, 𝒜₂))` depends on `𝒜₂` only through `[ac ∈ 𝒜₂]`.
Source: mandate T4 (grouping)
Kind: L -/
theorem o_ac_bits (b : Bool) (S : Finset Out) :
    (u1z (o (false, {ac}) (b, S)) : ℚ) = F0 b (decide (ac ∈ S)) := by
  rw [o_eq]
  simp only
  by_cases h : ac ∈ S
  · rw [singleton_inter_of_mem h, if_pos (singleton_nonempty _), selW_singleton_ac, u1z_ac]
    simp [F0, h]
  · rw [singleton_inter_of_notMem h, if_neg (by simp), u1z_pair_false]
    cases b <;> simp [F0, h]

/-- **`T₁(a, {ac}) = 72`**. Source: HA-4′; dp-cf-003 (regression: `72`). Kind: P -/
theorem t0_star : t0 (false, {ac}) = 72 := by
  unfold t0
  rw [sum_prod_bool]
  simp_rw [o_ac_bits]
  rw [sum_finset_one_bit, sum_finset_one_bit, card_out]
  simp [F0]
  norm_num

/-- The two-bit value table of `(a, {ac, bc})`. Source: mandate T4. Kind: D -/
def F1 (b : Bool) (x y : Bool) : ℚ := if y then 2 else if x then 3 else if b then 0 else 3

/-- `u1z (o (a, {ac, bc}) (b, 𝒜₂))` depends on `𝒜₂` only through `[ac ∈ 𝒜₂], [bc ∈ 𝒜₂]`.
Source: mandate T4 (grouping)
Kind: L -/
theorem o_acbc_bits (b : Bool) (S : Finset Out) :
    (u1z (o (false, {ac, bc}) (b, S)) : ℚ) = F1 b (decide (ac ∈ S)) (decide (bc ∈ S)) := by
  rw [o_eq]
  simp only
  by_cases hac : ac ∈ S <;> by_cases hbc : bc ∈ S
  · rw [insert_inter_of_mem hac, singleton_inter_of_mem hbc, if_pos (insert_nonempty _ _),
      selW_pair_ac_bc, u1z_bc]
    simp [F1, hac, hbc]
  · rw [insert_inter_of_mem hac, singleton_inter_of_notMem hbc, if_pos (insert_nonempty _ _),
      insert_empty, selW_singleton_ac, u1z_ac]
    simp [F1, hac, hbc]
  · rw [insert_inter_of_notMem hac, singleton_inter_of_mem hbc, if_pos (singleton_nonempty _),
      selW_singleton_bc, u1z_bc]
    simp [F1, hac, hbc]
  · rw [insert_inter_of_notMem hac, singleton_inter_of_notMem hbc, if_neg (by simp),
      u1z_pair_false]
    cases b <;> simp [F1, hac, hbc]

/-- **`T₁(a, {ac, bc}) = 68`**: SC's deviation "add `bc`" loses `4` at order `ε`.
Source: HA-4′; dp-cf-003 (regression: `68`, `4`)
Kind: P -/
theorem t0_alt : t0 (false, {ac, bc}) = 68 := by
  unfold t0
  rw [sum_prod_bool]
  simp_rw [o_acbc_bits]
  rw [sum_finset_two_bits ac_ne_bc, sum_finset_two_bits ac_ne_bc, card_out]
  simp [F1]
  norm_num

/-- **(L) for player 0**: `T₁` is maximised at `σ*₀`.
Source: HA-4′; dp-cf-003 (`lex_player1`)
Kind: C -/
theorem t0_max (x : Bool × Finset Out) : t0 x ≤ t0 (false, {ac}) := by
  rcases t0_le_candidates x with h | h
  · exact h
  · rw [t0_star]; rw [t0_alt] at h; linarith

/-- **The convicting sentence**: SC's proof deviation `(a, {ac, bc})` ties with `σ*₀` at order
`ε⁰` (both pay `0`) and loses exactly `4` at order `ε¹`.
Source: HA-4′ ("+8 − 4 − 8 = −4"); dp-cf-003 (`add_bc_ties_first_order`, `add_bc_loses_second_order`)
Kind: P -/
theorem add_bc_loses_four :
    u1z (o (false, {ac, bc}) (true, {bd})) = u1z (o (false, {ac}) (true, {bd})) ∧
      t0 (false, {ac}) - t0 (false, {ac, bc}) = 4 := by
  refine ⟨by rw [N0, N0], ?_⟩
  rw [t0_star, t0_alt]; norm_num

/-! ### Player 1: (N) and (L) -/

/-- (N) for player 1: every proposal pays `0` against `σ*₀ = (a, {ac})` — the outcome is `ac` or a
batna profile with first coordinate `a`.
Source: HA-4′; dp-cf-003 (`nash_player2`)
Kind: P -/
theorem N1 (y : Bool × Finset Out) : u2z (o (false, {ac}) y) = 0 := by
  apply u2z_of_zero
  unfold o
  rcases outcome_eq_sel_or_batna selW (up (false, {ac}) y) with ⟨hne, h⟩ | ⟨-, h⟩
  · rw [h]
    have hmem := (isWelfareSel_selW.2 _ hne).1
    rw [mem_inter] at hmem
    have h0 := hmem 0
    simp only [up_zero, mem_singleton] at h0
    rw [h0]
    rfl
  · rw [h]
    rfl

/-- Player 1's total against every opponent proposal.
Source: HA-4′; dp-cf-003 (`T2`)
Kind: D -/
def t1 (y : Bool × Finset Out) : ℚ := ∑ x : Bool × Finset Out, (u2z (o x y) : ℚ)

theorem t1_mono {y y' : Bool × Finset Out} (h : ∀ x, u2z (o x y) ≤ u2z (o x y')) :
    t1 y ≤ t1 y' :=
  sum_le_sum fun x _ => by exact_mod_cast h x

theorem selW_insert_bd (I : Finset Out) : selW (insert bd I) = bd := by
  unfold selW
  simp

theorem selW_erase_ac (I : Finset Out) :
    selW (I.erase ac) = if bd ∈ I then bd else if bc ∈ I then bc else ad := by
  unfold selW
  simp [mem_erase, bd_ne_ac, bc_ne_ac]

theorem u2z_batna_le : ∀ b : Bool, u2z ![b, false] ≤ u2z ![b, true] := by decide

theorem inter_erase' (s t : Finset Out) (a : Out) : s ∩ t.erase a = (s ∩ t).erase a := by
  ext z
  simp only [Finset.mem_erase, Finset.mem_inter]
  tauto

/-- (D1′) batna `d` weakly dominates `c` pointwise. Source: mandate T4. Kind: P -/
theorem D1_batna (𝒜 : Finset Out) (x : Bool × Finset Out) :
    u2z (o x (false, 𝒜)) ≤ u2z (o x (true, 𝒜)) := by
  rw [o_eq, o_eq]
  simp only
  split_ifs
  · exact le_refl _
  · exact u2z_batna_le x.1

/-- (D2′) inserting `bd` never lowers player 1's payoff pointwise. Source: mandate T4. Kind: P -/
theorem D1_insert_bd (𝒜 : Finset Out) (x : Bool × Finset Out) :
    u2z (o x (true, 𝒜)) ≤ u2z (o x (true, insert bd 𝒜)) := by
  rw [o_eq, o_eq]
  simp only
  by_cases hbd : bd ∈ x.2
  · rw [inter_insert_of_mem hbd, if_pos (insert_nonempty _ _), selW_insert_bd, u2z_bd]
    exact le_trans (u2z_le _) (le_refl _)
  · rw [inter_insert_of_notMem hbd]

/-- (D3′) erasing `ac` never lowers player 1's payoff pointwise. Source: mandate T4. Kind: P -/
theorem D1_erase_ac (𝒜 : Finset Out) (x : Bool × Finset Out) :
    u2z (o x (true, 𝒜)) ≤ u2z (o x (true, 𝒜.erase ac)) := by
  rw [o_eq, o_eq]
  simp only
  rw [inter_erase', selW_erase_ac]
  by_cases hne : ((x.2 ∩ 𝒜).erase ac).Nonempty
  · rw [if_pos hne, if_pos (hne.mono (erase_subset _ _))]
    unfold selW
    by_cases hbd : bd ∈ x.2 ∩ 𝒜
    · rw [if_pos hbd, if_pos hbd]
    · rw [if_neg hbd, if_neg hbd]
      by_cases hbc : bc ∈ x.2 ∩ 𝒜
      · rw [if_pos hbc, if_pos hbc]
      · rw [if_neg hbc, if_neg hbc]
        split_ifs
        · rw [u2z_ac, u2z_ad]
        · exact le_refl _
  · rw [if_neg hne]
    split_ifs with h
    · have hsub : x.2 ∩ 𝒜 ⊆ {ac} := by
        intro z hz
        rw [mem_singleton]
        by_contra hz'
        exact hne ⟨z, mem_erase.mpr ⟨hz', hz⟩⟩
      have hI : x.2 ∩ 𝒜 = {ac} := (subset_singleton_iff.mp hsub).resolve_left h.ne_empty
      rw [hI, selW_singleton_ac, u2z_ac]
      exact u2z_nonneg _
    · exact le_refl _

/-- (D4′) erasing `ad` never lowers player 1's payoff pointwise. Source: mandate T4. Kind: P -/
theorem D1_erase_ad (𝒜 : Finset Out) (x : Bool × Finset Out) :
    u2z (o x (true, 𝒜)) ≤ u2z (o x (true, 𝒜.erase ad)) := by
  rw [o_eq, o_eq]
  simp only
  rw [inter_erase', selW_erase_ad]
  by_cases hne : ((x.2 ∩ 𝒜).erase ad).Nonempty
  · rw [if_pos hne, if_pos (hne.mono (erase_subset _ _))]
  · rw [if_neg hne]
    split_ifs with h
    · have hsub : x.2 ∩ 𝒜 ⊆ {ad} := by
        intro z hz
        rw [mem_singleton]
        by_contra hz'
        exact hne ⟨z, mem_erase.mpr ⟨hz', hz⟩⟩
      have hI : x.2 ∩ 𝒜 = {ad} := (subset_singleton_iff.mp hsub).resolve_left h.ne_empty
      rw [hI]
      unfold selW
      rw [if_neg (by simp [bd_ne_ad]), if_neg (by simp [bc_ne_ad]), if_neg (by simp [ac_ne_ad]),
        u2z_ad]
      exact u2z_nonneg _
    · exact le_refl _

/-- After the three moves, player 1's acceptable set is `{bd}` or `{bd, bc}`.
Source: mandate T4
Kind: L -/
theorem reduced_set1 (𝒜 : Finset Out) :
    ((insert bd 𝒜).erase ac).erase ad = {bd} ∨ ((insert bd 𝒜).erase ac).erase ad = {bd, bc} := by
  set S := ((insert bd 𝒜).erase ac).erase ad with hS
  have hbd : bd ∈ S := by simp [hS, bd_ne_ac, bd_ne_ad]
  have hac : ac ∉ S := by simp [hS]
  have had : ad ∉ S := by simp [hS]
  by_cases hbc : bc ∈ S
  · right
    ext O
    rcases out_cases O with rfl | rfl | rfl | rfl <;>
      simp [hac, had, hbd, hbc, ac_ne_ad, ac_ne_bc, ac_ne_bd, ad_ne_bc, ad_ne_bd, bc_ne_bd,
        ad_ne_ac, bc_ne_ac, bd_ne_ac, bc_ne_ad, bd_ne_ad, bd_ne_bc]
  · left
    ext O
    rcases out_cases O with rfl | rfl | rfl | rfl <;>
      simp [hac, had, hbd, hbc, ac_ne_ad, ac_ne_bc, ac_ne_bd, ad_ne_bc, ad_ne_bd, bc_ne_bd,
        ad_ne_ac, bc_ne_ac, bd_ne_ac, bc_ne_ad, bd_ne_ad, bd_ne_bc]

/-- Every proposal of player 1 is dominated in `t1` by `(d, {bd})` or `(d, {bd, bc})`.
Source: mandate T4 (the dominance chain)
Kind: C -/
theorem t1_le_candidates (y : Bool × Finset Out) :
    t1 y ≤ t1 (true, {bd}) ∨ t1 y ≤ t1 (true, {bd, bc}) := by
  obtain ⟨b, 𝒜⟩ := y
  have h1 : t1 (b, 𝒜) ≤ t1 (true, 𝒜) := by
    cases b
    · exact t1_mono (D1_batna 𝒜)
    · exact le_refl _
  have h2 : t1 (true, 𝒜) ≤ t1 (true, insert bd 𝒜) := t1_mono (D1_insert_bd 𝒜)
  have h3 : t1 (true, insert bd 𝒜) ≤ t1 (true, (insert bd 𝒜).erase ac) :=
    t1_mono (D1_erase_ac _)
  have h4 : t1 (true, (insert bd 𝒜).erase ac) ≤ t1 (true, ((insert bd 𝒜).erase ac).erase ad) :=
    t1_mono (D1_erase_ad _)
  rcases reduced_set1 𝒜 with h | h
  · left; rw [h] at h4; linarith
  · right; rw [h] at h4; linarith

/-- The one-bit value table of `(d, {bd})`. Source: mandate T4. Kind: D -/
def G0 (b : Bool) (bit : Bool) : ℚ := if bit then 3 else if b then 3 else 0

theorem o_bd_bits (b : Bool) (S : Finset Out) :
    (u2z (o (b, S) (true, {bd})) : ℚ) = G0 b (decide (bd ∈ S)) := by
  rw [o_eq]
  simp only
  by_cases h : bd ∈ S
  · rw [inter_singleton_of_mem h, if_pos (singleton_nonempty _), selW_singleton_bd, u2z_bd]
    simp [G0, h]
  · rw [inter_singleton_of_notMem h, if_neg (by simp), u2z_pair_true]
    cases b <;> simp [G0, h]

/-- **`T₂(d, {bd}) = 72`**. Source: HA-4′; dp-cf-003 (regression: `72`). Kind: P -/
theorem t1_star : t1 (true, {bd}) = 72 := by
  unfold t1
  rw [sum_prod_bool]
  simp_rw [o_bd_bits]
  rw [sum_finset_one_bit, sum_finset_one_bit, card_out]
  simp [G0]
  norm_num

/-- The two-bit value table of `(d, {bd, bc})`. Source: mandate T4. Kind: D -/
def G1 (b : Bool) (x y : Bool) : ℚ := if x then 3 else if y then 1 else if b then 3 else 0

theorem o_bdbc_bits (b : Bool) (S : Finset Out) :
    (u2z (o (b, S) (true, {bd, bc})) : ℚ) = G1 b (decide (bd ∈ S)) (decide (bc ∈ S)) := by
  rw [o_eq]
  simp only
  by_cases hbd : bd ∈ S <;> by_cases hbc : bc ∈ S
  · rw [inter_insert_of_mem hbd, inter_singleton_of_mem hbc, if_pos (insert_nonempty _ _),
      selW_pair_bd_bc, u2z_bd]
    simp [G1, hbd, hbc]
  · rw [inter_insert_of_mem hbd, inter_singleton_of_notMem hbc, if_pos (insert_nonempty _ _),
      insert_empty, selW_singleton_bd, u2z_bd]
    simp [G1, hbd, hbc]
  · rw [inter_insert_of_notMem hbd, inter_singleton_of_mem hbc, if_pos (singleton_nonempty _),
      selW_singleton_bc, u2z_bc]
    simp [G1, hbd, hbc]
  · rw [inter_insert_of_notMem hbd, inter_singleton_of_notMem hbc, if_neg (by simp),
      u2z_pair_true]
    cases b <;> simp [G1, hbd, hbc]

/-- **`T₂(d, {bd, bc}) = 68`**: player 1's "add `bc`" also loses `4` at order `ε`.
Source: HA-4′; dp-cf-003 (regression: `68`, `4`)
Kind: P -/
theorem t1_alt : t1 (true, {bd, bc}) = 68 := by
  unfold t1
  rw [sum_prod_bool]
  simp_rw [o_bdbc_bits]
  rw [sum_finset_two_bits bd_ne_bc, sum_finset_two_bits bd_ne_bc, card_out]
  simp [G1]
  norm_num

/-- **(L) for player 1**: `T₂` is maximised at `σ*₁`.
Source: HA-4′; dp-cf-003 (`lex_player2`)
Kind: C -/
theorem t1_max (y : Bool × Finset Out) : t1 y ≤ t1 (true, {bd}) := by
  rcases t1_le_candidates y with h | h
  · exact h
  · rw [t1_star]; rw [t1_alt] at h; linarith

/-! ### The trembling-hand equilibrium and the refutation -/

/-- The strategic form of the counterexample's bargaining game.
Source: HA-4′
Kind: D -/
abbrev G : StrategicGame (Fin 2) ℝ := (bargain Γ selW).toStrategic

/-- `σ*` as a strategic profile. Source: HA-4′. Kind: D -/
def sStar' : G.Profile := toStrat Γ selW sStar

theorem ofStrat_pair (s : G.strategy 0) (t : G.strategy 1) :
    (bargain Γ selW).ofStrategicProfile (pair s t) = up s.val t.val := by
  funext i
  fin_cases i <;> rfl

theorem payoff_pair_zero (s : G.strategy 0) (t : G.strategy 1) :
    G.payoff (pair s t) 0 = (u1z (o s.val t.val) : ℝ) := by
  rw [bargain_payoff, ofStrat_pair]
  rfl

theorem payoff_pair_one (s : G.strategy 0) (t : G.strategy 1) :
    G.payoff (pair s t) 1 = (u2z (o s.val t.val) : ℝ) := by
  rw [bargain_payoff, ofStrat_pair]
  rfl

theorem sStar'_zero : (sStar' 0).val = (false, {ac}) := rfl
theorem sStar'_one : (sStar' 1).val = (true, {bd}) := rfl

theorem T0_eq (s : G.strategy 0) : T0 s = ((t0 s.val : ℚ) : ℝ) := by
  unfold T0 t0
  rw [Rat.cast_sum]
  calc ∑ t, G.payoff (pair s t) 0 = ∑ t : G.strategy 1, (u1z (o s.val t.val) : ℝ) :=
        Finset.sum_congr rfl (fun t _ => payoff_pair_zero s t)
    _ = ∑ y : Proposal Act 1, (u1z (o s.val y) : ℝ) :=
        Finset.sum_coe_sort (univ : Finset (Proposal Act 1)) (fun y => (u1z (o s.val y) : ℝ))
    _ = ∑ y : Proposal Act 1, ((u1z (o s.val y) : ℚ) : ℝ) := by simp

theorem T1_eq (t : G.strategy 1) : T1 t = ((t1 t.val : ℚ) : ℝ) := by
  unfold T1 t1
  rw [Rat.cast_sum]
  calc ∑ s, G.payoff (pair s t) 1 = ∑ s : G.strategy 0, (u2z (o s.val t.val) : ℝ) :=
        Finset.sum_congr rfl (fun s _ => payoff_pair_one s t)
    _ = ∑ x : Proposal Act 0, (u2z (o x t.val) : ℝ) :=
        Finset.sum_coe_sort (univ : Finset (Proposal Act 0)) (fun x => (u2z (o x t.val) : ℝ))
    _ = ∑ x : Proposal Act 0, ((u2z (o x t.val) : ℚ) : ℝ) := by simp

/-- **`σ*` is a trembling-hand equilibrium of `𝒢`** in exactly SC Def. 10.4's sense: (N) every
alternative ties at order `ε⁰` (all pay `0`), and (L) `σ*ᵢ` maximises the order-`ε¹` total `Tᵢ`
(`= 72`); `uniform_thpe_of_lex` supplies the ε-sequence and the perturbed equilibria.
Source: HA-4′; dp-cf-003 (the Selten step, now proved)
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem sStar_thpe : THPE (pureProfileToMixed sStar') := by
  apply uniform_thpe_of_lex
  · intro s
    right
    refine ⟨?_, ?_⟩
    · unfold M0
      rw [payoff_pair_zero, payoff_pair_zero, sStar'_one, sStar'_zero, N0, N0]
    · rw [T0_eq, T0_eq, sStar'_zero]
      exact_mod_cast t0_max s.val
  · intro t
    right
    refine ⟨?_, ?_⟩
    · unfold M1
      rw [payoff_pair_one, payoff_pair_one, sStar'_zero, sStar'_one, N1, N1]
    · rw [T1_eq, T1_eq, sStar'_one]
      exact_mod_cast t1_max t.val

/-- `σ*` is harmonious (pure form). Source: HA-4′. Kind: C -/
theorem sStar_harmonious : HarmoniousPure Γ selW sStar := sStar_thpe

/-- **SC Theorem 11.1 is false as stated.** Quoted: "In the bargaining game 𝒢 with a welfare
selection rule, any trembling-hand equilibrium outcome is not subjectively Pareto-dominated."
Reading: `THPE` (SC Def. 10.4, uniform floor, existential ε-sequence) of a pure profile of
`(bargain Γ sel).toStrategic`, outcome `outcome sel σ`, "not dominated" = FAF's `ParetoOptimalIn`.
Witness: the 2×2 game `Γ`, the injective welfare rule `(selW, W)`, and `σ* = ((a,{ac}),(d,{bd}))`,
harmonious with outcome `ad` strictly dominated by `bc` for both players (`ad_lt_bc_both`).
Surviving neighbour: `Neighbour.lean`'s `no_all_but_one_improvement` (T5).
Source: [[superconditioning-mismatched-ontologies]] §11 Thm 11.1; HA-4′; dp-cf-003
Kind: N+ (refutation)
Fidelity: exact
Hyps: (a) all -/
theorem thm111_refuted :
    ∃ (Γ : Game (Fin 2) Act) (sel : Finset Out → Out) (W : Out → ℝ),
      IsWelfareSel Γ sel W ∧ Function.Injective W ∧
      ∃ σ : ∀ i, Proposal Act i, HarmoniousPure Γ sel σ ∧
        ¬ Game.ParetoOptimalIn (Γ.u (outcome sel σ)) (Γ.u '' Set.univ) :=
  ⟨Γ, selW, W, isWelfareSel_selW, W_injective, sStar, sStar_harmonious, by
    rw [paretoOptimalIn_iff, outcome_sStar]
    exact fun h => h bc paretoDom_ad_bc⟩

/-- The dominating outcome, explicitly: `bc` dominates `outcome selW σ* = ad` with strict
inequality for **both** players.
Source: HA-4′
Kind: N+ -/
theorem thm111_dominator :
    ParetoDom Γ (outcome selW sStar) bc ∧
      Γ.u (outcome selW sStar) 0 < Γ.u bc 0 ∧ Γ.u (outcome selW sStar) 1 < Γ.u bc 1 := by
  rw [outcome_sStar]
  exact ⟨paretoDom_ad_bc, ad_lt_bc_both⟩

end

end Thm111

end Cleanroom.Udt.UdtHarmonyBargain
