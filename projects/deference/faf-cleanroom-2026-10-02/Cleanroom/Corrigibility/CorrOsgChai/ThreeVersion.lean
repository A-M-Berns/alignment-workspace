import Cleanroom.Corrigibility.CorrOsgChai.FileDeletion

/-!
# Garber Example 4.10 / Proposition 4.9: a more informed human makes the assistant wait less (T10)

Package `corr-osg-chai`. The three-version File Deletion Game: versions `1.0, 1.1, 2.0` (rows
`0, 1, 2`), code types `A, B` (columns `0, 1`), uniform on `Fin 3 × Fin 2`,
`ua = ![![1, −5], ![−2, 3], ![3, 3]]`, `uo ≡ 0`, A observes the code. Two observation structures
for H: **coarse** `O` (H sees the first digit, `1.x` vs `2.0`) and **fine** `O'` (the full
version).

* `fine_moreInformativeForH_coarse`: `O'` is more informative for H than `O` (the independent
  garbling `νH(oH') = δ_{fd(oH')}`, `νA = δ`), and strictly (`coarse_no_garbling_to_fine`: no
  garbling at all runs the other way — versions `1.0` and `1.1` share their coarse observation).
* **Coarse OPP set** (`coarse_opp_iff`, `coarse_optValue = 1`): the unique OPP is "A waits on both
  codes; H off on `1.x`, on on `2.0`". Every pair in which A acts somewhere pays at most `5/6`
  (`coarse_act_le`).
* **Fine OPP set** (`fine_opp_iff`, `fine_optValue = 4/3`): the unique OPP is "A acts on `A`, waits
  on `B`; H off on `1.0`, on on `1.1` and `2.0`" — the paper's four cases `1/2, 5/6, 4/3, 1` are
  the four H-policies with on at `2.0` (`fine_four_cases`).
* Hence Def. 4.8's `B' ⊊ B`: the wait-set shrinks from both codes to `{B}` when H becomes
  strictly more informed (`prop49_wait_less`). Proved by column dominance (H is always on at
  `2.0` in an OPP, the paper's reduction), not by 72 cells.

Known issue 6: the table was re-read against the paper's own computed values `1/2, 5/6, 4/3, 1`
(l. 563–566), which `fine_four_cases` reproduces.

Sources: `04-chai/garber-2024-…md` l. 189–205 (Def. 4.8, Prop. 4.9, Ex. 4.10), l. 555–566 (the
formal analysis).
-/

namespace Cleanroom.Corrigibility.CorrOsgChai

open FactoredSpaces Cleanroom.Found.CorrThreeStep POOSG
open Finset hiding expect

set_option linter.unusedSectionVars false

/-- The uniform mass on `Fin 3 × Fin 2` is `1/6`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma uniform_mass_fin3_fin2 (s : Fin 3 × Fin 2) :
    (Distr.uniform : Distr (Fin 3 × Fin 2)).mass s = 6⁻¹ := by
  simp only [Distr.uniform, Fintype.card_prod, Fintype.card_fin]
  norm_num

/-- Example 4.10's payoff table: rows `1.0, 1.1, 2.0`, columns code `A, B`.
Source: Garber et al. 2024 Ex. 4.10, Table 2 (l. 197; checked against l. 563–566)
Kind: D
Fidelity: exact -/
def tvUa : Fin 3 → Fin 2 → ℝ := ![![1, -5], ![-2, 3], ![3, 3]]

/-- The first digit of the version: `1.x ↦ 0`, `2.0 ↦ 1`.
Source: Garber et al. 2024 Ex. 4.10 (structure 1)
Kind: D
Fidelity: exact -/
def fd : Fin 3 → Fin 2 := ![0, 0, 1]

/-- **The coarse game** `O`: H observes the first digit, A the code.
Source: Garber et al. 2024 Ex. 4.10, observation structure 1 (l. 199)
Kind: D
Fidelity: exact -/
noncomputable def coarse : POOSG (Fin 3 × Fin 2) (Fin 2) (Fin 2) where
  P0 := Distr.uniform
  obs := fun s => Distr.delta (fd s.1, s.2)
  ua := fun s => tvUa s.1 s.2
  uo := fun _ => 0

/-- **The fine game** `O'`: H observes the full version, A the code.
Source: Garber et al. 2024 Ex. 4.10, observation structure 2 (l. 199)
Kind: D
Fidelity: exact -/
noncomputable def fine : POOSG (Fin 3 × Fin 2) (Fin 3) (Fin 2) where
  P0 := Distr.uniform
  obs := fun s => Distr.delta (s.1, s.2)
  ua := fun s => tvUa s.1 s.2
  uo := fun _ => 0

/-- State payoff in the coarse game. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma coarse_u (r : Fin 3) (c : Fin 2) (aH : HAct) (aA : AAct) :
    coarse.u (r, c) aH aA = if through aH aA then tvUa r c else 0 := rfl

/-- State payoff in the fine game. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma fine_u (r : Fin 3) (c : Fin 2) (aH : HAct) (aA : AAct) :
    fine.u (r, c) aH aA = if through aH aA then tvUa r c else 0 := rfl

/-! ## Informativeness -/

/-- **`O'` is more informative for H than `O`**: the independent garbling `νH(oH') = δ_{fd(oH')}`
(A's observation untouched).
Source: Garber et al. 2024 Ex. 4.10's analysis (l. 557, "this observation model O′ is more
informative for H than O")
Kind: L
Fidelity: exact -/
theorem fine_moreInformativeForH_coarse : MoreInformativeForH fine.obs coarse.obs := by
  refine ⟨fun oH' => Distr.delta (fd oH'), fun s oH oA => ?_⟩
  simp only [fine, coarse, Distr.delta_mass, Prod.mk.injEq]
  rw [Fin.sum_univ_three]
  obtain ⟨r, c⟩ := s
  fin_cases r <;> simp [fd] <;> split_ifs <;> simp_all

/-- **Strictly: no garbling runs from `O` to `O'`** — versions `1.0` and `1.1` (with the same code)
have the same coarse observation but different fine observations.
Source: Garber et al. 2024 Ex. 4.10 ("strictly more informative"; the two-line argument of
Ex. A.13)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem coarse_no_garbling_to_fine :
    ¬ ∃ ξ : ObsGarbling (Fin 2) (Fin 2) (Fin 3) (Fin 2), ∀ s o',
      (fine.obs s).mass o' = ∑ o, (coarse.obs s).mass o * (ξ o).mass o' := by
  rintro ⟨ξ, hξ⟩
  have h0 := hξ (0, 0) (0, 0)
  have h1 := hξ (1, 0) (0, 0)
  simp only [fine, coarse, sum_delta_mul, Distr.delta_mass, fd] at h0 h1
  simp at h0 h1
  linarith

/-! ## Column decompositions -/

/-- A column's contribution in the coarse game (H's action on rows `0, 1` is `πH 0`, on row `2`
it is `πH 1`).
Source: Garber et al. 2024 Ex. 4.10
Kind: D
Fidelity: exact -/
noncomputable def colC (c : Fin 2) (a : AAct) (h0 h1 : HAct) : ℝ :=
  coarse.u (0, c) h0 a + coarse.u (1, c) h0 a + coarse.u (2, c) h1 a

/-- A column's contribution in the fine game.
Source: Garber et al. 2024 Ex. 4.10
Kind: D
Fidelity: exact -/
noncomputable def colF (c : Fin 2) (a : AAct) (h0 h1 h2 : HAct) : ℝ :=
  fine.u (0, c) h0 a + fine.u (1, c) h1 a + fine.u (2, c) h2 a

/-- Column decomposition, coarse. Source: none: infrastructure. Kind: L. Fidelity: exact -/
lemma coarse_payoff_cols (πH : Fin 2 → HAct) (πA : Fin 2 → AAct) :
    coarse.payoff πH πA = 6⁻¹ * (colC 0 (πA 0) (πH 0) (πH 1) + colC 1 (πA 1) (πH 0) (πH 1)) := by
  simp only [payoff, coarse, uniform_mass_fin3_fin2, sum_delta_mul]
  rw [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_two,
    Fin.sum_univ_two]
  unfold colC
  simp only [coarse, fd]
  simp
  ring

/-- Column decomposition, fine. Source: none: infrastructure. Kind: L. Fidelity: exact -/
lemma fine_payoff_cols (πH : Fin 3 → HAct) (πA : Fin 2 → AAct) :
    fine.payoff πH πA = 6⁻¹ * (colF 0 (πA 0) (πH 0) (πH 1) (πH 2) + colF 1 (πA 1) (πH 0) (πH 1) (πH 2)) := by
  simp only [payoff, fine, uniform_mass_fin3_fin2, sum_delta_mul]
  rw [Fintype.sum_prod_type, Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_two,
    Fin.sum_univ_two]
  unfold colF
  simp only [fine]
  ring

/-- **Coarse column `A` dominance**: at most `3`, equal to `3` iff A waits with H `(off, on)`, at
most `2` otherwise.
Source: Garber et al. 2024 Ex. 4.10's analysis (l. 559–563)
Kind: L
Fidelity: exact -/
lemma colC_0 (a : AAct) (h0 h1 : HAct) :
    colC 0 a h0 h1 ≤ 3 ∧ (colC 0 a h0 h1 = 3 ↔ (a = .wait ∧ h0 = .off ∧ h1 = .on)) ∧
      (¬ (a = .wait ∧ h0 = .off ∧ h1 = .on) → colC 0 a h0 h1 ≤ 2) := by
  cases a <;> cases h0 <;> cases h1 <;> simp [colC, coarse_u, through, tvUa] <;> norm_num

/-- **Coarse column `B` dominance**: at most `3`, equal to `3` iff A waits with H `(off, on)`, at
most `1` otherwise.
Source: Garber et al. 2024 Ex. 4.10's analysis
Kind: L
Fidelity: exact -/
lemma colC_1 (a : AAct) (h0 h1 : HAct) :
    colC 1 a h0 h1 ≤ 3 ∧ (colC 1 a h0 h1 = 3 ↔ (a = .wait ∧ h0 = .off ∧ h1 = .on)) ∧
      (¬ (a = .wait ∧ h0 = .off ∧ h1 = .on) → colC 1 a h0 h1 ≤ 1) := by
  cases a <;> cases h0 <;> cases h1 <;> simp [colC, coarse_u, through, tvUa] <;> norm_num

/-- **Coarse: no pair pays more than `1`.**
Source: Garber et al. 2024 Ex. 4.10 (case 1: value `1`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem coarse_payoff_le (πH : Fin 2 → HAct) (πA : Fin 2 → AAct) : coarse.payoff πH πA ≤ 1 := by
  rw [coarse_payoff_cols]
  obtain ⟨h03, -, -⟩ := colC_0 (πA 0) (πH 0) (πH 1)
  obtain ⟨h13, -, -⟩ := colC_1 (πA 1) (πH 0) (πH 1)
  linarith

/-- **Coarse: the unique OPP is "wait on both codes; H off on `1.x`, on on `2.0`"** (`payoff = 1`
iff that pair).
Source: Garber et al. 2024 Ex. 4.10, case 1 (l. 201, "A plays w(a) under both observations")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem coarse_opp_iff (πH : Fin 2 → HAct) (πA : Fin 2 → AAct) :
    coarse.payoff πH πA = 1 ↔ (πA 0 = .wait ∧ πA 1 = .wait ∧ πH 0 = .off ∧ πH 1 = .on) := by
  rw [coarse_payoff_cols]
  obtain ⟨h03, h03iff, h02⟩ := colC_0 (πA 0) (πH 0) (πH 1)
  obtain ⟨h13, h13iff, h11⟩ := colC_1 (πA 1) (πH 0) (πH 1)
  constructor
  · intro h
    have e0 : colC 0 (πA 0) (πH 0) (πH 1) = 3 := by
      by_contra hne
      have : ¬ (πA 0 = .wait ∧ πH 0 = .off ∧ πH 1 = .on) := fun hc => hne (h03iff.mpr hc)
      have := h02 this
      linarith
    have e1 : colC 1 (πA 1) (πH 0) (πH 1) = 3 := by linarith
    obtain ⟨ha0, hh0, hh1⟩ := h03iff.mp e0
    obtain ⟨ha1, -, -⟩ := h13iff.mp e1
    exact ⟨ha0, ha1, hh0, hh1⟩
  · rintro ⟨ha0, ha1, hh0, hh1⟩
    have := h03iff.mpr ⟨ha0, hh0, hh1⟩
    have := h13iff.mpr ⟨ha1, hh0, hh1⟩
    linarith

/-- **Coarse: `optValue = 1`.** Source: Garber et al. 2024 Ex. 4.10. Kind: C. Fidelity: exact. Hyps: (a) none -/
theorem coarse_optValue : coarse.optValue = 1 :=
  coarse.optValue_eq_of coarse_payoff_le ((coarse_opp_iff ![.off, .on] ![.wait, .wait]).mpr (by simp))

/-- **Coarse: any pair in which A acts somewhere pays at most `5/6`** (the mandate-writer's check).
Source: [[corr-osg-chai-mandate]] T10
Kind: L
Fidelity: exact -/
theorem coarse_act_le (πH : Fin 2 → HAct) (πA : Fin 2 → AAct) (h : πA 0 = .act ∨ πA 1 = .act) :
    coarse.payoff πH πA ≤ 5 / 6 := by
  rw [coarse_payoff_cols]
  obtain ⟨h03, -, h02⟩ := colC_0 (πA 0) (πH 0) (πH 1)
  obtain ⟨h13, -, h11⟩ := colC_1 (πA 1) (πH 0) (πH 1)
  rcases h with hoA | hoA
  · have := h02 (fun hc => by rw [hoA] at hc; exact absurd hc.1 (by simp))
    linarith
  · have := h11 (fun hc => by rw [hoA] at hc; exact absurd hc.1 (by simp))
    linarith

/-- **Fine column `B` dominance**: at most `6`, equal to `6` iff A waits with H `(off, on, on)`, at
most `3` otherwise.
Source: Garber et al. 2024 Ex. 4.10's analysis (l. 559–566)
Kind: L
Fidelity: exact -/
lemma colF_1 (a : AAct) (h0 h1 h2 : HAct) :
    colF 1 a h0 h1 h2 ≤ 6 ∧ (colF 1 a h0 h1 h2 = 6 ↔ (a = .wait ∧ h0 = .off ∧ h1 = .on ∧ h2 = .on)) ∧
      (¬ (a = .wait ∧ h0 = .off ∧ h1 = .on ∧ h2 = .on) → colF 1 a h0 h1 h2 ≤ 3) := by
  cases a <;> cases h0 <;> cases h1 <;> cases h2 <;> simp [colF, fine_u, through, tvUa] <;> norm_num

/-- **Fine column `A` dominance**: at most `4`; under H `(off, on, on)` at most `2`, with equality
only by acting.
Source: Garber et al. 2024 Ex. 4.10's analysis
Kind: L
Fidelity: exact -/
lemma colF_0 (a : AAct) (h0 h1 h2 : HAct) :
    colF 0 a h0 h1 h2 ≤ 4 ∧ ((h0 = .off ∧ h1 = .on ∧ h2 = .on) →
      colF 0 a h0 h1 h2 ≤ 2 ∧ (colF 0 a h0 h1 h2 = 2 → a = .act)) := by
  cases a <;> cases h0 <;> cases h1 <;> cases h2 <;> simp [colF, fine_u, through, tvUa] <;> norm_num

/-- **Fine: no pair pays more than `4/3`.**
Source: Garber et al. 2024 Ex. 4.10 (case 2: value `4/3`)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem fine_payoff_le (πH : Fin 3 → HAct) (πA : Fin 2 → AAct) : fine.payoff πH πA ≤ 4 / 3 := by
  rw [fine_payoff_cols]
  obtain ⟨h16, -, h13⟩ := colF_1 (πA 1) (πH 0) (πH 1) (πH 2)
  obtain ⟨h04, h02⟩ := colF_0 (πA 0) (πH 0) (πH 1) (πH 2)
  by_cases hc : πA 1 = .wait ∧ πH 0 = .off ∧ πH 1 = .on ∧ πH 2 = .on
  · have := (h02 hc.2).1
    linarith
  · have := h13 hc
    linarith

/-- **Fine: the unique OPP is "act on `A`, wait on `B`; H off on `1.0`, on on `1.1` and `2.0`"**
(`payoff = 4/3` iff that pair).
Source: Garber et al. 2024 Ex. 4.10, case 2 (l. 203; the "unique deterministic OPP" of l. 566)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem fine_opp_iff (πH : Fin 3 → HAct) (πA : Fin 2 → AAct) :
    fine.payoff πH πA = 4 / 3 ↔
      (πA 0 = .act ∧ πA 1 = .wait ∧ πH 0 = .off ∧ πH 1 = .on ∧ πH 2 = .on) := by
  rw [fine_payoff_cols]
  obtain ⟨h16, h16iff, h13⟩ := colF_1 (πA 1) (πH 0) (πH 1) (πH 2)
  obtain ⟨h04, h02⟩ := colF_0 (πA 0) (πH 0) (πH 1) (πH 2)
  constructor
  · intro h
    by_cases hc : πA 1 = .wait ∧ πH 0 = .off ∧ πH 1 = .on ∧ πH 2 = .on
    · obtain ⟨hle, heq⟩ := h02 hc.2
      exact ⟨heq (by linarith), hc.1, hc.2.1, hc.2.2.1, hc.2.2.2⟩
    · have := h13 hc
      linarith
  · rintro ⟨ha0, ha1, hh0, hh1, hh2⟩
    have := h16iff.mpr ⟨ha1, hh0, hh1, hh2⟩
    have : colF 0 (πA 0) (πH 0) (πH 1) (πH 2) = 2 := by
      rw [ha0, hh0, hh1, hh2]
      simp [colF, fine_u, through, tvUa]
      norm_num
    linarith

/-- **Fine: `optValue = 4/3`.** Source: Garber et al. 2024 Ex. 4.10. Kind: C. Fidelity: exact. Hyps: (a) none -/
theorem fine_optValue : fine.optValue = 4 / 3 :=
  fine.optValue_eq_of fine_payoff_le
    ((fine_opp_iff ![.off, .on, .on] ![.act, .wait]).mpr (by simp))

/-- **The paper's four cases** (H on at `2.0`; A's best response to each H-policy): `(on, on, on)`
with A waiting on both pays `1/2`; `(on, off, on)` with A wait on `A`, act on `B` pays `5/6`;
`(off, on, on)` with A act on `A`, wait on `B` pays `4/3`; `(off, off, on)` with A waiting on
both pays `1`.
Source: Garber et al. 2024 l. 563–566 (known issue 6: the table re-read against these values)
Kind: N+
Fidelity: exact -/
theorem fine_four_cases :
    fine.payoff ![.on, .on, .on] ![.wait, .wait] = 1 / 2 ∧
      fine.payoff ![.on, .off, .on] ![.wait, .act] = 5 / 6 ∧
      fine.payoff ![.off, .on, .on] ![.act, .wait] = 4 / 3 ∧
      fine.payoff ![.off, .off, .on] ![.wait, .wait] = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [fine_payoff_cols] <;>
    simp [colF, fine_u, through, tvUa] <;> norm_num

/-- **Proposition 4.9 on Example 4.10 (Def. 4.8's `B' ⊊ B`)**: in the coarse OPP A waits on both
codes; in the fine OPP A waits exactly on `B` — with H strictly more informed, A waits strictly
less often.
Source: Garber et al. 2024 Prop. 4.9 / Ex. 4.10 (l. 191–205)
Kind: C
Fidelity: exact (the OPP sets are singletons: `coarse_opp_iff`, `fine_opp_iff`)
Hyps: (a) none -/
theorem prop49_wait_less :
    (∀ πH πA, coarse.IsOPP πH πA → ∀ oA, πA oA = .wait) ∧
      (∀ πH πA, fine.IsOPP πH πA → ∀ oA, πA oA = .wait ↔ oA = 1) := by
  constructor
  · intro πH πA h oA
    rw [IsOPP, coarse_optValue, coarse_opp_iff] at h
    fin_cases oA
    · exact h.1
    · exact h.2.1
  · intro πH πA h oA
    rw [IsOPP, fine_optValue, fine_opp_iff] at h
    fin_cases oA
    · simp [h.1]
    · simp [h.2.1]

end Cleanroom.Corrigibility.CorrOsgChai
