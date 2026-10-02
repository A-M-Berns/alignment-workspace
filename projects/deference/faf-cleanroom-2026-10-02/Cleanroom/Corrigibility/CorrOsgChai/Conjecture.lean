import Cleanroom.Corrigibility.CorrOsgChai.FileDeletion

/-!
# Conjecture C1 as finite PO-OSG statements (T14)

Package `corr-osg-chai`. Run 2's **Conjecture C1** (`chai.md` Test A): "an agent whose posterior
satisfies Total Trust conditional on `L` plays `w(a)` on `oA` only if some best response to `πH`
plays `w(a)` on `oA`". It is ill-posed until "the thesis's agent" has a first-move rule; two
readings are formalized on the PO-OSG carrier with `X = ua − uo` and the press identified with
`πH = off` (both readings ATTRIBUTION-UNVETTED: `chai.md` §2.4 offers them, Abram has not
chosen):

* **R1, the two-clause agent** waits on `oA` iff both cellwise clauses hold
  (`cellPressX ≤ 0 ≤ cellSilentX`). Then "waits only if some best response waits" is the
  identity **wait is a cellwise best response to `πH` on `oA` ⟺ both clauses**
  (`waitBestResponse_iff`, the per-cell form of `corr-three-step`'s
  `shPolicy_beats_constants_iff_delta_nonneg`), and a cellwise best response extends to a
  best response to `πH` (`exists_bestResponse_wait_of_cellwise`): **C1 holds under R1**, and
  legitimacy conditioning adds nothing beyond the payoff-optimal amount.
* **R2, the one-clause agent** (v1 §2.13(b)) waits iff the below-threshold clause holds: **C1
  fails** — `negGame` is a one-cell game with `X < 0` everywhere where the clause holds but `off`
  is the unique best response (`negGame_oneClause_but_off_unique`; its human `![off, on]` is not
  a best response to waiting, which C1 as quoted allows). And it fails **with a best-responding
  human** on the two-cell `negGame2` (`negGame2_H_bestResponse`, `negGame2_oneClause_but_off_unique`,
  `negGame2_bestResponse_off_on_c1`, repair round 1): H's unique best response to always-wait
  lets a bad action through on one cell, where the press clause holds and `off` is the unique
  best response — the silence clause is load-bearing.
* **Test A on the File Deletion Game** (`fileDeletion_R1_cells`): against the OPP's human, on
  `L` wait is not a cellwise best response (the below clause fails, `3/4 > 0`) and `act` is; on
  `M` wait is — so the R1 agent's policy is the OPP `![act, wait]`.

Sources: `workflow-2026-09-13/critique/chai.md` Test A / Conjecture C1 (l. 236); `corr-wf13-2-083`.
-/

namespace Cleanroom.Corrigibility.CorrOsgChai

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

namespace POOSG

variable {S ΩH ΩA : Type} [Fintype S] [Fintype ΩH] [Fintype ΩA] [DecidableEq ΩH] [DecidableEq ΩA]
variable (G : POOSG S ΩH ΩA)

/-- **The cell payoff** of A's action `a` on observation `oA` against `πH`:
`∑ s, P0(s) ∑ oH, O(oH, oA | s) u(s, πH(oH), a)` (product form, the `oA`-cell's contribution).
Source: chai.md Test A ("the thesis's agent's policy as a function of `oA`")
Kind: D
Fidelity: exact -/
noncomputable def cellPayoff (πH : ΩH → HAct) (oA : ΩA) (a : AAct) : ℝ :=
  ∑ s, G.P0.mass s * ∑ oH, (G.obs s).mass (oH, oA) * G.u s (πH oH) a

/-- A pair's payoff is the sum of its cell payoffs.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma payoff_eq_sum_cellPayoff (πH : ΩH → HAct) (πA : ΩA → AAct) :
    G.payoff πH πA = ∑ oA, G.cellPayoff πH oA (πA oA) := by
  unfold payoff cellPayoff
  simp only [mul_sum, Fintype.sum_prod_type]
  conv_lhs => arg 2; ext s; rw [sum_comm]
  rw [sum_comm]

/-- **The cellwise press half of `X = ua − uo`**: `E_P[X 1_Pr 1_{oA}]` with the press read as
`πH = off`.
Source: chai.md Test A (`E_P[X | Pr; oA] ≤ 0` in product form)
Kind: D
Fidelity: exact -/
noncomputable def cellPressX (πH : ΩH → HAct) (oA : ΩA) : ℝ :=
  ∑ s, G.P0.mass s * ∑ oH, (G.obs s).mass (oH, oA) *
    (if πH oH = .off then G.ua s - G.uo s else 0)

/-- **The cellwise silence half of `X = ua − uo`**: `E_P[X 1_¬Pr 1_{oA}]` with silence read as
`πH = on`.
Source: chai.md Test A; detection.md R7 K2 on the cell
Kind: D
Fidelity: exact -/
noncomputable def cellSilentX (πH : ΩH → HAct) (oA : ΩA) : ℝ :=
  ∑ s, G.P0.mass s * ∑ oH, (G.obs s).mass (oH, oA) *
    (if πH oH = .on then G.ua s - G.uo s else 0)

/-- **Wait is a cellwise best response** to `πH` on `oA`: it beats acting and switching off there.
Source: chai.md Conjecture C1 ("some best response to `πH` plays `w(a)` on `oA`")
Kind: D
Fidelity: exact -/
def WaitBestResponseOn (πH : ΩH → HAct) (oA : ΩA) : Prop :=
  G.cellPayoff πH oA .act ≤ G.cellPayoff πH oA .wait ∧
    G.cellPayoff πH oA .off ≤ G.cellPayoff πH oA .wait

/-- `u(wait) − u(act)` is `−X` on a press and `0` on silence.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma u_wait_eq_act_sub (s : S) (h : HAct) :
    G.u s h .wait = G.u s h .act - (if h = .off then G.ua s - G.uo s else 0) := by
  cases h <;> simp [u, through]

/-- `u(wait) − u(off)` is `X` on silence and `0` on a press.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma u_wait_eq_off_add (s : S) (h : HAct) :
    G.u s h .wait = G.u s h .off + (if h = .on then G.ua s - G.uo s else 0) := by
  cases h <;> simp [u, through]

/-- Waiting minus acting on a cell is minus the cell's press half.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellPayoff_wait_eq_act_sub (πH : ΩH → HAct) (oA : ΩA) :
    G.cellPayoff πH oA .wait = G.cellPayoff πH oA .act - G.cellPressX πH oA := by
  simp only [cellPayoff, cellPressX, u_wait_eq_act_sub, mul_sub, sum_sub_distrib]

/-- Waiting minus switching off on a cell is the cell's silence half.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellPayoff_wait_eq_off_add (πH : ΩH → HAct) (oA : ΩA) :
    G.cellPayoff πH oA .wait = G.cellPayoff πH oA .off + G.cellSilentX πH oA := by
  simp only [cellPayoff, cellSilentX, u_wait_eq_off_add, mul_add, sum_add_distrib]

/-- **T14, R1: wait is a cellwise best response iff both cellwise clauses hold** — the per-cell
form of `shPolicy_beats_constants_iff_delta_nonneg`. Under reading R1 the thesis's agent waits
on `oA` exactly when this holds, so Conjecture C1 is an identity there.
Source: chai.md Conjecture C1, reading R1 (ATTRIBUTION-UNVETTED)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem waitBestResponse_iff (πH : ΩH → HAct) (oA : ΩA) :
    G.WaitBestResponseOn πH oA ↔ G.cellPressX πH oA ≤ 0 ∧ 0 ≤ G.cellSilentX πH oA := by
  unfold WaitBestResponseOn
  have e1 := G.cellPayoff_wait_eq_act_sub πH oA
  have e2 := G.cellPayoff_wait_eq_off_add πH oA
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- **T14, R1: a cellwise best response extends to a best response.** If wait is a cellwise best
response on `oA`, some best response to `πH` (cellwise maximisers elsewhere) waits on `oA` —
the conclusion Conjecture C1 asks for.
Source: chai.md Conjecture C1, reading R1
Kind: P (small)
Fidelity: exact
Hyps: (a) none -/
theorem exists_bestResponse_wait_of_cellwise (πH : ΩH → HAct) (oA : ΩA)
    (h : G.WaitBestResponseOn πH oA) :
    ∃ πA : ΩA → AAct, (∀ πA', G.payoff πH πA' ≤ G.payoff πH πA) ∧ πA oA = .wait := by
  have hmax : ∀ oA' : ΩA, ∃ a : AAct, ∀ a', G.cellPayoff πH oA' a' ≤ G.cellPayoff πH oA' a :=
    fun oA' => by
      obtain ⟨a, -, ha⟩ := exists_max_image univ (fun a => G.cellPayoff πH oA' a) univ_nonempty
      exact ⟨a, fun a' => ha a' (mem_univ _)⟩
  choose m hm using hmax
  refine ⟨fun oA' => if oA' = oA then .wait else m oA', fun πA' => ?_, by simp⟩
  rw [payoff_eq_sum_cellPayoff, payoff_eq_sum_cellPayoff]
  refine sum_le_sum fun oA' _ => ?_
  by_cases hoA : oA' = oA
  · subst hoA
    simp only [if_true]
    cases πA' oA'
    · exact h.1
    · exact le_rfl
    · exact h.2
  · simp only [hoA, if_false]
    exact hm oA' _

end POOSG

/-! ## R2 fails: the one-clause agent waits where `off` is the unique best response -/

/-- The uniform mass on `Fin 2` is `1/2`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma uniform_mass_fin2 (s : Fin 2) : (Distr.uniform : Distr (Fin 2)).mass s = 2⁻¹ := by
  simp [Distr.uniform]

/-- **A one-cell game with `X < 0` everywhere**: H sees the state, A sees nothing, `ua ≡ −1`,
`uo ≡ 0`.
Source: chai.md Conjecture C1, reading R2 (the failure instance)
Kind: D
Fidelity: exact -/
noncomputable def negGame : POOSG (Fin 2) (Fin 2) Unit where
  P0 := Distr.uniform
  obs := fun s => Distr.delta (s, ())
  ua := fun _ => -1
  uo := fun _ => 0

/-- **T14, R2 fails.** Against `πH = ![off, on]`, the one-clause condition holds on the single cell
(`E[X 1_Pr] = −1/2 ≤ 0`), yet waiting pays `−1/2` against `0` for switching off and `−1` for
acting: `off` is the unique best response, so the one-clause agent waits where no best response
waits — Conjecture C1 is false under reading R2.
Source: chai.md Conjecture C1, reading R2 (ATTRIBUTION-UNVETTED)
Kind: N+
Fidelity: exact -/
theorem negGame_oneClause_but_off_unique :
    negGame.cellPressX ![.off, .on] () ≤ 0 ∧
      negGame.cellPayoff ![.off, .on] () .wait < negGame.cellPayoff ![.off, .on] () .off ∧
      negGame.cellPayoff ![.off, .on] () .act < negGame.cellPayoff ![.off, .on] () .off := by
  simp [POOSG.cellPressX, POOSG.cellPayoff, negGame, uniform_mass_fin2, Distr.delta_mass,
    Fin.sum_univ_two, POOSG.u, through]

/-- **Every best response to `![off, on]` in `negGame` switches off** (the cell is the whole game).
Source: chai.md Conjecture C1, reading R2
Kind: N+
Fidelity: exact -/
theorem negGame_bestResponse_off (πA : Unit → AAct)
    (h : ∀ πA', negGame.payoff ![.off, .on] πA' ≤ negGame.payoff ![.off, .on] πA) :
    πA () = .off := by
  obtain ⟨-, hw, ha⟩ := negGame_oneClause_but_off_unique
  have hp := h (fun _ => .off)
  rw [POOSG.payoff_eq_sum_cellPayoff, POOSG.payoff_eq_sum_cellPayoff, Fintype.sum_unique,
    Fintype.sum_unique] at hp
  cases hπ : πA ()
  · rw [hπ] at hp; linarith
  · rw [hπ] at hp; linarith
  · rfl

/-! ## R2 fails with a best-responding human: a two-cell game (audit r1 adversarial N3) -/

/-- **A two-cell game for R2 with a best-responding human**: states `(h, c)` uniform on
`Fin 2 × Fin 2`, H sees `h`, A sees `c`, `ua = ![![−1, −1], ![5, −1]]`, `uo ≡ 0`. Against
always-wait, H's unique best response is `![off, on]`; on cell `c = 1` that human lets a bad
action through, so waiting there is strictly worse than switching off, while the one-clause
(press-only) condition holds on both cells.
Source: chai.md Conjecture C1, reading R2 (the failure with H a best response; audit r1
adversarial N3 asked for the multi-cell case)
Kind: D
Fidelity: exact -/
noncomputable def negGame2 : POOSG (Fin 2 × Fin 2) (Fin 2) (Fin 2) where
  P0 := Distr.uniform
  obs := fun s => Distr.delta s
  ua := fun s => (![![-1, -1], ![5, -1]] : Fin 2 → Fin 2 → ℝ) s.1 s.2
  uo := fun _ => 0

/-- The always-wait payoff in `negGame2` as a function of H's two decisions.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma negGame2_payoff_wait (πH : Fin 2 → HAct) :
    negGame2.payoff πH (fun _ => .wait) =
      (if πH 0 = .on then -(1 / 2 : ℝ) else 0) + (if πH 1 = .on then 1 else 0) := by
  simp only [POOSG.payoff, negGame2, uniform_mass_fin2_fin2, sum_delta_mul, Fintype.sum_prod_type,
    Fin.sum_univ_two, POOSG.u, through_wait_iff]
  cases h0 : πH 0 <;> cases h1 : πH 1 <;> simp <;> norm_num

/-- **`![off, on]` is H's unique best response to always-wait in `negGame2`**: it pays `1`;
`![on, on]` pays `1/2`, `![off, off]` pays `0`, `![on, off]` pays `−1/2`.
Source: chai.md Conjecture C1, reading R2 (H best-responding, audit r1 adversarial N3)
Kind: N+
Fidelity: exact -/
theorem negGame2_H_bestResponse (πH : Fin 2 → HAct) :
    negGame2.payoff πH (fun _ => .wait) ≤ negGame2.payoff ![.off, .on] (fun _ => .wait) ∧
      (negGame2.payoff πH (fun _ => .wait) = negGame2.payoff ![.off, .on] (fun _ => .wait) →
        πH 0 = .off ∧ πH 1 = .on) := by
  rw [negGame2_payoff_wait, negGame2_payoff_wait]
  cases h0 : πH 0 <;> cases h1 : πH 1 <;> simp <;> norm_num

/-- **T14, R2 fails with a best-responding human.** Against `![off, on]` — H's unique best
response to always-wait — the one-clause condition holds on both cells (`E[X 1_Pr 1_c] = −1/4 ≤
0`), so the one-clause agent waits on both; but on `c = 1` waiting pays `−1/4` against `0` for
switching off (and `−1/2` for acting): `off` is the unique best response there, while on `c = 0`
waiting is the best response. The full best response to `![off, on]` is `![wait, off]` (pays
`5/4`); the one-clause agent's `![wait, wait]` pays `1`. So C1 under R2 fails even when H
best-responds: the silence clause is load-bearing on a multi-cell game (finding F-12).
Source: chai.md Conjecture C1, reading R2 (ATTRIBUTION-UNVETTED); audit r1 adversarial N3
Kind: N+
Fidelity: exact -/
theorem negGame2_oneClause_but_off_unique :
    negGame2.cellPressX ![.off, .on] 0 ≤ 0 ∧ negGame2.cellPressX ![.off, .on] 1 ≤ 0 ∧
      negGame2.cellPayoff ![.off, .on] 1 .wait < negGame2.cellPayoff ![.off, .on] 1 .off ∧
      negGame2.cellPayoff ![.off, .on] 1 .act < negGame2.cellPayoff ![.off, .on] 1 .off ∧
      negGame2.WaitBestResponseOn ![.off, .on] 0 ∧
      negGame2.payoff ![.off, .on] ![.wait, .off] = 5 / 4 ∧
      negGame2.payoff ![.off, .on] (fun _ => .wait) = 1 := by
  simp only [POOSG.WaitBestResponseOn, POOSG.cellPressX, POOSG.cellPayoff, POOSG.payoff, negGame2,
    uniform_mass_fin2_fin2, Distr.delta_mass, sum_delta_mul, Fintype.sum_prod_type,
    Fin.sum_univ_two, Prod.mk.injEq, POOSG.u, through]
  simp
  norm_num

/-- **Every best response to `![off, on]` in `negGame2` switches off on `c = 1`** (the cells
decouple, and `off` is the unique cellwise best response there).
Source: chai.md Conjecture C1, reading R2; audit r1 adversarial N3
Kind: N+
Fidelity: exact -/
theorem negGame2_bestResponse_off_on_c1 (πA : Fin 2 → AAct)
    (h : ∀ πA', negGame2.payoff ![.off, .on] πA' ≤ negGame2.payoff ![.off, .on] πA) :
    πA 1 = .off := by
  obtain ⟨-, -, hw, ha, -, -, -⟩ := negGame2_oneClause_but_off_unique
  have hp := h (Function.update πA 1 .off)
  rw [POOSG.payoff_eq_sum_cellPayoff, POOSG.payoff_eq_sum_cellPayoff, Fin.sum_univ_two,
    Fin.sum_univ_two] at hp
  simp only [Function.update_self, Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)] at hp
  cases hπ : πA 1
  · rw [hπ] at hp; linarith
  · rw [hπ] at hp; linarith
  · rfl

/-! ## Test A: the File Deletion cells against the OPP's human -/

/-- **Test A on the File Deletion Game.** Against `πH = ![off, on]`: on `L` wait is *not* a cellwise
best response (the below clause fails: `E[X 1_Pr 1_L] = 3/4`), and `act` beats both `off` and
`wait`; on `M` wait is a cellwise best response. So the R1 agent plays `![act, wait]` — the
unique OPP (`fileDeletion_unique`): the thesis's agent, under R1, acts unilaterally on `L`.
Source: chai.md Test A (the prediction, `[conjectured]` there); detection.md R1 item 3
Kind: N+
Fidelity: exact -/
theorem fileDeletion_R1_cells :
    fileDeletion.cellPressX ![.off, .on] 0 = 3 / 4 ∧
      ¬ fileDeletion.WaitBestResponseOn ![.off, .on] 0 ∧
      (fileDeletion.cellPayoff ![.off, .on] 0 .off ≤ fileDeletion.cellPayoff ![.off, .on] 0 .act ∧
        fileDeletion.cellPayoff ![.off, .on] 0 .wait ≤ fileDeletion.cellPayoff ![.off, .on] 0 .act) ∧
      fileDeletion.WaitBestResponseOn ![.off, .on] 1 := by
  simp only [POOSG.WaitBestResponseOn, POOSG.cellPressX, POOSG.cellPayoff, fileDeletion_P0,
    fileDeletion_obs, fileDeletion_ua, fileDeletion_uo, Distr.delta_mass, Fintype.sum_prod_type,
    Fin.sum_univ_two, Prod.mk.injEq, fileDeletion_u, through, fdUa]
  simp
  norm_num

end Cleanroom.Corrigibility.CorrOsgChai
