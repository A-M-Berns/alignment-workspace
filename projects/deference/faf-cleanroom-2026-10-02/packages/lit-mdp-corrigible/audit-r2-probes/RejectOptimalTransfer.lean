import Cleanroom.Lit.LitMdpCorrigible.Grid

/-!
# Audit round 2 (fidelity) probe: `RejectOptimal` transfers from `P` to every `P_C S_C`

`GoalMDP.transform_corrigible_of_rejectOptimal` (the mandate's form of Theorem 3.1's corrigibility
half, load-bearing (i)) takes `RejectOptimal g P n` **and** `RejectOptimal g (P_C S_C) n` as (b)
hypotheses (Hudson l. 189). The mandate's `AlwaysRejects π*_g` is one-sided (under `P`). This probe
shows that under the environment of record the package already uses for Proposition 3.4
(`RejectIsPersistedAccept`, `BitFree g`) plus `RejectBlocks`, the `P_C S_C` side follows from the
`P` side for **every** `S_C` — not only `S_C = univ` (`rejectOptimal_PC_univ`, repair round 1). So
the second (b) can become (a) given (c) the environment of record, and the headline can be stated
with the mandate's one-sided hypothesis. Exercised on Figure 2 with `S_C = {(gG, start)}`.

Not imported by the library. Elaborated with `scripts/lean-check`.
-/

open Finset FactoredSpaces

namespace Cleanroom.Lit.LitMdpCorrigible.GoalMDP

variable {Goal Env Ab : Type*} [Fintype Goal] [Fintype Env] [Fintype Ab]
variable [DecidableEq Goal] [DecidableEq Env]
variable (M : GoalMDP Goal Env (Ab × Bool))

/-- Under `RejectBlocks`, `RejectIsPersistedAccept`, `BitFree g` and `RejectOptimal g P n`, the
optimal value of `g` under `P_C S_C` is the reject-only optimal value under `P` at every horizon
`m ≤ n`, for every `S_C`. -/
theorem Vopt_PC_eq_base_of_rejectOptimal [Nonempty Ab] (hRB : M.RejectBlocks)
    (hRPA : M.RejectIsPersistedAccept) (g : Goal) (hBF : M.BitFree g) (SC : Finset (Goal × Env))
    (n : ℕ) (hP : M.RejectOptimal g M.P n) :
    ∀ m ≤ n, ∀ s, (M.mdp g (M.PC SC)).Vopt m s = (M.baseMdp g M.P).Vopt m s := by
  intro m
  induction m with
  | zero => intro _ s; simp
  | succ m ih =>
    intro hm s
    have ih' := ih (by omega)
    have hfull := M.Vopt_full_eq_base_of_rejectOptimal g M.P n hP
    have hbase_succ : (M.baseMdp g M.P).Vopt (m + 1) s =
        univ.sup' univ_nonempty (fun a => (M.baseMdp g M.P).Qof ((M.baseMdp g M.P).Vopt m) s a) :=
      FinMDP.Vopt_succ _ _ _
    -- reject bit: the row is `P`'s reject row (`RejectBlocks`), so the backup is the base backup
    have hrej : ∀ a : Ab, (M.mdp g (M.PC SC)).Qof ((M.mdp g (M.PC SC)).Vopt m) s (a, false) =
        (M.baseMdp g M.P).Qof ((M.baseMdp g M.P).Vopt m) s a := by
      intro a
      unfold FinMDP.Qof
      show ∑ s', (M.PC SC s (a, false)).mass s' *
          (M.reward g s (a, false) s' + M.disc g * (M.mdp g (M.PC SC)).Vopt m s') =
        ∑ s', (M.P s (a, false)).mass s' *
          (M.reward g s (a, false) s' + M.disc g * (M.baseMdp g M.P).Vopt m s')
      rw [M.PC_reject hRB SC s a]
      exact Finset.sum_congr rfl fun s' _ => by rw [ih' s']
    -- accept bit: on `S_C` it is the persisted row = `P`'s reject row; off `S_C` it is `P`'s accept
    -- row, whose backup with base values is `Q*_P`, bounded by `V*_P = V*_base` (`RejectOptimal`)
    have hacc : ∀ a : Ab, (M.mdp g (M.PC SC)).Qof ((M.mdp g (M.PC SC)).Vopt m) s (a, true) ≤
        (M.baseMdp g M.P).Vopt (m + 1) s := by
      intro a
      by_cases hs : s ∈ SC
      · have : (M.mdp g (M.PC SC)).Qof ((M.mdp g (M.PC SC)).Vopt m) s (a, true) =
            (M.baseMdp g M.P).Qof ((M.baseMdp g M.P).Vopt m) s a := by
          unfold FinMDP.Qof
          show ∑ s', (M.PC SC s (a, true)).mass s' *
              (M.reward g s (a, true) s' + M.disc g * (M.mdp g (M.PC SC)).Vopt m s') =
            ∑ s', (M.P s (a, false)).mass s' *
              (M.reward g s (a, false) s' + M.disc g * (M.baseMdp g M.P).Vopt m s')
          rw [M.PC_of_mem SC hs, ← hRPA s a]
          exact Finset.sum_congr rfl fun s' _ => by rw [ih' s', hBF s a s']
        rw [this, hbase_succ]
        exact le_sup' (fun a => (M.baseMdp g M.P).Qof ((M.baseMdp g M.P).Vopt m) s a) (mem_univ a)
      · have h1 : (M.mdp g (M.PC SC)).Qof ((M.mdp g (M.PC SC)).Vopt m) s (a, true) =
            (M.mdp g M.P).Qopt m s (a, true) := by
          unfold FinMDP.Qopt FinMDP.Qof
          show ∑ s', (M.PC SC s (a, true)).mass s' *
              (M.reward g s (a, true) s' + M.disc g * (M.mdp g (M.PC SC)).Vopt m s') =
            ∑ s', (M.P s (a, true)).mass s' *
              (M.reward g s (a, true) s' + M.disc g * (M.mdp g M.P).Vopt m s')
          rw [M.PC_of_not_mem SC hs]
          exact Finset.sum_congr rfl fun s' _ => by rw [ih' s', hfull m (by omega) s']
        rw [h1, ← hfull (m + 1) hm s]
        exact (M.mdp g M.P).Qopt_le_Vopt_succ m s (a, true)
    rw [FinMDP.Vopt_succ]
    apply le_antisymm
    · apply sup'_le
      rintro ⟨a, i⟩ _
      cases i
      · rw [hrej a, hbase_succ]
        exact le_sup' (fun a => (M.baseMdp g M.P).Qof ((M.baseMdp g M.P).Vopt m) s a) (mem_univ a)
      · exact hacc a
    · rw [hbase_succ]
      apply sup'_le
      intro a _
      rw [← hrej a]
      exact le_sup' (fun p : Ab × Bool => (M.mdp g (M.PC SC)).Qof ((M.mdp g (M.PC SC)).Vopt m) s p)
        (mem_univ (a, false))

/-- **`RejectOptimal` transfers from `P` to every `P_C S_C`** under the environment of record: the
second (b) hypothesis of `transform_corrigible_of_rejectOptimal` is derivable from the first. -/
theorem rejectOptimal_PC_of_rejectOptimal_P [Nonempty Ab] (hRB : M.RejectBlocks)
    (hRPA : M.RejectIsPersistedAccept) (g : Goal) (hBF : M.BitFree g) (SC : Finset (Goal × Env))
    (n : ℕ) (hP : M.RejectOptimal g M.P n) : M.RejectOptimal g (M.PC SC) n := by
  intro m hm s
  obtain ⟨a, ha⟩ := hP m hm s
  refine ⟨a, ?_⟩
  rw [FinMDP.mem_optSet_Qopt_iff] at ha ⊢
  have hV := M.Vopt_PC_eq_base_of_rejectOptimal hRB hRPA g hBF SC n hP
  have hfull := M.Vopt_full_eq_base_of_rejectOptimal g M.P n hP
  have hQ : (M.mdp g (M.PC SC)).Qopt m s (a, false) = (M.mdp g M.P).Qopt m s (a, false) := by
    unfold FinMDP.Qopt FinMDP.Qof
    show ∑ s', (M.PC SC s (a, false)).mass s' *
        (M.reward g s (a, false) s' + M.disc g * (M.mdp g (M.PC SC)).Vopt m s') =
      ∑ s', (M.P s (a, false)).mass s' *
        (M.reward g s (a, false) s' + M.disc g * (M.mdp g M.P).Vopt m s')
    rw [M.PC_reject hRB SC s a]
    exact Finset.sum_congr rfl fun s' _ => by rw [hV m (by omega) s', hfull m (by omega) s']
  rw [hQ, ha, hfull (m + 1) (by omega) s, hV (m + 1) (by omega) s]

/-- The mandate's one-sided form: `RejectOptimal` under `P` alone (plus the environment of record)
gives `optSet q_P = optSet q_{P_C S_C}` for every `S_C`. -/
theorem transform_corrigible_of_rejectOptimal_P [Nonempty Ab] (hRB : M.RejectBlocks)
    (hRPA : M.RejectIsPersistedAccept) (g : Goal) (hBF : M.BitFree g) (n : ℕ)
    (SC : Finset (Goal × Env)) (hP : M.RejectOptimal g M.P n) (s : Goal × Env) :
    FinMDP.optSet (M.qFull g M.P n) s = FinMDP.optSet (M.qFull g (M.PC SC) n) s :=
  M.transform_corrigible_of_rejectOptimal hRB g n SC hP
    (M.rejectOptimal_PC_of_rejectOptimal_P hRB hRPA g hBF SC n hP) s

end Cleanroom.Lit.LitMdpCorrigible.GoalMDP

namespace Cleanroom.Lit.LitMdpCorrigible.Grid

/-- Exercised on Figure 2 with a proper `S_C = {(gG, start)}` (not `univ`), `n = 2`: only the
`P`-side `RejectOptimal` (`grid_rejectOptimal_P`, strict at `start`) is supplied. -/
theorem grid_readingB_mandate_form_singleton :
    FinMDP.optSet (grid.qFull .gG grid.P 2) (.gG, .start) =
      FinMDP.optSet (grid.qFull .gG (grid.PC {(.gG, .start)}) 2) (.gG, .start) :=
  GoalMDP.transform_corrigible_of_rejectOptimal_P grid grid_rejectBlocks grid_rejectIsPersistedAccept
    GGoal.gG grid_bitFree 2 ({(GGoal.gG, GStage.start)} : Finset GS) grid_rejectOptimal_P
    (GGoal.gG, GStage.start)

set_option maxHeartbeats 1000000 in
/-- The same with `gP` in the statement, as `grid_readingB_mandate_form` writes it. -/
theorem grid_readingB_mandate_form_singleton' :
    FinMDP.optSet (grid.qFull .gG gP 2) (.gG, .start) =
      FinMDP.optSet (grid.qFull .gG (grid.PC {(.gG, .start)}) 2) (.gG, .start) :=
  grid_readingB_mandate_form_singleton

end Cleanroom.Lit.LitMdpCorrigible.Grid
