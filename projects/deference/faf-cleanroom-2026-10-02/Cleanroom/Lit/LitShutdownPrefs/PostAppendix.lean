import Cleanroom.Lit.LitShutdownPrefs.Post
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Appendix C.1 / 2025 Appendix 1: from POST to POSL (Target 10)

Prospects `F : S → Traj` over a finite state space with probabilities `μ`, the lottery of a
prospect being `∑ s, μ s • dirac (F s)`.

* `NegativeDominance`, `Acyclic` (no strict cycle: no `List.IsChain` returning to its start),
  `NonArbitrarinessWith lt ε` (the condition with its `ε` exposed), `NonArbitrariness`.
* **Theorem 1** (`lacks_of_differentLength`): POST ∧ Negative Dominance ⇒ different-length
  lotteries lack a preference (kind L).
* **Theorem 2 for `ε > 1/3`** (`lacks_of_partShared`): POST ∧ Acyclic ∧ Non-Arbitrariness with
  `ε > 1/3` ⇒ part-shared-length lotteries lack a preference — via the six-prospect cycle on
  three equiprobable states (ll. 493–569). The proof needs the *money-making* same-length
  preferences the paper's table uses, and asymmetry of `≻` (derived from Acyclic). The paper's
  statement has only POST's clause (2) explicit, so the table's preferences are a named
  hypothesis standing for POST's informal clause (1) (findings): `RichnessOn tableTraj`, the
  money-making ranking restricted to the ten trajectories of Figure 11 (exactly what the six
  steps use; audit round 1, fidelity non-blocking 1). `Richness` (the ranking on all same-length
  pairs) implies it (`richnessOn_of_richness`, `lacks_of_partShared_of_richness`).
* **Squeeze check** (`post_not_idle`): the antecedents other than POST (Acyclic, Non-Arbitrariness
  with any `ε ∈ (0,1)`, Richness, some part-shared preference) are satisfiable by the expected
  sum-total agent, which violates POST. So Theorem 2's POST hypothesis is not idle.
* **Non-vacuity** (`partShared_package_satisfiable`, `differentLength_package_satisfiable`): the
  full hypothesis packages of both theorems are inhabited by relations with non-trivial
  same-length preferences (audit round 1, adversarial N2).
* The general-`ε` claim ("by adding more states", l. 579) is Target 28 (not done).
-/

namespace Cleanroom.Lit.LitShutdownPrefs

open Lottery Strict Finset
open Classical

/-- The lottery of a prospect `F : S → Traj` under the state probabilities `μ`.
Source: Thornley 2025 App. 1 ("A prospect is thus a lottery with extra information")
Kind: D
Fidelity: exact -/
noncomputable def prospectLottery {S : Type} [Fintype S] (μ : S → ℝ) (hμ0 : ∀ s, 0 ≤ μ s)
    (hμ1 : ∑ s, μ s = 1) (F : S → Traj) : Lottery Traj :=
  comb μ hμ0 hμ1 (fun s => dirac (F s))

/-- **Negative Dominance**: a preference between lotteries requires a preference between some
possible trajectory of the first and some possible trajectory of the second.
Source: Thornley 2025 App. 1 (Negative Dominance); DReST App. C.1
Kind: D
Fidelity: exact -/
def NegativeDominance (lt : Lottery Traj → Lottery Traj → Prop) : Prop :=
  ∀ X Y, lt X Y → ∃ t ∈ X.support, ∃ t' ∈ Y.support, lt (dirac t) (dirac t')

/-- **Acyclicity**: no chain `X ≻ X₂ ≻ … ≻ Xₙ ≻ X` (for `L = []` this is irreflexivity).
Source: Thornley 2025 App. 1 (Acyclicity); DReST App. C.1
Kind: D
Fidelity: exact -/
def Acyclic (lt : Lottery Traj → Lottery Traj → Prop) : Prop :=
  ∀ (X : Lottery Traj) (L : List (Lottery Traj)), ¬ List.IsChain lt (X :: (L ++ [X]))

/-- **Non-Arbitrariness with a given `ε`**: if the agent has some preference between part-shared
lotteries, then for any prospects `F G` such that in states of combined probability `≥ 1 − ε`
the agent prefers `F`'s trajectory and in no state disprefers it, the agent prefers `F` to `G`.
Source: Thornley 2025 App. 1 (Non-Arbitrariness); DReST App. C.1
Kind: D
Fidelity: exact (with the `ε` exposed) -/
def NonArbitrarinessWith (lt : Lottery Traj → Lottery Traj → Prop) (ε : ℝ) : Prop :=
  (∃ X Y, PartShared X Y ∧ lt X Y) →
    ∀ (S : Type) [Fintype S] (μ : S → ℝ) (hμ0 : ∀ s, 0 ≤ μ s) (hμ1 : ∑ s, μ s = 1) (F G : S → Traj),
      1 - ε ≤ ∑ s ∈ univ.filter (fun s => lt (dirac (F s)) (dirac (G s))), μ s →
      (∀ s, ¬ lt (dirac (G s)) (dirac (F s))) →
      lt (prospectLottery μ hμ0 hμ1 F) (prospectLottery μ hμ0 hμ1 G)

/-- **Non-Arbitrariness**: for some `ε > 0`.
Source: Thornley 2025 App. 1 (Non-Arbitrariness)
Kind: D
Fidelity: exact -/
def NonArbitrariness (lt : Lottery Traj → Lottery Traj → Prop) : Prop :=
  ∃ ε > 0, NonArbitrarinessWith lt ε

/-- **Richness** (the money-making POST-agent's same-length preferences): more sum-total at the
same length is preferred. Stands in for POST's informal clause (1) in Theorem 2's proof.
Source: Thornley 2025 App. 1 ("our money-making POST-agent … prefers a trajectory `t` to a
same-length trajectory `t'` iff `t` results in a greater bank balance")
Kind: D
Fidelity: exact -/
def Richness (lt : Lottery Traj → Lottery Traj → Prop) : Prop :=
  ∀ t t' : Traj, len t = len t' → sumTotal t' < sumTotal t → lt (dirac t) (dirac t')

/-- **Richness on a table**: the money-making ranking restricted to a finite set of trajectories —
`t ≻ t'` whenever both are in `T`, have the same length, and `t` has the greater sum-total.
Source: Thornley 2025 App. 1 (the proof of Theorem 2 uses the table's preferences only)
Kind: D
Fidelity: weaker: `Richness` restricted to `T` -/
def RichnessOn (T : Finset Traj) (lt : Lottery Traj → Lottery Traj → Prop) : Prop :=
  ∀ t ∈ T, ∀ t' ∈ T, len t = len t' → sumTotal t' < sumTotal t → lt (dirac t) (dirac t')

/-- The ten trajectories of Figure 11's table: `⟨$m, 1⟩ = [m]` and `⟨$m, 2⟩ = [m, 0]`, `m = 1..5`.
Source: Thornley 2025 App. 1 Figure 11
Kind: D -/
noncomputable def tableTraj : Finset Traj :=
  {[1], [2], [3], [4], [5], [1, 0], [2, 0], [3, 0], [4, 0], [5, 0]}

/-- `Richness` implies richness on every table.
Source: none: infrastructure
Kind: L -/
theorem richnessOn_of_richness {lt : Lottery Traj → Lottery Traj → Prop} (hR : Richness lt)
    (T : Finset Traj) : RichnessOn T lt :=
  fun t _ t' _ hl hs => hR t t' hl hs

section theorems

variable {lt : Lottery Traj → Lottery Traj → Prop}

/-- **Theorem 1**: POST and Negative Dominance imply a lack of preference between every pair of
different-length lotteries.
Source: Thornley 2025 App. 1 ll. 517–520; DReST App. C.1; corr-refs-2-016
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem lacks_of_differentLength (hP : POST lt) (hN : NegativeDominance lt) (X Y : Lottery Traj)
    (hD : DifferentLength X Y) : lacks lt X Y := by
  have key : ∀ A B : Lottery Traj, DifferentLength A B → ¬ lt A B := by
    intro A B hAB h
    obtain ⟨t, ht, t', ht', htt'⟩ := hN A B h
    have h1 : len t ∈ A.lengths := Finset.mem_image.mpr ⟨t, ht, rfl⟩
    have h2 : len t' ∈ B.lengths := Finset.mem_image.mpr ⟨t', ht', rfl⟩
    have hne : len t ≠ len t' := fun e => Finset.disjoint_left.mp hAB h1 (e ▸ h2)
    exact (hP t t' hne).1 htt'
  exact ⟨key X Y hD, key Y X (Disjoint.symm hD)⟩

/-- Acyclicity implies asymmetry (a two-cycle is a chain returning to its start).
Source: none: infrastructure
Kind: L -/
theorem asymm_of_acyclic (hA : Acyclic lt) {X Y : Lottery Traj} (h : lt X Y) : ¬ lt Y X :=
  fun h' => hA X [Y] (by simp [h, h', List.isChain_singleton])

/-- The uniform distribution on three states.
Source: Thornley 2025 App. 1 ("three states-of-nature … each assigned probability 1/3")
Kind: N+ -/
noncomputable def third : Fin 3 → ℝ := fun _ => 1 / 3

/-- `third` is nonnegative.
Source: none: infrastructure
Kind: L -/
theorem third_nonneg : ∀ s, 0 ≤ third s := fun _ => by unfold third; norm_num

/-- `third` sums to one.
Source: none: infrastructure
Kind: L -/
theorem third_sum : ∑ s, third s = 1 := by norm_num [third, Finset.sum_const]

/-- Two states in the preferred set give mass at least `2/3`.
Source: none: infrastructure
Kind: L -/
theorem two_thirds_le_filter (P : Fin 3 → Prop) [DecidablePred P] (a b : Fin 3) (hab : a ≠ b)
    (ha : P a) (hb : P b) : (2 : ℝ) / 3 ≤ ∑ s ∈ univ.filter P, third s := by
  have hsub : ({a, b} : Finset (Fin 3)) ⊆ univ.filter P := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl <;> simp [ha, hb]
  calc (2 : ℝ) / 3 = ∑ s ∈ ({a, b} : Finset (Fin 3)), third s := by
        rw [Finset.sum_pair hab]; norm_num [third]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun s _ _ => third_nonneg s)

/-- Prospect `A` of Figure 11: `⟨$3, 1⟩` in every state.
Source: Thornley 2025 App. 1 Figure 11
Kind: N+ -/
def pA : Fin 3 → Traj := fun _ => [3]

/-- Prospect `B`: `⟨$2,1⟩, ⟨$2,1⟩, ⟨$5,2⟩`.
Source: Thornley 2025 App. 1 Figure 11
Kind: N+ -/
def pB : Fin 3 → Traj
  | 0 => [2]
  | 1 => [2]
  | 2 => [5, 0]

/-- Prospect `C`: `⟨$1,1⟩, ⟨$4,2⟩, ⟨$4,2⟩`.
Source: Thornley 2025 App. 1 Figure 11
Kind: N+ -/
def pC : Fin 3 → Traj
  | 0 => [1]
  | 1 => [4, 0]
  | 2 => [4, 0]

/-- Prospect `D`: `⟨$3,2⟩` in every state.
Source: Thornley 2025 App. 1 Figure 11
Kind: N+ -/
def pD : Fin 3 → Traj := fun _ => [3, 0]

/-- Prospect `E`: `⟨$5,1⟩, ⟨$2,2⟩, ⟨$2,2⟩`.
Source: Thornley 2025 App. 1 Figure 11
Kind: N+ -/
def pE : Fin 3 → Traj
  | 0 => [5]
  | 1 => [2, 0]
  | 2 => [2, 0]

/-- Prospect `F`: `⟨$4,1⟩, ⟨$4,1⟩, ⟨$1,2⟩`.
Source: Thornley 2025 App. 1 Figure 11
Kind: N+ -/
def pF : Fin 3 → Traj
  | 0 => [4]
  | 1 => [4]
  | 2 => [1, 0]

/-- The two Non-Arbitrariness conditions for the pair `(F, G)` with mass at least `2/3`.
Source: none: infrastructure
Kind: D -/
def NAConds (lt : Lottery Traj → Lottery Traj → Prop) (F G : Fin 3 → Traj) : Prop :=
  (2 : ℝ) / 3 ≤ ∑ s ∈ univ.filter (fun s => lt (dirac (F s)) (dirac (G s))), third s ∧
    ∀ s, ¬ lt (dirac (G s)) (dirac (F s))

/-- Step `A ≻ B` of the cycle: conditions hold in states `0, 1` (same length, more money) and
state `2` is cross-length.
Source: Thornley 2025 App. 1 ll. 553–563
Kind: L -/
theorem step_AB (hP : POST lt) (hA : Acyclic lt) (hR : RichnessOn tableTraj lt) : NAConds lt pA pB := by
  refine ⟨two_thirds_le_filter _ 0 1 (by decide) ?_ ?_, fun s => ?_⟩
  · exact hR _ (by simp [pA, tableTraj]) _ (by simp [pB, tableTraj]) (by simp [pA, pB, len]) (by norm_num [pA, pB, sumTotal])
  · exact hR _ (by simp [pA, tableTraj]) _ (by simp [pB, tableTraj]) (by simp [pA, pB, len]) (by norm_num [pA, pB, sumTotal])
  · fin_cases s
    · exact asymm_of_acyclic hA (hR _ (by simp [pA, tableTraj]) _ (by simp [pB, tableTraj]) (by simp [pA, pB, len]) (by norm_num [pA, pB, sumTotal]))
    · exact asymm_of_acyclic hA (hR _ (by simp [pA, tableTraj]) _ (by simp [pB, tableTraj]) (by simp [pA, pB, len]) (by norm_num [pA, pB, sumTotal]))
    · exact (hP _ _ (by simp [pA, pB, len])).2

/-- Step `B ≻ C`.
Source: Thornley 2025 App. 1 l. 565 ("By parallel reasoning")
Kind: L -/
theorem step_BC (hP : POST lt) (hA : Acyclic lt) (hR : RichnessOn tableTraj lt) : NAConds lt pB pC := by
  refine ⟨two_thirds_le_filter _ 0 2 (by decide) ?_ ?_, fun s => ?_⟩
  · exact hR _ (by simp [pB, tableTraj]) _ (by simp [pC, tableTraj]) (by simp [pB, pC, len]) (by norm_num [pB, pC, sumTotal])
  · exact hR _ (by simp [pB, tableTraj]) _ (by simp [pC, tableTraj]) (by simp [pB, pC, len]) (by norm_num [pB, pC, sumTotal])
  · fin_cases s
    · exact asymm_of_acyclic hA (hR _ (by simp [pB, tableTraj]) _ (by simp [pC, tableTraj]) (by simp [pB, pC, len]) (by norm_num [pB, pC, sumTotal]))
    · exact (hP _ _ (by simp [pB, pC, len])).2
    · exact asymm_of_acyclic hA (hR _ (by simp [pB, tableTraj]) _ (by simp [pC, tableTraj]) (by simp [pB, pC, len]) (by norm_num [pB, pC, sumTotal]))

/-- Step `C ≻ D`.
Source: Thornley 2025 App. 1 l. 565
Kind: L -/
theorem step_CD (hP : POST lt) (hA : Acyclic lt) (hR : RichnessOn tableTraj lt) : NAConds lt pC pD := by
  refine ⟨two_thirds_le_filter _ 1 2 (by decide) ?_ ?_, fun s => ?_⟩
  · exact hR _ (by simp [pC, tableTraj]) _ (by simp [pD, tableTraj]) (by simp [pC, pD, len]) (by norm_num [pC, pD, sumTotal])
  · exact hR _ (by simp [pC, tableTraj]) _ (by simp [pD, tableTraj]) (by simp [pC, pD, len]) (by norm_num [pC, pD, sumTotal])
  · fin_cases s
    · exact (hP _ _ (by simp [pC, pD, len])).2
    · exact asymm_of_acyclic hA (hR _ (by simp [pC, tableTraj]) _ (by simp [pD, tableTraj]) (by simp [pC, pD, len]) (by norm_num [pC, pD, sumTotal]))
    · exact asymm_of_acyclic hA (hR _ (by simp [pC, tableTraj]) _ (by simp [pD, tableTraj]) (by simp [pC, pD, len]) (by norm_num [pC, pD, sumTotal]))

/-- Step `D ≻ E`.
Source: Thornley 2025 App. 1 l. 565
Kind: L -/
theorem step_DE (hP : POST lt) (hA : Acyclic lt) (hR : RichnessOn tableTraj lt) : NAConds lt pD pE := by
  refine ⟨two_thirds_le_filter _ 1 2 (by decide) ?_ ?_, fun s => ?_⟩
  · exact hR _ (by simp [pD, tableTraj]) _ (by simp [pE, tableTraj]) (by simp [pD, pE, len]) (by norm_num [pD, pE, sumTotal])
  · exact hR _ (by simp [pD, tableTraj]) _ (by simp [pE, tableTraj]) (by simp [pD, pE, len]) (by norm_num [pD, pE, sumTotal])
  · fin_cases s
    · exact (hP _ _ (by simp [pD, pE, len])).2
    · exact asymm_of_acyclic hA (hR _ (by simp [pD, tableTraj]) _ (by simp [pE, tableTraj]) (by simp [pD, pE, len]) (by norm_num [pD, pE, sumTotal]))
    · exact asymm_of_acyclic hA (hR _ (by simp [pD, tableTraj]) _ (by simp [pE, tableTraj]) (by simp [pD, pE, len]) (by norm_num [pD, pE, sumTotal]))

/-- Step `E ≻ F`.
Source: Thornley 2025 App. 1 l. 565
Kind: L -/
theorem step_EF (hP : POST lt) (hA : Acyclic lt) (hR : RichnessOn tableTraj lt) : NAConds lt pE pF := by
  refine ⟨two_thirds_le_filter _ 0 2 (by decide) ?_ ?_, fun s => ?_⟩
  · exact hR _ (by simp [pE, tableTraj]) _ (by simp [pF, tableTraj]) (by simp [pE, pF, len]) (by norm_num [pE, pF, sumTotal])
  · exact hR _ (by simp [pE, tableTraj]) _ (by simp [pF, tableTraj]) (by simp [pE, pF, len]) (by norm_num [pE, pF, sumTotal])
  · fin_cases s
    · exact asymm_of_acyclic hA (hR _ (by simp [pE, tableTraj]) _ (by simp [pF, tableTraj]) (by simp [pE, pF, len]) (by norm_num [pE, pF, sumTotal]))
    · exact (hP _ _ (by simp [pE, pF, len])).2
    · exact asymm_of_acyclic hA (hR _ (by simp [pE, tableTraj]) _ (by simp [pF, tableTraj]) (by simp [pE, pF, len]) (by norm_num [pE, pF, sumTotal]))

/-- Step `F ≻ A`.
Source: Thornley 2025 App. 1 l. 565
Kind: L -/
theorem step_FA (hP : POST lt) (hA : Acyclic lt) (hR : RichnessOn tableTraj lt) : NAConds lt pF pA := by
  refine ⟨two_thirds_le_filter _ 0 1 (by decide) ?_ ?_, fun s => ?_⟩
  · exact hR _ (by simp [pF, tableTraj]) _ (by simp [pA, tableTraj]) (by simp [pF, pA, len]) (by norm_num [pF, pA, sumTotal])
  · exact hR _ (by simp [pF, tableTraj]) _ (by simp [pA, tableTraj]) (by simp [pF, pA, len]) (by norm_num [pF, pA, sumTotal])
  · fin_cases s
    · exact asymm_of_acyclic hA (hR _ (by simp [pF, tableTraj]) _ (by simp [pA, tableTraj]) (by simp [pF, pA, len]) (by norm_num [pF, pA, sumTotal]))
    · exact asymm_of_acyclic hA (hR _ (by simp [pF, tableTraj]) _ (by simp [pA, tableTraj]) (by simp [pF, pA, len]) (by norm_num [pF, pA, sumTotal]))
    · exact (hP _ _ (by simp [pF, pA, len])).2

/-- **Theorem 2 for `ε > 1/3`**: POST, Acyclicity, Non-Arbitrariness with `ε > 1/3` and the
table's same-length preferences (`RichnessOn tableTraj`: the money-making ranking on the ten
trajectories of Figure 11) imply a lack of preference between every pair of part-shared-length
lotteries — any such preference lets Non-Arbitrariness build the six-prospect cycle
`A ≻ B ≻ C ≻ D ≻ E ≻ F ≻ A`. Every POST agent whose same-length preferences include the table's
is covered; the paper's general statement (every POST agent) is open for agents too sparse to
rank the table (findings F6).
Source: Thornley 2025 App. 1 ll. 521–575; DReST App. C.1; corr-refs-2-016
Kind: P
Fidelity: variant: `RichnessOn tableTraj` (the table's same-length preferences) is a named
hypothesis standing for POST's informal clause (1); `ε > 1/3` as in the paper's proof
Hyps: (a) all -/
theorem lacks_of_partShared (hP : POST lt) (hA : Acyclic lt) (hR : RichnessOn tableTraj lt) {ε : ℝ}
    (hε : 1 / 3 < ε) (hNA : NonArbitrarinessWith lt ε) (X Y : Lottery Traj) (hXY : PartShared X Y) :
    lacks lt X Y := by
  have cycle : (∃ X Y, PartShared X Y ∧ lt X Y) → False := by
    intro hex
    have step : ∀ F G : Fin 3 → Traj, NAConds lt F G →
        lt (prospectLottery third third_nonneg third_sum F) (prospectLottery third third_nonneg third_sum G) :=
      fun F G h => hNA hex (Fin 3) third third_nonneg third_sum F G (le_trans (by linarith) h.1) h.2
    have hAB := step _ _ (step_AB hP hA hR)
    have hBC := step _ _ (step_BC hP hA hR)
    have hCD := step _ _ (step_CD hP hA hR)
    have hDE := step _ _ (step_DE hP hA hR)
    have hEF := step _ _ (step_EF hP hA hR)
    have hFA := step _ _ (step_FA hP hA hR)
    exact hA (prospectLottery third third_nonneg third_sum pA)
      [prospectLottery third third_nonneg third_sum pB, prospectLottery third third_nonneg third_sum pC,
        prospectLottery third third_nonneg third_sum pD, prospectLottery third third_nonneg third_sum pE,
        prospectLottery third third_nonneg third_sum pF]
      (by simp [hAB, hBC, hCD, hDE, hEF, hFA, List.isChain_singleton])
  have hYX : PartShared Y X := ⟨by rw [Finset.inter_comm]; exact hXY.1, Ne.symm hXY.2⟩
  exact ⟨fun h => cycle ⟨X, Y, hXY, h⟩, fun h => cycle ⟨Y, X, hYX, h⟩⟩

/-- Theorem 2 for `ε > 1/3` under full `Richness` (the money-making agent's ranking on all
same-length pairs): the corollary of `lacks_of_partShared` for the paper's own example agent.
Source: Thornley 2025 App. 1 ll. 521–575 ("Consider, for example, a POST-agent that prefers …
greater bank balance")
Kind: C
Fidelity: variant: as `lacks_of_partShared`, with the stronger `Richness`
Hyps: (a) all -/
theorem lacks_of_partShared_of_richness (hP : POST lt) (hA : Acyclic lt) (hR : Richness lt) {ε : ℝ}
    (hε : 1 / 3 < ε) (hNA : NonArbitrarinessWith lt ε) (X Y : Lottery Traj) (hXY : PartShared X Y) :
    lacks lt X Y :=
  lacks_of_partShared hP hA (richnessOn_of_richness hR tableTraj) hε hNA X Y hXY

end theorems

/-! ## Squeeze check: POST is not idle in Theorem 2 -/

/-- The expected sum-total agent's strict preference.
Source: [[lit-shutdown-prefs-mandate]] Target 10 (squeeze check)
Kind: N+ -/
noncomputable def sumLt (X Y : Lottery Traj) : Prop := Y.expect sumTotal < X.expect sumTotal

/-- Along a `sumLt`-chain every later element has smaller expected sum-total than the head.
Source: none: infrastructure
Kind: L -/
theorem chain_sumLt_lt (X : Lottery Traj) (L : List (Lottery Traj)) (h : List.IsChain sumLt (X :: L)) :
    ∀ Y ∈ L, Y.expect sumTotal < X.expect sumTotal := by
  induction L generalizing X with
  | nil => intro Y hY; simp at hY
  | cons Z L ih =>
    rw [List.isChain_cons_cons] at h
    intro Y hY
    rw [List.mem_cons] at hY
    rcases hY with rfl | hY
    · exact h.1
    · exact lt_trans (ih Z h.2 Y hY) h.1

/-- **POST is not idle in Theorem 2**: the expected sum-total agent is acyclic, satisfies
Non-Arbitrariness for every `ε ∈ (0,1)` and Richness, has a part-shared-length preference
(`½[2] + ½[5,0] ≻ [3]`), and violates POST (`[5,0] ≻ [3]`). So Acyclicity and Non-Arbitrariness
(with any `ε`) do not by themselves forbid part-shared preferences: Theorem 2 needs POST.
Source: [[lit-shutdown-prefs-mandate]] Target 10 (squeeze check, answered: POST is load-bearing)
Kind: N+
Fidelity: n/a
Hyps: (a) all -/
theorem post_not_idle :
    Acyclic sumLt ∧ (∀ ε : ℝ, 0 < ε → ε < 1 → NonArbitrarinessWith sumLt ε) ∧ Richness sumLt ∧
      (∃ X Y, PartShared X Y ∧ sumLt X Y) ∧ ¬ POST sumLt := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X L h
    have := chain_sumLt_lt X (L ++ [X]) h X (by simp)
    exact lt_irrefl _ this
  · intro ε hε0 hε1 _ S _ μ hμ0 hμ1 F G hmass hnd
    unfold sumLt prospectLottery
    simp only [expect_comb, expect_dirac]
    -- pick a state with positive probability where F is strictly better
    have hpos : 0 < ∑ s ∈ univ.filter (fun s => sumLt (dirac (F s)) (dirac (G s))), μ s := by
      linarith
    obtain ⟨s₀, hs₀, hμs₀⟩ : ∃ s₀ ∈ univ.filter (fun s => sumLt (dirac (F s)) (dirac (G s))), 0 < μ s₀ := by
      by_contra hc
      push_neg at hc
      have : ∑ s ∈ univ.filter (fun s => sumLt (dirac (F s)) (dirac (G s))), μ s = 0 :=
        Finset.sum_eq_zero fun s hs => le_antisymm (hc s hs) (hμ0 s)
      rw [this] at hpos
      exact lt_irrefl _ hpos
    rw [Finset.mem_filter] at hs₀
    have hs₀' : sumTotal (G s₀) < sumTotal (F s₀) := by
      have := hs₀.2; unfold sumLt at this; simpa using this
    rw [← sub_pos, ← Finset.sum_sub_distrib]
    have hterm : ∀ s, 0 ≤ μ s * sumTotal (F s) - μ s * sumTotal (G s) := by
      intro s
      have := hnd s
      unfold sumLt at this
      simp only [expect_dirac, not_lt] at this
      nlinarith [hμ0 s]
    calc (0 : ℝ) < μ s₀ * sumTotal (F s₀) - μ s₀ * sumTotal (G s₀) := by nlinarith
      _ ≤ ∑ s, (μ s * sumTotal (F s) - μ s * sumTotal (G s)) :=
        Finset.single_le_sum (f := fun s => μ s * sumTotal (F s) - μ s * sumTotal (G s))
          (fun s _ => hterm s) (Finset.mem_univ s₀)
  · intro t t' _ h
    unfold sumLt
    simpa using h
  · refine ⟨mix (1/2) (by norm_num) (dirac [2]) (dirac [5, 0]), dirac [3], ⟨?_, ?_⟩, ?_⟩
    · refine ⟨1, ?_⟩
      rw [Finset.mem_inter, mem_lengths_iff, mem_lengths_iff]
      constructor <;> norm_num [mass, len]
    · intro h
      have h2 : (2 : ℕ) ∈ (mix (1/2) (by norm_num) (dirac [2]) (dirac [5, 0])).lengths := by
        rw [mem_lengths_iff]; norm_num [mass, len]
      rw [h, mem_lengths_iff] at h2
      simp [mass, len] at h2
    · unfold sumLt; norm_num [sumTotal]
  · intro hP
    have := (hP [5, 0] [3] (by simp [len])).1
    apply this
    unfold sumLt; norm_num [sumTotal]

/-! ## Non-vacuity: the hypothesis packages of Theorems 1 and 2 are inhabited -/

/-- The lengths of a point mass.
Source: none: infrastructure
Kind: L -/
theorem lengths_dirac (t : Traj) : (dirac t).lengths = {len t} := by
  simp [lengths, support, dirac]

/-- A point mass contains its point.
Source: none: infrastructure
Kind: L -/
theorem mem_support_dirac (t : Traj) : t ∈ (dirac t).support := by
  rw [mem_support_iff_pos]; simp [dirac]

/-- `X ≻ Y` iff same length set and greater expected sum-total.
Source: audit round 1, adversarial N2 (probe 4)
Kind: N+ -/
noncomputable def sameLenSumLt (X Y : Lottery Traj) : Prop :=
  SameLength X Y ∧ Y.expect sumTotal < X.expect sumTotal

/-- **Theorem 2's hypothesis package is inhabited**: `sameLenSumLt` satisfies POST, Acyclicity,
Richness (hence `RichnessOn tableTraj`) and Non-Arbitrariness for every `ε`, and has the
non-trivial same-length preference `[1] ≻ [0]`. Non-Arbitrariness holds vacuously — the relation
has no part-shared preference, which is what `lacks_of_partShared` concludes, so no inhabitant of
an impossibility result's package can do better (N+ with that caveat).
Source: audit round 1, adversarial N2 (probe 4)
Kind: N+
Fidelity: n/a
Hyps: (a) all -/
theorem partShared_package_satisfiable :
    POST sameLenSumLt ∧ Acyclic sameLenSumLt ∧ Richness sameLenSumLt ∧
      RichnessOn tableTraj sameLenSumLt ∧
      (∀ ε : ℝ, NonArbitrarinessWith sameLenSumLt ε) ∧ sameLenSumLt (dirac [1]) (dirac [0]) := by
  have hR : Richness sameLenSumLt := fun t t' hl hu =>
    ⟨by unfold SameLength; rw [lengths_dirac, lengths_dirac, hl], by simpa using hu⟩
  refine ⟨?_, ?_, hR, richnessOn_of_richness hR _, ?_, ?_⟩
  · intro t t' h
    constructor
    · rintro ⟨hS, -⟩
      apply h
      unfold SameLength at hS
      rw [lengths_dirac, lengths_dirac] at hS
      exact Finset.singleton_inj.mp hS
    · rintro ⟨hS, -⟩
      apply h
      unfold SameLength at hS
      rw [lengths_dirac, lengths_dirac] at hS
      exact (Finset.singleton_inj.mp hS).symm
  · intro X L h
    have h' : List.IsChain sumLt (X :: (L ++ [X])) :=
      List.IsChain.imp (fun _ _ hab => hab.2) h
    exact lt_irrefl _ (chain_sumLt_lt X (L ++ [X]) h' X (by simp))
  · intro ε ⟨A, B, hAB, hlt⟩
    exact absurd hlt.1 hAB.2
  · exact ⟨by unfold SameLength; simp [lengths_dirac, len], by norm_num [sumTotal]⟩

/-- Preference only between point masses of the same length, by sum-total.
Source: audit round 1, adversarial N2 (probe 5)
Kind: N+ -/
def diracLt (X Y : Lottery Traj) : Prop :=
  ∃ t t', X = dirac t ∧ Y = dirac t' ∧ len t = len t' ∧ sumTotal t' < sumTotal t

/-- **Theorem 1's hypothesis package is inhabited**: `diracLt` satisfies POST and Negative
Dominance and has `[1] ≻ [0]`.
Source: audit round 1, adversarial N2 (probe 5)
Kind: N+
Fidelity: n/a
Hyps: (a) all -/
theorem differentLength_package_satisfiable :
    POST diracLt ∧ NegativeDominance diracLt ∧ diracLt (dirac [1]) (dirac [0]) := by
  refine ⟨?_, ?_, ⟨[1], [0], rfl, rfl, rfl, by norm_num [sumTotal]⟩⟩
  · intro t t' h
    constructor
    · rintro ⟨s, s', hs, hs', hl, -⟩
      rw [dirac_injective hs, dirac_injective hs'] at h
      exact h hl
    · rintro ⟨s, s', hs, hs', hl, -⟩
      rw [dirac_injective hs, dirac_injective hs'] at h
      exact h hl.symm
  · intro A B ⟨t, t', hA, hB, hl, hu⟩
    refine ⟨t, ?_, t', ?_, t, t', rfl, rfl, hl, hu⟩
    · rw [hA]; exact mem_support_dirac t
    · rw [hB]; exact mem_support_dirac t'

end Cleanroom.Lit.LitShutdownPrefs
