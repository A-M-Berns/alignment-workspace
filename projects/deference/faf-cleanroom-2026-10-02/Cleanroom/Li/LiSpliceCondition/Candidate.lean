import Cleanroom.Li.LiSpliceCondition.DayIndexed

/-!
# `li-splice-condition` · Candidate: 063(a) in the source's own reading (repair round 2)

Package `Cleanroom.Li.LiSpliceCondition` ([[li-splice-condition-mandate]]), file 13 of the layout,
added in repair round 2 after the adversarial audit's B1. The source's use case for the day-indexed
conditions (E7 escape (ii), `clusters/E/NEGATIVES.md` l. 235: "exploration that keeps `ℙ(a) ≥ ε`";
the inventory's 063(a): "a day-indexed condition sequence `a_n` with a price floor
`ℙ_n(a_n) ≥ ε_n` … any asymptotic guarantee on `ℙ_n(· | a_n)`") is a decision sequence whose
day-`n` condition is an *unchosen candidate* action `a_n`, kept unrefuted only by exploration. Such
conditions are mutually exclusive across a day's menu and refuted by the next stage, so no monotone
`DeductiveProcess` holds them consistently: the claim is not of the form "the conditioned market is
an inductor over a process" (which is what `DayIndexed.lean`'s (G)/(L)/(S) formalize), and the
realized-action reading (L) — where the floor is automatic — is not it.

What FAF can say about it is a statement about *trades*, through the same gated translation
`Trader.conditionedTranslation` that proves `thm:scon`: a trader against the day-wise conditioned
market `conditionedHistory P ψ` is translated into a trader against `P` whose day-`n` contract is
worth exactly `0` in a world failing `ψ n` and tracks the original's day-`n` value, less the day's
conditioning budget, in a world holding it. Summing, the translated trader's net worth dominates
the original's **gated net worth** — its day-by-day value against the conditioned market counted
only on the days whose condition the world realizes — minus `1`, in *every* world
(`gatedNetWorth_sub_one_le_conditionedTranslation`). Since the translation is e.c. whenever the
original is (FAF's `conditionedTranslation_preserves_ec`, which is where the uniform floor is
needed), `noExploit` transfers: **no e.c. trader's gated assessments over `DP`'s plausible worlds
are bounded below and unbounded above** (`conditioned_candidate_not_gatedExploits`). This is the
conditional-contract guarantee the decision-sequence use needs — bets on `· | a_n` are void on
days `a_n` is not realized — stated under a uniform floor. The floor is a genuine hypothesis here
(the candidates are not in the process, so nothing makes their prices tend to `1`); a decaying
`ε_n` "with `Σ` constraints" is outside FAF's translator, which takes one rational `ε`, and is
recorded, not attempted.

No limit claim about `ℙ_n(· | a_n)` is made or implied: gated non-exploitation is the criterion's
own guarantee transported to the conditioned market along realized days, and the limit properties
the paper derives from the criterion (convergence, coherence, …) are derived from `Exploits` over
*one* market and *all* plausible worlds, which the gated set is not.
-/

namespace Cleanroom.Li.LiSpliceCondition

open LogicalInduction LO.Propositional Cleanroom.Li.LiProjection Filter Topology
open Classical

/-- **The gated net worth**: a trader's day-by-day value against the day-wise conditioned market,
summed over the days up to `n` whose condition the world `v` realizes — the conditional-contract
accounting of a decision sequence (a bet on `· | a_i` is void when `a_i` is not taken).
Source: [[corr-legit-neg-inventory]] 063(a) (E7 escape (ii), the exploration reading); FAF `Trader.netWorth`, `conditionedHistory`
Kind: D
Fidelity: variant: FAF's `netWorth` with the day's term gated by `v.Holds (ψ i)` -/
noncomputable def gatedNetWorth (T : Trader) (P : History) (ψ : ℕ → Sentence) (v : PCWorld)
    (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    if v.Holds (ψ i) then (T.strat i).value (conditionedHistory P ψ) v.payout else 0

/-- The gated plausible assessments: the gated net worths over the worlds plausible at each stage
of `DP` (FAF's `plausibleAssessments` with `gatedNetWorth` in place of `netWorth`).
Source: [[corr-legit-neg-inventory]] 063(a); FAF `Trader.plausibleAssessments`
Kind: D
Fidelity: variant: gated -/
def gatedAssessments (T : Trader) (P : History) (ψ : ℕ → Sentence) (DP : DeductiveProcess) :
    Set ℝ :=
  { x | ∃ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) ∧ x = gatedNetWorth T P ψ v n }

/-- **Gated exploitation**: the gated assessments are bounded below and not above — FAF's
`Trader.Exploits` for the conditional-contract accounting.
Source: [[corr-legit-neg-inventory]] 063(a); FAF `Trader.Exploits`
Kind: D
Fidelity: variant: gated -/
def GatedExploits (T : Trader) (P : History) (ψ : ℕ → Sentence) (DP : DeductiveProcess) : Prop :=
  BddBelow (gatedAssessments T P ψ DP) ∧ ¬ BddAbove (gatedAssessments T P ψ DP)

/-- On a world holding every condition up to the day, the gated net worth is FAF's net worth
against the conditioned market: (C)'s accounting restricts to (L)'s on the worlds (L) uses.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem gatedNetWorth_eq_netWorth_of_holds (T : Trader) (P : History) (ψ : ℕ → Sentence)
    (v : PCWorld) (n : ℕ) (hall : ∀ i, i ≤ n → v.Holds (ψ i)) :
    gatedNetWorth T P ψ v n = T.netWorth (conditionedHistory P ψ) v n := by
  unfold gatedNetWorth Trader.netWorth
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [if_pos (hall i (by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi))]

/-- **Tracking in every world**: under a uniform floor, FAF's gated translation of `T` is worth at
least `T`'s gated net worth minus `1` on every day in every world — on a day whose condition the
world holds, FAF's `locallyGatedConditionalContract_value_lower` (the day's value less the day's
budget); on a day whose condition fails, the translated contract is worth exactly `0`
(`locallyGatedConditionalContract_value_eq_zero_of_not_holds`) and the gated term is `0`; the
budgets sum to at most `1` (`sum_conditioningBudget_le_one`). No hypothesis on `v`: this is
FAF's `conditionedTranslation_netWorth_lower` with its "holds every condition up to the day"
hypothesis traded for gating.
Source: [[corr-legit-neg-inventory]] 063(a); FAF `conditionedTranslation_netWorth_lower` (`thm:scon`'s tracking lemma)
Kind: P
Fidelity: stronger: FAF's tracking lemma on every world, with the gated accounting
Hyps: (a) -/
theorem gatedNetWorth_sub_one_le_conditionedTranslation (T : Trader) (P : History)
    (ψ : ℕ → Sentence) {ε : ℚ} (hε : 0 < (ε : ℝ)) (hfloor : ∀ d, (ε : ℝ) ≤ P d (ψ d))
    (v : PCWorld) (n : ℕ) :
    gatedNetWorth T P ψ v n - 1 ≤ (T.conditionedTranslation ψ ε).netWorth P v n := by
  have hday : ∀ i ∈ Finset.range (n + 1),
      (if v.Holds (ψ i) then (T.strat i).value (conditionedHistory P ψ) v.payout else 0) -
          (conditioningBudget i : ℝ) ≤
        ((T.conditionedTranslation ψ ε).strat i).value P v.payout := by
    intro i _
    change _ ≤ ((T.strat i).separatedLocallyGatedConditionalContract ψ ε
      (conditioningBudget i)).value P v.payout
    rw [Strategy.separatedLocallyGatedConditionalContract_value ψ ε (conditioningBudget i)
      (T.strat i) P v.payout hε hfloor]
    by_cases h : v.Holds (ψ i)
    · rw [if_pos h]
      exact Strategy.locallyGatedConditionalContract_value_lower (T.strat i) P ψ hε hfloor v h
    · rw [if_neg h, Strategy.locallyGatedConditionalContract_value_eq_zero_of_not_holds
        (T.strat i) P ψ hε hfloor _ v h]
      have := conditioningBudget_pos i
      linarith
  have hsum := Finset.sum_le_sum hday
  have hbudget := sum_conditioningBudget_le_one n
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Trader.netWorth, gatedNetWorth]
  linarith

/-- **063(a) in the candidate reading — gated non-exploitation**: for an inductor `P` over `DP`,
an e.c. day-indexed condition family `ψ` with a uniform price floor `ε ≤ P n (ψ n)` (the
exploration floor of E7 escape (ii)), and every e.c. trader `T`, the gated assessments of `T`
against the day-wise conditioned market over `DP`'s plausible worlds are not both bounded below
and unbounded above. Nothing is assumed about the conditions beyond the floor: they may be
mutually exclusive across days and refuted by later stages, and no process holds them — this is
the reading the source's decision-sequence use needs, which (G)/(L)/(S) are not. Proof: if the
gated assessments were bounded below by `L` and unbounded, the translated trader
`T.conditionedTranslation ψ ε` (e.c. by FAF's `conditionedTranslation_preserves_ec`) would have
plausible assessments over `DP` bounded below by `L − 1` and unbounded
(`gatedNetWorth_sub_one_le_conditionedTranslation`), i.e. would exploit `P` — against
`noExploit`. The floor is a genuine hypothesis here (nothing makes an unchosen candidate's price
tend to `1`); the source's decaying `ε_n` "with `Σ` constraints" is outside FAF's translator
(one rational `ε`) and is recorded, not attempted. No limit claim about `P_n(· | ψ_n)` follows.
Source: [[corr-legit-neg-inventory]] 063(a) (E7 escape (ii), "exploration that keeps `ℙ(a) ≥ ε`"; "CONJECTURE that a price floor `ε_n` with `Σ` constraints suffices"); FAF `Trader.conditionedTranslation`, `conditionedTranslation_preserves_ec`
Kind: C
Fidelity: variant: uniform floor; the guarantee is gated non-exploitation over `DP`, not inductor-hood over any process (none exists for this reading)
Hyps: (a) -/
theorem conditioned_candidate_not_gatedExploits (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (ψ : ℕ → Sentence) (hcode : MachineSentenceCodes ψ)
    (ε : ℚ) (hε : 0 < (ε : ℝ)) (hfloor : ∀ n, (ε : ℝ) ≤ P n (ψ n))
    (T : Trader) (hT : EfficientlyComputable T) :
    ¬ GatedExploits T P ψ DP := by
  rintro ⟨⟨L, hL⟩, hnb⟩
  apply hLI.noExploit (T.conditionedTranslation ψ ε)
    (CondStep.conditionedTranslation_preserves_ec ψ hcode ε T hT)
  refine exploits_of_bddBelow_of_unbounded _ _ _ (max (1 - L) 0) ?_ ?_
  · rintro x ⟨n, v, hv, rfl⟩
    have h1 := gatedNetWorth_sub_one_le_conditionedTranslation T P ψ hε hfloor v n
    have h2 : L ≤ gatedNetWorth T P ψ v n := hL ⟨n, v, hv, rfl⟩
    have h3 : 1 - L ≤ max (1 - L) 0 := le_max_left _ _
    linarith
  · intro B
    obtain ⟨x, ⟨n, v, hv, rfl⟩, hBx⟩ := not_bddAbove_iff.mp hnb (B + 1)
    refine ⟨_, ⟨n, v, hv, rfl⟩, ?_⟩
    have h1 := gatedNetWorth_sub_one_le_conditionedTranslation T P ψ hε hfloor v n
    linarith

/-- The gated assessments are nonempty whenever `DP` has a plausible world: the guarantee is not
the empty-set case of `BddBelow`.
Source: none: infrastructure (non-degeneracy of `GatedExploits`)
Kind: L
Fidelity: n/a -/
theorem gatedAssessments_nonempty (T : Trader) (P : History) (ψ : ℕ → Sentence)
    (DP : DeductiveProcess) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (gatedAssessments T P ψ DP).Nonempty := by
  obtain ⟨v, hv⟩ := hworld 0
  exact ⟨_, 0, v, hv, rfl⟩

end Cleanroom.Li.LiSpliceCondition
