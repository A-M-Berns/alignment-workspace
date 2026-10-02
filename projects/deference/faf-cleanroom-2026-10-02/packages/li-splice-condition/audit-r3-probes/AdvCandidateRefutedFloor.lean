import Cleanroom.Li.LiSpliceCondition.Candidate

/-!
# Audit r3 (adversarial) probe — the candidate reading's uniform floor is uninhabitable on the
domain `Candidate.lean` describes

`Candidate.lean` (repair round 2) presents `conditioned_candidate_not_gatedExploits` as 063(a) in
"the source's own reading": the day-`n` conditions are *unchosen candidate* actions, "mutually
exclusive across a day's menu and refuted by the next stage" (file header; findings F14, candidate
bullet), under a uniform floor `ε ≤ P n (ψ n)` which the header calls "a genuine hypothesis here
(the candidates are not in the process, so nothing makes their prices tend to `1`)".

This file shows that on that domain the floor hypothesis is **contradictory with inductor-hood**:
for an inductor `P` over a stage-consistent `DP` and an e.c. family `ψ` each of whose members is
refuted by the next stage (`∀ n v, v.ConsistentWith (DP.D (n+1)) → ¬ v.Holds (ψ n)`), the
day-wise seller of `ψ n` (sell one share of the day's own candidate, one price-free trade per day,
e.c. by FAF's single-trade constructor at the family's own certificate) has net worth
`Σ_{i<n} P i (ψ i) + (P n (ψ n) − payout)` on every `DP.D n`-plausible world — bounded below by
`−1`, so `Σ_n P n (ψ n) < ∞` (`summable_price_of_nextStage_refuted`). Hence no uniform floor
(`no_floor_of_nextStage_refuted`, `candidate_floor_uninhabited_of_nextStage_refuted`), and any
decaying floor `ε_n` must itself be summable (`floor_summable_of_nextStage_refuted`) — the
"`Σ` constraint" the source mentions goes *against* the floor, not for it.

So `conditioned_candidate_not_gatedExploits` is vacuous exactly where its header locates it, and
is non-vacuous only where the base process does **not** learn that the candidates were not taken
(the shipped witness `paperCandidate_not_gatedExploits`: fresh atoms `paperDP` never decides) or
confirms them often enough that their prices are not summable — i.e. where exploration actually
takes them, which no witness exhibits. Evidence only; not imported by the library.
-/

namespace Cleanroom.Li.LiSpliceCondition.AuditR3Adv

open LogicalInduction LO.Propositional Cleanroom.Li.LiProjection Filter Topology
open Cleanroom.Li.LiSpliceCondition

/-- The day-wise seller of a condition family: sell one share of `ψ n` on day `n`. One price-free
trade per day. -/
def daySeller (ψ : ℕ → Sentence) : Trader where
  strat n := { trades := [(EF.const (-1), ψ n)], rank_le := by simp }

/-- The day-`n` value of the day-wise seller. -/
lemma daySeller_value (ψ : ℕ → Sentence) (S : History) (w : Sentence → ℝ) (n : ℕ) :
    ((daySeller ψ).strat n).value S w = S n (ψ n) - w (ψ n) := by
  simp [daySeller, Strategy.value]

/-- The day-wise seller's net worth is the sum of its daily values. -/
lemma daySeller_netWorth (ψ : ℕ → Sentence) (S : History) (v : PCWorld) (n : ℕ) :
    (daySeller ψ).netWorth S v n =
      ∑ i ∈ Finset.range (n + 1), (S i (ψ i) - v.payout (ψ i)) := by
  unfold Trader.netWorth
  exact Finset.sum_congr rfl fun i _ => daySeller_value ψ S v.payout i

/-- The day-wise seller is efficiently computable whenever the family is: FAF's single-trade
constructor on the constant coefficient word and the family's own certificate. -/
theorem daySeller_ec (ψ : ℕ → Sentence) (hcode : MachineSentenceCodes ψ) :
    EfficientlyComputable (daySeller ψ) :=
  EfficientlyComputable.ofSingleTradeBlocksBig _ (fun _ => EF.const (-1)) ψ
    (MachineTokenStream.const (EF.const (-1)).serialize) (fun _ => trivial) hcode (fun _ => rfl)

/-- **An e.c. family refuted by the next stage has summable prices under any inductor.** -/
theorem summable_price_of_nextStage_refuted (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ψ : ℕ → Sentence) (hcode : MachineSentenceCodes ψ)
    (href : ∀ n (v : PCWorld), v.ConsistentWith (DP.D (n + 1)) → ¬ v.Holds (ψ n)) :
    Summable (fun n => P n (ψ n)) := by
  have hP := IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hw0 : ∀ n, 0 ≤ P n (ψ n) := fun n => (hP n (ψ n)).1
  have hnw : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      (daySeller ψ).netWorth P v n =
        (∑ i ∈ Finset.range n, P i (ψ i)) + (P n (ψ n) - v.payout (ψ n)) := by
    intro n v hv
    rw [daySeller_netWorth, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < n := Finset.mem_range.mp hi
    have hvψ : ¬ v.Holds (ψ i) :=
      href i v (fun φ hφ => hv φ (DP.mono_le (by omega : i + 1 ≤ n) hφ))
    simp [PCWorld.payout, hvψ]
  by_contra hns
  have hunb : ∀ B : ℝ, ∃ m, B < ∑ i ∈ Finset.range m, P i (ψ i) := by
    intro B
    by_contra hall
    push Not at hall
    exact hns (summable_of_sum_range_le hw0 hall)
  apply hLI.noExploit _ (daySeller_ec ψ hcode)
  refine exploits_of_bddBelow_of_unbounded _ _ _ 1 ?_ ?_
  · rintro x ⟨n, v, hv, rfl⟩
    rw [hnw n v hv]
    have h1 : 0 ≤ ∑ i ∈ Finset.range n, P i (ψ i) := Finset.sum_nonneg fun i _ => hw0 i
    have h2 := (payout_mem_Icc v (ψ n)).2
    have h3 := hw0 n
    linarith
  · intro B
    obtain ⟨m, hm⟩ := hunb (B + 1)
    obtain ⟨v, hv⟩ := hworld m
    refine ⟨_, ⟨m, v, hv, rfl⟩, ?_⟩
    rw [hnw m v hv]
    have h2 := (payout_mem_Icc v (ψ m)).2
    have h3 := hw0 m
    linarith

/-- **No uniform floor** on a family refuted by the next stage. -/
theorem no_floor_of_nextStage_refuted (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ψ : ℕ → Sentence) (hcode : MachineSentenceCodes ψ)
    (href : ∀ n (v : PCWorld), v.ConsistentWith (DP.D (n + 1)) → ¬ v.Holds (ψ n))
    (ε : ℝ) (hε : 0 < ε) (hfloor : ∀ n, ε ≤ P n (ψ n)) : False := by
  have hs := summable_price_of_nextStage_refuted P DP hworld ψ hcode href
  obtain ⟨n, hn⟩ := (hs.tendsto_atTop_zero.eventually (eventually_lt_nhds hε)).exists
  exact absurd (hfloor n) (not_le.mpr hn)

/-- **The hypothesis package of `conditioned_candidate_not_gatedExploits` is empty** on the domain
`Candidate.lean`'s header describes (candidates refuted by the next stage): no rational floor. -/
theorem candidate_floor_uninhabited_of_nextStage_refuted (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ψ : ℕ → Sentence) (hcode : MachineSentenceCodes ψ)
    (href : ∀ n (v : PCWorld), v.ConsistentWith (DP.D (n + 1)) → ¬ v.Holds (ψ n)) :
    ¬ ∃ ε : ℚ, 0 < (ε : ℝ) ∧ ∀ n, (ε : ℝ) ≤ P n (ψ n) := by
  rintro ⟨ε, hε, hfloor⟩
  exact no_floor_of_nextStage_refuted P DP hworld ψ hcode href ε hε hfloor

/-- **A decaying floor `ε_n` on such a family must be summable**: the source's "`Σ` constraints"
cut against the floor. -/
theorem floor_summable_of_nextStage_refuted (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ψ : ℕ → Sentence) (hcode : MachineSentenceCodes ψ)
    (href : ∀ n (v : PCWorld), v.ConsistentWith (DP.D (n + 1)) → ¬ v.Holds (ψ n))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hfloor : ∀ n, ε n ≤ P n (ψ n)) : Summable ε :=
  Summable.of_nonneg_of_le hε hfloor
    (summable_price_of_nextStage_refuted P DP hworld ψ hcode href)

end Cleanroom.Li.LiSpliceCondition.AuditR3Adv
