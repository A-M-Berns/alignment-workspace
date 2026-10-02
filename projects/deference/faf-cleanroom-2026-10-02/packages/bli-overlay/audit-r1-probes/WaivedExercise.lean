import Cleanroom.Bli.BliOverlay.Waived

/-!
# `bli-overlay` · audit r1 (adversarial) · probe: T3(a)'s waived branch is exercised

The mandate's optional N+ for T3(a) *on its own* — which neither attempt shipped (findings
F-12): a trader whose day-`0` value **exceeds** `marketMakerError 0 = 1/2` in some p.c. world
(so the `W = ∅` instance of the hypothesis is false), and which T3(a) with `W = {0}` nevertheless
proves not to exploit. Concrete: buy one share of `⌜a₀⌝` on day `0` and nothing afterwards, on
the all-`0` history, valued by the all-true world. Not imported by the library.
-/

namespace Cleanroom.Bli.BliOverlay.AuditR1Adversarial

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Bli.BliOverlay

/-- Buy one share of `⌜a₀⌝` on day `0`; trade nothing afterwards. -/
def spikeStrat (n : ℕ) : Strategy n where
  trades := if n = 0 then [(EF.const 1, (Formula.atom 0 : Sentence))] else []
  rank_le := by
    intro p hp
    by_cases h : n = 0
    · rw [if_pos h] at hp
      simp only [List.mem_singleton] at hp
      subst hp
      simp
    · rw [if_neg h] at hp
      simp at hp

/-- The spike trader. -/
def spike : Trader := ⟨spikeStrat⟩

/-- The all-`0` history. -/
def zeroHist : History := fun _ _ => 0

lemma zeroHist_range : ∀ day φ, 0 ≤ zeroHist day φ ∧ zeroHist day φ ≤ 1 :=
  fun _ _ => ⟨le_rfl, zero_le_one⟩

/-- The all-true world. -/
def allTrue : PCWorld := fun _ => True

lemma allTrue_payout_atom : allTrue.payout (Formula.atom 0) = 1 := by
  have h : allTrue.Holds (Formula.atom 0) := (PCWorld.holds_atom allTrue 0).mpr (by simp [allTrue])
  simp [PCWorld.payout, h]

/-- Day `0`: the value is `1` in the all-true world on the all-`0` history. -/
lemma spike_value_zero : (spike.strat 0).value zeroHist allTrue.payout = 1 := by
  simp [spike, spikeStrat, Strategy.value, zeroHist, allTrue_payout_atom]

/-- Days `n ≠ 0`: the value is `0`. -/
lemma spike_value_succ (n : ℕ) (hn : n ≠ 0) (w : Sentence → ℝ) :
    (spike.strat n).value zeroHist w = 0 := by
  simp [spike, spikeStrat, Strategy.value, hn]

/-- The `W = ∅` hypothesis of T3(a) is **false** for `spike` on `zeroHist`: day `0` is a
waived day in substance. -/
example : ¬ (∀ n ∉ (∅ : Finset ℕ), ∀ v : PCWorld,
    (spike.strat n).value zeroHist v.payout ≤ (marketMakerError n : ℝ)) := by
  intro h
  have h0 := h 0 (by simp) allTrue
  rw [spike_value_zero] at h0
  unfold marketMakerError at h0
  norm_num at h0

/-- T3(a) with `W = {0}` proves `spike` does not exploit `zeroHist`, relative to any process. -/
example (DP : DeductiveProcess) : ¬ spike.Exploits zeroHist DP := by
  apply not_exploits_of_dayValue_le_off_finite spike zeroHist DP zeroHist_range {0}
  intro n hn v
  have hn0 : n ≠ 0 := by simpa using hn
  rw [spike_value_succ n hn0]
  exact_mod_cast (marketMakerError_pos n).le

end Cleanroom.Bli.BliOverlay.AuditR1Adversarial
