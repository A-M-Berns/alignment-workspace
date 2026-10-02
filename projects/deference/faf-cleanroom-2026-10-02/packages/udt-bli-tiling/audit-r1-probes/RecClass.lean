import Cleanroom.Bli.UdtBliTiling.Refreeze

/-!
# Audit r1 (adversarial) probe · RecClass: the re-freezing on the coin-FALSE class reverses the
preference

`refreeze_dilemma` (ii) conditions the prior on the coin-**true** class (`coinClass`): there the
re-frozen prior strictly prefers `refrozen t` to `payAll` by `c · ∑_{k≥t} γ_k`. The package never
states the other branch. This probe does: under `conditionOn` at the coin-**false** class
(`recClass`, the `Rec_k` tables), the ex-ante value is `V · ∑_k γ_k [π Ask_k] + r₀ false`, so the
re-frozen prior there strictly prefers `payAll` to `refrozen t` by `V · ∑_{k≥t} γ_k` — the same
direction as the frozen prior. So "the re-frozen prior strictly prefers its own policy" is a
statement about the coin-true branch only (which is the branch where the decision has a stake;
the `Rec_k` tables carry none), and the two-sided dilemma is two-sided *at the `Ask` tables*.
Not imported by the library.
-/

namespace Cleanroom.Bli.UdtBliTiling.AuditR1

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist Finset
open Cleanroom.Bli.UdtBliSist.Iter SingleCoin

variable {K : ℕ} (p : Params K)

/-- The coin-false class: the tables pricing the coin `0` (every `Rec_k`, and `Other`). -/
def recClass (K : ℕ) : Finset ↥(iterTables K) := univ.filter (fun T => T.1 (coin1 K) = 0)

lemma baseState_mem_recClass_iff (ω : Base K) : baseState ω ∈ recClass K ↔ ω.1 = false := by
  simp only [recClass, Finset.mem_filter, Finset.mem_univ, true_and, baseState_coin]
  cases h : ω.1 <;> simp

lemma sum_baseMass_notcoin_mul (f : Bool → ℚ) :
    ∑ ω : Base K, (if ω.1 = false then baseMass p ω * f ω.1 else 0) = (1 - p.q) * f false := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, ↓reduceIte, Bool.true_eq_false, Finset.sum_const_zero, zero_add]
  have e : ∀ k : Fin K, baseMass p (false, k) * f false = p.w k * ((1 - p.q) * f false) := by
    intro k; unfold baseMass; simp only [Bool.false_eq_true, ↓reduceIte]; ring
  simp only [e]
  rw [← Finset.sum_mul, p.hw1, one_mul]

lemma massOf_notcoin : massOf (baseMass p) (fun ω : Base K => ω.1 = false) = 1 - p.q := by
  unfold massOf
  have := sum_baseMass_notcoin_mul p (fun _ => 1)
  simp only [mul_one] at this
  exact this

lemma stateClassMass_recClass : stateClassMass (scPrior p) (recClass K) = 1 - p.q := by
  unfold scPrior
  rw [IndepCalc.stateClassMass_toPrior]
  change massOf (baseMass p) (fun ω₀ : Base K => baseState ω₀ ∈ recClass K) = 1 - p.q
  rw [massOf_congr _ (fun ω₀ => baseState_mem_recClass_iff ω₀)]
  exact massOf_notcoin p

lemma recClass_pos (hq : p.q < 1) : 0 < stateClassMass (scPrior p) (recClass K) := by
  rw [stateClassMass_recClass]; linarith

/-- Under the prior re-frozen on the coin-false class, `𝔼''[U | pp = π] = V · roundSum π + r₀ false`. -/
theorem conditionOn_rec_exAnteValue_eq (h : 0 < stateClassMass (scPrior p) (recClass K))
    (hq : p.q < 1) (π : Policy (iterTables K) Bool) :
    (conditionOn (scPrior p) (recClass K) h).exAnteValue π =
      p.V * roundSum p.γ π + p.r₀ false := by
  unfold scPrior
  rw [IndepCalc.conditionOn_exAnteValue_toPrior (scData p) (recClass K) h π (ν_pos p π)]
  change (∑ ω₀ : Base K, if baseState ω₀ ∈ recClass K then baseMass p ω₀ * scU p ω₀ π else 0) /
    massOf (baseMass p) (fun ω₀ : Base K => baseState ω₀ ∈ recClass K) = _
  rw [massOf_congr _ (fun ω₀ => baseState_mem_recClass_iff ω₀), massOf_notcoin]
  simp only [baseState_mem_recClass_iff]
  unfold scU
  rw [show (∑ ω₀ : Base K, if ω₀.1 = false then
      baseMass p ω₀ * (payoff p.c p.V ω₀.1 * roundSum p.γ π + p.r₀ ω₀.1) else 0) = _ from
    sum_baseMass_notcoin_mul p (fun b => payoff p.c p.V b * roundSum p.γ π + p.r₀ b)]
  rw [mul_div_cancel_left₀ _ (by linarith : (1 - p.q) ≠ 0)]
  simp [payoff]

/-- **The reversal**: the prior re-frozen on the coin-false class prefers `payAll` to `refrozen t`
by exactly `V · ∑_{k≥t} γ_k`. -/
theorem rec_refrozen_gap (hq : p.q < 1) (t : ℕ) :
    (conditionOn (scPrior p) (recClass K) (recClass_pos p hq)).exAnteValue payAll -
      (conditionOn (scPrior p) (recClass K) (recClass_pos p hq)).exAnteValue (refrozen t) =
      p.V * tailSum p.γ t := by
  rw [conditionOn_rec_exAnteValue_eq p _ hq, conditionOn_rec_exAnteValue_eq p _ hq,
    ← roundSum_payAll_sub_refrozen]
  ring

theorem rec_prefers_payAll (hq : p.q < 1) (hV : 0 < p.V) (hγ : ∀ k, 0 < p.γ k) (t : ℕ)
    (ht : t < K) :
    (conditionOn (scPrior p) (recClass K) (recClass_pos p hq)).exAnteValue (refrozen t) <
      (conditionOn (scPrior p) (recClass K) (recClass_pos p hq)).exAnteValue payAll := by
  have h1 := rec_refrozen_gap p hq t
  have h2 := tailSum_pos p hγ t ht
  nlinarith

end Cleanroom.Bli.UdtBliTiling.AuditR1
