import Cleanroom.Bli.BliLinkage.LiaPackage

/-!
# Audit round 4 (adversarial) — probe: where the K3-at-LIA refutation lives

Evidence for [[bli-linkage-audit-r4-adversarial]] B1. The BLI paper defines "small" on day
`n` as the sentences "which the market assigns real prices to (if the logical inductor was
constructed by the Logical Induction Algorithm, this is the set of sentences bought or sold by
any trader)" (`references/bli/understanding-trust/overleaf-final-source/main.tex:427`). At
FAF's LIA that set is `(liaStates DP n).support` (the listed keys; FAF quotes `0` off it,
`RationalBeliefState.quote_eq_zero_of_not_mem`). The record's `smallSet n` is the syntactic
size-bounded set of bli-found D3 (`tokenSize ≤ 2^(2^n)`), chosen by [[bli-program]] §2.1,
which *rejected* the paper's reading ("small = traded …", bli-paper-031 / bli-soto-a-002
reading B) as circular for an arbitrary market. At the constructed inductor it is not circular.

This file shows, machine-checked, that `LiaPackage.not_lia_small_coherent_mixture_exists`
turns on that substitution:

1. the record's small set strictly exceeds the LIA's support on day `4`, for every `DP`;
2. so some small tautology is **unlisted** by the LIA on day `4`;
3. syntactic `E1x` forces the superbelief to copy the LIA's **default `0`** on it — a sentence
   the LIA never priced, hence large in the paper's sense — which is what contradicts
   coherence (a mixture prices it `1`);
4. the paper's constraint 1 at the LIA (`E1xSupp`: agreement on the listed keys) is strictly
   weaker than the record's `E1x`, by a `P` that agrees with the LIA on its support and
   prices everything else `1`;
5. the LIA bound of record is at least `n (n+1)^n` (its `j = n` term), so it is not a
   polynomial bound; the refutation is "`n (n+1)^n` against `2^(2^n − 2)`".

Not imported by the library. Elaborated with `scripts/lean-check`.
-/

namespace Cleanroom.Bli.BliLinkage.AuditR4

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound
open Cleanroom.Bli.BliLinkage

/-- **The paper's constraint 1 at an LIA-constructed inductor** (reading B of bli-soto-a-002,
the paper's own parenthetical): the superbelief agrees with the LIA on the sentences the LIA
actually prices, its listed keys. Not the record's `E1x` (syntactic `smallSet n`). -/
def E1xSupp (DP : DeductiveProcess) (P : History) : Prop :=
  ∀ n φ, φ ∈ (liaStates DP n).support → P n φ = liaHistory DP n φ

/-- 1. On day `4` the record's small set has more elements than the LIA lists (every `DP`):
`65536 < (smallSet 4).card` (bli-found) and `(liaStates DP 4).support.card ≤ 2945` (the
package). -/
theorem lia_support_card_lt_smallSet_card (DP : DeductiveProcess) :
    (liaStates DP 4).support.card < (smallSet 4).card := by
  have h1 := liaStates_support_card_le_day4 DP
  have h2 := sizeBound_lt_card_smallSet (n := 4) (by norm_num)
  have h3 : sizeBound 4 = 65536 := by unfold sizeBound; norm_num
  omega

/-- 2. A small tautology the LIA does not list on day `4` (pigeonhole over the chain of
`16384` small tautologies against at most `2945` listed keys). -/
theorem exists_small_taut_unlisted (DP : DeductiveProcess) :
    ∃ k, 4 + 4 * k ≤ sizeBound 4 ∧ tautChain k ∉ (liaStates DP 4).support := by
  have hcard : ((Finset.range 16384).image tautChain).card = 16384 := by
    rw [Finset.card_image_of_injective _ tautChain_injective, Finset.card_range]
  have hlt : (liaStates DP 4).support.card < ((Finset.range 16384).image tautChain).card := by
    rw [hcard]
    have := liaStates_support_card_le_day4 DP
    omega
  obtain ⟨φ, hφ, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hφ
  rw [Finset.mem_range] at hk
  refine ⟨k, ?_, hnot⟩
  have h3 : sizeBound 4 = 65536 := by unfold sizeBound; norm_num
  omega

/-- 3. **Syntactic `E1x` copies the LIA's default `0` onto an unpriced small tautology.** Under
`E1x (liaHistory DP) P` the superbelief prices some day-`4` small tautology at exactly `0`,
because the LIA never listed it. That `0` against coherence's `1` is the whole contradiction
of `lia_package_unsat`; under the paper's definition the sentence is large and `P` is free on
it. -/
theorem e1x_copies_default_zero (DP : DeductiveProcess) {P : History}
    (hE1 : E1x (liaHistory DP) P) :
    ∃ k, tautChain k ∈ smallSet 4 ∧ (∀ v : PCWorld, v.Holds (tautChain k)) ∧
      P 4 (tautChain k) = 0 := by
  obtain ⟨k, hk, hnot⟩ := exists_small_taut_unlisted DP
  have hsmall := tautChain_mem_smallSet hk
  refine ⟨k, hsmall, fun v => holds_tautChain v k, ?_⟩
  rw [hE1 4 _ hsmall, liaHistory_eq_quote_cast]
  change (((liaStates DP 4).quote (tautChain k) : ℚ) : ℝ) = 0
  rw [RationalBeliefState.quote_eq_zero_of_not_mem _ hnot]
  simp

/-- 4. **`E1xSupp` is strictly weaker than `E1x` at FAF's LIA** (every `DP`): the history that
copies the LIA on its listed keys and prices everything else `1` satisfies the paper's
constraint 1 and violates the record's `E1x` on day `4`. (Whether this `P` is coherent is not
claimed; the point is the scope of the agreement constraint.) -/
theorem e1xSupp_strictly_weaker (DP : DeductiveProcess) :
    ∃ P : History, E1xSupp DP P ∧ ¬ E1x (liaHistory DP) P := by
  classical
  refine ⟨fun n φ => if φ ∈ (liaStates DP n).support then liaHistory DP n φ else 1, ?_, ?_⟩
  · intro n φ hφ
    simp [hφ]
  · intro hE1
    obtain ⟨k, hk, hnot⟩ := exists_small_taut_unlisted DP
    have hsmall := tautChain_mem_smallSet hk
    have h := hE1 4 _ hsmall
    simp only [hnot, if_false] at h
    rw [liaHistory_eq_quote_cast] at h
    change (1 : ℝ) = (((liaStates DP 4).quote (tautChain k) : ℚ) : ℝ) at h
    rw [RationalBeliefState.quote_eq_zero_of_not_mem _ hnot] at h
    norm_num at h

/-- 5. The LIA bound of record is at least its `j = n` term `n (n+1)^n`: it is superpolynomial
in `n`, so "the LIA lists polynomially many sentences a day" is not what
`liaStates_support_card_le_poly` proves. -/
theorem lia_bound_ge_n_pow (n : ℕ) :
    n * (n + 1) ^ n ≤ ∑ j ∈ Finset.range (n + 1), (j * (n + 1) ^ j + j + 1) := by
  have h : n * (n + 1) ^ n + n + 1 ≤ ∑ j ∈ Finset.range (n + 1), (j * (n + 1) ^ j + j + 1) :=
    Finset.single_le_sum (f := fun j => j * (n + 1) ^ j + j + 1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_add_one n))
  exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans h)

end Cleanroom.Bli.BliLinkage.AuditR4
