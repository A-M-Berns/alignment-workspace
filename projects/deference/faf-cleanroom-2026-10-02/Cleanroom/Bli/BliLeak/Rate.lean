import Cleanroom.Bli.BliLeak.Trader
import Cleanroom.Bli.BliFound.Bridge
import Cleanroom.Bli.BliFound.Emitter

/-!
# `bli-leak` · Rate: how late a leak planted on day `k` can be read (E1)

**The honest rate.** `bli-found`'s bridge lemma meters what an efficiently computable trader can
name on day `n` by its polynomial output length `P(n)` through `bridgeBound C P`, and
`bridgeBound_le` bounds that by `2 ^ ((C + 6)(P + 1))` — **exponential** in the polynomial, not
polynomial, because FAF's structured paper-prime escape lets a word of `P` digits name a sentence
whose canonical size is exponential in `P` (`tokenSize_le_of_structured`). So the theorem the
bridge supports is

`no_early_read : ∃ A E, ∀ n φ, MentionedBy (Tr.strat n) φ → tokenSize φ ≤ 2 ^ (A · (n + 1) ^ E)`,

and for a sentence large on day `k` (`tokenSize φ > 2 ^ (2 ^ k)`) it gives `2 ^ k < A · (n + 1) ^ E`
(`no_early_read_large`): a leak planted on day `k` is unreadable before a day of order
`(2 ^ k / A) ^ (1 / E)` — **singly** exponential in `k`. The mandate's E1 (`tokenSize φ ≤ A (n+1)^E`
and "unreadable before day `≈ 2 ^ (2 ^ k)`") is not what the size model supports; the construction
draft's "readable on day `k + 1`" (X8) is false a fortiori (findings K2, F-1).

The leak atoms of record are nevertheless eventually small on their own day (`leakAtom_small`,
from `bli-found`'s `machineSentenceCodes_eventually_small` and the machine certificate
`machineSentenceCodes_leakAtom`), which is the reading-back mechanism L3.3 exploits.
-/

namespace Cleanroom.Bli.BliLeak

open LogicalInduction LO.Propositional
open Cleanroom.Bli.BliFound

/-- **The leak atoms are eventually small on their own day**: the reading day of member `n` is a
day on which `leakAtom K n` is small (so the trader may name it), for every fixed pad `K`.
Source: mandate L3.1 (`leakAtom_small`); `bli-found` `machineSentenceCodes_eventually_small`
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem leakAtom_small (K : ℕ) : ∃ N, ∀ n ≥ N, SmallOn n (leakAtom K n) :=
  machineSentenceCodes_eventually_small (machineSentenceCodes_leakAtom K)

/-- **E1. What an e.c. trader can name on day `n` has size at most `2 ^ (A (n + 1) ^ E)`**, for
constants `A`, `E` read off the trader's `FP` polynomial: the bridge's `bridgeBound` through
`bridgeBound_le`. Exponential of a polynomial, not polynomial (module docstring; findings F-1).
Source: mandate E1 (`no_early_read`, statement corrected); `bli-found` `bridge_lemma` (the same
argument, stopped before the `2 ^ (2 ^ n)` step)
Kind: C
Fidelity: weaker: `2 ^ (A (n+1)^E)` in place of the mandate's `A (n+1)^E`, which the size model
does not support
Hyps: (a) -/
theorem no_early_read (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ∃ A E : ℕ, ∀ n φ, MentionedBy (Tr.strat n) φ → tokenSize φ ≤ 2 ^ (A * (n + 1) ^ E) := by
  obtain ⟨C, hC⟩ := tokenSize_le_of_structured
  obtain ⟨F, hF, hstrat⟩ := hTr
  obtain ⟨p, hp⟩ := Complexity.Cobham.output_length_poly_of_mem_FP hF
  refine ⟨(C + 6) * ((∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) + 1), p.natDegree,
    fun n φ hφ => ?_⟩
  rw [← hstrat n] at hφ
  have hsize := tokenSize_le_bridgeBound_of_mentionedBy hC hφ
  have hdig : (bitsToDigits (F (unaryDay n))).length ≤ p.eval n := by
    rw [length_bitsToDigits]
    have := hp (unaryDay n)
    rw [length_unaryDay] at this
    omega
  have hpoly : p.eval n + 1 ≤
      ((∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) + 1) * (n + 1) ^ p.natDegree := by
    have h1 := polynomial_eval_le p n
    have h2 : 1 ≤ (n + 1) ^ p.natDegree := Nat.one_le_pow _ _ (by omega)
    nlinarith
  calc tokenSize φ ≤ bridgeBound C (bitsToDigits (F (unaryDay n))).length := hsize
    _ ≤ bridgeBound C (p.eval n) := bridgeBound_mono C hdig
    _ ≤ 2 ^ ((C + 6) * (p.eval n + 1)) := bridgeBound_le C _
    _ ≤ 2 ^ ((C + 6) * ((∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) + 1)
          * (n + 1) ^ p.natDegree) := by
        apply Nat.pow_le_pow_right (by norm_num)
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ hpoly

/-- **E1, the rate**: a sentence large on day `k` can be mentioned by an e.c. trader on day `n`
only if `2 ^ k < A (n + 1) ^ E` — the day is at least of order `(2 ^ k / A) ^ (1 / E)`, singly
exponential in `k`. The construction draft's "readable on day `k + 1`" (X8) is false as a theorem.
Source: mandate E1 (`no_early_read_large`, rate corrected); [[bli-program-construction]] X8
(refuted); [[bli-program]] §3.2(a)
Kind: C
Fidelity: weaker: the singly-exponential rate the size model supports, not the mandate's
doubly-exponential one
Hyps: (a) -/
theorem no_early_read_large (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ∃ A E : ℕ, ∀ n φ k, MentionedBy (Tr.strat n) φ → ¬ SmallOn k φ →
      2 ^ k < A * (n + 1) ^ E := by
  obtain ⟨A, E, h⟩ := no_early_read Tr hTr
  refine ⟨A, E, fun n φ k hφ hk => ?_⟩
  have h1 := h n φ hφ
  unfold SmallOn sizeBound at hk
  push Not at hk
  by_contra hcon
  push Not at hcon
  have h2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hcon
  omega

/-- The rate at the leak atoms of record: a trader that mentions `leakAtom (4 ^ sizeBound k) m`
on day `n` has `2 ^ k < A (n + 1) ^ E`.
Source: mandate E1; L3.1 (`leakAtom_large_pow`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem leakAtom_unreadable_before (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ∃ A E : ℕ, ∀ n k m, MentionedBy (Tr.strat n) (leakAtom (4 ^ sizeBound k) m) →
      2 ^ k < A * (n + 1) ^ E := by
  obtain ⟨A, E, h⟩ := no_early_read_large Tr hTr
  exact ⟨A, E, fun n k m hφ => h n _ k hφ (leakAtom_large_pow k le_rfl m)⟩

end Cleanroom.Bli.BliLeak
