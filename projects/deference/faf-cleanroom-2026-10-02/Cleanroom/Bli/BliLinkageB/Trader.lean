import Cleanroom.Bli.BliLinkageB.Mixture
import LogicalInduction.Framework.Machine.SpliceMachine
import LogicalInduction.Properties.Support.Exploitation

/-!
# bli-linkage, angle B — the one-share trader (K3b)

`buyOne ψ` buys one share of `ψ n` on day `n` (`(Tr.strat n).trades = [(EF.const 1, ψ n)]`).

* `buyOne_ec`: efficiently computable, by FAF's `EfficientlyComputable.ofSingleTradeBlocksBig`
  with the constant feature stream (`MachineTokenStream.const`) and a machine-metered sentence
  family. Hypotheses (a).
* `buyOne_exploits`: it exploits any market pricing `ψ n` at most `ε n`, with the partial sums
  of `ε` bounded by `C` (the finite form of "summable", `summable_partial_sums` turns a summable
  nonnegative `ε` into it), provided every "moved" day's `ψ n` is entailed by some stage and
  there are infinitely many moved days (`hmove`). By FAF's definitional engine
  `exploits_of_bddBelow_of_unbounded` (`Properties/Support/Exploitation.lean`): every
  plausible assessment is `≥ −C` (long positions, payouts `≥ 0`), and for every `B` the first
  `⌈B + C⌉ + 1` moved members have all entered by some stage `k`, where a world consistent with
  `D k` pays them. Not `exploits_of_ge_partialSums`, which needs a world-independent lower bound
  on every day's partial sum (the mandate's warning).
* `not_isLogicalInductor_of_cheap_moves`: hence no logical inductor prices such a family that
  cheaply; `no_inductor_prices_zero_eventually` is the `Q n (ψ n) = 0` (for `n ≥ N`) form that
  K3a feeds.

**`hmove` is a hypothesis** (the mandate's § K3): the theorem is conditional on the rounded
price moving infinitely often, and it is grade (a). The program's derivation of the move from
`lic_provind` is a misreading, filed in findings; the LIA instance over `bli-leak`'s family is
not built in this attempt.
-/

namespace Cleanroom.Bli.BliLinkageB

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

/-- **The one-share trader**: on day `n`, one share of `ψ n` at coefficient `EF.const 1`.
Source: mandate K3b (`buyOne ψ`); [[bli-program]] §3.6(iii)
Kind: D
Fidelity: exact -/
def buyOne (ψ : ℕ → Sentence) : Trader where
  strat n :=
    { trades := [(EF.const 1, ψ n)]
      rank_le := by
        intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        simp }

/-- The day-`n` strategy's value: the share's payout minus its price.
Source: none: infrastructure (FAF `Strategy.value`)
Kind: L
Fidelity: n/a -/
theorem buyOne_value (ψ : ℕ → Sentence) (V : History) (w : Sentence → ℝ) (n : ℕ) :
    ((buyOne ψ).strat n).value V w = w (ψ n) - V n (ψ n) := by
  simp [buyOne, Strategy.value, EF.denote]

/-- The net worth after day `n`: `∑_{i ≤ n} (payout(ψ i) − 𝓥_i(ψ i))`.
Source: none: infrastructure (FAF `Trader.netWorth`)
Kind: L
Fidelity: n/a -/
theorem buyOne_netWorth (ψ : ℕ → Sentence) (V : History) (v : PCWorld) (n : ℕ) :
    (buyOne ψ).netWorth V v n = ∑ i ∈ Finset.range (n + 1), (v.payout (ψ i) - V i (ψ i)) := by
  unfold Trader.netWorth
  exact Finset.sum_congr rfl fun i _ => buyOne_value ψ V v.payout i

/-- **The one-share trader is efficiently computable** for a machine-metered family.
Source: mandate K3b; FAF `EfficientlyComputable.ofSingleTradeBlocksBig` (`Framework/Machine/SpliceMachine.lean:461`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem buyOne_ec {ψ : ℕ → Sentence} (hψ : MachineSentenceCodes ψ) :
    EfficientlyComputable (buyOne ψ) :=
  EfficientlyComputable.ofSingleTradeBlocksBig (buyOne ψ) (fun _ => EF.const 1) ψ
    (MachineTokenStream.const _) (fun _ => trivial) hψ (fun _ => rfl)

/-- **The one-share trader exploits a market that prices a frequently-true family cheaply.**
If `𝓥_n(ψ n) ≤ ε n` with partial sums of `ε` bounded by `C`, every stage has a consistent
world, every moved day's `ψ n` is entailed by some stage, and there are infinitely many moved
days, then `buyOne ψ` exploits `𝓥` relative to `DP`.
Source: mandate K3b; [[bli-program]] §3.6(iii); FAF `exploits_of_bddBelow_of_unbounded`
Kind: P
Fidelity: exact (`hmove` explicit, as the mandate's § K3 requires)
Hyps: (a) -/
theorem buyOne_exploits (ψ : ℕ → Sentence) (V : History) (DP : DeductiveProcess) (ε : ℕ → ℝ)
    (C : ℝ) (hε : ∀ n, V n (ψ n) ≤ ε n) (hC : ∀ n, ∑ i ∈ Finset.range (n + 1), ε i ≤ C)
    (hworld : ∀ k, ∃ v : PCWorld, v.ConsistentWith (DP.D k)) {moved : ℕ → Prop}
    (hdec : ∀ n, moved n → ∃ k, ∀ v : PCWorld, v.ConsistentWith (DP.D k) → v.Holds (ψ n))
    (hmove : Set.Infinite {n | moved n}) : (buyOne ψ).Exploits V DP := by
  refine exploits_of_bddBelow_of_unbounded _ _ _ C ?_ ?_
  · rintro x ⟨n, v, -, rfl⟩
    rw [buyOne_netWorth, Finset.sum_sub_distrib]
    have h1 := Finset.sum_nonneg fun i (_ : i ∈ Finset.range (n + 1)) => payout_nonneg v (ψ i)
    have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.range (n + 1)) => hε i
    linarith [hC n]
  · intro B
    obtain ⟨t, ht, hcard⟩ := hmove.exists_subset_card_eq (⌈B + C⌉₊ + 1)
    have hk : ∀ i, ∃ k, i ∈ t → ∀ v : PCWorld, v.ConsistentWith (DP.D k) → v.Holds (ψ i) := by
      intro i
      by_cases hi : i ∈ t
      · obtain ⟨k, hk⟩ := hdec i (ht hi)
        exact ⟨k, fun _ => hk⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose kf hkf using hk
    obtain ⟨v, hv⟩ := hworld (max (t.sup id) (t.sup kf))
    refine ⟨_, ⟨max (t.sup id) (t.sup kf), v, hv, rfl⟩, ?_⟩
    rw [buyOne_netWorth, Finset.sum_sub_distrib]
    have hvi : ∀ i ∈ t, v.Holds (ψ i) := fun i hi =>
      hkf i hi v fun φ hφ => hv φ (DP.mono_le
        (le_trans (Finset.le_sup (f := kf) hi) (le_max_right _ _)) hφ)
    have hsub : t ⊆ Finset.range (max (t.sup id) (t.sup kf) + 1) := fun i hi =>
      Finset.mem_range.2 (Nat.lt_succ_of_le
        (le_trans (Finset.le_sup (f := id) hi) (le_max_left _ _)))
    have h1 : ∑ i ∈ t, v.payout (ψ i) ≤
        ∑ i ∈ Finset.range (max (t.sup id) (t.sup kf) + 1), v.payout (ψ i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => payout_nonneg _ _
    have h2 : ∑ i ∈ t, v.payout (ψ i) = (⌈B + C⌉₊ : ℝ) + 1 := by
      rw [Finset.sum_congr rfl fun i hi => payout_of_holds (hvi i hi), Finset.sum_const,
        nsmul_eq_mul, mul_one, hcard]
      push_cast; ring
    have h3 : ∑ i ∈ Finset.range (max (t.sup id) (t.sup kf) + 1), V i (ψ i) ≤ C :=
      le_trans (Finset.sum_le_sum fun i _ => hε i) (hC _)
    have h4 : B + C ≤ (⌈B + C⌉₊ : ℝ) := Nat.le_ceil _
    linarith

/-- **No logical inductor prices a frequently-true, machine-metered family cheaply.**
Source: mandate K3b (the trader half); [[bli-program]] §3.6(iii)
Kind: C
Fidelity: exact (`hmove` explicit)
Hyps: (a) -/
theorem not_isLogicalInductor_of_cheap_moves {ψ : ℕ → Sentence} (hψ : MachineSentenceCodes ψ)
    (V : History) (DP : DeductiveProcess) (ε : ℕ → ℝ) (C : ℝ) (hε : ∀ n, V n (ψ n) ≤ ε n)
    (hC : ∀ n, ∑ i ∈ Finset.range (n + 1), ε i ≤ C)
    (hworld : ∀ k, ∃ v : PCWorld, v.ConsistentWith (DP.D k)) {moved : ℕ → Prop}
    (hdec : ∀ n, moved n → ∃ k, ∀ v : PCWorld, v.ConsistentWith (DP.D k) → v.Holds (ψ n))
    (hmove : Set.Infinite {n | moved n}) : ¬ IsLogicalInductor V DP := fun hLI =>
  hLI.noExploit _ (buyOne_ec hψ) (buyOne_exploits ψ V DP ε C hε hC hworld hdec hmove)

/-- The partial sums of the eventually-zero sequence `[n < N]` are bounded by `N`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_indicator_lt_le (N n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (if i < N then (1 : ℝ) else 0) ≤ N := by
  rw [Finset.sum_boole]
  have : (Finset.range (n + 1)).filter (fun i => i < N) ⊆ Finset.range N := fun i hi =>
    Finset.mem_range.2 (Finset.mem_filter.1 hi).2
  have := Finset.card_le_card this
  rw [Finset.card_range] at this
  exact_mod_cast this

/-- **The `Q n (ψ n) = 0` eventually form**: a logical inductor cannot price a machine-metered,
frequently-true family at `0` from some day on.
Source: mandate K3 (the conclusion of record's price input)
Kind: C
Fidelity: exact (`hmove` explicit)
Hyps: (a) -/
theorem no_inductor_prices_zero_eventually {ψ : ℕ → Sentence} (hψ : MachineSentenceCodes ψ)
    (V : History) (DP : DeductiveProcess) [hLI : IsLogicalInductor V DP] (N : ℕ)
    (hzero : ∀ n ≥ N, V n (ψ n) = 0)
    (hworld : ∀ k, ∃ v : PCWorld, v.ConsistentWith (DP.D k)) {moved : ℕ → Prop}
    (hdec : ∀ n, moved n → ∃ k, ∀ v : PCWorld, v.ConsistentWith (DP.D k) → v.Holds (ψ n))
    (hmove : Set.Infinite {n | moved n}) : False := by
  refine not_isLogicalInductor_of_cheap_moves hψ V DP (fun n => if n < N then 1 else 0) N
    (fun n => ?_) (sum_indicator_lt_le N) hworld hdec hmove hLI
  by_cases hn : n < N
  · rw [if_pos hn]; exact (IsLogicalInductor.price_mem_Icc (P := V) (DP := DP) n (ψ n)).2
  · rw [if_neg hn, hzero n (not_lt.1 hn)]

/-- A summable nonnegative `ε` has partial sums bounded by its sum (the bridge from the
mandate's `Summable ε` to `buyOne_exploits`'s `hC`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma summable_partial_sums {ε : ℕ → ℝ} (h0 : ∀ n, 0 ≤ ε n) (hs : Summable ε) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), ε i ≤ ∑' i, ε i :=
  hs.sum_le_tsum _ fun i _ => h0 i

end Cleanroom.Bli.BliLinkageB
