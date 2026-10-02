import Cleanroom.Li.LiDiagonal.Defs
import LogicalInduction.Framework.Machine.SpliceMachine
import LogicalInduction.Framework.Machine.Witnesses

/-!
# `li-diagonal` · Agent: the agent that defects infinitely often (T8a)

bli-soto-a-066's environment, over FAF's criterion: an agent that defects on round `n` iff the
inductor's day-`n` price of "defect on `n`" is below a threshold `p n`, with the realized play fed
to the deductive process by the next day (`AgentCoupling`, `Defs.lean`). **If the thresholds are
not summable, the agent defects infinitely often** (`agent_defects_io`): otherwise, from some day
`m` on, every `D n` is priced at `≥ p n` and refuted the next day, and the trader that sells one
share of `D n` every day (`sellTrader`, e.c. by FAF's `ofSingleTradeBlocksBig` at a constant
coefficient) has net worth `≥ ∑_{m ≤ i < n} p i − (m + 1)` in every plausible world — bounded
below, unbounded above — so it exploits the market, against `IsLogicalInductor.noExploit`.

Hyps: (c) the coupling `C : AgentCoupling P DP D p` is the environment's design (K7): FAF's
`ParadoxResistanceQuote` gives `reflected` but nothing like `decided_by`, whose bounded delay
the source's "never loses" silently needs. Status `partial: coupling package (c)`; the package's
inhabitation is the coupled self-referential process (`li-coupled-pair` stretch).

Scope: single-market.
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO.Propositional
open Filter Topology

/-- The trader that sells one share of `D n` on day `n`.
Source: [[bli-soto-a-inventory]] 066; [[li-diagonal-mandate]] T8a
Kind: D
Fidelity: exact
Hyps: n/a -/
def sellTrader (D : ℕ → Sentence) : Trader :=
  ⟨fun n => ⟨[(EF.const (-1), D n)], fun p hp => by
    simp only [List.mem_singleton] at hp
    subst hp
    simp⟩⟩

/-- The sell trader is efficiently computable for e.c. `D` (FAF's `ofSingleTradeBlocksBig` at the
constant coefficient stream, as `efficientlyComputable_buyAtomDaily`).
Source: none: infrastructure (FAF `EfficientlyComputable.ofSingleTradeBlocksBig`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem sellTrader_ec (D : ℕ → Sentence) (hD : MachineSentenceCodes D) :
    EfficientlyComputable (sellTrader D) :=
  EfficientlyComputable.ofSingleTradeBlocksBig (sellTrader D) (fun _ => EF.const (-1)) D
    (MachineTokenStream.const (EF.const (-1)).serialize) (fun _ => trivial) hD (fun _ => rfl)

/-- The sell trader's day-`n` value in a valuation `w`: `P_n(D_n) − w(D_n)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sellTrader_value (D : ℕ → Sentence) (P : History) (w : Valuation) (n : ℕ) :
    ((sellTrader D).strat n).value P w = P n (D n) - w (D n) := by
  simp [sellTrader, Strategy.value, EF.denote_const]

/-- The sell trader's net worth is the sum of `P_i(D_i) − payout(D_i)` over days `≤ n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sellTrader_netWorth (D : ℕ → Sentence) (P : History) (v : PCWorld) (n : ℕ) :
    (sellTrader D).netWorth P v n = ∑ i ∈ Finset.range (n + 1), (P i (D i) - v.payout (D i)) := by
  unfold Trader.netWorth
  simp only [sellTrader_value]

/-- **T8a (headline). The coupled agent defects infinitely often** when the thresholds are not
summable: `∃ᶠ n, P_n(D_n) < p_n`. Otherwise the sell trader exploits the market. No upper bound
on `p` is assumed: at `p n > 1` the conclusion is immediate from `price_mem_Icc`, so the content
is in thresholds `p n → 0` with divergent sum, the source's `1/(2n)` (audit r2 adversarial N5).
Scope: single-market; threshold family `p`.
Source: [[bli-soto-a-inventory]] 066 ("`A` defects iff `1/P_n(D_n) > 2n`"), 067; [[li-diagonal-mandate]] T8a
Kind: C
Fidelity: exact (the source's `1/P > 2n` is `p n = 1/(2n)`)
Hyps: (c) the coupling `C` (the environment's design, K7); (a) `hp0` (thresholds are nonnegative) -/
theorem agent_defects_io (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (D : ℕ → Sentence) (p : ℕ → ℚ) (C : AgentCoupling P DP D p) (hp0 : ∀ n, 0 ≤ p n)
    (hdiv : Tendsto (prefixSum (fun n => (p n : ℝ))) atTop atTop)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∃ᶠ n in atTop, P n (D n) < (p n : ℝ) := by
  by_contra hnot
  rw [Filter.not_frequently] at hnot
  obtain ⟨m, hm⟩ := eventually_atTop.1 hnot
  have hP : ∀ n s, 0 ≤ P n s ∧ P n s ≤ 1 :=
    IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hmono : Monotone DP.D := monotone_nat_of_le_succ DP.mono
  have hpay01 : ∀ (v : PCWorld) s, 0 ≤ v.payout s ∧ v.payout s ≤ 1 := fun v s => by
    unfold PCWorld.payout; split_ifs <;> norm_num
  -- refuted shares pay nothing
  have hpay0 : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∀ i, m ≤ i → i < n → v.payout (D i) = 0 := by
    intro n v hv i hmi hin
    have hdec := C.decided_by i
    rw [if_neg (hm i hmi)] at hdec
    have hmem : ∼ D i ∈ DP.D n := hmono (by omega : i + 1 ≤ n) hdec
    have hholds : v.Holds (∼ D i) := hv _ hmem
    rw [PCWorld.holds_neg] at hholds
    unfold PCWorld.payout
    rw [if_neg hholds]
  -- termwise bounds
  have hterm_ge_neg1 : ∀ (v : PCWorld) i, -1 ≤ P i (D i) - v.payout (D i) := fun v i => by
    linarith [(hP i (D i)).1, (hpay01 v (D i)).2]
  have hterm_mid : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      ∀ i, m ≤ i → i < n → (p i : ℝ) ≤ P i (D i) - v.payout (D i) := by
    intro n v hv i hmi hin
    rw [hpay0 n v hv i hmi hin, sub_zero]
    exact le_of_not_gt (hm i hmi)
  -- the three-piece lower bound: range m, Ico m n, the day n
  have hsplit : ∀ n (v : PCWorld), m ≤ n → v.ConsistentWith (DP.D n) →
      -(m : ℝ) + (∑ i ∈ Finset.Ico m n, (p i : ℝ)) - 1 ≤ (sellTrader D).netWorth P v n := by
    intro n v hmn hv
    rw [sellTrader_netWorth, Finset.sum_range_succ, ← Finset.sum_range_add_sum_Ico _ hmn]
    have h1 : -(m : ℝ) ≤ ∑ i ∈ Finset.range m, (P i (D i) - v.payout (D i)) := by
      have := Finset.sum_le_sum (s := Finset.range m) (fun i _ => hterm_ge_neg1 v i)
      simpa using this
    have h2 : ∑ i ∈ Finset.Ico m n, (p i : ℝ) ≤
        ∑ i ∈ Finset.Ico m n, (P i (D i) - v.payout (D i)) :=
      Finset.sum_le_sum fun i hi => by
        rw [Finset.mem_Ico] at hi
        exact hterm_mid n v hv i hi.1 hi.2
    have h3 := hterm_ge_neg1 v n
    linarith
  -- the sell trader exploits
  have hexp : (sellTrader D).Exploits P DP := by
    constructor
    · -- bounded below by -(m+1), via the split for n ≥ m and termwise for n < m
      refine ⟨-((m : ℝ) + 1), ?_⟩
      rintro x ⟨n, v, hv, rfl⟩
      rcases le_or_gt m n with hmn | hnm
      · have := hsplit n v hmn hv
        have hpos : 0 ≤ ∑ i ∈ Finset.Ico m n, (p i : ℝ) :=
          Finset.sum_nonneg fun i _ => by exact_mod_cast hp0 i
        linarith
      · rw [sellTrader_netWorth]
        have := Finset.sum_le_sum (s := Finset.range (n + 1)) (fun i _ => hterm_ge_neg1 v i)
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_neg, mul_one] at this
        push_cast at this
        have hcast : (n : ℝ) ≤ m := by exact_mod_cast hnm.le
        linarith
    · -- unbounded above: the threshold sums diverge
      rintro ⟨B, hB⟩
      -- pick N ≥ m with prefixSum p N ≥ B + m + 1 + ∑_{i<m} p i
      have hev := (tendsto_atTop_atTop.1 hdiv) (B + (m : ℝ) + 2 + ∑ i ∈ Finset.range m, (p i : ℝ))
      obtain ⟨N₀, hN₀⟩ := hev
      set N := max N₀ m with hN
      obtain ⟨v, hv⟩ := hworld (N + 1)
      have hx : (sellTrader D).netWorth P v (N + 1) ∈ (sellTrader D).plausibleAssessments P DP :=
        ⟨N + 1, v, hv, rfl⟩
      have hle := hB hx
      have hsp := hsplit (N + 1) v (by omega) hv
      have hIco : ∑ i ∈ Finset.Ico m (N + 1), (p i : ℝ) =
          prefixSum (fun n => (p n : ℝ)) N - ∑ i ∈ Finset.range m, (p i : ℝ) := by
        have := Finset.sum_range_add_sum_Ico (fun i => (p i : ℝ)) (by omega : m ≤ N + 1)
        unfold prefixSum
        linarith
      have hN' := hN₀ N (le_max_left _ _)
      rw [hIco] at hsp
      linarith
  exact IsLogicalInductor.noExploit (sellTrader D) (sellTrader_ec D C.codes) hexp

end Cleanroom.Li.LiDiagonal
