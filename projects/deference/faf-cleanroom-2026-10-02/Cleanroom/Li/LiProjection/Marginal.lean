import Cleanroom.Li.LiProjection.Defs
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Properties.AffinePersistence
import LogicalInduction.Properties.Support.Exploitation
import LogicalInduction.Framework.Machine.SpliceMachine
import LogicalInduction.Framework.Machine.SentenceMachine

/-!
# `li-projection` · Marginal: restriction, marginal, limits (T1.7) and summable convergence (T4.4)

Package `Cleanroom.Li.LiProjection` ([[li-projection-mandate]]), file 7 of the layout.

* **Restriction**: on a `u`-free sentence the projected price *is* the base price, on every day
  (`project_restrict`) — the note's "`𝕡_n ↾ base = 𝕡̄_n` exactly".
* **Marginal**: `project P u q n (atom u) = q_n 𝕡̄_n(⊤) + (1 − q_n) 𝕡̄_n(⊥)` exactly
  (`project_atom`), whence `→ q_∞` (`project_atom_tendsto`) since `𝕡̄_n(⊤) → 1`, `𝕡̄_n(⊥) → 0` by
  provability induction at the constant families. **Not** the exact identity `𝕡_n(u) = q_n` at
  finite `n` (zip AUDIT §2.6; T7.3): that would need `𝕡̄_n(⊤) = 1`, which inductors promise only in
  the limit. The limiting belief of the projection on `u` is `q_∞` (`limitingBelief_project_atom`)
  — proved from the *base* inductor's criterion alone, so it does not rest on Lemma A.
* **Summable convergence on stage-decided sentences** (T4.4): for `φ ∈ DP.D k`,
  `Summable (fun n => 1 − P n φ)` and `Summable (fun n => P n (∼φ))` — the trader buying one share
  of `φ` daily (selling one share of `∼φ` daily) has net worth `Σ (1 − P n φ)` in every world
  plausible from day `k`, so divergence would exploit. A rate the corpus lacks; the contrast with
  Proposition 5.5.1 is that the rate is summable but not computable.
-/

namespace Cleanroom.Li.LiProjection

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Filter Topology

/-! ## T1.7 Restriction and marginal -/

/-- **Restriction.** On a `u`-free sentence the projected price is the base price, every day.
Source: [[dose-response]] §6.1 Lemma A ("restriction: `𝕡_n ↾ base = 𝕡̄_n` exactly")
Kind: P
Fidelity: exact -/
theorem project_restrict (P : History) (u : ℕ) (q : ℕ → ℚ) (n : ℕ) {φ : Sentence}
    (hφ : AtomFreeSentence u φ) : project P u q n φ = P n φ := by
  rw [project_apply, subst_eq_self_of_atomFree u true φ hφ, subst_eq_self_of_atomFree u false φ hφ]
  ring

/-- **Marginal, exact form.** `project P u q n (atom u) = q_n · P n ⊤ + (1 − q_n) · P n ⊥`.
Source: [[dose-response]] §6.1 Lemma A ("marginal")
Kind: P
Fidelity: exact -/
theorem project_atom (P : History) (u : ℕ) (q : ℕ → ℚ) (n : ℕ) :
    project P u q n (Formula.atom u) = (q n : ℝ) * P n ⊤ + (1 - (q n : ℝ)) * P n ⊥ := by
  rw [project_apply, subst_atom_self, subst_atom_self]
  rfl

/-- The negated atom: `project P u q n (∼atom u) = q_n · P n (∼⊤) + (1 − q_n) · P n (∼⊥)`.
Source: none: infrastructure (for the limit-coherence check of T4.3)
Kind: L
Fidelity: n/a -/
theorem project_neg_atom (P : History) (u : ℕ) (q : ℕ → ℚ) (n : ℕ) :
    project P u q n (∼Formula.atom u) = (q n : ℝ) * P n (∼⊤) + (1 - (q n : ℝ)) * P n (∼⊥) := by
  rw [project_apply]
  show (q n : ℝ) * P n (∼((Formula.atom u)⟦substAtom u true⟧)) +
      (1 - (q n : ℝ)) * P n (∼((Formula.atom u)⟦substAtom u false⟧)) = _
  rw [subst_atom_self, subst_atom_self]
  rfl

/-! ## The constants converge: `P n ⊤ → 1`, `P n ⊥ → 0` -/

/-- `P n ⊤ → 1` for any inductor over a process with a consistent world at every stage
(`lic_provind_true` at the constant family `⊤`).
Source: [[dose-response]] §6.1 Lemma A ("`𝕡̄_n(⊤) → 1` by Convergence [LI 4.1.1] and Limit Coherence [LI 4.1.2]")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem tendsto_price_top (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n => P n ⊤) atTop (𝓝 1) := by
  have h := lic_provind_true P DP (fun _ => (⊤ : Sentence)) (MachineSentenceCodes.const _)
    (fun _ v _ => PCWorld.holds_top v) hworld
  exact tendsto_sub_nhds_zero_iff.mp h

/-- `P n ⊥ → 0` (`lic_provind_false` at the constant family `⊥`).
Source: [[dose-response]] §6.1 Lemma A
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem tendsto_price_bot (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n => P n ⊥) atTop (𝓝 0) := by
  have h := lic_provind_false P DP (fun _ => (⊥ : Sentence)) (MachineSentenceCodes.const _)
    (fun _ v _ => by rw [PCWorld.holds_neg]; exact id) hworld
  exact tendsto_sub_nhds_zero_iff.mp h

/-- `P n (∼⊤) → 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tendsto_price_neg_top (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n => P n (∼⊤)) atTop (𝓝 0) := by
  have h := lic_provind_false P DP (fun _ => (∼⊤ : Sentence)) (MachineSentenceCodes.const _)
    (fun _ v _ => by rw [PCWorld.holds_neg, PCWorld.holds_neg]; exact fun h => h (PCWorld.holds_top v))
    hworld
  exact tendsto_sub_nhds_zero_iff.mp h

/-- `P n (∼⊥) → 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem tendsto_price_neg_bot (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n => P n (∼⊥)) atTop (𝓝 1) := by
  have h := lic_provind_true P DP (fun _ => (∼⊥ : Sentence)) (MachineSentenceCodes.const _)
    (fun _ v _ => by rw [PCWorld.holds_neg]; exact id) hworld
  exact tendsto_sub_nhds_zero_iff.mp h

/-! ## T1.7 The marginal converges to `q_∞` -/

/-- An eventually constant rational weight converges (as a real sequence) to its eventual value.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tendsto_weight_of_jump (q : ℕ → ℚ) (N : ℕ) (hjump : ∀ n, N ≤ n → q n = q N) :
    Tendsto (fun n => (q n : ℝ)) atTop (𝓝 (q N)) :=
  tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => by rw [hjump n hn]

/-- **The marginal converges to `q_∞`.** `project P u q n (atom u) → q N` for an eventually constant
weight over an inductor with a consistent world at every stage. The exact identity at finite `n`
is *not* available (zip AUDIT §2.6).
Source: [[dose-response]] §6.1 Lemma A ("whence `𝕡_n(u) → q_∞`")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem project_atom_tendsto (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ) (q : ℕ → ℚ) (N : ℕ)
    (hjump : ∀ n, N ≤ n → q n = q N) :
    Tendsto (fun n => project P u q n (Formula.atom u)) atTop (𝓝 (q N)) := by
  have hq := tendsto_weight_of_jump q N hjump
  have h := ((hq.mul (tendsto_price_top P DP hworld)).add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub hq).mul (tendsto_price_bot P DP hworld)))
  simp only [mul_one, mul_zero, add_zero] at h
  refine h.congr fun n => ?_
  rw [project_atom]

/-- The negated atom's projected price converges to `1 − q_∞`.
Source: none: infrastructure (limit coherence check for T4.3)
Kind: L
Fidelity: n/a -/
theorem project_neg_atom_tendsto (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ) (q : ℕ → ℚ) (N : ℕ)
    (hjump : ∀ n, N ≤ n → q n = q N) :
    Tendsto (fun n => project P u q n (∼Formula.atom u)) atTop (𝓝 (1 - q N)) := by
  have hq := tendsto_weight_of_jump q N hjump
  have h := ((hq.mul (tendsto_price_neg_top P DP hworld)).add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub hq).mul (tendsto_price_neg_bot P DP hworld)))
  simp only [mul_one, mul_zero, zero_add] at h
  refine h.congr fun n => ?_
  rw [project_neg_atom]

/-- **The limiting belief of the projection on `u` is `q_∞`**: `limitingBelief (project P u q) (atom u) = q N`.
Proved from the base inductor alone (a limsup of a convergent sequence); it does not rest on
Lemma A.
Source: [[dose-response]] §6.1 Lemma A ("So `𝕡_∞(u) = q_∞`")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem limitingBelief_project_atom (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ) (q : ℕ → ℚ) (N : ℕ)
    (hjump : ∀ n, N ≤ n → q n = q N) :
    limitingBelief (project P u q) (Formula.atom u) = q N :=
  (project_atom_tendsto P DP hworld u q N hjump).limsup_eq

/-- At a constant weight `c`: `limitingBelief (project P u (fun _ => c)) (atom u) = c`.
Source: [[dose-response]] §6.1 Lemma A; mandate T2.2
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem limitingBelief_project_const_atom (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ)
    (c : ℚ) : limitingBelief (project P u (fun _ => c)) (Formula.atom u) = c :=
  limitingBelief_project_atom P DP hworld u (fun _ => c) 0 (fun _ _ => rfl)

/-- The limiting belief of a projection on a `u`-free sentence is the base inductor's.
Source: [[dose-response]] §6.1 Lemma A (restriction)
Kind: L
Fidelity: exact -/
theorem limitingBelief_project_of_atomFree (P : History) (u : ℕ) (q : ℕ → ℚ) {φ : Sentence}
    (hφ : AtomFreeSentence u φ) : limitingBelief (project P u q) φ = limitingBelief P φ := by
  unfold limitingBelief
  congr 1
  funext n
  exact project_restrict P u q n hφ

/-! ## T4.4 Summable convergence on stage-decided sentences -/

/-- The trader buying one share of `φ` every day.
Source: [[lean-deference-2-inventory]] 032; mandate T4.4 (FAF's `APITests` `buyOneDaily` pattern)
Kind: D
Fidelity: exact -/
def buyDaily (φ : Sentence) : Trader where
  strat _ := { trades := [(EF.const 1, φ)], rank_le := by simp }

/-- The trader selling one share of `ψ` every day.
Source: mandate T4.4 (dual)
Kind: D
Fidelity: exact -/
def sellDaily (ψ : Sentence) : Trader where
  strat _ := { trades := [(EF.const (-1), ψ)], rank_le := by simp }

/-- `buyDaily φ` is efficiently computable (FAF's machine-side single-trade constructor).
Source: FAF `APITests/LogicalInduction.lean` §2
Kind: L
Fidelity: exact -/
theorem buyDaily_ec (φ : Sentence) : EfficientlyComputable (buyDaily φ) :=
  EfficientlyComputable.ofSingleTradeBlocksBig _ (fun _ => EF.const 1) (fun _ => φ)
    (MachineTokenStream.const (EF.const 1).serialize) (fun _ => trivial)
    (MachineSentenceCodes.const φ) (fun _ => rfl)

/-- `sellDaily ψ` is efficiently computable.
Source: FAF `APITests/LogicalInduction.lean` §2
Kind: L
Fidelity: exact -/
theorem sellDaily_ec (ψ : Sentence) : EfficientlyComputable (sellDaily ψ) :=
  EfficientlyComputable.ofSingleTradeBlocksBig _ (fun _ => EF.const (-1)) (fun _ => ψ)
    (MachineTokenStream.const (EF.const (-1)).serialize) (fun _ => trivial)
    (MachineSentenceCodes.const ψ) (fun _ => rfl)

/-- `buyDaily_netWorth`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma buyDaily_netWorth (φ : Sentence) (P : History) (v : PCWorld) (n : ℕ) :
    (buyDaily φ).netWorth P v n = ∑ i ∈ Finset.range (n + 1), (v.payout φ - P i φ) := by
  unfold Trader.netWorth
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [buyDaily, Strategy.value]

/-- `sellDaily_netWorth`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sellDaily_netWorth (ψ : Sentence) (P : History) (v : PCWorld) (n : ℕ) :
    (sellDaily ψ).netWorth P v n = ∑ i ∈ Finset.range (n + 1), (P i ψ - v.payout ψ) := by
  unfold Trader.netWorth
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [sellDaily, Strategy.value]

/-- **Summable convergence on a stage-decided sentence.** For `φ ∈ DP.D k`,
`Summable (fun n => 1 − P n φ)`: the trader buying one share of `φ` daily has net worth
`Σ_{i ≤ n} (1 − P i φ)` in every world plausible at a day `n ≥ k` and is bounded below by `−k`
before, so a divergent sum would exploit `P`.
Source: mandate T4.4 (a lemma the corpus lacks; contrast LI Proposition 5.5.1: summable, not computable)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem summable_one_sub_price_of_mem_stage (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {k : ℕ} {φ : Sentence} (hφ : φ ∈ DP.D k) :
    Summable (fun n => 1 - P n φ) := by
  by_contra hns
  have hP := IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hw0 : ∀ n, 0 ≤ 1 - P n φ := fun n => by linarith [(hP n φ).2]
  have hunb : ∀ B : ℝ, ∃ n, B < ∑ i ∈ Finset.range n, (1 - P i φ) := by
    intro B
    by_contra hall
    push_neg at hall
    exact hns (summable_of_sum_range_le hw0 hall)
  apply hLI.noExploit (buyDaily φ) (buyDaily_ec φ)
  apply exploits_of_bddBelow_of_unbounded (buyDaily φ) P DP k
  · rintro x ⟨n, v, hv, rfl⟩
    rw [buyDaily_netWorth]
    by_cases hnk : k ≤ n
    · have hvφ : v.Holds φ := hv φ (DP.mono_le hnk hφ)
      have : ∀ i ∈ Finset.range (n + 1), (0 : ℝ) ≤ v.payout φ - P i φ := by
        intro i _
        rw [PCWorld.payout, if_pos hvφ]
        linarith [(hP i φ).2]
      have hsum := Finset.sum_nonneg this
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    · push_neg at hnk
      have hterm : ∀ i ∈ Finset.range (n + 1), (-1 : ℝ) ≤ v.payout φ - P i φ := by
        intro i _
        linarith [(payout_mem_Icc v φ).1, (hP i φ).2]
      have hsum := Finset.sum_le_sum hterm
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
      have hcast : ((n + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hnk
      push_cast at hsum hcast
      linarith
  · intro B
    obtain ⟨m, hm⟩ := hunb B
    obtain ⟨v, hv⟩ := hworld (max m k)
    refine ⟨(buyDaily φ).netWorth P v (max m k), ⟨max m k, v, hv, rfl⟩, ?_⟩
    rw [buyDaily_netWorth]
    have hvφ : v.Holds φ := hv φ (DP.mono_le (le_max_right m k) hφ)
    have hterm : ∀ i, v.payout φ - P i φ = 1 - P i φ := fun i => by
      rw [PCWorld.payout, if_pos hvφ]
    simp only [hterm]
    calc B < ∑ i ∈ Finset.range m, (1 - P i φ) := hm
      _ ≤ ∑ i ∈ Finset.range (max m k + 1), (1 - P i φ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_trans (le_max_left m k) (Nat.le_succ _)))
        · intro i _ _; exact hw0 i

/-- **Summable convergence, dual:** for `φ ∈ DP.D k`, `Summable (fun n => P n (∼φ))` — the trader
selling one share of `∼φ` daily collects `Σ P i (∼φ)` in every world plausible from day `k`.
Source: mandate T4.4 (dual)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem summable_price_neg_of_mem_stage (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {k : ℕ} {φ : Sentence} (hφ : φ ∈ DP.D k) :
    Summable (fun n => P n (∼φ)) := by
  by_contra hns
  have hP := IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hw0 : ∀ n, 0 ≤ P n (∼φ) := fun n => (hP n (∼φ)).1
  have hunb : ∀ B : ℝ, ∃ n, B < ∑ i ∈ Finset.range n, P i (∼φ) := by
    intro B
    by_contra hall
    push_neg at hall
    exact hns (summable_of_sum_range_le hw0 hall)
  apply hLI.noExploit (sellDaily (∼φ)) (sellDaily_ec (∼φ))
  apply exploits_of_bddBelow_of_unbounded (sellDaily (∼φ)) P DP k
  · rintro x ⟨n, v, hv, rfl⟩
    rw [sellDaily_netWorth]
    by_cases hnk : k ≤ n
    · have hvφ : ¬ v.Holds (∼φ) := by
        rw [PCWorld.holds_neg]; exact fun h => h (hv φ (DP.mono_le hnk hφ))
      have : ∀ i ∈ Finset.range (n + 1), (0 : ℝ) ≤ P i (∼φ) - v.payout (∼φ) := by
        intro i _
        rw [PCWorld.payout, if_neg hvφ]
        linarith [(hP i (∼φ)).1]
      have hsum := Finset.sum_nonneg this
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    · push_neg at hnk
      have hterm : ∀ i ∈ Finset.range (n + 1), (-1 : ℝ) ≤ P i (∼φ) - v.payout (∼φ) := by
        intro i _
        linarith [(payout_mem_Icc v (∼φ)).2, (hP i (∼φ)).1]
      have hsum := Finset.sum_le_sum hterm
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
      have hcast : ((n + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hnk
      push_cast at hsum hcast
      linarith
  · intro B
    obtain ⟨m, hm⟩ := hunb B
    obtain ⟨v, hv⟩ := hworld (max m k)
    refine ⟨(sellDaily (∼φ)).netWorth P v (max m k), ⟨max m k, v, hv, rfl⟩, ?_⟩
    rw [sellDaily_netWorth]
    have hvφ : ¬ v.Holds (∼φ) := by
      rw [PCWorld.holds_neg]; exact fun h => h (hv φ (DP.mono_le (le_max_right m k) hφ))
    have hterm : ∀ i, P i (∼φ) - v.payout (∼φ) = P i (∼φ) := fun i => by
      rw [PCWorld.payout, if_neg hvφ]; ring
    simp only [hterm]
    calc B < ∑ i ∈ Finset.range m, P i (∼φ) := hm
      _ ≤ ∑ i ∈ Finset.range (max m k + 1), P i (∼φ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_trans (le_max_left m k) (Nat.le_succ _)))
        · intro i _ _; exact hw0 i

/-- The shifted form the mandate states: `Summable (fun n => 1 − P (n + k) φ)` for `φ ∈ DP.D k`.
Source: mandate T4.4
Kind: L
Fidelity: exact -/
theorem summable_one_sub_price_shift (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    {k : ℕ} {φ : Sentence} (hφ : φ ∈ DP.D k) :
    Summable (fun n => 1 - P (n + k) φ) :=
  (summable_nat_add_iff k).mpr (summable_one_sub_price_of_mem_stage P DP hworld hφ)

/-- `P n ⊤ → 1` with a summable rate, from T4.4 at `⊤ ∈ DP.D 0` — stated for processes whose stage
`0` contains `⊤`; in general `tendsto_price_top` needs no such stage.
Source: mandate T4.4 ("At `φ := ⊤`, `k := 0` this gives `P n ⊤ → 1` with a summable rate")
Kind: L
Fidelity: exact -/
theorem summable_one_sub_price_top (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (htop : (⊤ : Sentence) ∈ DP.D 0) :
    Summable (fun n => 1 - P n ⊤) :=
  summable_one_sub_price_of_mem_stage P DP hworld htop

end Cleanroom.Li.LiProjection
