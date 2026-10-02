import Cleanroom.Li.LiSpliceCondition.Defs
import LogicalInduction.Properties.Coherence
import LogicalInduction.Properties.AffinePersistence
import LogicalInduction.Properties.Support.Exploitation
import LogicalInduction.Framework.Machine.SpliceMachine
import LogicalInduction.Framework.Machine.WriteOutMachine
import LogicalInduction.Construction.Primcodable
import Mathlib.Analysis.PSeries

/-!
# `li-splice-condition` · Splice: switching between two belief processes (T1)

Package `Cleanroom.Li.LiSpliceCondition` ([[li-splice-condition-mandate]]), file 2 of the layout.

* **T1.1** The splice of two computable markets along a computable day selector is a computable
  market (`computableMarket_splice`); prices stay in `[0,1]` (`splice_mem_Icc`).
* **T1.2** *The splice is the Convergence theorem.* If the two components' prices on a sentence
  `φ` converge to different limits and the selector takes each value infinitely often, the
  splice's price on `φ` has no limit (`splice_price_not_convergesTo`), so the splice is not a
  logical inductor by FAF's `thm:con` (`splice_not_isLogicalInductor_of_limits_ne`); the parity
  instance and the two-inductor instance with `limitingBelief` are corollaries.
* **T1.3** *The explicit trader.* The parity trader (`Defs.lean`) exploits the parity splice with an
  explicit per-pair gain `(L₂ − L₁)/2` and a holding of at most one share
  (`paritySplice_exploited_of_limits_ne`); its net worth is computed exactly
  (`parityTrader_netWorth_odd`/`_even`), it is efficiently computable (`parityTrader_ec`, through
  FAF's single-trade constructor on a three-way dispatch by the day), and so the splice is not an
  inductor by `noExploit` (`paritySplice_not_isLogicalInductor_parityTrader`). The engine
  `parityTrader_exploits_of_pairSum` is stated for any history whose odd–even pair gains are
  nonnegative with unbounded partial sums; it serves T1.6 too.
* **T1.6 (i)** *The `o(1)` refutation at the path level.* The explicit paths
  `1/2 ∓ 1/(2(n+1))` disagree by exactly `1/(n+1)` on `φ` (and agree elsewhere), their parity
  splice converges to `1/2`, is a computable market, and is exploited by `parityTrader φ 1 0`
  (the harmonic series diverges): `splice_o1_conjecture_refuted_paths`. **(ii)** at the inductor
  level the refutation is conditional on two inductors with those paths
  (`splice_o1_conjecture_refuted_of_inductors`); their existence is OPEN (`Open.lean`).

Scope: one-way throughout (nothing reads another inductor's ledger); the exploited object is the
price path, so no statement here rests on li-projection's OPEN certificate.
-/

namespace Cleanroom.Li.LiSpliceCondition

open LogicalInduction LO.Propositional Cleanroom.Li.LiProjection Filter Topology

/-! ## T1.1 The splice and its market -/

/-- Prices of a splice lie in `[0,1]` when the components' do.
Source: mandate T1.1
Kind: L
Fidelity: exact -/
lemma splice_mem_Icc (P₁ P₂ : History) (g : ℕ → Bool)
    (h₁ : ∀ n φ, 0 ≤ P₁ n φ ∧ P₁ n φ ≤ 1) (h₂ : ∀ n φ, 0 ≤ P₂ n φ ∧ P₂ n φ ≤ 1) :
    ∀ n φ, 0 ≤ splice P₁ P₂ g n φ ∧ splice P₁ P₂ g n φ ≤ 1 := by
  intro n φ
  unfold splice
  split_ifs
  · exact h₂ n φ
  · exact h₁ n φ

/-- Prices of a splice lie in `[0,1]` at a sentence when the components' do there.
Source: mandate T1.1
Kind: L
Fidelity: exact -/
lemma splice_mem_Icc_at (P₁ P₂ : History) (g : ℕ → Bool) (φ : Sentence)
    (h₁ : ∀ n, 0 ≤ P₁ n φ ∧ P₁ n φ ≤ 1) (h₂ : ∀ n, 0 ≤ P₂ n φ ∧ P₂ n φ ≤ 1) :
    ∀ n, 0 ≤ splice P₁ P₂ g n φ ∧ splice P₁ P₂ g n φ ≤ 1 := by
  intro n
  unfold splice
  split_ifs
  · exact h₂ n
  · exact h₁ n

/-- The quote table of a market computation is computable on paired inputs.
Source: none: infrastructure (the step inside li-projection's `computableMarket_patch`)
Kind: L
Fidelity: n/a -/
lemma marketComputation_quote_computable {P : History} (M : MarketComputation P) :
    Computable fun z : ℕ => M.quote z.unpair.1 z.unpair.2 := by
  have hfst : Computable fun z : ℕ => z.unpair.1 := (Primrec.fst.comp Primrec.unpair).to_comp
  have hsnd : Computable fun z : ℕ => z.unpair.2 := (Primrec.snd.comp Primrec.unpair).to_comp
  have hin : Computable fun z : ℕ => Nat.pair z.unpair.1 z.unpair.2 :=
    Primrec₂.natPair.to_comp.comp hfst hsnd
  have heval : Partrec fun z : ℕ => M.code.eval (Nat.pair z.unpair.1 z.unpair.2) :=
    Nat.Partrec.Code.eval_part.comp (Computable.const M.code) hin
  have henc : Computable fun z : ℕ => Encodable.encode (M.quote z.unpair.1 z.unpair.2) :=
    heval.of_eq fun z => Part.eq_some_iff.mpr (by
      simpa using M.code_spec (Nat.pair z.unpair.1 z.unpair.2))
  exact Computable.encode_iff.mp henc

/-- **The splice of two computable markets along a computable selector is a computable market.**
Its quote table is the selector's choice between the two tables. (For `IsLogicalInductor` the
splice would also need `processComputable`, which the components' instances supply; the splice is
*not* an inductor when the limits differ — T1.2 — so this lemma is what makes that refutation go
through `noExploit` rather than through non-computability.)
Source: mandate T1.1
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem computableMarket_splice (P₁ P₂ : History) (g : ℕ → Bool)
    (h₁ : ComputableMarket P₁) (h₂ : ComputableMarket P₂) (hg : Computable g) :
    ComputableMarket (splice P₁ P₂ g) := by
  obtain ⟨M₁⟩ := h₁.nonemptyComputation
  obtain ⟨M₂⟩ := h₂.nonemptyComputation
  refine ComputableMarket.ofComputableTable
    (fun n c => bif g n then M₂.quote n c else M₁.quote n c) ?_ ?_ ?_
  · exact splice_mem_Icc P₁ P₂ g M₁.price_mem_Icc M₂.price_mem_Icc
  · intro n φ
    unfold splice
    cases g n
    · simp [M₁.quote_exact]
    · simp [M₂.quote_exact]
  · apply Computable.encode.comp
    have hfst : Computable fun z : ℕ => z.unpair.1 := (Primrec.fst.comp Primrec.unpair).to_comp
    exact Computable.cond (hg.comp hfst) (marketComputation_quote_computable M₂)
      (marketComputation_quote_computable M₁)

/-- The parity selector `n ↦ decide (n % 2 = 1)` is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma computable_paritySelector : Computable fun n : ℕ => decide (n % 2 = 1) :=
  (PrimrecRel.comp Primrec.eq (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
    (Primrec.const 1)).decide.to_comp

/-- The parity splice of two computable markets is a computable market.
Source: mandate T1.1
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem computableMarket_paritySplice (P₁ P₂ : History)
    (h₁ : ComputableMarket P₁) (h₂ : ComputableMarket P₂) :
    ComputableMarket (paritySplice P₁ P₂) :=
  computableMarket_splice P₁ P₂ _ h₁ h₂ computable_paritySelector

/-! ## T1.2 Non-convergence: the splice is the Convergence theorem -/

/-- **A splice of two paths with different limits has no limit.** If `P₁ n φ → L₁`, `P₂ n φ → L₂`,
`L₁ ≠ L₂`, and the selector takes each value infinitely often, the splice's price on `φ` does not
converge: along the `P₂`-days it is within `ε` of `L₂`, along the `P₁`-days within `ε` of `L₁`.
The hypothesis is on the *limits*, not on two prices at a single day (mandate trap (1)).
Source: [[corr-wf14-inventory]] 047 (`selection.md` R1.4, "any process that takes value `ℙ¹_n(φ)` infinitely often and `ℙ²_n(φ)` infinitely often has a non-convergent price")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem splice_price_not_convergesTo (P₁ P₂ : History) (g : ℕ → Bool) (φ : Sentence) (L₁ L₂ : ℝ)
    (h₁ : Tendsto (fun n => P₁ n φ) atTop (𝓝 L₁)) (h₂ : Tendsto (fun n => P₂ n φ) atTop (𝓝 L₂))
    (hne : L₁ ≠ L₂) (hg₁ : ∃ᶠ n in atTop, g n = false) (hg₂ : ∃ᶠ n in atTop, g n = true) :
    ¬ ∃ L, ConvergesTo (fun n => splice P₁ P₂ g n φ) L := by
  rintro ⟨L, hL⟩
  have hD : 0 < |L₁ - L₂| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hε : 0 < |L₁ - L₂| / 4 := by positivity
  have hL' : ∀ᶠ n in atTop, |splice P₁ P₂ g n φ - L| < |L₁ - L₂| / 4 := by
    simpa [Real.dist_eq] using Metric.tendsto_nhds.mp hL _ hε
  have h₁' : ∀ᶠ n in atTop, |P₁ n φ - L₁| < |L₁ - L₂| / 4 := by
    simpa [Real.dist_eq] using Metric.tendsto_nhds.mp h₁ _ hε
  have h₂' : ∀ᶠ n in atTop, |P₂ n φ - L₂| < |L₁ - L₂| / 4 := by
    simpa [Real.dist_eq] using Metric.tendsto_nhds.mp h₂ _ hε
  obtain ⟨n, hgn, hSn, hPn⟩ := (hg₂.and_eventually (hL'.and h₂')).exists
  obtain ⟨m, hgm, hSm, hPm⟩ := (hg₁.and_eventually (hL'.and h₁')).exists
  rw [splice_apply, if_pos hgn] at hSn
  rw [splice_apply, if_neg (by simp [hgm])] at hSm
  rw [abs_lt] at hSn hPn hSm hPm
  have : |L₁ - L₂| < |L₁ - L₂| := abs_lt.mpr ⟨by linarith, by linarith⟩
  exact lt_irrefl _ this

/-- **The splice is not a logical inductor (the Convergence-theorem reading).** Two price paths
with different limits on `φ`, spliced along a selector that takes each value infinitely often —
the source's "adaptive alternation" — give a market whose price on `φ` does not converge, which
FAF's `thm:con` (`lic_price_convergesTo`) forbids for an inductor. No trader is named here; the
certificate-free route of the mandate (FAF's `hystTrader` sits inside `lic_price_convergesTo`).
`¬ IsLogicalInductor` is also true for a non-computable `DP` (the criterion requires
`processComputable`); the content here is the exploitation route (`thm:con`'s trader), and the
`Exploits` conclusion with no such escape is `paritySplice_exploited_of_limits_ne`, instantiated
over the computable `paperDP 𝗜𝚺₁`.
Source: [[corr-wf14-inventory]] 047 (`selection.md` R1.4 "the LI splice is the Convergence theorem, not a selection result"); [[corr-wf13-inventory]] 062 (`positive/li.md` I14.4)
Kind: C
Fidelity: exact; stronger: any selector with both values frequent, not only the daily alternation
Hyps: (a) -/
theorem splice_not_isLogicalInductor_of_limits_ne (P₁ P₂ : History) (g : ℕ → Bool)
    (DP : DeductiveProcess) (φ : Sentence) (L₁ L₂ : ℝ)
    (h₁ : Tendsto (fun n => P₁ n φ) atTop (𝓝 L₁)) (h₂ : Tendsto (fun n => P₂ n φ) atTop (𝓝 L₂))
    (hne : L₁ ≠ L₂) (hg₁ : ∃ᶠ n in atTop, g n = false) (hg₂ : ∃ᶠ n in atTop, g n = true)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ¬ IsLogicalInductor (splice P₁ P₂ g) DP := by
  intro hLI
  exact splice_price_not_convergesTo P₁ P₂ g φ L₁ L₂ h₁ h₂ hne hg₁ hg₂
    (lic_price_convergesTo (splice P₁ P₂ g) DP (hLI := hLI) φ hcons)

/-- Even days are frequent for the parity selector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma frequently_paritySelector_false : ∃ᶠ n in atTop, (decide (n % 2 = 1)) = false :=
  Filter.frequently_atTop.mpr fun a => ⟨2 * a, by omega, by
    simp only [decide_eq_false_iff_not]; omega⟩

/-- Odd days are frequent for the parity selector.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma frequently_paritySelector_true : ∃ᶠ n in atTop, (decide (n % 2 = 1)) = true :=
  Filter.frequently_atTop.mpr fun a => ⟨2 * a + 1, by omega, by
    simp only [decide_eq_true_eq]; omega⟩

/-- The parity splice of two paths with different limits on `φ` is not a logical inductor. (As for
`splice_not_isLogicalInductor_of_limits_ne`: trivially true for a non-computable `DP`; the content
is the exploitation, `paritySplice_exploited_of_limits_ne`.)
Source: [[corr-wf13-inventory]] 062 (`positive/li.md` I14.4, the daily splice)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem paritySplice_not_isLogicalInductor_of_limits_ne (P₁ P₂ : History)
    (DP : DeductiveProcess) (φ : Sentence) (L₁ L₂ : ℝ)
    (h₁ : Tendsto (fun n => P₁ n φ) atTop (𝓝 L₁)) (h₂ : Tendsto (fun n => P₂ n φ) atTop (𝓝 L₂))
    (hne : L₁ ≠ L₂) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ¬ IsLogicalInductor (paritySplice P₁ P₂) DP :=
  splice_not_isLogicalInductor_of_limits_ne P₁ P₂ _ DP φ L₁ L₂ h₁ h₂ hne
    frequently_paritySelector_false frequently_paritySelector_true hcons

/-- **Two inductors, different limiting beliefs: no splice of them is an inductor.** The limits
are *derived* from the components' criterion (`lic_limitingBelief_tendsto`), not assumed; the
hypothesis is `limitingBelief P₁ φ ≠ limitingBelief P₂ φ`. Any selector with both values frequent.
Here `DP` is computable (the components are inductors over it), so the conclusion is not the
non-computability escape; it is carried by `thm:con`'s trader.
Source: [[corr-wf14-inventory]] 047 (`selection.md` R1.4); [[corr-wf13-inventory]] 062 ("estimator switching breaks reflection")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem splice_not_isLogicalInductor_of_limitingBelief_ne (P₁ P₂ : History) (g : ℕ → Bool)
    (DP : DeductiveProcess) [IsLogicalInductor P₁ DP] [IsLogicalInductor P₂ DP]
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (φ : Sentence)
    (hne : limitingBelief P₁ φ ≠ limitingBelief P₂ φ)
    (hg₁ : ∃ᶠ n in atTop, g n = false) (hg₂ : ∃ᶠ n in atTop, g n = true) :
    ¬ IsLogicalInductor (splice P₁ P₂ g) DP :=
  splice_not_isLogicalInductor_of_limits_ne P₁ P₂ g DP φ _ _
    (lic_limitingBelief_tendsto P₁ DP hcons φ) (lic_limitingBelief_tendsto P₂ DP hcons φ)
    hne hg₁ hg₂ hcons

/-- The daily alternation of two inductors with different limiting beliefs on `φ` is not an
inductor (`DP` computable, as for `splice_not_isLogicalInductor_of_limitingBelief_ne`).
Source: [[corr-wf13-inventory]] 062 (`positive/li.md` I14.4)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem paritySplice_not_isLogicalInductor_of_limitingBelief_ne (P₁ P₂ : History)
    (DP : DeductiveProcess) [IsLogicalInductor P₁ DP] [IsLogicalInductor P₂ DP]
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (φ : Sentence)
    (hne : limitingBelief P₁ φ ≠ limitingBelief P₂ φ) :
    ¬ IsLogicalInductor (paritySplice P₁ P₂) DP :=
  splice_not_isLogicalInductor_of_limitingBelief_ne P₁ P₂ _ DP hcons φ hne
    frequently_paritySelector_false frequently_paritySelector_true

/-! ## T1.3 The parity trader: net worth, exactly -/

/-- `parityCoeff` before the start day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma parityCoeff_of_lt (s : ℚ) {M n : ℕ} (h : n < 2 * M) : parityCoeff s M n = 0 := by
  simp [parityCoeff, h]

/-- `parityCoeff` on an even day from the start day on.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma parityCoeff_of_even (s : ℚ) {M n : ℕ} (hM : 2 * M ≤ n) (h2 : n % 2 = 0) :
    parityCoeff s M n = s := by
  simp [parityCoeff, not_lt.mpr hM, h2]

/-- `parityCoeff` on an odd day from the start day on.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma parityCoeff_of_odd (s : ℚ) {M n : ℕ} (hM : 2 * M ≤ n) (h2 : n % 2 = 1) :
    parityCoeff s M n = -s := by
  simp [parityCoeff, not_lt.mpr hM, h2]

/-- The day-`n` value of the parity trader: `c_n · (payout φ − S_n(φ))`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma parityTrader_value (φ : Sentence) (s : ℚ) (M : ℕ) (S : History) (w : Sentence → ℝ) (n : ℕ) :
    ((parityTrader φ s M).strat n).value S w = (parityCoeff s M n : ℝ) * (w φ - S n φ) := by
  simp [parityTrader, Strategy.value]

/-- The parity trader's net worth is the sum of its daily values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma parityTrader_netWorth (φ : Sentence) (s : ℚ) (M : ℕ) (S : History) (v : PCWorld) (n : ℕ) :
    (parityTrader φ s M).netWorth S v n =
      ∑ i ∈ Finset.range (n + 1), (parityCoeff s M i : ℝ) * (v.payout φ - S i φ) := by
  unfold Trader.netWorth
  exact Finset.sum_congr rfl fun i _ => parityTrader_value φ s M S v.payout i

/-- The **pair sum** `Σ_{k = M}^{m} (S_{2k+1}(φ) − S_{2k}(φ))`: the cash the parity trader banks
on the completed buy–sell pairs up to day `2m+1` (world-independent).
Source: [[corr-wf14-inventory]] 047 (`selection_checks.py` C5, "cash ≈ 0.2 per pair")
Kind: D
Fidelity: exact -/
noncomputable def pairSum (S : History) (φ : Sentence) (M m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico M (m + 1), (S (2 * k + 1) φ - S (2 * k) φ)

/-- The pair sum before the start index is empty.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pairSum_of_lt (S : History) (φ : Sentence) {M m : ℕ} (h : m + 1 ≤ M) :
    pairSum S φ M m = 0 := by
  unfold pairSum
  rw [Finset.Ico_eq_empty_of_le h, Finset.sum_empty]

/-- The pair sum grows by one pair.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pairSum_succ (S : History) (φ : Sentence) {M m : ℕ} (h : M ≤ m + 1) :
    pairSum S φ M (m + 1) = pairSum S φ M m + (S (2 * (m + 1) + 1) φ - S (2 * (m + 1)) φ) := by
  unfold pairSum
  rw [Finset.sum_Ico_succ_top h]

/-- **Net worth on an odd day is `s` times the pair sum**, in every world: the holding is closed.
Source: mandate T1.3 ("per even/odd pair the cash gain")
Kind: P
Fidelity: exact
Hyps: (a) -/
lemma parityTrader_netWorth_odd (φ : Sentence) (s : ℚ) (M : ℕ) (S : History) (v : PCWorld) :
    ∀ m : ℕ, (parityTrader φ s M).netWorth S v (2 * m + 1) = (s : ℝ) * pairSum S φ M m := by
  intro m
  induction m with
  | zero =>
      rw [parityTrader_netWorth]
      simp only [Nat.mul_zero, zero_add, Finset.sum_range_succ, Finset.sum_range_zero]
      rcases Nat.eq_zero_or_pos M with hM | hM
      · subst hM
        rw [parityCoeff_of_even s (by omega) (by omega), parityCoeff_of_odd s (by omega) (by omega)]
        unfold pairSum
        rw [Nat.Ico_zero_eq_range, Finset.sum_range_succ, Finset.sum_range_zero]
        simp only [Nat.mul_zero, zero_add]
        push_cast; ring
      · rw [parityCoeff_of_lt s (by omega), parityCoeff_of_lt s (by omega), pairSum_of_lt S φ hM]
        simp
  | succ m ih =>
      rw [parityTrader_netWorth, Finset.sum_range_succ, Finset.sum_range_succ,
        show 2 * (m + 1) = 2 * m + 1 + 1 by ring, ← parityTrader_netWorth, ih]
      by_cases hM : M ≤ m + 1
      · rw [parityCoeff_of_even s (n := 2 * m + 1 + 1) (by omega) (by omega),
          parityCoeff_of_odd s (n := 2 * m + 1 + 1 + 1) (by omega) (by omega),
          pairSum_succ S φ hM, show 2 * (m + 1) = 2 * m + 1 + 1 by ring]
        push_cast; ring
      · rw [not_le] at hM
        rw [parityCoeff_of_lt s (n := 2 * m + 1 + 1) (by omega),
          parityCoeff_of_lt s (n := 2 * m + 1 + 1 + 1) (by omega),
          pairSum_of_lt S φ (by omega), pairSum_of_lt S φ (by omega)]
        simp

/-- **Net worth on an even day**: the pair sum plus the one open position (bought that day).
Source: mandate T1.3 ("the holding is `≤ 1` share")
Kind: P
Fidelity: exact
Hyps: (a) -/
lemma parityTrader_netWorth_even (φ : Sentence) (s : ℚ) (M : ℕ) (S : History) (v : PCWorld)
    (m : ℕ) :
    (parityTrader φ s M).netWorth S v (2 * m) =
      (s : ℝ) * pairSum S φ M m + (if M ≤ m then (s : ℝ) * (v.payout φ - S (2 * m + 1) φ) else 0) := by
  have h := parityTrader_netWorth_odd φ s M S v m
  rw [parityTrader_netWorth, Finset.sum_range_succ, ← parityTrader_netWorth] at h
  by_cases hM : M ≤ m
  · rw [parityCoeff_of_odd s (n := 2 * m + 1) (by omega) (by omega)] at h
    rw [if_pos hM]
    push_cast at h
    linarith
  · rw [parityCoeff_of_lt s (n := 2 * m + 1) (by omega)] at h
    rw [if_neg hM]
    push_cast at h
    linarith

/-- Nonnegative oriented pair gains give a nonnegative oriented pair sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pairSum_nonneg (S : History) (φ : Sentence) (s : ℚ) (M : ℕ)
    (hgain : ∀ k, M ≤ k → 0 ≤ (s : ℝ) * (S (2 * k + 1) φ - S (2 * k) φ)) (m : ℕ) :
    0 ≤ (s : ℝ) * pairSum S φ M m := by
  unfold pairSum
  rw [Finset.mul_sum]
  exact Finset.sum_nonneg fun k hk => hgain k (Finset.mem_Ico.mp hk).1

/-- A uniform oriented pair gain `d` gives the pair sum at least `(m + 1 − M) · d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pairSum_ge (S : History) (φ : Sentence) (s : ℚ) (M : ℕ) (d : ℝ)
    (hgain : ∀ k, M ≤ k → d ≤ (s : ℝ) * (S (2 * k + 1) φ - S (2 * k) φ)) (m : ℕ) :
    ((m + 1 - M : ℕ) : ℝ) * d ≤ (s : ℝ) * pairSum S φ M m := by
  unfold pairSum
  rw [Finset.mul_sum]
  calc ((m + 1 - M : ℕ) : ℝ) * d = ∑ _k ∈ Finset.Ico M (m + 1), d := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ ∑ k ∈ Finset.Ico M (m + 1), (s : ℝ) * (S (2 * k + 1) φ - S (2 * k) φ) :=
        Finset.sum_le_sum fun k hk => hgain k (Finset.mem_Ico.mp hk).1

/-- **The exploitation engine.** For `s ∈ {1, −1}`, a history with prices in `[0,1]` on `φ` whose
oriented pair gains `s · (S_{2k+1}(φ) − S_{2k}(φ))` are nonnegative from `k = M` on and whose
oriented pair sums are unbounded, is exploited by `parityTrader φ s M`: the plausible value is
`≥ −1` on every day in every world (one share at most, prices and payouts in `[0,1]`), and on odd
days it is the pair sum, which exceeds every bound. The lower bound is proved on *every* world
consistent with `DP.D n`, every `n` (mandate trap (3)); the upper bound uses one consistent world
per day (`hcons`).
Source: mandate T1.3 (the explicit gain and the `≤ 1` holding); [[corr-wf14-inventory]] 047–048
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem parityTrader_exploits_of_pairSum (S : History) (DP : DeductiveProcess) (φ : Sentence)
    (s : ℚ) (hs : s = 1 ∨ s = -1) (M : ℕ) (hb : ∀ n, 0 ≤ S n φ ∧ S n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hgain : ∀ k, M ≤ k → 0 ≤ (s : ℝ) * (S (2 * k + 1) φ - S (2 * k) φ))
    (hunb : ∀ B : ℝ, ∃ m, B < (s : ℝ) * pairSum S φ M m) :
    (parityTrader φ s M).Exploits S DP := by
  apply exploits_of_bddBelow_of_unbounded _ S DP 1
  · rintro x ⟨n, v, -, rfl⟩
    obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' n
    · subst hm
      rw [parityTrader_netWorth_even]
      have hps := pairSum_nonneg S φ s M hgain m
      have hw := payout_mem_Icc v φ
      have hS := hb (2 * m + 1)
      rcases hs with rfl | rfl
      · simp only [Rat.cast_one] at hps ⊢
        split_ifs <;> linarith
      · simp only [Rat.cast_neg, Rat.cast_one] at hps ⊢
        split_ifs <;> linarith
    · subst hm
      rw [parityTrader_netWorth_odd]
      linarith [pairSum_nonneg S φ s M hgain m]
  · intro B
    obtain ⟨m, hm⟩ := hunb B
    obtain ⟨v, hv⟩ := hcons (2 * m + 1)
    exact ⟨_, ⟨2 * m + 1, v, hv, rfl⟩, by rw [parityTrader_netWorth_odd]; exact hm⟩

/-- **Exploitation from a uniform per-pair gain `d > 0`.**
Source: mandate T1.3
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem parityTrader_exploits_of_gain (S : History) (DP : DeductiveProcess) (φ : Sentence)
    (s : ℚ) (hs : s = 1 ∨ s = -1) (M : ℕ) (hb : ∀ n, 0 ≤ S n φ ∧ S n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (d : ℝ) (hd : 0 < d)
    (hgain : ∀ k, M ≤ k → d ≤ (s : ℝ) * (S (2 * k + 1) φ - S (2 * k) φ)) :
    (parityTrader φ s M).Exploits S DP := by
  refine parityTrader_exploits_of_pairSum S DP φ s hs M hb hcons
    (fun k hk => le_trans hd.le (hgain k hk)) ?_
  intro B
  obtain ⟨K, hK⟩ := exists_nat_gt (B / d)
  refine ⟨M + K, ?_⟩
  have h := pairSum_ge S φ s M d hgain (M + K)
  have hcard : ((M + K + 1 - M : ℕ) : ℝ) = (K : ℝ) + 1 := by
    rw [show M + K + 1 - M = K + 1 by omega]; push_cast; ring
  rw [hcard] at h
  have hBK : B < (K : ℝ) * d := by rwa [div_lt_iff₀ hd] at hK
  nlinarith

/-! ## T1.3 From the limits: the explicit gain -/

/-- **The parity trader exploits the parity splice of two paths with different limits**, with the
explicit per-pair gain `|L₁ − L₂| / 2` from some pair index `M` on and a holding of at most one
share. For `L₁ < L₂` the trader buys on even days (`s = 1`); for `L₂ < L₁` it sells first
(`s = −1`). `M` is the day from which `P₁` is within `|L₁ − L₂|/4` of `L₁` and `P₂` within
`|L₁ − L₂|/4` of `L₂`; the source's numerically observed "cash ≈ 0.2 per pair" is this exact bound
at its limits (`(0.7 − 0.3)/2 = 0.2`). The holding is `≤ 1` share, so the plausible value is
`≥ −1` in every world (`parityTrader_exploits_of_pairSum`).
Source: [[corr-wf14-inventory]] 047 (`selection.md` R1.4 and `selection_checks.py` C5); mandate T1.3
Kind: P
Fidelity: exact; the per-pair gain is stated as an exact bound, not a decimal (plan §0.4 rule 4)
Hyps: (a) -/
theorem paritySplice_exploited_of_limits_ne (P₁ P₂ : History) (DP : DeductiveProcess)
    (φ : Sentence) (hb₁ : ∀ n, 0 ≤ P₁ n φ ∧ P₁ n φ ≤ 1) (hb₂ : ∀ n, 0 ≤ P₂ n φ ∧ P₂ n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (L₁ L₂ : ℝ)
    (h₁ : Tendsto (fun n => P₁ n φ) atTop (𝓝 L₁)) (h₂ : Tendsto (fun n => P₂ n φ) atTop (𝓝 L₂))
    (hne : L₁ ≠ L₂) :
    ∃ (s : ℚ) (M : ℕ), (s = 1 ∨ s = -1) ∧
      (∀ k, M ≤ k → |L₁ - L₂| / 2 ≤
        (s : ℝ) * (paritySplice P₁ P₂ (2 * k + 1) φ - paritySplice P₁ P₂ (2 * k) φ)) ∧
      (parityTrader φ s M).Exploits (paritySplice P₁ P₂) DP := by
  have hD : 0 < |L₁ - L₂| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hδ : 0 < |L₁ - L₂| / 4 := by positivity
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp h₁ _ hδ)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp h₂ _ hδ)
  have hbS : ∀ n, 0 ≤ paritySplice P₁ P₂ n φ ∧ paritySplice P₁ P₂ n φ ≤ 1 :=
    splice_mem_Icc_at P₁ P₂ _ φ hb₁ hb₂
  have key : ∀ k, max N₁ N₂ ≤ k →
      |P₁ (2 * k) φ - L₁| < |L₁ - L₂| / 4 ∧ |P₂ (2 * k + 1) φ - L₂| < |L₁ - L₂| / 4 := by
    intro k hk
    have a := hN₁ (2 * k) (by have := le_trans (le_max_left N₁ N₂) hk; omega)
    have b := hN₂ (2 * k + 1) (by have := le_trans (le_max_right N₁ N₂) hk; omega)
    rw [Real.dist_eq] at a b
    exact ⟨a, b⟩
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have habs : |L₁ - L₂| = L₂ - L₁ := by rw [abs_sub_comm]; exact abs_of_pos (by linarith)
    have hgain : ∀ k, max N₁ N₂ ≤ k → |L₁ - L₂| / 2 ≤
        ((1 : ℚ) : ℝ) * (paritySplice P₁ P₂ (2 * k + 1) φ - paritySplice P₁ P₂ (2 * k) φ) := by
      intro k hk
      obtain ⟨a, b⟩ := key k hk
      rw [paritySplice_odd, paritySplice_even, Rat.cast_one, one_mul, habs]
      rw [habs, abs_lt] at a b
      linarith
    exact ⟨1, max N₁ N₂, Or.inl rfl, hgain,
      parityTrader_exploits_of_gain _ DP φ 1 (Or.inl rfl) _ hbS hcons _ (by positivity) hgain⟩
  · have habs : |L₁ - L₂| = L₁ - L₂ := abs_of_pos (by linarith)
    have hgain : ∀ k, max N₁ N₂ ≤ k → |L₁ - L₂| / 2 ≤
        ((-1 : ℚ) : ℝ) * (paritySplice P₁ P₂ (2 * k + 1) φ - paritySplice P₁ P₂ (2 * k) φ) := by
      intro k hk
      obtain ⟨a, b⟩ := key k hk
      rw [paritySplice_odd, paritySplice_even, Rat.cast_neg, Rat.cast_one, habs]
      rw [habs, abs_lt] at a b
      linarith
    exact ⟨-1, max N₁ N₂, Or.inr rfl, hgain,
      parityTrader_exploits_of_gain _ DP φ (-1) (Or.inr rfl) _ hbS hcons _ (by positivity) hgain⟩

/-! ## T1.3 The efficiency certificate -/

/-- The parity ruler `n ↦ n % 2` is a unary ruler (FAF's `divmodc_polyFueled` at `2`, second
component).
Source: none: infrastructure (mandate `Defs` table: "a parity ruler built as `modDispatch` builds its `% k`")
Kind: L
Fidelity: n/a -/
lemma unaryRuler_mod_two : UnaryRuler (fun n => n % 2) := by
  obtain ⟨c, hc⟩ := divmodc_polyFueled 2 (by norm_num)
  exact UnaryRuler.of_polyFueled ((PolyFueled.right.comp hc).of_eq (fun n => by simp))

/-- **The parity trader is efficiently computable**: FAF's single-trade constructor
(`EfficientlyComputable.ofSingleTradeBlocksBig`) on the constant sentence `φ` and the coefficient
stream `(EF.const (parityCoeff s M n)).serialize`, a three-way dispatch by the day — "before `2M`"
(`UnaryRuler.ite_lt_const`) and then parity (`unaryRuler_mod_two`) — each branch a constant word
(`MachineTokenStream.ifZero`, `.const`). The coefficients are price-free (mandate trap (4)).
Source: mandate `Defs` table (`parityTrader`, "e.c. by `EfficientlyComputable.ofSingleTradeBlocksBig` with `MachineTokenStream.ifZero`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem parityTrader_ec (φ : Sentence) (s : ℚ) (M : ℕ) :
    EfficientlyComputable (parityTrader φ s M) := by
  refine EfficientlyComputable.ofSingleTradeBlocksBig _ (fun n => EF.const (parityCoeff s M n))
    (fun _ => φ) ?_ (fun _ => trivial) (MachineSentenceCodes.const φ) (fun _ => rfl)
  have h0 := MachineTokenStream.const (EF.const 0).serialize
  have h1 := MachineTokenStream.const (EF.const s).serialize
  have h2 := MachineTokenStream.const (EF.const (-s)).serialize
  have hin := MachineTokenStream.ifZero h1 h2 unaryRuler_mod_two
  have hout := MachineTokenStream.ifZero h0 hin (UnaryRuler.ite_lt_const (2 * M) 0 1)
  refine hout.of_eq (fun n => ?_)
  simp only [parityCoeff]
  by_cases hlt : n < 2 * M
  · simp [hlt]
  · by_cases h2 : n % 2 = 0 <;> simp [hlt, h2]

/-- **The parity splice is not a logical inductor — by the named trader.** Same conclusion as
`paritySplice_not_isLogicalInductor_of_limits_ne` (T1.2, through `thm:con` and FAF's `hystTrader`),
now through `noExploit` at the explicit `parityTrader` with its explicit gain and certificate. The
components are computable markets so that the splice is one too (`computableMarket_paritySplice`):
the refutation is not an artefact of the *market's* non-computability (mandate trap (2)). No
`ComputableDeductiveProcess DP` is carried, so for a non-computable `DP` the `¬ IsLogicalInductor`
conjunct is true for the wrong reason; the content is the `Exploits` conjunct of
`paritySplice_exploited_of_limits_ne`, through which this proof goes (`Exploits` is refutable:
the trader does not exploit a constant-price history, adversarial audit r1 probe `Vacuity.lean`),
and the N+ instance is over the computable `paperDP 𝗜𝚺₁`.
Source: [[corr-wf14-inventory]] 047; [[corr-wf13-inventory]] 062; mandate T1.3 (`splice_not_isLogicalInductor`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem paritySplice_not_isLogicalInductor_parityTrader (P₁ P₂ : History) (DP : DeductiveProcess)
    (φ : Sentence) (hc₁ : ComputableMarket P₁) (hc₂ : ComputableMarket P₂)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (L₁ L₂ : ℝ)
    (h₁ : Tendsto (fun n => P₁ n φ) atTop (𝓝 L₁)) (h₂ : Tendsto (fun n => P₂ n φ) atTop (𝓝 L₂))
    (hne : L₁ ≠ L₂) :
    ComputableMarket (paritySplice P₁ P₂) ∧ ¬ IsLogicalInductor (paritySplice P₁ P₂) DP := by
  refine ⟨computableMarket_paritySplice P₁ P₂ hc₁ hc₂, fun hLI => ?_⟩
  obtain ⟨s, M, -, -, hex⟩ := paritySplice_exploited_of_limits_ne P₁ P₂ DP φ
    (fun n => hc₁.1 n φ) (fun n => hc₂.1 n φ) hcons L₁ L₂ h₁ h₂ hne
  exact hLI.noExploit _ (parityTrader_ec φ s M) hex

/-! ## T1.6 (i) The `o(1)` conjecture, refuted at the path level -/

/-- The low harmonic path: `1/2 − 1/(2(n+1))` on `φ`, `1/2` elsewhere.
Source: [[corr-wf14-inventory]] 048 (`selection.md` R1.5, "`ℙ¹_n(φ) = L − 1/n`"); mandate T1.6(i)
Kind: D
Fidelity: variant: `L = 1/2`, offset `1/(2(n+1))` (prices in `[0,1]` from day `0`; the disagreement `|ℙ¹ − ℙ²| = 1/(n+1)` is the source's) -/
noncomputable def harmonicLow (φ : Sentence) : History :=
  fun n χ => if χ = φ then 1 / 2 - 1 / (2 * ((n : ℝ) + 1)) else 1 / 2

/-- The high harmonic path: `1/2 + 1/(2(n+1))` on `φ`, `1/2` elsewhere.
Source: [[corr-wf14-inventory]] 048 (`selection.md` R1.5, "`ℙ²_n(φ) = L + 1/n`"); mandate T1.6(i)
Kind: D
Fidelity: variant: as `harmonicLow` -/
noncomputable def harmonicHigh (φ : Sentence) : History :=
  fun n χ => if χ = φ then 1 / 2 + 1 / (2 * ((n : ℝ) + 1)) else 1 / 2

/-- `harmonicLow` at `φ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma harmonicLow_apply (φ : Sentence) (n : ℕ) :
    harmonicLow φ n φ = 1 / 2 - 1 / (2 * ((n : ℝ) + 1)) := by simp [harmonicLow]

/-- `harmonicHigh` at `φ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma harmonicHigh_apply (φ : Sentence) (n : ℕ) :
    harmonicHigh φ n φ = 1 / 2 + 1 / (2 * ((n : ℝ) + 1)) := by simp [harmonicHigh]

/-- The offset `1/(2(n+1))` lies in `(0, 1/2]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma harmonicOffset_bounds (n : ℕ) :
    0 < 1 / (2 * ((n : ℝ) + 1)) ∧ 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · positivity
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith

/-- Both harmonic paths price every sentence in `[0,1]`.
Source: mandate T1.6(i) ("prices clipped nowhere")
Kind: L
Fidelity: exact -/
lemma harmonic_mem_Icc (φ : Sentence) :
    (∀ n χ, 0 ≤ harmonicLow φ n χ ∧ harmonicLow φ n χ ≤ 1) ∧
    (∀ n χ, 0 ≤ harmonicHigh φ n χ ∧ harmonicHigh φ n χ ≤ 1) := by
  constructor <;> intro n χ <;> obtain ⟨h0, h1⟩ := harmonicOffset_bounds n <;>
    simp only [harmonicLow, harmonicHigh] <;> split_ifs <;> constructor <;> linarith

/-- **The two paths disagree by exactly `1/(n+1)` on `φ` and agree elsewhere**: `o(1)` agreement
on every sentence sequence whatsoever.
Source: [[corr-wf14-inventory]] 048 (R1.5, "agreement to `o(1)`")
Kind: L
Fidelity: exact
Hyps: (a) -/
lemma harmonic_disagreement (φ : Sentence) (n : ℕ) (χ : Sentence) :
    |harmonicLow φ n χ - harmonicHigh φ n χ| ≤ 1 / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold harmonicLow harmonicHigh
  split_ifs
  · rw [show (1 / 2 - 1 / (2 * ((n : ℝ) + 1))) - (1 / 2 + 1 / (2 * ((n : ℝ) + 1))) =
      -(1 / ((n : ℝ) + 1)) by field_simp; ring]
    rw [abs_neg, abs_of_pos (by positivity)]
  · rw [sub_self, abs_zero]
    positivity

/-- The offset tends to `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma harmonicOffset_tendsto : Tendsto (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 2 : ℝ)
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  field_simp

/-- Both harmonic paths converge to `1/2` on `φ`.
Source: mandate T1.6(i)
Kind: L
Fidelity: exact -/
lemma harmonic_tendsto (φ : Sentence) :
    Tendsto (fun n => harmonicLow φ n φ) atTop (𝓝 (1 / 2)) ∧
    Tendsto (fun n => harmonicHigh φ n φ) atTop (𝓝 (1 / 2)) := by
  constructor
  · simp only [harmonicLow_apply]
    simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub harmonicOffset_tendsto
  · simp only [harmonicHigh_apply]
    simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).add harmonicOffset_tendsto

/-- **The parity splice of the harmonic paths converges to `1/2`** (squeezed between the two paths).
Source: [[corr-wf14-inventory]] 048 (R1.5, "the alternating splice converges to `L`")
Kind: P
Fidelity: exact
Hyps: (a) -/
lemma paritySplice_harmonic_tendsto (φ : Sentence) :
    Tendsto (fun n => paritySplice (harmonicLow φ) (harmonicHigh φ) n φ) atTop (𝓝 (1 / 2)) := by
  obtain ⟨hlo, hhi⟩ := harmonic_tendsto φ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi ?_ ?_
  · intro n
    simp only [paritySplice, splice, harmonicLow_apply, harmonicHigh_apply]
    split_ifs <;> linarith [(harmonicOffset_bounds n).1]
  · intro n
    simp only [paritySplice, splice, harmonicLow_apply, harmonicHigh_apply]
    split_ifs <;> linarith [(harmonicOffset_bounds n).1]

/-- Each harmonic pair gain is at least `1/(2(k+1))`: `1/(2(2k+2)) + 1/(2(2k+1)) ≥ 1/(2k+2)`.
Source: [[corr-wf14-inventory]] 048 (R1.5, "banks `≈ 2/n` per pair")
Kind: L
Fidelity: exact -/
lemma harmonic_pairGain (φ : Sentence) (k : ℕ) :
    1 / (2 * ((k : ℝ) + 1)) ≤
      paritySplice (harmonicLow φ) (harmonicHigh φ) (2 * k + 1) φ -
        paritySplice (harmonicLow φ) (harmonicHigh φ) (2 * k) φ := by
  rw [paritySplice_odd, paritySplice_even, harmonicHigh_apply, harmonicLow_apply]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  push_cast
  have h1 : 1 / (2 * ((k : ℝ) + 1)) ≤ 1 / (2 * (2 * (k : ℝ) + 1 + 1)) + 1 / (2 * (2 * (k : ℝ) + 1)) := by
    have a : 1 / (2 * (2 * (k : ℝ) + 1 + 1)) ≤ 1 / (2 * (2 * (k : ℝ) + 1)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have b : 1 / (2 * ((k : ℝ) + 1)) = 2 * (1 / (2 * (2 * (k : ℝ) + 1 + 1))) := by
      field_simp; ring
    linarith
  linarith

/-- The harmonic quote table is computable (FAF's `Primrec` calculus on `ℚ`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma harmonicTable_computable (φ : Sentence) (sign : ℚ) :
    Computable fun z : ℕ => Encodable.encode
      (if z.unpair.2 = Encodable.encode φ then (1 / 2 : ℚ) + sign / (2 * ((z.unpair.1 : ℚ) + 1))
        else (1 / 2 : ℚ)) := by
  have hn : Primrec fun z : ℕ => ((z.unpair.1 : ℕ) : ℚ) :=
    ratNatCast_prim.comp (Primrec.fst.comp Primrec.unpair)
  have hden : Primrec fun z : ℕ => (2 : ℚ) * ((z.unpair.1 : ℚ) + 1) :=
    ratMul_prim.comp (Primrec.const 2) (ratAdd_prim.comp hn (Primrec.const 1))
  have hfrac : Primrec fun z : ℕ => sign / (2 * ((z.unpair.1 : ℚ) + 1)) :=
    ratDiv_prim.comp (Primrec.const sign) hden
  have hval : Primrec fun z : ℕ => (1 / 2 : ℚ) + sign / (2 * ((z.unpair.1 : ℚ) + 1)) :=
    ratAdd_prim.comp (Primrec.const (1 / 2)) hfrac
  have htest : PrimrecPred fun z : ℕ => z.unpair.2 = Encodable.encode φ :=
    PrimrecRel.comp Primrec.eq (Primrec.snd.comp Primrec.unpair) (Primrec.const _)
  exact (Primrec.encode.comp (Primrec.ite htest hval (Primrec.const (1 / 2)))).to_comp

/-- Both harmonic paths are computable markets.
Source: mandate T1.6(i) (the explicit history)
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma computableMarket_harmonic (φ : Sentence) :
    ComputableMarket (harmonicLow φ) ∧ ComputableMarket (harmonicHigh φ) := by
  obtain ⟨hlo, hhi⟩ := harmonic_mem_Icc φ
  constructor
  · refine ComputableMarket.ofComputableTable
      (fun n c => if c = Encodable.encode φ then (1 / 2 : ℚ) + (-1) / (2 * ((n : ℚ) + 1)) else 1 / 2)
      hlo ?_ (harmonicTable_computable φ (-1))
    intro n χ
    unfold harmonicLow
    by_cases h : χ = φ
    · subst h; rw [if_pos rfl, if_pos rfl]; push_cast; ring
    · rw [if_neg h, if_neg (fun h' => h (Encodable.encode_injective h'))]; norm_num
  · refine ComputableMarket.ofComputableTable
      (fun n c => if c = Encodable.encode φ then (1 / 2 : ℚ) + 1 / (2 * ((n : ℚ) + 1)) else 1 / 2)
      hhi ?_ (harmonicTable_computable φ 1)
    intro n χ
    unfold harmonicHigh
    by_cases h : χ = φ
    · subst h; rw [if_pos rfl, if_pos rfl]; push_cast; ring
    · rw [if_neg h, if_neg (fun h' => h (Encodable.encode_injective h'))]; norm_num

/-- **Run 1's `o(1)` conjecture is refuted at the level the source argued it — price paths.** The
two explicit paths `1/2 ∓ 1/(2(n+1))` (i) price every sentence in `[0,1]`, (ii) disagree by at
most `1/(n+1)` on *every* sentence (agreement to `o(1)` along every sequence), (iii) each converge
to `1/2` on `φ`, (iv) have a parity splice converging to `1/2` on `φ` which (v) is a computable
market and (vi) is exploited by `parityTrader φ 1 0` (buy on even days, sell on odd, from day `0`):
each pair banks at least `1/(2(k+1))`, the harmonic series diverges, and the holding is at most
one share. **Not claimed:** anything about inductors — the two paths are not inductors (they are
constant off `φ`), and the inductor-level statement is `splice_o1_conjecture_refuted_of_inductors`,
conditional on the OPEN existence of two inductors with these paths.
Source: [[corr-wf14-inventory]] 048 (`selection.md` R1.5, "Run 1 `li`'s `o(1)` conjecture is refuted as stated … buy one share on even days, sell on odd days … divergent gain, bounded loss")
Kind: P
Fidelity: exact at the path level (the source's own argument); variant: offsets `1/(2(n+1))` so that prices stay in `[0,1]` from day `0`
Hyps: (a) -/
theorem splice_o1_conjecture_refuted_paths (φ : Sentence) (DP : DeductiveProcess)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    (∀ n χ, 0 ≤ harmonicLow φ n χ ∧ harmonicLow φ n χ ≤ 1) ∧
    (∀ n χ, 0 ≤ harmonicHigh φ n χ ∧ harmonicHigh φ n χ ≤ 1) ∧
    (∀ n χ, |harmonicLow φ n χ - harmonicHigh φ n χ| ≤ 1 / ((n : ℝ) + 1)) ∧
    Tendsto (fun n => harmonicLow φ n φ) atTop (𝓝 (1 / 2)) ∧
    Tendsto (fun n => harmonicHigh φ n φ) atTop (𝓝 (1 / 2)) ∧
    Tendsto (fun n => paritySplice (harmonicLow φ) (harmonicHigh φ) n φ) atTop (𝓝 (1 / 2)) ∧
    ComputableMarket (paritySplice (harmonicLow φ) (harmonicHigh φ)) ∧
    (parityTrader φ 1 0).Exploits (paritySplice (harmonicLow φ) (harmonicHigh φ)) DP := by
  obtain ⟨hlo, hhi⟩ := harmonic_mem_Icc φ
  obtain ⟨tlo, thi⟩ := harmonic_tendsto φ
  obtain ⟨clo, chi⟩ := computableMarket_harmonic φ
  refine ⟨hlo, hhi, harmonic_disagreement φ, tlo, thi, paritySplice_harmonic_tendsto φ,
    computableMarket_paritySplice _ _ clo chi, ?_⟩
  have hbS : ∀ n, 0 ≤ paritySplice (harmonicLow φ) (harmonicHigh φ) n φ ∧
      paritySplice (harmonicLow φ) (harmonicHigh φ) n φ ≤ 1 :=
    fun n => splice_mem_Icc _ _ _ hlo hhi n φ
  refine parityTrader_exploits_of_pairSum _ DP φ 1 (Or.inl rfl) 0 hbS hcons ?_ ?_
  · intro k _
    rw [Rat.cast_one, one_mul]
    exact le_trans (harmonicOffset_bounds k).1.le (harmonic_pairGain φ k)
  · intro B
    obtain ⟨n, hn⟩ := (Filter.tendsto_atTop.mp Real.tendsto_sum_range_one_div_nat_succ_atTop
      (2 * B + 1)).exists
    refine ⟨n, ?_⟩
    rw [Rat.cast_one, one_mul]
    unfold pairSum
    rw [Nat.Ico_zero_eq_range]
    have hterm : ∀ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) * (1 / ((k : ℝ) + 1)) ≤
        paritySplice (harmonicLow φ) (harmonicHigh φ) (2 * k + 1) φ -
          paritySplice (harmonicLow φ) (harmonicHigh φ) (2 * k) φ := by
      intro k _
      refine le_trans (le_of_eq ?_) (harmonic_pairGain φ k)
      field_simp
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.mul_sum] at hsum
    have hmono : ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1)) ≤
        ∑ i ∈ Finset.range (n + 1), (1 / ((i : ℝ) + 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ n))
        (fun i _ _ => by positivity)
    linarith

/-! ## T1.6 (ii) The inductor level: conditional on an OPEN existence -/

/-- **At the inductor level the `o(1)` conjecture is refuted *if* two inductors with the harmonic
paths exist.** Given two inductors over `DP` whose prices on `φ` are the harmonic paths and which
agree within `1/(n+1)` on every sentence, the parity splice is a computable market exploited by
`parityTrader φ 1 0`, hence not an inductor — so the conjecture "a splice of inductors agreeing to
`o(1)` on every sequence is an inductor" is false as a universal statement. The antecedent is
stated OPEN (`exists_inductor_pair_harmonic_disagreement`, `Open.lean`): no FAF construction
controls a price path on infinitely many days. **Do not read (i) as this theorem**: (i) is about
paths, this is about inductors and is conditional (findings).
Source: [[corr-wf14-inventory]] 048 (R1.5) and [[corr-wf13-inventory]] 062 (open problem 3, "prove or refute that an `o(1)`-agreeing splice of inductors is an inductor (~0.6)")
Kind: C
Fidelity: exact at the inductor level, conditional on the OPEN existence; the agreement is on every sentence (stronger than along e.c. sequences), at the explicit rate `1/(n+1)`
Hyps: (a) the antecedent is the OPEN existence statement, carried as a hypothesis -/
theorem splice_o1_conjecture_refuted_of_inductors (DP : DeductiveProcess) (φ : Sentence)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (hex : ∃ P₁ P₂ : History, IsLogicalInductor P₁ DP ∧ IsLogicalInductor P₂ DP ∧
      (∀ n, P₁ n φ = harmonicLow φ n φ) ∧ (∀ n, P₂ n φ = harmonicHigh φ n φ) ∧
      (∀ n χ, |P₁ n χ - P₂ n χ| ≤ 1 / ((n : ℝ) + 1))) :
    ¬ ∀ P₁ P₂ : History, IsLogicalInductor P₁ DP → IsLogicalInductor P₂ DP →
      (∀ n χ, |P₁ n χ - P₂ n χ| ≤ 1 / ((n : ℝ) + 1)) →
      IsLogicalInductor (paritySplice P₁ P₂) DP := by
  intro H
  obtain ⟨P₁, P₂, h₁, h₂, p₁, p₂, hagree⟩ := hex
  have hLI := H P₁ P₂ h₁ h₂ hagree
  have hpath : ∀ n, paritySplice P₁ P₂ n φ = paritySplice (harmonicLow φ) (harmonicHigh φ) n φ := by
    intro n
    simp only [paritySplice, splice]
    split_ifs
    · exact p₂ n
    · exact p₁ n
  have hbS : ∀ n, 0 ≤ paritySplice P₁ P₂ n φ ∧ paritySplice P₁ P₂ n φ ≤ 1 :=
    fun n => splice_mem_Icc P₁ P₂ _ (fun n ψ => h₁.price_mem_Icc n ψ)
      (fun n ψ => h₂.price_mem_Icc n ψ) n φ
  have hex' : (parityTrader φ 1 0).Exploits (paritySplice P₁ P₂) DP := by
    have h := (splice_o1_conjecture_refuted_paths φ DP hcons).2.2.2.2.2.2.2
    refine h.of_boundedDifference 0 (fun n v _ => ?_)
    rw [parityTrader_netWorth, parityTrader_netWorth]
    simp only [hpath, sub_self, abs_zero, le_refl]
  exact hLI.noExploit _ (parityTrader_ec φ 1 0) hex'

/-! ## Extension: the parity trader is harmless under summable disagreement -/

/-- **Transfer of exploitation from the splice to `P₁` under summable disagreement on `φ`.** The
parity trader's net worth against the parity splice and against `P₁` differ by
`Σ_{i ≤ n} c_i (P₁_i − S_i)`, with `|c_i| ≤ 1` and `|P₁_i − S_i| ≤ |P₁_i − P₂_i|`, so by at most
`Σ_i |P₁_i(φ) − P₂_i(φ)|` — a constant when the disagreement is summable. Hence if it exploits
the splice it exploits `P₁` (`Exploits.of_boundedDifference`).
Source: [[corr-wf14-inventory]] 048 (R1.5's replacement conjecture); mandate Extension (the attack through `Exploits.of_boundedDifference`)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem parityTrader_exploits_left_of_summable (P₁ P₂ : History) (DP : DeductiveProcess)
    (φ : Sentence) (s : ℚ) (hs : s = 1 ∨ s = -1) (M : ℕ)
    (hsum : Summable (fun n => |P₁ n φ - P₂ n φ|))
    (hex : (parityTrader φ s M).Exploits (paritySplice P₁ P₂) DP) :
    (parityTrader φ s M).Exploits P₁ DP := by
  refine hex.of_boundedDifference (∑' n, |P₁ n φ - P₂ n φ|) (fun n v _ => ?_)
  rw [parityTrader_netWorth, parityTrader_netWorth, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum (fun i _ => ?_))
    (hsum.sum_le_tsum (Finset.range (n + 1)) (fun i _ => abs_nonneg _))
  rw [show (parityCoeff s M i : ℝ) * (v.payout φ - paritySplice P₁ P₂ i φ) -
      (parityCoeff s M i : ℝ) * (v.payout φ - P₁ i φ) =
      (parityCoeff s M i : ℝ) * (P₁ i φ - paritySplice P₁ P₂ i φ) by ring, abs_mul]
  have hc : |(parityCoeff s M i : ℝ)| ≤ 1 := by
    unfold parityCoeff
    split_ifs <;> rcases hs with rfl | rfl <;> norm_num
  have hS : |P₁ i φ - paritySplice P₁ P₂ i φ| ≤ |P₁ i φ - P₂ i φ| := by
    simp only [paritySplice, splice]
    split_ifs
    · exact le_rfl
    · simp
  calc |(parityCoeff s M i : ℝ)| * |P₁ i φ - paritySplice P₁ P₂ i φ|
      ≤ 1 * |P₁ i φ - P₂ i φ| := mul_le_mul hc hS (abs_nonneg _) zero_le_one
    _ = |P₁ i φ - P₂ i φ| := one_mul _

/-- **The parity trader cannot exploit a parity splice of an inductor with a summably-disagreeing
path.** The one trader family for which R1.5's replacement conjecture is proved: for `P₁` an
inductor and `Σ_n |P₁_n(φ) − P₂_n(φ)| < ∞`, no `parityTrader φ s M` exploits `paritySplice P₁ P₂`
(else it would exploit `P₁`, and it is e.c.). Nothing is assumed of `P₂` beyond the disagreement.
The general conjecture (every e.c. trader) is OPEN (`splice_summable_conjecture`): the obstacles
are price-reading coefficients and unbounded quantities (findings).
Source: [[corr-wf14-inventory]] 048 (R1.5, "a *summable* disagreement along every e.c. sequence is the plausible sufficient condition [conjectured, ~0.6]"); mandate Extension
Kind: C
Fidelity: weaker: one trader family (the parity traders), not the criterion
Hyps: (a) -/
theorem parityTrader_not_exploits_paritySplice_of_summable (P₁ P₂ : History)
    (DP : DeductiveProcess) [hLI : IsLogicalInductor P₁ DP] (φ : Sentence) (s : ℚ)
    (hs : s = 1 ∨ s = -1) (M : ℕ) (hsum : Summable (fun n => |P₁ n φ - P₂ n φ|)) :
    ¬ (parityTrader φ s M).Exploits (paritySplice P₁ P₂) DP :=
  fun hex => hLI.noExploit _ (parityTrader_ec φ s M)
    (parityTrader_exploits_left_of_summable P₁ P₂ DP φ s hs M hsum hex)

end Cleanroom.Li.LiSpliceCondition
