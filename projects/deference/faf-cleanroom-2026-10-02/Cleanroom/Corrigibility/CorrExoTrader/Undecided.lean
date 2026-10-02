import Cleanroom.Corrigibility.CorrExoTrader.Defs
import Cleanroom.Li.LiProjection.Fragments
import Cleanroom.Li.LiProjection.Underdetermination

/-!
# `corr-exo-trader` · Undecided: what pays on undecidables (T7), the unpushed contrast, and the coefficient-one refutation

Package `Cleanroom.Corrigibility.CorrExoTrader` ([[corr-exo-trader-mandate]]), file 6 of the
layout. Imports `li-projection`'s `Fragments` / `Underdetermination` (no `Construction.*`).

* **T7.1 the mark-to-market decomposition** `netWorth_eq_markToMarket_add_openExposure`: for any
  trader, history, world and day, `netWorth = markToMarket + openExposure`, where the first is
  world-independent (positions repriced at today's price) and the second is the current position
  priced against the world at today's price. The headline `undecided_profit_is_markToMarket`: for
  a trader confined to `{φ, ∼φ}` with `φ` undecided (both verdicts plausible, `hboth`), its set of
  plausible assessments on day `n` is the set of two values — **at most two points** (they coincide
  iff `s_φ + s_{∼φ} = 0`) — mark-to-market plus the open position priced by either verdict. No settlement ever enters: the only world-independent profit
  on an undecidable is price movement (Abram's correction, line 105/115: "no payoff for being
  right about `u`, only for being right about the future price of `u`-sentences").
* **The unpushed contrast** `unpushed_interior` (T1.4's second half): over any inductor with `u`
  fresh, the limiting belief on `u` is in `(0, 1)` — `li-projection`'s
  `limitingBelief_atom_mem_Ioo`; so T1.4's pinned day price `1` is genuinely different.
* **The coefficient-one form of the generalised LIC is refuted** (`genLic_coefficientOne_refuted`,
  findings): the source's display `Value_n(T) ≤ c_T + Loss_n(H)` for an *unbudgeted* e.c. `T` is
  false already at `H = 0` (`Loss = 0`): over any inductor with `u` fresh, the e.c. trader
  `buyDaily u` has plausible assessments unbounded above (in the `u`-worlds, which are plausible at
  every stage, its net worth is `∑ (1 − P_i(u)) → ∞` because `P_∞(u) < 1`). The LIC forbids
  exploitation (bounded below *and* unbounded above), not unbounded upside alone; what holds is
  the budgeted form (`GenLic.lean` T2.2) and the exploitation form (T2.3).
* **T7.2** `u_price_converges_of_inductor`: convergence over an inductor is FAF's
  `lic_limitingBelief_tendsto` (citation); over the exo-market it needs the OPEN computability
  bridge (`Open.lean`). FAF API observation (findings): the §4 theorems take the class although
  their proofs use its `noExploit` and range fields only; a `NoEcExploit`-and-range refactor would
  make them available to the exo-market.
-/

namespace Cleanroom.Corrigibility.CorrExoTrader

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Li.LiProjection Filter Topology

/-! ## T7.1 — the mark-to-market decomposition -/

/-- **T7.1 — the mark-to-market decomposition.** For any trader `T`, history `P`, world `v` and day
`n`: `T.netWorth P v n = markToMarket T P n + openExposure T P v n`. (`Strategy.value` is
`∑ eᵢ(P)(w φᵢ − P i φᵢ)`; add and subtract `P n φᵢ`.) The first summand does not mention `v`.
`ring` after unfolding (kind L, audit r1 N3).
Source: line 105, 115; corr-core-046(i); mandate T7.1
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem netWorth_eq_markToMarket_add_openExposure (T : Trader) (P : History) (v : PCWorld)
    (n : ℕ) : T.netWorth P v n = markToMarket T P n + openExposure T P v n := by
  unfold Trader.netWorth markToMarket openExposure
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Strategy.value]
  rw [← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro p _
  ring

/-- **A closed position's net worth is its mark-to-market** (the `roundTrip_value_eq` corollary in
decomposition form): if the open exposure vanishes in world `v`, the net worth is world-independent.
Source: mandate T7.1 (corollary)
Kind: L
Fidelity: exact -/
theorem netWorth_eq_markToMarket_of_closed (T : Trader) (P : History) (v : PCWorld) (n : ℕ)
    (hclosed : openExposure T P v n = 0) : T.netWorth P v n = markToMarket T P n := by
  rw [netWorth_eq_markToMarket_add_openExposure, hclosed, add_zero]

/-! ## Net positions and the two-point set -/

/-- The trader's net share position in `ψ` through day `n`: the sum of the coefficients of its
`ψ`-trades.
Source: mandate T7.1 ("its net share position `s`")
Kind: D
Fidelity: exact -/
noncomputable def netPosition (T : Trader) (P : History) (n : ℕ) (ψ : Sentence) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (((T.strat i).trades.filter (fun p => p.2 = ψ)).map (fun p => p.1.denote P)).sum

/-- No sentence is its own negation (semantically: a world would both hold and refute it).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ne_neg_self (φ : Sentence) : φ ≠ ∼φ := by
  intro h
  have hiff := PCWorld.holds_neg (fun _ => True) φ
  rw [← h] at hiff
  by_cases hv : PCWorld.Holds (fun _ => True) φ
  · exact hiff.mp hv hv
  · exact hv (hiff.mpr hv)

/-- Regrouping a confined trade list by its two sentences.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma confined_list_sum (φ : Sentence) (P : History) (g : Sentence → ℝ)
    (l : List (EF × Sentence)) (hl : ∀ p ∈ l, p.2 = φ ∨ p.2 = ∼φ) :
    (l.map (fun p => p.1.denote P * g p.2)).sum =
      ((l.filter (fun p => p.2 = φ)).map (fun p => p.1.denote P)).sum * g φ +
      ((l.filter (fun p => p.2 = ∼φ)).map (fun p => p.1.denote P)).sum * g (∼φ) := by
  induction l with
  | nil => simp
  | cons p rest ih =>
      have hrest : ∀ p ∈ rest, p.2 = φ ∨ p.2 = ∼φ := fun p hp => hl p (List.mem_cons_of_mem _ hp)
      have ih' := ih hrest
      rcases hl p (List.mem_cons_self) with hp | hp
      · have hp' : p.2 ≠ ∼φ := by rw [hp]; exact ne_neg_self φ
        rw [List.filter_cons_of_pos (by simp [hp]), List.filter_cons_of_neg (by simp [hp'])]
        simp only [List.map_cons, List.sum_cons]
        rw [ih', hp]
        ring
      · have hp' : p.2 ≠ φ := by rw [hp]; exact (ne_neg_self φ).symm
        rw [List.filter_cons_of_neg (by simp [hp']), List.filter_cons_of_pos (by simp [hp])]
        simp only [List.map_cons, List.sum_cons]
        rw [ih', hp]
        ring

/-- For a trader confined to `{φ, ∼φ}`, the open exposure is the two net positions priced against
the world: `s_φ (w φ − P n φ) + s_{∼φ} (w (∼φ) − P n (∼φ))`.
Source: mandate T7.1
Kind: L
Fidelity: exact -/
lemma openExposure_confined (T : Trader) (P : History) (v : PCWorld) (φ : Sentence)
    (hT : ∀ n, ∀ p ∈ (T.strat n).trades, p.2 = φ ∨ p.2 = ∼φ) (n : ℕ) :
    openExposure T P v n =
      netPosition T P n φ * (v.payout φ - P n φ) +
      netPosition T P n (∼φ) * (v.payout (∼φ) - P n (∼φ)) := by
  unfold openExposure netPosition
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact confined_list_sum φ P (fun ψ => v.payout ψ - P n ψ) _ (hT i)

/-- The two candidate plausible values of a confined trader on day `n`: the verdict `φ` (payout `1`
on `φ`, `0` on `∼φ`) and the verdict `¬φ`.
Source: mandate T7.1
Kind: D
Fidelity: exact -/
noncomputable def confinedValueTrue (T : Trader) (P : History) (φ : Sentence) (n : ℕ) : ℝ :=
  markToMarket T P n + netPosition T P n φ * (1 - P n φ) - netPosition T P n (∼φ) * P n (∼φ)

/-- The `¬φ`-verdict value.
Source: mandate T7.1
Kind: D
Fidelity: exact -/
noncomputable def confinedValueFalse (T : Trader) (P : History) (φ : Sentence) (n : ℕ) : ℝ :=
  markToMarket T P n - netPosition T P n φ * P n φ + netPosition T P n (∼φ) * (1 - P n (∼φ))

/-- In a world holding `φ` the confined trader's net worth is `confinedValueTrue`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma confined_netWorth_of_holds (T : Trader) (P : History) (φ : Sentence)
    (hT : ∀ n, ∀ p ∈ (T.strat n).trades, p.2 = φ ∨ p.2 = ∼φ) (v : PCWorld) (hv : v.Holds φ)
    (n : ℕ) : T.netWorth P v n = confinedValueTrue T P φ n := by
  have hvneg : ¬ v.Holds (∼φ) := by rw [PCWorld.holds_neg]; exact fun h => h hv
  rw [netWorth_eq_markToMarket_add_openExposure, openExposure_confined T P v φ hT n,
    PCWorld.payout, if_pos hv, PCWorld.payout, if_neg hvneg, confinedValueTrue]
  ring

/-- In a world refuting `φ` the confined trader's net worth is `confinedValueFalse`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma confined_netWorth_of_not_holds (T : Trader) (P : History) (φ : Sentence)
    (hT : ∀ n, ∀ p ∈ (T.strat n).trades, p.2 = φ ∨ p.2 = ∼φ) (v : PCWorld) (hv : ¬ v.Holds φ)
    (n : ℕ) : T.netWorth P v n = confinedValueFalse T P φ n := by
  have hvneg : v.Holds (∼φ) := by rw [PCWorld.holds_neg]; exact hv
  rw [netWorth_eq_markToMarket_add_openExposure, openExposure_confined T P v φ hT n,
    PCWorld.payout, if_neg hv, PCWorld.payout, if_pos hvneg, confinedValueFalse]
  ring

/-- **T7.1 — on an undecided sentence, profit is mark-to-market plus one of two verdicts.** For a
trader all of whose trades are on `φ` or `∼φ`, over a process on which both verdicts on `φ` are
plausible at every stage (`hboth`, the premise shape of `confined_not_exploits_const`), the set of
its plausible assessments on day `n` is **the set of the two values** `{markToMarket + s_φ(1 − P_n φ) −
s_{∼φ} P_n(∼φ), markToMarket − s_φ P_n φ + s_{∼φ}(1 − P_n(∼φ))}`, where `s_ψ` is its net share position
in `ψ` — **at most two points** (they coincide exactly when `s_φ + s_{∼φ} = 0`, e.g. equal long
positions in `φ` and `∼φ`; audit r1 N9). Nothing settles; the world-independent part is price
movement alone. Single-market.
Source: line 105 ("LI traders can often make money betting on undecidable stuff … no money in expectation"), line 115 ("no payoff for being right about `u`, only for being right about the future price"); corr-core-046(i), 034's LI face; mandate T7.1
Kind: C (audit r2 adversarial N5: a set extensionality, a case split on the verdict and two regrouping lemmas — the content is the regrouping)
Fidelity: exact (the two-leg form; the mandate's one-leg display is the case `s_{∼φ} = 0`)
Hyps: (a): `hT` is the confinement, `hboth` is derived from freshness for a fresh atom (`exists_consistent_holds_atom`/`exists_consistent_not_holds_atom`) -/
theorem undecided_profit_is_markToMarket (T : Trader) (P : History) (DP : DeductiveProcess)
    (φ : Sentence) (hT : ∀ n, ∀ p ∈ (T.strat n).trades, p.2 = φ ∨ p.2 = ∼φ)
    (hboth : ∀ n, (∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ) ∧
      (∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds φ)) (n : ℕ) :
    {x | ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ x = T.netWorth P v n} =
      {confinedValueTrue T P φ n, confinedValueFalse T P φ n} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, _, rfl⟩
    by_cases hv : v.Holds φ
    · exact Or.inl (confined_netWorth_of_holds T P φ hT v hv n)
    · exact Or.inr (confined_netWorth_of_not_holds T P φ hT v hv n)
  · rintro (rfl | rfl)
    · obtain ⟨⟨v, hv, hvφ⟩, _⟩ := hboth n
      exact ⟨v, hv, (confined_netWorth_of_holds T P φ hT v hvφ n).symm⟩
    · obtain ⟨_, ⟨v, hv, hvφ⟩⟩ := hboth n
      exact ⟨v, hv, (confined_netWorth_of_not_holds T P φ hT v hvφ n).symm⟩

/-- The instance at the utility atom over a cleanroom-free process with a consistent world at every
stage: both verdicts on `u` are plausible at every stage (derived from freshness, never assumed).
Source: mandate decision 4 ("undecided at every stage")
Kind: L
Fidelity: exact -/
theorem utilityAtom_both_plausible (DP : DeductiveProcess) (hDP : CleanroomFreeProcess DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) :
    (∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds utilityAtom) ∧
      (∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds utilityAtom) :=
  ⟨exists_consistent_holds_atom (atomFreeProcess_exo_of_cleanroomFree hDP 0) hworld n,
   exists_consistent_not_holds_atom (atomFreeProcess_exo_of_cleanroomFree hDP 0) hworld n⟩

/-! ## The unpushed contrast (T1.4, second half) -/

/-- **The unpushed interior.** Over any inductor `P` with `u` fresh and a consistent world at every
stage, the limiting belief on `u` is in `(0, 1)` — `li-projection`'s `limitingBelief_atom_mem_Ioo`.
Against this, a pushed day pins the price to `1` (`Market.lean`, `push_pins_day_price`).
Source: mandate T1.4 (`unpushed_interior`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem unpushed_interior (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ) (hu : AtomFreeProcess u DP) :
    limitingBelief P (Formula.atom u) ∈ Set.Ioo (0 : ℝ) 1 :=
  limitingBelief_atom_mem_Ioo P DP hworld u hu

/-- The unpushed interior at the utility atom over a cleanroom-free process.
Source: mandate T1.4
Kind: L
Fidelity: exact -/
theorem unpushed_interior_utilityAtom (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hDP : CleanroomFreeProcess DP) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    limitingBelief P utilityAtom ∈ Set.Ioo (0 : ℝ) 1 :=
  unpushed_interior P DP hworld utilityAtomCode (atomFreeProcess_exo_of_cleanroomFree hDP 0)

/-! ## The coefficient-one form of the generalised LIC is false -/

/-- **The source's display `Value_n(T) ≤ c_T + Loss_n(H)` fails for unbudgeted e.c. `T`, already at
`H = 0`.** Over any inductor `P` with `u` fresh and a consistent world at every stage, the e.c.
trader `buyDaily u` (one share of `u` daily) has **no** upper bound on its plausible assessments: in
the `u`-worlds, plausible at every stage, its net worth is `∑_{i ≤ n} (1 − P_i(u))`, which diverges
because `P_∞(u) < 1` (non-dogmatism). The criterion forbids *exploitation* — bounded below and
unbounded above — not unbounded upside alone; a trader unbounded in both directions is permitted.
So the generalised LIC can hold only in the budgeted form (T2.2) or the exploitation form (T2.3).
Source: line 95 (the conjecture's display); corr-core-041; mandate T2.2 ("exhibit the obstruction")
Kind: P
Fidelity: exact (refutes the display at `H = 0`, where `Loss_n(H) = 0`)
Hyps: (a) -/
theorem genLic_coefficientOne_refuted (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (u : ℕ) (hu : AtomFreeProcess u DP) :
    ¬ ∃ c : ℝ, ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) →
      (buyDaily (Formula.atom u)).netWorth P v n ≤ c := by
  rintro ⟨c, hc⟩
  have hP := IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  obtain ⟨_, hL1⟩ := unpushed_interior P DP hworld u hu
  set L := limitingBelief P (Formula.atom u) with hL
  have hconv := lic_limitingBelief_tendsto P DP hworld (Formula.atom u)
  -- eventually `P_n(u) ≤ (1 + L)/2`
  have hgap : 0 < (1 - L) / 2 := by linarith
  obtain ⟨N, hN⟩ : ∃ N, ∀ n, N ≤ n → P n (Formula.atom u) ≤ (1 + L) / 2 := by
    have h := Metric.tendsto_atTop.mp hconv ((1 - L) / 2) hgap
    obtain ⟨N, hN⟩ := h
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]
  -- a day far enough out
  obtain ⟨k, hk⟩ := exists_nat_gt (c / ((1 - L) / 2))
  have hk' : c < k * ((1 - L) / 2) := by rwa [div_lt_iff₀ hgap] at hk
  set n := N + k with hn
  obtain ⟨v, hv, hvu⟩ := exists_consistent_holds_atom hu hworld n
  have hbound := hc n v hv
  rw [buyDaily_netWorth] at hbound
  have hterm : ∀ i, v.payout (Formula.atom u) - P i (Formula.atom u) = 1 - P i (Formula.atom u) :=
    fun i => by rw [PCWorld.payout, if_pos hvu]
  simp only [hterm] at hbound
  -- lower bound of the sum
  have hsub : Finset.Ico N (n + 1) ⊆ Finset.range (n + 1) := by
    intro i hi
    simp only [Finset.mem_Ico] at hi
    exact Finset.mem_range.mpr hi.2
  have hsum : ((Finset.Ico N (n + 1)).card : ℝ) * ((1 - L) / 2) ≤
      ∑ i ∈ Finset.range (n + 1), (1 - P i (Formula.atom u)) := by
    calc ((Finset.Ico N (n + 1)).card : ℝ) * ((1 - L) / 2)
        = (Finset.Ico N (n + 1)).card • ((1 - L) / 2) := by rw [nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.Ico N (n + 1), (1 - P i (Formula.atom u)) := by
          apply Finset.card_nsmul_le_sum
          intro i hi
          have := hN i (Finset.mem_Ico.mp hi).1
          linarith
      _ ≤ ∑ i ∈ Finset.range (n + 1), (1 - P i (Formula.atom u)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro i _ _
          linarith [(hP i (Formula.atom u)).2]
  have hcard : ((Finset.Ico N (n + 1)).card : ℝ) = (k : ℝ) + 1 := by
    rw [Nat.card_Ico, hn, show N + k + 1 - N = k + 1 by omega]
    push_cast
    rfl
  rw [hcard] at hsum
  nlinarith [hgap]

/-- **The refutation with the e.c. certificate conjoined** (audit r1 N8): the counterexample
`buyDaily u` is an e.c. trader (li-projection's `buyDaily_ec`), so the display *quantified over e.c.
`T`* is refuted, not merely its instance at an arbitrary trader.
Source: line 95 (the conjecture's display); audit r1 N8 (adversarial)
Kind: C
Fidelity: exact (refutes the display at `H = 0`, where `Loss_n(H) = 0`)
Hyps: (a) -/
theorem genLic_coefficientOne_refuted_ec (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (u : ℕ) (hu : AtomFreeProcess u DP) :
    EfficientlyComputable (buyDaily (Formula.atom u)) ∧
      ¬ ∃ c : ℝ, ∀ (n : ℕ) (v : PCWorld), v.ConsistentWith (DP.D n) →
        (buyDaily (Formula.atom u)).netWorth P v n ≤ c :=
  ⟨buyDaily_ec _, genLic_coefficientOne_refuted P DP hworld u hu⟩

/-! ## T7.2 — convergence -/

/-- **T7.2 — convergence over an inductor** is FAF's `lic_limitingBelief_tendsto` (`thm:con`): the
price of `u` converges to its limiting belief. A citation. Over the exo-market the statement needs
the computability bridge (T2.5, OPEN): see `Open.lean`'s `exo_u_price_converges`.
Source: line 115 ("Convergence still applies to `⌜u > 0.7⌝`"); corr-core-046(ii); mandate T7.2
Kind: L
Fidelity: exact (over an inductor; the exo-market form is OPEN)
Hyps: (a) -/
theorem u_price_converges_of_inductor (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ConvergesTo (fun n => P n utilityAtom) (limitingBelief P utilityAtom) :=
  lic_limitingBelief_tendsto P DP hworld utilityAtom

end Cleanroom.Corrigibility.CorrExoTrader
