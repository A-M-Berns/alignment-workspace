import Cleanroom.Bli.BliLinkageB.Trader

/-!
# bli-linkage, angle B — the price-reading trader for K3 (`sellCells`)

**Why a second trader.** `Trader.buyOne ψ` buys one share of a *fixed* sentence family `ψ n`;
its certificate `buyOne_ec` needs `MachineSentenceCodes ψ`. The conclusion of record
`Degenerate.no_degenerate_linked_bli` instantiates it at
`ψ n := ∼ lit_{n+1, χ n, todayIdx n}` — but `todayIdx n` is **today's rounded price** of the
inductor (`entryOf (χ n) (tableOfCode (deg n))`, with `deg n` the table copying today's rounded
entries). A trader that must *name* that sentence from `n` alone would have to compute the
inductor's rounded price in polynomial time, which no theorem gives (and which is false for the
pseudorandom coordinates the instance is meant for). The mandate's "a single negated atom, so
`MachineSentenceCodes` follows from `χ`'s" overlooks the cell index (findings FB-14).

**The repair.** The trader does not need to *name* today's cell: it can *read* today's prices
through the coefficient. On day `n`, for every cell `r < d`, `sellCells L d` sells
`price_n(lit_{n,r})` shares of `lit_{n,r}` — the coefficient `−price_n(lit_{n,r})` is the
expressible feature `EF.mul (EF.const (−1)) (EF.price (L n r) n)`, the sentence family
`z ↦ L z.unpair.1 z.unpair.2` is machine-metered whenever the literal family is (nothing about
today's cell enters it), and FAF's `EfficientlyComputable.ofTradeBlocksBig` certifies the
`d`-trade strategy with `MachineSpliceStream.serialize_price` for the price leaf. Its day-`n`
value in a world `w` is `∑_{r<d} p_r (p_r − w(lit_{n,r}))`. Under the degenerate linked package
the prices are `p_r = [r = today n]`, so the value is `1 − w(lit_{n, today n})`: `0` if
tomorrow's rounded price stays, `1` if it moves — exactly `buyOne`'s payoff at the negated
literal, obtained without naming it.

**Exploitation** (`sellCells_exploits`): bounded below by `−∑_{i<N} ∑_r |p_{i,r}|` (every day
`≥ N` has value `≥ 0`), unbounded above because every moved day `≥ N` whose negated literal has
entered a stage pays `1` in every world consistent with that stage — the same
`exploits_of_bddBelow_of_unbounded` argument as `buyOne_exploits`. `hmove` stays a hypothesis.
-/

namespace Cleanroom.Bli.BliLinkageB

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

/-- **The selling coefficient**: at the paired index `z = ⟨n, r⟩`, minus the day-`n` price of
`L n r` — the expressible feature `(−1) · price_n(L n r)`.
Source: mandate K3b (repaired: the trader reads today's cell through the price, FB-14)
Kind: D
Fidelity: n/a -/
def sellCoef (L : ℕ → ℕ → Sentence) (z : ℕ) : EF :=
  EF.mul (EF.const (-1)) (EF.price (L z.unpair.1 z.unpair.2) z.unpair.1)

/-- **The price-reading trader**: on day `n`, for every cell `r < d`, sells `price_n(L n r)`
shares of `L n r`.
Source: mandate K3b (repaired, FB-14); [[bli-program]] §3.6(iii)
Kind: D
Fidelity: variant: `d` price-weighted sales of the cell literals in place of one share of the
negated literal of today's cell (whose family is not machine-metered) -/
def sellCells (L : ℕ → ℕ → Sentence) (d : ℕ) : Trader where
  strat n :=
    { trades := (List.range d).map fun j =>
        (sellCoef L (Nat.pair n j), L (Nat.pair n j).unpair.1 (Nat.pair n j).unpair.2)
      rank_le := by
        intro p hp
        simp only [List.mem_map, List.mem_range] at hp
        obtain ⟨j, -, rfl⟩ := hp
        simp [sellCoef, EF.rank, Nat.unpair_pair] }

/-- A list sum over `List.range d` is the finset sum over `Finset.range d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma list_sum_map_range (g : ℕ → ℝ) (d : ℕ) :
    ((List.range d).map g).sum = ∑ r ∈ Finset.range d, g r := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
      simp

/-- The day-`n` value of `sellCells`: `∑_{r<d} p_r (p_r − w(L n r))` with `p_r := V n (L n r)`.
Source: none: infrastructure (FAF `Strategy.value`)
Kind: L
Fidelity: n/a -/
theorem sellCells_value (L : ℕ → ℕ → Sentence) (d : ℕ) (V : History) (w : Sentence → ℝ)
    (n : ℕ) :
    ((sellCells L d).strat n).value V w =
      ∑ r ∈ Finset.range d, V n (L n r) * (V n (L n r) - w (L n r)) := by
  unfold sellCells Strategy.value
  simp only [List.map_map]
  rw [list_sum_map_range]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Function.comp, sellCoef, EF.denote, EF.denoteWith, Nat.unpair_pair]
  push_cast
  ring

/-- The net worth after day `n`: the sum of the day values.
Source: none: infrastructure (FAF `Trader.netWorth`)
Kind: L
Fidelity: n/a -/
theorem sellCells_netWorth (L : ℕ → ℕ → Sentence) (d : ℕ) (V : History) (v : PCWorld)
    (n : ℕ) :
    (sellCells L d).netWorth V v n = ∑ i ∈ Finset.range (n + 1),
      ∑ r ∈ Finset.range d, V i (L i r) * (V i (L i r) - v.payout (L i r)) := by
  unfold Trader.netWorth
  exact Finset.sum_congr rfl fun i _ => sellCells_value L d V v.payout i

/-- **The price-reading trader is efficiently computable** whenever the paired literal family
`z ↦ L z.unpair.1 z.unpair.2` is machine-metered: `d` trades a day
(`EfficientlyComputable.ofTradeBlocksBig` at the constant count), each coefficient a `mul` of a
constant and a price leaf (`MachineSpliceStream.serialize_mul`/`serialize_const`/`serialize_price`,
the day read by the unary ruler `unpairFst`). Nothing about today's cell enters the certificate.
Source: mandate K3b (repaired, FB-14); FAF `EfficientlyComputable.ofTradeBlocksBig` (`Framework/Machine/SpliceMachine.lean:494`), `MachineSpliceStream.serialize_price` (`:391`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem sellCells_ec {L : ℕ → ℕ → Sentence} (d : ℕ)
    (hlit : MachineSentenceCodes fun z => L z.unpair.1 z.unpair.2) :
    EfficientlyComputable (sellCells L d) := by
  have hf : MachineSpliceStream fun z => (sellCoef L z).serialize :=
    (MachineSpliceStream.serialize_mul (MachineSpliceStream.serialize_const (-1))
      (MachineSpliceStream.serialize_price hlit UnaryRuler.id
        (MachineDigits.ofUnaryRuler UnaryRuler.unpairFst))).of_eq (fun _ => rfl)
  exact EfficientlyComputable.ofTradeBlocksBig (sellCells L d) (fun _ => d) (sellCoef L)
    (fun z => L z.unpair.1 z.unpair.2) (UnaryRuler.const d) hf hlit (fun _ => rfl)

/-- A single sale's value is bounded below by minus the absolute price: for a world payout
`w ∈ [0, 1]`, `p (p − w) ≥ −|p|`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sale_ge_neg_abs (p w : ℝ) (hw : 0 ≤ w ∧ w ≤ 1) : -|p| ≤ p * (p - w) := by
  have h1 : p * w ≤ |p| := by
    calc p * w ≤ |p * w| := le_abs_self _
      _ = |p| * |w| := abs_mul _ _
      _ ≤ |p| * 1 := mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, hw.2⟩) (abs_nonneg _)
      _ = |p| := mul_one _
  nlinarith [mul_self_nonneg p]

/-- **The price-reading trader exploits a market whose cell prices are the indicator of today's
cell from day `N` on**, provided every stage has a consistent world, every moved day's literal
of today's cell is refuted by some stage, and there are infinitely many moved days (`hmove`).
Bounded below by `−∑_{i<N} ∑_{r<d} |V i (L i r)|`; unbounded above along worlds consistent
with ever-later stages (`exploits_of_bddBelow_of_unbounded`, not `exploits_of_ge_partialSums`).
Source: mandate K3b (repaired, FB-14); [[bli-program]] §3.6(iii); FAF `exploits_of_bddBelow_of_unbounded`
Kind: P
Fidelity: exact (`hmove` explicit, as mandate § K3 requires)
Hyps: (a) -/
theorem sellCells_exploits (L : ℕ → ℕ → Sentence) (d : ℕ) (V : History) (DP : DeductiveProcess)
    (N : ℕ) (today : ℕ → ℕ)
    (hpr : ∀ n ≥ N, ∀ r < d, V n (L n r) = if r = today n then 1 else 0)
    (htoday : ∀ n ≥ N, today n < d)
    (hworld : ∀ k, ∃ v : PCWorld, v.ConsistentWith (DP.D k)) {moved : ℕ → Prop}
    (hdec : ∀ n, moved n → ∃ k, ∀ v : PCWorld, v.ConsistentWith (DP.D k) →
      ¬ v.Holds (L n (today n)))
    (hmove : Set.Infinite {n | moved n}) : (sellCells L d).Exploits V DP := by
  -- the day value and its three bounds
  set val : ℕ → PCWorld → ℝ := fun i v =>
    ∑ r ∈ Finset.range d, V i (L i r) * (V i (L i r) - v.payout (L i r)) with hval
  set c : ℕ → ℝ := fun i => ∑ r ∈ Finset.range d, |V i (L i r)| with hc
  have hc_nonneg : ∀ i, 0 ≤ c i := fun i => Finset.sum_nonneg fun r _ => abs_nonneg _
  have hday_lb : ∀ i v, -c i ≤ val i v := by
    intro i v
    simp only [hval, hc, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun r _ => sale_ge_neg_abs _ _ (payout_mem_Icc v _)
  have hday_ge : ∀ i ≥ N, ∀ v, 0 ≤ val i v := by
    intro i hi v
    refine Finset.sum_nonneg fun r hr => ?_
    rw [hpr i hi r (Finset.mem_range.1 hr)]
    split_ifs
    · linarith [(payout_mem_Icc v (L i r)).2]
    · simp
  have hday_one : ∀ i ≥ N, ∀ v : PCWorld, ¬ v.Holds (L i (today i)) → val i v = 1 := by
    intro i hi v hv
    simp only [hval]
    rw [Finset.sum_eq_single_of_mem (today i) (Finset.mem_range.2 (htoday i hi))]
    · rw [hpr i hi _ (htoday i hi), if_pos rfl, payout_of_not_holds hv]; norm_num
    · intro r hr hne
      rw [hpr i hi r (Finset.mem_range.1 hr), if_neg hne]; simp
  set C : ℝ := ∑ i ∈ Finset.range N, c i with hC
  -- the partial sums of the early losses are bounded by `C`
  have hearly : ∀ n, -C ≤ ∑ i ∈ Finset.range (n + 1), (if i < N then -c i else 0) := by
    intro n
    rw [← Finset.sum_filter, Finset.sum_neg_distrib, neg_le_neg_iff, hC]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi => Finset.mem_range.2 (Finset.mem_filter.1 hi).2) fun i _ _ => hc_nonneg i
  refine exploits_of_bddBelow_of_unbounded _ _ _ C ?_ ?_
  · rintro x ⟨n, v, -, rfl⟩
    rw [sellCells_netWorth]
    refine le_trans (hearly n) (Finset.sum_le_sum fun i _ => ?_)
    split_ifs with hi
    · exact hday_lb i v
    · exact hday_ge i (not_lt.1 hi) v
  · intro B
    obtain ⟨t, ht, hcard⟩ :=
      (hmove.sdiff (Set.finite_lt_nat N)).exists_subset_card_eq (⌈B + C⌉₊ + 1)
    have htN : ∀ i ∈ t, N ≤ i := fun i hi => not_lt.1 (ht hi).2
    have hk : ∀ i, ∃ k, i ∈ t → ∀ v : PCWorld, v.ConsistentWith (DP.D k) →
        ¬ v.Holds (L i (today i)) := by
      intro i
      by_cases hi : i ∈ t
      · obtain ⟨k, hk⟩ := hdec i (ht hi).1
        exact ⟨k, fun _ => hk⟩
      · exact ⟨0, fun h => absurd h hi⟩
    choose kf hkf using hk
    obtain ⟨v, hv⟩ := hworld (max (t.sup id) (t.sup kf))
    refine ⟨_, ⟨max (t.sup id) (t.sup kf), v, hv, rfl⟩, ?_⟩
    rw [sellCells_netWorth]
    have hvi : ∀ i ∈ t, ¬ v.Holds (L i (today i)) := fun i hi =>
      hkf i hi v fun φ hφ => hv φ (DP.mono_le
        (le_trans (Finset.le_sup (f := kf) hi) (le_max_right _ _)) hφ)
    have hsub : t ⊆ Finset.range (max (t.sup id) (t.sup kf) + 1) := fun i hi =>
      Finset.mem_range.2 (Nat.lt_succ_of_le
        (le_trans (Finset.le_sup (f := id) hi) (le_max_left _ _)))
    -- pointwise: early loss + membership indicator ≤ day value
    have hpt : ∀ i ∈ Finset.range (max (t.sup id) (t.sup kf) + 1),
        (if i < N then -c i else 0) + (if i ∈ t then (1 : ℝ) else 0) ≤ val i v := by
      intro i _
      by_cases hi : i < N
      · have hit : i ∉ t := fun h => absurd (htN i h) (not_le.2 hi)
        rw [if_pos hi, if_neg hit, add_zero]; exact hday_lb i v
      · rw [if_neg hi, zero_add]
        by_cases hit : i ∈ t
        · rw [if_pos hit, hday_one i (not_lt.1 hi) v (hvi i hit)]
        · rw [if_neg hit]; exact hday_ge i (not_lt.1 hi) v
    have hcount : ∑ i ∈ Finset.range (max (t.sup id) (t.sup kf) + 1),
        (if i ∈ t then (1 : ℝ) else 0) = (⌈B + C⌉₊ : ℝ) + 1 := by
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hsub, hcard]
      push_cast; ring
    have h4 : B + C ≤ (⌈B + C⌉₊ : ℝ) := Nat.le_ceil _
    have := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, hcount] at this
    linarith [hearly (max (t.sup id) (t.sup kf))]

/-- **No logical inductor prices tomorrow's cell literals of a machine-metered family as the
indicator of today's cell from some day on, if the rounded price moves infinitely often** — the
`Q n (lit_r) = [r = today n]` form of `Trader.no_inductor_prices_zero_eventually`, for the
price-reading trader. No metering of `today` is asked.
Source: mandate K3 (the conclusion of record's price input, repaired FB-14)
Kind: C
Fidelity: exact (`hmove` explicit)
Hyps: (a) -/
theorem no_inductor_prices_indicator_eventually {L : ℕ → ℕ → Sentence} {d : ℕ}
    (hlit : MachineSentenceCodes fun z => L z.unpair.1 z.unpair.2)
    (V : History) (DP : DeductiveProcess) [hLI : IsLogicalInductor V DP] (N : ℕ) (today : ℕ → ℕ)
    (hpr : ∀ n ≥ N, ∀ r < d, V n (L n r) = if r = today n then 1 else 0)
    (htoday : ∀ n ≥ N, today n < d)
    (hworld : ∀ k, ∃ v : PCWorld, v.ConsistentWith (DP.D k)) {moved : ℕ → Prop}
    (hdec : ∀ n, moved n → ∃ k, ∀ v : PCWorld, v.ConsistentWith (DP.D k) →
      ¬ v.Holds (L n (today n)))
    (hmove : Set.Infinite {n | moved n}) : False :=
  hLI.noExploit _ (sellCells_ec d hlit)
    (sellCells_exploits L d V DP N today hpr htoday hworld hdec hmove)

end Cleanroom.Bli.BliLinkageB
