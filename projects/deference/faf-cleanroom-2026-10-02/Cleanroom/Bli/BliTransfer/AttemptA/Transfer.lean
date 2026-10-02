import Cleanroom.Bli.BliTransfer.AttemptA.Splice
import Cleanroom.Bli.BliFound.Bridge
import LogicalInduction.Framework.Affine

/-!
# `bli-transfer` (attempt A) · Transfer: the accounting and the two-hypothesis headline (T1.2)

The economic half of the expressible-overlay transfer theorem, with the efficiency certificate
still a hypothesis (it is discharged in `Certificate.lean` and the headline assembled in
`Headline.lean`).

1. **The bridge day.** `bridge_lemma` (`Cleanroom.Bli.BliFound.Bridge`, grade (a)) gives a day
   `N` from which every sentence an efficiently computable trader trades is small on its day, so
   its settlement price agrees on `Q` and on the overlay (`exists_settle_day`).
2. **Exact transport from `N` on**, estimate before: on a day `≥ N` the spliced strategy against
   `Q` has exactly the value of the original against the overlay (`Strategy.spliceOn_value`); on
   the finitely many days `< N` the two values differ by at most the two magnitudes
   (`Strategy.abs_value_le_magnitude`, both markets priced in `[0,1]`). The generic form is
   `Trader.netWorth_difference_le_of_tail_eq` (two traders whose day values agree from `N` on
   have net worths within an explicit constant), the mirror of FAF's
   `Trader.freezeOn_netWorth_difference_le` with `D = range N`; the splice instance is
   `Trader.spliceOn_netWorth_difference_le`. `Restricted.lean` and `Clamp.lean` reuse the generic
   form.
3. **Exploitation transports** (`Exploits.of_boundedDifference`, per-trader constant, quantified
   over the worlds consistent with each stage): a trader exploiting the overlay yields its splice
   exploiting `Q` (`Trader.spliceOn_exploits`).
4. **`noExploit`**, given that the splice preserves efficiency
   (`noExploit_overlay_of_spliceEC`), and the inductor with `ComputableMarket (overlay Q ov)` as
   the second hypothesis (`overlay_isLogicalInductor_of_spliceEC`). The two hypotheses are kept
   visible here so an auditor can see which leg is which; the headline discharges both.

Sources: [[bli-program]] §3.1 (proof sketch); mandate T1.2; FAF `FinitePerturbations.lean:283`,
`Criterion.lean:1480`.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound
open scoped BigOperators

/-! ## Ranges and the bridge day -/

/-- The overlay of a `[0,1]`-market by a `[0,1]`-re-pricing is a `[0,1]`-market.
Source: mandate T1.2(b)
Kind: L
Fidelity: exact -/
lemma overlay_range {Q : History} {ov : ℕ → Sentence → ℚ}
    (hov : ∀ k ψ, 0 ≤ ov k ψ ∧ ov k ψ ≤ 1)
    (hQ : ∀ k ψ, 0 ≤ Q k ψ ∧ Q k ψ ≤ 1) (k : ℕ) (ψ : Sentence) :
    0 ≤ overlay Q ov k ψ ∧ overlay Q ov k ψ ≤ 1 := by
  by_cases hs : SmallOn k ψ
  · rw [overlay_small hs]; exact hQ k ψ
  · rw [overlay_large hs]
    rcases hov k ψ with ⟨h0, h1⟩
    exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩

/-- **The settlement day**: from the bridge lemma, an efficiently computable trader trades only
day-small sentences from some day `N` on, so its settlement prices agree on `Q` and the overlay.
Source: [[bli-program]] §2.1/§3.1; mandate T1.2(a); `Cleanroom.Bli.BliFound.bridge_lemma`
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma exists_settle_day (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ∃ N, ∀ n ≥ N, ∀ p ∈ (Tr.strat n).trades, SmallOn n p.2 := by
  obtain ⟨N, hN⟩ := bridge_lemma Tr hTr
  refine ⟨N, fun n hn p hp => hN n hn p.2 (Or.inl ⟨p.1, ?_⟩)⟩
  simpa using hp

/-! ## The net-worth accounting -/

/-- A world's payouts are `0`/`1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_zero_or_one (v : PCWorld) (φ : Sentence) : v.payout φ = 0 ∨ v.payout φ = 1 := by
  by_cases hφ : v.Holds φ
  · exact Or.inr (by simp [PCWorld.payout, hφ])
  · exact Or.inl (by simp [PCWorld.payout, hφ])

/-- **Generic finite-prefix accounting**: two traders on two `[0,1]`-markets whose day values
(against a `0/1` world) agree from day `N` on have net worths within the explicit constant
`∑_{d < N} (magnitude + magnitude)`. Every day `≥ N` cancels exactly, every day `< N` contributes
at most the two magnitudes. Mirror of FAF's `Trader.freezeOn_netWorth_difference_le` with
`D = range N`; reused by the splice, the restricted class and the clamp.
Source: mandate T1.2(b)–(c); FAF `Trader.freezeOn_netWorth_difference_le`
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma Trader.netWorth_difference_le_of_tail_eq (Tr Tr' : Trader) (V V' : History)
    (hV : ∀ k ψ, 0 ≤ V k ψ ∧ V k ψ ≤ 1) (hV' : ∀ k ψ, 0 ≤ V' k ψ ∧ V' k ψ ≤ 1)
    (N : ℕ) (v : PCWorld)
    (htail : ∀ n ≥ N, (Tr.strat n).value V v.payout = (Tr'.strat n).value V' v.payout)
    (n : ℕ) :
    |Tr.netWorth V v n - Tr'.netWorth V' v n| ≤
      ∑ d ∈ Finset.range N, ((Tr.strat d).magnitude V + (Tr'.strat d).magnitude V') := by
  classical
  let g : ℕ → ℝ := fun day ↦ (Tr.strat day).magnitude V + (Tr'.strat day).magnitude V'
  have hw : ∀ φ, v.payout φ = 0 ∨ v.payout φ = 1 := payout_zero_or_one v
  have hterm : ∀ day,
      |(Tr.strat day).value V v.payout - (Tr'.strat day).value V' v.payout| ≤
        if day ∈ Finset.range N then g day else 0 := by
    intro day
    by_cases hday : day ∈ Finset.range N
    · rw [if_pos hday]
      exact (abs_sub _ _).trans (add_le_add
        (Strategy.abs_value_le_magnitude (Tr.strat day) V v.payout hw (hV day))
        (Strategy.abs_value_le_magnitude (Tr'.strat day) V' v.payout hw (hV' day)))
    · rw [if_neg hday]
      have hge : N ≤ day := by simpa using hday
      rw [htail day hge]
      simp
  have hg : ∀ day, 0 ≤ g day := fun day ↦
    add_nonneg (Strategy.magnitude_nonneg _ _) (Strategy.magnitude_nonneg _ _)
  calc
    |Tr.netWorth V v n - Tr'.netWorth V' v n| =
        |∑ day ∈ Finset.range (n + 1),
          ((Tr.strat day).value V v.payout - (Tr'.strat day).value V' v.payout)| := by
          simp only [Trader.netWorth]
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ day ∈ Finset.range (n + 1),
          |(Tr.strat day).value V v.payout - (Tr'.strat day).value V' v.payout| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ day ∈ Finset.range (n + 1), if day ∈ Finset.range N then g day else 0 :=
          Finset.sum_le_sum (fun day _ ↦ hterm day)
    _ = ∑ day ∈ (Finset.range (n + 1)).filter (fun day ↦ day ∈ Finset.range N), g day := by
          rw [Finset.sum_filter]
    _ ≤ ∑ day ∈ Finset.range N, g day := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro day hday
            simp only [Finset.mem_filter] at hday
            exact hday.2
          · intro day _ _
            exact hg day

/-- The explicit bound on the net-worth discrepancy between a trader on the overlay and its
splice on `Q`, supported on the days before the settlement day `N`.
Source: mandate T1.2(c); FAF `Trader.freezeOnErrorBound`
Kind: D
Fidelity: exact -/
noncomputable def spliceErrorBound {Q : History} {ov : ℕ → Sentence → ℚ} (E : ExprMap Q ov)
    (Tr : Trader) (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.range N, ((Tr.strat d).magnitude (overlay Q ov) +
    ((Trader.spliceOn E.expr E.rank_le Tr).strat d).magnitude Q)

/-- **Net worths differ by a constant** (`spliceOn_netWorth_difference_le`): every day `≥ N`
cancels exactly (`Strategy.spliceOn_value`, the settlement day), every day `< N` contributes at
most the two magnitudes.
Source: [[bli-program]] §3.1 (proof sketch); mandate T1.2(c)
Kind: C
Fidelity: exact
Hyps: (a) `hQ` is the inductor's price range; `hN` is the settlement day -/
lemma Trader.spliceOn_netWorth_difference_le {Q : History} {ov : ℕ → Sentence → ℚ}
    (E : ExprMap Q ov) (hQ : ∀ k ψ, 0 ≤ Q k ψ ∧ Q k ψ ≤ 1) (Tr : Trader) (N : ℕ)
    (hN : ∀ n ≥ N, ∀ p ∈ (Tr.strat n).trades, SmallOn n p.2) (v : PCWorld) (n : ℕ) :
    |Tr.netWorth (overlay Q ov) v n - (Trader.spliceOn E.expr E.rank_le Tr).netWorth Q v n| ≤
      spliceErrorBound E Tr N :=
  Trader.netWorth_difference_le_of_tail_eq Tr (Trader.spliceOn E.expr E.rank_le Tr)
    (overlay Q ov) Q (overlay_range E.ov_range hQ) hQ N v
    (fun day hge => by
      rw [Trader.spliceOn_strat, Strategy.spliceOn_value E.spliceSpec E.rank_le (Tr.strat day)
        v.payout (fun p hp => (overlay_small (hN day hge p hp)).symm)])
    n

/-! ## Exploitation transports -/

/-- **Exploitation transports from the overlay to the base**: an efficiently computable trader
exploiting `overlay Q ov` yields its splice exploiting `Q` — bounded net-worth difference
(`spliceErrorBound` at the settlement day) through FAF's `Exploits.of_boundedDifference`, whose
world quantifier is `v.ConsistentWith (DP.D n)` (mandate trap (v)).
Source: [[bli-program]] §3.1 (proof sketch); mandate T1.2(d)
Kind: C
Fidelity: exact
Hyps: (a) -/
lemma Trader.spliceOn_exploits {Q : History} {ov : ℕ → Sentence → ℚ} {DP : DeductiveProcess}
    (E : ExprMap Q ov) (hQ : ∀ k ψ, 0 ≤ Q k ψ ∧ Q k ψ ≤ 1)
    (Tr : Trader) (hTr : EfficientlyComputable Tr) (h : Tr.Exploits (overlay Q ov) DP) :
    (Trader.spliceOn E.expr E.rank_le Tr).Exploits Q DP := by
  obtain ⟨N, hN⟩ := exists_settle_day Tr hTr
  exact Trader.Exploits.of_boundedDifference h (spliceErrorBound E Tr N)
    (fun n v _ => Trader.spliceOn_netWorth_difference_le E hQ Tr N hN v n)

/-- **No efficiently computable trader exploits the overlay, given that the splice preserves
efficiency.** The efficiency transport `hec` is the certificate leg (T1.3, discharged in
`Certificate.lean`); this lemma is the economic leg alone, kept separate so the two are auditable
apart. `hec` is a named hypothesis here, not a field of any structure (mandate trap (ii)).
Source: [[bli-program]] §3.1; mandate T1.2(d)
Kind: C
Fidelity: exact
Hyps: (a) except `hec`, the efficiency transport (T1.3) -/
lemma noExploit_overlay_of_spliceEC {Q : History} {ov : ℕ → Sentence → ℚ}
    {DP : DeductiveProcess} [hQ : IsLogicalInductor Q DP] (E : ExprMap Q ov)
    (hec : ∀ Tr : Trader, EfficientlyComputable Tr →
      EfficientlyComputable (Trader.spliceOn E.expr E.rank_le Tr)) :
    ∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits (overlay Q ov) DP := by
  intro Tr hTr hexp
  exact hQ.noExploit _ (hec Tr hTr)
    (Trader.spliceOn_exploits E (fun k ψ => hQ.marketComputable.1 k ψ) Tr hTr hexp)

/-- **The two-hypothesis form of the transfer theorem**: the overlay of a logical inductor by an
expression map is a logical inductor, given the efficiency transport (`hec`, T1.3) and the
overlay's computability (`hcomp`, T1.4). `marketComputable := hcomp`,
`processComputable := hQ.processComputable`, `noExploit` from `noExploit_overlay_of_spliceEC`.
The headline `Headline.overlay_isLogicalInductor` discharges both legs.
Source: [[bli-program]] §3.1; mandate T1 (two-hypothesis form)
Kind: C
Fidelity: exact
Hyps: (a) except `hec` (T1.3) and `hcomp` (T1.4), named -/
lemma overlay_isLogicalInductor_of_spliceEC {Q : History} {ov : ℕ → Sentence → ℚ}
    {DP : DeductiveProcess} [hQ : IsLogicalInductor Q DP] (E : ExprMap Q ov)
    (hec : ∀ Tr : Trader, EfficientlyComputable Tr →
      EfficientlyComputable (Trader.spliceOn E.expr E.rank_le Tr))
    (hcomp : ComputableMarket (overlay Q ov)) :
    IsLogicalInductor (overlay Q ov) DP where
  marketComputable := hcomp
  processComputable := hQ.processComputable
  noExploit := noExploit_overlay_of_spliceEC E hec

end Cleanroom.Bli.BliTransfer.AttemptA
