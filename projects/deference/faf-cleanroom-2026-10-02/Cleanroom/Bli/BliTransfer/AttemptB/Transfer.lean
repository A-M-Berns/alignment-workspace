import Cleanroom.Bli.BliTransfer.AttemptB.Splice
import Cleanroom.Bli.BliFound.Bridge
import LogicalInduction.Framework.Affine

/-!
# `bli-transfer` · attempt B · Transfer: the accounting and the two-hypothesis headline (T1.2)

The transfer argument, over FAF's `Trader.Exploits.of_boundedDifference`:

1. `netWorth_difference_le_of_eventually_eq` — the generic two-market accounting: if two
   traders' day values agree from day `N` on, their net worths differ by at most the sum over
   days `< N` of the two magnitudes (mirror of FAF's `Trader.freezeOn_netWorth_difference_le`,
   with "affected days" replaced by "days before `N`"). Reused by T2 and T3.
2. `ExprMap.spliceTrader_netWorth_difference_le` — the instance for the splice along an
   expression map: day values agree exactly from the bridge lemma's `N` on
   (`bridge_lemma`: every traded sentence is day-small from `N`, so its settlement price agrees
   on `Q` and the overlay) by `Strategy.spliceOn_value`.
3. `not_exploits_overlay_of_spliceTrader_ec` — per trader: if `Tr` is e.c. and its splice is
   e.c., `Tr` does not exploit the overlay (the splice would exploit `Q`).
4. `overlay_isLogicalInductor_of_transfer` — the two-hypothesis headline: the transfer of
   efficiency for every e.c. trader (T1.3's certificate discharges it) and the overlay's
   computability (T1.4) give `IsLogicalInductor (overlay Q ov) DP`. Kept as a lemma so an
   auditor can see which leg is which; the certificate files state the closed forms.

Direction of `of_boundedDifference`: it transports *exploitation* from `(Tr, overlay)` to
`(Tr', Q)`, so the hypothesis is `Tr.Exploits (overlay Q ov) DP` and the contradiction is with
`hQ.noExploit` at the spliced trader.

Sources: [[bli-program]] §3.1 (proof sketch); mandate T1.2; `Properties/FinitePerturbations.lean:283`.
-/

namespace Cleanroom.Bli.BliTransfer.AttemptB

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## Generic two-market accounting -/

/-- A p.c. world pays `0` or `1` on every sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma payout_zero_or_one (v : PCWorld) (φ : Sentence) : v.payout φ = 0 ∨ v.payout φ = 1 := by
  by_cases hφ : v.Holds φ
  · exact Or.inr (by simp [PCWorld.payout, hφ])
  · exact Or.inl (by simp [PCWorld.payout, hφ])

/-- **Eventually-equal day values give uniformly bounded net-worth difference.** If the day
values of `Tr` against `P` and of `Tr'` against `Q` (assessed by the same world) agree from day
`N` on, and both markets price in `[0, 1]`, then on every day the two net worths differ by at
most the sum, over days `< N`, of the two magnitudes — a constant independent of the day and
of the world. Mirror of FAF's `Trader.freezeOn_netWorth_difference_le`.
Source: mandate T1.2(b)–(c); `Properties/FinitePerturbations.lean:283`
Kind: C
Fidelity: exact -/
theorem netWorth_difference_le_of_eventually_eq (Tr Tr' : Trader) (P Q : History) (N : ℕ)
    (hP : ∀ d φ, 0 ≤ P d φ ∧ P d φ ≤ 1) (hQ : ∀ d φ, 0 ≤ Q d φ ∧ Q d φ ≤ 1) (v : PCWorld)
    (heq : ∀ d, N ≤ d → (Tr.strat d).value P v.payout = (Tr'.strat d).value Q v.payout)
    (n : ℕ) :
    |Tr.netWorth P v n - Tr'.netWorth Q v n| ≤
      ∑ d ∈ Finset.range N, ((Tr.strat d).magnitude P + (Tr'.strat d).magnitude Q) := by
  classical
  set g : ℕ → ℝ := fun d => (Tr.strat d).magnitude P + (Tr'.strat d).magnitude Q with hg
  have hw : ∀ φ, v.payout φ = 0 ∨ v.payout φ = 1 := payout_zero_or_one v
  have hterm : ∀ d, |(Tr.strat d).value P v.payout - (Tr'.strat d).value Q v.payout| ≤
      if d < N then g d else 0 := by
    intro d
    by_cases hd : d < N
    · rw [if_pos hd]
      exact (abs_sub _ _).trans (add_le_add
        (Strategy.abs_value_le_magnitude (Tr.strat d) P v.payout hw (hP d))
        (Strategy.abs_value_le_magnitude (Tr'.strat d) Q v.payout hw (hQ d)))
    · rw [if_neg hd, heq d (not_lt.mp hd), sub_self, abs_zero]
  have hg0 : ∀ d, 0 ≤ g d := fun d =>
    add_nonneg (Strategy.magnitude_nonneg _ _) (Strategy.magnitude_nonneg _ _)
  calc |Tr.netWorth P v n - Tr'.netWorth Q v n|
      = |∑ d ∈ Finset.range (n + 1),
          ((Tr.strat d).value P v.payout - (Tr'.strat d).value Q v.payout)| := by
          simp only [Trader.netWorth]
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ d ∈ Finset.range (n + 1),
          |(Tr.strat d).value P v.payout - (Tr'.strat d).value Q v.payout| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.range (n + 1), (if d < N then g d else 0) :=
          Finset.sum_le_sum (fun d _ => hterm d)
    _ = ∑ d ∈ (Finset.range (n + 1)).filter (· < N), g d := by rw [Finset.sum_filter]
    _ ≤ ∑ d ∈ Finset.range N, g d :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (by
              intro d hd
              simp only [Finset.mem_filter, Finset.mem_range] at hd ⊢
              exact hd.2)
            (fun d _ _ => hg0 d)

/-! ## The expression-map instance -/

namespace ExprMap

variable {Q : History} {ov : ℕ → Sentence → ℚ}

/-- **Day values agree from the bridge day on.** For `d ≥ N` (the bridge lemma's day for
`Tr`), the spliced trader's day-`d` value against `Q` equals `Tr`'s against the overlay.
Source: [[bli-program]] §3.1; mandate T1.2(a)
Kind: C
Fidelity: exact -/
lemma spliceTrader_value_eq (E : ExprMap Q ov) (Tr : Trader) {N : ℕ}
    (hN : ∀ n ≥ N, ∀ φ, MentionedBy (Tr.strat n) φ → SmallOn n φ) (w : Sentence → ℝ)
    {d : ℕ} (hd : N ≤ d) :
    ((E.spliceTrader Tr).strat d).value Q w = (Tr.strat d).value (overlay Q ov) w := by
  refine Strategy.spliceOn_value (hr := E.rank_le) (fun k φ ρ => E.spliceLeaf_denoteWith k φ ρ)
    (Tr.strat d) w (fun p hp => ?_)
  exact overlay_small (hN d hd p.2 (Or.inl ⟨p.1, hp⟩))

/-- **Net-worth accounting for the splice** (the mandate's
`Trader.spliceOn_netWorth_difference_le`): for an e.c. trader `Tr` with bridge day `N`, the
net worth of `Tr` on the overlay and of its splice on `Q` differ, on every day and in every
world, by at most the day-`< N` magnitude sum.
Source: [[bli-program]] §3.1; mandate T1.2(c)
Kind: C
Fidelity: exact -/
theorem spliceTrader_netWorth_difference_le (E : ExprMap Q ov)
    (hQ : ∀ d φ, 0 ≤ Q d φ ∧ Q d φ ≤ 1) (Tr : Trader) {N : ℕ}
    (hN : ∀ n ≥ N, ∀ φ, MentionedBy (Tr.strat n) φ → SmallOn n φ) (v : PCWorld) (n : ℕ) :
    |Tr.netWorth (overlay Q ov) v n - (E.spliceTrader Tr).netWorth Q v n| ≤
      ∑ d ∈ Finset.range N,
        ((Tr.strat d).magnitude (overlay Q ov) + ((E.spliceTrader Tr).strat d).magnitude Q) :=
  netWorth_difference_le_of_eventually_eq Tr (E.spliceTrader Tr) (overlay Q ov) Q N
    (overlay_mem_Icc hQ E.ov_range) hQ v
    (fun d hd => (E.spliceTrader_value_eq Tr hN v.payout hd).symm) n

end ExprMap

/-! ## No exploitation, per trader and as a headline -/

/-- **Per-trader transfer.** If `Tr` is efficiently computable and its splice along `E` is
efficiently computable, then `Tr` does not exploit the overlay: by the accounting, the splice
would exploit `Q`, against `hQ.noExploit`. The efficiency of the splice is exactly what a
certificate (T1.3) supplies for every e.c. trader.
Source: [[bli-program]] §3.1; mandate T1.2(d)
Kind: C
Fidelity: exact
Hyps: (a) `hTr`; (a) `hTr'` is the certificate's output, an explicit hypothesis here -/
theorem not_exploits_overlay_of_spliceTrader_ec (Q : History) (DP : DeductiveProcess)
    [hQ : IsLogicalInductor Q DP] (ov : ℕ → Sentence → ℚ) (E : ExprMap Q ov) (Tr : Trader)
    (hTr : EfficientlyComputable Tr) (hTr' : EfficientlyComputable (E.spliceTrader Tr)) :
    ¬ Tr.Exploits (overlay Q ov) DP := by
  intro hex
  obtain ⟨N, hN⟩ := bridge_lemma Tr hTr
  refine hQ.noExploit _ hTr' (hex.of_boundedDifference
    (∑ d ∈ Finset.range N,
      ((Tr.strat d).magnitude (overlay Q ov) + ((E.spliceTrader Tr).strat d).magnitude Q))
    (fun n v _ => ?_))
  exact E.spliceTrader_netWorth_difference_le (fun d φ => hQ.price_mem_Icc d φ) Tr hN v n

/-- **The two-hypothesis headline** (mandate T1, kept as a lemma): given the *transfer of
efficiency* for every e.c. trader (T1.3's certificate discharges it) and the overlay's
computability (T1.4), the overlay is a logical inductor. Scope: over an expression map whose
bodies are closed and read only small prices of days `≤ k`; one-market (nothing reads the
overlay back into `Q`).
Source: [[bli-program]] §3.1; bli-paper-039; bli-slides-002/006/030; bli-soto-a-004; mandate T1
Kind: C
Fidelity: exact for the stated hypotheses
Hyps: (a) `hQ`; (a) `htrans` — the certificate's output for every e.c. trader, an explicit
hypothesis in this form (the closed forms in `Certificate.lean` name the class it is discharged
over); (a) `hcomp` — `Computable.lean` -/
theorem overlay_isLogicalInductor_of_transfer (Q : History) (DP : DeductiveProcess)
    [hQ : IsLogicalInductor Q DP] (ov : ℕ → Sentence → ℚ) (E : ExprMap Q ov)
    (htrans : ∀ Tr : Trader, EfficientlyComputable Tr → EfficientlyComputable (E.spliceTrader Tr))
    (hcomp : ComputableMarket (overlay Q ov)) :
    IsLogicalInductor (overlay Q ov) DP where
  marketComputable := hcomp
  processComputable := hQ.processComputable
  noExploit := fun Tr hTr =>
    not_exploits_overlay_of_spliceTrader_ec Q DP ov E Tr hTr (htrans Tr hTr)

/-- **No exploitation over a class** — the form a certificate that covers only a class `Cls`
of e.c. traders yields (kind `C`, `(c)`: the class). Not the criterion unless
`Cls = EfficientlyComputable`.
Source: mandate T1 traps (i) (wrong quantifier)
Kind: L
Fidelity: weaker: quantified over `Cls`, not over `EfficientlyComputable` -/
theorem overlay_noExploit_of_class (Q : History) (DP : DeductiveProcess)
    [IsLogicalInductor Q DP] (ov : ℕ → Sentence → ℚ) (E : ExprMap Q ov)
    (Cls : Trader → Prop)
    (hcls : ∀ Tr, Cls Tr → EfficientlyComputable Tr ∧ EfficientlyComputable (E.spliceTrader Tr)) :
    ∀ Tr, Cls Tr → ¬ Tr.Exploits (overlay Q ov) DP :=
  fun Tr hTr =>
    not_exploits_overlay_of_spliceTrader_ec Q DP ov E Tr (hcls Tr hTr).1 (hcls Tr hTr).2

end Cleanroom.Bli.BliTransfer.AttemptB
