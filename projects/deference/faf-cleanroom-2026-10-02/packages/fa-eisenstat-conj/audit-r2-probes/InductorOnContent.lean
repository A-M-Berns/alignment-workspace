import Cleanroom.Fa.FaEisenstatConj.GenRefuted

/-!
# Audit r2 (adversarial) probe · InductorOnContent

Evidence for the audit of `fa-eisenstat-conj` (`fa-eisenstat-conj-audit-r2-adversarial.md`).
Not imported by the library.

What it checks, about the repair-round-1 object `InductorOn` (the criterion along a day-set) and
the OPEN `fallback_evenDays_noExploit` stated over it:

1. `InductorOn P DP ∅` holds for *every* market and process: a trader supported on the empty
   day-set has net worth `0` on every day, so its assessments are bounded above. The content of
   `InductorOn … S` therefore sits entirely in `S` being infinite — expected of a weakening
   ("at best an inductor on the subsequence"), recorded so a reader does not take
   `InductorOn … S` for a finite `S` as saying anything.
2. The even-day criterion is **not** trivially true for the merge shape: the feedback-free merge
   `mergeMarket A botQuotes`, and the mixed merge `mergeMarket A (mixedQuotes botQuotes)` whose
   even days are feedback-free, both *fail* `InductorOn … {n | n % 2 = 0}` against every process
   with consistent stages — the certified even-day trader `buyTopEven` exploits them (engine
   `buyTopEven_exploits`, the parity mirror of the package's `buyTopOdd_exploits`). So the OPEN
   `fallback_evenDays_noExploit` has content, and that content is carried by its hypothesis
   `pkg` (the honest even-day quotes): with the even-day quotes unconstrained the conclusion is
   false.
-/

namespace Cleanroom.Fa.FaEisenstatConj

open LogicalInduction Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- Probe 1: on the empty day-set every market satisfies the criterion along it. -/
theorem probe_inductorOn_empty (P : History) (DP : DeductiveProcess) : InductorOn P DP ∅ := by
  intro Tr _ hsupp hex
  apply hex.2
  refine ⟨0, ?_⟩
  rintro x ⟨n, v, _, rfl⟩
  unfold Trader.netWorth
  exact le_of_eq (Finset.sum_eq_zero fun i _ =>
    hsupp.value_eq_zero (by simp) P v.payout)

/-- Probe 2 engine: the even-day `⊤`-share trader exploits a `[0,1]` market with consistent
stages whose price of `⊤` is at most `1/2` on every late even day (the parity mirror of
`buyTopOdd_exploits`). -/
theorem probe_buyTopEven_exploits (P : History) (DP : DeductiveProcess)
    (hP : ∀ n φ, 0 ≤ P n φ ∧ P n φ ≤ 1)
    (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (k : ℕ) (hk : ∀ i, k ≤ i → i % 2 = 0 → P i ⊤ ≤ 1 / 2) :
    buyTopEven.Exploits P DP := by
  classical
  refine exploits_of_ge_partialSums_from buyTopEven P DP hP
    (fun i => if k ≤ i ∧ i % 2 = 0 then (1 / 2 : ℝ) else 0) (1 / 2) (by norm_num)
    (fun i => by split_ifs <;> norm_num) k ?_ ?_ hcons
  · intro n _ v _
    unfold Trader.netWorth
    refine Finset.sum_le_sum fun i _ => ?_
    have hpay : v.payout (⊤ : Sentence) = 1 := by
      unfold PCWorld.payout
      rw [if_pos (PCWorld.holds_top v)]
    simp only [buyTopEven, Strategy.value, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, EF.denote_const, hpay]
    by_cases hi : i % 2 = 0
    · rw [if_pos hi]
      simp only [Rat.cast_one, one_mul]
      split_ifs with h
      · linarith [hk i h.1 h.2]
      · linarith [(hP i ⊤).2]
    · have hw : ¬ (k ≤ i ∧ i % 2 = 0) := fun h => hi h.2
      rw [if_neg hw, if_neg hi]
      simp
  · have heven : ∃ᶠ n in atTop, n % 2 = 0 :=
      Filter.frequently_atTop.2 fun N => ⟨2 * N, by omega, by omega⟩
    refine (heven.and_eventually (eventually_ge_atTop k)).mono fun n hn => ?_
    rw [if_pos ⟨hn.2, hn.1⟩]

/-- Probe 2a: the feedback-free merge fails the criterion along the even days. -/
theorem probe_botQuotes_not_inductorOn_even {A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (DP : DeductiveProcess) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ¬ InductorOn (mergeMarket A botQuotes) DP {n | n % 2 = 0} := by
  intro h
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1
    ((bot_price_tendsto_zero (A := A) hworldA).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine h buyTopEven buyTopEven_efficientlyComputable buyTopEven_supportedOn ?_
  refine probe_buyTopEven_exploits _ DP
    (mergeMarket_mem_Icc (fun n s => IsLogicalInductor.price_mem_Icc (P := A) (DP := DPA) n s) _)
    hcons k fun i hi _ => ?_
  rw [mergeMarket_botQuotes]
  exact hk i hi

/-- Probe 2b: the mixed merge with feedback-free even days — the exact market shape of the OPEN
`fallback_evenDays_noExploit`, with `Q := botQuotes` in place of a package-of-record `Q` — fails
the criterion along the even days. The OPEN's conclusion is therefore carried by `pkg`. -/
theorem probe_mixedBot_not_inductorOn_even {A : History} {DPA : DeductiveProcess}
    [IsLogicalInductor A DPA] (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (DP : DeductiveProcess) (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ¬ InductorOn (mergeMarket A (mixedQuotes botQuotes)) DP {n | n % 2 = 0} := by
  intro h
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1
    ((bot_price_tendsto_zero (A := A) hworldA).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine h buyTopEven buyTopEven_efficientlyComputable buyTopEven_supportedOn ?_
  refine probe_buyTopEven_exploits _ DP
    (mergeMarket_mem_Icc (fun n s => IsLogicalInductor.price_mem_Icc (P := A) (DP := DPA) n s) _)
    hcons k fun i hi heven => ?_
  rw [mergeMarket_mixedQuotes_even A botQuotes heven, mergeMarket_botQuotes]
  exact hk i hi

end Cleanroom.Fa.FaEisenstatConj
