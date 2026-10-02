import Cleanroom.Li.LiSpliceCondition.Splice
import Cleanroom.Li.LiSpliceCondition.Condition
import Cleanroom.Li.LiProjection.Prescribe
import Cleanroom.Li.LiProjection.Fragments
import LogicalInduction.Construction.Conditioning.Endpoints
import LogicalInduction.Properties.NonDogmatism
import LogicalInduction.Properties.AffineCoherence

/-!
# `li-splice-condition` · DayIndexed: 063(a), the day-indexed conditions (repair rounds 1–2)

Package `Cleanroom.Li.LiSpliceCondition` ([[li-splice-condition-mandate]]), file 11 of the layout,
added in repair round 1 and revised in repair round 2. Both round-1 audits found the OPEN
statement of record for 063(a) (`conditioned_dayIndexed_floor`, formerly in `Open.lean`)
trivially true: its `∃ DP'` admitted an unsatisfiable process, which FAF's
`isLogicalInductor_of_stage_unsatisfiable` turns into an inductor for free. This file replaces it.
The source (E7 escape (ii), `clusters/E/NEGATIVES.md` l. 235: "For the day-indexed conditions a
decision sequence needs, no theorem of the paper covers the gap directly (CONJECTURE that a price
floor `ε_n` with `Σ` constraints suffices; not attempted)"; the inventory's 063(a): "whether a
day-indexed condition sequence `a_n` with a price floor `ℙ_n(a_n) ≥ ε_n` gives any asymptotic
guarantee on `ℙ_n(· | a_n)`") fixes the day's condition to the day's own `a_n` but not the process
the conditioned market should be an inductor over — and its use case, candidate actions kept
unrefuted by exploration, is not an "inductor over a `DeductiveProcess`" claim at all. The
FAF-expressible "inductor over a process" readings are exactly (G), (L) and (S) below: the naive
per-day process `n ↦ DP.D n ∪ {ψ n}` is a `DeductiveProcess` iff `ψ n ∈ DP.D (n+1) ∪ {ψ (n+1)}`,
i.e. iff it is (L)'s shape, and any monotone process holding the day's condition is (S)'s. The
candidate reading itself is formalized in `Candidate.lean` as a statement about trades, not
inductor-hood. Status here:

* **(G) Growing conjunction** — condition day `n` on `ψ₀ ⋏ ⋯ ⋏ ψₙ`, over `DP ∪ prefixProcess ψ`:
  **FAF's theorem, with no floor at all** (`lic_conditioned_growing_ofSequence`;
  `conditioned_prefix_isLogicalInductor` below adds the membership and non-degeneracy clauses).
  This is the inventory's own "`thm:scon` covers … growing prefix conjunctions" case, restated
  over FAF for the record — not a settlement of the conjecture, which the inventory states for
  the day's own condition.
* **(F) Presentation-shaped families with a uniform floor** — FAF's `lic_conditioned_gated_ofMarketComputation`
  (`conditioned_presentation_floor`); a `ConditioningPresentation`'s condition family is monotone
  in content (`presentation_condition_antitone`), so this is (G)'s shape, not a per-day one.
* **(L) Learned past** — the day's own condition `ψ n`, where the earlier conditions are already in
  the base process (`ψ m ∈ DP.D n` for `m < n`: the *realized* action of each day, asserted by
  the base process the next day): **proved, with the floor derived**
  (`conditioned_learnedPast_isLogicalInductor`). Because `ψ n ∈ DP.D (n+1)`, FAF's provability
  induction (`lic_provind_true`) gives `P n (ψ n) → 1` (`learnedPast_tendsto_one`), so the
  uniform floor the ε-form lemma `conditioned_learnedPast_of_floor` takes is automatic from some
  day on; the theorem of record assumes only per-day positivity (no early price exactly `0`), and
  `conditioned_learnedPast_patch` drops even that by a finite patch. In this reading the source's
  floor conjecture is vacuous — nothing needs to be conjectured — and the conditions are the
  realized actions, which need no exploration to keep their prices up; so (L) is **not** the
  source's use case (unchosen candidates), and settles 063(a) only for a reading the source does
  not make. The proof is FAF's `Trader.conditionedTranslation` with a first-failure argument
  (the failure can only be the current day), over the pinned, stage-consistent process
  `DP ∪ prefixProcess ψ`.
* **(S) The day's own condition over any process that accumulates the conditions** (the former
  statement's shape, with the non-degeneracy the audits asked for): **refuted at the alternating
  instance**, which is enough for the `¬ ∀`. This is the mismatch reading: the base inductor is
  over `DP`, which does not contain the earlier conditions, while `DP'` does. With fresh atoms
  `a ≠ b` and the alternating family `a, b, a, b, …`, every process containing the day's condition
  at every stage contains `a` from stage `0`, so every plausible world holds `a`, while the day-`n`
  market conditions on `b` alone and keeps `P_n(∼a | b) ≥ P_n(∼a ⋏ b)` bounded away from `0`
  (non-dogmatism under `DP`). Selling `∼a` on odd days exploits it
  (`conditioned_alternating_exploited`), for every inductor and every such process;
  `conditioned_dayIndexed_floor_false` is the `¬ ∀` form, with the floor hypothesis inhabited by a
  finite patch of any inductor (`exists_inductor_floor_two_atoms`). The exploit uses no floor: it
  bites because the alternating family makes an earlier condition recur as a fixed sentence with
  a non-dogmatism floor; a distinct condition per day would need a floor along a varying family,
  not in hand — so this is a refutation of (S) as a universal, not a theory of (S).
* **(C) Candidate reading** (`Candidate.lean`): the day's conditions are unchosen candidates with a
  price floor, held by no process; FAF's translator gives *gated* non-exploitation — no e.c.
  trader's net worth against the day-wise conditioned market, counted only on the days whose
  condition the world realizes, is bounded below and unbounded above over `DP`'s plausible
  worlds (`conditioned_candidate_not_gatedExploits`). The floor is a genuine hypothesis there.

Also here, from the adversarial audit's N2 (the sharpening of li-projection's
`summable_price_neg_of_mem_stage` that (B3)'s docstring needed): for an e.c. selling schedule `Q`
on a stage-refuted sentence, `Σ_n Q_n · P_n(ψ) < ∞` (`summable_schedule_mul_price_of_refuted`).
-/

namespace Cleanroom.Li.LiSpliceCondition

open LogicalInduction LO.Propositional Cleanroom.Li.LiProjection Filter Topology

/-! ## (G) The growing-conjunction reading: FAF's theorem, no floor -/

/-- The growing process `DP ∪ prefixProcess ψ` contains `DP`'s stages and the day's condition.
Source: none: infrastructure (FAF's `prefixProcess`, stage `n` = `{ψ₀, …, ψₙ}`)
Kind: L
Fidelity: n/a -/
theorem prefixUnion_mem (DP : DeductiveProcess) (ψ : ℕ → Sentence) :
    (∀ n, DP.D n ⊆ (DP.union (prefixProcess ψ)).D n) ∧
    (∀ n, ψ n ∈ (DP.union (prefixProcess ψ)).D n) := by
  refine ⟨fun n φ hφ => ?_, fun n => ?_⟩
  · simp only [DeductiveProcess.union_stage, Finset.mem_union]
    exact Or.inl hφ
  · simp only [DeductiveProcess.union_stage, Finset.mem_union, prefixProcess, List.mem_toFinset,
      List.mem_map, List.mem_range]
    exact Or.inr ⟨n, Nat.lt_succ_self n, rfl⟩

/-- A world consistent with a stage of the growing process holds every condition up to that day,
and conversely.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem consistentWith_prefixUnion_iff (DP : DeductiveProcess) (ψ : ℕ → Sentence) (v : PCWorld)
    (n : ℕ) :
    v.ConsistentWith ((DP.union (prefixProcess ψ)).D n) ↔
      v.ConsistentWith (DP.D n) ∧ ∀ i, i ≤ n → v.Holds (ψ i) := by
  rw [PCWorld.consistentWith_union_iff]
  constructor
  · rintro ⟨hv, hp⟩
    refine ⟨hv, fun i hi => hp _ ?_⟩
    simp only [prefixProcess, List.mem_toFinset, List.mem_map, List.mem_range]
    exact ⟨i, Nat.lt_succ_of_le hi, rfl⟩
  · rintro ⟨hv, hψ⟩
    refine ⟨hv, fun φ hφ => ?_⟩
    simp only [prefixProcess, List.mem_toFinset, List.mem_map, List.mem_range] at hφ
    obtain ⟨i, hi, rfl⟩ := hφ
    exact hψ i (Nat.lt_succ_iff.mp hi)

/-- Non-degeneracy of the growing process: a world consistent with each stage of `DP` and holding
the conditions up to that day is consistent with the stage of `DP ∪ prefixProcess ψ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem prefixUnion_hworld (DP : DeductiveProcess) (ψ : ℕ → Sentence)
    (hjoint : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ∀ i, i ≤ n → v.Holds (ψ i)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union (prefixProcess ψ)).D n) := by
  intro n
  obtain ⟨v, hv, hψ⟩ := hjoint n
  exact ⟨v, (consistentWith_prefixUnion_iff DP ψ v n).mpr ⟨hv, hψ⟩⟩

/-- **The growing-conjunction reading of 063(a) is FAF's theorem, with no price floor** — the
inventory's own already-covered case ("`thm:scon` covers fixed conditions or growing prefix
conjunctions only"), restated over FAF for the record, not a settlement of the conjecture. For an
inductor `P` and an e.c. condition family `ψ`, conditioning day `n` on `ψ₀ ⋏ ⋯ ⋏ ψₙ` is an inductor
over `DP ∪ prefixProcess ψ`, whose stages contain `DP`'s and the day's condition; the process is
non-degenerate whenever the prefixes are jointly plausible (`prefixUnion_hworld`). No floor
hypothesis: FAF derives the floor by compactness in the consistent case
(`lic_conditioned_growing_ofSequence`'s first branch) and the criterion is vacuous in the other.
One application of FAF's theorem conjoined with two membership facts: plumbing (Kind lowered in
repair round 2). N+ over the paper LIA: `paperPrefix_instance` (`DayIndexedWitness.lean`).
Source: [[corr-legit-neg-inventory]] 063(a) ("`thm:scon` covers … growing prefix conjunctions only"), growing-conjunction reading; FAF `lic_conditioned_growing_ofSequence` (`thm:scon`, tex:1613–1618)
Kind: L
Fidelity: variant: the day-`n` condition is the prefix conjunction `ψ₀ ⋏ ⋯ ⋏ ψₙ` (FAF's `sentenceConjunction`, with its harmless `⊤` tail); no floor needed
Hyps: (a) -/
theorem conditioned_prefix_isLogicalInductor (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (ψ : ℕ → Sentence) (hψ : MachineSentenceCodes ψ) :
    IsLogicalInductor
      (conditionedHistory P (fun n => sentenceConjunction ((List.range (n + 1)).map ψ)))
      (DP.union (prefixProcess ψ)) ∧
    (∀ n, DP.D n ⊆ (DP.union (prefixProcess ψ)).D n) ∧
    (∀ n, ψ n ∈ (DP.union (prefixProcess ψ)).D n) :=
  ⟨ConditioningCompile.lic_conditioned_growing_ofSequence P DP ψ hψ, (prefixUnion_mem DP ψ).1,
    (prefixUnion_mem DP ψ).2⟩

/-! ## (F) Presentation-shaped families with a uniform floor: FAF's gated endpoint -/

/-- **FAF's floor theorem, as this package consumes it**: for a `ConditioningPresentation DP extra`
and a uniform floor `ε ≤ P d (C.condition d)` on every day, the conditioned market is an inductor
over `DP ∪ extra`. The market computation is read off the inductor instance. This is the
day-indexed floor form the former OPEN (B6) pointed at; its condition family is
presentation-shaped, i.e. monotone in content (`presentation_condition_antitone`), so it is the
growing reading (G) with the floor supplied instead of derived.
Source: [[corr-legit-neg-inventory]] 063(a); FAF `lic_conditioned_gated_ofMarketComputation` (`thm:scon`)
Kind: L
Fidelity: exact (FAF's statement with the market computation discharged)
Hyps: (a) -/
theorem conditioned_presentation_floor (P : History) (DP extra : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (C : ConditioningPresentation DP extra) (ε : ℚ)
    (hε : 0 < (ε : ℝ)) (hfloor : ∀ d, (ε : ℝ) ≤ P d (C.condition d)) :
    IsLogicalInductor (conditionedHistory P C.condition) (DP.union extra) := by
  obtain ⟨market⟩ := hLI.marketComputable.nonemptyComputation
  exact ConditioningCompile.lic_conditioned_gated_ofMarketComputation P DP extra C market ε hε hfloor

/-- A presentation's condition family is monotone in content: a world holding the day-`n`
condition holds every earlier one (FAF's `extra` is a deductive process, so its stages grow). This
is why (F) is a growing reading, not a per-day one.
Source: none: infrastructure (FAF's `ConditioningPresentation.not_holds_condition_of_le`)
Kind: L
Fidelity: n/a -/
theorem presentation_condition_antitone {DP extra : DeductiveProcess}
    (C : ConditioningPresentation DP extra) (v : PCWorld) {m n : ℕ} (hmn : m ≤ n)
    (hn : v.Holds (C.condition n)) : v.Holds (C.condition m) := by
  by_contra hm
  exact C.not_holds_condition_of_le v hmn hm hn

/-! ## (L) The learned-past reading: proved, the floor derived -/

/-- Non-degeneracy of the learned-past reading: when the earlier conditions are in the base
process, the stages of `DP ∪ prefixProcess ψ` are consistent as soon as each day's own condition
is plausible at its stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem learnedPast_hworld (DP : DeductiveProcess) (ψ : ℕ → Sentence)
    (hpast : ∀ m n, m < n → ψ m ∈ DP.D n)
    (hjoint : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds (ψ n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.union (prefixProcess ψ)).D n) := by
  refine prefixUnion_hworld DP ψ fun n => ?_
  obtain ⟨v, hv, hψ⟩ := hjoint n
  refine ⟨v, hv, fun i hi => ?_⟩
  rcases Nat.lt_or_eq_of_le hi with h | h
  · exact hv _ (hpast i n h)
  · exact h ▸ hψ

/-- **The learned-past reading of 063(a), ε-form (the lemma behind the theorem of record)**: for
an inductor `P` over `DP`, an e.c. condition family `ψ` whose earlier members are in the base
process (`ψ m ∈ DP.D n` for `m < n`), and a uniform rational floor `ε ≤ P n (ψ n)`, the market
conditioned day `n` on the day's own condition `ψ n` is an inductor over the pinned process
`DP ∪ prefixProcess ψ` (stage `n` = `DP.D n ∪ {ψ₀, …, ψₙ}`, which equals `DP.D n ∪ {ψₙ}` here).
The process is non-degenerate under per-day plausibility (`learnedPast_hworld`), so the
`isLogicalInductor_of_stage_unsatisfiable` escape of the former OPEN statement is closed.

The floor is where FAF's translator enters (it certifies the translated coefficients,
`1/P_n(ψ_n)` approximated within the conditioning budget) — but in this reading it is **not an
independent hypothesis**: `hpast` puts `ψ n` into stage `n + 1`, so provability induction makes
`P n (ψ n) → 1` (`learnedPast_tendsto_one`), and the theorem of record
`conditioned_learnedPast_isLogicalInductor` assumes only per-day positivity (repair round 2,
both audits). Was named `conditioned_learnedPast_isLogicalInductor` in repair round 1.

Proof: FAF's gated translation `T.conditionedTranslation ψ ε` (defined for any condition family)
tracks `T` within `1` on worlds holding every condition up to the day
(`conditionedTranslation_netWorth_lower`), and its day-`n` trade is worth exactly `0` in a world
failing `ψ n` (`locallyGatedConditionalContract_value_eq_zero_of_not_holds`). A `DP`-plausible
world holds every *earlier* condition by `hpast`, so the only possible failure is the current day,
and the first-failure argument of `thm:scon` goes through with no monotonicity of `ψ`: the
translated trader's plausible assessments over `DP` are bounded below by `min (L − 1) 0` and
unbounded above, so it exploits `P` — against `noExploit`, since it is e.c. by FAF's
`CondStep.conditionedTranslation_preserves_ec`.
Source: [[corr-legit-neg-inventory]] 063(a), learned-past reading; FAF `Trader.conditionedTranslation` (`thm:scon`'s translator)
Kind: C
Fidelity: variant: uniform floor `ε` as a hypothesis (derived in the theorem of record); the earlier conditions are taken to be in the base process; the process is `DP ∪ prefixProcess ψ`
Hyps: (a) -/
theorem conditioned_learnedPast_of_floor (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (ψ : ℕ → Sentence) (hcode : MachineSentenceCodes ψ)
    (hpast : ∀ m n, m < n → ψ m ∈ DP.D n) (ε : ℚ) (hε : 0 < (ε : ℝ))
    (hfloor : ∀ n, (ε : ℝ) ≤ P n (ψ n)) :
    IsLogicalInductor (conditionedHistory P ψ) (DP.union (prefixProcess ψ)) := by
  obtain ⟨base⟩ := hLI.processComputable.nonemptyComputation
  obtain ⟨market⟩ := hLI.marketComputable.nonemptyComputation
  refine ⟨(ConditioningCompile.conditionedMarketComputation market ψ hcode).toComputable,
    (base.union (prefixProcessComputation ψ hcode)).toComputable, ?_⟩
  intro T hT hex
  obtain ⟨⟨L, hL⟩, hnb⟩ := hex
  have hpastHolds : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → ∀ i, i < n → v.Holds (ψ i) :=
    fun n v hv i hi => hv _ (hpast i n hi)
  -- the day-`n` translated trade is worth `0` in a world failing `ψ n`
  have hzero : ∀ n (v : PCWorld), ¬ v.Holds (ψ n) →
      ((T.conditionedTranslation ψ ε).strat n).value P v.payout = 0 := by
    intro n v hv
    change ((T.strat n).separatedLocallyGatedConditionalContract ψ ε
      (conditioningBudget n)).value P v.payout = 0
    rw [Strategy.separatedLocallyGatedConditionalContract_value ψ ε (conditioningBudget n)
      (T.strat n) P v.payout hε hfloor]
    exact Strategy.locallyGatedConditionalContract_value_eq_zero_of_not_holds (T.strat n) P ψ hε
      hfloor (conditioningBudget n) v hv
  apply hLI.noExploit (T.conditionedTranslation ψ ε)
    (CondStep.conditionedTranslation_preserves_ec ψ hcode ε T hT)
  refine exploits_of_bddBelow_of_unbounded _ _ _ (max (1 - L) 0) ?_ ?_
  · rintro x ⟨n, v, hv, rfl⟩
    have h3 : 1 - L ≤ max (1 - L) 0 := le_max_left _ _
    by_cases hn : v.Holds (ψ n)
    · have hall : ∀ i, i ≤ n → v.Holds (ψ i) := fun i hi =>
        (Nat.lt_or_eq_of_le hi).elim (hpastHolds n v hv i) (fun h => h ▸ hn)
      have h1 := T.conditionedTranslation_netWorth_lower P ψ hε hfloor v n hall
      have h2 := hL ⟨n, v, (consistentWith_prefixUnion_iff DP ψ v n).mpr ⟨hv, hall⟩, rfl⟩
      linarith
    · cases n with
      | zero =>
          rw [Trader.netWorth, Finset.sum_range_one, hzero 0 v hn]
          have : (0 : ℝ) ≤ max (1 - L) 0 := le_max_right _ _
          linarith
      | succ m =>
          have hall : ∀ i, i ≤ m → v.Holds (ψ i) := fun i hi =>
            hpastHolds (m + 1) v hv i (Nat.lt_succ_of_le hi)
          have hvm : v.ConsistentWith (DP.D m) := fun φ hφ => hv φ (DP.mono_le (Nat.le_succ m) hφ)
          have h1 := T.conditionedTranslation_netWorth_lower P ψ hε hfloor v m hall
          have h2 := hL ⟨m, v, (consistentWith_prefixUnion_iff DP ψ v m).mpr ⟨hvm, hall⟩, rfl⟩
          have hsplit : (T.conditionedTranslation ψ ε).netWorth P v (m + 1) =
              (T.conditionedTranslation ψ ε).netWorth P v m +
                ((T.conditionedTranslation ψ ε).strat (m + 1)).value P v.payout := by
            unfold Trader.netWorth
            exact Finset.sum_range_succ _ _
          rw [hsplit, hzero (m + 1) v hn, add_zero]
          linarith
  · intro B
    obtain ⟨x, ⟨n, v, hv, rfl⟩, hBx⟩ := not_bddAbove_iff.mp hnb (B + 1)
    obtain ⟨hv₁, hall⟩ := (consistentWith_prefixUnion_iff DP ψ v n).mp hv
    refine ⟨_, ⟨n, v, hv₁, rfl⟩, ?_⟩
    have h1 := T.conditionedTranslation_netWorth_lower P ψ hε hfloor v n hall
    linarith

/-- **In the learned-past reading the day's condition is believed in the limit**: `ψ n` lies in
stage `n + 1` (`hpast`), so it holds in every world consistent with the completed theory, and
FAF's provability induction (`lic_provind_true`, `thm:provind`) gives `P n (ψ n) → 1`. This is why
the floor of `conditioned_learnedPast_of_floor` is automatic from some day on (both round-2
audits' probes).
Source: [[corr-legit-neg-inventory]] 063(a), learned-past reading; FAF `lic_provind_true` (`thm:provind`)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem learnedPast_tendsto_one (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ψ : ℕ → Sentence) (hcode : MachineSentenceCodes ψ)
    (hpast : ∀ m n, m < n → ψ m ∈ DP.D n) :
    Tendsto (fun n => P n (ψ n)) atTop (𝓝 1) := by
  have h : AsympEq (fun n => P n (ψ n)) (fun _ => 1) :=
    lic_provind_true P DP ψ hcode
      (fun n v hv => hv.holds_of_mem_stage ⟨n + 1, hpast n (n + 1) (Nat.lt_succ_self n)⟩) hworld
  have h' : Tendsto (fun n => (P n (ψ n) - 1) + 1) atTop (𝓝 (0 + 1)) :=
    Filter.Tendsto.add_const 1 (h : Tendsto (fun n => P n (ψ n) - 1) atTop (𝓝 0))
  simpa using h'

/-- Finitely many positive reals have a positive common lower bound.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exists_pos_lb_of_pos (f : ℕ → ℝ) (hf : ∀ n, 0 < f n) (N : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n, n < N → δ ≤ f n := by
  induction N with
  | zero => exact ⟨1, one_pos, fun n hn => absurd hn (Nat.not_lt_zero n)⟩
  | succ N ih =>
      obtain ⟨δ, hδ, hle⟩ := ih
      refine ⟨min δ (f N), lt_min hδ (hf N), fun n hn => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | rfl
      · exact (min_le_left _ _).trans (hle n h)
      · exact min_le_right _ _

/-- **063(a) in the learned-past reading, proved with the floor derived (theorem of record,
repair round 2)**: for an inductor `P` over a stage-consistent `DP` and an e.c. condition family
`ψ` whose earlier members are in the base process (`ψ m ∈ DP.D n` for `m < n` — the realized
action of each day, asserted by the base process the next day), if no day's price of its own
condition is exactly `0`, the market conditioned day `n` on `ψ n` is an inductor over the pinned
process `DP ∪ prefixProcess ψ`. The uniform floor of `conditioned_learnedPast_of_floor` is
manufactured: `1/2` from the provability-induction day on (`learnedPast_tendsto_one`), the
minimum of the finitely many earlier positive prices before it, and a rational below both. So in
this reading the source's "price floor `ε_n` with `Σ` constraints" is not a condition that needs
conjecturing — the price tends to `1` — and the conditions are the realized actions, which need no
exploration: this is **not** the source's use case (unchosen candidates kept unrefuted by
exploration; see `Candidate.lean`), and it settles 063(a) only for a reading the source does not
make. Adopted from the adversarial round-2 probe `AdvLearnedPastPositivity.lean`.
Source: [[corr-legit-neg-inventory]] 063(a) (E7 escape (ii)), learned-past reading; FAF `Trader.conditionedTranslation`, `lic_provind_true`
Kind: C
Fidelity: variant: the earlier conditions are taken to be in the base process; the process is `DP ∪ prefixProcess ψ`; per-day positivity in place of the source's floor (the floor is derived, not assumed)
Hyps: (a) -/
theorem conditioned_learnedPast_isLogicalInductor (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ψ : ℕ → Sentence) (hcode : MachineSentenceCodes ψ)
    (hpast : ∀ m n, m < n → ψ m ∈ DP.D n) (hpos : ∀ n, 0 < P n (ψ n)) :
    IsLogicalInductor (conditionedHistory P ψ) (DP.union (prefixProcess ψ)) := by
  have hT := learnedPast_tendsto_one P DP hworld ψ hcode hpast
  have he : ∀ᶠ n in atTop, (1 / 2 : ℝ) < P n (ψ n) :=
    hT.eventually (eventually_gt_nhds (by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  obtain ⟨δ, hδ, hle⟩ := exists_pos_lb_of_pos (fun n => P n (ψ n)) hpos N
  obtain ⟨ε, hε0, hεδ⟩ := exists_rat_btwn (lt_min hδ (by norm_num : (0 : ℝ) < 1 / 2))
  refine conditioned_learnedPast_of_floor P DP ψ hcode hpast ε hε0 fun n => ?_
  by_cases hn : n < N
  · exact hεδ.le.trans ((min_le_left _ _).trans (hle n hn))
  · exact hεδ.le.trans ((min_le_right _ _).trans (hN n (not_lt.mp hn)).le)

/-- **The learned-past reading with no price hypothesis at all**: every inductor over a
stage-consistent `DP` has a finite patch (li-projection's `prescribe_finiteSupport`, FAF's
corrected `thm:ifp`) with a uniform floor `1/2` on the family and whose day-wise conditioned
market is an inductor over `DP ∪ prefixProcess ψ` — the days before the provability-induction day
are patched at the coordinates `(n, ψ n)`. Adopted from the fidelity round-2 probe
`LearnedPastFloorFree.lean`.
Source: [[corr-legit-neg-inventory]] 063(a), learned-past reading; li-projection `prescribe_finiteSupport`
Kind: C
Fidelity: variant: as `conditioned_learnedPast_isLogicalInductor`, for a finite patch of `P`
Hyps: (a) -/
theorem conditioned_learnedPast_patch (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ψ : ℕ → Sentence) (hcode : MachineSentenceCodes ψ)
    (hpast : ∀ m n, m < n → ψ m ∈ DP.D n) :
    ∃ P' : History, IsLogicalInductor P' DP ∧
      (∀ n, ((1 / 2 : ℚ) : ℝ) ≤ P' n (ψ n)) ∧
      IsLogicalInductor (conditionedHistory P' ψ) (DP.union (prefixProcess ψ)) := by
  have hT := learnedPast_tendsto_one P DP hworld ψ hcode hpast
  have he : ∀ᶠ n in atTop, (1 / 2 : ℝ) < P n (ψ n) :=
    hT.eventually (eventually_gt_nhds (by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  let S : Finset (ℕ × Sentence) := (Finset.range N).image (fun n => (n, ψ n))
  let t : ℕ → Sentence → ℚ := fun _ _ => 1 / 2
  have hLI' : IsLogicalInductor (patch P S t) DP :=
    prescribe_finiteSupport P DP S t (fun p _ => by norm_num [t])
  have hfloor : ∀ n, ((1 / 2 : ℚ) : ℝ) ≤ patch P S t n (ψ n) := by
    intro n
    by_cases hn : n < N
    · have hmem : (n, ψ n) ∈ S := by
        simp only [S, Finset.mem_image, Finset.mem_range]
        exact ⟨n, hn, rfl⟩
      rw [patch_mem P S t hmem]
    · have hnot : (n, ψ n) ∉ S := by
        simp only [S, Finset.mem_image, Finset.mem_range, not_exists, not_and]
        intro a ha hae
        have : a = n := (Prod.mk.inj hae).1
        omega
      rw [patch_notMem P S t hnot]
      push_cast
      exact (hN n (not_lt.mp hn)).le
  refine ⟨patch P S t, hLI', hfloor, ?_⟩
  haveI := hLI'
  exact conditioned_learnedPast_of_floor (patch P S t) DP ψ hcode hpast (1 / 2) (by norm_num)
    hfloor

/-! ## (S) The day's own condition over an accumulating process: refuted -/

/-- The alternating condition family: the atom `a` on even days, the atom `b` on odd days. A
decision sequence's shape (a different condition each day, all jointly consistent) in its simplest
instance.
Source: none: infrastructure (the counterexample family for 063(a)'s single-condition reading)
Kind: D
Fidelity: n/a -/
def altCondition (a b : ℕ) (n : ℕ) : Sentence :=
  if n % 2 = 0 then Formula.atom a else Formula.atom b

/-- `altCondition` on an even day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma altCondition_even {a b n : ℕ} (h : n % 2 = 0) : altCondition a b n = Formula.atom a := by
  simp [altCondition, h]

/-- `altCondition` on an odd day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma altCondition_odd {a b n : ℕ} (h : n % 2 = 1) : altCondition a b n = Formula.atom b := by
  simp [altCondition, h]

/-- The alternating family is efficiently computable in FAF's sense (`MachineSentenceCodes`): a
two-way dispatch on the parity ruler between two constant families.
Source: none: infrastructure (FAF's `MachineSentenceCodes.ifZero`, `.const`; `unaryRuler_mod_two`)
Kind: L
Fidelity: n/a -/
theorem altCondition_codes (a b : ℕ) : MachineSentenceCodes (altCondition a b) :=
  (MachineSentenceCodes.ifZero (MachineSentenceCodes.const (Formula.atom a))
    (MachineSentenceCodes.const (Formula.atom b)) unaryRuler_mod_two).of_eq (fun _ => rfl)

/-- The odd-day coefficient: `−1` on odd days, `0` on even days.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def oddCoeff (n : ℕ) : ℚ := if n % 2 = 0 then 0 else -1

/-- `oddCoeff` is nonpositive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma oddCoeff_nonpos (n : ℕ) : (oddCoeff n : ℝ) ≤ 0 := by
  unfold oddCoeff; split_ifs <;> norm_num

/-- `oddCoeff` on an odd day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma oddCoeff_odd {n : ℕ} (h : n % 2 = 1) : oddCoeff n = -1 := by
  simp [oddCoeff, h]

/-- **The odd-day seller**: sell one share of `φ` on every odd day, nothing on even days. One trade
per day with a constant (price-free) coefficient, so its certificate is FAF's single-trade
constructor on the parity dispatch, as for `parityTrader`.
Source: none: infrastructure (the exploiting trader of `conditioned_alternating_exploited`)
Kind: D
Fidelity: n/a -/
def oddSeller (φ : Sentence) : Trader where
  strat n := { trades := [(EF.const (oddCoeff n), φ)], rank_le := by simp }

/-- The odd-day seller's day-`n` value.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma oddSeller_value (φ : Sentence) (S : History) (w : Sentence → ℝ) (n : ℕ) :
    ((oddSeller φ).strat n).value S w = (oddCoeff n : ℝ) * (w φ - S n φ) := by
  simp [oddSeller, Strategy.value]

/-- The odd-day seller's net worth is the sum of its daily values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma oddSeller_netWorth (φ : Sentence) (S : History) (v : PCWorld) (n : ℕ) :
    (oddSeller φ).netWorth S v n =
      ∑ i ∈ Finset.range (n + 1), (oddCoeff i : ℝ) * (v.payout φ - S i φ) := by
  unfold Trader.netWorth
  exact Finset.sum_congr rfl fun i _ => oddSeller_value φ S v.payout i

/-- The odd-day seller is efficiently computable (FAF's single-trade constructor on the constant
sentence and the parity dispatch between two constant coefficient words).
Source: none: infrastructure (as `parityTrader_ec`)
Kind: L
Fidelity: n/a -/
theorem oddSeller_ec (φ : Sentence) : EfficientlyComputable (oddSeller φ) := by
  refine EfficientlyComputable.ofSingleTradeBlocksBig _ (fun n => EF.const (oddCoeff n))
    (fun _ => φ) ?_ (fun _ => trivial) (MachineSentenceCodes.const φ) (fun _ => rfl)
  have h0 := MachineTokenStream.const (EF.const 0).serialize
  have h1 := MachineTokenStream.const (EF.const (-1)).serialize
  refine (MachineTokenStream.ifZero h0 h1 unaryRuler_mod_two).of_eq (fun n => ?_)
  simp only [oddCoeff]
  by_cases h2 : n % 2 = 0 <;> simp [h2]

/-- The capped conditional quote lies in `[0,1]` whenever the valuation does.
Source: none: infrastructure (from `conditionalQuote_dichotomy`)
Kind: L
Fidelity: n/a -/
theorem conditionalQuote_mem_Icc' (V : Valuation) (hV : ∀ χ, 0 ≤ V χ ∧ V χ ≤ 1) (φ ψ : Sentence) :
    0 ≤ conditionalQuote V φ ψ ∧ conditionalQuote V φ ψ ≤ 1 := by
  rcases conditionalQuote_dichotomy V hV φ ψ with ⟨-, h⟩ | ⟨hpos, h⟩
  · rw [h]; exact ⟨zero_le_one, le_rfl⟩
  · rw [h]; exact ⟨le_min (div_nonneg (hV _).1 hpos.le) zero_le_one, min_le_right _ _⟩

/-- **The capped conditional quote is at least the price of the conjunction**: with prices in
`[0,1]`, `conditionalQuote V φ ψ ≥ V (φ ⋏ ψ)` — the cap gives `1`, and the ratio divides by a
denominator `≤ 1`. This is the one-line fact that makes conditioning on `b` alone unable to hide
`∼a ⋏ b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem conditionalQuote_ge_and (V : Valuation) (hV : ∀ χ, 0 ≤ V χ ∧ V χ ≤ 1) (φ ψ : Sentence) :
    V (φ ⋏ ψ) ≤ conditionalQuote V φ ψ := by
  rcases conditionalQuote_dichotomy V hV φ ψ with ⟨-, h⟩ | ⟨hpos, h⟩
  · rw [h]; exact (hV _).2
  · rw [h]
    refine le_min ?_ (hV _).2
    rw [le_div_iff₀ hpos]
    exact mul_le_of_le_one_right (hV _).1 (hV ψ).2

/-- Over a process free of two distinct atoms, a world refuting `a` and holding `b` is plausible at
every stage (the premise shape of `lic_nonDogmatism` at `∼a ⋏ b`).
Source: none: infrastructure (li-projection's `consistentWith_setAtom_iff`, twice)
Kind: L
Fidelity: n/a -/
theorem exists_consistent_holds_neg_and_atom {a b : ℕ} {DP : DeductiveProcess} (hab : a ≠ b)
    (ha : AtomFreeProcess a DP) (hb : AtomFreeProcess b DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) :
    ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds ((∼ Formula.atom a) ⋏ Formula.atom b) := by
  obtain ⟨v, hv⟩ := hworld n
  refine ⟨setAtom (setAtom v a false) b true,
    (consistentWith_setAtom_iff hb _ true n).mp ((consistentWith_setAtom_iff ha v false n).mp hv),
    ?_⟩
  rw [PCWorld.holds_and, PCWorld.holds_neg, PCWorld.holds_atom, PCWorld.holds_atom]
  simp [setAtom, hab]

/-- **The single-condition reading of 063(a) is false over every accumulating process.** For every
inductor `P` over a process `DP` with a consistent world at every stage and two distinct fresh
atoms `a ≠ b`, and every process `DP'` that contains the alternating condition of the day at every
stage and has a consistent world at every stage, the odd-day seller of `∼a` exploits the market
conditioned day `n` on `altCondition a b n`. Why: `DP'` contains `a` from stage `0`, so every
plausible world holds `a` and the sold share of `∼a` pays `0`; on odd days the market conditions on
`b` alone and quotes `∼a` at least `P_n(∼a ⋏ b)` (`conditionalQuote_ge_and`), which FAF's
non-dogmatism keeps above some `ε > 0` from some day on because `∼a ⋏ b` stays plausible under
`DP`. The net worth is `Σ_{odd k ≤ n} P_k(∼a | b) ≥ 0` on every plausible world and grows at least
linearly. No floor or inclusion `DP ⊆ DP'` is needed; (B6)'s floor and inclusion hypotheses only
make the statement's instance *harder* to escape.
Source: [[corr-legit-neg-inventory]] 063(a) (E7 escape (ii)), single-condition reading over an accumulating process (the former OPEN (B6)'s shape with the audits' non-degeneracy clause)
Kind: P
Fidelity: exact for the alternating instance of (S) — enough for the `¬ ∀`, not a theory of (S): the exploit bites because the alternating family makes an earlier condition recur as a fixed sentence with a non-dogmatism floor over `DP`; a distinct condition per day would need a floor along a varying family, not in hand. (S) is the mismatch reading (the base inductor's process lacks the earlier conditions, `DP'` has them); the surviving neighbours are (G), (L) above and (C) in `Candidate.lean`
Hyps: (a) -/
theorem conditioned_alternating_exploited (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (a b : ℕ) (hab : a ≠ b) (ha : AtomFreeProcess a DP) (hb : AtomFreeProcess b DP)
    (DP' : DeductiveProcess) (hmem : ∀ n, altCondition a b n ∈ DP'.D n)
    (hcons' : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP'.D n)) :
    (oddSeller (∼ Formula.atom a)).Exploits (conditionedHistory P (altCondition a b)) DP' := by
  set S := conditionedHistory P (altCondition a b) with hS
  have hP := IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  have hholds : ∀ n (v : PCWorld), v.ConsistentWith (DP'.D n) → v.Holds (Formula.atom a) := by
    intro n v hv
    have h0 : altCondition a b 0 ∈ DP'.D n := DP'.mono_le (Nat.zero_le n) (hmem 0)
    rw [altCondition_even (by norm_num)] at h0
    exact hv _ h0
  have hpay : ∀ n (v : PCWorld), v.ConsistentWith (DP'.D n) →
      v.payout (∼ Formula.atom a) = 0 := by
    intro n v hv
    rw [PCWorld.payout, if_neg]
    rw [PCWorld.holds_neg]
    exact fun h => h (hholds n v hv)
  have hSq : ∀ n χ, 0 ≤ S n χ ∧ S n χ ≤ 1 := fun n χ =>
    conditionalQuote_mem_Icc' (P n) (hP n) χ _
  have hterm : ∀ n (v : PCWorld), v.ConsistentWith (DP'.D n) → ∀ i,
      0 ≤ (oddCoeff i : ℝ) * (v.payout (∼ Formula.atom a) - S i (∼ Formula.atom a)) := by
    intro n v hv i
    rw [hpay n v hv, zero_sub, mul_neg, neg_nonneg]
    exact mul_nonpos_of_nonpos_of_nonneg (oddCoeff_nonpos i) (hSq i _).1
  obtain ⟨ε, hε, hev⟩ := lic_nonDogmatism P DP ((∼ Formula.atom a) ⋏ Formula.atom b)
    (exists_consistent_holds_neg_and_atom hab ha hb hworld)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  have hodd : ∀ i, N₀ ≤ i → i % 2 = 1 → ε ≤ S i (∼ Formula.atom a) := by
    intro i hi h2
    calc ε ≤ P i ((∼ Formula.atom a) ⋏ Formula.atom b) := hN₀ i hi
      _ ≤ conditionalQuote (P i) (∼ Formula.atom a) (Formula.atom b) :=
          conditionalQuote_ge_and (P i) (hP i) _ _
      _ = S i (∼ Formula.atom a) := by rw [hS, conditionedHistory, altCondition_odd h2]
  refine exploits_of_bddBelow_of_unbounded _ _ _ 0 ?_ ?_
  · rintro x ⟨n, v, hv, rfl⟩
    rw [oddSeller_netWorth, neg_zero]
    exact Finset.sum_nonneg fun i _ => hterm n v hv i
  · intro B
    obtain ⟨j, hj⟩ := exists_nat_gt (B / ε)
    have hjε : B < j * ε := by rwa [div_lt_iff₀ hε] at hj
    obtain ⟨v, hv⟩ := hcons' (2 * (N₀ + j) + 1)
    refine ⟨_, ⟨2 * (N₀ + j) + 1, v, hv, rfl⟩, ?_⟩
    rw [oddSeller_netWorth]
    have key : ∀ k : ℕ, (k : ℝ) * ε ≤ ∑ i ∈ Finset.range (2 * (N₀ + k) + 2),
        (oddCoeff i : ℝ) * (v.payout (∼ Formula.atom a) - S i (∼ Formula.atom a)) := by
      intro k
      induction k with
      | zero =>
          simp only [Nat.cast_zero, zero_mul]
          exact Finset.sum_nonneg fun i _ => hterm _ v hv i
      | succ k ih =>
          rw [show 2 * (N₀ + (k + 1)) + 2 = (2 * (N₀ + k) + 2) + 1 + 1 by ring,
            Finset.sum_range_succ, Finset.sum_range_succ]
          have h1 := hterm _ v hv (2 * (N₀ + k) + 2)
          have h2 : ε ≤ (oddCoeff (2 * (N₀ + k) + 2 + 1) : ℝ) *
              (v.payout (∼ Formula.atom a) - S (2 * (N₀ + k) + 2 + 1) (∼ Formula.atom a)) := by
            rw [hpay _ v hv, oddCoeff_odd (by omega)]
            have := hodd (2 * (N₀ + k) + 2 + 1) (by omega) (by omega)
            push_cast
            linarith
          push_cast
          linarith
    calc B < j * ε := hjε
      _ ≤ _ := by
        have := key j
        rwa [show 2 * (N₀ + j) + 2 = 2 * (N₀ + j) + 1 + 1 by ring] at this

/-- The single-condition reading, as non-inductor-hood: through `noExploit` at the odd-day seller
(which is e.c., `oddSeller_ec`), so the conclusion is carried by the exploitation and not by any
failure of `DP'`'s computability.
Source: [[corr-legit-neg-inventory]] 063(a), single-condition reading
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem conditioned_alternating_not_isLogicalInductor (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (a b : ℕ) (hab : a ≠ b) (ha : AtomFreeProcess a DP) (hb : AtomFreeProcess b DP)
    (DP' : DeductiveProcess) (hmem : ∀ n, altCondition a b n ∈ DP'.D n)
    (hcons' : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP'.D n)) :
    ¬ IsLogicalInductor (conditionedHistory P (altCondition a b)) DP' :=
  fun hLI' => hLI'.noExploit _ (oddSeller_ec _)
    (conditioned_alternating_exploited P DP hworld a b hab ha hb DP' hmem hcons')

/-! ## The floor is inhabited: a finite patch of any inductor -/

/-- **Any inductor can be given a uniform floor on two fresh atoms by a finite patch**: the limits
on `a` and `b` are interior (li-projection's `limitingBelief_atom_mem_Ioo`), so the prices exceed
half the limits from some day `N` on, and the finitely many coordinates `(n, a)`, `(n, b)` for
`n < N` are patched to `1/2` — an inductor by FAF's corrected `thm:ifp` through li-projection's
`prescribe_finiteSupport`. This inhabits the floor hypothesis of the refuted universal
`conditioned_dayIndexed_floor_false` (so the refutation bites on a genuine inductor) and the floor
hypothesis of the candidate reading's `conditioned_candidate_not_gatedExploits` on the alternating
family (`paperCandidate_not_gatedExploits`); it says nothing about the source's conjecture itself.
Source: mandate T6.2 (063(a)'s hypotheses must be inhabited for the refutation to bite); li-projection `prescribe_finiteSupport`, `limitingBelief_atom_mem_Ioo`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem exists_inductor_floor_two_atoms (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (a b : ℕ) (ha : AtomFreeProcess a DP) (hb : AtomFreeProcess b DP) :
    ∃ P' : History, IsLogicalInductor P' DP ∧ ∃ ε : ℝ, 0 < ε ∧
      (∀ n, ε ≤ P' n (Formula.atom a)) ∧ (∀ n, ε ≤ P' n (Formula.atom b)) := by
  have hLa := limitingBelief_atom_mem_Ioo P DP hworld a ha
  have hLb := limitingBelief_atom_mem_Ioo P DP hworld b hb
  have hTa := lic_limitingBelief_tendsto P DP hworld (Formula.atom a)
  have hTb := lic_limitingBelief_tendsto P DP hworld (Formula.atom b)
  set La := limitingBelief P (Formula.atom a) with hLa_def
  set Lb := limitingBelief P (Formula.atom b) with hLb_def
  have hea : ∀ᶠ n in atTop, La / 2 < P n (Formula.atom a) :=
    hTa.eventually (eventually_gt_nhds (by linarith [hLa.1]))
  have heb : ∀ᶠ n in atTop, Lb / 2 < P n (Formula.atom b) :=
    hTb.eventually (eventually_gt_nhds (by linarith [hLb.1]))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hea.and heb)
  set S : Finset (ℕ × Sentence) :=
    (Finset.range N) ×ˢ ({Formula.atom a, Formula.atom b} : Finset Sentence) with hS
  set t : ℕ → Sentence → ℚ := fun _ _ => 1 / 2 with ht
  refine ⟨patch P S t, prescribe_finiteSupport P DP S t (fun p _ => by norm_num [ht]),
    min (min (La / 2) (Lb / 2)) (1 / 2),
    lt_min (lt_min (by linarith [hLa.1]) (by linarith [hLb.1])) (by norm_num), ?_, ?_⟩
  · intro n
    by_cases hn : n < N
    · rw [patch_mem P S t (by simp [hS, hn])]
      calc min (min (La / 2) (Lb / 2)) (1 / 2) ≤ 1 / 2 := min_le_right _ _
        _ = ((t n (Formula.atom a) : ℚ) : ℝ) := by norm_num [ht]
    · rw [patch_notMem P S t (by simp [hS, hn])]
      calc min (min (La / 2) (Lb / 2)) (1 / 2) ≤ min (La / 2) (Lb / 2) := min_le_left _ _
        _ ≤ La / 2 := min_le_left _ _
        _ ≤ _ := (hN n (not_lt.mp hn)).1.le
  · intro n
    by_cases hn : n < N
    · rw [patch_mem P S t (by simp [hS, hn])]
      calc min (min (La / 2) (Lb / 2)) (1 / 2) ≤ 1 / 2 := min_le_right _ _
        _ = ((t n (Formula.atom b) : ℚ) : ℝ) := by norm_num [ht]
    · rw [patch_notMem P S t (by simp [hS, hn])]
      calc min (min (La / 2) (Lb / 2)) (1 / 2) ≤ min (La / 2) (Lb / 2) := min_le_left _ _
        _ ≤ Lb / 2 := min_le_right _ _
        _ ≤ _ := (hN n (not_lt.mp hn)).2.le

/-- **The former OPEN (B6), restated with the audits' non-degeneracy clause, is false.** Given any
inductor over a process with a consistent world at every stage and two distinct fresh atoms, it
is not the case that every inductor `Q`, e.c. condition family `ψ` with a uniform price floor and
per-day plausibility admits a stage-consistent process `DP' ⊇ DQ` containing the day's condition
at every stage over which `conditionedHistory Q ψ` is an inductor. Instance: the floor-patched
inductor of `exists_inductor_floor_two_atoms` with the alternating family, against
`conditioned_alternating_not_isLogicalInductor`. The surviving "inductor over a process" readings
of 063(a) are (G) (`conditioned_prefix_isLogicalInductor`, the inventory's covered case, no floor
needed) and (L) (`conditioned_learnedPast_isLogicalInductor`, where the floor is automatic); the
source's own candidate reading is `Candidate.lean`'s gated non-exploitation.
Source: [[corr-legit-neg-inventory]] 063(a); the round-1 audits' repair of the former `conditioned_dayIndexed_floor`
Kind: C
Fidelity: exact (the negated statement is the former OPEN's with `∀ n, ∃ v, v.ConsistentWith (DP'.D n)` added to its conclusion)
Hyps: (a) -/
theorem conditioned_dayIndexed_floor_false (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (a b : ℕ) (hab : a ≠ b) (ha : AtomFreeProcess a DP) (hb : AtomFreeProcess b DP) :
    ¬ ∀ (Q : History) (DQ : DeductiveProcess) [IsLogicalInductor Q DQ] (ψ : ℕ → Sentence),
        MachineSentenceCodes ψ → ∀ ε : ℝ, 0 < ε → (∀ n, ε ≤ Q n (ψ n)) →
        (∀ n, ∃ v : PCWorld, v.ConsistentWith (DQ.D n) ∧ v.Holds (ψ n)) →
        ∃ DP' : DeductiveProcess, (∀ n, DQ.D n ⊆ DP'.D n) ∧ (∀ n, ψ n ∈ DP'.D n) ∧
          (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP'.D n)) ∧
          IsLogicalInductor (conditionedHistory Q ψ) DP' := by
  intro H
  obtain ⟨P', hP', ε, hε, hfa, hfb⟩ := exists_inductor_floor_two_atoms P DP hworld a b ha hb
  haveI := hP'
  obtain ⟨DP', -, hmem, hcons', hLI'⟩ := H P' DP (altCondition a b) (altCondition_codes a b) ε hε
    (fun n => by
      unfold altCondition
      split_ifs
      · exact hfa n
      · exact hfb n)
    (fun n => by
      unfold altCondition
      split_ifs
      · exact exists_consistent_holds_atom ha hworld n
      · exact exists_consistent_holds_atom hb hworld n)
  exact conditioned_alternating_not_isLogicalInductor P' DP hworld a b hab ha hb DP' hmem hcons'
    hLI'

/-! ## (B3) sharpened: every e.c. selling schedule on a refuted sentence is summable -/

/-- The schedule coefficient: `0` before day `N`, `−Q n` from day `N` on.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def scheduleCoeff (Q : ℕ → ℚ) (N n : ℕ) : ℚ := if n < N then 0 else -Q n

/-- **The selling schedule**: sell `Q n` shares of `ψ` on each day `n ≥ N`, nothing before. One
price-free trade per day (so FAF's single-trade constructor certifies it whenever the coefficient
stream is a machine token stream; the certificate is a hypothesis below).
Source: adversarial audit r1 N2 (the generalisation of li-projection's `sellDaily`)
Kind: D
Fidelity: n/a -/
def sellSchedule (ψ : Sentence) (Q : ℕ → ℚ) (N : ℕ) : Trader where
  strat n := { trades := [(EF.const (scheduleCoeff Q N n), ψ)], rank_le := by simp }

/-- The schedule's net worth is the sum of its daily values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sellSchedule_netWorth (ψ : Sentence) (Q : ℕ → ℚ) (N : ℕ) (S : History) (v : PCWorld)
    (n : ℕ) :
    (sellSchedule ψ Q N).netWorth S v n =
      ∑ i ∈ Finset.range (n + 1), (scheduleCoeff Q N i : ℝ) * (v.payout ψ - S i ψ) := by
  unfold Trader.netWorth
  exact Finset.sum_congr rfl fun i _ => by simp [sellSchedule, Strategy.value]

/-- **Every e.c. selling schedule on a stage-refuted sentence has summable proceeds**: for an
inductor over `DP`, a sentence `ψ` refuted at stage `N` (every world consistent with `DP.D N`
refutes it) and a nonnegative quantity stream `Q` whose selling schedule is efficiently
computable, `Σ_n Q_n · P_n(ψ) < ∞`. The schedule's net worth on every plausible world is exactly
`Σ_{N ≤ m ≤ n} Q_m P_m(ψ) ≥ 0` (the sold shares pay `0` from stage `N` on), so divergence would
exploit. li-projection's `summable_price_neg_of_mem_stage` is the case `Q ≡ 1`; a geometrically
growing e.c. `Q` (FAF's `EF` has a sharing `letE`, so `2^{2^n}`-sized constants are polynomial in
the day) shows a positive price on a refuted sentence must decay faster than the reciprocal of
every e.c. schedule — the obstruction (B3)'s docstring now states. The certificate `hec` is the
quantifier "e.c. schedule", not a squeeze: the conclusion is about `P`.
Source: adversarial audit r1 N2; [[corr-legit-neg-inventory]] 063(c) (the free horn's positivity); li-projection `summable_price_neg_of_mem_stage`
Kind: P
Fidelity: stronger: arbitrary nonnegative e.c. schedule (li-projection's is `Q ≡ 1`)
Hyps: (a) (`hec` is the schedule's own certificate, the quantifier of the claim) -/
theorem summable_schedule_mul_price_of_refuted (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
    (ψ : Sentence) (N : ℕ) (href : ∀ v : PCWorld, v.ConsistentWith (DP.D N) → ¬ v.Holds ψ)
    (Q : ℕ → ℚ) (hQ : ∀ n, 0 ≤ Q n) (hec : EfficientlyComputable (sellSchedule ψ Q N)) :
    Summable (fun n => (Q n : ℝ) * P n ψ) := by
  have hP := IsLogicalInductor.price_mem_Icc (P := P) (DP := DP)
  set w : ℕ → ℝ := fun n => if n < N then 0 else (Q n : ℝ) * P n ψ with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n => by
    simp only [hw]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (by exact_mod_cast hQ n) (hP n ψ).1
  have hterm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → ∀ i ∈ Finset.range (n + 1),
      (scheduleCoeff Q N i : ℝ) * (v.payout ψ - P i ψ) = w i := by
    intro n v hv i hi
    simp only [hw, scheduleCoeff]
    by_cases hiN : i < N
    · simp [hiN]
    · have hNn : N ≤ n := by rw [Finset.mem_range] at hi; omega
      have hvψ : ¬ v.Holds ψ := href v (fun φ hφ => hv φ (DP.mono_le hNn hφ))
      simp only [if_neg hiN, PCWorld.payout, if_neg hvψ]
      push_cast
      ring
  have hgated : Summable w := by
    by_contra hns
    have hunb : ∀ B : ℝ, ∃ m, B < ∑ i ∈ Finset.range m, w i := by
      intro B
      by_contra hall
      push Not at hall
      exact hns (summable_of_sum_range_le hw0 hall)
    apply hLI.noExploit _ hec
    refine exploits_of_bddBelow_of_unbounded _ _ _ 0 ?_ ?_
    · rintro x ⟨n, v, hv, rfl⟩
      rw [sellSchedule_netWorth, Finset.sum_congr rfl (hterm n v hv), neg_zero]
      exact Finset.sum_nonneg fun i _ => hw0 i
    · intro B
      obtain ⟨m, hm⟩ := hunb B
      obtain ⟨v, hv⟩ := hworld m
      refine ⟨_, ⟨m, v, hv, rfl⟩, ?_⟩
      rw [sellSchedule_netWorth, Finset.sum_congr rfl (hterm m v hv)]
      calc B < ∑ i ∈ Finset.range m, w i := hm
        _ ≤ ∑ i ∈ Finset.range (m + 1), w i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ m))
            (fun i _ _ => hw0 i)
  have h1 := (summable_nat_add_iff N).mpr hgated
  refine (summable_nat_add_iff N).mp (h1.congr fun n => ?_)
  simp only [hw]
  rw [if_neg (by omega)]

/-- A constant selling schedule is efficiently computable: FAF's single-trade constructor on a
two-way dispatch ("before `N`" / "from `N` on") between two constant coefficient words.
Source: none: infrastructure (as `parityTrader_ec`)
Kind: L
Fidelity: n/a -/
theorem sellSchedule_const_ec (ψ : Sentence) (q : ℚ) (N : ℕ) :
    EfficientlyComputable (sellSchedule ψ (fun _ => q) N) := by
  refine EfficientlyComputable.ofSingleTradeBlocksBig _
    (fun n => EF.const (scheduleCoeff (fun _ => q) N n)) (fun _ => ψ) ?_ (fun _ => trivial)
    (MachineSentenceCodes.const ψ) (fun _ => rfl)
  have h0 := MachineTokenStream.const (EF.const 0).serialize
  have h1 := MachineTokenStream.const (EF.const (-q)).serialize
  refine (MachineTokenStream.ifZero h0 h1 (UnaryRuler.ite_lt_const N 0 1)).of_eq (fun n => ?_)
  simp only [scheduleCoeff]
  by_cases hn : n < N <;> simp [hn]

/-- The `Q ≡ 1` instance: an inductor's price on a stage-refuted sentence is summable — li-projection's
`summable_price_neg_of_mem_stage` under the semantic refutation hypothesis `href` (every world
consistent with `DP.D N` refutes `ψ`) instead of the syntactic `∼φ ∈ DP.D k`; the N− inhabitant of
`summable_schedule_mul_price_of_refuted`'s certificate hypothesis.
Source: li-projection `summable_price_neg_of_mem_stage`; [[corr-legit-neg-inventory]] 063(c)
Kind: C
Fidelity: variant: semantic refutation at a stage
Hyps: (a) -/
theorem summable_price_of_refuted (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (ψ : Sentence) (N : ℕ)
    (href : ∀ v : PCWorld, v.ConsistentWith (DP.D N) → ¬ v.Holds ψ) :
    Summable (fun n => P n ψ) := by
  have h := summable_schedule_mul_price_of_refuted P DP hworld ψ N href (fun _ => 1)
    (fun _ => zero_le_one) (sellSchedule_const_ec ψ 1 N)
  simpa using h

/-- **A finite patch gives any inductor a uniform rational floor on a sentence whose price tends to a
positive limit**: the price exceeds half the limit from some day on, and the finitely many earlier
coordinates are patched to `1/2` (li-projection's `prescribe_finiteSupport`, FAF's corrected
`thm:ifp`). The floor is rational so that it can feed FAF's conditioning translator.
Source: mandate T6.2 (063(a)'s floor hypothesis must be inhabited); li-projection `prescribe_finiteSupport`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem exists_patch_floor_of_tendsto (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (φ : Sentence) (L : ℝ) (hL : 0 < L)
    (hT : Tendsto (fun n => P n φ) atTop (𝓝 L)) :
    ∃ P' : History, IsLogicalInductor P' DP ∧
      ∃ ε : ℚ, 0 < (ε : ℝ) ∧ ∀ n, (ε : ℝ) ≤ P' n φ := by
  obtain ⟨r, hr0, hrL⟩ := exists_rat_btwn (half_pos hL)
  have he : ∀ᶠ n in atTop, (r : ℝ) < P n φ :=
    hT.eventually (eventually_gt_nhds (by linarith))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  set S : Finset (ℕ × Sentence) := (Finset.range N) ×ˢ ({φ} : Finset Sentence) with hS
  set t : ℕ → Sentence → ℚ := fun _ _ => 1 / 2 with ht
  refine ⟨patch P S t, prescribe_finiteSupport P DP S t (fun p _ => by norm_num [ht]),
    min r (1 / 2), ?_, fun n => ?_⟩
  · rw [Rat.cast_min]
    exact lt_min hr0 (by norm_num)
  · rw [Rat.cast_min]
    push_cast
    by_cases hn : n < N
    · rw [patch_mem P S t (by simp [hS, hn])]
      simp only [ht]
      push_cast
      exact min_le_right _ _
    · rw [patch_notMem P S t (by simp [hS, hn])]
      exact (min_le_left _ _).trans (hN n (not_lt.mp hn)).le

end Cleanroom.Li.LiSpliceCondition
