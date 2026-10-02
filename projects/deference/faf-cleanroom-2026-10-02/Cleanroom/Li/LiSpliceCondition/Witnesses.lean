import Cleanroom.Li.LiSpliceCondition.Splice
import Cleanroom.Li.LiSpliceCondition.Condition
import Cleanroom.Li.LiSpliceCondition.Utility
import Cleanroom.Li.LiSpliceCondition.Perturb
import Cleanroom.Li.LiSpliceCondition.Transfer
import Cleanroom.Li.LiProjection.Witnesses
import Cleanroom.Li.LiProjection.Market

/-!
# `li-splice-condition` · Witnesses: the N+ packages over `liaHistory (paperDP 𝗜𝚺₁)`

Package `Cleanroom.Li.LiSpliceCondition` ([[li-splice-condition-mandate]]), file 9 of the layout —
the only file importing `Construction.LIACompiler`/`Construction.Paper.TheoremDP` (through
li-projection's `Witnesses.lean`).

* **T1.4** The paper splice: `paperLow`/`paperHigh` are the projections of FAF's paper LIA on the
  splice atom `spliceAtomCode 0` at weights `3/10`, `7/10`. Their limits on `spliceAtom 0` are
  `3/10` and `7/10` **outright** (`paperSplice_limits`), their prices lie in `[0,1]`, they are
  computable markets, so the parity splice is exploited by the parity trader with per-pair gain
  `1/5` (`paperSplice_exploited`) and is not an inductor (`paperSplice_not_isLogicalInductor`),
  all **sorry-free**. The conjunct that the two components are inductors
  (`paperSplice_components_isLogicalInductor`) rests on li-projection's (A). The source's
  `q ↦ ¬q` automorphism was not needed: the projection gives both limits directly, and its
  "different limits unless `ℙ_∞` is exactly `σ`-symmetric" caveat is bypassed by choosing the
  weights.
* **T1.6** The harmonic refutation over `trivialDP` and over `paperDP 𝗜𝚺₁`.
* **T2.2/T2.4** `patchPolicy_paper`, `paperDefies`.
* **T3.1** `paperRefDP := (paperDP 𝗜𝚺₁).adjoinSentence (∼ spliceAtom 1)`: a real computable process
  with a consistent world at every stage (`paperRefDP_hworld`) in which `spliceAtom 1` is refuted
  *by the stage* at day `0`; every computable market is an inductor over
  `paperRefDP.adjoinSentence (spliceAtom 1)` (`paperConditioned_vacuous`, N+). The N− instance
  `ψ := ⊥` over `paperDP` (`paperConditioned_vacuous_bot`).
* **T3.2** `gridLUV` inhabits the injectivity hypothesis; `grid_three_tenths` is the fixture's
  `3/10` at precision `10`, as an exact rational.
* **T3.3** `paperTranslate`: the translation identities with a trader that actually trades a
  re-priced sentence.
* **T3.4/T3.5** `paperZeroOut`, `paperReprice`: the two horns over the LIA of `paperRefDP` (rest on
  the OPEN (B1), listed).
* **T4.2/T4.4** `paperGridLUV_not_valued`, `paperUndecidedPrior` (outright) and
  `undecided_limit_is_prior_inductors` (rests on (A)).
-/

namespace Cleanroom.Li.LiSpliceCondition

open LogicalInduction LO.Propositional Cleanroom.Li.LiProjection Cleanroom.Bli.BliFound
open Filter Topology

/-! ## The base inductor and freshness -/

/-- FAF's paper LIA over the paper process, the base of every witness here.
Source: mandate T1.4
Kind: D
Fidelity: exact -/
noncomputable abbrev paperBase : History := liaHistory (paperDP 𝗜𝚺₁)

/-- The base is a logical inductor (FAF's `LIA_is_logical_inductor`).
Source: mandate T1.4
Kind: L
Fidelity: exact -/
theorem paperBase_isLogicalInductor : IsLogicalInductor paperBase (paperDP 𝗜𝚺₁) :=
  LIA_is_logical_inductor _ (paperDP_computable _)

/-- Every splice atom is fresh for the paper process (`bli-found`'s `paperDP_cleanroomFree`).
Source: mandate header (freshness)
Kind: L
Fidelity: exact -/
theorem paperDP_spliceAtomFree (k : ℕ) : AtomFreeProcess (spliceAtomCode k) (paperDP 𝗜𝚺₁) :=
  atomFreeProcess_splice_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁) k

/-- The base's prices lie in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperBase_mem_Icc : ∀ n φ, 0 ≤ paperBase n φ ∧ paperBase n φ ≤ 1 :=
  paperBase_isLogicalInductor.marketComputable.1

/-! ## T1.4 The paper splice -/

/-- The low component: the projection of the paper LIA on `spliceAtomCode 0` at weight `3/10`.
Source: mandate T1.4
Kind: D
Fidelity: exact -/
noncomputable abbrev paperLow : History := project paperBase (spliceAtomCode 0) (fun _ => 3 / 10)

/-- The high component: weight `7/10`.
Source: mandate T1.4
Kind: D
Fidelity: exact -/
noncomputable abbrev paperHigh : History := project paperBase (spliceAtomCode 0) (fun _ => 7 / 10)

/-- **The two limits, outright**: `paperLow n (spliceAtom 0) → 3/10`, `paperHigh n (spliceAtom 0) → 7/10`
(li-projection's `project_atom_tendsto` from the base's criterion; no (A)).
Source: mandate T1.4 ("the limits `3/10`, `7/10` are sorry-free")
Kind: N+
Fidelity: exact -/
theorem paperSplice_limits :
    Tendsto (fun n => paperLow n (spliceAtom 0)) atTop (𝓝 (3 / 10)) ∧
    Tendsto (fun n => paperHigh n (spliceAtom 0)) atTop (𝓝 (7 / 10)) := by
  haveI := paperBase_isLogicalInductor
  constructor
  · have h := project_atom_tendsto paperBase (paperDP 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁) (spliceAtomCode 0)
      (fun _ => 3 / 10) 0 (fun _ _ => rfl)
    push_cast at h
    exact h
  · have h := project_atom_tendsto paperBase (paperDP 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁) (spliceAtomCode 0)
      (fun _ => 7 / 10) 0 (fun _ _ => rfl)
    push_cast at h
    exact h

/-- Both components are computable markets with prices in `[0,1]`.
Source: mandate T1.4
Kind: N+
Fidelity: exact -/
theorem paperSplice_components_computable :
    ComputableMarket paperLow ∧ ComputableMarket paperHigh :=
  ⟨computableMarket_project _ _ _ paperBase_isLogicalInductor.marketComputable
      (Computable.const _) (fun _ => by norm_num),
   computableMarket_project _ _ _ paperBase_isLogicalInductor.marketComputable
      (Computable.const _) (fun _ => by norm_num)⟩

/-- **T1.3/T1.4, the paper instance**: the parity trader (buying on even days from some pair index
`M` on) exploits the parity splice of the two projections over `paperDP 𝗜𝚺₁`, with per-pair gain
at least `1/5` — the source's "cash ≈ 0.2 per pair" as an exact rational — and the splice is a
computable market that is not a logical inductor. **Sorry-free**: the exploited object is the price
path, whose limits are outright.
Source: mandate T1.4; [[corr-wf14-inventory]] 047 (`selection_checks.py` C5)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paperSplice_exploited :
    (∃ M, (∀ k, M ≤ k → (1 / 5 : ℝ) ≤
        paritySplice paperLow paperHigh (2 * k + 1) (spliceAtom 0) -
          paritySplice paperLow paperHigh (2 * k) (spliceAtom 0)) ∧
      (parityTrader (spliceAtom 0) 1 M).Exploits (paritySplice paperLow paperHigh) (paperDP 𝗜𝚺₁)) ∧
    ComputableMarket (paritySplice paperLow paperHigh) ∧
    ¬ IsLogicalInductor (paritySplice paperLow paperHigh) (paperDP 𝗜𝚺₁) := by
  obtain ⟨clo, chi⟩ := paperSplice_components_computable
  obtain ⟨hlo, hhi⟩ := paperSplice_limits
  refine ⟨?_, (paritySplice_not_isLogicalInductor_parityTrader paperLow paperHigh (paperDP 𝗜𝚺₁)
    (spliceAtom 0) clo chi (paperDP_hworld 𝗜𝚺₁) _ _ hlo hhi (by norm_num)).1,
    (paritySplice_not_isLogicalInductor_parityTrader paperLow paperHigh (paperDP 𝗜𝚺₁)
    (spliceAtom 0) clo chi (paperDP_hworld 𝗜𝚺₁) _ _ hlo hhi (by norm_num)).2⟩
  have hb₁ : ∀ n, 0 ≤ paperLow n (spliceAtom 0) ∧ paperLow n (spliceAtom 0) ≤ 1 :=
    fun n => clo.1 n _
  have hb₂ : ∀ n, 0 ≤ paperHigh n (spliceAtom 0) ∧ paperHigh n (spliceAtom 0) ≤ 1 :=
    fun n => chi.1 n _
  have hδ : (0 : ℝ) < 1 / 10 := by norm_num
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hlo _ hδ)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp hhi _ hδ)
  have hgain : ∀ k, max N₁ N₂ ≤ k → (1 / 5 : ℝ) ≤
      ((1 : ℚ) : ℝ) * (paritySplice paperLow paperHigh (2 * k + 1) (spliceAtom 0) -
        paritySplice paperLow paperHigh (2 * k) (spliceAtom 0)) := by
    intro k hk
    have a := hN₁ (2 * k) (by have := le_trans (le_max_left N₁ N₂) hk; omega)
    have b := hN₂ (2 * k + 1) (by have := le_trans (le_max_right N₁ N₂) hk; omega)
    rw [Real.dist_eq, abs_lt] at a b
    rw [paritySplice_odd, paritySplice_even, Rat.cast_one, one_mul]
    linarith
  refine ⟨max N₁ N₂, fun k hk => by simpa using hgain k hk, ?_⟩
  exact parityTrader_exploits_of_gain _ (paperDP 𝗜𝚺₁) (spliceAtom 0) 1 (Or.inl rfl) _
    (splice_mem_Icc_at _ _ _ _ hb₁ hb₂) (paperDP_hworld 𝗜𝚺₁) _ (by norm_num) hgain

/-- **The two components are inductors** — li-projection's `project_const_isLogicalInductor`, which
rests on the OPEN (A); the splice result above does not depend on this.
Source: mandate T1.4 ("state it as a separate theorem … listed in your open file")
Kind: N+
Fidelity: exact
Hyps: (a) none; rests on li-projection's OPEN rewriters -/
theorem paperSplice_components_isLogicalInductor :
    IsLogicalInductor paperLow (paperDP 𝗜𝚺₁) ∧ IsLogicalInductor paperHigh (paperDP 𝗜𝚺₁) := by
  haveI := paperBase_isLogicalInductor
  exact ⟨project_const_isLogicalInductor paperBase (paperDP 𝗜𝚺₁) _ (paperDP_spliceAtomFree 0)
      (3 / 10) (by norm_num) (by norm_num),
    project_const_isLogicalInductor paperBase (paperDP 𝗜𝚺₁) _ (paperDP_spliceAtomFree 0)
      (7 / 10) (by norm_num) (by norm_num)⟩

/-! ## T1.6 The harmonic refutation, instantiated -/

/-- The path-level refutation over the empty process (every world consistent at every stage).
Source: mandate T1.6(i) ("use `trivialDP` for the N+ instance")
Kind: N−
Fidelity: exact -/
theorem harmonic_refuted_trivialDP :
    (parityTrader (spliceAtom 0) 1 0).Exploits
      (paritySplice (harmonicLow (spliceAtom 0)) (harmonicHigh (spliceAtom 0))) trivialDP :=
  (splice_o1_conjecture_refuted_paths (spliceAtom 0) trivialDP
    (fun n => ⟨worldTrue, trivialDP_consistentWith _ n⟩)).2.2.2.2.2.2.2

/-- The path-level refutation over the paper process.
Source: mandate T1.6(i)
Kind: N+
Fidelity: exact -/
theorem harmonic_refuted_paperDP :
    (parityTrader (spliceAtom 0) 1 0).Exploits
      (paritySplice (harmonicLow (spliceAtom 0)) (harmonicHigh (spliceAtom 0))) (paperDP 𝗜𝚺₁) :=
  (splice_o1_conjecture_refuted_paths (spliceAtom 0) (paperDP 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁)).2.2.2.2.2.2.2

/-! ## T2.2 / T2.4 instances -/

/-- The two-day patch policy of li-projection's witness is criterion-preserving over the paper
process; applied to the paper LIA it is li-projection's `paperPatchTwoDays`.
Source: mandate T2.2 ("T2.2's witness is li-projection's `paperPatchTwoDays`")
Kind: N+
Fidelity: exact -/
theorem patchPolicy_paper : CriterionPreserving (patchPolicy twoDayS twoDayT) (paperDP 𝗜𝚺₁) :=
  patchPolicy_criterionPreserving (paperDP 𝗜𝚺₁) twoDayS twoDayT (by
    intro p hp
    simp only [twoDayS, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> norm_num [twoDayT])

/-- The paper LIA patched to price the press family `spliceAtom (n + 3)` at `0` on days `≤ 5` is an
inductor over `paperDP 𝗜𝚺₁`, with the prescription exact.
Source: mandate T2.4 (the corrigibility instance)
Kind: N+
Fidelity: exact -/
theorem paperDefies :
    IsLogicalInductor (patch paperBase (pressCoords (fun n => spliceAtom (n + 3)) 5) (fun _ _ => 0))
      (paperDP 𝗜𝚺₁) ∧
    ∀ n, n ≤ 5 → patch paperBase (pressCoords (fun n => spliceAtom (n + 3)) 5) (fun _ _ => 0) n
      (spliceAtom (n + 3)) = 0 :=
  defies_first_N_presses paperBase (paperDP 𝗜𝚺₁) (hLI := paperBase_isLogicalInductor) _ 5

/-! ## T3.1 instances -/

/-- The paper process with `∼ spliceAtom 1` adjoined: a computable process refuting `spliceAtom 1`
at every stage, by the stage.
Source: mandate T3.1 (N+)
Kind: D
Fidelity: exact -/
noncomputable abbrev paperRefDP : DeductiveProcess :=
  (paperDP 𝗜𝚺₁).adjoinSentence (∼ spliceAtom 1)

/-- `paperRefDP` is computable.
Source: mandate T3.1
Kind: L
Fidelity: exact -/
theorem paperRefDP_computable : ComputableDeductiveProcess paperRefDP :=
  computableDeductiveProcess_adjoinSentence _ (paperDP_computable _) _

/-- `paperRefDP` has a consistent world at every stage (a world consistent with the paper stage and
refuting the fresh atom).
Source: mandate T3.1 ("T3.1's N+ must have `hworld` for `DP`")
Kind: N+
Fidelity: exact -/
theorem paperRefDP_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (paperRefDP.D n) := by
  intro n
  obtain ⟨v, hv, hnot⟩ :=
    exists_consistent_not_holds_atom (paperDP_spliceAtomFree 1) (paperDP_hworld 𝗜𝚺₁) n
  refine ⟨v, fun φ hφ => ?_⟩
  simp only [DeductiveProcess.adjoinSentence, DeductiveProcess.union_stage, Finset.mem_union,
    fixedConditionProcess, Finset.mem_singleton] at hφ
  rcases hφ with hφ | rfl
  · exact hv φ hφ
  · exact (PCWorld.holds_neg v _).mpr hnot

/-- `∼ spliceAtom 1` is in stage `0` of `paperRefDP`.
Source: mandate T3.1
Kind: L
Fidelity: exact -/
theorem paperRefDP_neg_mem : (∼ spliceAtom 1) ∈ paperRefDP.D 0 := by
  simp [DeductiveProcess.adjoinSentence, DeductiveProcess.union_stage, fixedConditionProcess]

/-- **T3.1's N+**: every computable market is a logical inductor over
`paperRefDP.adjoinSentence (spliceAtom 1)` — a real computable process (the paper process plus one
literal) with a consistent world at every stage, and a sentence refuted by the stages.
Source: mandate T3.1
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paperConditioned_vacuous :
    ∀ P : History, ComputableMarket P →
      IsLogicalInductor P (paperRefDP.adjoinSentence (spliceAtom 1)) :=
  conditioned_vacuous_of_neg_mem paperRefDP paperRefDP_computable _ 0 paperRefDP_neg_mem

/-- **T3.1's N−**: `ψ := ⊥` over the paper process itself (every world refutes it at every stage;
exercises nothing about `DP`).
Source: mandate T3.1 ("`ψ := ⊥` … grade that N−")
Kind: N−
Fidelity: exact -/
theorem paperConditioned_vacuous_bot :
    ∀ P : History, ComputableMarket P → IsLogicalInductor P ((paperDP 𝗜𝚺₁).adjoinSentence ⊥) :=
  conditioned_vacuous_of_refuted _ (paperDP_computable _) ⊥ 0 (fun v _ h => holds_bot_false v h)

/-! ## T3.2 instance -/

/-- The grid LUV's thresholds are injective on every day's grid.
Source: mandate T3.2(ii)
Kind: L
Fidelity: exact -/
theorem gridLUV_hinj (n : ℕ) : ∀ i j, i < n + 1 → j < n + 1 →
    gridLUV.gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)) = gridLUV.gt ((j : ℚ) / ((n + 1 : ℕ) : ℚ)) → i = j := by
  intro i j _ _ h
  have := gridLUV_gt_injective h
  rw [div_left_inj' (by positivity)] at this
  exact_mod_cast this

/-- **The fixture's `3/10` at precision `10`**, as an exact rational: the grid history at `k = 3`,
`ε = 1/2` gives `𝔼_9(gridLUV | spliceAtom 1) = 3/10` (Lean day `9` is precision `10`). Nothing of
the paper LIA is used — the history is `gridHistory` at a synthetic valuation (renamed from
`paperGrid_three_tenths` in repair round 1, adversarial audit N6(ii)); the fresh atom is the
splice atom only so the thresholds are distinct from it.
Source: [[corr-legit-neg-inventory]] 060 ("`𝔼_n(X|ψ)` is set to each of `0, 3/10, 9/10` at `n = 10`")
Kind: N+
Fidelity: exact -/
theorem grid_three_tenths :
    condExpect (gridHistory (spliceAtom 1) gridLUV 3 (1 / 2)) (spliceAtom 1) gridLUV 9 = 3 / 10 := by
  have h := (condExpect_gridHistory (spliceAtom 1) gridLUV 9 3 (by norm_num) (1 / 2) (by norm_num)
    (gridLUV_hinj 9)).2
  rw [h]; norm_num

/-! ## T3.3 instance -/

/-- The translation identities with a trader that trades the re-priced sentence
`spliceAtom 2 ⋏ spliceAtom 1` (so the discrepancy terms are live), over the paper LIA.
Source: mandate T3.3 (N+)
Kind: N+
Fidelity: exact -/
theorem paperTranslate :
    (∀ (v : PCWorld), ¬ v.Holds (spliceAtom 1) → ∀ n,
      (Trader.repriceTranslate (spliceAtom 1) {spliceAtom 2} (fun _ _ => 1 / 2)
          (parityTrader (spliceAtom 2 ⋏ spliceAtom 1) 1 0)).netWorth paperBase v n =
        (parityTrader (spliceAtom 2 ⋏ spliceAtom 1) 1 0).netWorth
          (reprice paperBase (spliceAtom 1) {spliceAtom 2} (fun _ _ => 1 / 2)) v n ∧
      (Trader.zeroTranslate (spliceAtom 1) {spliceAtom 2} 0
          (parityTrader (spliceAtom 2 ⋏ spliceAtom 1) 1 0)).netWorth paperBase v n =
        (parityTrader (spliceAtom 2 ⋏ spliceAtom 1) 1 0).netWorth
          (zeroOut paperBase (spliceAtom 1) {spliceAtom 2} 0) v n) ∧
    (∀ (v : PCWorld) (n : ℕ),
      |(parityTrader (spliceAtom 2 ⋏ spliceAtom 1) 1 0).netWorth
          (reprice paperBase (spliceAtom 1) {spliceAtom 2} (fun _ _ => 1 / 2)) v n -
        (Trader.repriceTranslate (spliceAtom 1) {spliceAtom 2} (fun _ _ => 1 / 2)
          (parityTrader (spliceAtom 2 ⋏ spliceAtom 1) 1 0)).netWorth paperBase v n| ≤
        repriceBound (spliceAtom 1) {spliceAtom 2} (fun _ _ => 1 / 2) paperBase
          (parityTrader (spliceAtom 2 ⋏ spliceAtom 1) 1 0) n ∧
      |(parityTrader (spliceAtom 2 ⋏ spliceAtom 1) 1 0).netWorth
          (zeroOut paperBase (spliceAtom 1) {spliceAtom 2} 0) v n -
        (Trader.zeroTranslate (spliceAtom 1) {spliceAtom 2} 0
          (parityTrader (spliceAtom 2 ⋏ spliceAtom 1) 1 0)).netWorth paperBase v n| ≤
        zeroBound (spliceAtom 1) {spliceAtom 2} 0 paperBase
          (parityTrader (spliceAtom 2 ⋏ spliceAtom 1) 1 0) n) :=
  translated_trader_netWorth (spliceAtom 1) {spliceAtom 2} (fun _ _ => 1 / 2)
    (fun _ _ _ => by norm_num) 0 paperBase (parityTrader (spliceAtom 2 ⋏ spliceAtom 1) 1 0)

/-! ## T3.4 / T3.5 instances (rest on the OPEN (B1)) -/

/-- The LIA over `paperRefDP`.
Source: mandate T3.4
Kind: D
Fidelity: exact -/
noncomputable abbrev paperRefBase : History := liaHistory paperRefDP

/-- The LIA over `paperRefDP` is an inductor over it.
Source: mandate T3.4
Kind: L
Fidelity: exact -/
theorem paperRefBase_isLogicalInductor : IsLogicalInductor paperRefBase paperRefDP :=
  LIA_is_logical_inductor _ paperRefDP_computable

/-- **T3.4's instance**: the convention horn over the LIA of `paperRefDP` at the stage-refuted
`spliceAtom 1` with `Φ = {spliceAtom 2}`. Rests on the OPEN (B1).
Source: mandate T3.4
Kind: N+
Fidelity: exact
Hyps: (a) none; rests on `translateStreamRewriter` -/
theorem paperZeroOut :
    IsLogicalInductor (zeroOut paperRefBase (spliceAtom 1) {spliceAtom 2} 0) paperRefDP :=
  zeroOut_isLogicalInductor paperRefBase paperRefDP (hLI := paperRefBase_isLogicalInductor)
    (spliceAtom 1) 0 (refuted_of_neg_mem _ _ 0 paperRefDP_neg_mem) {spliceAtom 2}

/-- **T3.5's instance**: the free horn over the LIA of `paperRefDP` with the constant `r ≡ 1/2`.
Rests on the OPEN (B1).
Source: mandate T3.5
Kind: N+
Fidelity: exact
Hyps: (a) none; rests on `translateStreamRewriter` -/
theorem paperReprice :
    IsLogicalInductor (reprice paperRefBase (spliceAtom 1) {spliceAtom 2} (fun _ _ => 1 / 2))
      paperRefDP :=
  reprice_isLogicalInductor paperRefBase paperRefDP (hLI := paperRefBase_isLogicalInductor)
    (spliceAtom 1) 0 (refuted_of_neg_mem _ _ 0 paperRefDP_neg_mem) {spliceAtom 2} _
    (fun _ _ _ => by norm_num) (fun _ _ _ => by norm_num) (fun _ _ => Computable.const _)
    (fun _ _ => MachineRatCodes.const _)

/-! ## T4 instances -/

/-- The grid LUV is undecided over the paper process yet some completed-theory world values it
nowhere (`hval` fails).
Source: mandate T4.2; Known issue 6
Kind: N+
Fidelity: exact -/
theorem paperGridLUV_not_valued :
    UndecidedLUV (paperDP 𝗜𝚺₁) gridLUV ∧
    ∃ v : PCWorld, v.ConsistentWithTheory (paperDP 𝗜𝚺₁) ∧ ∀ x : ℝ, ¬ v.ValuesAt gridLUV x :=
  gridLUV_undecided_not_valued (paperDP 𝗜𝚺₁) (paperDP_cleanroomFree 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁)

/-- **T4.4's instance, outright**: over the paper LIA, the two-valued undecided LUV at
`spliceAtomCode 0` has expectation sequences converging to `3/10` and `7/10` under the two
projections.
Source: mandate T4.4
Kind: N+
Fidelity: exact (the LUV is two-valued — degenerate as a utility, disclosed)
Hyps: (a) none -/
theorem paperUndecidedPrior :
    UndecidedLUV (paperDP 𝗜𝚺₁) (atomLUV (spliceAtomCode 0)) ∧
    (∀ v : PCWorld, ∃ x : ℝ, v.ValuesAt (atomLUV (spliceAtomCode 0)) x) ∧
    ConvergesTo ((atomLUV (spliceAtomCode 0)).expectSeq paperLow) (3 / 10) ∧
    ConvergesTo ((atomLUV (spliceAtomCode 0)).expectSeq paperHigh) (7 / 10) ∧
    ((3 / 10 : ℚ) : ℝ) ≠ ((7 / 10 : ℚ) : ℝ) := by
  haveI := paperBase_isLogicalInductor
  have h := undecided_limit_is_prior paperBase (paperDP 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁) (spliceAtomCode 0)
    (paperDP_spliceAtomFree 0) (3 / 10) (7 / 10) (by norm_num)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, ?_, ?_, h5⟩
  · have := h3; push_cast at this; exact this
  · have := h4; push_cast at this; exact this

/-- **T4.4's inductor conjuncts**: the two projections carrying the different limit expectations
are inductors — rests on li-projection's (A).
Source: mandate T4.4 ("the inductor conjuncts rest on (A) (list them)")
Kind: N+
Fidelity: exact
Hyps: (a) none; rests on li-projection's OPEN rewriters -/
theorem undecided_limit_is_prior_inductors :
    IsLogicalInductor paperLow (paperDP 𝗜𝚺₁) ∧ IsLogicalInductor paperHigh (paperDP 𝗜𝚺₁) :=
  paperSplice_components_isLogicalInductor

end Cleanroom.Li.LiSpliceCondition
