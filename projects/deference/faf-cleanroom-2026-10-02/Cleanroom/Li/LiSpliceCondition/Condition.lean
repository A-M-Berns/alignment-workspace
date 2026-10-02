import Cleanroom.Li.LiSpliceCondition.Defs
import LogicalInduction.Construction.Conditioning.Presentation
import LogicalInduction.Framework.Affine

/-!
# `li-splice-condition` · Condition: conditioning on a refuted sentence (T3.1, T3.2, T3.5, T3.6)

Package `Cleanroom.Li.LiSpliceCondition` ([[li-splice-condition-mandate]]), file 3 of the layout.

* **T3.1 Vacuity at a refuted sentence.** Once `ψ` is refuted at a stage `N` of `DP` (every world
  consistent with `DP.D N` refutes it), stage `N` of FAF's adjoined process `DP.adjoinSentence ψ`
  is propositionally unsatisfiable, so by FAF's `isLogicalInductor_of_stage_unsatisfiable` *every*
  computable market is a logical inductor over it (`conditioned_vacuous_of_refuted`). The
  syntactic sufficient condition is `∼ψ ∈ DP.D N` (`refuted_of_neg_mem`). Corollary: at a refuted
  `ψ`, the conclusion of FAF's `lic_conditioned_fixed` follows from the computability of the
  conditioned market alone (`conditioned_isLogicalInductor_of_computable`) — a finding about the
  paper's and FAF's convention, not a defect (the paper's proof carries the consistency
  hypothesis, `main.tex:6122`; FAF's docstring calls this "the degenerate branch"). Non-vacuity of
  the impossibility: at an *unrefuted* fresh atom the adjoined process keeps a consistent world at
  every stage (`adjoinSentence_hworld_of_atomFree`), so the hypothesis is not an artefact.
* **T3.2 The junk value.** FAF's capped `conditionalQuote` is `1` whenever `V ψ = 0`
  (`conditionalQuote_eq_one_of_zero`), hence `𝔼_n(X | ψ) = 1` for every LUV
  (`condExpect_eq_one_of_zero`) and also for the complementary LUV `1 − X`
  (`condExpect_compl_eq_one_of_zero`): the two sum to `2`, incoherently
  (`condExpect_add_compl_eq_two_of_zero`). **This is a lemma about the cap, not about inductors**
  (the ledger's Claim column says "junk value"). Reachability: at a positive price of `ψ`, every
  grid value `k/(n+1)` is attained by an explicit (non-coherent) valuation
  (`condExpect_gridHistory`). At a positive price the quote is the Bayesian ratio capped at `1`.
* **T3.5 The dichotomy** (the cheap honest theorem of the free horn): on every day either
  `P_n(ψ) = 0` and every conditional quote is the cap `1`, or `P_n(ψ) > 0` and the quote is
  `min (P_n(φ ⋏ ψ) / P_n(ψ)) 1` (`conditionalQuote_dichotomy`). The criterion enters only through
  `Transfer.lean`.
* **T3.6 Consequences**: two histories agreeing off the sentences `⌜X > i/(n+1)⌝ ⋏ ψ` whose
  conditional expectations are `0` and `1`, flipping any two-option argmax (`condExpect_flip`);
  under the cap every refuted option scores `1` (`condExpect_refuted_options_eq_one`).
-/

namespace Cleanroom.Li.LiSpliceCondition

open LogicalInduction LO.Propositional Cleanroom.Li.LiProjection Cleanroom.Bli.BliFound

/-! ## T3.1 Vacuity at a refuted sentence -/

/-- Stage `N` of the adjoined process is unsatisfiable when `ψ` is refuted at stage `N` of `DP`.
Source: [[corr-legit-neg-inventory]] 059 (E7 (iii), "that process has a propositionally unsatisfiable stage")
Kind: L
Fidelity: exact -/
lemma adjoinSentence_stage_unsat (DP : DeductiveProcess) (ψ : Sentence) (N : ℕ)
    (href : ∀ v : PCWorld, v.ConsistentWith (DP.D N) → ¬ v.Holds ψ) :
    ∀ v : PCWorld, ¬ v.ConsistentWith ((DP.adjoinSentence ψ).D N) := by
  intro v hv
  have h1 : v.ConsistentWith (DP.D N) := fun φ hφ => hv φ (by
    simp only [DeductiveProcess.adjoinSentence, DeductiveProcess.union_stage, Finset.mem_union]
    exact Or.inl hφ)
  have h2 : v.Holds ψ := hv ψ (by
    simp [DeductiveProcess.adjoinSentence, DeductiveProcess.union_stage, fixedConditionProcess])
  exact href v h1 h2

/-- The adjoined process of a computable process is computable (FAF's union of computations).
Source: mandate T3.1 ("computability from `union_toComputable`")
Kind: L
Fidelity: exact -/
theorem computableDeductiveProcess_adjoinSentence (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) (ψ : Sentence) :
    ComputableDeductiveProcess (DP.adjoinSentence ψ) := by
  obtain ⟨base⟩ := hDP.nonemptyComputation
  exact base.union_toComputable (fixedConditionProcessComputation ψ)

/-- **Vacuity at a refuted sentence.** If `ψ` is refuted at stage `N` of a computable process `DP`
(every world consistent with `DP.D N` refutes `ψ`), then *every* computable market is a logical
inductor over FAF's adjoined process `DP.adjoinSentence ψ` — the process `thm:scon` conditions
over. The criterion over that process is empty: no trader of any class exploits a process with an
unsatisfiable stage (`isLogicalInductor_of_stage_unsatisfiable`). The hypothesis is "`ψ` refuted
at a stage", not "the process itself unsatisfiable" (mandate trap (2)): the N+ instance keeps a
consistent world at every stage of `DP`. The theorem is also (trivially) true when `DP.D N` is
itself unsatisfiable; it is non-trivial only when `DP` has a consistent world at every stage,
which the witness supplies (`paperRefDP_hworld`) and `adjoinSentence_hworld_of_atomFree` shows is
compatible with the construction at an unrefuted atom.
Source: [[corr-legit-neg-inventory]] 059 (`clusters/E/NEGATIVES.md` E7 (iii), "*every* computable market is a logical inductor over such a process")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem conditioned_vacuous_of_refuted (DP : DeductiveProcess) (hDP : ComputableDeductiveProcess DP)
    (ψ : Sentence) (N : ℕ) (href : ∀ v : PCWorld, v.ConsistentWith (DP.D N) → ¬ v.Holds ψ) :
    ∀ P : History, ComputableMarket P → IsLogicalInductor P (DP.adjoinSentence ψ) :=
  fun P hP => isLogicalInductor_of_stage_unsatisfiable P _ hP
    (computableDeductiveProcess_adjoinSentence DP hDP ψ) (adjoinSentence_stage_unsat DP ψ N href)

/-- The syntactic sufficient condition: `∼ψ ∈ DP.D N` refutes `ψ` at stage `N`.
Source: mandate T3.1 ("`∼ψ ∈ DP.D N → href`")
Kind: L
Fidelity: exact -/
lemma refuted_of_neg_mem (DP : DeductiveProcess) (ψ : Sentence) (N : ℕ) (h : (∼ψ) ∈ DP.D N) :
    ∀ v : PCWorld, v.ConsistentWith (DP.D N) → ¬ v.Holds ψ :=
  fun v hv => (PCWorld.holds_neg v ψ).mp (hv _ h)

/-- Vacuity at a sentence whose negation is in a stage.
Source: [[corr-legit-neg-inventory]] 059 (E7's "`Γ ⊢ ¬ψ`")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem conditioned_vacuous_of_neg_mem (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) (ψ : Sentence) (N : ℕ) (h : (∼ψ) ∈ DP.D N) :
    ∀ P : History, ComputableMarket P → IsLogicalInductor P (DP.adjoinSentence ψ) :=
  conditioned_vacuous_of_refuted DP hDP ψ N (refuted_of_neg_mem DP ψ N h)

/-- **FAF's `lic_conditioned_fixed` has no content at a refuted `ψ`**: its conclusion,
`IsLogicalInductor (conditionedHistory P (fun _ => ψ)) (DP.adjoinSentence ψ)`, follows from the
computability of the conditioned market alone — no criterion on `P` is used. A finding about FAF's
(and the paper's) convention, not a defect: the paper's proof carries the consistency hypothesis
(`main.tex:6122`) and FAF's docstring calls this the degenerate branch.
Source: [[corr-legit-neg-inventory]] 059 (E7 (iii), "Closure Under Conditioning is vacuous here")
Kind: L
Fidelity: exact -/
theorem conditioned_isLogicalInductor_of_computable (P : History) (DP : DeductiveProcess)
    (hDP : ComputableDeductiveProcess DP) (ψ : Sentence) (N : ℕ)
    (href : ∀ v : PCWorld, v.ConsistentWith (DP.D N) → ¬ v.Holds ψ)
    (hcm : ComputableMarket (conditionedHistory P (fun _ => ψ))) :
    IsLogicalInductor (conditionedHistory P (fun _ => ψ)) (DP.adjoinSentence ψ) :=
  conditioned_vacuous_of_refuted DP hDP ψ N href _ hcm

/-- **The impossibility is not an artefact of the encoding**: at an *unrefuted* sentence — a fresh
atom `u` — the adjoined process keeps a consistent world at every stage, so `thm:scon` has content
there and T3.1's hypothesis is what kills it, not the construction `adjoinSentence`.
Source: mandate T3.1 ("also show the adjoined process at an unrefuted `ψ` keeps `hworld`")
Kind: N+
Fidelity: exact -/
theorem adjoinSentence_hworld_of_atomFree (DP : DeductiveProcess) (u : ℕ)
    (hu : AtomFreeProcess u DP) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith ((DP.adjoinSentence (Formula.atom u)).D n) := by
  intro n
  obtain ⟨v, hv, hu'⟩ := exists_consistent_holds_atom hu hworld n
  refine ⟨v, fun φ hφ => ?_⟩
  simp only [DeductiveProcess.adjoinSentence, DeductiveProcess.union_stage, Finset.mem_union,
    fixedConditionProcess, Finset.mem_singleton] at hφ
  rcases hφ with hφ | rfl
  · exact hv φ hφ
  · exact hu'

/-! ## T3.2 The junk value -/

/-- **The cap at a zero-priced condition**: `conditionalQuote V φ ψ = 1` whenever `V ψ = 0` and
`V (φ ⋏ ψ) ≥ 0`. The value `1` is FAF's cap (`def:condp`), not a belief.
Source: [[corr-legit-neg-2-inventory]] 023 (E7's fixture `e5_li_conditional.py` (3)); [[corr-legit-neg-inventory]] 060
Kind: L
Fidelity: exact -/
theorem conditionalQuote_eq_one_of_zero (V : Valuation) (φ ψ : Sentence) (hV : 0 ≤ V (φ ⋏ ψ))
    (h0 : V ψ = 0) : conditionalQuote V φ ψ = 1 :=
  conditionalQuote_eq_one (by rw [h0]; exact hV)

/-- **The conditional expectation at a zero-priced condition is the cap `1`** for every LUV: every
threshold term is `1` and `expectApprox` averages `n+1` ones. A finding about FAF's capped
convention — do not read the `1` as content about inductors.
Source: [[corr-legit-neg-inventory]] 060 (E7 (i), "`𝔼_n(X | ψ) = 𝔼_n(1 − X | ψ) = 1`"); [[corr-legit-neg-2-inventory]] 023
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem condExpect_eq_one_of_zero (P : History) (ψ : Sentence) (X : LUV) (n : ℕ)
    (hP : ∀ χ, 0 ≤ P n χ) (h0 : P n ψ = 0) : condExpect P ψ X n = 1 := by
  unfold condExpect LUV.expect LUV.expectApprox conditionedHistory
  rw [Finset.sum_congr rfl (fun i _ => conditionalQuote_eq_one_of_zero (P n) _ ψ (hP _) h0)]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by positivity)

/-- The complementary LUV `1 − X`: `⌜(1 − X) > r⌝ := ∼⌜X > 1 − r⌝`.
Source: mandate T3.2(i) ("the complementary LUV `X'` with `X'.gt r := ∼(X.gt (1 − r))`")
Kind: D
Fidelity: exact -/
def LUV.compl (X : LUV) : LUV := ⟨fun r => ∼(X.gt (1 - r))⟩

/-- The complementary LUV's conditional expectation is also the cap `1` at a zero-priced condition.
Source: [[corr-legit-neg-inventory]] 060
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem condExpect_compl_eq_one_of_zero (P : History) (ψ : Sentence) (X : LUV) (n : ℕ)
    (hP : ∀ χ, 0 ≤ P n χ) (h0 : P n ψ = 0) : condExpect P ψ (LUV.compl X) n = 1 :=
  condExpect_eq_one_of_zero P ψ (LUV.compl X) n hP h0

/-- **Incoherence of the cap**: `𝔼_n(X | ψ) + 𝔼_n(1 − X | ψ) = 2`, not `1`, at a zero-priced
condition. A property of the cap, stated so that nobody reads the two `1`s as beliefs.
Source: [[corr-legit-neg-inventory]] 060 (E7 (i)); mandate trap (1) for T3
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem condExpect_add_compl_eq_two_of_zero (P : History) (ψ : Sentence) (X : LUV) (n : ℕ)
    (hP : ∀ χ, 0 ≤ P n χ) (h0 : P n ψ = 0) :
    condExpect P ψ X n + condExpect P ψ (LUV.compl X) n = 2 := by
  rw [condExpect_eq_one_of_zero P ψ X n hP h0, condExpect_compl_eq_one_of_zero P ψ X n hP h0]
  norm_num

/-- A conjunction is never its own right conjunct (by size).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma and_ne_right : ∀ (φ ψ : Sentence), (φ ⋏ ψ) ≠ ψ
  | _, .atom _ => fun h => by cases h
  | _, .falsum => fun h => by cases h
  | φ, .and a b => fun h => by
      have h' : Formula.and φ (Formula.and a b) = Formula.and a b := h
      injection h' with _ h2
      exact and_ne_right a b h2
  | _, .or _ _ => fun h => by cases h
  | _, .imp _ _ => fun h => by cases h

open Classical in
/-- **The grid valuation**: `ψ` at `ε`, the conjunctions `⌜X > i/(n+1)⌝ ⋏ ψ` at `ε` for `i < k`
and at `0` for `i ≥ k`, everything else `0`. Not coherent, and not meant to be: it exhibits that
nothing in the *definition* of the conditional expectation ties it down.
Source: mandate T3.2(ii) ("a finite construction over `Valuation`; define `V` by cases on the sentence; it need not be coherent — say so")
Kind: D
Fidelity: exact -/
noncomputable def gridValuation (ψ : Sentence) (X : LUV) (n k : ℕ) (ε : ℝ) : Valuation :=
  fun χ => if χ = ψ then ε
    else if ∃ i, i < n + 1 ∧ i < k ∧ χ = X.gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)) ⋏ ψ then ε else 0

/-- The history whose day-`n` valuation is the grid valuation at precision `n+1`.
Source: mandate T3.2(ii)
Kind: D
Fidelity: exact -/
noncomputable def gridHistory (ψ : Sentence) (X : LUV) (k : ℕ) (ε : ℝ) : History :=
  fun n => gridValuation ψ X n k ε

/-- The grid valuation prices `ψ` at `ε`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gridValuation_self (ψ : Sentence) (X : LUV) (n k : ℕ) (ε : ℝ) :
    gridValuation ψ X n k ε ψ = ε := by
  simp [gridValuation]

/-- The grid valuation on the threshold conjunctions, under injectivity of the threshold family on
the grid.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gridValuation_and (ψ : Sentence) (X : LUV) (n k : ℕ) (ε : ℝ)
    (hinj : ∀ i j, i < n + 1 → j < n + 1 →
      X.gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)) = X.gt ((j : ℚ) / ((n + 1 : ℕ) : ℚ)) → i = j)
    {i : ℕ} (hi : i < n + 1) :
    gridValuation ψ X n k ε (X.gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)) ⋏ ψ) = if i < k then ε else 0 := by
  unfold gridValuation
  rw [if_neg (and_ne_right _ _)]
  by_cases hik : i < k
  · rw [if_pos hik, if_pos ⟨i, hi, hik, rfl⟩]
  · rw [if_neg hik, if_neg]
    rintro ⟨j, hj, hjk, hEq⟩
    have h' : Formula.and (X.gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))) ψ =
        Formula.and (X.gt ((j : ℚ) / ((n + 1 : ℕ) : ℚ))) ψ := hEq
    injection h' with h1 _
    have := hinj i j hi hj h1
    omega

/-- The conditional quote of the grid valuation is the indicator `[i < k]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma conditionalQuote_gridValuation (ψ : Sentence) (X : LUV) (n k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hinj : ∀ i j, i < n + 1 → j < n + 1 →
      X.gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)) = X.gt ((j : ℚ) / ((n + 1 : ℕ) : ℚ)) → i = j)
    {i : ℕ} (hi : i < n + 1) :
    conditionalQuote (gridValuation ψ X n k ε) (X.gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))) ψ =
      if i < k then 1 else 0 := by
  have hand := gridValuation_and ψ X n k ε hinj hi
  have hself := gridValuation_self ψ X n k ε
  by_cases hik : i < k
  · rw [if_pos hik] at hand ⊢
    exact conditionalQuote_eq_one (by rw [hand, hself])
  · rw [if_neg hik] at hand ⊢
    rw [conditionalQuote_eq_div (by rw [hand, hself]; exact hε), hand, zero_div]

/-- **Reachability of every grid value.** At a positive price `ε` of `ψ`, the day-`n` conditional
expectation of `X` under the grid history is exactly `k/(n+1)` for every `k ≤ n+1`: nothing in the
definition of `𝔼_n(· | ψ)` constrains it beyond the grid. The threshold family is assumed injective
on the grid (a witness: `gridLUV`, `Witnesses.lean`); the valuation is not coherent.
Source: [[corr-legit-neg-inventory]] 060 (E7 (ii), "`𝔼_n(X | ψ)` is set to each of `0, 3/10, 9/10` at `n = 10`"); mandate T3.2(ii)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem condExpect_gridHistory (ψ : Sentence) (X : LUV) (n k : ℕ) (hk : k ≤ n + 1) (ε : ℝ)
    (hε : 0 < ε)
    (hinj : ∀ i j, i < n + 1 → j < n + 1 →
      X.gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)) = X.gt ((j : ℚ) / ((n + 1 : ℕ) : ℚ)) → i = j) :
    gridHistory ψ X k ε n ψ = ε ∧
    condExpect (gridHistory ψ X k ε) ψ X n = (k : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  refine ⟨gridValuation_self ψ X n k ε, ?_⟩
  unfold condExpect LUV.expect LUV.expectApprox conditionedHistory gridHistory
  rw [Finset.sum_congr rfl (fun i hi =>
    conditionalQuote_gridValuation ψ X n k ε hε hinj (Finset.mem_range.mp hi))]
  rw [Finset.sum_boole]
  have hfilt : (Finset.range (n + 1)).filter (fun i => i < k) = Finset.range k := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hfilt, Finset.card_range, div_eq_inv_mul]

/-! ## T3.5 The day-wise dichotomy -/

/-- **The day-wise dichotomy at a valuation with prices in `[0,1]`**: either `V ψ = 0` and every
conditional quote on `ψ` is the cap `1`, or `V ψ > 0` and the quote is the Bayesian ratio capped
at `1`, `min (V (φ ⋏ ψ) / V ψ) 1` — the `min` made visible. No criterion is involved; the
criterion enters only through the transfer theorems (`Transfer.lean`), and what the verifier's
narrowing of E7 leaves is exactly this dichotomy plus those.
Source: [[corr-legit-neg-inventory]] 061, 063; `clusters/E/VERIFY.md` "E7 — narrowed"; mandate T3.5 ("the dichotomy itself is the cheap honest theorem")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem conditionalQuote_dichotomy (V : Valuation) (hV : ∀ χ, 0 ≤ V χ ∧ V χ ≤ 1)
    (φ ψ : Sentence) :
    (V ψ = 0 ∧ conditionalQuote V φ ψ = 1) ∨
    (0 < V ψ ∧ conditionalQuote V φ ψ = min (V (φ ⋏ ψ) / V ψ) 1) := by
  rcases (hV ψ).1.eq_or_lt with h0 | hpos
  · exact Or.inl ⟨h0.symm, conditionalQuote_eq_one_of_zero V φ ψ (hV _).1 h0.symm⟩
  · refine Or.inr ⟨hpos, ?_⟩
    by_cases hlt : V (φ ⋏ ψ) < V ψ
    · rw [conditionalQuote_eq_div hlt, min_eq_left ((div_le_one hpos).2 hlt.le)]
    · rw [conditionalQuote_eq_one (le_of_not_gt hlt),
        min_eq_right ((one_le_div hpos).2 (le_of_not_gt hlt))]

/-- The dichotomy on every day of a history with prices in `[0,1]`.
Source: mandate T3.5
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem conditionedHistory_dichotomy (P : History) (hP : ∀ n χ, 0 ≤ P n χ ∧ P n χ ≤ 1)
    (ψ : Sentence) (n : ℕ) :
    (P n ψ = 0 ∧ ∀ φ, conditionedHistory P (fun _ => ψ) n φ = 1) ∨
    (0 < P n ψ ∧ ∀ φ, conditionedHistory P (fun _ => ψ) n φ = min (P n (φ ⋏ ψ) / P n ψ) 1) := by
  rcases (hP n ψ).1.eq_or_lt with h0 | hpos
  · exact Or.inl ⟨h0.symm, fun φ => conditionalQuote_eq_one_of_zero (P n) φ ψ (hP n _).1 h0.symm⟩
  · refine Or.inr ⟨hpos, fun φ => ?_⟩
    rcases conditionalQuote_dichotomy (P n) (hP n) φ ψ with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h hpos.ne'
    · exact h

/-! ## T3.6 Consequences -/

/-- **Two histories agreeing off the threshold conjunctions, with conditional expectations `0` and
`1`**: the grid histories at `k = 0` and `k = n+1` agree at `ψ` and at every sentence that is not a
`⌜X > i/(n+1)⌝ ⋏ ψ`, and score the "unchosen option" `ψ` at `0` and at `1` — flipping the argmax
against any fixed alternative `u₀ ∈ (0,1)` (the fixture's `0` versus `3/10` regret is one such
`u₀`).
Source: [[corr-legit-neg-inventory]] 062 (E7 Consequence 1, "two logical inductors … give entries `0` and `1` for `a₁`; the menu's argmax … flip") — here two *histories*, no criterion (the inductor form rests on the OPEN certificate, `Transfer.lean`)
Kind: L
Fidelity: weaker: histories, not inductors
Hyps: (a) -/
theorem condExpect_flip (ψ : Sentence) (X : LUV) (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hinj : ∀ i j, i < n + 1 → j < n + 1 →
      X.gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)) = X.gt ((j : ℚ) / ((n + 1 : ℕ) : ℚ)) → i = j) :
    (∀ m χ, (∀ i, χ ≠ X.gt ((i : ℚ) / ((m + 1 : ℕ) : ℚ)) ⋏ ψ) →
      gridHistory ψ X 0 ε m χ = gridHistory ψ X (n + 1) ε m χ) ∧
    condExpect (gridHistory ψ X 0 ε) ψ X n = 0 ∧
    condExpect (gridHistory ψ X (n + 1) ε) ψ X n = 1 ∧
    ∀ u₀ : ℝ, 0 < u₀ → u₀ < 1 →
      condExpect (gridHistory ψ X 0 ε) ψ X n < u₀ ∧ u₀ < condExpect (gridHistory ψ X (n + 1) ε) ψ X n := by
  have h0 := (condExpect_gridHistory ψ X n 0 (by omega) ε hε hinj).2
  have h1 := (condExpect_gridHistory ψ X n (n + 1) le_rfl ε hε hinj).2
  rw [Nat.cast_zero, zero_div] at h0
  rw [div_self (by positivity)] at h1
  refine ⟨?_, h0, h1, fun u₀ hu0 hu1 => by rw [h0, h1]; exact ⟨hu0, hu1⟩⟩
  intro m χ hχ
  unfold gridHistory gridValuation
  by_cases hψ : χ = ψ
  · simp [hψ]
  · rw [if_neg hψ, if_neg hψ, if_neg, if_neg]
    · rintro ⟨i, -, -, hEq⟩; exact hχ i hEq
    · rintro ⟨i, -, -, hEq⟩; exact hχ i hEq

/-- **Under the cap every refuted option scores `1`**: for a finite family of option sentences
each priced `0` on day `n`, every conditional expectation is the cap `1` — so a menu scored by
`𝔼_n(U | ⌜took a⌝)` ranks every unchosen (refuted) option at the maximum.
Source: [[corr-legit-neg-inventory]] 062 (E7 Consequence 1, "under horn (i) every unchosen option is scored at the maximum `1`")
Kind: L
Fidelity: exact -/
theorem condExpect_refuted_options_eq_one (P : History) (n : ℕ) (hP : ∀ χ, 0 ≤ P n χ) (X : LUV)
    {ι : Type*} (a : ι → Sentence) (h0 : ∀ j, P n (a j) = 0) :
    ∀ j, condExpect P (a j) X n = 1 :=
  fun j => condExpect_eq_one_of_zero P (a j) X n hP (h0 j)

/-- D8 row 5's escape, as a definition: the belief state "conditioned on the consultation's
answer" is FAF's `conditionedHistory` at the fixed answer; `lic_conditioned_fixed` makes it an
inductor over `DP.adjoinSentence answer` when `answer` is not refuted — and T3.1 makes the
statement empty when it is.
Source: [[corr-legit-neg-2-inventory]] 034 (D8 row 5, "the day-`n` inductor conditioned on the consultation's answer")
Kind: D
Fidelity: exact -/
noncomputable abbrev answerConditioned (P : History) (answer : Sentence) : History :=
  conditionedHistory P (fun _ => answer)

end Cleanroom.Li.LiSpliceCondition
