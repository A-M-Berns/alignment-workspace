import Cleanroom.Li.LiSpliceCondition.Defs
import Cleanroom.Li.LiProjection.Marginal
import LogicalInduction.Properties.NonDogmatism
import LogicalInduction.Properties.ExpectationConvergence
import LogicalInduction.Properties.Relationships
import LogicalInduction.Framework.Compactness

/-!
# `li-splice-condition` · Utility: an undecidable utility as a LUV (T4)

Package `Cleanroom.Li.LiSpliceCondition` ([[li-splice-condition-mandate]]), file 7 of the layout.

* **T4.1** `UndecidedLUV DP X` (`Defs.lean`) gives both non-dogmatism bounds at every threshold in
  `(0,1)` (`UndecidedLUV.nonDogmatism`, FAF's `lic_nonDogmatism`/`_dual`).
* **T4.2** The limit expectation exists — FAF's `LUV.expect_converges` applied, **with `hval`
  (every completed-theory world values `X`) as a hypothesis** (`undecided_expect_converges`): it is
  *not* implied by undecidedness, and `gridLUV_undecided_not_valued` exhibits an undecided LUV
  (thresholds at distinct fresh atoms) and a completed-theory world valuing it nowhere. The
  per-threshold limits need no `hval` (`undecided_threshold_tendsto`).
* **T4.3** The limit CDF is antitone **given** that the implications `⌜X > r⌝ → ⌜X > r'⌝`
  (`r' < r`) are in every stage (`limitingBelief_antitone_of_imp_mem`, FAF's
  `lic_imp_eventually_le`); without that, the thresholds are independent and monotonicity has no
  source (findings).
* **T4.4** The criterion leaves the limit a prior: the two-valued LUV `atomLUV u` at a fresh atom
  is undecided, valued in every world, has expectation exactly the atom's price every day
  (`expect_atomLUV`), so under the two projections of one inductor its expectation sequences
  converge to `c` and `c'` (`undecided_limit_is_prior`, outright); the inductor conjuncts of the
  two projections rest on li-projection's (A) and live in `Witnesses.lean`.
* **T4.5** Obedience versus deference: a sentence in a stage converges to `1` at a summable rate
  (`obedience_summable`, "true by definition"); if `a` is in a stage and `⌜X > p⌝` is undecided,
  `⌜X > p⌝ ⋏ a` is undecided too (`undecided_and_decided`), so nothing the stages decide
  constrains the conditional on `a` — stated as "both verdicts plausible at every stage", not as a
  claim about the conditional's limit.
-/

namespace Cleanroom.Li.LiSpliceCondition

open LogicalInduction LO.Propositional Cleanroom.Li.LiProjection Cleanroom.Bli.BliFound
open Filter Topology

/-! ## T4.1 Non-dogmatism at every threshold -/

/-- An undecided LUV has both non-dogmatism bounds at every threshold in `(0,1)`.
Source: [[corr-core-inventory]] 034(i); mandate T4.1
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem UndecidedLUV.nonDogmatism (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (X : LUV) (hX : UndecidedLUV DP X) (r : ℚ) (hr0 : 0 < r) (hr1 : r < 1) :
    (∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop, ε ≤ P n (X.gt r)) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n in atTop, P n (X.gt r) ≤ 1 - ε) :=
  ⟨lic_nonDogmatism P DP (X.gt r) (fun n => (hX r hr0 hr1 n).1),
   lic_nonDogmatism_dual P DP (X.gt r) (fun n => (hX r hr0 hr1 n).2)⟩

/-- An undecided LUV's process has a consistent world at every stage.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma UndecidedLUV.hcons {DP : DeductiveProcess} {X : LUV} (hX : UndecidedLUV DP X) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) :=
  fun n => by
    obtain ⟨v, hv, -⟩ := (hX (1 / 2) (by norm_num) (by norm_num) n).1
    exact ⟨v, hv⟩

/-! ## T4.2 The limit exists — with `hval` as a hypothesis -/

/-- **The limit expectation of an undecided LUV exists**, by FAF's `LUV.expect_converges` — with
the valuation hypothesis `hval` (every completed-theory world values `X` somewhere) and the
threshold-code certificate carried as hypotheses. `hval` is **not** discharged by undecidedness
(the chat's "`Γ ⊢ ∃!x (u = x)` and a bound" is exactly its content; `gridLUV_undecided_not_valued`
below shows it can fail).
Source: [[corr-core-inventory]] 034(ii) (BLI paste l. 53, "the limit prices `P_∞(u > p)` are a coherent CDF"); mandate T4.2
Kind: L
Fidelity: exact
Hyps: (a) `hcode` is FAF's write-out interface for the thresholds; `hval` is FAF's linkage, disclosed as a hypothesis (not derivable from `hX`) -/
theorem undecided_expect_converges (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (X : LUV) (hX : UndecidedLUV DP X) (hcode : X.MachineThresholdCodes)
    (hval : ∀ v : PCWorld, v.ConsistentWithTheory DP → ∃ x : ℝ, v.ValuesAt X x) :
    ∃ L : ℝ, ConvergesTo (X.expectSeq P) L :=
  X.expect_converges P DP hcode hX.hcons hval

/-- The per-threshold limits exist with no `hval`: every threshold price converges to its
limiting belief (FAF's `thm:con`).
Source: mandate T4.2 ("state the per-threshold limit existence separately")
Kind: L
Fidelity: exact -/
theorem undecided_threshold_tendsto (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (X : LUV) (hX : UndecidedLUV DP X) (r : ℚ) :
    ConvergesTo (fun n => P n (X.gt r)) (limitingBelief P (X.gt r)) :=
  lic_limitingBelief_tendsto P DP hX.hcons (X.gt r)

/-- The grid LUV: threshold `r` at the splice atom with payload `⌜r⌝` — thresholds at pairwise
distinct fresh atoms.
Source: mandate T4.2 ("the thresholds are independent atoms")
Kind: D
Fidelity: exact -/
def gridLUV : LUV := ⟨fun r => spliceAtom (Encodable.encode r)⟩

/-- The grid LUV's thresholds are injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gridLUV_gt_injective : Function.Injective gridLUV.gt := by
  intro r r' h
  simp only [gridLUV, spliceAtom, Formula.atom.injEq] at h
  exact Encodable.encode_injective (spliceAtomCode_injective h)

/-- **`hval` is not implied by undecidedness.** Over a cleanroom-free process with a consistent
world at every stage, the grid LUV is undecided at every threshold in `(0,1)`, yet some
completed-theory world values it nowhere: the world holding `⌜X > 7/10⌝` and refuting `⌜X > 3/10⌝`
(both fresh atoms, set independently) can value `X` neither at `x ≥ 7/10` nor at `x ≤ 3/10`.
Source: [[corr-core-inventory]] 034(ii) (the inventory's "`hval` discharged" is false for independent threshold atoms); mandate T4.2, Known issue 6
Kind: P
Fidelity: exact (a counterexample to the universal reading)
Hyps: (a) -/
theorem gridLUV_undecided_not_valued (DP : DeductiveProcess) (hDP : CleanroomFreeProcess DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    UndecidedLUV DP gridLUV ∧
    ∃ v : PCWorld, v.ConsistentWithTheory DP ∧ ∀ x : ℝ, ¬ v.ValuesAt gridLUV x := by
  constructor
  · intro r _ _ n
    have hu := atomFreeProcess_splice_of_cleanroomFree hDP (Encodable.encode r)
    exact ⟨exists_consistent_holds_atom hu hworld n, exists_consistent_not_holds_atom hu hworld n⟩
  · obtain ⟨v₀, hv₀⟩ := DP.exists_consistentWithTheory hworld
    set a := spliceAtomCode (Encodable.encode (7 / 10 : ℚ)) with ha
    set b := spliceAtomCode (Encodable.encode (3 / 10 : ℚ)) with hb
    have hab : a ≠ b := by
      intro h
      have := Encodable.encode_injective (spliceAtomCode_injective h)
      norm_num at this
    have hua := atomFreeProcess_splice_of_cleanroomFree hDP (Encodable.encode (7 / 10 : ℚ))
    have hub := atomFreeProcess_splice_of_cleanroomFree hDP (Encodable.encode (3 / 10 : ℚ))
    refine ⟨setAtom (setAtom v₀ a true) b false,
      (consistentWithTheory_setAtom_iff hub _ false).mp
        ((consistentWithTheory_setAtom_iff hua v₀ true).mp hv₀), fun x hx => ?_⟩
    obtain ⟨-, -, hthr⟩ := hx
    have h7 : (setAtom (setAtom v₀ a true) b false).Holds (gridLUV.gt (7 / 10)) := by
      show (setAtom (setAtom v₀ a true) b false).Holds (Formula.atom a)
      rw [PCWorld.holds_atom]
      rw [setAtom_of_ne _ _ _ hab]
      exact (setAtom_self v₀ a true).mpr rfl
    have h3 : ¬ (setAtom (setAtom v₀ a true) b false).Holds (gridLUV.gt (3 / 10)) :=
      setAtom_not_holds_atom_false _ b
    have hx7 : ¬ (x < ((7 / 10 : ℚ) : ℝ)) := fun hlt => (hthr (7 / 10)).2 hlt h7
    have hx3 : ¬ (((3 / 10 : ℚ) : ℝ) < x) := fun hlt => h3 ((hthr (3 / 10)).1 hlt)
    push_cast at hx7 hx3
    linarith [not_lt.mp hx7, not_lt.mp hx3]

/-! ## T4.3 The limit CDF is antitone given the implications -/

/-- **Antitonicity of the limiting CDF, given the threshold implications in every stage.** If
`⌜X > r⌝ → ⌜X > r'⌝` (as `∼⌜X > r⌝ ⋎ ⌜X > r'⌝`) is in every stage of `DP`, then
`limitingBelief P (X.gt r) ≤ limitingBelief P (X.gt r')` (FAF's `lic_imp_eventually_le` and the
two limits). The hypothesis is the exact one used; without it the thresholds are independent and
monotonicity has no source (findings: the chat's "coherent CDF" needs the implications to be
revealed).
Source: [[corr-core-inventory]] 034(ii) ("a coherent CDF"); mandate T4.3
Kind: C
Fidelity: exact
Hyps: (a) `himp` is the stage membership of the implications (FAF's `thm:lex` premise shape) -/
theorem limitingBelief_antitone_of_imp_mem (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hcons : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (X : LUV)
    (r r' : ℚ) (himp : ∀ n, (∼(X.gt r) ⋎ X.gt r') ∈ DP.D n) :
    limitingBelief P (X.gt r) ≤ limitingBelief P (X.gt r') := by
  have hL := lic_limitingBelief_tendsto P DP hcons (X.gt r)
  have hL' := lic_limitingBelief_tendsto P DP hcons (X.gt r')
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hev := lic_imp_eventually_le P DP (X.gt r) (X.gt r') himp hcons ε hε
  exact le_of_tendsto_of_tendsto hL (hL'.add_const ε) hev

/-! ## T4.4 The criterion leaves the limit a prior -/

/-- The two-valued LUV at an atom: `⌜X > r⌝` is `⊤` for `r < 0`, the atom for `0 ≤ r < 1`, `⊥` for
`r ≥ 1`. Every world values it at the atom's payout.
Source: mandate T4.4 ("the two-valued LUV `X.gt r := spliceAtom 0` for `r ∈ [0,1)` and `⊥` for `r ≥ 1`")
Kind: D
Fidelity: exact -/
def atomLUV (u : ℕ) : LUV :=
  ⟨fun r => if r < 0 then ⊤ else if r < 1 then Formula.atom u else ⊥⟩

/-- On the day-`n` grid every threshold of `atomLUV u` is the atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomLUV_gt_grid (u : ℕ) (n i : ℕ) (hi : i < n + 1) :
    (atomLUV u).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ)) = Formula.atom u := by
  have h0 : ¬ ((i : ℚ) / ((n : ℚ) + 1) < 0) := by
    rw [not_lt]; positivity
  have h1 : (i : ℚ) / ((n : ℚ) + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast hi
  simp only [atomLUV]
  push_cast
  rw [if_neg h0, if_pos h1]

/-- **The expectation of `atomLUV u` is the atom's price, exactly, every day.**
Source: mandate T4.4 ("`expect` is then the atom's price up to the `expectApprox` grid" — here exactly, since every grid threshold is the atom)
Kind: P
Fidelity: stronger: exact, not up to the grid
Hyps: (a) -/
theorem expect_atomLUV (P : History) (u : ℕ) (n : ℕ) :
    (atomLUV u).expect P n = P n (Formula.atom u) := by
  unfold LUV.expect LUV.expectApprox
  rw [Finset.sum_congr rfl (fun i hi => by rw [atomLUV_gt_grid u n i (Finset.mem_range.mp hi)])]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

/-- No world holds `⊥`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma holds_bot_false (v : PCWorld) : ¬ v.Holds (⊥ : Sentence) := fun h => h

/-- Every world values `atomLUV u` at the atom's payout (`hval` holds for it).
Source: mandate T4.4 ("`hval` holds: every world values it at `0` or `1`")
Kind: L
Fidelity: exact -/
theorem atomLUV_valuesAt (v : PCWorld) (u : ℕ) :
    v.ValuesAt (atomLUV u) (v.payout (Formula.atom u)) := by
  refine ⟨(payout_mem_Icc v _).1, (payout_mem_Icc v _).2, fun r => ?_⟩
  by_cases hv : v.Holds (Formula.atom u)
  · have hp : v.payout (Formula.atom u) = 1 := by simp [PCWorld.payout, hv]
    rw [hp]
    constructor
    · intro hr
      have hr' : r < 1 := by exact_mod_cast hr
      simp only [atomLUV, if_pos hr']
      split_ifs
      · exact PCWorld.holds_top v
      · exact hv
    · intro hr
      have hr' : 1 < r := by exact_mod_cast hr
      have hn0 : ¬ r < 0 := not_lt.mpr (le_of_lt (lt_trans zero_lt_one hr'))
      have hn1 : ¬ r < 1 := not_lt.mpr hr'.le
      simp only [atomLUV, if_neg hn0, if_neg hn1]
      exact holds_bot_false v
  · have hp : v.payout (Formula.atom u) = 0 := by simp [PCWorld.payout, hv]
    rw [hp]
    constructor
    · intro hr
      have hr' : r < 0 := by exact_mod_cast hr
      simp only [atomLUV, if_pos hr']
      exact PCWorld.holds_top v
    · intro hr
      have hr' : 0 < r := by exact_mod_cast hr
      have hn0 : ¬ r < 0 := not_lt.mpr hr'.le
      simp only [atomLUV, if_neg hn0]
      split_ifs
      · exact hv
      · exact holds_bot_false v

/-- `atomLUV u` is undecided over any process free of `u` with a consistent world at every stage.
Source: mandate T4.4
Kind: L
Fidelity: exact -/
theorem atomLUV_undecided (DP : DeductiveProcess) (u : ℕ) (hu : AtomFreeProcess u DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) : UndecidedLUV DP (atomLUV u) := by
  intro r hr0 hr1 n
  have hgt : (atomLUV u).gt r = Formula.atom u := by
    simp [atomLUV, not_lt.mpr hr0.le, hr1]
  rw [hgt]
  exact ⟨exists_consistent_holds_atom hu hworld n, exists_consistent_not_holds_atom hu hworld n⟩

/-- **The criterion leaves the limit expectation of an undecided LUV a prior** — the content part,
proved outright: for an inductor `P` over `DP` with a fresh atom `u` and rationals `c ≠ c'`, the
two-valued LUV `atomLUV u` is undecided and valued in every world, and its expectation sequences
under the two projections `project P u (fun _ => c)` / `(fun _ => c')` converge to `c` and to `c'`
(li-projection's `project_atom_tendsto`, outright). The further conjunct that the two projections
are *inductors* rests on li-projection's OPEN (A) and is `undecided_limit_is_prior_inductors`
(`Witnesses.lean`). The LUV is two-valued — admittedly degenerate as a utility; see the report.
Source: [[corr-core-inventory]] 034(iii) (BLI paste l. 53, "a prior, with no calibration theorem behind it"; "legitimacy detection is a prior, not a theorem"); mandate T4.4
Kind: C
Fidelity: exact (two inductors, same process, same undecided LUV, different limit expectations), the inductor conjuncts separate
Hyps: (a) -/
theorem undecided_limit_is_prior (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ) (hu : AtomFreeProcess u DP)
    (c c' : ℚ) (hne : c ≠ c') :
    UndecidedLUV DP (atomLUV u) ∧
    (∀ v : PCWorld, ∃ x : ℝ, v.ValuesAt (atomLUV u) x) ∧
    ConvergesTo ((atomLUV u).expectSeq (project P u (fun _ => c))) c ∧
    ConvergesTo ((atomLUV u).expectSeq (project P u (fun _ => c'))) c' ∧
    (c : ℝ) ≠ c' := by
  refine ⟨atomLUV_undecided DP u hu hworld, fun v => ⟨_, atomLUV_valuesAt v u⟩, ?_, ?_,
    by exact_mod_cast hne⟩
  · have h := project_atom_tendsto P DP hworld u (fun _ => c) 0 (fun _ _ => rfl)
    refine h.congr fun n => ?_
    simp only [LUV.expectSeq, expect_atomLUV]
  · have h := project_atom_tendsto P DP hworld u (fun _ => c') 0 (fun _ _ => rfl)
    refine h.congr fun n => ?_
    simp only [LUV.expectSeq, expect_atomLUV]

/-! ## T4.5 Obedience versus deference -/

/-- **Obedience**: a sentence in a stage converges to price `1` at a summable rate — "true by
definition" (li-projection's `summable_one_sub_price_of_mem_stage`, imported).
Source: [[corr-core-inventory]] 035 (BLI paste l. 53, "their pronouncements are *elements of D*, in which case they are true by definition … that is obedience"); mandate T4.5
Kind: L
Fidelity: exact -/
theorem obedience_summable (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) {m : ℕ} {a : Sentence}
    (ha : a ∈ DP.D m) : Summable (fun n => 1 - P n a) :=
  summable_one_sub_price_of_mem_stage P DP hworld ha

/-- **Deference's bridging sentence is undecided**: if `a` ("`H` asserts `u > p`") is in a stage and
`⌜X > p⌝` is undecided, both verdicts on `⌜X > p⌝ ⋏ a` are plausible at every stage — nothing the
stages decide constrains the conditional quote of `⌜X > p⌝` on `a`. A statement about plausibility,
not about the conditional's limit (which T3.5's narrowing covers).
Source: [[corr-core-inventory]] 035 ("the bridging beliefs `P_n(u > p | H asserts u > p)` are themselves never decided"); mandate T4.5
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem undecided_and_decided (DP : DeductiveProcess) (X : LUV) (hX : UndecidedLUV DP X)
    {m : ℕ} {a : Sentence} (ha : a ∈ DP.D m) (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ n, (∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds (X.gt p ⋏ a)) ∧
      (∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds (X.gt p ⋏ a)) := by
  intro n
  obtain ⟨⟨v₁, hv₁, h₁⟩, ⟨v₂, hv₂, h₂⟩⟩ := hX p hp0 hp1 (max n m)
  have hsub : DP.D n ⊆ DP.D (max n m) := DP.mono_le (le_max_left n m)
  have hm : DP.D m ⊆ DP.D (max n m) := DP.mono_le (le_max_right n m)
  refine ⟨⟨v₁, fun φ hφ => hv₁ φ (hsub hφ), ?_⟩, ⟨v₂, fun φ hφ => hv₂ φ (hsub hφ), ?_⟩⟩
  · exact (PCWorld.holds_and v₁ _ _).mpr ⟨h₁, hv₁ a (hm ha)⟩
  · intro h
    exact h₂ ((PCWorld.holds_and v₂ _ _).mp h).1

end Cleanroom.Li.LiSpliceCondition
