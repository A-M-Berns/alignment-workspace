import Cleanroom.Li.LiSpliceCondition.Defs
import Cleanroom.Li.LiProjection.Prescribe
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.LiminfLimsup

/-!
# `li-splice-condition` · Perturb: finite perturbations, tail properties, criterion-preservation (T2)

Package `Cleanroom.Li.LiSpliceCondition` ([[li-splice-condition-mandate]]), file 8 of the layout.
Everything about finite perturbations goes through FAF's **corrected** closure theorem
(`FiniteSupportPerturbation`, finitely many `(day, sentence)` coordinates), never the printed one,
which FAF refutes (`FinitePerturbationCounterexample.not_overgeneral_ifp`).

* **T2.1** `CriterionPreserving m DP` (`Defs.lean`) and its one consequence (`CriterionPreserving.apply`).
* **T2.2** The finite-patch policy is criterion-preserving (`patchPolicy_criterionPreserving`,
  li-projection's `prescribe_finiteSupport`). **T2.3** The whole-day overwrite policy is **not**
  (`overwriteBefore_not_criterionPreserving`, li-projection's `prescribe_wholeDay_closure_false`
  restated in this vocabulary): the note's "Closure under Finite Perturbations makes every finite
  pushing legitimate", read at the whole-day grain, is refuted; the surviving neighbour is T2.2.
* **T2.4** Statement 2(a) at the finite-coordinate grain: no property of all inductors over `DP`
  excludes any finitely-supported pattern of prices (`criterion_only_property_of_patch`); the
  corrigibility instance `defies_first_N_presses`. Statement 2(b) is li-projection's
  `convergence_rate_not_computable` (proved outright there; cited, not restated); 2(c) is a
  conjecture, recorded.
* **T2.5** The grade lattice over bare real sequences: "eventually above every margin"
  ⟺ "finitely many violations at every margin" ⟺ "summable ramp weight at every margin" (the ramp
  offset `δ` is absorbed), and, for a bounded sequence, ⟺ `t ≤ liminf`; and summability of a
  nonnegative sequence ⟺ bounded partial sums. No named grade is defined (`tt-ladder` owns the
  gated ones; these are ungated, over bare sequences).
* **T2.6** Every `liminf`/`limsup` statement is invariant under a finite-support change of the
  sequence, and a finite patch changes each sentence's price sequence on finitely many days.
* **T2.7(i)** Refreezing with `g = id` is the identity.
-/

namespace Cleanroom.Li.LiSpliceCondition

open LogicalInduction LO.Propositional Cleanroom.Li.LiProjection Filter Topology

/-! ## T2.1 Criterion preservation -/

/-- The one consequence of criterion preservation: the pushed process inherits every theorem
proved for inductors (`[IsLogicalInductor (m P) DP]`). The note's "`cee`/`ccee` hold for the pushed
process" is this instance applied to FAF's `lic_expected_future_expectations`; no restatement.
Source: [[corr-wf13-inventory]] 069 (I5.7); mandate T2.1
Kind: L
Fidelity: exact -/
theorem CriterionPreserving.apply {m : History → History} {DP : DeductiveProcess}
    (hm : CriterionPreserving m DP) (P : History) [hLI : IsLogicalInductor P DP] :
    IsLogicalInductor (m P) DP :=
  hm P hLI

/-! ## T2.2 Finite pushing is legitimate — at the finite-coordinate grain -/

/-- **The finite-patch policy is criterion-preserving**: for any finite coordinate set `S` and any
table `t` with values in `[0,1]` on `S`, `P ↦ patch P S t` sends inductors over `DP` to inductors
over `DP` (li-projection's `prescribe_finiteSupport`, FAF's corrected `thm:ifp`). This is the
reading of "any finite pushing of the belief process is legitimate" that survives.
Source: [[corr-wf13-inventory]] 069 (`positive/li.md` I5.7, criterion-preservation as legitimacy); mandate T2.2
Kind: L
Fidelity: variant: finite support (finitely many `(day, sentence)` coordinates), not a whole-day prefix
Hyps: (a) -/
theorem patchPolicy_criterionPreserving (DP : DeductiveProcess) (S : Finset (ℕ × Sentence))
    (t : ℕ → Sentence → ℚ) (ht : ∀ p ∈ S, 0 ≤ t p.1 p.2 ∧ t p.1 p.2 ≤ 1) :
    CriterionPreserving (patchPolicy S t) DP :=
  fun P hLI => prescribe_finiteSupport P DP (hLI := hLI) S t ht

/-! ## T2.3 Not at the whole-day grain -/

/-- **The whole-day overwrite policy is not criterion-preserving in general.** It is not the case
that for every process, day `N` and table `t` whose overwrite is a computable market (on some
history — equivalently, for computable histories, on any), the policy "overwrite days `< N` by
`t`" sends every inductor over `DP` to an inductor. This is li-projection's
`prescribe_wholeDay_closure_false` (FAF's `not_overgeneral_ifp`: one overwritten day is an
infinite computable table carrying unbounded advice) in the `CriterionPreserving` vocabulary.
Quantifier shape: the `P'` whose overwrite is a computable market is decoupled from the inductor
`P` because `CriterionPreserving` cannot carry the computability condition inside the policy; for
the inductors the statement is about the two are equivalent, and the content is li-projection's
form, from which this is a three-line corollary (so the Kind is `C`, not `P`: adversarial audit r1
N4/N8).
Source: [[corr-wf13-inventory]] 069 (I5.7, "every finite pushing of the belief process is legitimate" — ATTRIBUTION-UNVETTED that the whole-day reading is intended); [[corr-wf14-inventory]] 072 (Statement 2(a) as printed); mandate T2.3
Kind: C
Fidelity: exact (the refuted reading is the whole-day one; the surviving neighbour is `patchPolicy_criterionPreserving`)
Hyps: (a) -/
theorem overwriteBefore_not_criterionPreserving :
    ¬ ∀ (DP : DeductiveProcess) (N : ℕ) (t : ℕ → Sentence → ℚ),
        (∃ P' : History, ComputableMarket (overwriteBefore P' N t)) →
        CriterionPreserving (fun P => overwriteBefore P N t) DP := by
  intro H
  apply prescribe_wholeDay_closure_false
  intro P DP N t hLI hCM
  exact H DP N t ⟨P, hCM⟩ P hLI

/-! ## T2.4 Statement 2(a) at the finite-coordinate grain -/

/-- **No property of all inductors excludes any finitely-supported pattern of prices.** For a
property `Φ` of histories holding of every inductor over `DP`, every finite patch of an inductor
has `Φ`. This is Statement 2(a) restated at the grain FAF's corrected closure theorem supports; as
printed ("every finite prefix of belief states — arbitrary, incoherent, catastrophic"), 2(a) cites
the theorem FAF refutes (`overwriteBefore_not_criterionPreserving`; findings).
Source: [[corr-wf14-inventory]] 072 (`invariant-final.md` Statement 2(a), "no theorem provable from the criterion alone excludes any finite prefix of belief states"); mandate T2.4
Kind: C
Fidelity: variant: finitely many coordinates, not a whole-day prefix
Hyps: (a) -/
theorem criterion_only_property_of_patch (DP : DeductiveProcess) (Φ : History → Prop)
    (hΦ : ∀ P : History, IsLogicalInductor P DP → Φ P) (P : History) [hLI : IsLogicalInductor P DP]
    (S : Finset (ℕ × Sentence)) (t : ℕ → Sentence → ℚ)
    (ht : ∀ p ∈ S, 0 ≤ t p.1 p.2 ∧ t p.1 p.2 ≤ 1) :
    Φ (patch P S t) :=
  hΦ _ (prescribe_finiteSupport P DP (hLI := hLI) S t ht)

/-- The press coordinates: `(n, ψ n)` for `n ≤ N`.
Source: mandate T2.4
Kind: D
Fidelity: exact -/
def pressCoords (ψ : ℕ → Sentence) (N : ℕ) : Finset (ℕ × Sentence) :=
  (Finset.range (N + 1)).image fun n => (n, ψ n)

/-- **The corrigibility instance**: for an inductor `P` over `DP` and a press family `ψ`
("continuing is wrong on day `n`"), the patch pricing every `ψ n`, `n ≤ N`, at exactly `0` is an
inductor over `DP` — so no theorem about inductors excludes defying each of the first `N` presses.
The prefix is finitely many *coordinates*, which is why the instance survives the refutation of the
printed closure theorem.
Source: [[corr-wf14-inventory]] 072 (Statement 2(a), "for every `N` there is a logical inductor pricing 'continuing is wrong' at `0` on every pressed day `n ≤ N`"); mandate T2.4
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem defies_first_N_presses (P : History) (DP : DeductiveProcess) [hLI : IsLogicalInductor P DP]
    (ψ : ℕ → Sentence) (N : ℕ) :
    IsLogicalInductor (patch P (pressCoords ψ N) (fun _ _ => 0)) DP ∧
    ∀ n, n ≤ N → patch P (pressCoords ψ N) (fun _ _ => 0) n (ψ n) = 0 := by
  refine ⟨prescribe_finiteSupport P DP (hLI := hLI) _ _ (fun _ _ => by norm_num), fun n hn => ?_⟩
  rw [patch_mem P _ _ (by
    simp only [pressCoords, Finset.mem_image, Finset.mem_range]
    exact ⟨n, by omega, rfl⟩)]
  simp

/-! ## T2.5 The grade lattice collapses (bare sequences) -/

/-- The ramp indicator of `x < a` at width `δ`: `1` for `x ≤ a − δ`, `0` for `x ≥ a`, linear between.
Source: [[corr-wf14-2-inventory]] 026 (`Ind_δ(x < a)`); mandate T2.5 ("state the ramp exactly")
Kind: D
Fidelity: exact -/
noncomputable def rampBelow (δ a x : ℝ) : ℝ := max 0 (min 1 ((a - x) / δ))

/-- The ramp is `1` below `a − δ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rampBelow_eq_one {δ a x : ℝ} (hδ : 0 < δ) (h : x ≤ a - δ) : rampBelow δ a x = 1 := by
  unfold rampBelow
  have : 1 ≤ (a - x) / δ := by rw [le_div_iff₀ hδ]; linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

/-- The ramp is `0` at and above `a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rampBelow_eq_zero {δ a x : ℝ} (hδ : 0 < δ) (h : a ≤ x) : rampBelow δ a x = 0 := by
  unfold rampBelow
  have : (a - x) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  rw [max_eq_left (le_trans (min_le_right _ _) this)]

/-- The ramp lies in `[0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rampBelow_mem_Icc (δ a x : ℝ) : 0 ≤ rampBelow δ a x ∧ rampBelow δ a x ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- **Eventually above every margin ⟺ finitely many violations at every margin.**
Source: [[corr-wf14-2-inventory]] 026 (Lemma 1); mandate T2.5
Kind: P
Fidelity: exact (bare sequences, no named grade)
Hyps: (a) -/
theorem eventually_iff_finite_violations (E : ℕ → ℝ) (t : ℝ) :
    (∀ ε > 0, ∀ᶠ n in atTop, t - ε ≤ E n) ↔ ∀ ε > 0, {n | E n < t - ε}.Finite := by
  constructor
  · intro h ε hε
    have := (h ε hε)
    rw [Filter.eventually_atTop] at this
    obtain ⟨N, hN⟩ := this
    refine (Finset.range N).finite_toSet.subset fun n hn => ?_
    simp only [Set.mem_setOf_eq] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    exact absurd (hN n (not_lt.mp hcon)) (not_le.mpr hn)
  · intro h ε hε
    have hfin := h ε hε
    rw [Filter.eventually_atTop]
    obtain ⟨N, hN⟩ := hfin.bddAbove
    refine ⟨N + 1, fun n hn => ?_⟩
    by_contra hcon
    have := hN (show n ∈ {n | E n < t - ε} from not_le.mp hcon)
    omega

/-- **Finitely many violations at every margin ⟺ summable ramp weight at every margin**, for any
fixed ramp width `δ > 0` (the offset is absorbed by re-quantifying the margin).
Source: [[corr-wf14-2-inventory]] 026 (Lemma 2, with the inventory's flag on the `δ` offset); mandate T2.5
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem finite_violations_iff_summable_ramp (E : ℕ → ℝ) (t δ : ℝ) (hδ : 0 < δ) :
    (∀ ε > 0, {n | E n < t - ε}.Finite) ↔
      ∀ ε > 0, Summable (fun n => rampBelow δ (t - ε) (E n)) := by
  constructor
  · intro h ε hε
    refine summable_of_ne_finset_zero (s := (h ε hε).toFinset) fun n hn => ?_
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hn
    exact rampBelow_eq_zero hδ hn
  · intro h ε hε
    by_contra hinf
    -- at margin `ε/2`, every violation `E n < t − ε` puts the ramp at least `min 1 ((ε/2)/δ) > 0`;
    -- infinitely many such `n` contradict the summable sequence's terms tending to `0`.
    have hs := h (ε / 2) (by positivity)
    have h0 := hs.tendsto_atTop_zero
    have hcpos : 0 < min (1 : ℝ) ((ε / 2) / δ) := lt_min one_pos (by positivity)
    have hfreq : ∃ᶠ n in atTop, min (1 : ℝ) ((ε / 2) / δ) ≤ rampBelow δ (t - ε / 2) (E n) := by
      rw [Filter.frequently_atTop]
      intro a
      have hI : {n | E n < t - ε}.Infinite := hinf
      obtain ⟨n, hn, hna⟩ := hI.exists_gt a
      refine ⟨n, hna.le, ?_⟩
      simp only [Set.mem_setOf_eq] at hn
      unfold rampBelow
      refine le_trans (min_le_min_left 1 ?_) (le_max_right _ _)
      exact div_le_div_of_nonneg_right (by linarith) hδ.le
    have hev : ∀ᶠ n in atTop, rampBelow δ (t - ε / 2) (E n) < min (1 : ℝ) ((ε / 2) / δ) := by
      have b := (Metric.tendsto_nhds.mp h0) _ hcpos
      filter_upwards [b] with n hb
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (rampBelow_mem_Icc _ _ _).1] at hb
    obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hev).exists
    exact absurd hn1 (not_le.mpr hn2)

/-- **Eventually above every margin ⟺ `t ≤ liminf`**, for a bounded sequence.
Source: [[corr-wf14-2-inventory]] 026 (the `liminf` rung); mandate T2.5
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem eventually_iff_le_liminf (E : ℕ → ℝ) (t : ℝ) (hb : ∀ n, |E n| ≤ 1) :
    (∀ ε > 0, ∀ᶠ n in atTop, t - ε ≤ E n) ↔ t ≤ liminf E atTop := by
  have hbdd : IsBoundedUnder (· ≥ ·) atTop E :=
    isBoundedUnder_of ⟨-1, fun n => by linarith [(abs_le.mp (hb n)).1]⟩
  have hcob : IsCoboundedUnder (· ≥ ·) atTop E :=
    (isBoundedUnder_of ⟨1, fun n => (abs_le.mp (hb n)).2⟩ :
      IsBoundedUnder (· ≤ ·) atTop E).isCoboundedUnder_ge
  rw [Filter.le_liminf_iff hcob hbdd]
  constructor
  · intro h b hb'
    have := h ((t - b) / 2) (by linarith)
    filter_upwards [this] with n hn
    linarith
  · intro h ε hε
    have := h (t - ε) (by linarith)
    filter_upwards [this] with n hn
    exact hn.le

/-- **Summability of a nonnegative sequence ⟺ bounded partial sums.**
Source: [[corr-wf14-2-inventory]] 026 (the bounded-violation rung); mandate T2.5
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem summable_iff_partialSums_bdd (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    Summable w ↔ ∃ C : ℝ, ∀ n, ∑ i ∈ Finset.range n, w i ≤ C := by
  constructor
  · intro h
    exact ⟨∑' i, w i, fun n => h.sum_le_tsum (Finset.range n) (fun i _ => hw i)⟩
  · rintro ⟨C, hC⟩
    exact summable_of_sum_range_le hw hC

/-! ## T2.6 Every criterion-only guarantee is a tail property -/

/-- A `liminf` is invariant under a finite-support change of the sequence.
Source: [[corr-wf14-inventory]] 092 (`li-final.md` S3, "any liminf/limsup is insensitive to any finite prefix"); mandate T2.6
Kind: L
Fidelity: exact -/
theorem liminf_congr_of_finite (E E' : ℕ → ℝ) (h : {n | E n ≠ E' n}.Finite) :
    liminf E atTop = liminf E' atTop :=
  Filter.liminf_congr (by
    rw [← Nat.cofinite_eq_atTop]
    exact (Set.Finite.eventually_cofinite_notMem h).mono fun n hn => not_not.mp hn)

/-- A `limsup` is invariant under a finite-support change of the sequence.
Source: [[corr-wf14-inventory]] 092; mandate T2.6
Kind: L
Fidelity: exact -/
theorem limsup_congr_of_finite (E E' : ℕ → ℝ) (h : {n | E n ≠ E' n}.Finite) :
    limsup E atTop = limsup E' atTop :=
  Filter.limsup_congr (by
    rw [← Nat.cofinite_eq_atTop]
    exact (Set.Finite.eventually_cofinite_notMem h).mono fun n hn => not_not.mp hn)

/-- A finite patch changes each sentence's price sequence on finitely many days.
Source: mandate T2.6
Kind: L
Fidelity: exact -/
theorem patch_ne_finite (P : History) (S : Finset (ℕ × Sentence)) (t : ℕ → Sentence → ℚ)
    (φ : Sentence) : {n | patch P S t n φ ≠ P n φ}.Finite := by
  refine (S.image Prod.fst).finite_toSet.subset fun n hn => ?_
  simp only [Set.mem_setOf_eq] at hn
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  by_contra hcon
  apply hn
  apply patch_notMem
  intro hmem
  exact hcon ⟨(n, φ), hmem, rfl⟩

/-- **Every `liminf`/`limsup` guarantee about a price sequence is a tail property**: a finite patch
leaves both unchanged, for every sentence.
Source: [[corr-wf14-inventory]] 092 (`li-final.md` Statement 9(a)); mandate T2.6
Kind: L
Fidelity: exact -/
theorem liminf_limsup_patch (P : History) (S : Finset (ℕ × Sentence)) (t : ℕ → Sentence → ℚ)
    (φ : Sentence) :
    liminf (fun n => patch P S t n φ) atTop = liminf (fun n => P n φ) atTop ∧
    limsup (fun n => patch P S t n φ) atTop = limsup (fun n => P n φ) atTop :=
  ⟨liminf_congr_of_finite _ _ (patch_ne_finite P S t φ),
   limsup_congr_of_finite _ _ (patch_ne_finite P S t φ)⟩

/-! ## T2.7 (i) Refreezing with the identity -/

/-- Refreezing every day (`g = id`) is the identity, so it keeps the criterion.
Source: [[bli-soto-b-inventory]] 016(i); mandate T2.7(i)
Kind: L
Fidelity: exact -/
theorem staleHistory_id (P : History) : staleHistory P id = P := rfl

/-- `staleHistory P id` is an inductor when `P` is.
Source: mandate T2.7(i)
Kind: L
Fidelity: exact -/
theorem staleHistory_id_isLogicalInductor (P : History) (DP : DeductiveProcess)
    [hLI : IsLogicalInductor P DP] : IsLogicalInductor (staleHistory P id) DP :=
  hLI

end Cleanroom.Li.LiSpliceCondition
