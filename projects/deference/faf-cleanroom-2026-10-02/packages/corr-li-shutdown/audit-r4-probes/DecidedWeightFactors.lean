import Cleanroom.Corrigibility.CorrLiShutdown.Legitimacy
import Cleanroom.Deference.DefSelfTrust.FeatComb

/-! # Audit round 4 (adversarial) — probe: is `decidedWeight_factors_open` really open over FAF?

Repair round 3 stated T2(b) reading (a) OPEN (`decidedWeight_factors_open`, `Legitimacy.lean`
§(b′)) and recorded in findings F19 / the open list / the module header that the mandate's `loe`
route "resists for a structural reason": FAF's `lic_linearity_of_expectation_seq` needs
`DeterminedViaTheory`, which (so the record says) "asks the day-`n` deductive state `D_n` to
decide the value of the combination … and no deductive process decides the literals of its own
day-`n` prices at day `n`".

FAF's `LUVCombination.DeterminedViaTheory` quantifies over `v.ConsistentWithTheory DP`, i.e.
`∀ k, v.ConsistentWith (DP.D k)` — the completed theory, not the day-`n` stage — and evaluates
the coefficient feature at the market (`(a n).denote P`, the value the *market* computed). So the
recorded obstacle is not FAF's hypothesis. What the exact `loe` does not absorb is the mesh slack
(`meshProductLUV_valuesAt`: the product is realized within `1/(n+1)`), and FAF's `thm:expprovind`
substrate `lic_expect_combination_provind_le/ge` takes one-sided completed-world bounds that
absorb exactly such a vanishing slack. This probe:

* `probe_currentWeight_mesh_valuesAt` — the completed-theory worlds value the mesh product of
  the *current-day* weight quote at `w_n · x` within `1/(n+1)` (FAF's mesh law, one line);
* `probe_decidedWeight_factors` — **the OPEN statement, proved** (statement copied verbatim from
  `decidedWeight_factors_open`): `E_n(⌜X_n · w_n⌝) ≈ₙ w_n · E_n(X_n)`, through
  `def-self-trust`'s `featCombSyntax` (the two-term feature-coefficient combination
  `a_n·X_n − Z_n` with `a` the generating feature of `w`) and `expect_asympLE/GE_of_eventually`
  (FAF's `lic_expect_combination_provind_le/ge` under an eventual world bound).

Not imported by the library. -/

namespace Cleanroom.Corrigibility.CorrLiShutdown.AuditR4

open LogicalInduction Filter Topology
open Cleanroom.Found.DefLattice Cleanroom.Deference.DefSelfTrust
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment

noncomputable section

/-- The two-term feature-coefficient combination `a_n · X_n − Z_n` (constant `0`). -/
def probeComb (a : ℕ → EF) (X Z : ℕ → LUV) : ℕ → LUVCombination :=
  featComb (fun _ => EF.const 0) [(a, X), (fun _ => EF.const (-1), Z)]

lemma probeComb_terms (a : ℕ → EF) (X Z : ℕ → LUV) (n : ℕ) :
    (probeComb a X Z n).terms = [(a n, X n), (EF.const (-1), Z n)] := by
  simp [probeComb, featComb]

lemma probeComb_expect (P : History) (a : ℕ → EF) (X Z : ℕ → LUV) (n : ℕ) :
    (probeComb a X Z n).expect P n = (a n).denote P * (X n).expect P n - (Z n).expect P n := by
  rw [probeComb, featComb_expect]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const]
  push_cast; ring

lemma probeComb_value (P : History) (a : ℕ → EF) (X Z : ℕ → LUV) (n : ℕ) (ν : LUV → ℝ) :
    (probeComb a X Z n).value P ν = (a n).denote P * ν (X n) - ν (Z n) := by
  rw [probeComb, featComb_value]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const]
  push_cast; ring

lemma probeComb_l1Norm (P : History) (a : ℕ → EF) (X Z : ℕ → LUV) (n : ℕ) :
    (probeComb a X Z n).l1Norm P = |(a n).denote P| + 1 := by
  rw [probeComb, featComb_l1Norm]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, EF.denote_const]
  push_cast
  simp only [abs_zero, abs_neg, abs_one, zero_add, add_zero]

/-- Compact syntax for the probe combination, from `def-self-trust`'s `featCombSyntax`. -/
def probeSyntax (a : ℕ → EF) (ha : PGenerableWeighting a) (X Z : ℕ → LUV)
    (hX : LUV.MachineThresholdCodeSeq X) (hZ : LUV.MachineThresholdCodeSeq Z) :
    LUVCombinationSyntax (probeComb a X Z) :=
  featCombSyntax (fun _ => EF.const 0) (constWeighting 0) [(a, X), (fun _ => EF.const (-1), Z)]
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact ha
      · exact constWeighting (-1))
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact hX
      · exact hZ)

variable (T : ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T]

/-- **P1.** Every completed-theory world values the mesh product of the current-day weight quote
at `x · w_n` within `1/(n+1)`: the quote literals of the day-`n` weight are decided by the
completed theory (`RationalQuoteCode.reflected`), exactly as for FAF's deferred weight. -/
theorem probe_currentWeight_mesh_valuesAt (X : ℕ → LUV) (w : ℕ → ℚ)
    (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1) (hw : PGenerableRat (liaHistory (paperDP T)) w)
    (n : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) {x : ℝ}
    (hx : v.ValuesAt (X n) x) :
    ∃ z, v.ValuesAt (meshProductLUV (paperCurrentWeightQuoteCode T w hw hmem) X n) z ∧
      |z - x * (w n : ℝ)| ≤ 1 / ((n : ℝ) + 1) :=
  meshProductLUV_valuesAt (paperQuotationPresentation T) _ X n v hv hx

/-- **P2.** `decidedWeight_factors_open`, proved: statement copied verbatim from
`Legitimacy.lean` §(b′). -/
theorem probe_decidedWeight_factors (X : ℕ → LUV) (hX : LUV.MachineThresholdCodeSeq X)
    (hval : Valued (paperDP T) X) (w : ℕ → ℚ) (hmem : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (hw : PGenerableRat (liaHistory (paperDP T)) w) :
    (fun n => (meshProductLUV (paperCurrentWeightQuoteCode T w hw hmem) X n).expect
        (liaHistory (paperDP T)) n) ≈ₙ
      (fun n => (w n : ℝ) * (X n).expect (liaHistory (paperDP T)) n) := by
  classical
  haveI := paperLIA T
  obtain ⟨a, ha⟩ := id hw
  have haW : PGenerableWeighting a := ⟨ha.polyTok, ha.rank_le, ha.closed⟩
  set Z : ℕ → LUV := meshProductLUV (paperCurrentWeightQuoteCode T w hw hmem) X with hZdef
  have hZ : LUV.MachineThresholdCodeSeq Z :=
    meshProductLUV_machineThresholdCodeSeq (paperCurrentWeightQuoteCode T w hw hmem) hX
  have S : LUVCombinationSyntax (probeComb a X Z) := probeSyntax a haW X Z hX hZ
  have hbdd : ∀ n, (probeComb a X Z n).l1Norm (liaHistory (paperDP T)) ≤ 2 := by
    intro n
    rw [probeComb_l1Norm, ha.denote]
    have h := hmem n
    have h1 : (0 : ℝ) ≤ w n := by exact_mod_cast h.1
    have h2 : (w n : ℝ) ≤ 1 := by exact_mod_cast h.2
    rw [abs_of_nonneg h1]
    linarith
  have hmesh : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) → ∀ x,
      v.ValuesAt (X n) x → ∃ z, v.ValuesAt (Z n) z ∧ |z - x * (w n : ℝ)| ≤ 1 / ((n : ℝ) + 1) :=
    fun n v hv x hx =>
      meshProductLUV_valuesAt (paperQuotationPresentation T)
        (paperCurrentWeightQuoteCode T w hw hmem) X n v hv hx
  have hwv : LUVCombination.WorldValued (probeComb a X Z) (paperDP T) := by
    intro n v hv
    obtain ⟨x, hx⟩ := hval n v hv
    obtain ⟨z, hz, -⟩ := hmesh n v hv x hx
    refine ⟨fun L => if L = X n then x else z, ?_⟩
    intro p hp
    rw [probeComb_terms] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · simpa using hx
    · show v.ValuesAt (Z n) (if Z n = X n then x else z)
      split_ifs with h
      · rw [h]; exact hx
      · exact hz
  have hvalue : ∀ n (v : PCWorld), v.ConsistentWithTheory (paperDP T) → ∀ ν,
      (probeComb a X Z n).ValuesAt v ν →
      |(probeComb a X Z n).value (liaHistory (paperDP T)) ν| ≤ 1 / ((n : ℝ) + 1) := by
    intro n v hv ν hν
    have hX' : v.ValuesAt (X n) (ν (X n)) :=
      hν (a n, X n) (by rw [probeComb_terms]; simp)
    have hZ' : v.ValuesAt (Z n) (ν (Z n)) :=
      hν (EF.const (-1), Z n) (by rw [probeComb_terms]; simp)
    obtain ⟨z, hz, hzb⟩ := hmesh n v hv _ hX'
    rw [probeComb_value, ha.denote, hZ'.eq hz,
      show (w n : ℝ) * ν (X n) - z = -(z - ν (X n) * (w n : ℝ)) by ring, abs_neg]
    exact hzb
  have hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((paperDP T).D n) :=
    fun n => paperDP_hworld T n
  have hsmall : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ ε := by
    intro ε hε
    have h := (Metric.tendsto_nhds.mp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))) ε hε
    filter_upwards [h] with n hn
    rw [Real.dist_eq, _root_.sub_zero, abs_lt] at hn
    exact hn.2.le
  have hle : ∀ ε > 0,
      (fun n => (probeComb a X Z n).expect (liaHistory (paperDP T)) n) ≲ₙ fun _ => ε := by
    intro ε hε
    refine expect_asympLE_of_eventually (P := liaHistory (paperDP T)) (DP := paperDP T) S hbdd
      hwv hε.le ?_ hworld
    filter_upwards [hsmall ε hε] with n hn v hv ν hν
    have h := hvalue n v hv ν hν
    rw [abs_le] at h
    linarith [h.2]
  have hge : ∀ ε > 0,
      (fun n => (probeComb a X Z n).expect (liaHistory (paperDP T)) n) ≳ₙ fun _ => -ε := by
    intro ε hε
    refine expect_asympGE_of_eventually (P := liaHistory (paperDP T)) (DP := paperDP T) S hbdd
      hwv (by linarith) ?_ hworld
    filter_upwards [hsmall ε hε] with n hn v hv ν hν
    have h := hvalue n v hv ν hν
    rw [abs_le] at h
    linarith [h.1]
  unfold AsympEq
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h1 := hle (ε / 4) (by linarith) (ε / 4) (by linarith)
  have h2 := hge (ε / 4) (by linarith) (ε / 4) (by linarith)
  filter_upwards [h1, h2] with n hn1 hn2
  simp only [probeComb_expect, ha.denote] at hn1 hn2
  rw [Real.dist_eq, _root_.sub_zero, abs_lt]
  constructor <;> linarith

end

end Cleanroom.Corrigibility.CorrLiShutdown.AuditR4

#print axioms Cleanroom.Corrigibility.CorrLiShutdown.AuditR4.probe_currentWeight_mesh_valuesAt
#print axioms Cleanroom.Corrigibility.CorrLiShutdown.AuditR4.probe_decidedWeight_factors
