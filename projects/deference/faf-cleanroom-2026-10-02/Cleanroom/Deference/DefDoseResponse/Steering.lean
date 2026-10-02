import Cleanroom.Deference.DefDoseResponse.Arms
import Cleanroom.Deference.DefDoseResponse.Audit
import Cleanroom.Deference.DefDoseResponse.Advisor
import Cleanroom.Li.LiProjection.Market
import LogicalInduction.Properties.ExpectationAffine

/-!
# `def-dose-response` · Steering: dose-graded, detected, criterion-compliant (T2)

Fix `γ ∈ (0,1)`, `N > 0`, a committed stream `a` with `a_j = v` for `j < N` (the steered prefix,
produced by `Advisor.lean`'s `steeredAdvisor` when `v` is exact at every mesh `≤ N`), and coins
`c_i`. Write `s := γ(v − ½)` and `p̂_i := realizedDose (c i) N`. **One-way throughout**: the arms
read the fixed `a`; in (b-half) the advisor reads the fixed production arm.

* **(a) dose-graded destinations** (`dose_graded_destination`, `dose_graded_expect_tendsto`):
  `limitingBelief (arm i) u = ½ + s p̂_i` (`li-projection`'s `limitingBelief_project_atom` and (∗)),
  and the expectation form `𝔼^{(i)}_n(𝟙u) → ½ + s p̂_i`. The expectation step is **derived from
  the base criterion alone**: FAF's `𝟙(φ)` averages `n+1` copies of the price of `φ ⋏ ∼∼φ`
  (`indicatorOf_expect_eq`, an identity of every history), the projection prices
  `u ⋏ ∼∼u` at `q_n·P̄_n(⊤ ⋏ ∼∼⊤) + (1−q_n)·P̄_n(⊥ ⋏ ∼∼⊥)`, and the base inductor's provability
  induction sends those to `1` and `0`. So (a) and (d) hold for the arm *as a market* and do
  **not** rest on `li-projection` (A); the mandate's route through FAF's
  `lic_expectation_indicator` on the arm is also shipped (`arm_indicator_expect_asympEq_lic`,
  which does rest on (A)) — anson-2-030's provenance upgrade of the zip's `cross_arm_audit_fires`
  either way.
* **(b-half)** (`production_quote_tendsto`): for any inductor `A` over the mirror ledger of the
  production arm, `A`'s quote stream converges to the arm's destination `½ + s p̂_1`
  (`Advisor.lean`'s `mirror_quote_tendsto` on (a)); hence every within-arm residual vanishes over
  every battery (**Cor T2.1**, memory asymmetry).
* **(c)** refuted as stated / surviving neighbour: `Advisor.lean`'s
  `steeredAdvisor_isLogicalInductor`, instantiated here at the mirror process
  (`steeredAdvisor_mirror_inductor`); the refutation of the note's closure reading is
  `li-projection`'s `prescribe_wholeDay_closure_false` (findings F2).
* **(d) the audit fires** (`cross_arm_audit_fires`): `G^{ij}_N(u) → s(p̂_i − p̂_j)`, nonzero when
  `s ≠ 0` and the realized doses differ (`N`-separation, a hypothesis on fixed `{0,1}` prefixes).
* **(e)** is `Arms.lean`'s `non_attribution`.

The arm's `MarketComputation` (needed to state the mirror ledger) is at grade (a):
`computableMarket_project_ofMachineRatCodes` on the LIA's certificate (`arm_computableMarket`).
-/

namespace Cleanroom.Deference.DefDoseResponse

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Li.LiProjection
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc Cleanroom.Deference.DefTrackingPin
open Filter Topology

/-! ## The indicator mesh identity and the projected price of `u ⋏ ∼∼u` -/

/-- **FAF's indicator LUV averages the price of `φ ⋏ ∼∼φ`**: for every history,
`𝔼_n(𝟙(φ)) = P_n(φ ⋏ ∼∼φ)` — the `n+1` thresholds `i/(n+1)`, `i ≤ n`, all lie in `[0,1)`, where
`LUV.indicatorOf φ` has the threshold sentence `φ ⋏ ∼∼φ`. No criterion.
Source: FAF `LUV.indicatorOf` (`Framework/Expectations.lean:612`) and `def:e`; mandate T2 trap (ii)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem indicatorOf_expect_eq (P : History) (n : ℕ) (φ : Sentence) :
    (LUV.indicatorOf φ).expect P n = P n (φ ⋏ ∼∼φ) := by
  simp only [LUV.expect, LUV.expectApprox]
  have h : ∀ i ∈ Finset.range (n + 1),
      P n ((LUV.indicatorOf φ).gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))) = P n (φ ⋏ ∼∼φ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h0 : ¬ ((i : ℚ) / ((n : ℚ) + 1) < 0) := not_lt.mpr (by positivity)
    have h1 : (i : ℚ) / ((n : ℚ) + 1) < 1 := by
      rw [div_lt_one (by positivity)]; exact_mod_cast hi
    simp [LUV.indicatorOf, h0, h1]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Substituting `⊤` for `u` in `u ⋏ ∼∼u`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem substAtom_atomDouble_true (u : ℕ) :
    ((Formula.atom u ⋏ ∼∼Formula.atom u : Sentence)⟦substAtom u true⟧) = (⊤ ⋏ ∼∼⊤ : Sentence) := by
  simp [substAtom]

/-- Substituting `⊥` for `u` in `u ⋏ ∼∼u`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem substAtom_atomDouble_false (u : ℕ) :
    ((Formula.atom u ⋏ ∼∼Formula.atom u : Sentence)⟦substAtom u false⟧) = (⊥ ⋏ ∼∼⊥ : Sentence) := by
  simp [substAtom]

/-- The projected price of `u ⋏ ∼∼u` is the mixture of the base prices of `⊤ ⋏ ∼∼⊤` and
`⊥ ⋏ ∼∼⊥`.
Source: [[dose-response]] §6.1 Lemma A (the displayed `𝕡_n(φ)` at `φ := u ⋏ ∼∼u`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem project_atomDouble (P : History) (u : ℕ) (q : ℕ → ℚ) (n : ℕ) :
    project P u q n (Formula.atom u ⋏ ∼∼Formula.atom u) =
      (q n : ℝ) * P n (⊤ ⋏ ∼∼⊤) + (1 - (q n : ℝ)) * P n (⊥ ⋏ ∼∼⊥) := by
  rw [project_apply, substAtom_atomDouble_true, substAtom_atomDouble_false]

/-- `P_n(⊤ ⋏ ∼∼⊤) → 1` for any inductor over a satisfiable process (FAF's `lic_provind_true` at a
constant tautology).
Source: [[dose-response]] §6.1 Lemma A ("`𝕡̄_n(⊤) → 1` by Convergence and Limit Coherence")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem tendsto_price_topDouble (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n => P n (⊤ ⋏ ∼∼⊤)) atTop (𝓝 1) := by
  have h := lic_provind_true P DP (fun _ => (⊤ ⋏ ∼∼⊤ : Sentence)) (MachineSentenceCodes.const _)
    (fun _ v _ => by simp [PCWorld.holds_and, PCWorld.holds_neg, PCWorld.holds_top]) hworld
  exact tendsto_sub_nhds_zero_iff.mp h

/-- `P_n(⊥ ⋏ ∼∼⊥) → 0` (FAF's `lic_provind_false` at a constant contradiction).
Source: [[dose-response]] §6.1 Lemma A ("`𝕡̄_n(⊥) → 0`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem tendsto_price_botDouble (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) :
    Tendsto (fun n => P n (⊥ ⋏ ∼∼⊥)) atTop (𝓝 0) := by
  have h := lic_provind_false P DP (fun _ => (⊥ ⋏ ∼∼⊥ : Sentence)) (MachineSentenceCodes.const _)
    (fun _ v _ => by
      rw [PCWorld.holds_neg, PCWorld.holds_and]
      exact fun h => h.1) hworld
  simpa [AsympEq] using h

/-- **The projected market's expectation of `𝟙(u)` tends to `q_∞`**, from the base criterion
alone: the mesh identity, the projected price of `u ⋏ ∼∼u`, and the base limits on `⊤ ⋏ ∼∼⊤`,
`⊥ ⋏ ∼∼⊥`. The projection is *not* assumed to be an inductor.
Source: [[dose-response]] §6.1 Lemma A (marginal) and §6.3 T2(a) ("[LI 4.8.6] transfers the limit to `E_∞`"); anson-2-030
Kind: C
Fidelity: stronger: no criterion on the projection
Hyps: (a) none -/
theorem project_indicator_expect_tendsto (P : History) (DP : DeductiveProcess)
    [IsLogicalInductor P DP] (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (u : ℕ)
    (q : ℕ → ℚ) (N : ℕ) (hjump : ∀ n, N ≤ n → q n = q N) :
    Tendsto (fun n => (LUV.indicatorOf (Formula.atom u)).expect (project P u q) n) atTop
      (𝓝 (q N)) := by
  have hq : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 (q N)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [hjump n hn]
  have h1 := tendsto_price_topDouble P DP hworld
  have h0 := tendsto_price_botDouble P DP hworld
  have heq : (fun n => (LUV.indicatorOf (Formula.atom u)).expect (project P u q) n) =
      fun n => (q n : ℝ) * P n (⊤ ⋏ ∼∼⊤) + (1 - (q n : ℝ)) * P n (⊥ ⋏ ∼∼⊥) := by
    funext n
    rw [indicatorOf_expect_eq, project_atomDouble]
  rw [heq]
  have := (hq.mul h1).add (((tendsto_const_nhds (x := (1 : ℝ))).sub hq).mul h0)
  simpa using this

/-! ## The arm's market certificate (grade (a)) -/

/-- The arm is a `ComputableMarket` outright (`li-projection`'s
`computableMarket_project_ofMachineRatCodes` on the LIA's certificate) — the arm's exact rational
quote table exists without appeal to the OPEN rewriters.
Source: [[dose-response]] §6.1 Lemma A ("computability … immediate"); `li-projection` T1.3
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem arm_computableMarket {base : DeductiveProcess} {c : ℕ → Bool} {a : ℕ → ℚ}
    [hB : IsLogicalInductor (armBase base c a) (armProcess base c a)] {γ : ℚ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (N : ℕ) (hmem : ∀ n, 0 ≤ a n ∧ a n ≤ 1) :
    ComputableMarket (arm base γ N c a) :=
  computableMarket_project_ofMachineRatCodes _ _ _ hB.marketComputable
    (armWeight_machineRatCodes γ N c a) (fun n => by
      obtain ⟨h1, h2⟩ := armWeight_mem γ hγ0 N c a hmem n
      constructor <;> linarith)

/-! ## T2(a): dose-graded destinations -/

/-- The arm's price of `u` tends to its jump target (`li-projection`'s `project_atom_tendsto`).
Source: [[dose-response]] §6.1 Lemma A (marginal, limit form)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem arm_atom_tendsto {base : DeductiveProcess} {c : ℕ → Bool} {a : ℕ → ℚ}
    [IsLogicalInductor (armBase base c a) (armProcess base c a)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base c a).D n)) (γ : ℚ) (N : ℕ) :
    Tendsto (fun n => arm base γ N c a n protSentence) atTop (𝓝 (armWeight γ N c a N)) :=
  project_atom_tendsto (armBase base c a) (armProcess base c a) hworld protAtom
    (armWeight γ N c a) N (armWeight_jump γ N c a)

/-- The arm's expectation of `𝟙(u)` tends to its jump target, from the base criterion alone.
Source: [[dose-response]] §6.3 T2(a)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem arm_indicator_expect_tendsto {base : DeductiveProcess} {c : ℕ → Bool} {a : ℕ → ℚ}
    [IsLogicalInductor (armBase base c a) (armProcess base c a)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base c a).D n)) (γ : ℚ) (N : ℕ) :
    Tendsto (fun n => (LUV.indicatorOf protSentence).expect (arm base γ N c a) n) atTop
      (𝓝 (armWeight γ N c a N)) :=
  project_indicator_expect_tendsto (armBase base c a) (armProcess base c a) hworld protAtom
    (armWeight γ N c a) N (armWeight_jump γ N c a)

/-- **T2(a), dose-graded destinations (headline).** On a committed stream whose steered prefix is
`v` (`a_j = v` for `j < N`), the arm's limiting belief on the protected atom is
`½ + γ(v − ½)·p̂`, affine in the realized dose with slope the steering magnitude
(`limitingBelief_project_atom` and (∗)). Scope: one-way.
Source: [[dose-response]] §6.3 T2(a) ("`E^{(i)}_∞(u) = ½ + s p̂_i`"); anson-054
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem dose_graded_destination {base : DeductiveProcess} {c : ℕ → Bool} {a : ℕ → ℚ}
    [IsLogicalInductor (armBase base c a) (armProcess base c a)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base c a).D n))
    (γ : ℚ) {N : ℕ} (hN : 0 < N) {v : ℚ} (hv : ∀ j < N, a j = v) :
    limitingBelief (arm base γ N c a) protSentence =
      ((1 / 2 + γ * (v - 1 / 2) * realizedDose c N : ℚ) : ℝ) := by
  unfold arm
  rw [limitingBelief_project_atom (armBase base c a) (armProcess base c a) hworld protAtom
    (armWeight γ N c a) N (armWeight_jump γ N c a), armWeight_of_le γ N c a le_rfl,
    jump_target_eq γ hN (fun j hj _ => hv j hj)]

/-- **T2(a), expectation form (headline).** `𝔼^{(i)}_n(𝟙u) → ½ + γ(v − ½)·p̂_i`, derived — the
provenance upgrade of the zip's `cross_arm_audit_fires` hypothesis (anson-2-030); from the base
criterion alone (`project_indicator_expect_tendsto`). Scope: one-way.
Source: [[dose-response]] §6.3 T2(a) ("`𝕡^{(i)}_n(u) → ½ + s p̂_i` … [LI 4.8.6] transfers the limit to `E^{(i)}_∞`"); anson-2-030
Kind: C
Fidelity: exact (stronger provenance: no criterion on the arm itself)
Hyps: (a) none -/
theorem dose_graded_expect_tendsto {base : DeductiveProcess} {c : ℕ → Bool} {a : ℕ → ℚ}
    [IsLogicalInductor (armBase base c a) (armProcess base c a)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base c a).D n))
    (γ : ℚ) {N : ℕ} (hN : 0 < N) {v : ℚ} (hv : ∀ j < N, a j = v) :
    Tendsto (fun n => (LUV.indicatorOf protSentence).expect (arm base γ N c a) n) atTop
      (𝓝 ((1 / 2 + γ * (v - 1 / 2) * realizedDose c N : ℚ) : ℝ)) := by
  have h := arm_indicator_expect_tendsto hworld γ N
  rwa [armWeight_of_le γ N c a le_rfl, jump_target_eq γ hN (fun j hj _ => hv j hj)] at h

/-- **The mandate's route**: FAF's `lic_expectation_indicator` on the arm *as an inductor* gives
`𝔼^{arm}_n(𝟙u) ≈ₙ arm_n(u)`; with `arm_atom_tendsto` this is a second proof of the expectation
form. Rests on `li-projection` (A) through the instance; superseded for the record by
`dose_graded_expect_tendsto`, which needs no criterion on the arm.
Source: mandate T2(a) ("via FAF's `lic_expectation_indicator` … derived"); FAF `thm:ei`
Kind: C
Fidelity: exact
Hyps: (a) all; the instance rests on the OPEN rewriters -/
theorem arm_indicator_expect_asympEq_lic {base : DeductiveProcess} {γ : ℚ} {N : ℕ} {c : ℕ → Bool}
    {a : ℕ → ℚ} [IsLogicalInductor (arm base γ N c a) (armProcess base c a)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base c a).D n)) :
    (fun n => (LUV.indicatorOf protSentence).expect (arm base γ N c a) n) ≈ₙ
      (fun n => arm base γ N c a n protSentence) :=
  lic_expectation_indicator_unconditional (arm base γ N c a) (armProcess base c a)
    (fun _ => protSentence) (MachineSentenceCodes.const _) hworld

/-! ## T2(d): the audit fires -/

/-- Distinct realized doses and a nonzero slope give distinct destinations.
Source: [[dose-response]] §6.3 T2(a) ("these are pairwise distinct")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem destinations_ne {γ v : ℚ} (hs : γ * (v - 1 / 2) ≠ 0) {ci cj : ℕ → Bool} {N : ℕ}
    (hp : realizedDose ci N ≠ realizedDose cj N) :
    ((1 / 2 + γ * (v - 1 / 2) * realizedDose ci N : ℚ) : ℝ) ≠
      ((1 / 2 + γ * (v - 1 / 2) * realizedDose cj N : ℚ) : ℝ) := by
  intro h
  have h' : (1 / 2 + γ * (v - 1 / 2) * realizedDose ci N : ℚ) =
      1 / 2 + γ * (v - 1 / 2) * realizedDose cj N := by exact_mod_cast h
  exact hp (mul_left_cancel₀ hs (by linarith))

/-- **T2(d), the cross-arm audit fires (headline).** For two arms of the design on the committed
stream with steered prefix `v`, the uniform cross-arm audit on `u` tends to `s(p̂_i − p̂_j)`,
`s = γ(v − ½)`: (a)'s expectation form on each arm and `tendsto_cesaro`. Scope: one-way.
Source: [[dose-response]] §6.3 T2(d) ("`G^{ij}_N(u) → s(p̂_i − p̂_j)`"); anson-054; anson-2-030
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem cross_arm_audit_fires {base : DeductiveProcess} {ci cj : ℕ → Bool} {a : ℕ → ℚ}
    [IsLogicalInductor (armBase base ci a) (armProcess base ci a)]
    [IsLogicalInductor (armBase base cj a) (armProcess base cj a)]
    (hworldi : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base ci a).D n))
    (hworldj : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base cj a).D n))
    (γ : ℚ) {N : ℕ} (hN : 0 < N) {v : ℚ} (hv : ∀ j < N, a j = v) :
    Tendsto (crossArmAudit (arm base γ N ci a) (arm base γ N cj a) (LUV.indicatorOf protSentence))
      atTop (𝓝 ((γ * (v - 1 / 2) * (realizedDose ci N - realizedDose cj N) : ℚ) : ℝ)) := by
  have hi := dose_graded_expect_tendsto hworldi γ hN hv
  have hj := dose_graded_expect_tendsto hworldj γ hN hv
  have h := tendsto_cesaro (hi.sub hj)
  unfold crossArmAudit
  convert h using 2
  · rfl
  · push_cast; ring

/-- **T2(d), the negative form**: with `s ≠ 0` and `N`-separated coins (distinct realized doses —
a checkable property of the fixed `{0,1}` prefixes), the uniform audit does **not** pass:
detection is exact and permanent, from the crudest statistic.
Source: [[dose-response]] §6.3 T2(d) ("`≠ 0` for all `i < j`: detection is exact and permanent, from the uniform statistic alone")
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem cross_arm_audit_fires_ne {base : DeductiveProcess} {ci cj : ℕ → Bool} {a : ℕ → ℚ}
    [IsLogicalInductor (armBase base ci a) (armProcess base ci a)]
    [IsLogicalInductor (armBase base cj a) (armProcess base cj a)]
    (hworldi : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base ci a).D n))
    (hworldj : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base cj a).D n))
    {γ : ℚ} {N : ℕ} (hN : 0 < N) {v : ℚ} (hv : ∀ j < N, a j = v) (hs : γ * (v - 1 / 2) ≠ 0)
    (hp : realizedDose ci N ≠ realizedDose cj N) :
    ¬ Tendsto (crossArmAudit (arm base γ N ci a) (arm base γ N cj a) (LUV.indicatorOf protSentence))
      atTop (𝓝 0) := by
  intro h0
  have h := tendsto_nhds_unique (cross_arm_audit_fires hworldi hworldj γ hN hv) h0
  have h' : (γ * (v - 1 / 2) * (realizedDose ci N - realizedDose cj N) : ℚ) = 0 := by
    exact_mod_cast h
  rcases mul_eq_zero.mp h' with h1 | h1
  · exact hs h1
  · exact hp (sub_eq_zero.mp h1)

/-! ## T2(b-half): the advisor's quote converges to the production arm's destination -/

/-- The protected LUV family the mirror pair quotes: the constant family `𝟙(u)`.
Source: mandate D4 (`X n := LUV.indicatorOf (Formula.atom u)`)
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev protX : ℕ → LUV := fun _ => LUV.indicatorOf protSentence

/-- **T2(b-half) (headline).** For the production arm `arm base γ N c a` (with any market program
`M` for it — one exists at grade (a), `arm_computableMarket`), any inductor `A` over the mirror
ledger `ledgerProcess baseA (realizedExpectation M protX f) σ` (`A` reads the arm's realized day-`f n`
expectations of `𝟙u`; every stage satisfiable) has quote stream converging to the arm's
destination `½ + γ(v − ½)·p̂`. Scope: one-way (`A` reads a fixed `H`).
Source: [[dose-response]] §6.3 T2(b) ("The quote stream converges pointwise: `a_n(u) → ½ + s p̂_1`"); anson-054; `def-tracking-pin` T3
Kind: C
Fidelity: exact (the note's "[LI 4.8.10] in both directions" is `pinning_tendsto`)
Hyps: (a) none -/
theorem production_quote_tendsto {base : DeductiveProcess} {c : ℕ → Bool} {a : ℕ → ℚ}
    [IsLogicalInductor (armBase base c a) (armProcess base c a)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base c a).D n))
    (γ : ℚ) {N : ℕ} (hN : 0 < N) {v : ℚ} (hv : ∀ j < N, a j = v)
    (M : MarketComputation (arm base γ N c a)) (f : DeferralFunction) (baseA : DeductiveProcess)
    (σ : ℕ → PublicationSchedule) (A : History)
    [IsLogicalInductor A (ledgerProcess baseA (realizedExpectation M protX f) σ)]
    (hworldA : ∀ n, ∃ w : PCWorld,
      w.ConsistentWith ((ledgerProcess baseA (realizedExpectation M protX f) σ).D n)) :
    Tendsto (quoteStreamR A) atTop
      (𝓝 ((1 / 2 + γ * (v - 1 / 2) * realizedDose c N : ℚ) : ℝ)) :=
  mirror_quote_tendsto M protX f baseA σ A hworldA
    ((dose_graded_expect_tendsto hworld γ hN hv).comp f.tendsto_atTop)

/-- **T2(c), the surviving neighbour at the mirror process**: the steered advisor over the
production arm's mirror ledger is a logical inductor exactly (`prescribe_finiteSupport`); with
`li-quote-lane`'s `mirrorPair_inductor`, FAF's LIA over that ledger is one such `A`.
Source: [[dose-response]] §6.3 T2(c) ("the steered `A_v` is an honest inductor among honest inductors")
Kind: C
Fidelity: variant (finite-support prescription; see `Advisor.lean`)
Hyps: (a) none -/
theorem steeredAdvisor_mirror_inductor {base : DeductiveProcess} {c : ℕ → Bool} {a : ℕ → ℚ}
    {γ : ℚ} {N : ℕ} (M : MarketComputation (arm base γ N c a)) (f : DeferralFunction)
    (baseA : DeductiveProcess) (σ : ℕ → PublicationSchedule) (A : History)
    [IsLogicalInductor A (ledgerProcess baseA (realizedExpectation M protX f) σ)] (v : ℚ)
    (N' : ℕ) :
    IsLogicalInductor (steeredAdvisor A v N')
      (ledgerProcess baseA (realizedExpectation M protX f) σ) :=
  steeredAdvisor_isLogicalInductor A _ v N'

/-! ## Cor T2.1: memory asymmetry -/

/-- A within-arm residual against a stream converging to the arm's own destination vanishes.
Source: [[dose-response]] §6.3 T2(b) ("the `n ≥ N*` residuals tend to `0`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem withinArmResidual_tendsto_zero {H A : History} {X : LUV} {L : ℝ}
    (hH : Tendsto (fun n => X.expect H n) atTop (𝓝 L)) (hA : Tendsto (quoteStreamR A) atTop (𝓝 L))
    (f : DeferralFunction) :
    Tendsto (withinArmResidual H X f.f (quoteStreamR A)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => X.expect H (f.f n)) atTop (𝓝 L) := hH.comp f.tendsto_atTop
  have h2 := h1.sub hA
  rw [sub_self] at h2
  exact h2

/-- **Cor T2.1, memory asymmetry (headline).** In the steered system every within-arm
calibration residual of the production arm vanishes over *every* battery — trajectory audits are
memoryless — while the cross-arm audit converges to the constant `s(p̂_i − p̂_j)` (T2(d)):
destination audits have memory. Scope: one-way.
Source: [[dose-response]] §6.3 Cor T2.1 ("Finite-time influence, permanent effect, transient trace"); anson-054
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem memory_asymmetry {base : DeductiveProcess} {c : ℕ → Bool} {a : ℕ → ℚ}
    [IsLogicalInductor (armBase base c a) (armProcess base c a)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base c a).D n))
    (γ : ℚ) {N : ℕ} (hN : 0 < N) {v : ℚ} (hv : ∀ j < N, a j = v)
    (M : MarketComputation (arm base γ N c a)) (f : DeferralFunction) (baseA : DeductiveProcess)
    (σ : ℕ → PublicationSchedule) (A : History)
    [IsLogicalInductor A (ledgerProcess baseA (realizedExpectation M protX f) σ)]
    (hworldA : ∀ n, ∃ w : PCWorld,
      w.ConsistentWith ((ledgerProcess baseA (realizedExpectation M protX f) σ).D n)) :
    ∀ w, IsBattery w →
      Tendsto (weightedAverage w
        (withinArmResidual (arm base γ N c a) (LUV.indicatorOf protSentence) f.f (quoteStreamR A)))
        atTop (𝓝 0) := by
  intro w hw
  exact weightedAverage_tendsto_zero hw.1 hw.2
    (withinArmResidual_tendsto_zero (dose_graded_expect_tendsto hworld γ hN hv)
      (production_quote_tendsto hworld γ hN hv M f baseA σ A hworldA) f)

/-! ## D4 meets T2, one-way: arms built on a steered advisor's quote stream -/

/-- The quote stream of a steered advisor (any inductor `A₀` over any process, patched at a target
`v` that is mesh-exact on every steering day) has the steered prefix `v` — the hypothesis every T2
row takes.
Source: mandate D4/T2 (the committed stream "produced by `Advisor.lean`'s `steeredAdvisor`"); adversarial audit r1 N4
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem quoteStream_steeredAdvisor_prefix {A₀ : History} {v : ℚ} {N : ℕ}
    (MS : MarketComputation (steeredAdvisor A₀ v N))
    (hmesh : ∀ n < N, ∃ k ≤ n + 1, v = (k : ℚ) / ((n : ℚ) + 1)) :
    ∀ j < N, quoteStream MS j = v := fun j hj => by
  obtain ⟨k, hk, hv⟩ := hmesh j hj
  exact quoteStream_steeredAdvisor_exact MS hj hk hv

/-- **The arm built on a steered advisor's stream has an inductor base** (the instance hypothesis
of the two rows below, discharged): for a computable `base` and coin, FAF's LIA over the
exposure ledger of the stream `quoteStream MS` is a logical inductor, because that stream is
computable (`quoteStream_computable`) — `armBase_isLogicalInductor` at it.
Source: mandate D4/T2; adversarial audit r2 N2
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem steered_armBase_isLogicalInductor {base : DeductiveProcess}
    (hbase : ComputableDeductiveProcess base) {c : ℕ → Bool} (hc : Computable c) {A₀ : History}
    {v : ℚ} {N : ℕ} (MS : MarketComputation (steeredAdvisor A₀ v N)) :
    IsLogicalInductor (armBase base c (quoteStream MS)) (armProcess base c (quoteStream MS)) :=
  armBase_isLogicalInductor hbase hc (quoteStream_computable MS)

/-- **T2(a) on a steered advisor's stream (one-way).** Arms built on the quote stream of a steered
advisor `A₀` (an inductor patched at a mesh-exact target `v` on days `< N`; `A₀` does not read the
arms) have the dose-graded destinations `½ + γ(v − ½)·p̂`: D4 and T2 composed without the OPEN
closure. The stream is `quoteStream MS`, exact rationals through `A₀`'s market program. The
instance hypothesis is discharged for computable `base` and `c` by
`steered_armBase_isLogicalInductor` (adversarial audit r2 N2).
Source: [[dose-response]] §6.3 T2(a) with the stream of §6.2's `A_v`; adversarial audit r1 N4
Kind: C
Fidelity: exact (one-way: the advisor is any inductor, not one reading these arms)
Hyps: (a) none -/
theorem dose_graded_destination_steered {base : DeductiveProcess} {c : ℕ → Bool} {A₀ : History}
    {v : ℚ} {N : ℕ} (MS : MarketComputation (steeredAdvisor A₀ v N))
    [IsLogicalInductor (armBase base c (quoteStream MS)) (armProcess base c (quoteStream MS))]
    (hworld : ∀ n, ∃ w : PCWorld, w.ConsistentWith ((armProcess base c (quoteStream MS)).D n))
    (γ : ℚ) (hN : 0 < N) (hmesh : ∀ n < N, ∃ k ≤ n + 1, v = (k : ℚ) / ((n : ℚ) + 1)) :
    limitingBelief (arm base γ N c (quoteStream MS)) protSentence =
      ((1 / 2 + γ * (v - 1 / 2) * realizedDose c N : ℚ) : ℝ) :=
  dose_graded_destination hworld γ hN (quoteStream_steeredAdvisor_prefix MS hmesh)

/-- **T2(d) on a steered advisor's stream (one-way)**: the uniform cross-arm audit of two arms
built on the steered advisor's quote stream tends to `s(p̂_i − p̂_j)`. The instance hypotheses are
discharged for computable `base`, `ci`, `cj` by `steered_armBase_isLogicalInductor`.
Source: [[dose-response]] §6.3 T2(d) with the stream of §6.2's `A_v`; adversarial audit r1 N4
Kind: C
Fidelity: exact (one-way)
Hyps: (a) none -/
theorem cross_arm_audit_fires_steered {base : DeductiveProcess} {ci cj : ℕ → Bool}
    {A₀ : History} {v : ℚ} {N : ℕ} (MS : MarketComputation (steeredAdvisor A₀ v N))
    [IsLogicalInductor (armBase base ci (quoteStream MS)) (armProcess base ci (quoteStream MS))]
    [IsLogicalInductor (armBase base cj (quoteStream MS)) (armProcess base cj (quoteStream MS))]
    (hworldi : ∀ n, ∃ w : PCWorld, w.ConsistentWith ((armProcess base ci (quoteStream MS)).D n))
    (hworldj : ∀ n, ∃ w : PCWorld, w.ConsistentWith ((armProcess base cj (quoteStream MS)).D n))
    (γ : ℚ) (hN : 0 < N) (hmesh : ∀ n < N, ∃ k ≤ n + 1, v = (k : ℚ) / ((n : ℚ) + 1)) :
    Tendsto (crossArmAudit (arm base γ N ci (quoteStream MS)) (arm base γ N cj (quoteStream MS))
      (LUV.indicatorOf protSentence))
      atTop (𝓝 ((γ * (v - 1 / 2) * (realizedDose ci N - realizedDose cj N) : ℚ) : ℝ)) :=
  cross_arm_audit_fires hworldi hworldj γ hN (quoteStream_steeredAdvisor_prefix MS hmesh)

end Cleanroom.Deference.DefDoseResponse
