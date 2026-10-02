import Cleanroom.Fa.FaForcingTrader.A.Analysis
import Cleanroom.Fa.FaForcingTrader.A.NonDerivability
import Cleanroom.Fa.FaForcingTrader.A.Gating

/-!
# `fa-forcing-trader` · Analysis: the real-sequence results of record (T8, T9, T10, T12 (b)/(c))

Main module of the reconciled package. All of it is angle A's (angle B attempted none of T8–T10,
T12). The load-bearing T10 is restated in the package namespace and proved `:= A.…`; the
witnesses of T8 and T9 and the two gating lemmas are re-exported under the package namespace
(`export`), their statements being over real sequences where the namespace carries no content.

* **T10** — `tendsto_zero_of_summable_on_windowDisjoint` (⟹, the greedy schedule);
  `not_summable_on_windowDisjoint_of_tendsto_zero` (the mandate's ⇐ **refuted**, findings F-A3);
  `ChasingSchedule` (the e.c.-level gap of record, (A4)); `v3Theorem1_tendsto_zero_of_chasing`
  and `v3Corollary2_of_chasing` (the FAF corollaries under chasing, two-way, partial).
* **T9** — `signed_average_not_absolute` (i); `approximant_mismatch_not_small` (ii, new: the
  (R2) approximant cannot replace (L) on a sparse schedule, findings F-A4).
* **T8** — `averaged_not_perDay` (Prop 7.1), `scheduled_averaged_not_perDay` (vq-wiki-2-011),
  `two_limit_points_permanent_violation` (Prop 5.4), `one_big_lie`.
* **T12 (b), (c)** — `not_inductor_of_gated_bias`, `bounded_gate_mass_not_divergent`.

(Angle A's declarations are referenced fully qualified, `_root_.Cleanroom.Fa.FaForcingTrader.A.…`,
wherever a theorem binds a market named `A`: the variable would otherwise shadow the namespace.)
-/
namespace Cleanroom.Fa.FaForcingTrader

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Filter Topology

export A (ChasingSchedule tendsto_zero_of_chasing altSign harmonicGate sqrtMismatch
  signed_average_not_absolute approximant_mismatch_not_small averaged_not_perDay
  scheduled_averaged_not_perDay two_limit_points_permanent_violation one_big_lie schedH
  not_inductor_of_gated_bias bounded_gate_mass_not_divergent)

/-- **T10 (⟹, of record). Finite on every window-disjoint schedule forces `w_n → 0`** (real
sequences, any lookahead `f` with `f n > n`): if `w_n ≥ θ` infinitely often, the greedy schedule
— the first such day, then the first such day beyond the previous window — is strictly
increasing, window-disjoint, and carries weight `≥ θ` at every step, so it is not summable.
Angle A's theorem, restated.
Source: root-fa-2-003 (ii) (the greedy lemma); [[fa-positive-results-corrected-v3]] §4
Kind: P
Fidelity: exact (this direction; the converse is refuted below)
Hyps: (a) none -/
theorem tendsto_zero_of_summable_on_windowDisjoint {f : ℕ → ℕ} (hf : ∀ n, n < f n) {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n)
    (h : ∀ d : ℕ → ℕ, StrictMono d → (∀ k, f (d k) < d (k + 1)) → Summable (fun k => w (d k))) :
    Tendsto w atTop (𝓝 0) :=
  A.tendsto_zero_of_summable_on_windowDisjoint hf hw0 h

/-- **T10 (⇐, refuted, of record).** A `[0,1]` weight tending to `0` that is **not** summable on a
window-disjoint schedule: `w_n = 1/(n+1)`, `d_k = 2k` (gaps `2`, window-disjoint for the successor
lookahead), `∑_k 1/(2k+1) = ∞`. The mandate's T10 and root-fa-2-003 (ii) state an equivalence;
only ⟹ holds (findings F-A3). Angle A's theorem, restated. Scope: this is the refutation for the
**successor** lookahead (the mandate's "any `f` with `f n > n`" form); root-fa-2-003 (ii)'s own
class `d_{k+1} ≥ 2^{d_k}` is refuted by `tower_converse_fails` below, and the package's strict
window shape for the lookahead `2^n` by `tower_converse_fails_strict` (repair round 2).
Source: root-fa-2-003 (ii) (refuted in the ⇐ direction: here for `f = succ`, below for the inventory's `2^n` class); mandate T10
Kind: N+
Fidelity: n/a (refutation of the stated converse)
Hyps: n/a -/
theorem not_summable_on_windowDisjoint_of_tendsto_zero :
    ∃ w : ℕ → ℝ, (∀ n, w n ∈ Set.Icc (0 : ℝ) 1) ∧ Tendsto w atTop (𝓝 0) ∧
      ∃ d : ℕ → ℕ, StrictMono d ∧ (∀ k, d k + 1 < d (k + 1)) ∧ ¬ Summable (fun k => w (d k)) :=
  A.not_summable_on_windowDisjoint_of_tendsto_zero

/-- **T10, the FAF corollary (of record).** If v3 Theorem 1's joint legibility holds on every
window-disjoint `DeferralFunction` schedule and the violation days can be chased
(`ChasingSchedule`), then the schedule-free violation weight `Ind_δ(a_n > t) · Ind_δ(h_n < t − ε)`
tends to `0`. The chasing hypothesis is exactly the (c) `fa-adaptive-joint` must discharge ((A4));
without it, T3 over all `DeferralFunction` schedules says nothing about `w_n → 0`
(lean-deference-2-010). Angle A's theorem, restated.
Scope: two-way (partial: over the OPEN pair, and under chasing). e.d. family.
Source: root-fa-005 (the box, recovered only under (A4)); root-fa-2-003 (ii); lean-deference-2-010; mandate T10
Kind: C
Fidelity: variant: conditional on `ChasingSchedule` (the e.c.-level gap named, not closed)
Hyps: (c) `pkg.reflected`; (c) `hjointAll` (joint legibility on every schedule); (c) `hch` (chasing, (A4)). -/
theorem v3Theorem1_tendsto_zero_of_chasing {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ) (hε : 0 < ε)
    (hjointAll : ∀ d : DeferralFunction, WindowDisjoint f d →
      LegibleOn A (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ) ∧
        LegibleOn H (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ))
    (hch : ChasingSchedule f (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ)) :
    Tendsto (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ) atTop (𝓝 0) :=
  _root_.Cleanroom.Fa.FaForcingTrader.A.v3Theorem1_tendsto_zero_of_chasing
    pkg hcode hworldA hworldH hval t ε hδ hε hjointAll hch

/-- **v3's Corollary 2 under chasing (of record)**: with joint legibility on every schedule and
chasing for every rational parameter triple, `H`'s credence dominates `A`'s quote
(`Dominates`: `∀ c > 0, ∀ᶠ n, a_n − c < h_n`). Angle A's theorem, restated.
Scope: two-way (partial: over the OPEN pair, and under chasing).
Source: [[fa-positive-results-corrected-v3]] §5 Corollary 2; root-fa-005; li-asymp-calc `tendsto_viol_iff_dominates`
Kind: C
Fidelity: variant: conditional on `ChasingSchedule` for every `(t, ε, δ)`
Hyps: (c) `pkg.reflected`; (c) `hjointAll`; (c) `hch`. -/
theorem v3Corollary2_of_chasing {H A : History} {DPA DPH : DeductiveProcess}
    [IsLogicalInductor A DPA] [IsLogicalInductor H DPH] {f : DeferralFunction} {X Y : ℕ → LUV}
    (pkg : CrossQuotePackage H DPA f X Y) (hcode : LUV.MachineThresholdCodeSeq X)
    (hworldA : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPA.D n))
    (hworldH : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DPH.D n))
    (hval : ∀ n (v : PCWorld), v.ConsistentWithTheory DPH → ∃ x : ℝ, v.ValuesAt (X n) x)
    (hjointAll : ∀ (t ε δ : ℚ) (d : DeferralFunction), WindowDisjoint f d →
      LegibleOn A (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ) ∧
        LegibleOn H (violW d (quoteSeq Y A) (fun n => (X n).expect H n) t ε δ))
    (hch : ∀ t ε δ : ℚ, 0 < ε → 0 < δ →
      ChasingSchedule f (viol (fun n => (X n).expect H n) (quoteSeq Y A) t ε δ)) :
    Dominates (fun n => (X n).expect H n) (quoteSeq Y A) :=
  _root_.Cleanroom.Fa.FaForcingTrader.A.v3Corollary2_of_chasing
    pkg hcode hworldA hworldH hval hjointAll hch


/-! ## T10 ⇐, refuted for the inventory's own class (repair round 1, audit r1 fidelity N2)

`not_summable_on_windowDisjoint_of_tendsto_zero` refutes the converse for the successor
lookahead (gaps `2`), the mandate's generalization; root-fa-2-003 (ii)'s own class is
`d (k+1) ≥ 2^{d k}` (lookahead `2^n`), which findings F-A3 refuted only in prose (`1/log* n`).
The refutation below is for that class, without `log*`: weight `1/(k+1)` on the `k`-th day of
the tower `1, 2, 4, 16, 65536, …` and `0` elsewhere. (The fidelity auditor's probe
`audit-r1-probes/TowerConverse.lean`, adopted.) The tower here is a plain `ℕ → ℕ`; the
`DeferralFunction` `towerSchedule` with a built decider (T2 stretch) remains unbuilt. -/

/-- The tower schedule as a plain sequence: `d 0 = 1`, `d (k+1) = 2^{d k}`.
Source: root-fa-2-003 (ii) (the class `d_{k+1} ≥ 2^{d_k}`); audit r1 fidelity N2
Kind: D
Fidelity: exact (the inventory's class, at its boundary)
Hyps: n/a -/
def towerSeq : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 ^ towerSeq k

/-- `towerSeq k < towerSeq (k+1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem towerSeq_lt_succ (k : ℕ) : towerSeq k < towerSeq (k + 1) := by
  show towerSeq k < 2 ^ towerSeq k
  exact Nat.lt_two_pow_self

/-- The tower is strictly increasing.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem towerSeq_strictMono : StrictMono towerSeq := strictMono_nat_of_lt_succ towerSeq_lt_succ

/-- The tower is in root-fa-2-003 (ii)'s class: `2^{d k} ≤ d (k+1)` (with equality).
Source: root-fa-2-003 (ii)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem towerSeq_window (k : ℕ) : 2 ^ towerSeq k ≤ towerSeq (k + 1) := le_rfl

open Classical in
/-- Weight `1/(k+1)` on `towerSeq k`, `0` off the tower.
Source: audit r1 fidelity N2
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def towerWeight (n : ℕ) : ℝ :=
  if h : ∃ k, towerSeq k = n then 1 / ((Nat.find h : ℝ) + 1) else 0

/-- `towerWeight (towerSeq k) = 1/(k+1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem towerWeight_apply (k : ℕ) : towerWeight (towerSeq k) = 1 / ((k : ℝ) + 1) := by
  have h : ∃ j, towerSeq j = towerSeq k := ⟨k, rfl⟩
  rw [towerWeight, dif_pos h]
  have hk : Nat.find h = k := towerSeq_strictMono.injective (Nat.find_spec h)
  rw [hk]

/-- `0 ≤ towerWeight n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem towerWeight_nonneg (n : ℕ) : 0 ≤ towerWeight n := by
  unfold towerWeight
  split_ifs <;> positivity

/-- `towerWeight n ≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem towerWeight_le_one (n : ℕ) : towerWeight n ≤ 1 := by
  unfold towerWeight
  split_ifs with h
  · rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg (Nat.find h) : (0 : ℝ) ≤ Nat.find h)]
  · norm_num

/-- Beyond `towerSeq K` every weight is at most `1/(K+1)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem towerWeight_le (n K : ℕ) (hn : towerSeq K ≤ n) : towerWeight n ≤ 1 / ((K : ℝ) + 1) := by
  unfold towerWeight
  split_ifs with h
  · have hspec := Nat.find_spec h
    have hk : K ≤ Nat.find h := by
      by_contra hlt
      have hlt' : Nat.find h < K := not_le.1 hlt
      have := towerSeq_strictMono hlt'
      omega
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hk)
  · positivity

/-- `towerWeight → 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem towerWeight_tendsto_zero : Tendsto towerWeight atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop (towerSeq K)] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (towerWeight_nonneg n)]
  exact lt_of_le_of_lt (towerWeight_le n K hn) hK

/-- The tower weight is not summable along the tower (`∑_k 1/(k+1) = ∞`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem not_summable_towerWeight_on_towerSeq : ¬ Summable (fun k => towerWeight (towerSeq k)) := by
  intro hs
  have h1 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1)) := hs.congr (fun k => towerWeight_apply k)
  have h2 : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) :=
    h1.congr (fun k => by push_cast; rfl)
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 h2)

/-- **T10 ⇐, refuted for root-fa-2-003 (ii)'s own class (of record).** A `[0,1]` weight tending
to `0` whose sum along a schedule with `2^{d k} ≤ d (k+1)` diverges: the harmonic weight on the
tower. Together with `not_summable_on_windowDisjoint_of_tendsto_zero` (the successor case) this
puts findings F-A3 in Lean for both the mandate's and the inventory's class.
Source: root-fa-2-003 (ii) (refuted in the ⇐ direction, for its own class); audit r1 fidelity N2
Kind: N+
Fidelity: n/a (refutation of the stated converse)
Hyps: n/a -/
theorem tower_converse_fails :
    ∃ w : ℕ → ℝ, (∀ n, w n ∈ Set.Icc (0 : ℝ) 1) ∧ Tendsto w atTop (𝓝 0) ∧
      ∃ d : ℕ → ℕ, StrictMono d ∧ (∀ k, 2 ^ d k ≤ d (k + 1)) ∧ ¬ Summable (fun k => w (d k)) :=
  ⟨towerWeight, fun n => ⟨towerWeight_nonneg n, towerWeight_le_one n⟩, towerWeight_tendsto_zero,
    towerSeq, towerSeq_strictMono, towerSeq_window, not_summable_towerWeight_on_towerSeq⟩


/-! ## T10 ⇐, refuted for the strict `2^n`-window class (repair round 2, audit r2 adversarial N4)

`tower_converse_fails` sits at the boundary `d (k+1) = 2^{d k}` of root-fa-2-003 (ii)'s class,
which the package's own `WindowDisjoint` (strict: `f (d k) < d (k+1)`) excludes. The converse
fails for the strict class too — the package's window shape with the lookahead `2^n`, as a
real-sequence schedule: shift the tower by one, `d 0 = 1`, `d (k+1) = 2^{d k} + 1`, harmonic
weight on its image. (The adversarial auditor's probe `audit-r2-probes/TowerStrict.lean`,
adopted.) Same proof as the boundary case. -/

/-- The strict tower: `d 0 = 1`, `d (k+1) = 2^{d k} + 1`.
Source: audit r2 adversarial N4; root-fa-2-003 (ii) (its class, strictly)
Kind: D
Fidelity: exact (the package's strict window shape for the lookahead `2^n`)
Hyps: n/a -/
def towerSeqStrict : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 ^ towerSeqStrict k + 1

/-- `towerSeqStrict k < towerSeqStrict (k+1)`.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem towerSeqStrict_lt_succ (k : ℕ) : towerSeqStrict k < towerSeqStrict (k + 1) := by
  show towerSeqStrict k < 2 ^ towerSeqStrict k + 1
  have := Nat.lt_two_pow_self (n := towerSeqStrict k)
  omega

/-- The strict tower is strictly increasing.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem towerSeqStrict_strictMono : StrictMono towerSeqStrict :=
  strictMono_nat_of_lt_succ towerSeqStrict_lt_succ

/-- The strict tower is window-disjoint for the lookahead `2^n`, strictly: `2^{d k} < d (k+1)`.
Source: audit r2 adversarial N4
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem towerSeqStrict_window (k : ℕ) : 2 ^ towerSeqStrict k < towerSeqStrict (k + 1) :=
  Nat.lt_succ_self _

open Classical in
/-- Weight `1/(k+1)` on `towerSeqStrict k`, `0` off the strict tower.
Source: audit r2 adversarial N4
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def towerWeightStrict (n : ℕ) : ℝ :=
  if h : ∃ k, towerSeqStrict k = n then 1 / ((Nat.find h : ℝ) + 1) else 0

/-- `towerWeightStrict (towerSeqStrict k) = 1/(k+1)`.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem towerWeightStrict_apply (k : ℕ) : towerWeightStrict (towerSeqStrict k) = 1 / ((k : ℝ) + 1) := by
  have h : ∃ j, towerSeqStrict j = towerSeqStrict k := ⟨k, rfl⟩
  rw [towerWeightStrict, dif_pos h]
  have hk : Nat.find h = k := towerSeqStrict_strictMono.injective (Nat.find_spec h)
  rw [hk]

/-- `0 ≤ towerWeightStrict n`.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem towerWeightStrict_nonneg (n : ℕ) : 0 ≤ towerWeightStrict n := by
  unfold towerWeightStrict
  split_ifs <;> positivity

/-- `towerWeightStrict n ≤ 1`.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem towerWeightStrict_le_one (n : ℕ) : towerWeightStrict n ≤ 1 := by
  unfold towerWeightStrict
  split_ifs with h
  · rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg (Nat.find h) : (0 : ℝ) ≤ Nat.find h)]
  · norm_num

/-- Beyond `towerSeqStrict K` every weight is at most `1/(K+1)`.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem towerWeightStrict_le (n K : ℕ) (hn : towerSeqStrict K ≤ n) :
    towerWeightStrict n ≤ 1 / ((K : ℝ) + 1) := by
  unfold towerWeightStrict
  split_ifs with h
  · have hspec := Nat.find_spec h
    have hk : K ≤ Nat.find h := by
      by_contra hlt
      have hlt' : Nat.find h < K := not_le.1 hlt
      have := towerSeqStrict_strictMono hlt'
      omega
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.succ_le_succ hk)
  · positivity

/-- `towerWeightStrict → 0`.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem towerWeightStrict_tendsto_zero : Tendsto towerWeightStrict atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop (towerSeqStrict K)] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (towerWeightStrict_nonneg n)]
  exact lt_of_le_of_lt (towerWeightStrict_le n K hn) hK

/-- The strict tower weight is not summable along the strict tower (`∑_k 1/(k+1) = ∞`).
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem not_summable_towerWeightStrict_on_towerSeqStrict :
    ¬ Summable (fun k => towerWeightStrict (towerSeqStrict k)) := by
  intro hs
  have h1 : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1)) :=
    hs.congr (fun k => towerWeightStrict_apply k)
  have h2 : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) :=
    h1.congr (fun k => by push_cast; rfl)
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).1 h2)

/-- **T10 ⇐, refuted for the strict `2^n`-window class** — the package's `WindowDisjoint` shape
(`f (d k) < d (k+1)`) with the lookahead `2^n`, as a real-sequence schedule: a `[0,1]` weight
tending to `0` whose sum along a schedule with `2^{d k} < d (k+1)` diverges. With
`tower_converse_fails` (the inventory's `≥` class, at its boundary) and
`not_summable_on_windowDisjoint_of_tendsto_zero` (the successor lookahead), the converse of T10
fails for every class the sources or the package name.
Source: audit r2 adversarial N4 (probe `TowerStrict.lean`, adopted); root-fa-2-003 (ii)
Kind: N+
Fidelity: n/a (refutation of the stated converse, strict class)
Hyps: n/a -/
theorem tower_converse_fails_strict :
    ∃ w : ℕ → ℝ, (∀ n, w n ∈ Set.Icc (0 : ℝ) 1) ∧ Tendsto w atTop (𝓝 0) ∧
      ∃ d : ℕ → ℕ, StrictMono d ∧ (∀ k, 2 ^ d k < d (k + 1)) ∧ ¬ Summable (fun k => w (d k)) :=
  ⟨towerWeightStrict, fun n => ⟨towerWeightStrict_nonneg n, towerWeightStrict_le_one n⟩,
    towerWeightStrict_tendsto_zero, towerSeqStrict, towerSeqStrict_strictMono,
    towerSeqStrict_window, not_summable_towerWeightStrict_on_towerSeqStrict⟩

/-! ## The note's finite-mass remark (repair round 2, audit r2 adversarial N2)

[[theorem-ss-streamlined]] §0 adds to Theorem SS: "If `∑_i w_i < ∞`, then `w_i → 0` along the
schedule and every displayed per-day quantity vanishes there, so the unnormalized forms hold with
an additive constant." Every grade of T6/T7 in `TheoremSS` is stated for the divergent-mass case
(`hdiv`); the finite-mass half is this real-sequence pair: a summable weight tends to `0`
(Mathlib), and the unnormalized bias `∑_{i≤n} w_i (a_i − h_i)` of two sequences within `1` of
each other is bounded by `∑ w` on every day — the "additive constant". -/

/-- A summable weight tends to `0` (along the whole sequence, hence along every schedule).
Source: [[theorem-ss-streamlined]] §0 (the finite-mass remark); Mathlib `Summable.tendsto_atTop_zero`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem tendsto_zero_of_summable_weight {w : ℕ → ℝ} (hs : Summable w) :
    Tendsto w atTop (𝓝 0) :=
  hs.tendsto_atTop_zero

/-- **The unnormalized bias is bounded under finite mass**: if `0 ≤ w`, `∑ w < ∞` and
`|a_i − h_i| ≤ 1` on every day (true of `[0,1]`-valued quotes and credences), then
`|∑_{i≤n} w_i (a_i − h_i)| ≤ ∑_i w_i` for every `n` — the note's "the unnormalized forms hold
with an additive constant".
Source: [[theorem-ss-streamlined]] §0 (the finite-mass remark); audit r2 adversarial N2
Kind: L
Fidelity: exact (the remark's content, over real sequences)
Hyps: (a) none -/
theorem unnormBias_bounded_of_summable {w a h : ℕ → ℝ} (hw : ∀ i, 0 ≤ w i) (hs : Summable w)
    (hab : ∀ i, |a i - h i| ≤ 1) (n : ℕ) :
    |prefixSum (fun i => w i * (a i - h i)) n| ≤ ∑' i, w i := by
  unfold prefixSum
  calc |∑ i ∈ Finset.range (n + 1), w i * (a i - h i)|
      ≤ ∑ i ∈ Finset.range (n + 1), |w i * (a i - h i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), w i := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [abs_mul, abs_of_nonneg (hw i)]
        calc w i * |a i - h i| ≤ w i * 1 := mul_le_mul_of_nonneg_left (hab i) (hw i)
          _ = w i := mul_one _
    _ ≤ ∑' i, w i := Summable.sum_le_tsum _ (fun i _ => hw i) hs

end Cleanroom.Fa.FaForcingTrader
