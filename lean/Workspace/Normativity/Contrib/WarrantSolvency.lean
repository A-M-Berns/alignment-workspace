/-
# Solvency as soundness: the schema instantiation of the liability identity, and the conflict audit

Round `projects/normativity/rounds/2026-11-07-score-side-binding/`.

**§1, the instantiation.**  `DecisionComponent.liability_identity` and
`bounded_iff_not_outperformed` are stated over two bare real sequences: an enforcer holding
prices to one source and settling against another owes the source's realized shortfall, bounded
exactly when the source is not systematically outperformed.  A **warrant schema with
timely-settling instances** (`Schema`) — one strength, and per instance whether it is
undefeated and the settled truth of its consequent — instantiates both with the source the
strength and the alternative the settled consequent: the enforcer's cumulative liability is
bounded below by `−B` iff `c · U_n − T_n ≤ B` at every `n`, where `U_n` counts the undefeated
instances and `T_n` the true consequents among them (`bounded_iff_frequency`).  The step from
`WarrantForce`'s calibrated trader to a unit position per instance is the hypothesis
`UnitPosition`, named and not derived.  This is a renaming of the deference result, not new
mathematics; the report says so.  Two witnesses inhabit the two sides
(`Witness.always_true_bounded`, `Witness.always_false_unbounded`).

**§2, the conflict audit.**  In the generality of `NormativeInductorComposition.FarkasCert`:
at every price vector some row with positive multiplier is violated
(`exists_violated_suspect`); hence if every weighted row holds at a point no valid certificate
exists (`no_conflict_of_sound`), against a bundle a violated suspect is a *bundle* row at any
cube point (`suspect_in_bundle`, also on a `NormState`), and when all suspects but one hold the
remaining one is violated (`unique_suspect`).  Read at the true posterior: sound rows cannot
conflict, so a valid conflict certificate proves a mis-admission among the rows it weights.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Deference.Contrib.DecisionComponent
import Workspace.Normativity.Contrib.WarrantInductor

namespace Workspace.Normativity.Contrib.WarrantSolvency

open Finset
open Workspace.Deference.Contrib.DecisionComponent (liability liability_identity
  bounded_iff_not_outperformed systematic_outperformance_unbounded)
open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.WarrantInductor

/-! ## 1. Solvency as soundness -/

/-- **A warrant schema with timely-settling instances** (provisional name): one strength `c`,
and per instance `t` whether the instance is undefeated at its date and the settled truth of
its consequent.  Timeliness is the shape of the data — the consequent of instance `t` is a
settled value by the date the cumulative account is read, so the settled payout is a function
of `t` alone. -/
structure Schema where
  c : ℚ
  undefeated : ℕ → Bool
  consequent : ℕ → Bool

namespace Schema

variable (S : Schema)

/-- The price the enforcer holds instance `t` to: the strength on an undefeated instance;
nothing on a defeated one, which is not enforced. -/
noncomputable def held (t : ℕ) : ℝ := if S.undefeated t then (S.c : ℝ) else 0

/-- The settled payout of instance `t` to the ordinary valuation: the consequent's truth on an
undefeated instance; nothing on a defeated one. -/
noncomputable def realized (t : ℕ) : ℝ :=
  if S.undefeated t then (if S.consequent t then 1 else 0) else 0

/-- **The unit-position hypothesis** on an enforcer's per-instance settled value `v`: on each
instance the enforcer's settled gain is one unit of the consequent bought at the held price,
`realized − held`.  Named, not derived: `WarrantForce`'s calibrated intensity trades in
proportion to the displayed violation, and reducing its day value to a unit position per
instance is the assumption this instantiation carries. -/
def UnitPosition (v : ℕ → ℝ) : Prop := ∀ t, v t = S.realized t - S.held t

/-- Under the unit-position hypothesis the enforcer's cumulative value is
`DecisionComponent.liability` with `h := realized` and `g := held`. -/
theorem cumulative_eq_liability {v : ℕ → ℝ} (hv : S.UnitPosition v) (n : ℕ) :
    ∑ t ∈ range n, v t = liability S.realized S.held n := by
  unfold liability
  exact sum_congr rfl fun t _ => hv t

/-- The undefeated instances before `n`. -/
def undefeatedCount (n : ℕ) : ℕ := ((range n).filter fun t => S.undefeated t = true).card

/-- The undefeated instances before `n` whose consequent settled true. -/
def trueCount (n : ℕ) : ℕ :=
  ((range n).filter fun t => S.undefeated t = true ∧ S.consequent t = true).card

lemma sum_held (n : ℕ) : ∑ t ∈ range n, S.held t = S.c * S.undefeatedCount n := by
  unfold held undefeatedCount
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

lemma sum_realized (n : ℕ) : ∑ t ∈ range n, S.realized t = S.trueCount n := by
  unfold realized trueCount
  have : ∀ t, (if S.undefeated t = true then (if S.consequent t = true then (1 : ℝ) else 0) else 0) =
      if (S.undefeated t = true ∧ S.consequent t = true) then 1 else 0 := by
    intro t
    by_cases hu : S.undefeated t = true <;> by_cases hc : S.consequent t = true <;> simp [hu, hc]
  simp_rw [this]
  rw [sum_boole]

/-- **The outperformance sum** is the strength times the undefeated count less the true count. -/
theorem outperformance_eq (n : ℕ) :
    ∑ t ∈ range n, (S.held t - S.realized t) = S.c * S.undefeatedCount n - S.trueCount n := by
  rw [sum_sub_distrib, sum_held, sum_realized]

/-- **Solvency as soundness.**  The enforcer's cumulative liability on the schema is bounded
below by `−B` iff the frequency of the consequent on undefeated instances is not systematically
below the strength: `c · U_n − T_n ≤ B` at every `n`.  An instance of
`DecisionComponent.bounded_iff_not_outperformed` with the source the strength and the
alternative the settled consequent. -/
theorem bounded_iff_frequency (B : ℝ) :
    (∀ n, -B ≤ liability S.realized S.held n) ↔
      ∀ n, S.c * S.undefeatedCount n - S.trueCount n ≤ B := by
  rw [bounded_iff_not_outperformed]
  exact forall_congr' fun n => by rw [outperformance_eq]

/-- The same for any enforcer under the unit-position hypothesis. -/
theorem solvent_iff {v : ℕ → ℝ} (hv : S.UnitPosition v) (B : ℝ) :
    (∀ n, -B ≤ ∑ t ∈ range n, v t) ↔
      ∀ n, S.c * S.undefeatedCount n - S.trueCount n ≤ B := by
  simp only [S.cumulative_eq_liability hv]
  exact S.bounded_iff_frequency B

end Schema

namespace Witness

/-- A schema whose consequent always settles true, at strength `3/4`, every instance undefeated. -/
def alwaysTrue : Schema := ⟨3/4, fun _ => true, fun _ => true⟩

/-- The same schema with the consequent always false. -/
def alwaysFalse : Schema := ⟨3/4, fun _ => true, fun _ => false⟩

/-- **Bounded**: a consequent that always settles true outperforms the strength, and the
liability is nonnegative at every date. -/
theorem always_true_bounded : ∀ n, -(0 : ℝ) ≤ liability alwaysTrue.realized alwaysTrue.held n := by
  rw [alwaysTrue.bounded_iff_frequency]
  intro n
  simp [Schema.undefeatedCount, Schema.trueCount, alwaysTrue]
  linarith

/-- **Unbounded**: a consequent that always settles false puts the frequency `3/4` below the
strength at every date, and the liability falls below every bound
(`systematic_outperformance_unbounded` with gap `3/4`). -/
theorem always_false_unbounded (B : ℝ) :
    ∃ n, liability alwaysFalse.realized alwaysFalse.held n < -B :=
  systematic_outperformance_unbounded _ _ (3/4) (by norm_num)
    (fun _ => by simp [Schema.held, Schema.realized, alwaysFalse]) B

end Witness

/-! ## 2. The conflict audit -/

section Audit

variable {d m : ℕ}

/-- The suspects of a Farkas certificate: the rows it weights positively. -/
def suspects (c : FarkasCert d m) : Finset (Fin m) := univ.filter fun i => 0 < c.mult i

/-- **At every price vector some suspect is violated.**  If every positively weighted row held,
the weighted sum of the rows would give `0 ≤ Σ mult · b < 0`. -/
theorem exists_violated_suspect (c : FarkasCert d m) (x : Fin d → ℚ) :
    ∃ i, 0 < c.mult i ∧ ¬ (c.row i).Sat x := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have h1 : ∑ i, c.mult i * ∑ j, (c.row i).a j * x j ≤ ∑ i, c.mult i * (c.row i).b := by
    apply sum_le_sum
    intro i _
    rcases (c.mult_nonneg i).lt_or_eq with hpos | hzero
    · exact mul_le_mul_of_nonneg_left (h i hpos) hpos.le
    · rw [← hzero]; simp
  have h2 : ∑ i, c.mult i * ∑ j, (c.row i).a j * x j = 0 := by
    calc ∑ i, c.mult i * ∑ j, (c.row i).a j * x j
        = ∑ i, ∑ j, c.mult i * (c.row i).a j * x j := by
          apply sum_congr rfl
          intro i _
          rw [mul_sum]
          apply sum_congr rfl
          intro j _
          ring
      _ = ∑ j, ∑ i, c.mult i * (c.row i).a j * x j := sum_comm
      _ = ∑ j, (∑ i, c.mult i * (c.row i).a j) * x j := by
          apply sum_congr rfl
          intro j _
          rw [sum_mul]
      _ = 0 := by
          apply sum_eq_zero
          intro j _
          rw [c.coeff_sum j, zero_mul]
  have := c.const_sum
  linarith

/-- **Sound rows cannot conflict**: if every row a certificate weights positively holds at a
point, there is no such certificate.  Read at the true posterior, this is the contrapositive
of `conflict_sound`. -/
theorem no_conflict_of_sound (c : FarkasCert d m) (x : Fin d → ℚ)
    (hs : ∀ i, 0 < c.mult i → (c.row i).Sat x) : False :=
  let ⟨i, hi, hv⟩ := exists_violated_suspect c x
  hv (hs i hi)

/-- **A conflict names its suspects.**  Against a bundle, a valid certificate has, at every cube
point, a positively weighted *bundle* row violated there: the cube rows all hold in the cube,
so the violated suspect is one of the bundle's own. -/
theorem suspect_in_bundle {Q : Type*} (B : Bundle Q d) (c : FarkasCert d m)
    (hv : ∀ i, B.Allowed (c.row i)) (x : Fin d → ℚ) (hx : InCube x) :
    ∃ i, 0 < c.mult i ∧ (∃ cr ∈ B, cr.row = c.row i) ∧ ¬ (c.row i).Sat x := by
  obtain ⟨i, hi, hviol⟩ := exists_violated_suspect c x
  refine ⟨i, hi, ?_, hviol⟩
  rcases hv i with h | ⟨j, hj⟩ | ⟨j, hj⟩
  · exact h
  · exact absurd (by rw [hj]; exact cubeUpper_sat hx j) hviol
  · exact absurd (by rw [hj]; exact cubeLower_sat hx j) hviol

/-- The same on a normative state's compiled bundle: a valid conflict certificate names a held
row violated at every cube point. -/
theorem suspect_in_normState (N : NormState d) (cert : FarkasCert d m)
    (hv : ∀ i, N.bundle.Allowed (cert.row i)) (x : Fin d → ℚ) (hx : InCube x) :
    ∃ i, 0 < cert.mult i ∧ (∃ cr ∈ N.bundle, cr.row = cert.row i) ∧ ¬ (cert.row i).Sat x :=
  suspect_in_bundle N.bundle cert hv x hx

/-- **The one mis-admission.**  If every suspect but `i₀` holds at the point, `i₀`'s row is
violated there. -/
theorem unique_suspect (c : FarkasCert d m) (x : Fin d → ℚ) (i₀ : Fin m)
    (hothers : ∀ i, 0 < c.mult i → i ≠ i₀ → (c.row i).Sat x) : ¬ (c.row i₀).Sat x := by
  intro h0
  obtain ⟨i, hi, hv⟩ := exists_violated_suspect c x
  by_cases hii : i = i₀
  · exact hv (hii ▸ h0)
  · exact hv (hothers i hi hii)

/-- A violated suspect lies in `suspects`. -/
theorem mem_suspects_of_violated (c : FarkasCert d m) (x : Fin d → ℚ) :
    ∃ i ∈ suspects c, ¬ (c.row i).Sat x := by
  obtain ⟨i, hi, hv⟩ := exists_violated_suspect c x
  exact ⟨i, by simp [suspects, hi], hv⟩

end Audit

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.WarrantSolvency.Schema.held
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.Schema.realized
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.Schema.UnitPosition
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.Schema.cumulative_eq_liability
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.Schema.undefeatedCount
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.Schema.trueCount
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.Schema.sum_held
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.Schema.sum_realized
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.Schema.outperformance_eq
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.Schema.bounded_iff_frequency
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.Schema.solvent_iff
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.Witness.alwaysTrue
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.Witness.alwaysFalse
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.Witness.always_true_bounded
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.Witness.always_false_unbounded
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.suspects
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.exists_violated_suspect
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.no_conflict_of_sound
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.suspect_in_bundle
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.suspect_in_normState
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.unique_suspect
#print axioms Workspace.Normativity.Contrib.WarrantSolvency.mem_suspects_of_violated

end Workspace.Normativity.Contrib.WarrantSolvency
