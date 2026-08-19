/-
# The projection enforcer as finite data

`EnforcedComputation` asks for an enforcer presented as finite syntax.  The compiler in
`ProjectionCompiler` takes its representations as `Sentence → Rep`, which is a *function*
on sentences: the right shape for the algebra and the wrong one for a computability claim,
since a function on sentences is not finite data and cannot be an input to a
primitive-recursive evaluator.

`ProjectionCompiler.AffineForm` now carries its coefficients as a `List ℚ` in the
fragment's own order, so the compiler's own representations are already finite data.  A
`ProjectionSchedule` is a computable fragment schedule, a computable positive rational
tolerance schedule, and one representation list per date.  From that data alone the day-`n` enforcement trade list is
computed, with the intensity calibrated from the ordinary aggregate's `absBound` — so the
enforcer is an `EffectiveEnforcer` and the whole modified market is the one
`EnforcedComputation` evaluates.

Nothing here re-proves the force algebra.  The bridge lemma says the compiled trades are
the projection position, after which every theorem in `ProjectionMarket`,
`ProjectionCalibrated` and `ProjectionBudget` applies unchanged.

Names are provisional (`AGENTS.md` standard 6).
-/

import LogicalInduction.Construction.LIACompiler
import Workspace.Normativity.Contrib.EnforcedComputation

namespace Workspace.Normativity.Contrib.ProjectionEnforcer

open LogicalInduction
open Workspace.Normativity.Contrib.ProjectionForce
open Workspace.Normativity.Contrib.ProjectionMarket
open Workspace.Normativity.Contrib.ProjectionCompiler
open Workspace.Normativity.Contrib.ProjectionCalibrated
open Workspace.Normativity.Contrib.DeductiveEnforcement
open Workspace.Normativity.Contrib.EnforcedComputation

/-! ## The representation attached to a priced sentence

`ProjectionCompiler.AffineForm` is now itself finite data — a `List ℚ` of coefficients
positionally aligned with the fragment, plus a constant — so there is no second
representation to maintain and no conversion to prove correct.  All that is left is to say
which representation belongs to which priced sentence. -/

/-- The representation attached to a priced sentence by its position in the fragment.
Positional rather than by association list: `List.idxOf` and `List.getD` both have
primitive-recursive certificates, which an association lookup does not, and on a
duplicate-free fragment with aligned data the two agree. -/
def repAt (coords : List Sentence) (reps : List Rep) (dflt : Rep) : Sentence → Rep :=
  fun φ => reps.getD (coords.idxOf φ) dflt

/-! ## The schedule

The minimal effective input interface: which sentences are priced, how closely, and one
finite representation of the day's projector.  Everything else the enforcer needs — the
market's resistance, hence the intensity — it reads off the ordinary aggregate's syntax. -/

/-- The effective input data of the projection construction. -/
structure ProjectionSchedule where
  /-- The day-`n` priced fragment, listed once each. -/
  coords : ℕ → List Sentence
  /-- Each priced sentence is listed once. -/
  nodup : ∀ n, (coords n).Nodup
  /-- The day-`n` requested tolerance. -/
  tol : ℕ → ℚ
  /-- Tolerances are strictly positive; a zero tolerance buys nothing. -/
  tol_pos : ∀ n, 0 < tol n
  /-- The day-`n` max–min representations, positionally aligned with `coords n`. -/
  reps : ℕ → List Rep
  /-- The value used where a lookup fails; it never occurs in a well-formed schedule. -/
  dflt : Rep

/-- **The effectiveness requirement on a schedule**, and the whole of it: its three
components are computable functions of the date.  Every type involved is `Primcodable`
from the pinned dependency's public instances, which is what the finite presentation of
`FinAffine` buys.  This is the input side of the computability claim;
`EnforcedComputation.EnforcedBoundedEvaluatorCompiler` is the output side. -/
structure ProjectionScheduleComputation (S : ProjectionSchedule) where
  /-- The fragment schedule is computable. -/
  coordsComputable : Primrec S.coords
  /-- The tolerance schedule is computable. -/
  tolComputable : Primrec S.tol
  /-- The representation schedule is computable. -/
  repsComputable : Primrec S.reps

/-- The day-`n` fragment of a schedule. -/
def ProjectionSchedule.fragment (S : ProjectionSchedule) (n : ℕ) : Fragment :=
  ⟨S.coords n, S.nodup n⟩

/-- The day-`n` representation map of a schedule. -/
def ProjectionSchedule.rep (S : ProjectionSchedule) (n : ℕ) : Sentence → Rep :=
  repAt (S.coords n) (S.reps n) S.dflt

/-- The day-`n` calibrated intensity, read off the ordinary aggregate's trade list.  It is
computed before the day's price exists, because `tradeListAbsBound` looks only at
syntax. -/
def ProjectionSchedule.intensity (S : ProjectionSchedule) (n : ℕ)
    (ord : List (EF × Sentence)) : ℚ :=
  calibratedIntensity n (Strategy.tradeListAbsBound ord) (S.tol n)

/-- **The projection enforcer, as effective data.**  A `def`: given the schedule, the
day-`n` trade list is finite syntax computed from finite syntax. -/
def ProjectionSchedule.enforcer (S : ProjectionSchedule) : EffectiveEnforcer where
  trades n ord :=
    (projectionStrategy (S.fragment n) n (S.intensity n ord) (S.rep n)).trades
  rank_le n ord p hp :=
    (projectionStrategy (S.fragment n) n (S.intensity n ord) (S.rep n)).rank_le p hp

lemma ProjectionSchedule.enforcer_strategy (S : ProjectionSchedule) (n : ℕ)
    (ord : Strategy n) :
    S.enforcer.strategy n ord =
      projectionStrategy (S.fragment n) n (S.intensity n ord.trades) (S.rep n) := rfl

/-- The traded support is exactly the day's fragment. -/
theorem ProjectionSchedule.enforcer_support (S : ProjectionSchedule) (n : ℕ)
    (ord : Strategy n) :
    (S.enforcer.strategy n ord).support = (S.fragment n).toFinset := by
  rw [S.enforcer_strategy n ord]
  exact projectionStrategy_support (S.fragment n) n (S.intensity n ord.trades) (S.rep n)

/-- **The bridge.**  When the schedule's day-`n` representations evaluate to the target's
coordinates at the day's prices, the compiled trades are the projection position at the
calibrated intensity — so the force algebra applies to them. -/
theorem ProjectionSchedule.enforcer_realizes (S : ProjectionSchedule) (n : ℕ)
    (ord : Strategy n) (V : History) (q : Sentence → ℝ)
    (hrep : ∀ φ ∈ S.coords n, repEval (S.fragment n) (S.rep n φ) (V n) = q φ) :
    Realizes (S.fragment n).toFinset
      ((S.intensity n ord.trades : ℚ) : ℝ) q (S.enforcer.strategy n ord) V := by
  rw [S.enforcer_strategy n ord]
  exact projectionStrategy_realizes (S.fragment n) n (S.intensity n ord.trades)
    (S.rep n) V q hrep

/-! ## The modified deductive market from a schedule -/

/-- The market generated by pricing the source firm together with the schedule's
enforcer. -/
noncomputable def ProjectionSchedule.market (S : ProjectionSchedule)
    (DP : DeductiveProcess) : History :=
  history DP (S.enforcer.adaptive DP)

lemma ProjectionSchedule.market_eq_marketMakerHistory (S : ProjectionSchedule)
    (DP : DeductiveProcess) :
    S.market DP = marketMakerHistory (realizedAggregate DP (S.enforcer.adaptive DP)) :=
  history_eq_marketMakerHistory DP (S.enforcer.adaptive DP)

lemma ProjectionSchedule.aggregate_join (S : ProjectionSchedule) (DP : DeductiveProcess)
    (n : ℕ) :
    (realizedAggregate DP (S.enforcer.adaptive DP)).strat n =
      Strategy.join [(realizedFirm DP (S.enforcer.adaptive DP)).strat n,
        (realizedEnforcer DP (S.enforcer.adaptive DP)).strat n] := rfl

lemma ProjectionSchedule.realizedEnforcer_strat (S : ProjectionSchedule)
    (DP : DeductiveProcess) (n : ℕ) :
    (realizedEnforcer DP (S.enforcer.adaptive DP)).strat n =
      S.enforcer.strategy n ((realizedFirm DP (S.enforcer.adaptive DP)).strat n) := rfl

/-- **Finite-time Euclidean conformance for the schedule's market.**  At every date the
displayed price is within the requested tolerance of the day's region, in the intrinsic
Euclidean distance on the day's fragment. -/
theorem ProjectionSchedule.dist2_le_tol (S : ProjectionSchedule) (DP : DeductiveProcess)
    (n : ℕ) {K : (Sentence → ℝ) → Prop} {q : Sentence → ℝ}
    (hlocal : FragmentLocal (S.fragment n).toFinset K)
    (hKcube : ∀ y, K y → ∀ φ ∈ (S.fragment n).toFinset, 0 ≤ y φ ∧ y φ ≤ 1)
    (hq : IsNearestPoint (S.fragment n).toFinset K (S.market DP n) q)
    (hrep : ∀ φ ∈ S.coords n,
      repEval (S.fragment n) (S.rep n φ) (S.market DP n) = q φ) :
    dist2 (S.fragment n).toFinset (S.market DP n) q ≤ ((S.tol n : ℚ) : ℝ) := by
  set Tr := realizedAggregate DP (S.enforcer.adaptive DP) with hTr
  set ord := (realizedFirm DP (S.enforcer.adaptive DP)).strat n with hord
  have hmarket := S.market_eq_marketMakerHistory DP
  have henf : Realizes (S.fragment n).toFinset
      ((calibratedIntensity n (Strategy.tradeListAbsBound ord.trades) (S.tol n) : ℚ) : ℝ) q
      ((realizedEnforcer DP (S.enforcer.adaptive DP)).strat n) (marketMakerHistory Tr) := by
    rw [S.realizedEnforcer_strat DP n, ← hord, ← hmarket]
    exact S.enforcer_realizes n ord (S.market DP) q hrep
  rw [hmarket] at hq hrep ⊢
  exact dist2_le_of_calibrated Tr n ord
    ((realizedEnforcer DP (S.enforcer.adaptive DP)).strat n)
    (S.aggregate_join DP n) hlocal hKcube hq henf
    (by rw [Strategy.tradeListAbsBound_strategy]) (S.tol_pos n)

/-- **The theorem of record for the schedule's deductive market.**  With the bounded
evaluator compiled, and with every date's region admitting every world the process leaves
plausible, the market is a logical inductor **in the source's original sense** — no
`ComputableMarket` premise — and is finite-time coherent to the requested tolerance at
every date. -/
theorem ProjectionSchedule.end_to_end (S : ProjectionSchedule) {DP : DeductiveProcess}
    (process : DeductiveProcessComputation DP)
    (compiler : EnforcedBoundedEvaluatorCompiler process S.enforcer)
    {K : ℕ → (Sentence → ℝ) → Prop} {q : ℕ → Sentence → ℝ}
    (hlocal : ∀ n, FragmentLocal (S.fragment n).toFinset (K n))
    (hKcube : ∀ n y, K n y → ∀ φ ∈ (S.fragment n).toFinset, 0 ≤ y φ ∧ y φ ≤ 1)
    (hq : ∀ n, IsNearestPoint (S.fragment n).toFinset (K n) (S.market DP n) (q n))
    (hrep : ∀ n, ∀ φ ∈ S.coords n,
      repEval (S.fragment n) (S.rep n φ) (S.market DP n) = q n φ)
    (hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → K n v.payout) :
    IsLogicalInductor (S.market DP) DP ∧
      (∀ n, dist2 (S.fragment n).toFinset (S.market DP n) (q n) ≤ ((S.tol n : ℚ) : ℝ)) ∧
      ∀ n, K n (q n) ∧ ∀ φ ∈ (S.fragment n).toFinset,
        |S.market DP n φ - q n φ| ≤ ((S.tol n : ℚ) : ℝ) := by
  have hconf : ∀ n, dist2 (S.fragment n).toFinset (S.market DP n) (q n)
      ≤ ((S.tol n : ℚ) : ℝ) := fun n =>
    S.dist2_le_tol DP n (hlocal n) (hKcube n) (hq n) (hrep n)
  have hlam : ∀ n, (0 : ℝ) ≤
      ((S.intensity n ((realizedFirm DP (S.enforcer.adaptive DP)).strat n).trades : ℚ) : ℝ) := by
    intro n
    have := calibratedIntensity_pos
      (n := n)
      (A := Strategy.tradeListAbsBound ((realizedFirm DP (S.enforcer.adaptive DP)).strat n).trades)
      (δ := S.tol n)
      (by rw [Strategy.tradeListAbsBound_strategy]; exact Strategy.absBound_nonneg _)
      (S.tol_pos n)
    exact_mod_cast this.le
  have hday : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      0 ≤ ((realizedEnforcer DP (S.enforcer.adaptive DP)).strat n).value
        (S.market DP) v.payout := by
    intro n v hv
    refine day_value_nonneg (Φ := (S.fragment n).toFinset) (K := K n)
      (S.enforcer_realizes n ((realizedFirm DP (S.enforcer.adaptive DP)).strat n)
        (S.market DP) (q n) (hrep n)) (hlam n) (hq n) v.payout (hadm n v hv)
  exact ⟨isLogicalInductor_of_compiler_of_worldInclusive process S.enforcer compiler hday,
    hconf, fun n => sup_conformance_of_dist2 (hq n) (hconf n)⟩

/-- **The canonical instantiation.**  Taking the target to *be* what the day's
representation computes makes the representation hypothesis definitional, so the whole
content of the construction sits in one place: that the represented point is the nearest
point of the day's region.  There is no freedom left in `q`. -/
theorem ProjectionSchedule.end_to_end_canonical (S : ProjectionSchedule)
    {DP : DeductiveProcess} (process : DeductiveProcessComputation DP)
    (compiler : EnforcedBoundedEvaluatorCompiler process S.enforcer)
    {K : ℕ → (Sentence → ℝ) → Prop}
    (hlocal : ∀ n, FragmentLocal (S.fragment n).toFinset (K n))
    (hKcube : ∀ n y, K n y → ∀ φ ∈ (S.fragment n).toFinset, 0 ≤ y φ ∧ y φ ≤ 1)
    (hq : ∀ n, IsNearestPoint (S.fragment n).toFinset (K n) (S.market DP n)
      (fun φ => repEval (S.fragment n) (S.rep n φ) (S.market DP n)))
    (hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → K n v.payout) :
    IsLogicalInductor (S.market DP) DP ∧
      (∀ n, dist2 (S.fragment n).toFinset (S.market DP n)
        (fun φ => repEval (S.fragment n) (S.rep n φ) (S.market DP n))
          ≤ ((S.tol n : ℚ) : ℝ)) ∧
      ∀ n, K n (fun φ => repEval (S.fragment n) (S.rep n φ) (S.market DP n)) ∧
        ∀ φ ∈ (S.fragment n).toFinset,
          |S.market DP n φ - repEval (S.fragment n) (S.rep n φ) (S.market DP n)|
            ≤ ((S.tol n : ℚ) : ℝ) :=
  S.end_to_end process compiler hlocal hKcube hq (fun _ _ _ => rfl) hadm

/-- **Eventual coherence on every fixed finite set.**  If the fragment schedule exhausts
the sentences and the tolerances vanish, then for every finite set of sentences and every
positive slack, from some date on the displayed prices agree with an admitted price vector
to within that slack on that set.  This is the paper's closing consequence, and it needs
nothing beyond the per-date conformance already proved. -/
theorem ProjectionSchedule.eventual_coherence (S : ProjectionSchedule)
    (DP : DeductiveProcess) {K : ℕ → (Sentence → ℝ) → Prop} {q : ℕ → Sentence → ℝ}
    (hconf : ∀ n, K n (q n) ∧ ∀ φ ∈ (S.fragment n).toFinset,
      |S.market DP n φ - q n φ| ≤ ((S.tol n : ℚ) : ℝ))
    (hexh : ∀ Ψ : Finset Sentence, ∃ N, ∀ n, N ≤ n → Ψ ⊆ (S.fragment n).toFinset)
    (hvanish : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n → ((S.tol n : ℚ) : ℝ) ≤ ε)
    (Ψ : Finset Sentence) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n, N ≤ n → ∃ y, K n y ∧ ∀ φ ∈ Ψ, |S.market DP n φ - y φ| ≤ ε := by
  obtain ⟨N₁, hN₁⟩ := hexh Ψ
  obtain ⟨N₂, hN₂⟩ := hvanish ε hε
  refine ⟨max N₁ N₂, fun n hn => ⟨q n, (hconf n).1, fun φ hφ => ?_⟩⟩
  have h1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have h2 : N₂ ≤ n := le_trans (le_max_right _ _) hn
  exact le_trans ((hconf n).2 φ (hN₁ n h1 hφ)) (hN₂ n h2)

end Workspace.Normativity.Contrib.ProjectionEnforcer

#print axioms Workspace.Normativity.Contrib.ProjectionEnforcer.ProjectionSchedule.enforcer_support
#print axioms Workspace.Normativity.Contrib.ProjectionEnforcer.ProjectionSchedule.enforcer_realizes
#print axioms Workspace.Normativity.Contrib.ProjectionEnforcer.ProjectionSchedule.dist2_le_tol
#print axioms Workspace.Normativity.Contrib.ProjectionEnforcer.ProjectionSchedule.end_to_end
#print axioms Workspace.Normativity.Contrib.ProjectionEnforcer.ProjectionSchedule.end_to_end_canonical
#print axioms Workspace.Normativity.Contrib.ProjectionEnforcer.ProjectionSchedule.eventual_coherence
