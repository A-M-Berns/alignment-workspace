/-
# The intrinsic trader budget, and the deductive specialisation

`ProjectionMarket` bounds one date.  This file sums the dates, and then reads the
sum off in the deductive case, where it collapses to zero.

Two things are worth stating plainly about the quantifiers.

**Nothing here assumes the region schedule is nested.**  The day-`k` liability is
assessed against the day-`k` region and nothing else, so the cumulative bound is a
sum of per-date terms.  For a *monotone* schedule one is tempted to say "the point
is admitted at the last date, so the whole history is safe"; that is false in
general, and `late_admission_is_not_enough` exhibits data where the
point is admitted on the final date and the cumulative net worth is still negative.
The correct hypothesis is per-date admission, `∀ k ≤ n, K k w`.

**In the deductive case the correct hypothesis is available.**  A deductive process
is monotone by definition, so a world plausible at date `n` is plausible at every
earlier date; if every plausible world's payout is admitted at its own date, the
per-date hypothesis holds for free and the risk capital is exactly zero.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.ProjectionCompiler
import Workspace.Normativity.Contrib.DeductiveEnforcement

namespace Workspace.Normativity.Contrib.ProjectionBudget

open LogicalInduction
open Workspace.Normativity.Contrib.ProjectionForce
open Workspace.Normativity.Contrib.ProjectionMarket
open Workspace.Normativity.Contrib.DeductiveEnforcement

/-! ## Summing the dates

`Trader.netWorth` is only defined at a world.  The cumulative value is meaningful
at any point of the cube — that is what the region hypotheses are about — so the
sum is stated first at an arbitrary point and then read off at a world. -/

/-- The trader's cumulative day-`0`-to-`n` value, assessed at an arbitrary point. -/
noncomputable def cumValue (E : Trader) (V : History) (w : Sentence → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (E.strat k).value V w

lemma netWorth_eq_cumValue (E : Trader) (V : History) (v : PCWorld) (n : ℕ) :
    E.netWorth V v n = cumValue E V v.payout n := rfl

/-- Per-date lower bounds sum to a cumulative lower bound.  Stated with the
hypotheses restricted to the dates that actually contribute. -/
theorem cumValue_ge_of_dayBounds (E : Trader) (V : History) (w : Sentence → ℝ)
    (b : ℕ → ℝ) (n : ℕ)
    (hday : ∀ k, k ≤ n → -(b k) ≤ (E.strat k).value V w) :
    -(∑ k ∈ Finset.range (n + 1), b k) ≤ cumValue E V w n := by
  rw [cumValue, neg_le, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum ?_
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  linarith [hday k hkn]

/-- **The intrinsic trader budget.**  An enforcement trader that plays the
projection position every day, at intensity `lam k` and confirmed tolerance
`tol k`, has cumulative assessed value at least

    − ∑_{k ≤ n} lam k · tol k · d₂(w, K k)

at every point `w`, where `d₂(w, K k)` is the intrinsic Euclidean distance from
`w` to the day-`k` region on the day-`k` fragment.  No presentation of any region
appears in the bound, and no relation between the regions at different dates is
assumed. -/
theorem cumValue_ge_of_projection (E : Trader) (V : History)
    {Φ : ℕ → Finset Sentence} {K : ℕ → (Sentence → ℝ) → Prop}
    {lam tol : ℕ → ℝ} {q z : ℕ → Sentence → ℝ} (w : Sentence → ℝ) (n : ℕ)
    (henf : ∀ k, k ≤ n → Realizes (Φ k) (lam k) (q k) (E.strat k) V)
    (hlam : ∀ k, k ≤ n → 0 ≤ lam k) (htol : ∀ k, k ≤ n → 0 ≤ tol k)
    (hq : ∀ k, k ≤ n → IsNearestPoint (Φ k) (K k) (V k) (q k))
    (hz : ∀ k, k ≤ n → IsNearestPoint (Φ k) (K k) w (z k))
    (hconf : ∀ k, k ≤ n → dist2 (Φ k) (V k) (q k) ≤ tol k) :
    -(∑ k ∈ Finset.range (n + 1), lam k * tol k * dist2 (Φ k) w (z k))
      ≤ cumValue E V w n :=
  cumValue_ge_of_dayBounds E V w
    (fun k => lam k * tol k * dist2 (Φ k) w (z k)) n
    (fun k hk => day_value_ge (henf k hk) (hlam k hk) (htol k hk) (hq k hk) w
      (hz k hk) (hconf k hk))

/-- **Zero risk capital under per-date admission.**  If the point is admitted by
every region up to the date in question, the projection trader has never lost. -/
theorem cumValue_nonneg_of_forall_mem (E : Trader) (V : History)
    {Φ : ℕ → Finset Sentence} {K : ℕ → (Sentence → ℝ) → Prop}
    {lam : ℕ → ℝ} {q : ℕ → Sentence → ℝ} (w : Sentence → ℝ) (n : ℕ)
    (henf : ∀ k, k ≤ n → Realizes (Φ k) (lam k) (q k) (E.strat k) V)
    (hlam : ∀ k, k ≤ n → 0 ≤ lam k)
    (hq : ∀ k, k ≤ n → IsNearestPoint (Φ k) (K k) (V k) (q k))
    (hw : ∀ k, k ≤ n → K k w) :
    0 ≤ cumValue E V w n := by
  have := cumValue_ge_of_dayBounds E V w (fun _ => 0) n
    (fun k hk => by
      simpa using day_value_nonneg (henf k hk) (hlam k hk) (hq k hk) w (hw k hk))
  simpa using this

/-! ## Late admission is not enough

The witness below is deliberately minimal: one priced atom, a day-`0` region that
excludes the assessed world and a day-`1` region that admits everything.  Every
hypothesis of `cumValue_nonneg_of_forall_mem` holds except that admission is only
required at the last date, and the conclusion fails.  So the per-date quantifier in
that theorem is not a convenience, and the paper's budget statement has to carry it.

-/

/-- The single priced atom of the witness. -/
def wAtom : Sentence := .atom 0

/-- The witness fragment. -/
def wFrag : Finset Sentence := {wAtom}

/-- The witness history: every sentence is quoted at `1/2` on every date. -/
noncomputable def wHistory : History := fun _ _ => (1 : ℝ) / 2

/-- The witness world: every atom is true, so the atom pays `1`. -/
def wWorld : PCWorld := fun _ => True

lemma wWorld_payout_atom : wWorld.payout wAtom = 1 := by
  have : PCWorld.Holds wWorld wAtom := trivial
  simp [PCWorld.payout, this]

/-- The day-`k` region: on date `0` the atom must be worth `0`; after that, anything. -/
def wRegion : ℕ → (Sentence → ℝ) → Prop
  | 0 => fun y => y wAtom = 0
  | _ => fun _ => True

/-- The projected point on date `k`. -/
noncomputable def wProj : ℕ → Sentence → ℝ
  | 0 => fun _ => 0
  | _ => fun _ => (1 : ℝ) / 2

/-- The intensity on date `k`: unit force on date `0`, none afterwards. -/
def wLam : ℕ → ℝ
  | 0 => 1
  | _ => 0

/-- The witness trader: on date `0` it holds `-1/2` units of the atom — exactly the
projection position `lam · (q − p)` — and after that it does nothing. -/
noncomputable def wTrader : Trader where
  strat n :=
    match n with
    | 0 =>
        { trades := [(EF.const (-1 / 2), wAtom)]
          rank_le := by
            intro p hp
            simp only [List.mem_singleton] at hp
            subst hp
            simp [EF.rank] }
    | _ + 1 => { trades := [], rank_le := by intro p hp; simp at hp }

lemma wTrader_zero_value (w : Sentence → ℝ) :
    (wTrader.strat 0).value wHistory w = (-1 / 2) * (w wAtom - 1 / 2) := by
  simp [wTrader, Strategy.value, wHistory, EF.denote]

lemma wTrader_succ_value (m : ℕ) (w : Sentence → ℝ) :
    (wTrader.strat (m + 1)).value wHistory w = 0 := by
  simp [wTrader, Strategy.value]

lemma wRealizes : ∀ k, k ≤ 1 →
    Realizes wFrag (wLam k) (wProj k) (wTrader.strat k) wHistory := by
  intro k hk
  interval_cases k
  · intro w
    rw [wTrader_zero_value]
    simp only [ip, shares, wFrag, wLam, wProj, wHistory, Finset.sum_singleton]
    ring
  · intro w
    rw [wTrader_succ_value]
    simp only [ip, shares, wFrag, wLam, Finset.sum_singleton]
    ring

lemma wLam_nonneg : ∀ k, k ≤ 1 → 0 ≤ wLam k := by
  intro k hk
  interval_cases k <;> norm_num [wLam]

lemma wNearest : ∀ k, k ≤ 1 →
    IsNearestPoint wFrag (wRegion k) (wHistory k) (wProj k) := by
  intro k hk
  interval_cases k
  · refine ⟨by simp [wRegion, wProj], ?_⟩
    intro y hy
    simp only [wRegion] at hy
    simp [ip, wFrag, wProj, wHistory, hy]
  · exact ⟨trivial, by intro y _; simp [ip, wFrag, wProj, wHistory]⟩

/-- **Admission at the last date does not bound the budget.**  The witness satisfies
every other hypothesis of `cumValue_nonneg_of_forall_mem`, is admitted by the final
region, and has strictly negative cumulative net worth. -/
theorem late_admission_is_not_enough :
    (∀ k, k ≤ 1 → Realizes wFrag (wLam k) (wProj k) (wTrader.strat k) wHistory) ∧
    (∀ k, k ≤ 1 → 0 ≤ wLam k) ∧
    (∀ k, k ≤ 1 → IsNearestPoint wFrag (wRegion k) (wHistory k) (wProj k)) ∧
    wRegion 1 wWorld.payout ∧
    wTrader.netWorth wHistory wWorld 1 = -1 / 4 := by
  refine ⟨wRealizes, wLam_nonneg, wNearest, trivial, ?_⟩
  rw [Trader.netWorth]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  rw [wTrader_zero_value, wTrader_succ_value, wWorld_payout_atom]
  norm_num

/-! ## The deductive specialisation

A deductive process is monotone, so the per-date admission hypothesis follows from
a single clause: every world the process leaves plausible at a date has its payout
admitted by that date's region.  The risk capital is then exactly zero, and the
original exploitation criterion survives with the source's own constant `1`.

Nothing in this section refers to a presentation of a region.  The regions enter
only through `IsNearestPoint`, which is the Euclidean nearest-point property. -/

/-- One date's enforcement value is nonnegative when the date's region admits every
world the process leaves plausible. -/
theorem deductive_day_value_nonneg (DP : DeductiveProcess) (E : AdaptiveTrader)
    {Φ : ℕ → Finset Sentence} {K : ℕ → (Sentence → ℝ) → Prop} {lam : ℕ → ℝ}
    {q : ℕ → Sentence → ℝ}
    (henf : ∀ n, Realizes (Φ n) (lam n) (q n)
      ((realizedEnforcer DP E).strat n) (history DP E))
    (hlam : ∀ n, 0 ≤ lam n)
    (hq : ∀ n, IsNearestPoint (Φ n) (K n) (history DP E n) (q n))
    (hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → K n v.payout)
    (n : ℕ) (v : PCWorld) (hv : v.ConsistentWith (DP.D n)) :
    0 ≤ ((realizedEnforcer DP E).strat n).value (history DP E) v.payout :=
  day_value_nonneg (henf n) (hlam n) (hq n) v.payout (hadm n v hv)

/-- **Zero risk capital, intrinsically.**  A projection enforcer whose regions admit
the plausible worlds leaves the source's exploitation criterion intact. -/
theorem no_efficient_trader_exploits_of_projection (DP : DeductiveProcess)
    (E : AdaptiveTrader)
    {Φ : ℕ → Finset Sentence} {K : ℕ → (Sentence → ℝ) → Prop} {lam : ℕ → ℝ}
    {q : ℕ → Sentence → ℝ}
    (henf : ∀ n, Realizes (Φ n) (lam n) (q n)
      ((realizedEnforcer DP E).strat n) (history DP E))
    (hlam : ∀ n, 0 ≤ lam n)
    (hq : ∀ n, IsNearestPoint (Φ n) (K n) (history DP E n) (q n))
    (hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → K n v.payout)
    (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (history DP E) DP :=
  no_efficient_trader_exploits_of_worldInclusive DP E
    (deductive_day_value_nonneg DP E henf hlam hq hadm) Tr hTr

/-- **Finite-time coherence in the modified deductive market.**  The intensity is
computed from the market maker's own slack and the source firm's syntactic bound;
no external bound on the ordinary traders is assumed. -/
theorem deductive_dist2_le_of_intensity (DP : DeductiveProcess) (E : AdaptiveTrader)
    (n : ℕ) {Φ : Finset Sentence} {K : (Sentence → ℝ) → Prop} {lam δ : ℝ}
    {q : Sentence → ℝ}
    (henf : Realizes Φ lam q ((realizedEnforcer DP E).strat n) (history DP E))
    (hq : IsNearestPoint Φ K (history DP E n) q)
    (hqcube : ∀ φ, 0 ≤ q φ ∧ q φ ≤ 1) (hδ : 0 < δ)
    (hlam : ((marketMakerError n : ℝ) +
        (((realizedFirm DP E).strat n).absBound : ℝ)) / δ ^ 2 ≤ lam) :
    dist2 Φ (history DP E n) q ≤ δ := by
  rw [history_eq_marketMakerHistory] at henf hq ⊢
  exact dist2_le_of_intensity (realizedAggregate DP E) n
    ((realizedFirm DP E).strat n) ((realizedEnforcer DP E).strat n) rfl henf hq
    hqcube hδ hlam

/-- **The deductive theorem of record.**  One market, and both halves at once: the
original criterion is preserved with zero risk capital, and at every date the
displayed price is within the date's tolerance of the date's region in the
intrinsic Euclidean distance on the date's fragment.  The third conjunct is the
paper's own `ℓ^∞` form of the coherence conclusion, which follows from the second
with the same tolerance. -/
theorem deductive_projection_end_to_end (DP : DeductiveProcess) (E : AdaptiveTrader)
    {Φ : ℕ → Finset Sentence} {K : ℕ → (Sentence → ℝ) → Prop} {lam δ : ℕ → ℝ}
    {q : ℕ → Sentence → ℝ}
    (henf : ∀ n, Realizes (Φ n) (lam n) (q n)
      ((realizedEnforcer DP E).strat n) (history DP E))
    (hq : ∀ n, IsNearestPoint (Φ n) (K n) (history DP E n) (q n))
    (hqcube : ∀ n φ, 0 ≤ q n φ ∧ q n φ ≤ 1)
    (hadm : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) → K n v.payout)
    (hδ : ∀ n, 0 < δ n)
    (hlam : ∀ n, ((marketMakerError n : ℝ) +
        (((realizedFirm DP E).strat n).absBound : ℝ)) / (δ n) ^ 2 ≤ lam n) :
    (∀ Tr : Trader, EfficientlyComputable Tr → ¬ Tr.Exploits (history DP E) DP) ∧
      (∀ n, dist2 (Φ n) (history DP E n) (q n) ≤ δ n) ∧
      ∀ n, K n (q n) ∧ ∀ φ ∈ Φ n, |history DP E n φ - q n φ| ≤ δ n := by
  have hlam0 : ∀ n, 0 ≤ lam n := by
    intro n
    refine le_trans ?_ (hlam n)
    have h1 : (0 : ℝ) < (marketMakerError n : ℝ) := by
      exact_mod_cast marketMakerError_pos n
    have h2 : (0 : ℝ) ≤ (((realizedFirm DP E).strat n).absBound : ℝ) := by
      exact_mod_cast Strategy.absBound_nonneg _
    have h3 : (0 : ℝ) < (δ n) ^ 2 := pow_pos (hδ n) 2
    exact div_nonneg (by linarith) h3.le
  have hconf : ∀ n, dist2 (Φ n) (history DP E n) (q n) ≤ δ n := fun n =>
    deductive_dist2_le_of_intensity DP E n (henf n) (hq n) (hqcube n) (hδ n) (hlam n)
  exact ⟨fun Tr hTr =>
      no_efficient_trader_exploits_of_projection DP E henf hlam0 hq hadm Tr hTr,
    hconf,
    fun n => sup_conformance_of_dist2 (hq n) (hconf n)⟩

#print axioms Workspace.Normativity.Contrib.ProjectionBudget.cumValue_ge_of_dayBounds
#print axioms Workspace.Normativity.Contrib.ProjectionBudget.cumValue_ge_of_projection
#print axioms Workspace.Normativity.Contrib.ProjectionBudget.cumValue_nonneg_of_forall_mem
#print axioms Workspace.Normativity.Contrib.ProjectionBudget.late_admission_is_not_enough
#print axioms Workspace.Normativity.Contrib.ProjectionBudget.no_efficient_trader_exploits_of_projection
#print axioms Workspace.Normativity.Contrib.ProjectionBudget.deductive_dist2_le_of_intensity
#print axioms Workspace.Normativity.Contrib.ProjectionBudget.deductive_projection_end_to_end

end Workspace.Normativity.Contrib.ProjectionBudget
