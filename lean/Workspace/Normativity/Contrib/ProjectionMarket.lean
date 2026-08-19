/-
# The projection trader against the actual market maker

Two facts about the pinned dependency turn the algebra of `ProjectionForce` into a
theorem about the market Logical Induction actually builds.

**The market maker's guarantee holds at every point of the price cube.** Its
acceptance test quantifies over `{0,1}` tables on the traded support
(`MarketMaker_worldValue_le`), and a strategy's value is *affine* in the world —
`Strategy.value_eq_sum_support` writes it as `⟪ζ, w − P⟫` with `ζ` independent of
`w`. A linear functional on a box attains its maximum at a vertex, so the bound at
the vertices is the bound on the box. Consequently the comparison point may be any
cube point, **including the projection `q` of the displayed price**, chosen after
the price is displayed. There is no circularity: the bound is a statement about the
realized share vector, which is fixed before any comparison point is named.

**The opposing-pressure bound is already in the source.**
`Strategy.abs_value_le` bounds a strategy's value by its own `Strategy.absBound` at
*any* cube point — again not only at `{0,1}` worlds. So the ordinary aggregate's
opposition at `q` is bounded by a rational number computed from the strategy the
firm has already emitted, and the external `M_n` hypothesis the row construction
carried is eliminated rather than assumed.

Together: `λ‖q − P_n‖² ≤ ε_n + A_n`, with `ε_n` the market maker's own slack and
`A_n = absBound` of the ordinary aggregate.

Names are provisional (`AGENTS.md` standard 6).
-/

import Workspace.Normativity.Contrib.ProjectionForce

namespace Workspace.Normativity.Contrib.ProjectionMarket

open LogicalInduction
open Workspace.Normativity.Contrib.ProjectionForce

/-! ## The contract extends from the vertices to the cube -/

/-- A strategy's value is maximised over the price cube at a `{0,1}` table: it is
affine in the world, and a linear functional on a box attains its maximum at a
vertex. -/
theorem value_le_of_forall_bitWorld {n : ℕ} (T : Strategy n) (V : History) (ε : ℝ)
    (h : ∀ b : ↥T.support → Bool, T.value V (supportBitWorld T b) ≤ ε)
    (w : Sentence → ℝ) (hw : ∀ φ, 0 ≤ w φ ∧ w φ ≤ 1) :
    T.value V w ≤ ε := by
  classical
  refine le_trans ?_ (h (fun ψ => decide (0 ≤ T.shares V ψ.1)))
  rw [Strategy.value_eq_sum_support, Strategy.value_eq_sum_support]
  refine Finset.sum_le_sum fun φ hφ => ?_
  have hbit : supportBitWorld T (fun ψ => decide (0 ≤ T.shares V ψ.1)) φ =
      if 0 ≤ T.shares V φ then 1 else 0 := by
    unfold supportBitWorld
    simp [hφ]
  rw [hbit]
  by_cases hs : 0 ≤ T.shares V φ
  · rw [if_pos hs]
    have := (hw φ).2
    nlinarith [hs]
  · rw [if_neg hs]
    have hs' : T.shares V φ < 0 := lt_of_not_ge hs
    have := (hw φ).1
    nlinarith [hs']

/-- The recursive market's prices lie in `[0,1]`. -/
lemma marketMakerHistory_mem_Icc (Tr : Trader) (n : ℕ) (φ : Sentence) :
    0 ≤ marketMakerHistory Tr n φ ∧ marketMakerHistory Tr n φ ≤ 1 :=
  (marketMakerStates Tr n).toValuation_mem_Icc φ

/-- **The market maker's contract at every cube point.**  The source states it at
`{0,1}` worlds; this is the same bound at any price vector in `[0,1]`, which is what
lets the comparison point be the projection of the displayed price. -/
theorem marketMaker_day_value_le_cube (Tr : Trader) (n : ℕ)
    (w : Sentence → ℝ) (hw : ∀ φ, 0 ≤ w φ ∧ w φ ≤ 1) :
    (Tr.strat n).value (marketMakerHistory Tr) w ≤ (marketMakerError n : ℝ) := by
  classical
  set past := marketMakerPast Tr (marketMakerStates Tr) n with hpast
  set Hc := Function.update (beliefHistory past) n
    (marketMakerStates Tr n).toValuation with hHc
  have hbit : ∀ b : ↥(Tr.strat n).support → Bool,
      (Tr.strat n).value Hc (supportBitWorld (Tr.strat n) b) ≤ (marketMakerError n : ℝ) := by
    intro b
    have hmm := MarketMaker_worldValue_le (Tr.strat n) past (marketMakerError n)
      (marketMakerError_pos n) b
    have hstate : MarketMaker (Tr.strat n) past (marketMakerError n)
        (marketMakerError_pos n) = marketMakerStates Tr n := by
      rw [marketMakerStates]
      rfl
    rw [hstate] at hmm
    exact hmm
  have hcube := value_le_of_forall_bitWorld (Tr.strat n) Hc _ hbit w hw
  have hhistory : (Tr.strat n).value Hc w =
      (Tr.strat n).value (marketMakerHistory Tr) w := by
    apply (Tr.strat n).value_eq_of_eqUpTo
    intro day hday φ
    exact congrFun (candidate_marketMakerHistory_eq_upTo Tr n day hday) φ
  rwa [hhistory] at hcube

/-! ## A strategy that realizes the projection position -/

/-- The day-`n` strategy `T` **realizes** the projection position for the fragment
`Φ` at intensity `λ` and nearest point `q`: its value against any world is the
fragment pairing of `λ(q − P_n)` with the displacement from the displayed price.

Stated as the value identity rather than as a condition on shares, because that is
what every theorem below consumes and it is what a compiler has to deliver.
`ProjectionCompiler.projectionStrategy_realizes` produces one. -/
def Realizes (Φ : Finset Sentence) (lam : ℝ) (q : Sentence → ℝ)
    {n : ℕ} (T : Strategy n) (V : History) : Prop :=
  ∀ w : Sentence → ℝ, T.value V w = ip Φ (shares lam (V n) q) (fun φ => w φ - V n φ)

/-- A realizing strategy's value is the fragment pairing the algebra is about. -/
theorem value_eq_ip {Φ : Finset Sentence} {lam : ℝ} {q : Sentence → ℝ} {n : ℕ}
    {T : Strategy n} {V : History} (h : Realizes Φ lam q T V) (w : Sentence → ℝ) :
    T.value V w = ip Φ (shares lam (V n) q) (fun φ => w φ - V n φ) := h w

/-- The share form implies the value form: a strategy trading exactly the fragment
with the projection shares realizes the position. -/
theorem realizes_of_shares {Φ : Finset Sentence} {lam : ℝ} {q : Sentence → ℝ} {n : ℕ}
    {T : Strategy n} {V : History} (hsupp : T.support = Φ)
    (hshares : ∀ φ ∈ Φ, T.shares V φ = lam * (q φ - V n φ)) :
    Realizes Φ lam q T V := by
  intro w
  rw [Strategy.value_eq_sum_support, hsupp]
  unfold ip shares
  exact Finset.sum_congr rfl fun φ hφ => by rw [hshares φ hφ]

/-! ## Conformance, with no external volume hypothesis -/

/-- **Finite-time projection conformance.**  If the market prices the ordinary
aggregate joined with a realizing projection strategy, then

    λ · ‖q − P_n‖²  ≤  ε_n + absBound(ordinary aggregate),

where `ε_n` is the market maker's own slack.  Both quantities on the right are
computed from objects that exist before the price is displayed. -/
theorem sqDist_le_slack_add_absBound
    (Tr : Trader) (n : ℕ) {Φ : Finset Sentence} {K : (Sentence → ℝ) → Prop}
    {lam : ℝ} {q : Sentence → ℝ} (ord enf : Strategy n)
    (hjoin : Tr.strat n = Strategy.join [ord, enf])
    (henf : Realizes Φ lam q enf (marketMakerHistory Tr))
    (hq : IsNearestPoint Φ K (marketMakerHistory Tr n) q)
    (hqcube : ∀ φ, 0 ≤ q φ ∧ q φ ≤ 1) (hlam : 0 ≤ lam) :
    lam * sqDist Φ (marketMakerHistory Tr n) q
      ≤ (marketMakerError n : ℝ) + (ord.absBound : ℝ) := by
  have hcontract := marketMaker_day_value_le_cube Tr n q hqcube
  have hsplit : (Tr.strat n).value (marketMakerHistory Tr) q =
      ord.value (marketMakerHistory Tr) q + enf.value (marketMakerHistory Tr) q := by
    rw [hjoin, Strategy.join_value]
    simp
  have hord : |ord.value (marketMakerHistory Tr) q| ≤ (ord.absBound : ℝ) :=
    Strategy.abs_value_le ord (marketMakerHistory Tr)
      (fun day φ => marketMakerHistory_mem_Icc Tr day φ) q hqcube
  have hforce : lam * sqDist Φ (marketMakerHistory Tr n) q
      ≤ enf.value (marketMakerHistory Tr) q := by
    rw [value_eq_ip henf]
    exact force_inequality hlam hq hq.1
  have hordlow := (abs_le.mp hord).1
  rw [hsplit] at hcontract
  linarith

/-- **The intensity that buys a tolerance.**  With `λ ≥ ρ / δ²` and `ρ` the day's
slack-plus-opposition, the displayed price is within `δ` of the region in the
intrinsic Euclidean distance on the fragment. -/
theorem dist2_le_of_intensity
    (Tr : Trader) (n : ℕ) {Φ : Finset Sentence} {K : (Sentence → ℝ) → Prop}
    {lam δ : ℝ} {q : Sentence → ℝ} (ord enf : Strategy n)
    (hjoin : Tr.strat n = Strategy.join [ord, enf])
    (henf : Realizes Φ lam q enf (marketMakerHistory Tr))
    (hq : IsNearestPoint Φ K (marketMakerHistory Tr n) q)
    (hqcube : ∀ φ, 0 ≤ q φ ∧ q φ ≤ 1)
    (hδ : 0 < δ)
    (hlam : ((marketMakerError n : ℝ) + (ord.absBound : ℝ)) / δ ^ 2 ≤ lam) :
    dist2 Φ (marketMakerHistory Tr n) q ≤ δ := by
  set ρ : ℝ := (marketMakerError n : ℝ) + (ord.absBound : ℝ) with hρ
  have hρpos : 0 < ρ := by
    have h1 : (0 : ℝ) < (marketMakerError n : ℝ) := by
      exact_mod_cast marketMakerError_pos n
    have h2 : (0 : ℝ) ≤ (ord.absBound : ℝ) := by
      exact_mod_cast Strategy.absBound_nonneg ord
    rw [hρ]; linarith
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hlampos : 0 < lam := lt_of_lt_of_le (div_pos hρpos hδ2) hlam
  have hbound := sqDist_le_slack_add_absBound Tr n ord enf hjoin henf hq hqcube
    hlampos.le
  have hlamdelta : ρ ≤ lam * δ ^ 2 := (div_le_iff₀ hδ2).mp hlam
  have hsq : sqDist Φ (marketMakerHistory Tr n) q ≤ δ ^ 2 := by
    have := hbound.trans hlamdelta
    exact le_of_mul_le_mul_left (by linarith) hlampos
  have hnn := sqDist_nonneg Φ (marketMakerHistory Tr n) q
  unfold dist2
  calc Real.sqrt (sqDist Φ (marketMakerHistory Tr n) q)
      ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = δ := by rw [Real.sqrt_sq hδ.le]

/-! ## Liability at a world -/

/-- **The day's assessed loss.**  At a world whose fragment restriction the region
admits, the projection trader's value is nonnegative.  At any other point it loses
at most `λδ` times that point's intrinsic distance from the region. -/
theorem day_value_ge
    {Φ : Finset Sentence} {K : (Sentence → ℝ) → Prop} {lam δ : ℝ}
    {q : Sentence → ℝ} {n : ℕ} {T : Strategy n} {V : History}
    (henf : Realizes Φ lam q T V) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (hq : IsNearestPoint Φ K (V n) q) (w : Sentence → ℝ) {z : Sentence → ℝ}
    (hz : IsNearestPoint Φ K w z) (hconf : dist2 Φ (V n) q ≤ δ) :
    -(lam * δ * dist2 Φ w z) ≤ T.value V w := by
  rw [value_eq_ip henf]
  exact liability_calibrated hlam hδ hq hz hconf

/-- The zero-liability case, stated at the shape the preservation theorem consumes:
if the region admits the world's fragment restriction, the day costs nothing. -/
theorem day_value_nonneg
    {Φ : Finset Sentence} {K : (Sentence → ℝ) → Prop} {lam : ℝ}
    {q : Sentence → ℝ} {n : ℕ} {T : Strategy n} {V : History}
    (henf : Realizes Φ lam q T V) (hlam : 0 ≤ lam)
    (hq : IsNearestPoint Φ K (V n) q) (w : Sentence → ℝ) (hw : K w) :
    0 ≤ T.value V w := by
  rw [value_eq_ip henf]
  exact value_nonneg_of_mem hlam hq hw

end Workspace.Normativity.Contrib.ProjectionMarket

#print axioms Workspace.Normativity.Contrib.ProjectionMarket.value_le_of_forall_bitWorld
#print axioms Workspace.Normativity.Contrib.ProjectionMarket.marketMaker_day_value_le_cube
#print axioms Workspace.Normativity.Contrib.ProjectionMarket.value_eq_ip
#print axioms Workspace.Normativity.Contrib.ProjectionMarket.sqDist_le_slack_add_absBound
#print axioms Workspace.Normativity.Contrib.ProjectionMarket.dist2_le_of_intensity
#print axioms Workspace.Normativity.Contrib.ProjectionMarket.day_value_ge
#print axioms Workspace.Normativity.Contrib.ProjectionMarket.day_value_nonneg
