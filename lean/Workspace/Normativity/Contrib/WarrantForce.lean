/-
# Warrant force: the calibrated warrant enforcer on the deductive market

Round `projects/normativity/rounds/2026-10-22-normative-inductor-integration/`.

The force layer's rowwise trader (`EnforcementStrategy.enforcementStrategy`) is here run on
the market the repository's computability and preservation theorems are stated for — the
deductive market `DeductiveEnforcement.history` of a `DeductiveProcess` priced together
with an `EffectiveEnforcer` — on the rows of a compiled bundle, at the **calibrated
intensity** `(ε_n + A_n)/tol_n²` of `ProjectionCalibrated` (the market maker's slack plus the
ordinary aggregate's syntactic bound, over the squared tolerance).

* **The schedule** (`WarrantSchedule`): a fragment map `ι : Fin d → Sentence`, the day's
  compiled bundle, the day's tolerance.  `enforcer` is the trader as effective data
  (finite syntax from the bundle, the date and the ordinary trade list); `market` is the
  augmented deductive market; `account` is its `OddsBankroll.Account` with the capital `3`
  (`marketMaker_netWorth_lt_one` and the source firm's floor `tradingFirmTrader_netWorth_floor`).
* **Preservation** (`isLogicalInductor`): the augmented market is a logical inductor over
  the deductive process from a liability bound and the enforcer's effectiveness
  (`EnforcedCompiler.computableMarket` supplies `ComputableMarket`).  **The bankroll**
  (`liability`, `liability_reopened`): the odds bankroll on the compiled bundle's rows,
  stated on the seed rows' gaps so that the intensity never appears.
* **Conformance** (`rowViolation_le_tol`, `excess_le_tol`): at every date with a rational
  feasibility witness in the cube, every row of the day's bundle has excess at most `tol_n`
  at the displayed price — the real market-maker contract (`marketMaker_day_value_le_cube`)
  and the ordinary aggregate's bound (`Strategy.abs_value_le`) are what discharge the
  force inequality's slack and volume terms.
* **Transport** (`FunctionalCert.le_of_excess`, `BoundCert.transport`,
  `bracket_at_market`): a certificate — nonnegative multipliers on rows whose normals sum to
  a functional — carries rowwise conformance to the functional: at the displayed price the
  functional is within `mass · tol_n` of the certified bound, where `mass` is the
  multiplier sum.  For a `Supported` verdict, the displayed price of the coordinate lies in
  the certified bracket widened by `mass · tol_n` on each side.  This is the quantitative
  conversion from the force layer's rowwise guarantee to the bounds a licence certifies and
  an adapter reads.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.WarrantEntitlement
import Workspace.Normativity.Contrib.EnforcedCompiler
import Workspace.Normativity.Contrib.ProjectionCalibrated
import Workspace.Normativity.Contrib.ProjectionPrimrec

namespace Workspace.Normativity.Contrib.WarrantForce

open LogicalInduction
open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.SeedStatics
open Workspace.Normativity.Contrib.WarrantEntitlement
open Workspace.Normativity.Contrib.WarrantEntitlement.Fixture (toForceRow toForceRow_pair
  toForceRow_gap)
open Workspace.Normativity.Contrib.EnforcementStrategy
open Workspace.Normativity.Contrib.TraderizedEnforcement
open Workspace.Normativity.Contrib.OddsBankroll
open Workspace.Normativity.Contrib.DeductiveEnforcement
open Workspace.Normativity.Contrib.EnforcedComputation
open Workspace.Normativity.Contrib.ProjectionCalibrated (calibratedIntensity resistance
  calibratedIntensity_pos)
open Workspace.Normativity.Contrib.ProjectionMarket (marketMaker_day_value_le_cube)
open Workspace.Normativity.Contrib.AssessmentProcess (ratPayout)

variable {d : ℕ}

/-! ## 1. A bundle as a presentation -/

/-- **The force presentation of a bundle**: every cited row through the bridge `toForceRow`
at the intensity `κ`, on the fragment `coords`. -/
def bundlePres (ι : Fin d → Sentence) (coords : List Sentence) (hnodup : coords.Nodup)
    (B : Bundle (Cite d) d) (κ : ℚ) (hκ : 0 ≤ κ) : Presentation :=
  ⟨coords, hnodup, B.map fun c => toForceRow ι κ hκ c.row⟩

section BundlePres

variable (ι : Fin d → Sentence) (coords : List Sentence) (hnodup : coords.Nodup)
  (B : Bundle (Cite d) d) (κ : ℚ) (hκ : 0 ≤ κ)

@[simp] lemma bundlePres_rows :
    (bundlePres ι coords hnodup B κ hκ).rows = B.map fun c => toForceRow ι κ hκ c.row := rfl

@[simp] lemma bundlePres_coordList : (bundlePres ι coords hnodup B κ hκ).coordList = coords := rfl

lemma mem_bundlePres_rows {r : Row} :
    r ∈ (bundlePres ι coords hnodup B κ hκ).rows ↔ ∃ c ∈ B, r = toForceRow ι κ hκ c.row := by
  simp [bundlePres, eq_comm]

/-- Every row of the bundle's presentation is enforced at the intensity `κ`. -/
lemma bundlePres_intensity (i : Fin (bundlePres ι coords hnodup B κ hκ).rows.length) :
    (bundlePres ι coords hnodup B κ hκ).intensities i = κ := by
  have hmem := List.get_mem (bundlePres ι coords hnodup B κ hκ).rows i
  obtain ⟨c, -, hc⟩ := (mem_bundlePres_rows ι coords hnodup B κ hκ).1 hmem
  simp only [Presentation.intensities, Presentation.rowAt] at hc ⊢
  rw [hc]
  rfl

lemma mem_coords_of_mem (hι : ∀ j, ι j ∈ coords) (j : Fin d) :
    ι j ∈ (bundlePres ι coords hnodup B κ hκ).coords := by
  simp [Presentation.coords, bundlePres, hι j]

end BundlePres

/-- The violation of a bridged row at a price is the positive part of the seed row's excess
`a · p − b` at the pulled-back price `p = q ∘ ι`. -/
theorem violation_toForceRow (ι : Fin d → Sentence) (κ : ℚ) (hκ : 0 ≤ κ) (coords : Finset Sentence)
    (hι : ∀ j, ι j ∈ coords) (r : Row d) (q : Sentence → ℚ) :
    violation coords (toForceRow ι κ hκ r).coeff (toForceRow ι κ hκ r).rhs q =
      max 0 (∑ j, r.a j * q (ι j) - r.b) := by
  unfold violation
  rw [toForceRow_pair ι κ hκ r coords hι]
  simp only [toForceRow]
  congr 1
  ring

/-- The seed row's gap at a world, through the fragment map: positive when the world clears
the row. -/
noncomputable def seedGap (ι : Fin d → Sentence) (r : Row d) (v : PCWorld) : ℚ :=
  r.b - ∑ j, r.a j * ratPayout v (ι j)

lemma rowGap_toForceRow (ι : Fin d → Sentence) (κ : ℚ) (hκ : 0 ≤ κ) (coords : Finset Sentence)
    (hι : ∀ j, ι j ∈ coords) (r : Row d) (v : PCWorld) :
    rowGap coords (toForceRow ι κ hκ r) v = seedGap ι r v :=
  toForceRow_gap ι κ hκ r coords hι v

/-- The seed row's excess at a point of `Fin d → ℚ`. -/
def excess (r : Row d) (p : Fin d → ℚ) : ℚ := ∑ j, r.a j * p j - r.b

lemma excess_nonpos_of_sat {r : Row d} {p : Fin d → ℚ} (h : r.Sat p) : excess r p ≤ 0 := by
  unfold excess Row.Sat at *; linarith

/-- At a world the settlement pins, the specialized row's gap is the row's gap. -/
theorem seedGap_specialize (ι : Fin d → Sentence) (F : Settlement d) (r : Row d) (v : PCWorld)
    (hv : F.Pinned fun j => ratPayout v (ι j)) :
    seedGap ι (specialize F r) v = seedGap ι r v := by
  unfold seedGap specialize
  simp only
  have key : ∀ j, r.a j * ratPayout v (ι j) =
      (if (F.val j).isSome then 0 else r.a j) * ratPayout v (ι j) + settledTerm F r j := by
    intro j
    unfold settledTerm
    cases h : F.val j with
    | none => simp
    | some b => simp [hv j b h]
  rw [show (∑ j, r.a j * ratPayout v (ι j)) =
      ∑ j, ((if (F.val j).isSome then 0 else r.a j) * ratPayout v (ι j) + settledTerm F r j) from
      Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib]
  ring

/-- At a world the settlement pins, a pin row's gap is zero. -/
theorem seedGap_pinRow (ι : Fin d → Sentence) (F : Settlement d) {i : Fin d} {r : Row d}
    (hr : r ∈ F.pinRowsAt i) (v : PCWorld) (hv : F.Pinned fun j => ratPayout v (ι j)) :
    seedGap ι r v = 0 := by
  unfold Settlement.pinRowsAt at hr
  cases h : F.val i with
  | none => simp [h] at hr
  | some b =>
      simp only [h, Option.elim, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hr
      have hp := hv i b h
      rcases hr with rfl | rfl <;>
        simp [seedGap, ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq', hp]

/-! ## 2. The schedule and the enforcer -/

/-- **A warrant schedule**: a fixed fragment, the compiled bundle of each date, and the
tolerance requested at each date. -/
structure WarrantSchedule (d : ℕ) where
  /-- The fragment map: coordinate `j` is priced as the sentence `ι j`. -/
  ι : Fin d → Sentence
  inj : Function.Injective ι
  /-- The priced sentences, listed once each. -/
  coords : List Sentence
  nodup : coords.Nodup
  mem : ∀ j, ι j ∈ coords
  /-- The compiled bundle of each date. -/
  bundle : ℕ → Bundle (Cite d) d
  /-- The tolerance requested at each date. -/
  tol : ℕ → ℚ
  tol_pos : ∀ n, 0 < tol n

lemma tradeListAbsBound_nonneg (l : List (EF × Sentence)) : 0 ≤ Strategy.tradeListAbsBound l := by
  unfold Strategy.tradeListAbsBound
  exact List.sum_nonneg fun q hq => by
    simp only [List.mem_map] at hq
    obtain ⟨p, -, rfl⟩ := hq
    exact p.1.absBound_nonneg

namespace WarrantSchedule

variable (W : WarrantSchedule d)

/-- The calibrated intensity of date `n` against the ordinary trade list `ord`:
`(ε_n + A)/tol_n²`. -/
def κ (n : ℕ) (ord : List (EF × Sentence)) : ℚ :=
  calibratedIntensity n (Strategy.tradeListAbsBound ord) (W.tol n)

lemma κ_pos (n : ℕ) (ord : List (EF × Sentence)) : 0 < W.κ n ord :=
  calibratedIntensity_pos (tradeListAbsBound_nonneg ord) (W.tol_pos n)

/-- The presentation enforced on date `n` against the ordinary trade list `ord`. -/
def presAt (n : ℕ) (ord : List (EF × Sentence)) : Presentation :=
  bundlePres W.ι W.coords W.nodup (W.bundle n) (W.κ n ord) (W.κ_pos n ord).le

/-- **The calibrated warrant enforcer**, as effective data: the compiled position on the
day's bundle at the calibrated intensity. -/
def enforcer : EffectiveEnforcer where
  trades n _ ord := (enforcementStrategy (W.presAt n ord) n).trades
  rank_le n _ ord p hp := (enforcementStrategy (W.presAt n ord) n).rank_le p hp

variable (DP : DeductiveProcess)

/-- **The augmented deductive market**: the source firm priced together with the warrant
enforcer. -/
noncomputable def market : History := history DP (W.enforcer.adaptive DP)

/-- Its exact rational quotes. -/
noncomputable def quoteAt : ℕ → Sentence → ℚ := quote DP (W.enforcer.adaptive DP)

lemma market_eq_quote_cast (n : ℕ) (φ : Sentence) : W.market DP n φ = (W.quoteAt DP n φ : ℝ) :=
  rfl

/-- The ordinary aggregate's realized day-`n` trade list. -/
noncomputable def ordAt (n : ℕ) : List (EF × Sentence) :=
  ((realizedFirm DP (W.enforcer.adaptive DP)).strat n).trades

/-- The presentation realized on date `n`. -/
noncomputable def realizedPres (n : ℕ) : Presentation := W.presAt n (W.ordAt DP n)

/-- The realized intensity of date `n`. -/
noncomputable def realizedκ (n : ℕ) : ℚ := W.κ n (W.ordAt DP n)

lemma realizedκ_pos (n : ℕ) : 0 < W.realizedκ DP n := W.κ_pos n _

lemma realizedEnforcer_strat (n : ℕ) :
    (realizedEnforcer DP (W.enforcer.adaptive DP)).strat n =
      enforcementStrategy (W.realizedPres DP n) n := rfl

lemma mem_realizedPres_rows {n : ℕ} {r : Row} :
    r ∈ (W.realizedPres DP n).rows ↔
      ∃ c ∈ W.bundle n, r = toForceRow W.ι (W.realizedκ DP n) (W.realizedκ_pos DP n).le c.row :=
  mem_bundlePres_rows _ _ _ _ _ _

lemma mem_realizedPres_coords (n : ℕ) (j : Fin d) : W.ι j ∈ (W.realizedPres DP n).coords :=
  mem_coords_of_mem _ _ _ _ _ _ W.mem j

/-- The displayed price pulled back to the fragment's coordinates. -/
noncomputable def priceVec (n : ℕ) : Fin d → ℚ := fun j => W.quoteAt DP n (W.ι j)

lemma quoteAt_mem_Icc (n : ℕ) (φ : Sentence) : 0 ≤ W.quoteAt DP n φ ∧ W.quoteAt DP n φ ≤ 1 := by
  have := history_range DP (W.enforcer.adaptive DP) n φ
  rw [history_eq_quote_cast] at this
  exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩

/-! ### The account and the bankroll -/

/-- **The deductive market's account**: the warrant enforcer on the augmented deductive
market, capped at `3` — the market maker's constant `1` plus the source firm's floor `2`. -/
noncomputable def account : Account where
  P := W.market DP
  Q := W.quoteAt DP
  hQ := history_eq_quote_cast DP _
  Live n v := v.ConsistentWith (DP.D n)
  enf := realizedEnforcer DP (W.enforcer.adaptive DP)
  pres := W.realizedPres DP
  strat_eq := fun _ => rfl
  cap := 3
  netWorth_lt_cap := by
    intro n v hv
    set E := W.enforcer.adaptive DP
    have hmm : (realizedAggregate DP E).netWorth (history DP E) v n < 1 := by
      rw [history_eq_marketMakerHistory]
      exact marketMaker_netWorth_lt_one (realizedAggregate DP E) v n
    have hfirm : -2 ≤ (realizedFirm DP E).netWorth (history DP E) v n := by
      rw [← tradingFirmTrader_quote_eq_realizedFirm]
      exact LogicalInduction.tradingFirmTrader_netWorth_floor DP (history DP E)
        (history_range DP E) (quote DP E) (history_eq_quote_cast DP E) n v hv
    have hsplit := realizedAggregate_netWorth DP E n (history DP E) v
    show (realizedEnforcer DP E).netWorth (history DP E) v n < 3
    linarith

/-- A domination hypothesis on the bundle's seed rows is one on the realized presentation's
rows, whatever the intensity. -/
lemma dom_of_seed {ρ : ℚ} {n : ℕ} {w v' : PCWorld}
    (h : ∀ c ∈ W.bundle n, -(seedGap W.ι c.row w) ≤ ρ * seedGap W.ι c.row v') :
    ∀ r ∈ (W.realizedPres DP n).rows,
      -(rowGap (W.realizedPres DP n).coords r w) ≤ ρ * rowGap (W.realizedPres DP n).coords r v' := by
  intro r hr
  obtain ⟨c, hc, rfl⟩ := (W.mem_realizedPres_rows DP).1 hr
  rw [rowGap_toForceRow _ _ _ _ (W.mem_realizedPres_coords DP n),
    rowGap_toForceRow _ _ _ _ (W.mem_realizedPres_coords DP n)]
  exact h c hc

/-- **The odds bankroll on the deductive market**: a slack plausible world at every date,
dominating every row of every date's bundle at the odds, bounds the enforcer's assessed net
worth below by `−3ρ`. -/
theorem liability (ρ : ℚ) (hρ : 0 ≤ ρ)
    (hslack : ∀ n, ∃ v' : PCWorld, v'.ConsistentWith (DP.D n) ∧
      ∀ w : PCWorld, w.ConsistentWith (DP.D n) → ∀ t ≤ n, ∀ c ∈ W.bundle t,
        -(seedGap W.ι c.row w) ≤ ρ * seedGap W.ι c.row v') :
    ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      -(3 * (ρ : ℝ)) ≤
        (realizedEnforcer DP (W.enforcer.adaptive DP)).netWorth (W.market DP) v n := by
  refine (W.account DP).liability_of_odds ρ hρ fun n => ?_
  obtain ⟨v', hv', h⟩ := hslack n
  exact ⟨v', hv', fun w hw t ht => W.dom_of_seed DP (h w hw t ht)⟩

/-- **The odds bankroll across one reopening on the deductive market**: `−3ρ(2 + ρ)`. -/
theorem liability_reopened (ρ : ℚ) (hρ : 0 ≤ ρ) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (v₀ : PCWorld) (hv₀ : v₀.ConsistentWith (DP.D (m - 1))) (v' : PCWorld)
    (hv' : v'.ConsistentWith (DP.D n)) (w : PCWorld)
    (hdom₀w : ∀ t < m, ∀ c ∈ W.bundle t, -(seedGap W.ι c.row w) ≤ ρ * seedGap W.ι c.row v₀)
    (hdom₀v' : ∀ t < m, ∀ c ∈ W.bundle t, -(seedGap W.ι c.row v') ≤ ρ * seedGap W.ι c.row v₀)
    (hdom' : ∀ t, m ≤ t → t ≤ n → ∀ c ∈ W.bundle t,
      -(seedGap W.ι c.row w) ≤ ρ * seedGap W.ι c.row v') :
    -(3 * (ρ : ℝ) * (2 + ρ)) ≤
      (realizedEnforcer DP (W.enforcer.adaptive DP)).netWorth (W.market DP) w n :=
  (W.account DP).netWorth_ge_neg_odds_reopened ρ hρ hm hmn v₀ hv₀ v' hv' w
    (fun t ht => W.dom_of_seed DP (hdom₀w t ht)) (fun t ht => W.dom_of_seed DP (hdom₀v' t ht))
    (fun t ht₁ ht₂ => W.dom_of_seed DP (hdom' t ht₁ ht₂))

/-- Rows every plausible world clears cost nothing. -/
theorem netWorth_nonneg_of_inclusive (n : ℕ) (w : PCWorld)
    (hw : ∀ t ≤ n, ∀ c ∈ W.bundle t, 0 ≤ seedGap W.ι c.row w) :
    0 ≤ (realizedEnforcer DP (W.enforcer.adaptive DP)).netWorth (W.market DP) w n := by
  refine (W.account DP).netWorth_nonneg_of_inclusive n w fun t ht r hr => ?_
  obtain ⟨c, hc, rfl⟩ := (W.mem_realizedPres_rows DP).1 hr
  show 0 ≤ rowGap (W.realizedPres DP t).coords _ w
  rw [rowGap_toForceRow _ _ _ _ (W.mem_realizedPres_coords DP t)]
  exact hw t ht c hc

/-! ### Preservation -/

/-- **The augmented deductive market is a logical inductor** from a liability bound and the
enforcer's effectiveness: `ComputableMarket` is supplied by `EnforcedCompiler`, not
assumed. -/
theorem isLogicalInductor (process : DeductiveProcessComputation DP)
    (hE : EnforcedCompiler.EffectiveEnforcerComputation W.enforcer) (B : ℝ)
    (hliab : ∀ n (v : PCWorld), v.ConsistentWith (DP.D n) →
      -B ≤ (realizedEnforcer DP (W.enforcer.adaptive DP)).netWorth (W.market DP) v n) :
    IsLogicalInductor (W.market DP) DP :=
  isLogicalInductor_of_computableMarket DP (W.enforcer.adaptive DP) B process.toComputable
    hliab (EnforcedCompiler.computableMarket process hE)

/-! ### Conformance at the realized market -/

/-- A rational point of the cube on the fragment extends to a rational valuation of every
sentence in the cube. -/
theorem exists_extension (y : Fin d → ℚ) (hy : InCube y) :
    ∃ x : Sentence → ℚ, (∀ φ, 0 ≤ x φ ∧ x φ ≤ 1) ∧ ∀ j, x (W.ι j) = y j := by
  classical
  refine ⟨fun φ => if h : ∃ j, W.ι j = φ then y h.choose else 0, fun φ => ?_, fun j => ?_⟩
  · dsimp only
    split_ifs with h
    · exact hy _
    · norm_num
  · have h : ∃ j', W.ι j' = W.ι j := ⟨j, rfl⟩
    dsimp only
    rw [dif_pos h]
    congr 1
    exact W.inj h.choose_spec

/-- **Row-wise conformance at the realized market.**  If a rational cube point satisfies
every row of the day's bundle, every row of the realized presentation has violation at
most the day's tolerance at the displayed price.  The force inequality's slack is the
market maker's own (`marketMaker_day_value_le_cube`) and its volume term is the ordinary
aggregate's syntactic bound (`Strategy.abs_value_le`); the calibrated intensity is exactly
what buys the tolerance. -/
theorem rowViolation_le_tol (n : ℕ) (y : Fin d → ℚ) (hy : (W.bundle n).Region y)
    (i : Fin (W.realizedPres DP n).rows.length) :
    (W.realizedPres DP n).rowViolation i (W.quoteAt DP n) ≤ W.tol n := by
  obtain ⟨x, hxcube, hxι⟩ := W.exists_extension y hy.1
  set E := W.enforcer.adaptive DP with hE
  set A := Strategy.tradeListAbsBound (W.ordAt DP n) with hA
  have hA0 : 0 ≤ A := tradeListAbsBound_nonneg _
  have hε : 0 < marketMakerError n := marketMakerError_pos n
  have hxR : ∀ φ, 0 ≤ ((x φ : ℚ) : ℝ) ∧ ((x φ : ℚ) : ℝ) ≤ 1 := fun φ =>
    ⟨by exact_mod_cast (hxcube φ).1, by exact_mod_cast (hxcube φ).2⟩
  -- every row holds at `x`, in force-row form
  have hxrows : ∀ i ∈ (W.realizedPres DP n).rowIndex, (W.realizedPres DP n).rhss i ≤ pair (W.realizedPres DP n).coords ((W.realizedPres DP n).normals i) x := by
    intro i _
    have hmem := List.get_mem (W.realizedPres DP n).rows i
    obtain ⟨c, hc, hr⟩ := (W.mem_realizedPres_rows DP).1 hmem
    simp only [Presentation.rhss, Presentation.normals, Presentation.rowAt] at hr ⊢
    rw [hr, toForceRow_pair _ _ _ _ _ (W.mem_realizedPres_coords DP n)]
    have hsat := hy.2 c hc
    unfold Row.Sat at hsat
    simp only [toForceRow]
    have : ∑ j, c.row.a j * x (W.ι j) = ∑ j, c.row.a j * y j := by
      refine Finset.sum_congr rfl fun j _ => ?_; rw [hxι j]
    rw [this]; linarith
  -- the enforcement inequality against `x`
  have hsq : ∑ i ∈ (W.realizedPres DP n).rowIndex, (W.realizedPres DP n).intensities i * (W.realizedPres DP n).rowViolation i (W.quoteAt DP n) ^ 2 ≤
      pair (W.realizedPres DP n).coords ((W.realizedPres DP n).compiledPosition (W.quoteAt DP n))
        (fun φ => x φ - W.quoteAt DP n φ) :=
    weighted_square_le_pair (W.realizedPres DP n).intensities_nonneg hxrows
  -- the value identity
  have hval : ((pair (W.realizedPres DP n).coords ((W.realizedPres DP n).compiledPosition (W.quoteAt DP n))
      (fun φ => x φ - W.quoteAt DP n φ) : ℚ) : ℝ) =
      ((realizedEnforcer DP E).strat n).value (W.market DP) (fun φ => (x φ : ℝ)) := by
    rw [W.realizedEnforcer_strat]
    exact (value_enforcementStrategy (W.realizedPres DP n) n (W.market DP) (W.quoteAt DP)
      (history_eq_quote_cast DP E) x).symm
  -- the market maker's contract at the cube point `x`
  have hmaker : ((realizedAggregate DP E).strat n).value (W.market DP) (fun φ => (x φ : ℝ)) ≤
      (marketMakerError n : ℝ) := by
    have h := history_eq_marketMakerHistory DP E
    show ((realizedAggregate DP E).strat n).value (history DP E) (fun φ => (x φ : ℝ)) ≤ _
    rw [h]
    exact marketMaker_day_value_le_cube _ n _ hxR
  -- the ordinary aggregate's bound at `x`
  have hfirm : -(A : ℝ) ≤ ((realizedFirm DP E).strat n).value (W.market DP) (fun φ => (x φ : ℝ)) := by
    have h := Strategy.abs_value_le ((realizedFirm DP E).strat n) (W.market DP)
      (history_range DP E) _ hxR
    have hAeq : ((realizedFirm DP E).strat n).absBound = A := by
      rw [hA, WarrantSchedule.ordAt, Strategy.tradeListAbsBound_strategy]
    rw [hAeq] at h
    exact (abs_le.mp h).1
  have hsplit := realizedAggregate_value DP E n (W.market DP) (fun φ => (x φ : ℝ))
  have hboundR : ((∑ i ∈ (W.realizedPres DP n).rowIndex,
      (W.realizedPres DP n).intensities i * (W.realizedPres DP n).rowViolation i (W.quoteAt DP n) ^ 2 : ℚ) : ℝ) ≤
      (marketMakerError n : ℝ) + A := by
    have h1 : ((∑ i ∈ (W.realizedPres DP n).rowIndex,
        (W.realizedPres DP n).intensities i * (W.realizedPres DP n).rowViolation i (W.quoteAt DP n) ^ 2 : ℚ) : ℝ) ≤
        ((pair (W.realizedPres DP n).coords ((W.realizedPres DP n).compiledPosition (W.quoteAt DP n))
          (fun φ => x φ - W.quoteAt DP n φ) : ℚ) : ℝ) := by exact_mod_cast hsq
    rw [hval] at h1
    linarith
  have hbound : ∑ i ∈ (W.realizedPres DP n).rowIndex,
      (W.realizedPres DP n).intensities i * (W.realizedPres DP n).rowViolation i (W.quoteAt DP n) ^ 2 ≤ marketMakerError n + A := by
    exact_mod_cast hboundR
  refine rowViolation_le_of_intensity_ge (W.realizedPres DP n) n (W.quoteAt DP) (marketMakerError n) A (W.tol n)
    (W.tol_pos n) (by linarith) hbound i ?_
  have hint : (W.realizedPres DP n).intensities i = W.realizedκ DP n :=
    bundlePres_intensity _ _ _ _ _ _ i
  rw [hint]
  unfold WarrantSchedule.realizedκ WarrantSchedule.κ calibratedIntensity resistance
  exact le_rfl

/-- **Every row of the day's bundle conforms at the displayed price**: its seed-row excess at
the pulled-back price is at most the tolerance. -/
theorem excess_le_tol (n : ℕ) (y : Fin d → ℚ) (hy : (W.bundle n).Region y) {c : CitedRow (Cite d) d}
    (hc : c ∈ W.bundle n) : excess c.row (W.priceVec DP n) ≤ W.tol n := by
  have hmem : toForceRow W.ι (W.realizedκ DP n) (W.realizedκ_pos DP n).le c.row ∈
      (W.realizedPres DP n).rows :=
    (W.mem_realizedPres_rows DP).2 ⟨c, hc, rfl⟩
  obtain ⟨i, hi⟩ := List.get_of_mem hmem
  have hviol := W.rowViolation_le_tol DP n y hy i
  simp only [Presentation.rowViolation, Presentation.normals, Presentation.rhss,
    Presentation.rowAt] at hviol
  rw [hi, violation_toForceRow _ _ _ _ (W.mem_realizedPres_coords DP n)] at hviol
  exact le_trans (le_max_right _ _) hviol

/-- Cube faces conform at every displayed price, exactly. -/
theorem excess_cube_le (n : ℕ) {r : Row d} (hr : (∃ j, r = cubeUpper j) ∨ ∃ j, r = cubeLower j) :
    excess r (W.priceVec DP n) ≤ 0 := by
  rcases hr with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp only [excess, cubeUpper, WarrantSchedule.priceVec, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith [(W.quoteAt_mem_Icc DP n (W.ι j)).2]
  · simp only [excess, cubeLower, WarrantSchedule.priceVec, ite_mul, neg_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith [(W.quoteAt_mem_Icc DP n (W.ι j)).1]

/-- **An admitted row conforms**: a row cited into the day's bundle, or a cube face, has
excess at most the tolerance at the displayed price. -/
theorem excess_le_tol_of_admitted (n : ℕ) (y : Fin d → ℚ) (hy : (W.bundle n).Region y)
    {q : Cite d} {r : Row d} (hadm : VerdictCert.RowAdmitted (W.bundle n) q r) :
    excess r (W.priceVec DP n) ≤ W.tol n := by
  rcases hadm with h | h
  · exact W.excess_le_tol DP n y hy (c := ⟨q, r⟩) h
  · exact le_trans (W.excess_cube_le DP n h) (W.tol_pos n).le

end WarrantSchedule

/-! ## 3. Certificates transport conformance -/

/-- **A functional certificate**: nonnegative multipliers on rows whose weighted normals sum
to the functional `ℓ`.  `BoundCert d m φ s` is the case `ℓ = s · e_φ`. -/
structure FunctionalCert (d m : ℕ) (ℓ : Fin d → ℚ) where
  mult : Fin m → ℚ
  row : Fin m → Row d
  mult_nonneg : ∀ i, 0 ≤ mult i
  coeff_sum : ∀ j, ∑ i, mult i * (row i).a j = ℓ j

namespace FunctionalCert

variable {m : ℕ} {ℓ : Fin d → ℚ} (c : FunctionalCert d m ℓ)

/-- The value the certificate certifies: the weighted right-hand sides. -/
def value : ℚ := ∑ i, c.mult i * (c.row i).b

/-- The certificate's **mass**: the multiplier sum, the Lipschitz constant of the certified
bound in the rows' excesses. -/
def mass : ℚ := ∑ i, c.mult i

lemma mass_nonneg : 0 ≤ c.mass := Finset.sum_nonneg fun i _ => c.mult_nonneg i

/-- The functional at a point, through the rows. -/
lemma apply_eq (p : Fin d → ℚ) :
    ∑ j, ℓ j * p j = ∑ i, c.mult i * ∑ j, (c.row i).a j * p j := by
  calc ∑ j, ℓ j * p j = ∑ j, (∑ i, c.mult i * (c.row i).a j) * p j := by
        refine Finset.sum_congr rfl fun j _ => ?_; rw [c.coeff_sum j]
    _ = ∑ j, ∑ i, c.mult i * (c.row i).a j * p j := by
        refine Finset.sum_congr rfl fun j _ => ?_; rw [Finset.sum_mul]
    _ = ∑ i, ∑ j, c.mult i * (c.row i).a j * p j := Finset.sum_comm
    _ = ∑ i, c.mult i * ∑ j, (c.row i).a j * p j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_; ring

/-- **Transport.**  Where every positively weighted row's excess is at most `δ`, the
functional is at most `value + mass · δ`. -/
theorem le_of_excess (p : Fin d → ℚ) (δ : ℚ)
    (hex : ∀ i, 0 < c.mult i → excess (c.row i) p ≤ δ) :
    ∑ j, ℓ j * p j ≤ c.value + c.mass * δ := by
  rw [c.apply_eq]
  have h2 : ∀ i, c.mult i * ∑ j, (c.row i).a j * p j ≤ c.mult i * ((c.row i).b + δ) := by
    intro i
    rcases (c.mult_nonneg i).lt_or_eq with hpos | hzero
    · have := hex i hpos
      unfold excess at this
      exact mul_le_mul_of_nonneg_left (by linarith) hpos.le
    · rw [← hzero]; simp
  calc ∑ i, c.mult i * ∑ j, (c.row i).a j * p j
      ≤ ∑ i, c.mult i * ((c.row i).b + δ) := Finset.sum_le_sum fun i _ => h2 i
    _ = c.value + c.mass * δ := by
        unfold value mass
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_; ring

/-- Soundness at a point satisfying the positively weighted rows: the transport at `δ = 0`. -/
theorem sound (p : Fin d → ℚ) (hx : ∀ i, 0 < c.mult i → (c.row i).Sat p) :
    ∑ j, ℓ j * p j ≤ c.value := by
  have := c.le_of_excess p 0 fun i hi => excess_nonpos_of_sat (hx i hi)
  simpa using this

end FunctionalCert

/-- A bound certificate is a functional certificate for `s · e_φ`. -/
def _root_.Workspace.Normativity.Contrib.SeedStatics.BoundCert.toFunctional {m : ℕ} {φ : Fin d}
    {s : ℚ} (c : BoundCert d m φ s) :
    FunctionalCert d m (fun j => if j = φ then s else 0) :=
  ⟨c.mult, c.row, c.mult_nonneg, c.coeff_sum⟩

/-- The mass of a bound certificate. -/
def _root_.Workspace.Normativity.Contrib.SeedStatics.BoundCert.mass {m : ℕ} {φ : Fin d} {s : ℚ}
    (c : BoundCert d m φ s) : ℚ := ∑ i, c.mult i

/-- **Transport of a bound certificate**: `s · p φ ≤ value + mass · δ` where every
positively weighted row's excess is at most `δ`. -/
theorem _root_.Workspace.Normativity.Contrib.SeedStatics.BoundCert.transport {m : ℕ} {φ : Fin d}
    {s : ℚ} (c : BoundCert d m φ s) (p : Fin d → ℚ)
    (δ : ℚ) (hex : ∀ i, 0 < c.mult i → excess (c.row i) p ≤ δ) :
    s * p φ ≤ c.value + c.mass * δ := by
  have h := c.toFunctional.le_of_excess p δ hex
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  exact h

namespace WarrantSchedule

variable (W : WarrantSchedule d) (DP : DeductiveProcess)

/-- **A supported verdict's bracket holds at the displayed price**, widened by the
certificates' masses times the tolerance: for a verdict `Supported` on grounds whose settled
bundle is the day's compiled bundle, the displayed price of the coordinate lies in
`[−lo.value − lo.mass · tol, hi.value + hi.mass · tol]`.  Semantic entitlement (the licence)
and operative force (the enforcer) meet here. -/
theorem bracket_at_market (n : ℕ) (y : Fin d → ℚ) (hy : (W.bundle n).Region y)
    {G : Grounds d} {st : DocketState} {F : Settlement d} (hB : W.bundle n = G.settledBundle st F)
    {m m' : ℕ} {φ : Fin d} {v : ℚ} {c : VerdictCert d m m' φ} (hsupp : Supported G st F φ v c) :
    -c.lo.value - c.lo.mass * W.tol n ≤ W.priceVec DP n φ ∧
      W.priceVec DP n φ ≤ c.hi.value + c.hi.mass * W.tol n := by
  obtain ⟨⟨hlo, hhi⟩, -⟩ := hsupp
  rw [← hB] at hlo hhi
  constructor
  · have := c.lo.transport (W.priceVec DP n) (W.tol n) fun i hi =>
      W.excess_le_tol_of_admitted DP n y hy (hlo i hi)
    linarith
  · have := c.hi.transport (W.priceVec DP n) (W.tol n) fun i hi =>
      W.excess_le_tol_of_admitted DP n y hy (hhi i hi)
    linarith

/-- **A functional certificate cited into the day's bundle holds at the displayed price**
within its mass times the tolerance. -/
theorem functional_at_market (n : ℕ) (y : Fin d → ℚ) (hy : (W.bundle n).Region y) {m : ℕ}
    {ℓ : Fin d → ℚ} (c : FunctionalCert d m ℓ) (cites : Fin m → Cite d)
    (hcites : ∀ i, 0 < c.mult i → VerdictCert.RowAdmitted (W.bundle n) (cites i) (c.row i)) :
    ∑ j, ℓ j * W.priceVec DP n j ≤ c.value + c.mass * W.tol n :=
  c.le_of_excess _ _ fun i hi => W.excess_le_tol_of_admitted DP n y hy (hcites i hi)

end WarrantSchedule

/-! ## 4. The enforcer is effective data

`EnforcedCompiler` discharges the augmented market's computability from one hypothesis: the
enforcer's trade map is primitive recursive in the date, the stage and the ordinary trade
list.  For the warrant enforcer the trade map is a fixed syntax tree in the date `n` and the
intensity `κ` once the day's bundle is fixed (`tradesOf`), and a schedule whose bundle runs
through finitely many phases (`stepBundle`) has a primitive recursive trade map
(`WarrantSchedule.computation`).  Everything here is plumbing. -/

section Primrec

open Workspace.Normativity.Contrib.ProjectionPrimrec

/-- The warrant enforcer's day-`n` trades on a bundle at intensity `κ`, as a term in `n` and
`κ` with the bundle, the fragment and the coordinates fixed. -/
def tradesOf (ι : Fin d → Sentence) (coords : List Sentence) (B : Bundle (Cite d) d) (n : ℕ)
    (κ : ℚ) : List (EF × Sentence) :=
  coords.map fun φ =>
    (ROIBudget.sumFeatures (B.map fun c =>
      EF.mul (EF.const (κ * ∑ j, if ι j = φ then -c.row.a j else 0))
        (EF.max (EF.const 0) (EF.add (EF.const (-c.row.b))
          (EF.neg (ROIBudget.sumFeatures (coords.map fun ψ =>
            EF.mul (EF.const (∑ j, if ι j = ψ then -c.row.a j else 0)) (EF.price ψ n))))))), φ)

lemma ofFn_get_map {α β : Type*} (l : List α) (g : α → β) :
    (List.ofFn fun i : Fin l.length => g (l.get i)) = l.map g := by
  apply List.ext_get
  · simp
  · intro i h1 h2
    simp

/-- The term is the enforcement strategy's trade list. -/
theorem tradesOf_eq (ι : Fin d → Sentence) (coords : List Sentence) (hnodup : coords.Nodup)
    (B : Bundle (Cite d) d) (κ : ℚ) (hκ : 0 ≤ κ) (n : ℕ) :
    tradesOf ι coords B n κ = (enforcementStrategy (bundlePres ι coords hnodup B κ hκ) n).trades := by
  unfold tradesOf enforcementStrategy coefficientFeature
  simp only [bundlePres_coordList]
  refine List.map_congr_left fun φ _ => ?_
  congr 2
  change List.map _ B =
    List.ofFn fun i : Fin (bundlePres ι coords hnodup B κ hκ).rows.length =>
      (fun r : Row => EF.mul (EF.const (r.intensity * r.coeff φ))
        (violationFeature (bundlePres ι coords hnodup B κ hκ) r n))
        ((bundlePres ι coords hnodup B κ hκ).rows.get i)
  refine Eq.trans ?_ (ofFn_get_map (bundlePres ι coords hnodup B κ hκ).rows
    (fun r : Row => EF.mul (EF.const (r.intensity * r.coeff φ))
      (violationFeature (bundlePres ι coords hnodup B κ hκ) r n))).symm
  rw [bundlePres_rows, List.map_map]
  refine List.map_congr_left fun c _ => ?_
  simp only [Function.comp, violationFeature, priceCombo, bundlePres_coordList, toForceRow]

lemma primrec_map_const {α β γ : Type*} [Primcodable β] [Primcodable γ] (l : List α)
    (f : β → α → γ) (hf : ∀ a ∈ l, Primrec fun x => f x a) :
    Primrec fun x => l.map (f x) := by
  induction l with
  | nil => exact (Primrec.const []).of_eq fun _ => rfl
  | cons a l ih =>
      have h := Primrec.list_cons.comp (hf a (List.mem_cons_self ..))
        (ih fun b hb => hf b (List.mem_cons_of_mem a hb))
      exact h.of_eq fun x => rfl

/-- The day's trades are primitive recursive in the date and the intensity, for a fixed
bundle. -/
theorem tradesOf_primrec (ι : Fin d → Sentence) (coords : List Sentence) (B : Bundle (Cite d) d) :
    Primrec fun p : ℕ × ℚ => tradesOf ι coords B p.1 p.2 := by
  unfold tradesOf
  refine primrec_map_const coords _ fun φ _ => ?_
  refine Primrec.pair ?_ (Primrec.const φ)
  refine sumFeatures_primrec.comp ?_
  refine primrec_map_const B _ fun c _ => ?_
  refine efMul_primrec.comp ?_ ?_
  · exact efConst_primrec.comp (ratMul_prim.comp Primrec.snd (Primrec.const _))
  · refine efMax_primrec.comp (Primrec.const _) ?_
    refine efAdd_primrec.comp (Primrec.const _) ?_
    refine efNeg_primrec.comp (sumFeatures_primrec.comp ?_)
    refine primrec_map_const coords _ fun ψ _ => ?_
    exact efMul_primrec.comp (Primrec.const _) (efPrice_primrec.comp (Primrec.const ψ) Primrec.fst)

/-- A bundle schedule through finitely many phases: `B` before the first threshold, the next
bundle before the next, and the default from the last threshold on. -/
def stepBundle (dflt : Bundle (Cite d) d) : List (ℕ × Bundle (Cite d) d) → ℕ → Bundle (Cite d) d
  | [], _ => dflt
  | (k, B) :: rest, n => if n < k then B else stepBundle dflt rest n

theorem tradesOf_stepBundle_primrec (ι : Fin d → Sentence) (coords : List Sentence)
    (dflt : Bundle (Cite d) d) (phases : List (ℕ × Bundle (Cite d) d)) :
    Primrec fun p : ℕ × ℚ => tradesOf ι coords (stepBundle dflt phases p.1) p.1 p.2 := by
  induction phases with
  | nil => exact tradesOf_primrec ι coords dflt
  | cons kB rest ih =>
      obtain ⟨k, B⟩ := kB
      have hcond : PrimrecPred fun p : ℕ × ℚ => p.1 < k :=
        Primrec.nat_lt.comp Primrec.fst (Primrec.const k)
      have h := Primrec.ite hcond (tradesOf_primrec ι coords B) ih
      exact h.of_eq fun p => by
        simp only [stepBundle]
        split_ifs <;> rfl

/-- **The warrant enforcer is effective data** when its bundle schedule runs through finitely
many phases and its tolerance schedule is primitive recursive. -/
theorem WarrantSchedule.computation (W : WarrantSchedule d) (dflt : Bundle (Cite d) d)
    (phases : List (ℕ × Bundle (Cite d) d)) (hb : ∀ n, W.bundle n = stepBundle dflt phases n)
    (htol : Primrec W.tol) : EnforcedCompiler.EffectiveEnforcerComputation W.enforcer := by
  refine ⟨?_⟩
  have hn : Primrec fun z : (ℕ × Finset Sentence) × List (EF × Sentence) => z.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hκ : Primrec fun z : (ℕ × Finset Sentence) × List (EF × Sentence) => W.κ z.1.1 z.2 := by
    have := calibratedIntensity_primrec.comp
      ((hn.pair (tradeListAbsBound_primrec.comp Primrec.snd)).pair (htol.comp hn))
    exact this.of_eq fun z => rfl
  have h := (tradesOf_stepBundle_primrec W.ι W.coords dflt phases).comp (hn.pair hκ)
  refine h.of_eq fun z => ?_
  show tradesOf W.ι W.coords (stepBundle dflt phases z.1.1) z.1.1 (W.κ z.1.1 z.2) =
    (enforcementStrategy (W.presAt z.1.1 z.2) z.1.1).trades
  rw [WarrantSchedule.presAt, ← hb, tradesOf_eq]

end Primrec

/-! ## 5. Nonvacuity

A one-coordinate schedule with the empty bundle at every date: its enforcer trades nothing,
its account's net worth is `0`, and the transport theorem is inhabited by the cube face. -/

namespace Witness

/-- The one-sentence fragment. -/
def ι : Fin 1 → Sentence := fun _ => .atom 0

def schedule : WarrantSchedule 1 where
  ι := ι
  inj := fun _ _ _ => Subsingleton.elim _ _
  coords := [.atom 0]
  nodup := List.nodup_singleton _
  mem := fun _ => List.mem_singleton.2 rfl
  bundle := fun _ => []
  tol := fun _ => 1
  tol_pos := fun _ => one_pos

/-- The empty bundle's presentation has no rows, so the enforcer's day value is zero. -/
theorem day_value_zero (DP : DeductiveProcess) (n : ℕ) (v : PCWorld) :
    ((realizedEnforcer DP (schedule.enforcer.adaptive DP)).strat n).value
      (schedule.market DP) v.payout = 0 :=
  (schedule.account DP).day_value_eq_zero_of_rows_nil n rfl v

/-- The cube face certifies `p 0 ≤ 1` with mass `1`, so the transport reads `p 0 ≤ 1 + δ`. -/
def faceCert : BoundCert 1 1 0 1 where
  mult := fun _ => 1
  row := fun _ => cubeUpper 0
  mult_nonneg := fun _ => zero_le_one
  coeff_sum := fun j => by simp [cubeUpper]

theorem faceCert_transport (p : Fin 1 → ℚ) (hp : p 0 ≤ 1) :
    1 * p 0 ≤ faceCert.value + faceCert.mass * 0 :=
  faceCert.transport p 0 fun _ _ => by simp [excess, cubeUpper, faceCert]; linarith

end Witness

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.WarrantForce.bundlePres
#print axioms Workspace.Normativity.Contrib.WarrantForce.bundlePres_rows
#print axioms Workspace.Normativity.Contrib.WarrantForce.bundlePres_coordList
#print axioms Workspace.Normativity.Contrib.WarrantForce.mem_bundlePres_rows
#print axioms Workspace.Normativity.Contrib.WarrantForce.bundlePres_intensity
#print axioms Workspace.Normativity.Contrib.WarrantForce.mem_coords_of_mem
#print axioms Workspace.Normativity.Contrib.WarrantForce.violation_toForceRow
#print axioms Workspace.Normativity.Contrib.WarrantForce.seedGap
#print axioms Workspace.Normativity.Contrib.WarrantForce.rowGap_toForceRow
#print axioms Workspace.Normativity.Contrib.WarrantForce.excess
#print axioms Workspace.Normativity.Contrib.WarrantForce.excess_nonpos_of_sat
#print axioms Workspace.Normativity.Contrib.WarrantForce.seedGap_specialize
#print axioms Workspace.Normativity.Contrib.WarrantForce.seedGap_pinRow
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule
#print axioms Workspace.Normativity.Contrib.WarrantForce.tradeListAbsBound_nonneg
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.κ
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.κ_pos
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.presAt
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.enforcer
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.market
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.quoteAt
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.market_eq_quote_cast
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.ordAt
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.realizedPres
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.realizedκ
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.realizedκ_pos
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.realizedEnforcer_strat
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.mem_realizedPres_rows
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.mem_realizedPres_coords
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.priceVec
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.quoteAt_mem_Icc
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.account
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.dom_of_seed
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.liability
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.liability_reopened
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.netWorth_nonneg_of_inclusive
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.isLogicalInductor
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.exists_extension
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.rowViolation_le_tol
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.excess_le_tol
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.excess_cube_le
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.excess_le_tol_of_admitted
#print axioms Workspace.Normativity.Contrib.WarrantForce.FunctionalCert
#print axioms Workspace.Normativity.Contrib.WarrantForce.FunctionalCert.value
#print axioms Workspace.Normativity.Contrib.WarrantForce.FunctionalCert.mass
#print axioms Workspace.Normativity.Contrib.WarrantForce.FunctionalCert.mass_nonneg
#print axioms Workspace.Normativity.Contrib.WarrantForce.FunctionalCert.apply_eq
#print axioms Workspace.Normativity.Contrib.WarrantForce.FunctionalCert.le_of_excess
#print axioms Workspace.Normativity.Contrib.WarrantForce.FunctionalCert.sound
#print axioms Workspace.Normativity.Contrib.SeedStatics.BoundCert.toFunctional
#print axioms Workspace.Normativity.Contrib.SeedStatics.BoundCert.mass
#print axioms Workspace.Normativity.Contrib.SeedStatics.BoundCert.transport
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.bracket_at_market
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.functional_at_market
#print axioms Workspace.Normativity.Contrib.WarrantForce.tradesOf
#print axioms Workspace.Normativity.Contrib.WarrantForce.ofFn_get_map
#print axioms Workspace.Normativity.Contrib.WarrantForce.tradesOf_eq
#print axioms Workspace.Normativity.Contrib.WarrantForce.primrec_map_const
#print axioms Workspace.Normativity.Contrib.WarrantForce.tradesOf_primrec
#print axioms Workspace.Normativity.Contrib.WarrantForce.stepBundle
#print axioms Workspace.Normativity.Contrib.WarrantForce.tradesOf_stepBundle_primrec
#print axioms Workspace.Normativity.Contrib.WarrantForce.WarrantSchedule.computation
#print axioms Workspace.Normativity.Contrib.WarrantForce.Witness.ι
#print axioms Workspace.Normativity.Contrib.WarrantForce.Witness.schedule
#print axioms Workspace.Normativity.Contrib.WarrantForce.Witness.day_value_zero
#print axioms Workspace.Normativity.Contrib.WarrantForce.Witness.faceCert
#print axioms Workspace.Normativity.Contrib.WarrantForce.Witness.faceCert_transport

end Workspace.Normativity.Contrib.WarrantForce