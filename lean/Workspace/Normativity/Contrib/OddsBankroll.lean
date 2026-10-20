/-
# The odds bankroll on an abstract enforcement account

Round `projects/normativity/rounds/2026-10-22-normative-inductor-integration/`.

The general affordability interface, separated from its discharges.  An **account**
(`Account`) is a trader whose day-`n` strategy is the force layer's compiled position on the
day's presentation (`EnforcementStrategy.enforcementStrategy`), read against a history with
exact rational quotes, assessed at a family of live worlds, and **capped**: its cumulative
value at a live world is below `cap`.  Both markets this repository builds supply such an
account with `cap = 3` — the market maker's constant `1` plus the trading firm's floor `2` —
the assessment market of `EnforcementPreservation` (`WarrantEntitlement.assessmentAccount`)
and the deductive market of `DeductiveEnforcement` (`WarrantForce.deductiveAccount`).

Theorems, on an account `A`:

* `day_value_eq`, `day_value_ge` — the day's value at a world is the units-weighted signed
  row gaps plus the intensity-weighted squared violations.
* `netWorth_ge_neg_odds` — **the odds bankroll**: if at date `n` a live world `v'` clears
  every enforced row of every date `t ≤ n` with a surplus dominating, by the factor `ρ`, the
  deficit of the world `w` on that row, then `−ρ·cap ≤ netWorth w n`.  Intensity, tolerance,
  the number of rows and the number of dates do not appear.
* `netWorth_ge_neg_odds_reopened` — **across one reopening**: a slack world `v₀` before date
  `m` and a slack world `v'` from `m` on give `−ρ·cap·(2 + ρ)`.
* `netWorth_nonneg_of_inclusive` — rows every assessed world clears cost nothing.
* `liability_of_odds` — the shape the conditional Normative Inductor theorems consume.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.EnforcementStrategy
import Workspace.Normativity.Contrib.AssessmentProcess

namespace Workspace.Normativity.Contrib.OddsBankroll

open LogicalInduction
open Workspace.Normativity.Contrib.AssessmentProcess
open Workspace.Normativity.Contrib.EnforcementStrategy
open Workspace.Normativity.Contrib.TraderizedEnforcement

/-- **An enforcement account**: a trader whose day-`n` strategy is the compiled position on
the day's presentation, read against a history with exact rational quotes, assessed at the
live worlds, and capped there. -/
structure Account where
  /-- The market history. -/
  P : History
  /-- Its exact rational quotes. -/
  Q : ℕ → Sentence → ℚ
  hQ : ∀ day φ, P day φ = (Q day φ : ℝ)
  /-- The worlds the trader is assessed in at each date. -/
  Live : ℕ → PCWorld → Prop
  /-- The enforcement trader. -/
  enf : Trader
  /-- The presentation it enforces at each date. -/
  pres : ℕ → Presentation
  strat_eq : ∀ n, enf.strat n = enforcementStrategy (pres n) n
  /-- The market's capital: the trader's cumulative value at a live world is below it. -/
  cap : ℝ
  netWorth_lt_cap : ∀ n v, Live n v → enf.netWorth P v n < cap

/-- **The signed row gap** at a world: positive is a surplus (the world clears the row),
negative is a deficit (the row excludes the world). -/
noncomputable def rowGap (coords : Finset Sentence) (r : Row) (v : PCWorld) : ℚ :=
  pair coords r.coeff (ratPayout v) - r.rhs

/-- The units the enforcer holds on a row at a price: intensity times violation. -/
def rowUnits (pres : Presentation) (i : Fin pres.rows.length) (p : Sentence → ℚ) : ℚ :=
  pres.intensities i * pres.rowViolation i p

lemma rowUnits_nonneg (pres : Presentation) (i : Fin pres.rows.length) (p : Sentence → ℚ) :
    0 ≤ rowUnits pres i p :=
  mul_nonneg (pres.rowAt i).intensity_nonneg (violation_nonneg _ _ _ _)

/-- **Frozen tail**: a trader that trades nothing after date `m` has at every later date the
net worth it had at `m`. -/
theorem netWorth_eq_of_tail_zero (Tr : Trader) (P : History) (v : PCWorld) {m n : ℕ}
    (hmn : m ≤ n) (hz : ∀ t, m < t → (Tr.strat t).value P v.payout = 0) :
    Tr.netWorth P v n = Tr.netWorth P v m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Nat.add_succ, Trader.netWorth, Finset.sum_range_succ, ← Trader.netWorth,
        ih (by omega), hz _ (by omega), add_zero]

namespace Account

variable (A : Account)

/-- **The day's value, resolved**: the units-weighted signed gaps plus the
intensity-weighted squared violations. -/
theorem day_value_eq (n : ℕ) (v : PCWorld) :
    (A.enf.strat n).value A.P v.payout =
      (((∑ i, rowUnits (A.pres n) i (A.Q n) * rowGap (A.pres n).coords ((A.pres n).rowAt i) v) +
          ∑ i, (A.pres n).intensities i * (A.pres n).rowViolation i (A.Q n) ^ 2 : ℚ) : ℝ) := by
  rw [A.strat_eq]
  have hpay : (fun φ => ((ratPayout v φ : ℚ) : ℝ)) = v.payout := by
    funext φ; exact (payout_eq_ratPayout v φ).symm
  have hval := value_enforcementStrategy (A.pres n) n A.P A.Q A.hQ (ratPayout v)
  rw [hpay] at hval
  rw [hval]
  congr 1
  rw [Presentation.compiledPosition, pair_position, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pair_sub]
  have hgap := violation_mul_gap (A.pres n).coords ((A.pres n).normals i) ((A.pres n).rhss i)
    (A.Q n)
  simp only [rowUnits, rowGap, Presentation.rowViolation, Presentation.normals,
    Presentation.rhss] at hgap ⊢
  linear_combination ((A.pres n).intensities i) * hgap

/-- At a world, the day's value is at least the units-weighted signed gap. -/
theorem day_value_ge (n : ℕ) (v : PCWorld) :
    ((∑ i, rowUnits (A.pres n) i (A.Q n) * rowGap (A.pres n).coords ((A.pres n).rowAt i) v :
        ℚ) : ℝ) ≤ (A.enf.strat n).value A.P v.payout := by
  rw [A.day_value_eq]
  have : 0 ≤ ∑ i, (A.pres n).intensities i * (A.pres n).rowViolation i (A.Q n) ^ 2 :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg ((A.pres n).rowAt i).intensity_nonneg (sq_nonneg _)
  exact_mod_cast le_add_of_nonneg_right this

/-- The units-weighted signed gap of one date at a world. -/
noncomputable def dayGap (v : PCWorld) (t : ℕ) : ℚ :=
  ∑ i, rowUnits (A.pres t) i (A.Q t) * rowGap (A.pres t).coords ((A.pres t).rowAt i) v

/-- The slack mass through date `n`: the units-weighted surplus at a world. -/
noncomputable def slackMass (v' : PCWorld) (n : ℕ) : ℚ :=
  ∑ t ∈ Finset.range (n + 1), A.dayGap v' t

lemma slackMass_eq (v : PCWorld) (n : ℕ) :
    A.slackMass v n = ∑ t ∈ Finset.range (n + 1), A.dayGap v t := rfl

/-- A world's net worth dominates its slack mass. -/
theorem slackMass_le_netWorth (v' : PCWorld) (n : ℕ) :
    ((A.slackMass v' n : ℚ) : ℝ) ≤ A.enf.netWorth A.P v' n := by
  unfold slackMass Trader.netWorth
  rw [Rat.cast_sum]
  exact Finset.sum_le_sum fun t _ => A.day_value_ge t v'

/-- One date's domination: deficits at `w` dominated by `ρ` times the surpluses at `v'`. -/
theorem dayGap_dominated (ρ : ℚ) (t : ℕ) (w v' : PCWorld)
    (hgap : ∀ r ∈ (A.pres t).rows,
      -(rowGap (A.pres t).coords r w) ≤ ρ * rowGap (A.pres t).coords r v') :
    -(ρ * A.dayGap v' t) ≤ A.dayGap w t := by
  unfold dayGap
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hu := rowUnits_nonneg (A.pres t) i (A.Q t)
  have hg := hgap ((A.pres t).rowAt i) (List.get_mem _ _)
  nlinarith

/-- The slack mass at a live world is below the capital. -/
theorem slackMass_lt_cap (n : ℕ) (v' : PCWorld) (hv' : A.Live n v') :
    ((A.slackMass v' n : ℚ) : ℝ) < A.cap :=
  lt_of_le_of_lt (A.slackMass_le_netWorth v' n) (A.netWorth_lt_cap n v' hv')

/-- **The odds bankroll.**  If at date `n` a live world `v'` clears every enforced row of
every date `t ≤ n` with a surplus dominating, by the factor `ρ`, the deficit of the world
`w` on that row, then the account's net worth at `w` is at least `−ρ·cap`.  Intensity,
tolerance, the number of rows and the number of dates do not appear. -/
theorem netWorth_ge_neg_odds (ρ : ℚ) (hρ : 0 ≤ ρ) (n : ℕ) (v' : PCWorld) (hv' : A.Live n v')
    (w : PCWorld)
    (hgap : ∀ t ≤ n, ∀ r ∈ (A.pres t).rows,
      -(rowGap (A.pres t).coords r w) ≤ ρ * rowGap (A.pres t).coords r v') :
    -(A.cap * (ρ : ℝ)) ≤ A.enf.netWorth A.P w n := by
  have hS := A.slackMass_lt_cap n v' hv'
  have hday : ∀ t ≤ n, -((ρ : ℝ) * ((A.dayGap v' t : ℚ) : ℝ)) ≤
      (A.enf.strat t).value A.P w.payout := by
    intro t htn
    refine le_trans ?_ (A.day_value_ge t w)
    have hq := A.dayGap_dominated ρ t w v' (hgap t htn)
    have hq' : ((-(ρ * A.dayGap v' t) : ℚ) : ℝ) ≤ ((A.dayGap w t : ℚ) : ℝ) := by
      exact_mod_cast hq
    push_cast at hq'
    exact hq'
  have hsum : ∑ t ∈ Finset.range (n + 1), -((ρ : ℝ) * ((A.dayGap v' t : ℚ) : ℝ)) =
      -((ρ : ℝ) * ((A.slackMass v' n : ℚ) : ℝ)) := by
    unfold slackMass
    rw [Rat.cast_sum, Finset.mul_sum, Finset.sum_neg_distrib]
  have hw : -((ρ : ℝ) * ((A.slackMass v' n : ℚ) : ℝ)) ≤ A.enf.netWorth A.P w n := by
    unfold Trader.netWorth
    rw [← hsum]
    exact Finset.sum_le_sum fun t ht => hday t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))
  have hρS : (ρ : ℝ) * ((A.slackMass v' n : ℚ) : ℝ) ≤ (ρ : ℝ) * A.cap :=
    mul_le_mul_of_nonneg_left hS.le (by exact_mod_cast hρ)
  linarith

/-- **Liability discharged by the odds bankroll**: a slack live world at every date gives
the `liability` hypothesis of the conditional Normative Inductor theorems with
`B = cap·ρ`. -/
theorem liability_of_odds (ρ : ℚ) (hρ : 0 ≤ ρ)
    (hslack : ∀ n, ∃ v' : PCWorld, A.Live n v' ∧ ∀ w : PCWorld, A.Live n w →
      ∀ t ≤ n, ∀ r ∈ (A.pres t).rows,
        -(rowGap (A.pres t).coords r w) ≤ ρ * rowGap (A.pres t).coords r v') :
    ∀ n (v : PCWorld), A.Live n v → -(A.cap * (ρ : ℝ)) ≤ A.enf.netWorth A.P v n := by
  intro n v hv
  obtain ⟨v', hv', hgap⟩ := hslack n
  exact A.netWorth_ge_neg_odds ρ hρ n v' hv' v (hgap v hv)

/-- **World-inclusive rows cost nothing**: when every row's gap at a world is nonnegative
at every date through `n`, the account's net worth there is nonnegative. -/
theorem netWorth_nonneg_of_inclusive (n : ℕ) (w : PCWorld)
    (hw : ∀ t ≤ n, ∀ r ∈ (A.pres t).rows, 0 ≤ rowGap (A.pres t).coords r w) :
    0 ≤ A.enf.netWorth A.P w n := by
  unfold Trader.netWorth
  refine Finset.sum_nonneg fun t ht => ?_
  have htn : t ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  refine le_trans ?_ (A.day_value_ge t w)
  have : 0 ≤ ∑ i, rowUnits (A.pres t) i (A.Q t) * rowGap (A.pres t).coords ((A.pres t).rowAt i) w :=
    Finset.sum_nonneg fun i _ => mul_nonneg (rowUnits_nonneg _ _ _)
      (hw t htn _ (List.get_mem _ _))
  exact_mod_cast this

/-- A date with no rows trades nothing. -/
theorem day_value_eq_zero_of_rows_nil (t : ℕ) (h : (A.pres t).rows = []) (v : PCWorld) :
    (A.enf.strat t).value A.P v.payout = 0 := by
  rw [A.day_value_eq]
  have hempty : IsEmpty (Fin (A.pres t).rows.length) := by
    rw [h]; exact Fin.isEmpty'
  simp

/-- **The odds bankroll across one reopening.**  Before date `m` a live world `v₀` dominates
every enforced row at the odds (for the bounded world `w` and for the later witness `v'`);
from `m` on a live world `v'` dominates the rows then enforced.  The account's net worth at
`w` is at least `−ρ·cap·(2 + ρ)`: the pre-reopening bankroll `ρ·cap`, plus `ρ` times the
post-reopening slack mass, which the capital bounds by `cap` plus the reopened mass
`ρ·cap`. -/
theorem netWorth_ge_neg_odds_reopened (ρ : ℚ) (hρ : 0 ≤ ρ) {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (v₀ : PCWorld) (hv₀ : A.Live (m - 1) v₀) (v' : PCWorld) (hv' : A.Live n v') (w : PCWorld)
    (hdom₀w : ∀ t < m, ∀ r ∈ (A.pres t).rows,
      -(rowGap (A.pres t).coords r w) ≤ ρ * rowGap (A.pres t).coords r v₀)
    (hdom₀v' : ∀ t < m, ∀ r ∈ (A.pres t).rows,
      -(rowGap (A.pres t).coords r v') ≤ ρ * rowGap (A.pres t).coords r v₀)
    (hdom' : ∀ t, m ≤ t → t ≤ n → ∀ r ∈ (A.pres t).rows,
      -(rowGap (A.pres t).coords r w) ≤ ρ * rowGap (A.pres t).coords r v') :
    -(A.cap * (ρ : ℝ) * (2 + ρ)) ≤ A.enf.netWorth A.P w n := by
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hρR : (0 : ℝ) ≤ ρ := by exact_mod_cast hρ
  -- the prefix through `m − 1`, bounded by the pre-reopening bankroll
  have hpre : -(A.cap * (ρ : ℝ)) ≤ A.enf.netWorth A.P w (m - 1) :=
    A.netWorth_ge_neg_odds ρ hρ (m - 1) v₀ hv₀ w (fun t ht r hr => hdom₀w t (by omega) r hr)
  -- the slack mass of `v₀` through `m − 1` is under the capital
  have hS₀ : ((A.slackMass v₀ (m - 1) : ℚ) : ℝ) < A.cap := A.slackMass_lt_cap (m - 1) v₀ hv₀
  -- the slack mass of `v'` through `m − 1` is bounded below by the reopened mass
  have hSv'pre : -(ρ * A.slackMass v₀ (m - 1)) ≤ A.slackMass v' (m - 1) := by
    rw [slackMass_eq, slackMass_eq, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun t ht => ?_
    have htm : t < m := by have := Finset.mem_range.mp ht; omega
    exact A.dayGap_dominated ρ t v' v₀ (hdom₀v' t htm)
  -- the slack mass of `v'` through `n` is under the capital
  have hSv' : ((A.slackMass v' n : ℚ) : ℝ) < A.cap := A.slackMass_lt_cap n v' hv'
  -- the tail of the slack mass of `v'`
  have htail_eq : ∑ t ∈ Finset.Ico m (n + 1), A.dayGap v' t =
      A.slackMass v' n - A.slackMass v' (m - 1) := by
    rw [slackMass_eq, slackMass_eq, hm1]
    exact Finset.sum_Ico_eq_sub _ (by omega)
  -- the tail of the net worth at `w`
  have hworth : A.enf.netWorth A.P w n =
      A.enf.netWorth A.P w (m - 1) +
        ∑ t ∈ Finset.Ico m (n + 1), (A.enf.strat t).value A.P w.payout := by
    unfold Trader.netWorth
    rw [hm1, Finset.sum_range_add_sum_Ico _ (by omega)]
  have htailw : ((-(ρ * ∑ t ∈ Finset.Ico m (n + 1), A.dayGap v' t) : ℚ) : ℝ) ≤
      ∑ t ∈ Finset.Ico m (n + 1), (A.enf.strat t).value A.P w.payout := by
    have hq : ∀ t ∈ Finset.Ico m (n + 1),
        ((-(ρ * A.dayGap v' t) : ℚ) : ℝ) ≤ (A.enf.strat t).value A.P w.payout := by
      intro t ht
      have hbd := Finset.mem_Ico.mp ht
      refine le_trans ?_ (A.day_value_ge t w)
      exact_mod_cast A.dayGap_dominated ρ t w v' (hdom' t hbd.1 (by omega))
    calc ((-(ρ * ∑ t ∈ Finset.Ico m (n + 1), A.dayGap v' t) : ℚ) : ℝ)
        = ∑ t ∈ Finset.Ico m (n + 1), ((-(ρ * A.dayGap v' t) : ℚ) : ℝ) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
          push_cast
          rfl
      _ ≤ _ := Finset.sum_le_sum hq
  -- the reopened tail, in ℝ
  have htail_le : ((A.slackMass v' n : ℚ) : ℝ) - ((A.slackMass v' (m - 1) : ℚ) : ℝ) ≤
      A.cap + (ρ : ℝ) * A.cap := by
    have h1 : -((ρ : ℝ) * ((A.slackMass v₀ (m - 1) : ℚ) : ℝ)) ≤
        ((A.slackMass v' (m - 1) : ℚ) : ℝ) := by exact_mod_cast hSv'pre
    have h2 : (ρ : ℝ) * ((A.slackMass v₀ (m - 1) : ℚ) : ℝ) ≤ (ρ : ℝ) * A.cap :=
      mul_le_mul_of_nonneg_left hS₀.le hρR
    linarith
  have hcast : -((ρ : ℝ) * (A.cap + (ρ : ℝ) * A.cap)) ≤
      ((-(ρ * ∑ t ∈ Finset.Ico m (n + 1), A.dayGap v' t) : ℚ) : ℝ) := by
    rw [htail_eq]
    push_cast
    have := mul_le_mul_of_nonneg_left htail_le hρR
    linarith
  rw [hworth]
  have hfinal : -(A.cap * (ρ : ℝ) * (2 + ρ)) =
      -(A.cap * (ρ : ℝ)) + -((ρ : ℝ) * (A.cap + (ρ : ℝ) * A.cap)) := by ring
  rw [hfinal]
  exact add_le_add hpre (hcast.trans htailw)

end Account

/-! ## Nonvacuity: a trivial account

The zero presentation at every date on any history with rational quotes, assessed nowhere
live, is an account with cap `1`; its net worth is `0` at every world, which is what the
bankroll says for `ρ = 0`. -/

namespace Witness

/-- The empty presentation. -/
def emptyPres : Presentation := ⟨[], List.nodup_nil, []⟩

/-- An account on the constant market `1/2`, with no live worlds and no rows. -/
noncomputable def account : Account where
  P := fun _ _ => (1/2 : ℝ)
  Q := fun _ _ => 1/2
  hQ := fun _ _ => by norm_num
  Live := fun _ _ => False
  enf := ⟨fun n => enforcementStrategy emptyPres n⟩
  pres := fun _ => emptyPres
  strat_eq := fun _ => rfl
  cap := 1
  netWorth_lt_cap := fun _ _ h => h.elim

theorem account_netWorth (n : ℕ) (w : PCWorld) :
    account.enf.netWorth account.P w n = 0 := by
  unfold Trader.netWorth
  refine Finset.sum_eq_zero fun t _ => ?_
  exact account.day_value_eq_zero_of_rows_nil t rfl w

end Witness

end Workspace.Normativity.Contrib.OddsBankroll

#print axioms Workspace.Normativity.Contrib.OddsBankroll.Account
#print axioms Workspace.Normativity.Contrib.OddsBankroll.rowGap
#print axioms Workspace.Normativity.Contrib.OddsBankroll.rowUnits
#print axioms Workspace.Normativity.Contrib.OddsBankroll.rowUnits_nonneg
#print axioms Workspace.Normativity.Contrib.OddsBankroll.netWorth_eq_of_tail_zero
#print axioms Workspace.Normativity.Contrib.OddsBankroll.Account.day_value_eq
#print axioms Workspace.Normativity.Contrib.OddsBankroll.Account.day_value_ge
#print axioms Workspace.Normativity.Contrib.OddsBankroll.Account.dayGap
#print axioms Workspace.Normativity.Contrib.OddsBankroll.Account.slackMass
#print axioms Workspace.Normativity.Contrib.OddsBankroll.Account.slackMass_eq
#print axioms Workspace.Normativity.Contrib.OddsBankroll.Account.slackMass_le_netWorth
#print axioms Workspace.Normativity.Contrib.OddsBankroll.Account.dayGap_dominated
#print axioms Workspace.Normativity.Contrib.OddsBankroll.Account.slackMass_lt_cap
#print axioms Workspace.Normativity.Contrib.OddsBankroll.Account.netWorth_ge_neg_odds
#print axioms Workspace.Normativity.Contrib.OddsBankroll.Account.liability_of_odds
#print axioms Workspace.Normativity.Contrib.OddsBankroll.Account.netWorth_nonneg_of_inclusive
#print axioms Workspace.Normativity.Contrib.OddsBankroll.Account.day_value_eq_zero_of_rows_nil
#print axioms Workspace.Normativity.Contrib.OddsBankroll.Account.netWorth_ge_neg_odds_reopened
#print axioms Workspace.Normativity.Contrib.OddsBankroll.Witness.emptyPres
#print axioms Workspace.Normativity.Contrib.OddsBankroll.Witness.account
#print axioms Workspace.Normativity.Contrib.OddsBankroll.Witness.account_netWorth
