import Cleanroom.Decision.DpLearnerNr.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# `dp-learner-nr` target 8(a)(d): E1, the provable positive half (static), and the regret row

**E1-static** (`e1_static`): for sequences `p` (the NR3 marginal `P₀_t(incon)`), `eGood` (the
estimate `Ê_t(cross, ¬incon)`) and `eBad` (`Ê_t(cross, incon)`), with
`limsup p < ½` (rendered `∃ p̄ < ½, ∀ᶠ t, p t ≤ p̄`), `eGood → 10` (rendered `∀ δ > 0, ∀ᶠ t,
|eGood t − 10| < δ`) and `eBad = −10` from the rule, the NR3 rule
`cf_t(cross) := (1 − p t)·eGood t + p t·eBad t` is eventually positive — the learner crosses at all
but finitely many rounds. The two limits are **hypotheses**: `eGood → 10` is Conjecture F(i)
(frequency convergence / SLLN, grade (b)), never discharged by assuming `∀ t, eGood t = 10`;
`limsup p < ½` is "not a theorem" (an LI need not converge on a false Σ₁ sentence; grade (b)).
The per-round average of always-cross on the fallible troll is `10(1−2θ)`
(`cfMarginal_trollE_bool`, `Defs.lean`).

**Regret** (`regret_eq`, `regret_unbounded`): in the deterministic-expectation model the stopper
that crosses for `T_L` rounds then stays totals `10(1−2θ)·T_L` against `10(1−2θ)·T` for
always-cross: regret `10(1−2θ)(T − T_L)`, unbounded in `T`. "The non-responsive learner's regret
is `0`" is the identification of that learner with always-cross, not a theorem. The simulation's
`2620`/`17520` are not theorems.
-/

namespace Cleanroom.Decision.DpLearnerNr

open Cleanroom.Found.DpCoreTree Filter Finset

/-- **The NR3 rule's per-round value of crossing**: `cf_t(cross) := (1 − p t)·eGood t + p t·eBad t`,
with `p t` the anonymous marginal's `P₀_t(incon)` and `eGood`, `eBad` the estimated responses.
Source: [[non-responsiveness-learnability]] §5 E1 ("`Ê_t(cross, ¬□⊥) → 10` … `Ê(cross, □⊥) = −10`
from the rule … `cf_t(cross) → 10 − 20p > 0`"); [[dp-learner-nr-mandate]] target 8(a)
Kind: D -/
def nr3Cf (p eGood eBad : ℕ → ℚ) (t : ℕ) : ℚ := (1 - p t) * eGood t + p t * eBad t

/-- **E1-static** (load-bearing 4): an NR3 learner with `limsup P₀_t(incon) < ½`, estimates
`Ê_t(cross, ¬incon) → 10` and `Ê_t(cross, incon) = −10` (from the rule, in `𝓛_exo`) has
`cf_t(cross) > 0 = cf_t(stay)` at all but finitely many rounds, i.e. eventually crosses every
round. The Löb half (the per-round lesion is unprovable) is `conjectureF_v_per_round`
(`Modal.lean`); the LI-level (v) is `li_decided_crosser_no_lesion` (`LeakLI.lean`).
Source: [[non-responsiveness-learnability]] §5 E1 ("Every NR3 learner with `lim sup_t P₀_t(□⊥)
< 1/2` … crosses at all but finitely many rounds"); [[dp-core-2-inventory]] 046; [[dp-core-inventory]]
111; [[dp-learner-nr-mandate]] target 8(a), load-bearing 4
Kind: P (one ε-δ argument with `δ := 5(1−2p̄)` over the two (b) hypotheses; relabelled from C at
audit r1 — the docstring caught up at repair r2)
Fidelity: exact (of the statistical half, as an eventual inequality; "averages `10(1−2θ)`" is
`cfMarginal_trollE_bool`)
Hyps: (b) `hgood`: `Ê_t(cross, ¬incon) → 10` is Conjecture F(i) (frequency convergence on
infinitely-visited cells / SLLN), taken as a hypothesis, never as `∀ t, eGood t = 10`; (b)
`hlimsup`: `limsup P₀_t(incon) < ½` is a hypothesis, "not a theorem" (an LI need not converge on a
false Σ₁ sentence; non-dogmatism gives only `p > 0`); (a) `hbad` is the troll's stated rule, a
sentence of `𝓛_exo`; (a) `0 ≤ p t ≤ 1` -/
theorem e1_static (p eGood eBad : ℕ → ℚ)
    (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1)
    (hlimsup : ∃ pbar : ℚ, pbar < 1 / 2 ∧ ∀ᶠ t in atTop, p t ≤ pbar)
    (hgood : ∀ δ : ℚ, 0 < δ → ∀ᶠ t in atTop, |eGood t - 10| < δ)
    (hbad : ∀ t, eBad t = -10) :
    ∀ᶠ t in atTop, 0 < nr3Cf p eGood eBad t := by
  obtain ⟨pbar, hpbar, hev⟩ := hlimsup
  have hδpos : 0 < 5 * (1 - 2 * pbar) := by linarith
  filter_upwards [hev, hgood _ hδpos] with t ht hgt
  rw [abs_lt] at hgt
  have hp0t := hp0 t
  have hp1t := hp1 t
  have hprod : 0 ≤ (1 - p t) * (eGood t - (10 - 5 * (1 - 2 * pbar))) :=
    mul_nonneg (by linarith) (by linarith [hgt.1])
  have hpδ : 0 ≤ p t * (5 * (1 - 2 * pbar)) := mul_nonneg hp0t hδpos.le
  have h1 : nr3Cf p eGood eBad t
      = (1 - p t) * (10 - 5 * (1 - 2 * pbar))
        + (1 - p t) * (eGood t - (10 - 5 * (1 - 2 * pbar))) - 10 * p t := by
    unfold nr3Cf; rw [hbad]; ring
  rw [h1]
  nlinarith [hprod, hpδ, ht, hpbar]

/-- **The NR3 learner's estimated response table at round `t`**: the troll's table `trollE` with
the stated values replaced by the estimates — `(cross, incon) ↦ Ê_t(cross, incon)`,
`(cross, ¬incon) ↦ Ê_t(cross, ¬incon)`, `stay ↦ 0` (the rule: staying pays `0` in every world).
Source: [[non-responsiveness-learnability]] §5 E1; [[dp-learner-nr-mandate]] target 8(a)
Kind: D -/
def nr3Table (eGood eBad : ℕ → ℚ) (t : ℕ) : Act2 → Bool → ℚ
  | .a, true => eBad t
  | .a, false => eGood t
  | .b, _ => 0

/-- `nr3Cf` is D2 (`cfMarginal`) fed the Bernoulli marginal `p t` and the estimated table, at
`cross`; at `stay` D2 gives `0`. So `e1_static`'s conclusion is a statement about the NR3
learner's act-level decision rule, not only about one expression.
Source: [[dp-learner-nr-mandate]] D2, target 8(a)
Kind: L -/
theorem nr3Cf_eq_cfMarginal (p eGood eBad : ℕ → ℚ) (t : ℕ) (h0 : 0 ≤ p t) (h1 : p t ≤ 1) :
    nr3Cf p eGood eBad t = cfMarginal (boolDistr (p t) h0 h1) (nr3Table eGood eBad t) Act2.a ∧
    cfMarginal (boolDistr (p t) h0 h1) (nr3Table eGood eBad t) Act2.b = 0 := by
  constructor
  · simp [cfMarginal, Fintype.sum_bool, nr3Table, nr3Cf] <;> ring
  · simp [cfMarginal, nr3Table]

/-- **E1-static as a decision**: under E1's hypotheses the NR3 learner's marginal formula
eventually strictly prefers `cross` to `stay` (`cf_t(stay) = 0 < cf_t(cross)`), i.e. the
learner crosses at all but finitely many rounds. (Before audit r1 the stay value was carried as
the stub `0 ≤ 0`; it is now D2's value at `stay`.)
Source: [[non-responsiveness-learnability]] §5 E1 ("crosses at all but finitely many rounds");
[[dp-learner-nr-mandate]] target 8(a)
Kind: L (over `e1_static` and `nr3Cf_eq_cfMarginal`)
Hyps: as `e1_static` -/
theorem e1_crosses (p eGood eBad : ℕ → ℚ)
    (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1)
    (hlimsup : ∃ pbar : ℚ, pbar < 1 / 2 ∧ ∀ᶠ t in atTop, p t ≤ pbar)
    (hgood : ∀ δ : ℚ, 0 < δ → ∀ᶠ t in atTop, |eGood t - 10| < δ)
    (hbad : ∀ t, eBad t = -10) :
    ∀ᶠ t in atTop, cfMarginal (boolDistr (p t) (hp0 t) (hp1 t)) (nr3Table eGood eBad t) Act2.b
      < cfMarginal (boolDistr (p t) (hp0 t) (hp1 t)) (nr3Table eGood eBad t) Act2.a := by
  filter_upwards [e1_static p eGood eBad hp0 hp1 hlimsup hgood hbad] with t ht
  obtain ⟨h1, h2⟩ := nr3Cf_eq_cfMarginal p eGood eBad t (hp0 t) (hp1 t)
  rw [h2, ← h1]; exact ht

/-- **The strict threshold `p̄ < ½` is load-bearing**: at `p ≡ ½` with the estimator at its limit,
`cf_t(cross) = 0` at every `t`, so `e1_static`'s conclusion fails at `p̄ = ½`. A content check
(the theorem is not an artifact of the encoding); adopted from audit r1's `E1Content` probe.
Source: [[dp-learner-nr-audit-r1-adversarial]] §3 item 10; [[STANDARDS]] §3 (non-vacuity)
Kind: L -/
theorem e1_fails_at_half :
    (∀ t, nr3Cf (fun _ => 1 / 2) (fun _ => 10) (fun _ => -10) t = 0) ∧
    ¬ ∀ᶠ t in atTop, 0 < nr3Cf (fun _ => 1 / 2) (fun _ => 10) (fun _ => -10) t := by
  have hz : ∀ t, nr3Cf (fun _ => 1 / 2) (fun _ => 10) (fun _ => -10) t = 0 := by
    intro t; simp [nr3Cf]; norm_num
  refine ⟨hz, ?_⟩
  intro h
  rw [eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  have := hN N le_rfl
  rw [hz] at this
  exact lt_irrefl _ this

/-- The witness marginal sequence: `3/4` for `t < 3` (above `½`), then `1/4` — so the "eventually"
of `limsup p < ½` is exercised (the marginal exceeds `½` finitely often before settling).
Source: none: infrastructure. Kind: D -/
def pW : ℕ → ℚ := fun t => if t < 3 then 3 / 4 else 1 / 4

/-- The witness estimator `eGood t := 10 − 1/(t+1)` (tends to `10`, never equal to it).
Source: none: infrastructure. Kind: D -/
def eW : ℕ → ℚ := fun t => 10 - 1 / ((t : ℚ) + 1)

/-- **N+ for E1's hypothesis package**: `pW` is `3/4 > ½` for `t < 3` and `1/4` after (so
`limsup p < ½` holds only *eventually* — the marginal is above `½` at `t = 0`, and the
conclusion is not claimed there), `eW t = 10 − 1/(t+1)` (tends to `10`, never equal to it),
`eBad ≡ −10` — the package is inhabited by a non-constant marginal and a non-constant estimator,
and the conclusion is exercised (`cf_t = 5 − (3/4)/(t+1) > 0` for `t ≥ 3`). Before audit r1 the
marginal was the constant `1/4`.
Source: [[dp-learner-nr-mandate]] target 8 trap (i) (the hypothesis is not `∀ t, eGood t = 10`)
Kind: N+ -/
theorem e1_witness :
    (∀ t, 0 ≤ pW t) ∧ (∀ t, pW t ≤ 1) ∧
    (∃ t, 1 / 2 < pW t) ∧
    (∃ pbar : ℚ, pbar < 1 / 2 ∧ ∀ᶠ t in atTop, pW t ≤ pbar) ∧
    (∀ δ : ℚ, 0 < δ → ∀ᶠ t in atTop, |eW t - 10| < δ) ∧
    (∀ t, eW t ≠ 10) ∧
    (∀ᶠ t in atTop, 0 < nr3Cf pW eW (fun _ => -10) t) := by
  have h0 : ∀ t, 0 ≤ pW t := fun t => by unfold pW; split_ifs <;> norm_num
  have h1 : ∀ t, pW t ≤ 1 := fun t => by unfold pW; split_ifs <;> norm_num
  have hex : ∃ t, 1 / 2 < pW t := ⟨0, by norm_num [pW]⟩
  have hl : ∃ pbar : ℚ, pbar < 1 / 2 ∧ ∀ᶠ t in atTop, pW t ≤ pbar := by
    refine ⟨1 / 4, by norm_num, ?_⟩
    rw [eventually_atTop]
    exact ⟨3, fun t ht => by unfold pW; rw [if_neg (by omega)]⟩
  have hg : ∀ δ : ℚ, 0 < δ → ∀ᶠ t in atTop, |eW t - 10| < δ := by
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
    rw [eventually_atTop]
    refine ⟨N, fun t ht => ?_⟩
    have ht' : (N : ℚ) ≤ t := by exact_mod_cast ht
    have hpos : (0 : ℚ) < (t : ℚ) + 1 := by positivity
    have h1' : 1 / ((t : ℚ) + 1) < δ := by
      rw [div_lt_iff₀ hpos]
      have : 1 / δ < (t : ℚ) + 1 := by linarith
      rwa [div_lt_iff₀ hδ, mul_comm] at this
    rw [eW, show (10 : ℚ) - 1 / ((t : ℚ) + 1) - 10 = -(1 / ((t : ℚ) + 1)) by ring, abs_neg,
      abs_of_pos (by positivity)]
    exact h1'
  refine ⟨h0, h1, hex, hl, hg, ?_, e1_static pW eW _ h0 h1 hl hg (fun _ => rfl)⟩
  intro t h
  have hpos : (0 : ℚ) < 1 / ((t : ℚ) + 1) := by positivity
  simp only [eW] at h
  linarith

/-! ## Target 8(d): regret in the deterministic-expectation model -/

/-- Total expected payoff over `T` rounds of always-cross on the fallible troll with
`𝔼[bad ∣ cross] = θ`: `10(1−2θ)·T`.
Source: [[non-responsiveness-learnability]] §2.2 ("Regret against always-cross");
[[dp-core-2-inventory]] 042; [[dp-learner-nr-mandate]] target 8(d)
Kind: D -/
def alwaysCrossTotal (θ : ℚ) (T : ℕ) : ℚ := ∑ _t ∈ range T, 10 * (1 - 2 * θ)

/-- Total expected payoff over `T` rounds of the stopper that crosses for `T_L` rounds then stays.
Source: [[non-responsiveness-learnability]] §2.2 ("the responsive learner that stops at the proof");
[[dp-learner-nr-mandate]] target 8(d)
Kind: D -/
def stopperTotal (θ : ℚ) (TL T : ℕ) : ℚ := ∑ t ∈ range T, if t < TL then 10 * (1 - 2 * θ) else 0

/-- `alwaysCrossTotal θ T = 10(1−2θ)·T`. Source: none: infrastructure. Kind: L -/
theorem alwaysCrossTotal_eq (θ : ℚ) (T : ℕ) : alwaysCrossTotal θ T = 10 * (1 - 2 * θ) * T := by
  unfold alwaysCrossTotal; rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- `stopperTotal θ TL T = 10(1−2θ)·T_L` for `T_L ≤ T`. Source: none: infrastructure. Kind: L -/
theorem stopperTotal_eq (θ : ℚ) (TL T : ℕ) (h : TL ≤ T) :
    stopperTotal θ TL T = 10 * (1 - 2 * θ) * TL := by
  unfold stopperTotal
  induction T, h using Nat.le_induction with
  | base =>
    rw [Finset.sum_congr rfl (fun t ht => if_pos (Finset.mem_range.mp ht))]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  | succ T hT ih =>
    rw [Finset.sum_range_succ, ih, if_neg (by omega)]; ring

/-- **Regret of the stopper against always-cross is `10(1−2θ)(T − T_L)`**. The note's companion
clause "the non-responsive learner's regret is `0`" is not a theorem here: in this model the
non-responsive learner is *identified* with always-cross (E1-static says it eventually crosses
every round, which is always-cross up to finitely many rounds), so its regret against
always-cross is `0` by that identification, not by a computation. (Before audit r1 this was
carried as the stub `a − a = 0`; dropped.)
Source: [[non-responsiveness-learnability]] §2.2 ("Regret against always-cross is `O(1)` for the
non-responsive learner and linear for the responsive one"); [[dp-core-2-inventory]] 042;
[[dp-learner-nr-mandate]] target 8(d)
Kind: L
Fidelity: exact (deterministic-expectation model; the simulation's `2620`/`17520` are not
theorems; the `O(1)` half is the identification above, not a theorem) -/
theorem regret_eq (θ : ℚ) (TL T : ℕ) (h : TL ≤ T) :
    alwaysCrossTotal θ T - stopperTotal θ TL T = 10 * (1 - 2 * θ) * ((T : ℚ) - TL) := by
  rw [alwaysCrossTotal_eq, stopperTotal_eq θ TL T h]
  ring

/-- **The stopper's regret is unbounded in `T`** (`θ < ½`).
Source: [[non-responsiveness-learnability]] §2.2 ("linear for the responsive one");
[[dp-learner-nr-mandate]] target 8(d)
Kind: P
Hyps: (a) `θ < ½` -/
theorem regret_unbounded (θ : ℚ) (hθ : θ < 1 / 2) (TL : ℕ) (M : ℚ) :
    ∃ T : ℕ, TL ≤ T ∧ M < alwaysCrossTotal θ T - stopperTotal θ TL T := by
  have hc : 0 < 10 * (1 - 2 * θ) := by linarith
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (M / (10 * (1 - 2 * θ)))
  refine ⟨N₀ + TL, by omega, ?_⟩
  rw [regret_eq θ TL (N₀ + TL) (by omega)]
  have h1 : ((N₀ + TL : ℕ) : ℚ) - TL = N₀ := by push_cast; ring
  rw [h1]
  rw [div_lt_iff₀ hc] at hN₀
  linarith

end Cleanroom.Decision.DpLearnerNr
