import Cleanroom.Corrigibility.CorrCautionPower.Setting
import Mathlib.Data.Finset.Lattice.Fold

/-!
# `corr-caution-power` — D9 reversibility and S9: the irreversibility guard is a rate cap

* `AUModel` — an abstract attainable-utility model: states `S`, transitions `succ`, attainable
  value `AU ω s` per hypothesis.
* **D9** `Reversible lam s a`: `∀ ω, AU ω s − AU ω (succ s a) ≤ lam` — the *decrease* half of
  attainable-utility preservation only ("the trap half of AUP, not AUP", adversary A9.2);
  `ReversiblePM` the two-sided variant (defined, no theorems). `stepValue s ω a = AU ω (succ s a)`
  links D9 to D4's `harmOf`.
* (i) `harm_le_of_reversible`: a `lam`-reversible action has harm `≤ lam` under every `ω`, given
  `hnull` (the null action does not raise `AU`).
* (ii) **`hnull` is free in a Bellman model** `AUfin_null_le`: with the finite-horizon
  `AU (n+1) ω s = max_a (r ω s a + AU n ω (succ s a))` and `r ω s nul = 0`,
  `AU n ω (succ s nul) ≤ AU (n+1) ω s` (horizons shift by one — the honest finite form).
* (iii) **The rate cap (load-bearing 5)** `rate_cap`: along a trajectory of `lam`-reversible
  actions, `AU ω (s 0) − AU ω (s T) ≤ lam · T` — *linear in `T`*, a cap on the rate of permanent
  loss, not a guard; `rate_cap_zero` / `au_mono_of_traps`: Kosoy's traps (`lam = 0`) make `AU`
  nondecreasing. Kind L: a telescoping sum; the content is the finding.
* (iv) `reversible_of_gain` and the instance `gainModel_reversible` (N+): an action that raises
  `AU` under every `ω` is `lam`-reversible for every `lam ≥ 0` — D9 never penalizes power gain.

Kosoy 2019's regret theorem is not a target (no RL layer in FAF); its two corrections (A9.3)
are in the findings file.

Sources: [[corr-wf14-inventory]] 100 → `caution-final.md` D9 (l. 51), S9(a) (l. 84), proof §9
(l. 155); [[corr-wf14-2-inventory]] 2-043 → `caution-adversary.md` A9.1, A9.2, A9.4 (l. 83–89).
-/

namespace Cleanroom.Corrigibility.CorrCautionPower

open Finset hiding expect expect_const

/-- **An attainable-utility model:** states, transitions, and the attainable value `AU ω s`
(maximum over continuation policies of expected `ω`-value) as an abstract function.
Source: [[corr-wf14-inventory]] 100 / caution-final.md D9 (l. 51)
Kind: D
Fidelity: variant: `AU` is abstract (the Bellman form is `AUfin` below)
Hyps: n/a (definition) -/
structure AUModel (S A Ω : Type*) where
  /-- The transition `s · a`. -/
  succ : S → A → S
  /-- The attainable value under hypothesis `ω` at state `s`. -/
  AU : Ω → S → ℝ

namespace AUModel

variable {S A Ω : Type*} (M : AUModel S A Ω)

/-- **D9, `lam`-reversibility (decrease half):** `∀ ω, AU ω s − AU ω (s · a) ≤ lam` — no
hypothesis loses more than `lam` of attainable value. This is the *trap half* of AUP only; the
increase direction (power gain) is not penalized (`reversible_of_gain`).
Source: [[corr-wf14-inventory]] 100 / caution-final.md D9 (l. 51); caution-adversary.md A9.2 (l. 85)
Kind: D
Fidelity: exact (decrease half, as the source relabelled it) -/
def Reversible (lam : ℝ) (s : S) (a : A) : Prop := ∀ ω, M.AU ω s - M.AU ω (M.succ s a) ≤ lam

/-- **D9±, the two-sided variant:** `∀ ω, |AU ω (s · a) − AU ω s| ≤ lam` (AUP proper). Defined;
no theorem here uses it (the increase direction is `corr-power-channel`'s).
Source: [[corr-wf14-inventory]] 100 / caution-final.md D9± (l. 51)
Kind: D
Fidelity: exact -/
def ReversiblePM (lam : ℝ) (s : S) (a : A) : Prop := ∀ ω, |M.AU ω (M.succ s a) - M.AU ω s| ≤ lam

/-- The step value `V ω a = AU ω (s · a)` that links D9 to D4's harm.
Source: [[corr-wf14-inventory]] 100 / caution-final.md proof §9 (l. 155)
Kind: D
Fidelity: exact -/
def stepValue (s : S) : Ω → A → ℝ := fun ω a => M.AU ω (M.succ s a)

/-- **S9 (i):** a `lam`-reversible action has harm at most `lam` under every hypothesis, given
that the null action does not raise attainable value (`hnull`) and `0 ≤ lam`.
Source: [[corr-wf14-inventory]] 100 / caution-final.md proof §9 (l. 155)
Kind: L
Fidelity: exact
Hyps: (a) only (`hnull` is discharged by `AUfin_null_le` in the Bellman model) -/
theorem harm_le_of_reversible {lam : ℝ} (hlam : 0 ≤ lam) (s : S) (a nul : A)
    (hrev : M.Reversible lam s a) (hnull : ∀ ω, M.AU ω (M.succ s nul) ≤ M.AU ω s) :
    ∀ ω, harmOf nul (M.stepValue s ω) a ≤ lam := by
  intro ω
  unfold harmOf stepValue
  refine max_le ?_ hlam
  linarith [hrev ω, hnull ω]

/-- **A9.2:** an action that raises attainable value under every hypothesis is `lam`-reversible
for every `lam ≥ 0` — D9 never penalizes power gain.
Source: [[corr-wf14-2-inventory]] 2-043 / caution-adversary.md A9.2 (l. 85)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem reversible_of_gain {lam : ℝ} (hlam : 0 ≤ lam) (s : S) (a : A)
    (hgain : ∀ ω, M.AU ω s ≤ M.AU ω (M.succ s a)) : M.Reversible lam s a := by
  intro ω; linarith [hgain ω]

/-- **S9(a), the rate cap (load-bearing 5).** Along a trajectory `s (t+1) = s t · a t` of
`lam`-reversible actions, `AU ω (s 0) − AU ω (s T) ≤ lam · T` for every `ω` — permanent loss is
**linear in `T`**: a rate cap, not a guard. One telescoping sum; the content is the finding.
Source: [[corr-wf14-inventory]] 100 / caution-final.md S9(a) (l. 84), proof §9 (l. 155); caution-adversary.md A9.1 (l. 83)
Kind: L
Fidelity: variant: every action along the trajectory is `lam`-reversible; the covered branch of the source's guarded form `AU(s_{t+1}) ≥ AU(s_t) − max{λ, k_t + 2δ}` is not modelled (mandate T7(iii))
Hyps: (a) only -/
theorem rate_cap {lam : ℝ} (s : ℕ → S) (a : ℕ → A) (hs : ∀ t, s (t + 1) = M.succ (s t) (a t))
    (hrev : ∀ t, M.Reversible lam (s t) (a t)) (ω : Ω) (T : ℕ) :
    M.AU ω (s 0) - M.AU ω (s T) ≤ lam * T := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h := hrev T ω
    rw [← hs T] at h
    push_cast
    linarith

/-- **Kosoy's traps (`lam = 0`):** attainable value never decreases along the trajectory.
Source: [[corr-wf14-inventory]] 100 / caution-final.md S9(a) (l. 84, "Kosoy's traps are the `λ → 0` case")
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem rate_cap_zero (s : ℕ → S) (a : ℕ → A) (hs : ∀ t, s (t + 1) = M.succ (s t) (a t))
    (hrev : ∀ t, M.Reversible 0 (s t) (a t)) (ω : Ω) (T : ℕ) : M.AU ω (s 0) ≤ M.AU ω (s T) := by
  have := M.rate_cap s a hs hrev ω T
  linarith

/-- **`lam = 0` makes `AU` monotone in time.**
Source: [[corr-wf14-inventory]] 100 / caution-final.md S9(a) (l. 84)
Kind: L
Fidelity: exact
Hyps: (a) only -/
theorem au_mono_of_traps (s : ℕ → S) (a : ℕ → A) (hs : ∀ t, s (t + 1) = M.succ (s t) (a t))
    (hrev : ∀ t, M.Reversible 0 (s t) (a t)) (ω : Ω) : Monotone fun t => M.AU ω (s t) := by
  refine monotone_nat_of_le_succ fun t => ?_
  have := hrev t ω
  rw [← hs t] at this
  linarith

end AUModel

/-! ## The finite-horizon Bellman model: `hnull` is free -/

/-- **The finite-horizon attainable value** `AU 0 = 0`,
`AU (n+1) ω s = max_a (r ω s a + AU n ω (succ s a))`.
Source: [[corr-wf14-2-inventory]] 2-043 / caution-adversary.md A9.4 (l. 89, "by definition of a max over continuations")
Kind: D
Fidelity: variant: finite horizon (the source's stationary `AU` is not available finitely) -/
noncomputable def AUfin {S A Ω : Type*} [Fintype A] [Nonempty A] (succ : S → A → S)
    (r : Ω → S → A → ℝ) : ℕ → Ω → S → ℝ
  | 0, _, _ => 0
  | n + 1, ω, s => univ.sup' univ_nonempty (fun a => r ω s a + AUfin succ r n ω (succ s a))

/-- **S9 (ii), `hnull` is free in a Bellman model (A9.4):** if the null action has zero immediate
reward, `AU n ω (s · nul) ≤ AU (n+1) ω s` — the honest finite-horizon form of "the null action
does not raise attainable value" (horizons shift by one).
Source: [[corr-wf14-2-inventory]] 2-043 / caution-adversary.md A9.4 (l. 89)
Kind: L
Fidelity: variant: horizons shift by one
Hyps: (a) only -/
theorem AUfin_null_le {S A Ω : Type*} [Fintype A] [Nonempty A] (succ : S → A → S)
    (r : Ω → S → A → ℝ) (nul : A) (hnull : ∀ ω s, r ω s nul = 0) (n : ℕ) (ω : Ω) (s : S) :
    AUfin succ r n ω (succ s nul) ≤ AUfin succ r (n + 1) ω s := by
  show AUfin succ r n ω (succ s nul) ≤ univ.sup' univ_nonempty (fun a => r ω s a + AUfin succ r n ω (succ s a))
  refine le_trans ?_ (le_sup' (fun a => r ω s a + AUfin succ r n ω (succ s a)) (mem_univ nul))
  rw [hnull, zero_add]

/-! ## A9.2 witness: a power-gaining action passes D9 -/

/-- A two-state model in which the single action moves to the high-value state under every
hypothesis (`AU ω false = 0`, `AU ω true = 1`).
Source: [[corr-wf14-2-inventory]] 2-043 / caution-adversary.md A9.2 (l. 85)
Kind: D
Fidelity: n/a (witness) -/
def gainModel : AUModel Bool Unit (Fin 2) where
  succ _ _ := true
  AU _ s := if s then 1 else 0

/-- **A9.2 (N+):** in `gainModel` the action from the low state raises `AU` by `1` under both
hypotheses and is `lam`-reversible for every `lam ≥ 0`: D9 does not see power gain.
Source: [[corr-wf14-2-inventory]] 2-043 / caution-adversary.md A9.2 (l. 85)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem gainModel_reversible {lam : ℝ} (hlam : 0 ≤ lam) :
    (∀ ω, gainModel.AU ω (gainModel.succ false ()) = gainModel.AU ω false + 1) ∧
      gainModel.Reversible lam false () := by
  refine ⟨fun ω => by simp [gainModel], ?_⟩
  exact gainModel.reversible_of_gain hlam false () fun ω => by simp [gainModel]

end Cleanroom.Corrigibility.CorrCautionPower
