import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# `dp-learner-nr` D5 and targets 11(b)–(d): the refuser chains

**D5.** Transition kernels over `ℚ` with rows summing to one (proved); `Absorbing i := M i i = 1`;
the expected hitting time of a target set as **the solution of the first-step linear system**
`h_i = 1 + ∑_{j ∉ target} M i j h_j`, with uniqueness proved directly (the determinant `η/4` is
recorded). The identification "solution of the first-step system = `𝔼[hitting time]`" is a (b)
hypothesis (Norris, *Markov Chains*, Thm 1.3.5) on every row that uses the phrase "expected
escape time" — target 15 would discharge it.

**GR-16 product chain** (`gr16`): states `(verdict = pay?, unsealed?) : Bool × Bool`; Omega's
verdict is the last observed tails action; transfer on heads iff the verdict is `pay`; the
two-hypothesis agent pays when unsealed, and while sealed refuses except for exploring (paying)
with probability `η` on tails; a sealed agent that observes a transfer unseals. The kernel is
*derived* as `½·tails + ½·heads` from the two per-outcome kernels (`tailsKernel`, `headsKernel`),
each of whose rows is listed in its docstring.

* `gr16_rows_sum_one`; `gr16_absorbing`: `(P,U)` absorbing; `(R,S)` absorbing iff `η = 0`; no
  other absorbing state (`0 < η ≤ 1`).
* `gr16_firstStep_unique`: the first-step system for the target `{(P,U)}` has the **unique**
  solution `h(P,S) = 2/η`, `h(R,S) = 4/η`, `h(R,U) = 2` (`0 < η`); `fs_det`: the `2×2` subsystem's
  determinant is `η/4`. N+: `η = 1/10 ↦ 20, 40`; `η = 1 ↦ 2, 4`.

**GR-15, the sealed hazard** (`sealedHazard`): `½·(η(1−ε) + ε(1−η)) = ½(η + ε − 2ηε)` — the
probability that exactly one of two independent events fires, scaled by the heads probability.
The one-way-reset chains (`resetChainA`: data-then-replacement; `resetChainB`:
replacement-then-data) have the unique stationary sealed probabilities `ρ/(ρ + (1−ρ)r)` and
`ρ(1−r)/(ρ(1−r) + r)` (`resetChainA_stationary_unique`, `resetChainB_stationary_unique`), with
exact odds `ρ : (1−ρ)r` and `ρ(1−r) : r` (first-order `ρ : r`).
-/

namespace Cleanroom.Decision.DpLearnerNr

open Finset

/-- A state of the GR-16 product chain: `(verdict = pay?, agent unsealed?)`.
`(true, true)` = `(P,U)`, `(true, false)` = `(P,S)`, `(false, true)` = `(R,U)`,
`(false, false)` = `(R,S)`.
Source: `cf-workflow/phase2-notes/repair/grounding.md` GR-16 ("states `(v, a) ∈ {P, R} × {U, S}`");
[[dp-learner-nr-mandate]] D5
Kind: D -/
abbrev GrState : Type := Bool × Bool

/-- **The tails kernel** (the agent acts; Omega's verdict becomes the observed action):
an unsealed agent pays, so `(·, U) → (P, U)` w.p. `1`; a sealed agent explores (pays) w.p. `η`,
`(·, S) → (P, S)`, and refuses otherwise, `(·, S) → (R, S)` w.p. `1 − η`.
Source: GR-16 ("the agent refuses while sealed, explores (paying) w.p. `η` on tails"; "Omega's
verdict = the agent's last observed tails action"); [[dp-learner-nr-mandate]] target 11(b)
Kind: D -/
def tailsKernel (η : ℚ) : GrState → GrState → ℚ
  | (_, true), (true, true) => 1
  | (_, true), _ => 0
  | (_, false), (true, false) => η
  | (_, false), (false, false) => 1 - η
  | (_, false), _ => 0

/-- **The heads kernel** (Omega transfers iff the verdict is `pay`; a transfer is observed and
unseals): `(P, ·) → (P, U)` w.p. `1`; `(R, a) → (R, a)` w.p. `1` (no transfer, nothing observed).
Source: GR-16 ("transfer on heads iff verdict `P`"); [[dp-learner-nr-mandate]] target 11(b)
Kind: D -/
def headsKernel : GrState → GrState → ℚ
  | (true, _), (true, true) => 1
  | (true, _), _ => 0
  | (false, a), (false, a') => if a = a' then 1 else 0
  | (false, _), _ => 0

/-- **The GR-16 product chain**: a fair coin, then the tails or heads kernel.
Source: GR-16; [[dp-cf-2-inventory]] 031; [[dp-learner-nr-mandate]] D5, target 11(b)
Kind: D
Fidelity: exact (derived from the episode mechanics, not written down as the answer) -/
def gr16 (η : ℚ) (i j : GrState) : ℚ := 1 / 2 * tailsKernel η i j + 1 / 2 * headsKernel i j

/-- An absorbing state: `M i i = 1`. Source: [[dp-learner-nr-mandate]] D5. Kind: D -/
def Absorbing {S : Type} (M : S → S → ℚ) (i : S) : Prop := M i i = 1

/-- The rows of `gr16` sum to one (`0 ≤ η ≤ 1` is not even needed for the sum).
Source: [[dp-learner-nr-mandate]] D5 ("rows summing to one (prove it)")
Kind: L -/
theorem gr16_rows_sum_one (η : ℚ) (i : GrState) : ∑ j, gr16 η i j = 1 := by
  rcases i with ⟨v, a⟩
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  cases v <;> cases a <;> simp [gr16, tailsKernel, headsKernel] <;> ring

/-- The entries of `gr16` are non-negative for `0 ≤ η ≤ 1`. Source: none: infrastructure. Kind: L -/
theorem gr16_nonneg (η : ℚ) (h0 : 0 ≤ η) (h1 : η ≤ 1) (i j : GrState) : 0 ≤ gr16 η i j := by
  rcases i with ⟨v, a⟩; rcases j with ⟨v', a'⟩
  cases v <;> cases a <;> cases v' <;> cases a' <;> simp [gr16, tailsKernel, headsKernel] <;> linarith

/-- **The absorbing states of GR-16**: `(P,U)` is absorbing; `(R,S)` is absorbing iff `η = 0`;
`(P,S)` and `(R,U)` are never absorbing (`η ≤ 1`). So "XC-8's two absorbing states hold exactly
at `η = 0` and only there".
Source: GR-16 ("Absorbing: `{(P,U)}` for `η > 0`; `{(P,U),(R,S)}` at `η = 0`");
[[dp-cf-2-inventory]] 031; [[dp-learner-nr-mandate]] target 11(b), load-bearing 5
Kind: P
Fidelity: exact
Hyps: (a) `η ≤ 1` -/
theorem gr16_absorbing (η : ℚ) (h1 : η ≤ 1) :
    Absorbing (gr16 η) (true, true) ∧
    (Absorbing (gr16 η) (false, false) ↔ η = 0) ∧
    ¬ Absorbing (gr16 η) (true, false) ∧ ¬ Absorbing (gr16 η) (false, true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Absorbing, gr16, tailsKernel, headsKernel]; norm_num
  · simp [Absorbing, gr16, tailsKernel, headsKernel]
    constructor <;> intro h <;> linarith
  · simp [Absorbing, gr16, tailsKernel, headsKernel] <;> intro h <;> linarith
  · simp [Absorbing, gr16, tailsKernel, headsKernel]

/-- **The first-step system** for hitting a *single* target state (D5 says "target set"; the
GR-16 instance has the one-point target `{(P,U)}`, so nothing is lost): `h target = 0` and, at
every other state, `h i = 1 + ∑_{j ≠ target} M i j · h j`.
Source: [[dp-learner-nr-mandate]] D5 ("the solution of the first-step linear system
`h_i = 1 + ∑_{j ∉ target} M i j h_j`"); Norris, *Markov Chains*, Thm 1.3.5 (the identification
with the expected hitting time is a (b) hypothesis, not proved here)
Kind: D -/
def FirstStepSolution {S : Type} [Fintype S] [DecidableEq S] (M : S → S → ℚ) (target : S)
    (h : S → ℚ) : Prop :=
  h target = 0 ∧ ∀ i, i ≠ target → h i = 1 + ∑ j, if j = target then 0 else M i j * h j

/-- The `2×2` subsystem's determinant (`u = h(P,S)`, `w = h(R,S)`): `(1 − η/2)(η/2) − ((1−η)/2)(η/2) = η/4`.
Source: GR-16 ("determinant `η/4`"); [[dp-learner-nr-mandate]] target 11(c)
Kind: L -/
theorem fs_det (η : ℚ) : (1 - η / 2) * (η / 2) - ((1 - η) / 2) * (η / 2) = η / 4 := by ring

/-- **The first-step system of GR-16 for the target `(P,U)` has the unique solution
`h(P,S) = 2/η`, `h(R,S) = 4/η`, `h(R,U) = 2`** (`0 < η`) — the "expected escape times" `2/η` from
`(P,S)` and `4/η` from `(R,S)` (load-bearing 5).
Source: GR-16 ("Expected unsealing time from `(R,S)`: `4/η` … from `(P,S)`: `2/η` (first-step
system `u = 1 + (η/2)u + ((1−η)/2)w`, `w = 1 + (η/2)u + (1 − η/2)w`, determinant `η/4`)");
[[dp-cf-2-inventory]] 031; [[dp-cf-inventory]] 123; [[dp-learner-nr-mandate]] target 11(c)
Kind: P
Fidelity: exact (of the first-step system; the phrase "expected escape time" carries the (b)
identification)
Hyps: (b) "solution of the first-step system = `𝔼[hitting time]`" (Norris Thm 1.3.5) — the
theorem itself is about the system; (a) `0 < η`, load-bearing: at `η = 0` the system has *no*
solution (`gr16_firstStep_eta0_no_solution`), consistent with `(R,S)` absorbing and an infinite
hitting time — the mandate's "`{(P,U),(R,S)}` at `η = 0`" row and the `2/η` row meet exactly there -/
theorem gr16_firstStep_unique (η : ℚ) (hη : 0 < η) (h : GrState → ℚ)
    (hs : FirstStepSolution (gr16 η) (true, true) h) :
    h (true, false) = 2 / η ∧ h (false, false) = 4 / η ∧ h (false, true) = 2 := by
  obtain ⟨h0, hrec⟩ := hs
  have hu := hrec (true, false) (by decide)
  have hw := hrec (false, false) (by decide)
  have hr := hrec (false, true) (by decide)
  rw [Fintype.sum_prod_type] at hu hw hr
  simp only [Fintype.sum_bool] at hu hw hr
  simp [gr16, tailsKernel, headsKernel] at hu hw hr
  have hηu : η * h (true, false) = 2 := by
    linear_combination 2 * (1 - η) * hw + 2 * η * hu
  have hr2 : h (false, true) = 2 := by linarith
  refine ⟨?_, ?_, hr2⟩
  · rw [eq_div_iff hη.ne']; linarith
  · rw [eq_div_iff hη.ne']; linear_combination 2 * hw + hηu

/-- **N+**: `η = 1/10 ↦ 20, 40` and `η = 1 ↦ 2, 4` — the formulas, and the system is inhabited by
them (the solution exists: `h := (0, 2/η, 2, 4/η)` satisfies the system).
Source: GR-16 ("`40, 400, 8, 4` at `η = 1/10, 1/100, 1/2, 1`"); [[dp-learner-nr-mandate]] target 11(c)
Kind: N+ -/
theorem gr16_firstStep_instance (η : ℚ) (hη : 0 < η) :
    FirstStepSolution (gr16 η) (true, true)
      (fun s => match s with
        | (true, true) => 0 | (true, false) => 2 / η | (false, true) => 2 | (false, false) => 4 / η) ∧
    (2 : ℚ) / (1 / 10) = 20 ∧ (4 : ℚ) / (1 / 10) = 40 ∧ (2 : ℚ) / 1 = 2 ∧ (4 : ℚ) / 1 = 4 := by
  refine ⟨⟨rfl, ?_⟩, by norm_num, by norm_num, by norm_num, by norm_num⟩
  rintro ⟨v, a⟩ hne
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have hη' : η ≠ 0 := hη.ne'
  cases v <;> cases a
  all_goals first
    | exact absurd rfl hne
    | (simp [gr16, tailsKernel, headsKernel]; field_simp; ring)
    | (simp [gr16, tailsKernel, headsKernel]; ring)
    | simp [gr16, tailsKernel, headsKernel]

/-- **At `η = 0` the first-step system for `(P,U)` has no solution at all**: `(R,S)` is absorbing
(`gr16_absorbing`) and its equation reads `w = 1 + w`. So `0 < η` in `gr16_firstStep_unique` is
load-bearing and the system is not trivially solvable. Adopted from audit r1's `FirstStepEta0`
probe.
Source: GR-16 (the absorbing set `{(P,U), (R,S)}` at `η = 0`); [[dp-learner-nr-audit-r1-adversarial]]
§3 item 13
Kind: L -/
theorem gr16_firstStep_eta0_no_solution :
    ¬ ∃ h : GrState → ℚ, FirstStepSolution (gr16 0) (true, true) h := by
  rintro ⟨h, _, hrec⟩
  have hw := hrec (false, false) (by decide)
  rw [Fintype.sum_prod_type] at hw
  simp only [Fintype.sum_bool] at hw
  simp [gr16, tailsKernel, headsKernel] at hw
  all_goals linarith

/-! ## GR-15: the sealed hazard and the one-way-reset chains -/

/-- **The sealed state's escape hazard** with exploration `η` and Omega's symmetric transfer noise
`ε`: `½·(η(1−ε) + ε(1−η))` — the heads probability times the probability that exactly one of
two independent events fires.
Source: GR-15 ("the sealed state's escape hazard is `r_b = ½(η + ε − 2ηε)`"); [[dp-cf-2-inventory]]
031; [[dp-learner-nr-mandate]] target 11(d)
Kind: D -/
def sealedHazard (η ε : ℚ) : ℚ := 1 / 2 * (η * (1 - ε) + ε * (1 - η))

/-- `r_b = ½(η + ε − 2ηε)`, and `η/2` at `ε = 0`. Source: GR-15. Kind: L -/
theorem sealedHazard_eq (η ε : ℚ) :
    sealedHazard η ε = 1 / 2 * (η + ε - 2 * η * ε) ∧ sealedHazard η 0 = η / 2 := by
  unfold sealedHazard; constructor <;> ring

/-- A `2×2` kernel on `Fin 2` (`0` = sealed, `1` = unsealed) is stationary at `π` if
`π ⬝ M = π` and `π 0 + π 1 = 1`.
Source: [[dp-learner-nr-mandate]] D5
Kind: D -/
def IsStationary (M : Matrix (Fin 2) (Fin 2) ℚ) (π : Fin 2 → ℚ) : Prop :=
  (∀ j, ∑ i, π i * M i j = π j) ∧ π 0 + π 1 = 1

/-- **The data-then-replacement reset chain**: from sealed, escape (data) w.p. `r` then survive
replacement w.p. `1 − ρ`, so `S → U` w.p. `(1−ρ)r`; from unsealed, replacement by a fresh sealed
agent w.p. `ρ`.
Source: GR-15 ("`P(sealed) = ρ/(ρ + (1−ρ)r_b)` (data-then-replacement)"); [[dp-learner-nr-mandate]] target 11(d)
Kind: D -/
def resetChainA (ρ r : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1 - (1 - ρ) * r, (1 - ρ) * r; ρ, 1 - ρ]

/-- **The replacement-then-data reset chain**: from sealed, escape w.p. `r`; from unsealed,
replacement w.p. `ρ` to sealed and then escape w.p. `r`, so `U → S` w.p. `ρ(1−r)`.
Source: GR-15 ("`ρ(1−r_b)/(ρ(1−r_b) + r_b)` (replacement-then-data)"); [[dp-learner-nr-mandate]] target 11(d)
Kind: D -/
def resetChainB (ρ r : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1 - r, r; ρ * (1 - r), 1 - ρ * (1 - r)]

/-- The rows of both reset chains sum to one. Source: none: infrastructure. Kind: L -/
theorem resetChains_rows_sum_one (ρ r : ℚ) (i : Fin 2) :
    ∑ j, resetChainA ρ r i j = 1 ∧ ∑ j, resetChainB ρ r i j = 1 := by
  fin_cases i <;> simp [resetChainA, resetChainB, Fin.sum_univ_two] <;> ring

/-- **The unique stationary sealed probability of chain A is `ρ/(ρ + (1−ρ)r)`**, with exact odds
`π_S : π_U = ρ : (1−ρ)r` (first-order `ρ : r`). The theorem is about the linear system
`π M = π`, `π₀ + π₁ = 1`: it carries no hypothesis `ρ, r ∈ [0, 1]` and applies as linear algebra
outside the stochastic domain (audit r2's `ResetChainDomain` probe: `ρ = 2`, `r = −1`); the
chain reading needs `0 ≤ ρ, r ≤ 1`, where the N+ instance `resetChains_instance` sits.
Source: GR-15 ("`P(sealed) = ρ/(ρ + (1−ρ)r_b)` … first-order odds `ρ : r_b`");
[[dp-cf-2-inventory]] 031, 030; [[dp-learner-nr-mandate]] target 11(d)
Kind: P
Fidelity: exact (of the stationarity equations; the Markov-chain reading adds `ρ, r ∈ [0, 1]`,
not assumed because not used)
Hyps: (a) `0 < ρ + (1−ρ)r` (the chain is not frozen) -/
theorem resetChainA_stationary_unique (ρ r : ℚ) (hpos : 0 < ρ + (1 - ρ) * r) (π : Fin 2 → ℚ)
    (hπ : IsStationary (resetChainA ρ r) π) :
    π 0 = ρ / (ρ + (1 - ρ) * r) ∧ π 0 * ((1 - ρ) * r) = π 1 * ρ := by
  obtain ⟨hst, hsum⟩ := hπ
  have h0 := hst 0
  simp [resetChainA, Fin.sum_univ_two] at h0
  have hodds : π 0 * ((1 - ρ) * r) = π 1 * ρ := by linarith
  refine ⟨?_, hodds⟩
  rw [eq_div_iff hpos.ne']
  have : π 1 = 1 - π 0 := by linarith
  rw [this] at hodds
  linarith

/-- The stationary distribution of chain A exists: the formula is stationary.
Source: none: infrastructure
Kind: L -/
theorem resetChainA_stationary_exists (ρ r : ℚ) (hpos : 0 < ρ + (1 - ρ) * r) :
    IsStationary (resetChainA ρ r)
      ![ρ / (ρ + (1 - ρ) * r), (1 - ρ) * r / (ρ + (1 - ρ) * r)] := by
  have hne := hpos.ne'
  constructor
  · intro j
    fin_cases j <;> simp [resetChainA, Fin.sum_univ_two] <;> field_simp <;> ring
  · simp; field_simp; try ring

/-- **The unique stationary sealed probability of chain B is `ρ(1−r)/(ρ(1−r) + r)`**, with exact
odds `π_S : π_U = ρ(1−r) : r`. As for chain A: a statement about the linear system, with no
`ρ, r ∈ [0, 1]` hypothesis (not used); the chain reading lives inside that domain.
Source: GR-15 ("`ρ(1−r_b)/(ρ(1−r_b) + r_b)` (replacement-then-data)"); [[dp-learner-nr-mandate]] target 11(d)
Kind: P
Fidelity: exact (of the stationarity equations; the Markov-chain reading adds `ρ, r ∈ [0, 1]`,
not assumed because not used)
Hyps: (a) `0 < ρ(1−r) + r` -/
theorem resetChainB_stationary_unique (ρ r : ℚ) (hpos : 0 < ρ * (1 - r) + r) (π : Fin 2 → ℚ)
    (hπ : IsStationary (resetChainB ρ r) π) :
    π 0 = ρ * (1 - r) / (ρ * (1 - r) + r) ∧ π 0 * r = π 1 * (ρ * (1 - r)) := by
  obtain ⟨hst, hsum⟩ := hπ
  have h0 := hst 0
  simp [resetChainB, Fin.sum_univ_two] at h0
  have hodds : π 0 * r = π 1 * (ρ * (1 - r)) := by linarith
  refine ⟨?_, hodds⟩
  rw [eq_div_iff hpos.ne']
  have : π 1 = 1 - π 0 := by linarith
  rw [this] at hodds
  linarith

/-- The stationary distribution of chain B exists: the formula is stationary.
Source: none: infrastructure
Kind: L -/
theorem resetChainB_stationary_exists (ρ r : ℚ) (hpos : 0 < ρ * (1 - r) + r) :
    IsStationary (resetChainB ρ r)
      ![ρ * (1 - r) / (ρ * (1 - r) + r), r / (ρ * (1 - r) + r)] := by
  have hne := hpos.ne'
  constructor
  · intro j
    fin_cases j <;> simp [resetChainB, Fin.sum_univ_two] <;> field_simp <;> ring
  · simp; field_simp; try ring

/-- **N+ (GR-15's numbers)**: at `ρ = r = 1/100`, chain A's sealed probability is `100/199` and
chain B's is `99/199` — the two orderings differ at first order from GR-14's `ρ : (ρ + r)`
(findings: dp-cf-2-030's corrected `f`).
Source: GR-15 ("`0.503` vs `0.332` at `ρ = r_b = 1/100`"); [[dp-learner-nr-mandate]] target 11(d)
Kind: N+ -/
theorem resetChains_instance :
    (1 / 100 : ℚ) / (1 / 100 + (1 - 1 / 100) * (1 / 100)) = 100 / 199 ∧
    (1 / 100 : ℚ) * (1 - 1 / 100) / ((1 / 100) * (1 - 1 / 100) + 1 / 100) = 99 / 199 := by
  norm_num

end Cleanroom.Decision.DpLearnerNr
