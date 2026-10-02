import Cleanroom.Corrigibility.LegitNegStatic.Problem

/-!
# Scorings: menu vectors as exact functions of `u`

Package `legit-neg-static`, target 2. Source: `clusters/B/fixtures/model.py:79-141`, pinned by
[[corr-legit-neg-2-inventory]] item 2-002 and [[corr-legit-neg-inventory]] item 003.

A menu vector `V s a c` is the number the humans at terminal `(s, a)` write for option `c`.
It is meaningful only where `leg s a = true`; the proposals (`Proposals.lean`) multiply every
read by `ind (leg s a)`, so they never consult it elsewhere.

**Convention of record, and the finding it carries.** S1 prices *every* option `c` at a
legitimate terminal by `u s c`, *including when `(s, c)` is void*: the legitimate humans at
`(s, a)` price the void outcome of the unchosen `c` by the standard's own value (sighted
evaluators). This is `model.py:80-94` verbatim and it contradicts the run's own prose ("void
terminals carry no score"); it is what makes the R2-S1 lemma of `Readouts.lean` true.
`blindImpute` is the honest variant (the evaluators cannot see what a voiding option would
have done and write `y`). Finding recorded in `legit-neg-static-findings.md` (1).
-/

namespace Cleanroom.Corrigibility.LegitNegStatic

open Finset

/-- A menu vector: `V s a c` is the score the humans at terminal `(s, a)` give option `c`.
Source: [[corr-legit-neg-inventory]] item 001
Kind: D
Fidelity: exact -/
abbrev MenuVec (S A : Type) := S → A → A → ℚ

/-- The selection-independent lift of a state-indexed vector `V s c` (the sealed regime's
`V_s(c)`, NEGATIVES A §0): the same vector whatever option was selected.
Source: [[corr-legit-neg-inventory]] item 003 (R3 with selection-blindness)
Kind: D
Fidelity: exact -/
def liftV {S A : Type} (V : S → A → ℚ) : MenuVec S A := fun s _ c => V s c

/-- `liftV_apply`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma liftV_apply {S A : Type} (V : S → A → ℚ) (s : S) (a c : A) :
    liftV V s a c = V s c := rfl

/-- **S1**, outcome / absolute quality: `V s a c = u s c` at every legitimate terminal,
*including when `(s, c)` is void* (sighted evaluators; `model.py:80-94`). See the file
docstring for why this convention is a finding.
Source: [[corr-legit-neg-2-inventory]] item 2-002
Kind: D
Fidelity: exact -/
def S1 {S A : Type} (u : S → A → ℚ) : MenuVec S A := fun s _ c => u s c

/-- `S1_apply`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma S1_apply {S A : Type} (u : S → A → ℚ) (s : S) (a c : A) : S1 u s a c = u s c := rfl

namespace Problem

variable {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)

/-- **S1-blind** (`blind_impute = y`): the humans at `(s, a)` cannot see what an unchosen
option `c ≠ a` would have done where it voids legitimacy, and write `y` for it; elsewhere `u s c`.
The honest variant of `S1`.
Source: [[corr-legit-neg-2-inventory]] item 2-002
Kind: D
Fidelity: exact -/
def blindImpute [DecidableEq A] (y : ℚ) : MenuVec S A :=
  fun s a c => if c ≠ a ∧ P.leg s c = false then y else P.u s c

/-- `E_π[u(·, c) | E]` for an event `E`: the conditional expectation of the standard; junk
`… / 0` when `mass E = 0` (every use carries `0 < mass E` or multiplies by `mass E`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def Hcond (E : S → Bool) (c : A) : ℚ := (∑ s, P.prior s * ind (E s) * P.u s c) / P.mass E

/-- **S2**, decision-scored ex ante, accurate: option `c` scored as the bet `E_π[u(·, c)]` from
the agent's issuance-time information — the prior, when there are no cells (`model.py:97-106`).
Reads `u` on void terminals: this is exactly A6's escape (ingredient 2 supplied).
Source: [[corr-legit-neg-2-inventory]] item 2-002
Kind: D
Fidelity: exact -/
def S2 : MenuVec S A := fun _ _ c => P.H c

/-- **S2** within information cells: `V s a c = H c (cell s)` (`model.py:97-106` with `cell_of`).
Junk-free only for cells of positive mass (T2 restriction).
Source: [[corr-legit-neg-2-inventory]] item 2-002
Kind: D
Fidelity: exact -/
def S2cell [DecidableEq S] (cellOf : S → Finset S) : MenuVec S A :=
  fun s _ c => P.Hc c (cellOf s)

/-- **S2sel**, selection-correlated: the evaluators at `(s, a)` cannot un-know that legitimacy
held under the *taken* action `a`, and score `c` as `E_π[u(·, c) | L_a]` with
`L_a = {t | leg t a}` (`model.py:109-119`). Conditions on the legitimacy of `a`, not of `c`.
Source: [[corr-legit-neg-2-inventory]] item 2-002
Kind: D
Fidelity: exact -/
def S2sel : MenuVec S A := fun _ a c => P.Hcond (fun t => P.leg t a) c

/-- The within-state maximum of the standard, `max_{c'} u s c'`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def umax [Nonempty A] (s : S) : ℚ := univ.sup' univ_nonempty (fun c => P.u s c)

/-- `le_umax`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma le_umax [Nonempty A] (s : S) (c : A) : P.u s c ≤ P.umax s :=
  Finset.le_sup' (fun c => P.u s c) (Finset.mem_univ c)

/-- **S3**, menu-relative in hindsight-regret form: `V s a c = 1 − (max_{c'} u s c' − u s c)/D`
(`model.py:122-131`). **Not** confined to `[0, 1]`: when the within-state range of `u`
exceeds `D` the value is negative (B12's `w = −1`, `D = 1` gives `−1/4`; see
`Toys.lean`, `S3_toy_neg`). The type is `ℚ`, on purpose. At `D = 0` Lean's `x / 0 = 0` makes
`S3 0` the constant vector `1`; the mandate has `0 < D`, and no headline uses `D = 0`.
Source: [[corr-legit-neg-2-inventory]] item 2-002
Kind: D
Fidelity: exact -/
def S3 [Nonempty A] (D : ℚ) : MenuVec S A := fun s _ c => 1 - (P.umax s - P.u s c) / D

/-- **Shift-type S3** (VERIFY A, V1): `V s a c = u s c − k s`, a common per-state shift.
Source: VERIFY A "A1: narrowed (i)"
Kind: D
Fidelity: exact -/
def shiftS3 (k : S → ℚ) : MenuVec S A := fun s _ c => P.u s c - k s

/-- **Ordinal S3** (VERIFY A, V1): the rank score `1` for a within-state maximiser of `u`, `0`
otherwise — `RUN.md` §3's "options ranked relative to each other" read literally.
Source: VERIFY A "A1: narrowed (i)"
Kind: D
Fidelity: exact -/
def ordinalS3 : MenuVec S A := fun s _ c => ind (decide (∀ c', P.u s c' ≤ P.u s c))

/-- **Hybrid** scoring `penalise V where option p` (`model.py:134-141`): subtract `p` from
`option`'s entry at the terminals selected by `where`.
Source: [[corr-legit-neg-2-inventory]] item 2-002
Kind: D
Fidelity: exact -/
def penalise [DecidableEq A] (V : MenuVec S A) (where_ : S → A → Bool) (option : A) (p : ℚ) :
    MenuVec S A :=
  fun s a c => if where_ s a ∧ c = option then V s a c - p else V s a c

/-- `S1` and `blindImpute` agree on the diagonal (the option actually taken), so every
proposal that reads only the diagonal cannot tell them apart; they differ only off-diagonal
(R2 readouts).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma blindImpute_diag [DecidableEq A] (y : ℚ) (s : S) (a : A) :
    P.blindImpute y s a a = S1 P.u s a a := by
  simp [blindImpute]

/-- `blindImpute` agrees with `S1 u` wherever the scored option is itself legitimate.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma blindImpute_of_leg [DecidableEq A] (y : ℚ) (s : S) (a c : A) (h : P.leg s c = true) :
    P.blindImpute y s a c = P.u s c := by
  simp [blindImpute, h]

/-- The shift-type S3 differs from S1 by a per-state constant, which is what makes it keep
A1's bound (target 9 (iv)).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma shiftS3_eq (k : S → ℚ) (s : S) (a c : A) : P.shiftS3 k s a c = S1 P.u s a c - k s := rfl

end Problem

end Cleanroom.Corrigibility.LegitNegStatic
