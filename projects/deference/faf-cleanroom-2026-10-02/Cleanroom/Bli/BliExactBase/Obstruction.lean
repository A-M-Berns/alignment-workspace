import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# `bli-exact-base` — M4's obstruction theorem ([[bli-program]] §3.8's "fixed-point obstruction in
convex-analytic form"; a different constraint from bli-soto-a-058 (ii)'s)

**FAF-free, finite.** A finite set of worlds `ι` with a `{0,1}` payout table `pay : ι → Φ → ℝ` on
a finite set of sentences `Φ`; a price vector `p ∈ Δ(ι)` induces prices
`induced pay p φ = ∑ w, p w · pay w φ`; a trade `t : Φ → ℝ` has value
`tradeValue pay t p w = ∑ φ, t φ · (pay w φ − induced pay p φ)` in world `w`; and `p` is
**acceptable** for `t` when the value is `≤ 0` in every world (the market maker's acceptance at
slack `0`; FAF's `MarketMakerAccepts` checks the same inequality over every Boolean table on the
strategy's support, a superset of any plausible-world class, so an obstruction over plausible
worlds is an obstruction there too — see the ledger).

**The cell setting.** One coordinate `φ` with `m` cell literals `lit r` and representatives
`rep r`; the plausible worlds are the assignments with exactly one literal true
(`Bool × Fin m`, the truth value of `φ` and the true cell). The **constrained set**
`Constrained rep` is `D_NNUcell` at this coordinate as an affine constraint on the day-`n` price
vector: `∑ r, rep r · p(lit r) = p(φ)`.

**The theorem** (`obstruction`, Kind `P`): the bundle trade `bundleTrade rep` (buy one `φ`, sell
`rep r` of each `lit r` — bli-soto-b-025's bundle) has, for **every** `p ∈ Constrained rep`, in
the plausible world `(φ true, lit r₀ true)`, value exactly `1 − rep r₀` (`tradeValue_bundle`:
the price-dependent part is the constraint, which vanishes on `K`). So whenever some cell has
`rep r₀ < 1`, no constrained price is acceptable: the per-day market-maker route restricted to
`K` cannot deliver exact `D_NNUcell`. The slack form (`obstruction_slack`) survives every
`ε < 1 − rep r₀`: exactness is not what breaks it, the per-day constraint is.

**The artifact check** ([[STANDARDS]] §3): `constrained_nonempty` (the constraint is satisfiable
on the simplex) and `contrast_acceptable` (on the *unconstrained* simplex the same trade has an
acceptable point — the point mass on `(φ true, lit rmin true)` at a cell of minimal
representative), which is not constrained when `rep rmin < 1` (`contrast_not_constrained`). The
impossibility is the intersection `K ∩ Acc(t) = ∅`, not an empty `K` or an empty `Acc(t)`.

**What this is not** (repair round 1, audit r1 fidelity B2). bli-soto-a-058 (ii) diagnoses a
*different* constraint: same-day exact introspection with a sharp indicator of the current price
(`Q_n(“Q_n(φ) > 0.5”) = 1[Q_n(φ) > 0.5]`), where the demand's discontinuity in the price is the
right obstacle to a Brouwer fixed point (FAF's `lic_introspection` uses the continuous `ctsInd`
for that reason). The constraint here is [[bli-program]] §3.8's *next-day affine* `D_NNUcell`
constraint at one coordinate; its set `K` is closed and convex, every continuous self-map of it
has a fixed point, and no point of `K` is acceptable. The two mechanisms are distinct; the
program's §3.8 attributes this one to the source ("Soto's fixed-point obstruction … in
convex-analytic form"), loosely (findings F5).
-/

namespace Cleanroom.Bli.BliExactBase.Obstruction

open Finset

variable {ι Φ : Type} [Fintype ι] [Fintype Φ]

/-! ## Markets, trades, acceptance -/

/-- The price of `φ` induced by the world-price vector `p`: `∑ w, p w · pay w φ`.
Source: mandate § 7 (setting); [[bli-program]] §3.8
Kind: D
Fidelity: exact -/
def induced (pay : ι → Φ → ℝ) (p : ι → ℝ) (φ : Φ) : ℝ := ∑ w, p w * pay w φ

/-- The value of the trade `t` at prices `p` in world `w`: `∑ φ, t φ · (pay w φ − induced p φ)`.
Source: mandate § 7 (`B_t(p, w)`)
Kind: D
Fidelity: exact -/
def tradeValue (pay : ι → Φ → ℝ) (t : Φ → ℝ) (p : ι → ℝ) (w : ι) : ℝ :=
  ∑ φ, t φ * (pay w φ - induced pay p φ)

/-- **Acceptance at slack `0`**: the trade's value is `≤ 0` in every world of the class.
Source: mandate § 7 (`Acceptable`); FAF `MarketMakerAccepts` (`Construction/MarketMaker.lean:945`,
the same inequality over every Boolean table on the support, at slack `ε`)
Kind: D
Fidelity: variant: the world class is the finite type `ι` (plausible worlds) in place of every Boolean table on the support; slack `0` -/
def Acceptable (pay : ι → Φ → ℝ) (t : Φ → ℝ) (p : ι → ℝ) : Prop :=
  ∀ w, tradeValue pay t p w ≤ 0

/-- The price simplex on the worlds.
Source: mandate § 7 (`Δ(W)`)
Kind: D
Fidelity: exact -/
def Simplex (ι : Type) [Fintype ι] : Set (ι → ℝ) :=
  {p | (∀ w, 0 ≤ p w) ∧ ∑ w, p w = 1}

/-- The point mass on a world.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def pointMass [DecidableEq ι] (w₀ : ι) : ι → ℝ := fun w => if w = w₀ then 1 else 0

/-- The point mass is on the simplex.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pointMass_mem_simplex [DecidableEq ι] (w₀ : ι) : pointMass w₀ ∈ Simplex ι := by
  refine ⟨fun w => by unfold pointMass; split_ifs <;> norm_num, ?_⟩
  simp [pointMass]

omit [Fintype Φ] in
/-- The induced price under a point mass is the payout.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma induced_pointMass [DecidableEq ι] (pay : ι → Φ → ℝ) (w₀ : ι) (φ : Φ) :
    induced pay (pointMass w₀) φ = pay w₀ φ := by
  simp [induced, pointMass]

/-! ## The cell setting -/

/-- The payout table of the cell setting: the sentence `none` is the coordinate `φ`, `some r` is
the cell literal `lit r`; the world `(b, r₀)` holds `φ` iff `b` and holds exactly `lit r₀`.
Source: mandate § 7 ("the plausible worlds all assignments with exactly one `lit r` true")
Kind: D
Fidelity: exact -/
def cellPay (m : ℕ) : Bool × Fin m → Option (Fin m) → ℝ
  | (b, _), none => if b then 1 else 0
  | (_, r₀), some r => if r = r₀ then 1 else 0

/-- **The bundle trade**: buy one share of `φ`, sell `rep r` shares of each cell literal
(bli-soto-b-025's bundle, the trade of the market's own self-trust constraint).
Source: bli-soto-b-025; mandate § 7 (`t := (φ ↦ 1, lit r ↦ −rep r)`)
Kind: D
Fidelity: exact -/
def bundleTrade {m : ℕ} (rep : Fin m → ℝ) : Option (Fin m) → ℝ
  | none => 1
  | some r => - rep r

/-- **The constrained set**: simplex points whose induced prices satisfy `D_NNUcell` at the
coordinate — `∑ r, rep r · p(lit r) = p(φ)`.
Source: mandate § 7 (`K`); [[bli-program]] §3.8
Kind: D
Fidelity: exact -/
def Constrained {m : ℕ} (rep : Fin m → ℝ) : Set (Bool × Fin m → ℝ) :=
  {p | p ∈ Simplex (Bool × Fin m) ∧
    ∑ r, rep r * induced (cellPay m) p (some r) = induced (cellPay m) p none}

/-- **The slack-`ε` constrained set**: `|∑ r, rep r · p(lit r) − p(φ)| ≤ ε`.
Source: mandate § 7 (`K_ε`)
Kind: D
Fidelity: exact -/
def ConstrainedSlack {m : ℕ} (rep : Fin m → ℝ) (ε : ℝ) : Set (Bool × Fin m → ℝ) :=
  {p | p ∈ Simplex (Bool × Fin m) ∧
    |∑ r, rep r * induced (cellPay m) p (some r) - induced (cellPay m) p none| ≤ ε}

/-- **The value of the bundle trade in the world `(b, r₀)`** is
`1[b] − rep r₀ − (p(φ) − ∑ r, rep r · p(lit r))`: the world's own payoff minus the constraint.
Source: mandate § 7 ("the value in `w₀` equals `(1[φ] − rep(cell of w₀)) − (p φ − ∑ rep · p(lit))`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem tradeValue_bundle {m : ℕ} (rep : Fin m → ℝ) (p : Bool × Fin m → ℝ) (b : Bool)
    (r₀ : Fin m) :
    tradeValue (cellPay m) (bundleTrade rep) p (b, r₀) =
      (if b then 1 else 0) - rep r₀ -
        (induced (cellPay m) p none - ∑ r, rep r * induced (cellPay m) p (some r)) := by
  have key : ∀ r, bundleTrade rep (some r) *
      (cellPay m (b, r₀) (some r) - induced (cellPay m) p (some r)) =
      -(if r = r₀ then rep r else 0) + rep r * induced (cellPay m) p (some r) := by
    intro r
    simp only [bundleTrade, cellPay]
    split_ifs <;> ring
  unfold tradeValue
  rw [Fintype.sum_option, Finset.sum_congr rfl (fun r _ => key r), Finset.sum_add_distrib,
    Finset.sum_neg_distrib, Finset.sum_ite_eq' Finset.univ r₀ fun r => rep r]
  simp only [bundleTrade, cellPay, Finset.mem_univ, if_true]
  ring

/-- **M4's obstruction theorem.** For every constrained price `p ∈ K` and every cell `r₀`, the
bundle trade is worth exactly `1 − rep r₀` in the plausible world `(φ true, lit r₀ true)` —
independent of `p`. Hence, as soon as some cell has `rep r₀ < 1`, **no constrained price is
acceptable**: the per-day market-maker search restricted to `K` cannot deliver exact `D_NNUcell`
(the static route to an infinite base with exact self-trust is closed).
Source: [[bli-program]] §3.8 (M4); cf. bli-soto-a-058 (ii), a *different* constraint (same-day sharp-indicator introspection; findings F5); [[bli-program]]
§3.8 (M4), §4 row M4, §7 item 10; mandate § 7 (judged item 4)
Kind: P
Fidelity: exact
Hyps: (a); `rep r₀ < 1` is the non-vacuity guard (with every `rep = 1` the theorem is empty) -/
theorem obstruction {m : ℕ} (rep : Fin m → ℝ) {p : Bool × Fin m → ℝ} (hp : p ∈ Constrained rep)
    {r₀ : Fin m} (hr : rep r₀ < 1) : ¬ Acceptable (cellPay m) (bundleTrade rep) p := by
  intro hacc
  have h := hacc (true, r₀)
  rw [tradeValue_bundle, hp.2] at h
  simp at h
  linarith

/-- The exact value, stated for the record: `1 − rep r₀` on `K`.
Source: mandate § 7
Kind: L
Fidelity: n/a -/
theorem tradeValue_bundle_constrained {m : ℕ} (rep : Fin m → ℝ) {p : Bool × Fin m → ℝ}
    (hp : p ∈ Constrained rep) (r₀ : Fin m) :
    tradeValue (cellPay m) (bundleTrade rep) p (true, r₀) = 1 - rep r₀ := by
  rw [tradeValue_bundle, hp.2]
  simp

/-- **The slack form**: on `K_ε` the value in `(φ true, lit r₀ true)` is at least
`1 − rep r₀ − ε`, so the obstruction survives every `ε < 1 − rep r₀`.
Source: mandate § 7 ("exactness is not what breaks it; per-day constraint is")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem obstruction_slack {m : ℕ} (rep : Fin m → ℝ) {ε : ℝ} {p : Bool × Fin m → ℝ}
    (hp : p ∈ ConstrainedSlack rep ε) (r₀ : Fin m) :
    1 - rep r₀ - ε ≤ tradeValue (cellPay m) (bundleTrade rep) p (true, r₀) := by
  rw [tradeValue_bundle]
  have := (abs_le.1 hp.2).1
  simp only [if_true]
  linarith

/-- No slack-`ε` constrained price is acceptable when `ε < 1 − rep r₀`.
Source: mandate § 7
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem obstruction_of_slack {m : ℕ} (rep : Fin m → ℝ) {ε : ℝ} {p : Bool × Fin m → ℝ}
    (hp : p ∈ ConstrainedSlack rep ε) {r₀ : Fin m} (hr : ε < 1 - rep r₀) :
    ¬ Acceptable (cellPay m) (bundleTrade rep) p := by
  intro hacc
  have := hacc (true, r₀)
  have := obstruction_slack rep hp r₀
  linarith

/-! ## The artifact check -/

/-- The two-point price: mass `rep r₀` on `(φ true, lit r₀)` and `1 − rep r₀` on
`(φ false, lit r₀)`.
Source: mandate § 7 (`K` non-empty)
Kind: D
Fidelity: n/a -/
noncomputable def twoPoint {m : ℕ} (rep : Fin m → ℝ) (r₀ : Fin m) : Bool × Fin m → ℝ :=
  fun w => if w = (true, r₀) then rep r₀ else if w = (false, r₀) then 1 - rep r₀ else 0

/-- Sum over `Bool × Fin m` of a function supported on the two worlds of cell `r₀`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_twoPoint_mul {m : ℕ} (rep : Fin m → ℝ) (r₀ : Fin m) (g : Bool × Fin m → ℝ) :
    ∑ w, twoPoint rep r₀ w * g w = rep r₀ * g (true, r₀) + (1 - rep r₀) * g (false, r₀) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [twoPoint, ite_mul]

/-- **The constrained set is non-empty** whenever `rep r₀ ∈ [0,1]`: the two-point price has
`p(φ) = rep r₀`, `p(lit r₀) = 1`, so `∑ rep · p(lit) = rep r₀ = p(φ)`.
Source: mandate § 7 ("`K` is non-empty"); [[STANDARDS]] §3 (artifact check)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem constrained_nonempty {m : ℕ} (rep : Fin m → ℝ) (r₀ : Fin m) (h0 : 0 ≤ rep r₀)
    (h1 : rep r₀ ≤ 1) : twoPoint rep r₀ ∈ Constrained rep := by
  refine ⟨⟨fun w => ?_, ?_⟩, ?_⟩
  · unfold twoPoint; split_ifs <;> linarith
  · have := sum_twoPoint_mul rep r₀ (fun _ => 1)
    simpa using this
  · simp only [induced, sum_twoPoint_mul, cellPay]
    have : ∀ r : Fin m, rep r * ((rep r₀ * if r = r₀ then (1 : ℝ) else 0) +
        (1 - rep r₀) * if r = r₀ then (1 : ℝ) else 0) = if r = r₀ then rep r else 0 := by
      intro r; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun r _ => this r), Finset.sum_ite_eq' Finset.univ r₀ fun r => rep r]
    simp

/-- **The contrast lemma — on the unconstrained simplex the bundle trade has an acceptable
point**: the point mass on `(φ true, lit rmin true)` at a cell of minimal representative. In
the world `(b, r)` the value is `1[b] − rep r − (1 − rep rmin) ≤ rep rmin − rep r ≤ 0`.
Source: mandate § 7 ("the contrast lemma (P) — the artifact check [[STANDARDS]] §3 demands")
Kind: P
Fidelity: variant: the acceptable point is the point mass at a cell of *minimal* representative (the mandate's "`rep r_max = 1`" point mass is not acceptable: in `(φ true, lit r)` with `rep r < 1` its value is `1 − rep r > 0`; findings F6)
Hyps: (a) -/
theorem contrast_acceptable {m : ℕ} (rep : Fin m → ℝ) (rmin : Fin m)
    (hmin : ∀ r, rep rmin ≤ rep r) :
    Acceptable (cellPay m) (bundleTrade rep) (pointMass (true, rmin)) := by
  rintro ⟨b, r⟩
  rw [tradeValue_bundle, induced_pointMass]
  have hsum : ∑ r', rep r' * induced (cellPay m) (pointMass (true, rmin)) (some r') = rep rmin := by
    simp only [induced_pointMass, cellPay]
    rw [Finset.sum_congr rfl (g := fun r' => if r' = rmin then rep r' else 0)]
    · simp
    · intro r' _
      split_ifs <;> ring
  rw [hsum]
  simp only [cellPay, if_true]
  have := hmin r
  cases b <;> simp <;> linarith

/-- The contrast point is **not** constrained when `rep rmin < 1`: its `p(φ) = 1` while
`∑ rep · p(lit) = rep rmin`.
Source: mandate § 7
Kind: L
Fidelity: n/a -/
theorem contrast_not_constrained {m : ℕ} (rep : Fin m → ℝ) (rmin : Fin m) (hr : rep rmin < 1) :
    pointMass (true, rmin) ∉ Constrained rep := by
  intro hp
  have h := hp.2
  simp only [induced_pointMass, cellPay] at h
  rw [Finset.sum_congr rfl (g := fun r' => if r' = rmin then rep r' else 0)] at h
  · simp at h
    linarith
  · intro r' _
    split_ifs <;> ring

/-- **The obstruction is not an artifact** (packaged): for a coordinate with some cell below `1`
and a cell of minimal representative, `K` is non-empty, the bundle trade has an acceptable
point on the simplex, and no point of `K` is acceptable.
Source: mandate § 7; [[STANDARDS]] §3
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem obstruction_package {m : ℕ} (rep : Fin m → ℝ) (r₀ rmin : Fin m)
    (h0 : 0 ≤ rep r₀) (h1 : rep r₀ < 1) (hmin : ∀ r, rep rmin ≤ rep r) :
    (Constrained rep).Nonempty ∧
    (∃ p ∈ Simplex (Bool × Fin m), Acceptable (cellPay m) (bundleTrade rep) p) ∧
    ∀ p ∈ Constrained rep, ¬ Acceptable (cellPay m) (bundleTrade rep) p :=
  ⟨⟨_, constrained_nonempty rep r₀ h0 h1.le⟩,
    ⟨_, pointMass_mem_simplex _, contrast_acceptable rep rmin hmin⟩,
    fun _ hp => obstruction rep hp h1⟩

/-- **A numeral instance** (two cells, midpoint representatives `1/4`, `3/4`): the obstruction
package at the grid of bli-soto-b-025.
Source: bli-soto-b-025 (the `n = 1` bundle market); mandate § 7 ("discharge it at the grid")
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem obstruction_two_cells :
    let rep : Fin 2 → ℝ := ![1 / 4, 3 / 4]
    (Constrained rep).Nonempty ∧
    (∃ p ∈ Simplex (Bool × Fin 2), Acceptable (cellPay 2) (bundleTrade rep) p) ∧
    ∀ p ∈ Constrained rep, ¬ Acceptable (cellPay 2) (bundleTrade rep) p := by
  intro rep
  refine obstruction_package rep 0 0 (by simp [rep]) (by norm_num [rep]) ?_
  intro r
  fin_cases r <;> norm_num [rep]

end Cleanroom.Bli.BliExactBase.Obstruction
