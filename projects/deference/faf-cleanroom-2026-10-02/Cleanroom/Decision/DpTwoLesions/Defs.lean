import Cleanroom.Decision.DpSmokingLesion
import Cleanroom.Decision.DpLocalOpt

/-!
# `dp-two-lesions`: definitions of record — the double lesion over `dp-core-tree`

Package `Cleanroom.Decision.DpTwoLesions` (area `decision`). This file holds the definitions of
record of [[dp-two-lesions-mandate]] §3: the parameters, the worlds, the two trees (`bypass`,
`overwrite`) and their lifts, the label, the law-derived penalty `Δ`, the best response, (H),
and the instances. Every number in the package is a theorem about `nu` on these trees.

## Modelling choices, disclosed once here

* **Scalars** are a linearly ordered field `K` (so the dynamics files run over `ℝ` on the *same*
  `Δ` the tree defines; `norm_num` cells instantiate `K := ℚ`). `FinDistr.coin`/`bool` of the
  catalogue are `ℚ`-only, so `coinK`/`boolK`/`procBoolK` are their `K`-generic copies
  (`procBoolK_eq_procBool` at `K := ℚ`).
* **Worlds** are `DlW := DlState × Bool × Bool` (`(s, m, k)`: state, act, cancer) with the
  ternary state `L | A | N` (doc Definition 2). The anti-lesion is the whole point, so
  `dp-core-tree`'s lesion-only `overwrite` (`OwW`) and `dp-causal-consist`'s `bypassTree` are
  the one-sided ancestors, not reused.
* **The label** is `procBoolK p`. A policy exists only for `p ∈ [0, 1]`; `nuP P p X` is `ν` of
  `X` under `procBoolK p` on `overwrite P` when `0 ≤ p ≤ 1` and **`0` otherwise** — a junk
  value at non-policies, disclosed here; every theorem of the package is stated on `Icc 0 1` and
  reads `nuP` only there (`nuP_eq`). `Delta`, `VP`, `obs` are built from `nuP`, never from a
  closed form.
* **Divisions in `Δ`** are honest because `nuP P p evSmoke > 0` and `nuP P p evAbstain > 0` for
  every `p ∈ [0, 1]` (`Laws.lean`, from `δL, δA > 0`); nothing is stated at grip `0` (the
  `δ → 0` claims are limits, `Corollary.lean`).
* **Ties**: `bestResp` is `[0, 1]` at `Δ(p) = α` (the doc's `β(p)`); the dynamics are stated for
  trajectories that never tie, and discharged at the doc's numbers by irrationality.
* **Fidelity**: the trees are custom `dp-core-tree` trees (plan rule 10), not a `(c)`; the
  payoff `α[m] − β[k]` is the doc's "utilities add".
-/

namespace Cleanroom.Decision.DpTwoLesions

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## `K`-generic coins and the label -/

/-- The coin `(p, 1 − p)` on `Fin 2` (index `0` = "yes"), over any ordered field.
Source: none: infrastructure (the `K`-generic copy of `FinDistr.coin`)
Kind: D -/
def coinK (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) : FinDistr K (Fin 2) where
  w := ![p, 1 - p]
  nonneg := by
    intro i; fin_cases i
    · simpa using h0
    · simp; linarith
  sum_one := by simp [Fin.sum_univ_two]

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem coinK_w (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) (i : Fin 2) :
    (coinK p h0 h1).w i = if i = 0 then p else 1 - p := by
  fin_cases i <;> simp [coinK]

/-- The mixed action `(q, 1 − q)` on `Bool` (`true ↦ q`), over any ordered field.
Source: none: infrastructure (the `K`-generic copy of `FinDistr.bool`)
Kind: D -/
def boolK (q : K) (h0 : 0 ≤ q) (h1 : q ≤ 1) : FinDistr K Bool where
  w b := if b then q else 1 - q
  nonneg b := by cases b <;> simp <;> linarith
  sum_one := by simp

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem boolK_w (q : K) (h0 : 0 ≤ q) (h1 : q ≤ 1) (b : Bool) :
    (boolK q h0 h1).w b = if b then q else 1 - q := rfl

/-- **The label**: the one-point procedure `C(d)(smoke) = p` on `Bool`-acts (`true` = smoke).
Source: [[two-lesions-doc-2026-09-18]] §3 Definition 2 ("A policy is a probability `p ∈ [0, 1]`
of smoking when acting on policy"); `dp-core-tree`'s `procBool` made `K`-generic
Kind: D -/
def procBoolK (q : K) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Proc Unit (fun _ => Bool) K :=
  fun _ => boolK q h0 h1

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem procBoolK_w (q : K) (h0 : 0 ≤ q) (h1 : q ≤ 1) (b : Bool) :
    (procBoolK q h0 h1 ()).w b = if b then q else 1 - q := rfl

/-- At `K := ℚ` the generic label is `dp-core-tree`'s `procBool`.
Source: none: infrastructure
Kind: L -/
theorem procBoolK_eq_procBool (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    procBoolK q h0 h1 = procBool q h0 h1 := by
  funext d; ext b; cases b <;> rfl

/-! ## Parameters -/

/-- **The double-lesion parameters** (general `γ`): lesion rate `ρ`, anti-lesion rate `ρA`,
grips `δL`, `δA`, cancer rates `γ₁` (with the lesion) and `γ₀` (without), payoffs `α` (smoking)
and `β` (cancer, a cost), with the doc's bounds. The doc is `γ = (1, 0)`, `δL = δA`, `π := α`,
`C := β`.
Source: [[two-lesions-doc-2026-09-18]] §3 Definition 2; [[double-lesion]] (general-`γ` forms)
Kind: D
Fidelity: stronger: general `γ₁ ≥ γ₀` and two grips (the doc's case is `docP`) -/
structure DlParams (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  /-- The lesion rate `ε_L`. -/
  ρ : K
  /-- The anti-lesion rate `ε_A`. -/
  ρA : K
  /-- The lesion's grip. -/
  δL : K
  /-- The anti-lesion's grip. -/
  δA : K
  /-- The cancer rate with the lesion. -/
  γ₁ : K
  /-- The cancer rate without the lesion. -/
  γ₀ : K
  /-- The pleasure of smoking `π`. -/
  α : K
  /-- The cost of cancer `C`. -/
  β : K
  ρ_pos : 0 < ρ
  ρA_pos : 0 < ρA
  ρ_add_ρA_lt_one : ρ + ρA < 1
  δL_pos : 0 < δL
  δL_le_one : δL ≤ 1
  δA_pos : 0 < δA
  δA_le_one : δA ≤ 1
  γ₀_nonneg : 0 ≤ γ₀
  γ₀_le_γ₁ : γ₀ ≤ γ₁
  γ₁_le_one : γ₁ ≤ 1
  α_pos : 0 < α
  β_pos : 0 < β

namespace DlParams

variable (P : DlParams K)

/-- `κ := 1 − ρδL − ρAδA`, the mass of the runs that act on policy ("compliers").
Source: [[two-lesions-doc-2026-09-18]] §3 ("`κ = 1 − δ(ε_L + ε_A)`"); [[double-lesion]]
Kind: D -/
def kappa : K := 1 - P.ρ * P.δL - P.ρA * P.δA

/-- The compliers' cancer *mass* `κ·c_C = ρ(1−δL)γ₁ + (ρA(1−δA) + 1 − ρ − ρA)γ₀`.
Source: [[double-lesion]] (`c_C`); [[iv-design-draw-as-instrument]] §2 (B1)
Kind: D -/
def kcC : K := P.ρ * (1 - P.δL) * P.γ₁ + (P.ρA * (1 - P.δA) + 1 - P.ρ - P.ρA) * P.γ₀

/-- The compliers' cancer rate `c_C := κc_C / κ`.
Source: [[double-lesion]] (`c_C`)
Kind: D -/
def cC : K := P.kcC / P.kappa

/-- `0 < κ`. Source: none: infrastructure. Kind: L -/
theorem kappa_pos : 0 < P.kappa := by
  unfold kappa
  have h1 : P.ρ * P.δL ≤ P.ρ := by nlinarith [P.ρ_pos, P.δL_le_one]
  have h2 : P.ρA * P.δA ≤ P.ρA := by nlinarith [P.ρA_pos, P.δA_le_one]
  linarith [P.ρ_add_ρA_lt_one]

/-- `1 − ρ − ρA > 0`. Source: none: infrastructure. Kind: L -/
theorem one_sub_pos : 0 < 1 - P.ρ - P.ρA := by linarith [P.ρ_add_ρA_lt_one]

/-- `0 ≤ κc_C`. Source: none: infrastructure. Kind: L -/
theorem kcC_nonneg : 0 ≤ P.kcC := by
  unfold kcC
  have := P.one_sub_pos
  have h1 : 0 ≤ P.ρ * (1 - P.δL) := mul_nonneg P.ρ_pos.le (by linarith [P.δL_le_one])
  have h2 : 0 ≤ P.ρA * (1 - P.δA) := mul_nonneg P.ρA_pos.le (by linarith [P.δA_le_one])
  have h3 : 0 ≤ P.γ₁ := le_trans P.γ₀_nonneg P.γ₀_le_γ₁
  nlinarith [P.γ₀_nonneg]

/-- `κc_C ≤ κγ₁` (the compliers' rate is at most `γ₁`). Source: none: infrastructure. Kind: L -/
theorem kcC_le_kappa_mul : P.kcC ≤ P.kappa * P.γ₁ := by
  unfold kcC kappa
  have h2 : 0 ≤ P.ρA * (1 - P.δA) := mul_nonneg P.ρA_pos.le (by linarith [P.δA_le_one])
  have := P.one_sub_pos
  nlinarith [P.γ₀_le_γ₁]

/-- `κγ₀ ≤ κc_C`. Source: none: infrastructure. Kind: L -/
theorem kappa_mul_le_kcC : P.kappa * P.γ₀ ≤ P.kcC := by
  unfold kcC kappa
  have h1 : 0 ≤ P.ρ * (1 - P.δL) := mul_nonneg P.ρ_pos.le (by linarith [P.δL_le_one])
  nlinarith [P.γ₀_le_γ₁]

/-- The state weights `(ρ, ρA, 1 − ρ − ρA)` indexed by `Fin 3` (`0 = L`, `1 = A`, `2 = N`).
Source: [[two-lesions-doc-2026-09-18]] §3 Definition 2
Kind: D -/
def stateW : Fin 3 → K := ![P.ρ, P.ρA, 1 - P.ρ - P.ρA]

/-- The root chance over the three states.
Source: [[two-lesions-doc-2026-09-18]] §3 Definition 2
Kind: D -/
def stateDistr : FinDistr K (Fin 3) where
  w := P.stateW
  nonneg := by
    intro i; fin_cases i <;> simp [stateW]
    · exact P.ρ_pos.le
    · exact P.ρA_pos.le
    · linarith [P.ρ_add_ρA_lt_one]
  sum_one := by simp [stateW, Fin.sum_univ_three]

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem stateDistr_w (i : Fin 3) : P.stateDistr.w i = P.stateW i := rfl

/-- The grip at each state: `δL` on `L`, `δA` on `A`, `0` on `N`.
Source: [[two-lesions-doc-2026-09-18]] §3 Definition 2
Kind: D -/
def force : Fin 3 → K := ![P.δL, P.δA, 0]

/-- The cancer rate at each state: `γ₁` on `L`, `γ₀` elsewhere.
Source: [[two-lesions-doc-2026-09-18]] §3 Definition 2 ("cancer … iff it is in `L`", at
`γ = (1, 0)`); [[double-lesion]]
Kind: D -/
def gam : Fin 3 → K := ![P.γ₁, P.γ₀, P.γ₀]

/-- `0 ≤ force i`. Source: none: infrastructure. Kind: L -/
theorem force_nonneg (i : Fin 3) : 0 ≤ P.force i := by
  fin_cases i <;> simp [force] <;> linarith [P.δL_pos, P.δA_pos]

/-- `force i ≤ 1`. Source: none: infrastructure. Kind: L -/
theorem force_le_one (i : Fin 3) : P.force i ≤ 1 := by
  fin_cases i <;> simp [force] <;> linarith [P.δL_le_one, P.δA_le_one]

/-- `0 ≤ gam i`. Source: none: infrastructure. Kind: L -/
theorem gam_nonneg (i : Fin 3) : 0 ≤ P.gam i := by
  fin_cases i <;> simp [gam] <;> linarith [P.γ₀_nonneg, P.γ₀_le_γ₁]

/-- `gam i ≤ 1`. Source: none: infrastructure. Kind: L -/
theorem gam_le_one (i : Fin 3) : P.gam i ≤ 1 := by
  fin_cases i <;> simp [gam] <;> linarith [P.γ₀_le_γ₁, P.γ₁_le_one]

/-- The payoff `α[m] − β[k]`.
Source: [[two-lesions-doc-2026-09-18]] §3 Definition 2 ("Smoking yields utility `π`; cancer
yields `−C`; utilities add")
Kind: D -/
def pay (m k : Bool) : K := (if m then P.α else 0) - (if k then P.β else 0)

end DlParams

/-! ## Worlds and events -/

/-- The three mutually exclusive states.
Source: [[two-lesions-doc-2026-09-18]] §3 Definition 2
Kind: D -/
inductive DlState : Type
  | L | A | N
  deriving DecidableEq, Fintype, Repr

/-- The state at index `i : Fin 3`. Source: none: infrastructure. Kind: D -/
def stateOf : Fin 3 → DlState
  | ⟨0, _⟩ => .L
  | ⟨1, _⟩ => .A
  | ⟨_ + 2, _⟩ => .N

/-- Worlds `(s, m, k)`: state, act (`true` = smoke), cancer.
Source: [[two-lesions-doc-2026-09-18]] §3 ("the measure on triples (state, act, outcome)")
Kind: D -/
abbrev DlW : Type := DlState × Bool × Bool

/-- The act event `{m = a}`. Source: doc §3. Kind: D -/
def evAct (a : Bool) : Finset DlW := Finset.univ.filter fun w => w.2.1 = a

/-- `{smoke}`. Source: doc §3. Kind: D -/
abbrev evSmoke : Finset DlW := evAct true

/-- `{abstain}`. Source: doc §3. Kind: D -/
abbrev evAbstain : Finset DlW := evAct false

/-- `{cancer}`. Source: doc §3. Kind: D -/
def evCancer : Finset DlW := Finset.univ.filter fun w => w.2.2 = true

/-- `{state = s}`. Source: doc §3. Kind: D -/
def evState (s : DlState) : Finset DlW := Finset.univ.filter fun w => w.1 = s

/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evAct (a : Bool) (w : DlW) : w ∈ evAct a ↔ w.2.1 = a := by simp [evAct]

/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evCancer (w : DlW) : w ∈ evCancer ↔ w.2.2 = true := by simp [evCancer]

/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evState (s : DlState) (w : DlW) : w ∈ evState s ↔ w.1 = s := by simp [evState]

/-- `O_d = ⊤`: the untagged agent observes nothing before acting.
Source: [[two-lesions-doc-2026-09-18]] §6 Definition 3 ("Neither kind of agent observes the
state directly"); v2 (S3)
Kind: D -/
def dlObs : Unit → Finset DlW := fun _ => Finset.univ

/-- The action events `{m = ·}` on the act algebra. Source: v2 (S1). Kind: D -/
def dlActEv : Unit → Bool → Finset DlW := fun _ a => evAct a

/-- The realized act on the overwrite tree: the lesion (`i = 0`) firing (`j = 0`) writes
smoke, the anti-lesion (`i = 1`) firing writes abstention, else the draw `m'` stands.
Source: [[two-lesions-doc-2026-09-18]] §3 Definition 2 ("smokes regardless of its policy");
[[smoking-lesion-exploration-and-boundaries]] §1 (the overwrite tree)
Kind: D -/
def actOf (i : Fin 3) (m' : Bool) (j : Fin 2) : Bool :=
  if i = 0 ∧ j = 0 then true else if i = 1 ∧ j = 0 then false else m'

/-! ## The trees -/

namespace DlParams

variable (P : DlParams K)

/-- The cancer block at state index `i` with realized act `m`: `k ∼ Bern(γ_i)`, leaf
`(s_i, m, k)`, payoff `α[m] − β[k]`.
Source: [[two-lesions-doc-2026-09-18]] §3 Definition 2
Kind: D -/
def kBlock (i : Fin 3) (m : Bool) : Tree DlW Unit (fun _ => Bool) K :=
  .chance 2 (coinK (P.gam i) (P.gam_nonneg i) (P.gam_le_one i)) fun k =>
    .leaf (stateOf i, m, decide (k = 0)) (P.pay m (decide (k = 0)))

/-- **The overwrite tree**: root chance over the state; `d` is consulted on every run, drawing
`m'`; a post-draw coin fires with probability `force i` and, when it fires, overwrites the
draw (`L ↦ smoke`, `A ↦ abstain`); then the cancer block. `#_d = 1` on every run;
action-veridicality fails on the forced runs.
Source: [[two-lesions-doc-2026-09-18]] §3 Definition 2 read as
[[smoking-lesion-exploration-and-boundaries]] §1's overwrite tree;
[[iv-design-draw-as-instrument]] §0 ("the IV mapping … needs the overwrite reading")
Kind: D -/
def overwrite : Tree DlW Unit (fun _ => Bool) K :=
  .chance 3 P.stateDistr fun i =>
    .decision () fun m' =>
      .chance 2 (coinK (P.force i) (P.force_nonneg i) (P.force_le_one i)) fun j =>
        P.kBlock i (actOf i m' j)

/-- The branch below a forcing coin on the bypass tree: fired (`j = 0`) goes to the cancer
block with the forced act **without a `d`-node**; not fired consults `d`.
Source: [[smoking-lesion-exploration-and-boundaries]] §1 (the bypass tree)
Kind: D -/
def bypassBranch (i : Fin 3) (forcedAct : Bool) : Fin 2 → Tree DlW Unit (fun _ => Bool) K
  | ⟨0, _⟩ => P.kBlock i forcedAct
  | ⟨_ + 1, _⟩ => .decision () fun m => P.kBlock i m

/-- The subtree of the bypass tree at each state: `L` and `A` carry the forcing coin, `N` the
decision alone.
Source: [[smoking-lesion-exploration-and-boundaries]] §1
Kind: D -/
def bypassState : Fin 3 → Tree DlW Unit (fun _ => Bool) K
  | ⟨0, _⟩ => .chance 2 (coinK P.δL P.δL_pos.le P.δL_le_one) (P.bypassBranch 0 true)
  | ⟨1, _⟩ => .chance 2 (coinK P.δA P.δA_pos.le P.δA_le_one) (P.bypassBranch 1 false)
  | ⟨_ + 2, _⟩ => .decision () fun m => P.kBlock 2 m

/-- **The bypass tree**: root chance over the state; on `L` (resp. `A`) a chance `δL` (`δA`)
sends the run to the cancer block with `m := smoke` (`abstain`) **without consulting `d`**;
otherwise `d` is consulted and the draw is the act. Coverage fails (`#_d = 0` on forced runs).
Source: [[two-lesions-doc-2026-09-18]] §3 Definition 2 read as
[[smoking-lesion-exploration-and-boundaries]] §1's bypass tree
Kind: D -/
def bypass : Tree DlW Unit (fun _ => Bool) K :=
  .chance 3 P.stateDistr P.bypassState

end DlParams

/-! ## The label's law, the penalty, the best response -/

namespace DlParams

variable (P : DlParams K)

/-- `ν` under the label `p` on the overwrite tree, as a total function of `p`: the run law's
world-marginal for `p ∈ [0, 1]`, and **`0` outside** (no policy exists there; every theorem of
the package reads this only on `Icc 0 1`, through `nuP_eq`).
Source: [[two-lesions-doc-2026-09-18]] §3 ("Write `P_p` for the measure … induced by policy
`p`"), rendered as Definition 6's `ν` on the overwrite tree
Kind: D
Fidelity: exact on `[0, 1]`; junk `0` outside, disclosed -/
def nuP (p : K) (X : Finset DlW) : K :=
  if h : 0 ≤ p ∧ p ≤ 1 then nu (procBoolK p h.1 h.2) P.overwrite X else 0

/-- `nuP` on `[0, 1]` is `ν` under the label. Source: none: infrastructure. Kind: L -/
theorem nuP_eq {p : K} (h0 : 0 ≤ p) (h1 : p ≤ 1) (X : Finset DlW) :
    P.nuP p X = nu (procBoolK p h0 h1) P.overwrite X := by
  unfold nuP; rw [dif_pos ⟨h0, h1⟩]

/-- The value `V(p)` under the label `p` on the overwrite tree (total as `nuP`).
Source: dp-core-092 (the policy value); [[decision-problems-v2]] Definition 6 (`V_B(C)`)
Kind: D
Fidelity: exact on `[0, 1]`; junk `0` outside, disclosed -/
def VP (p : K) : K :=
  if h : 0 ≤ p ∧ p ≤ 1 then value (procBoolK p h.1 h.2) P.overwrite else 0

/-- `VP` on `[0, 1]`. Source: none: infrastructure. Kind: L -/
theorem VP_eq {p : K} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    P.VP p = value (procBoolK p h0 h1) P.overwrite := by
  unfold VP; rw [dif_pos ⟨h0, h1⟩]

/-- **The evidential penalty** `Δ(p) := C·[P_p(cancer | smoke) − P_p(cancer | abstain)]`, each
conditional a quotient of `ν`'s on the overwrite tree under the label `p` (**from `nu`**, not a
closed form; `Laws.lean` proves the closed form and the positivity of both denominators on
`[0, 1]`).
Source: [[two-lesions-doc-2026-09-18]] §3 (the display `Δ(p)`)
Kind: D
Fidelity: exact -/
def Delta (p : K) : K :=
  P.β * (P.nuP p (evCancer ∩ evSmoke) / P.nuP p evSmoke -
    P.nuP p (evCancer ∩ evAbstain) / P.nuP p evAbstain)

/-- **The best response** `β(p)`: `{1}` if `π > Δ(p)`, `{0}` if `π < Δ(p)`, `[0, 1]` if equal.
Source: [[two-lesions-doc-2026-09-18]] §3 ("Define the best response `β(p)` …")
Kind: D
Fidelity: exact -/
def bestResp (p : K) : Set K :=
  {b | (P.α > P.Delta p → b = 1) ∧ (P.α < P.Delta p → b = 0) ∧ 0 ≤ b ∧ b ≤ 1}

/-- **A fixed point**: `p ∈ β(p)`.
Source: [[two-lesions-doc-2026-09-18]] §3 ("A policy `p*` is a fixed point if `p* ∈ β(p*)`")
Kind: D
Fidelity: exact -/
def IsFixedPt (p : K) : Prop := p ∈ P.bestResp p

/-- The fixed-point set in `[0, 1]`. Source: doc §4 Proposition 3(iii). Kind: D -/
def fixedPts : Set K := {p ∈ Set.Icc 0 1 | P.IsFixedPt p}

/-- **(H)**, general-`γ` form: `π < C(γ₁ − γ₀)·min(ε_L, 1 − ε_L)`; at `γ = (1, 0)` it is the
doc's display.
Source: [[two-lesions-doc-2026-09-18]] §4 ("(H) `π < C·min(ε_L, 1 − ε_L)`")
Kind: D
Fidelity: exact at `γ = (1, 0)`; the general-`γ` form is [[double-lesion]]'s -/
def HypH : Prop := P.α < P.β * (P.γ₁ - P.γ₀) * min P.ρ (1 - P.ρ)

end DlParams

/-! ## Instances -/

/-- The doc's parameters at grip `δ`: `ε_L = ε_A = 1/5`, `γ = (1, 0)`, `π = 1`, `C = 100`.
Source: [[two-lesions-doc-2026-09-18]] §4 ("with `ε_L = ε_A = 0.2`, `C = 100`, `π = 1`")
Kind: D -/
def docP (δ : K) (h0 : 0 < δ) (h1 : δ ≤ 1) : DlParams K where
  ρ := 1/5
  ρA := 1/5
  δL := δ
  δA := δ
  γ₁ := 1
  γ₀ := 0
  α := 1
  β := 100
  ρ_pos := by norm_num
  ρA_pos := by norm_num
  ρ_add_ρA_lt_one := by norm_num
  δL_pos := h0
  δL_le_one := h1
  δA_pos := h0
  δA_le_one := h1
  γ₀_nonneg := le_refl 0
  γ₀_le_γ₁ := zero_le_one
  γ₁_le_one := le_refl 1
  α_pos := zero_lt_one
  β_pos := by norm_num

/-- The session note's parameters: `ρ = ρA = 1/10`, `δ = 1/20`, `γ = (3/5, 1/20)`, `α = 1`,
`β = 10`; (H) fails here (`β·ρ·(γ₁ − γ₀) = 11/20 < 1`).
Source: [[iv-design-draw-as-instrument]] §2 ("Parameters of the note's §1");
[[smoking-lesion-exploration-and-boundaries]] §1
Kind: D -/
def sessP : DlParams K where
  ρ := 1/10
  ρA := 1/10
  δL := 1/20
  δA := 1/20
  γ₁ := 3/5
  γ₀ := 1/20
  α := 1
  β := 10
  ρ_pos := by norm_num
  ρA_pos := by norm_num
  ρ_add_ρA_lt_one := by norm_num
  δL_pos := by norm_num
  δL_le_one := by norm_num
  δA_pos := by norm_num
  δA_le_one := by norm_num
  γ₀_nonneg := by norm_num
  γ₀_le_γ₁ := by norm_num
  γ₁_le_one := by norm_num
  α_pos := by norm_num
  β_pos := by norm_num

/-- `P` with both grips set to `δ` when `0 < δ ≤ 1`, and `P` itself otherwise (so that
`δ ↦ withGrip P δ` is a total family for the `δ → 0⁺` limits; the junk branch is never
reached within `𝓝[>] 0 ∩ (0, 1]`).
Source: [[two-lesions-doc-2026-09-18]] §4 Proposition 3 ("as `δ → 0`")
Kind: D
Fidelity: exact on `(0, 1]`; junk `P` outside, disclosed -/
def DlParams.withGrip (P : DlParams K) (δ : K) : DlParams K :=
  if h : 0 < δ ∧ δ ≤ 1 then
    { P with δL := δ, δA := δ, δL_pos := h.1, δL_le_one := h.2, δA_pos := h.1, δA_le_one := h.2 }
  else P

/-- `docP δ = (docP 1).withGrip δ`. Source: none: infrastructure. Kind: L -/
theorem docP_eq_withGrip (δ : K) (h0 : 0 < δ) (h1 : δ ≤ 1) :
    docP δ h0 h1 = (docP (1 : K) zero_lt_one le_rfl).withGrip δ := by
  unfold DlParams.withGrip; rw [dif_pos ⟨h0, h1⟩]; rfl

end Cleanroom.Decision.DpTwoLesions
