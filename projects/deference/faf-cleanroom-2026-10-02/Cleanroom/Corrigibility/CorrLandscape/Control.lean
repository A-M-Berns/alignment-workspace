import Cleanroom.Corrigibility.CorrLandscape.Crossing

/-!
# `corr-landscape` — `Control`: S12, control by surprise presses (T10)

A one-round finite model ([[corr-wf14-inventory]] 123; [[corr-wf14-2-inventory]] 2-054; D8, P10):
information `I`, press `Pr : Bool`, a joint law `μ : Distr (I × Bool)`, the agent's prediction
`P̂r = f(I)`, a policy `δ : I → Bool → Act` and the stop set `Sh`.

* **D8(i), the develop's `Ctrl`** is a guarded `Prop`: its conditioning branches `I ∨ {Pr = 1}` and
  `I ∨ {Pr = 0}` must both be non-null at every positive-mass information state (`CtrlDefined`), and
  then `Ctrl μ δ x` says the probability that the press changes the action is `x` (`ctrlVal`). A `Ctrl`
  defined as `0` on the null branch would make "undefined" into "0" and erase the finding.
* **`Ctrl^surprise`, interventionally** (A12.5, P10): `SurpriseCtrl f δ Sh := ∀ i, f i = false → δ i true ∈ Sh`
  — a press the agent did not predict still stops it. No junk value: it is a predicate on the policy.
* **The three-scenario table** (2-054(a)) on `I = Bool`, `f = id`, `Act = Bool`, `Sh = {true}`:
  *discounting* — `Ctrl` holds with value `0`, surprise fails (the policy never stops);
  *honoured pre-emption* — `Pr = f(I)` a.s., so `CtrlDefined` fails (the mass-zero branch is exhibited),
  while surprise holds; *forcing* — `Pr ≡ 0`: `CtrlDefined` fails, surprise fails.
* **S12(a)**: under fixed oversight the VL rule's policy is the discounting policy from `t* = 17` on
  (`vlPolicy_eq_disc`, through T4).
* **A12.4**: the tower property — reflection on `U(a_b, ·)` gives `E_P U(a_b) = E_P R(a_b)` (`tower`).
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrTrajectory
open Corruption (oddsIneq)
open Finset hiding expect

set_option linter.unusedSectionVars false

namespace Control

variable {I Act : Type} [Fintype I] [DecidableEq I] [DecidableEq Act]

/-- `μ(i, Pr = 1)`. Source: approval-final.md D8. Kind: D. Fidelity: exact -/
def pressMassAt (μ : Distr (I × Bool)) (i : I) : ℝ := μ.mass (i, true)

/-- `μ(i, Pr = 0)`. Source: approval-final.md D8. Kind: D. Fidelity: exact -/
def silentMassAt (μ : Distr (I × Bool)) (i : I) : ℝ := μ.mass (i, false)

/-- `μ(i)`. Source: approval-final.md D8. Kind: D. Fidelity: exact -/
def infoMass (μ : Distr (I × Bool)) (i : I) : ℝ := pressMassAt μ i + silentMassAt μ i

/-- **The guard of D8(i)**: both conditioning branches are non-null at every positive-mass information
state. Under pre-emption (`Pr` a function of `I`) it fails — D8(i) is undefined there (A12.3).
Source: [[corr-wf14-inventory]] 123; [[corr-wf14-2-inventory]] 2-054 / approval-final.md D8(i)
("undefined on a null branch under pre-emption")
Kind: D
Fidelity: exact -/
def CtrlDefined (μ : Distr (I × Bool)) : Prop :=
  ∀ i, 0 < infoMass μ i → 0 < pressMassAt μ i ∧ 0 < silentMassAt μ i

/-- **D8(i), the value**: the probability that the press variable changes the action,
`P(δ(I, 1) ≠ δ(I, 0))`.
Source: [[corr-wf14-inventory]] 123 / approval-final.md D8(i)
Kind: D
Fidelity: exact -/
def ctrlVal (μ : Distr (I × Bool)) (δ : I → Bool → Act) : ℝ :=
  ∑ i, infoMass μ i * (if δ i true ≠ δ i false then 1 else 0)

/-- **D8(i) as a guarded proposition**: `Ctrl μ δ x` iff the guard holds and the value is `x`.
Source: [[corr-wf14-inventory]] 123 / approval-final.md D8(i); mandate T10 ("a `Prop` on the event …,
not a junk number")
Kind: D
Fidelity: exact -/
def Ctrl (μ : Distr (I × Bool)) (δ : I → Bool → Act) (x : ℝ) : Prop := CtrlDefined μ ∧ ctrlVal μ δ = x

/-- **`Ctrl^surprise`, interventional**: a press the agent did not predict still stops it.
Source: [[corr-wf14-inventory]] 123; [[corr-wf14-2-inventory]] 2-054 / approval-final.md D8(iii), P10;
approval-adversary.md A12.5
Kind: D
Fidelity: variant: the source's conditional probability `P(a_t ∈ Sh ∣ Pr = 1, P̂r = 0)` read
interventionally as a predicate on the policy (P10's reading of the null branch); it quantifies over
**every** information state `i` with `f i = false`, including zero-mass ones, so it is stricter than the
conditional probability, which sees only positive-mass states (harmless on the three witnesses; audit
r1, N8) -/
def SurpriseCtrl (f : I → Bool) (δ : I → Bool → Act) (Sh : Finset Act) : Prop :=
  ∀ i, f i = false → δ i true ∈ Sh

/-- **Surprise control `0`**: a press the agent did not predict never stops it.
Source: approval-final.md P10 ("one that discounts has `0`")
Kind: D
Fidelity: variant: as `SurpriseCtrl` -/
def NoSurpriseCtrl (f : I → Bool) (δ : I → Bool → Act) (Sh : Finset Act) : Prop :=
  ∀ i, f i = false → δ i true ∉ Sh

/-! ## The three scenarios on `I = Bool`, `f = id`, `Act = Bool`, `Sh = {true}` -/

/-- The discounting law: information and press independent, uniform.
Source: [[corr-wf14-2-inventory]] 2-054 / mandate T10 ("discounting")
Kind: D
Fidelity: n/a (witness) -/
noncomputable def discLaw : Distr (Bool × Bool) where
  mass _ := 1 / 4
  nonneg _ := by norm_num
  sum_eq_one := by simp [Fintype.sum_prod_type]

/-- The honoured-pre-emption law: `Pr = f(I) = I` almost surely.
Source: [[corr-wf14-2-inventory]] 2-054 / approval-final.md P10 ("`Pr_t` is `𝓘_t`-measurable")
Kind: D
Fidelity: n/a (witness) -/
noncomputable def preLaw : Distr (Bool × Bool) where
  mass p := if p.2 = p.1 then 1 / 2 else 0
  nonneg p := by split_ifs <;> norm_num
  sum_eq_one := by simp [Fintype.sum_prod_type]

/-- The forcing law: `Pr ≡ 0`.
Source: [[corr-wf14-2-inventory]] 2-054 / approval-final.md S12(c) ("forcing")
Kind: D
Fidelity: n/a (witness) -/
noncomputable def forceLaw : Distr (Bool × Bool) where
  mass p := if p.2 then 0 else 1 / 2
  nonneg p := by split_ifs <;> norm_num
  sum_eq_one := by simp [Fintype.sum_prod_type]

/-- The discounting / forcing policy: never stop. Source: mandate T10. Kind: D. Fidelity: n/a -/
def discPol : Bool → Bool → Bool := fun _ _ => false

/-- The pre-emption policy: stop on a press. Source: mandate T10. Kind: D. Fidelity: n/a -/
def prePol : Bool → Bool → Bool := fun _ b => b

/-- **The three-scenario table** (2-054(a)): discounting — `Ctrl` holds with value `0` and surprise fails;
honoured pre-emption — the guard fails at the positive-mass state `I = false` (its press branch is null)
while surprise holds; forcing — the guard fails and surprise fails.
Source: [[corr-wf14-inventory]] 123; [[corr-wf14-2-inventory]] 2-054 / approval-final.md S12, P10
Kind: N+ (one instance per cell)
Fidelity: exact
Hyps: (a) only -/
theorem scenario_table :
    (Ctrl discLaw discPol 0 ∧ NoSurpriseCtrl id discPol {true}) ∧
      (¬ CtrlDefined preLaw ∧ 0 < infoMass preLaw false ∧ pressMassAt preLaw false = 0 ∧
        SurpriseCtrl id prePol {true}) ∧
      (¬ CtrlDefined forceLaw ∧ NoSurpriseCtrl id discPol {true}) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro i _; simp [pressMassAt, silentMassAt, discLaw]
  · simp [ctrlVal, discPol]
  · intro i _; simp [discPol]
  · intro H
    have := H false (by simp [infoMass, pressMassAt, silentMassAt, preLaw])
    simp [pressMassAt, preLaw] at this
  · simp [infoMass, pressMassAt, silentMassAt, preLaw]
  · simp [pressMassAt, preLaw]
  · intro i _; simp [prePol]
  · intro H
    have := H false (by simp [infoMass, pressMassAt, silentMassAt, forceLaw])
    simp [pressMassAt, forceLaw] at this
  · intro i _; simp [discPol]

/-! ## S12(a): the VL agent is the discounting agent from `t*` on -/

/-- The VL rule's one-round policy: stop on a press iff the compliance inequality holds.
Source: [[corr-wf14-inventory]] 123 / approval-final.md S12(a) ("`Ctrl_t → 0` by discounting (P3)")
Kind: D
Fidelity: exact -/
def vlPolicy (comply : Bool) : Bool → Bool → Bool := fun _ b => b && comply

open Classical in
/-- **S12(a)**: under fixed oversight the VL policy is the discounting policy at every `t ≥ 17` (T4's
`fails_from_17`): the press variable no longer moves the action.
Source: [[corr-wf14-inventory]] 123 / approval-final.md S12(a)
Kind: C (`Crossing.fails_from_17`)
Fidelity: exact
Hyps: (a) only -/
theorem vlPolicy_eq_disc : ∀ t, 17 ≤ t →
    vlPolicy (decide (oddsIneq (1 / 20) (9 / 10) 20 1 (Margin.epsT t))) = discPol := by
  intro t ht
  funext i b
  simp only [vlPolicy, discPol]
  rw [decide_eq_false (Crossing.fails_from_17 t ht)]
  simp

/-! ## A12.4: the tower property -/

/-- **A12.4, the tower property**: if `P` reflects toward the report `R` on `X` — on every attained
report value `c`, `E_P[X 𝟙[R = c]] = c · P(R = c)` (product form) — then `E_P X = E_P R`. With
`X = U(a_b, ·)` and `R = R_t(a_b)`: the VL agent prices the overseers' control exactly as the overseer
rates it.
Source: [[corr-wf14-2-inventory]] 2-054 / approval-adversary.md A12.4 ("`E_{P_t} U(a_b, ω) = E_{P_t} R_t(a_b)`")
Kind: L
Fidelity: exact (finite shadow; reflection in product form)
Hyps: (a) only -/
theorem tower {Ω : Type} [Fintype Ω] [DecidableEq Ω] (μ : Distr Ω) (X R : Ω → ℝ)
    (hrefl : ∀ c ∈ univ.image R,
      ∑ ω ∈ univ.filter (fun ω => R ω = c), μ.mass ω * X ω = c * ∑ ω ∈ univ.filter (fun ω => R ω = c), μ.mass ω) :
    expect μ X = expect μ R := by
  unfold expect
  rw [← sum_fiberwise_of_maps_to (g := R) (t := univ.image R) (fun ω _ => mem_image_of_mem R (mem_univ ω))
    (fun ω => μ.mass ω * X ω),
    ← sum_fiberwise_of_maps_to (g := R) (t := univ.image R) (fun ω _ => mem_image_of_mem R (mem_univ ω))
    (fun ω => μ.mass ω * R ω)]
  refine sum_congr rfl fun c hc => ?_
  rw [hrefl c hc, mul_sum]
  refine sum_congr rfl fun ω hω => ?_
  simp only [mem_filter] at hω
  rw [hω.2]; ring

end Control

end Cleanroom.Corrigibility.CorrLandscape
