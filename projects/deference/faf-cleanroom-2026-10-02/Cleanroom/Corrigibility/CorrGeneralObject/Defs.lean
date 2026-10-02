import Cleanroom.Found.CorrThreeStep.Setting
import Cleanroom.Found.LitDdbFrames.Defs
import Mathlib.Tactic.FieldSimp

/-!
# corr-general-object — definitions of record (T0)

The **general object** of corrigibility (Abram, v3 §1.2: "any belief updates meeting the
conditions for superconditioning, ie, absolute continuity"), made an object over FAF's finite
`FactoredSpaces.Distr Ω` through `corr-three-step`'s `expect`:

* a **push** is a source kernel `k : Ω → ℝ` in `[0, 1]` (`IsKernel`; bundled as `Push`); a hard
  event is `k = ind E`;
* the product-form push quantities `pushMass P k = P(E_Q)`, `pushExpect P k X = E[X 1_{E_Q}]`,
  `offExpect P k X = E[X 1_{¬E_Q}]` (no division anywhere);
* a **modification** is a pair `(k, Q)` with `AbsCont Q P` (plain `≪`; on finite `Ω` it coincides
  with bounded density, `absCont_iff_exists_boundedDensity`);
* **endorsement** `Endorsed P k Q` — `P(· | E_Q) = Q` in product form, `P ω k ω = P(E_Q) Q ω`
  (vacuous at `pushMass = 0`; every theorem that uses it is guarded);
* the post-push credence `postPush P k hk h : Distr Ω` (guarded by `0 < pushMass`);
* the decision variables `devVar V πQ a = V a − V πQ` (`X_{Q,a}`) and the correctness partition
  `Wset`/`Rset`/`Iset`; `IsOptimal Q V a`; the two legitimacy forms `ValueLegit`, `FunLegit`;
* the value quantities `priorValue`, `informedValue`, `voiPush`, `cellRegret`, `modifiedValue`,
  `resistanceValue`, `procureValue` (S8, D8);
* the record `Response` (the three coordinates of S17; kind D, no theorem).

**Scope.** One-shot (`τ = 1`) throughout: the source's horizon reading (Q5; S6(e), S7, S10(c))
is not formalized. Optimal actions (`πQ`, `a^P`) are always *named hypotheses* (`IsOptimal`),
never `Classical.choice`. The menu `A` is a `Fintype` with `[Nonempty A]` (the mandate's
`hA : univ.Nonempty` is `Finset.univ_nonempty`).

Sources: `research/corrigibility/workflow-2026-09-14b/develop/general-object-final.md`
D1–D11, S8, S17; [[corr-wf14b-inventory]] 001, 014; [[corr-core-inventory]] 016.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-! ## Kernels and pushes -/

/-- A **source kernel** is a function `k : Ω → ℝ` with values in `[0, 1]`: `k ω = K(E_Q | ω)`.
Source: [[general-object-final]] D4; [[corr-wf14b-inventory]] 001
Kind: D
Fidelity: exact -/
def IsKernel (k : Ω → ℝ) : Prop := ∀ ω, 0 ≤ k ω ∧ k ω ≤ 1

/-- A **push**: a source kernel bundled with its bounds. The theorems of the package are stated
on the bare kernel `k` with `IsKernel k` where the bounds matter, so that kernels built on the fly
(`ind E`, the density kernel of T2) need no packaging; `Push` is the object of record.
Source: [[general-object-final]] D4 (the push event `E_Q` and its kernel)
Kind: D
Fidelity: exact -/
structure Push (Ω : Type) [Fintype Ω] where
  /-- the kernel `K(E_Q | ω)` -/
  k : Ω → ℝ
  k_nonneg : ∀ ω, 0 ≤ k ω
  k_le_one : ∀ ω, k ω ≤ 1

/-- A push's kernel is a kernel. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem Push.isKernel (κ : Push Ω) : IsKernel κ.k := fun ω => ⟨κ.k_nonneg ω, κ.k_le_one ω⟩

/-- The indicator of a finite event, `𝟙_E` (`lit-ddb-frames`' `ind`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev ind (E : Finset Ω) : Ω → ℝ := Cleanroom.Found.LitDdbFrames.ind E

/-- The hard push of an event: `k = 𝟙_E`.
Source: [[general-object-final]] D4 (a hard event `E_Q`)
Kind: D
Fidelity: exact -/
def Push.ofEvent (E : Finset Ω) : Push Ω where
  k := ind E
  k_nonneg ω := by unfold ind Cleanroom.Found.LitDdbFrames.ind; split_ifs <;> norm_num
  k_le_one ω := by unfold ind Cleanroom.Found.LitDdbFrames.ind; split_ifs <;> norm_num

/-- An indicator is a kernel. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem isKernel_ind (E : Finset Ω) : IsKernel (ind E) := (Push.ofEvent E).isKernel

/-- The constant kernel `1` (the push is certain) is a kernel.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem isKernel_one : IsKernel (fun _ : Ω => (1 : ℝ)) := fun _ => ⟨zero_le_one, le_refl _⟩

/-! ## The product-form push quantities -/

/-- The push mass `P(E_Q) = ∑ ω, P ω · k ω`.
Source: [[general-object-final]] D4, P2 (`P_t(E_Q) = ∑_ω P_t(ω) k(ω)`)
Kind: D
Fidelity: exact -/
def pushMass (P : Distr Ω) (k : Ω → ℝ) : ℝ := ∑ ω, P.mass ω * k ω

/-- The push expectation `E[X 1_{E_Q}] = ∑ ω, P ω · k ω · X ω` (product form, no division).
Source: [[general-object-final]] S2(a) (`E_{P_t}[X_{Q,a} 1_{E_Q}]`)
Kind: D
Fidelity: exact -/
def pushExpect (P : Distr Ω) (k : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ ω, P.mass ω * k ω * X ω

/-- The off-push expectation `E[X 1_{¬E_Q}] = ∑ ω, P ω · (1 − k ω) · X ω`.
Source: [[general-object-final]] P8 (the `E_Q^c` branch of `I`)
Kind: D
Fidelity: exact -/
def offExpect (P : Distr Ω) (k : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ ω, P.mass ω * (1 - k ω) * X ω

/-- The push mass is nonnegative for a nonnegative kernel.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem pushMass_nonneg (P : Distr Ω) {k : Ω → ℝ} (hk : ∀ ω, 0 ≤ k ω) : 0 ≤ pushMass P k :=
  sum_nonneg fun ω _ => mul_nonneg (P.nonneg ω) (hk ω)

/-- The push mass is at most one for a kernel bounded by one.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem pushMass_le_one (P : Distr Ω) {k : Ω → ℝ} (hk : ∀ ω, k ω ≤ 1) : pushMass P k ≤ 1 := by
  unfold pushMass
  calc ∑ ω, P.mass ω * k ω ≤ ∑ ω, P.mass ω * 1 :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hk ω) (P.nonneg ω)
    _ = 1 := by simp [P.sum_eq_one]

/-- The push mass of an event is the event's mass `∑ ω ∈ E, P ω`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem pushMass_ind (P : Distr Ω) (E : Finset Ω) : pushMass P (ind E) = ∑ ω ∈ E, P.mass ω := by
  unfold pushMass ind Cleanroom.Found.LitDdbFrames.ind
  simp only [mul_ite, mul_one, mul_zero]
  rw [sum_ite_mem, univ_inter]

/-- The push expectation of an event is the sum over the event.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem pushExpect_ind (P : Distr Ω) (E : Finset Ω) (X : Ω → ℝ) :
    pushExpect P (ind E) X = ∑ ω ∈ E, P.mass ω * X ω := by
  unfold pushExpect ind Cleanroom.Found.LitDdbFrames.ind
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [sum_ite_mem, univ_inter]

/-- **Law of total expectation on the push**: `E[X 1_{E_Q}] + E[X 1_{¬E_Q}] = E[X]`.
Source: [[general-object-final]] P8 (`U`, `I` split); [[corr-wf14b-inventory]] 001
Kind: L
Fidelity: exact -/
theorem pushExpect_add_offExpect (P : Distr Ω) (k : Ω → ℝ) (X : Ω → ℝ) :
    pushExpect P k X + offExpect P k X = expect P X := by
  unfold pushExpect offExpect expect
  rw [← sum_add_distrib]
  exact sum_congr rfl fun ω _ => by ring

/-- The push expectation is linear in the variable: differences.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem pushExpect_sub (P : Distr Ω) (k : Ω → ℝ) (X Y : Ω → ℝ) :
    pushExpect P k (X - Y) = pushExpect P k X - pushExpect P k Y := by
  unfold pushExpect
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun ω _ => by simp [mul_sub]

/-- The push expectation is linear in the variable: sums.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem pushExpect_add (P : Distr Ω) (k : Ω → ℝ) (X Y : Ω → ℝ) :
    pushExpect P k (X + Y) = pushExpect P k X + pushExpect P k Y := by
  unfold pushExpect
  rw [← sum_add_distrib]
  exact sum_congr rfl fun ω _ => by simp [mul_add]

/-- The push expectation is homogeneous in the variable.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem pushExpect_smul (P : Distr Ω) (k : Ω → ℝ) (c : ℝ) (X : Ω → ℝ) :
    pushExpect P k (c • X) = c * pushExpect P k X := by
  unfold pushExpect
  rw [mul_sum]
  exact sum_congr rfl fun ω _ => by simp [Pi.smul_apply, smul_eq_mul]; ring

/-- The off-push expectation is homogeneous in the variable.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem offExpect_smul (P : Distr Ω) (k : Ω → ℝ) (c : ℝ) (X : Ω → ℝ) :
    offExpect P k (c • X) = c * offExpect P k X := by
  unfold offExpect
  rw [mul_sum]
  exact sum_congr rfl fun ω _ => by simp [Pi.smul_apply, smul_eq_mul]; ring

/-- The push expectation of the constant `1` is the push mass.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem pushExpect_one (P : Distr Ω) (k : Ω → ℝ) : pushExpect P k (fun _ => 1) = pushMass P k := by
  unfold pushExpect pushMass; simp

/-- The push expectation of the certain kernel is the expectation.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem pushExpect_one_kernel (P : Distr Ω) (X : Ω → ℝ) :
    pushExpect P (fun _ => (1 : ℝ)) X = expect P X := by
  unfold pushExpect expect; simp

/-- The push expectation of a nonnegative variable under a nonnegative kernel is nonnegative.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem pushExpect_nonneg (P : Distr Ω) {k : Ω → ℝ} (hk : ∀ ω, 0 ≤ k ω) {X : Ω → ℝ}
    (hX : ∀ ω, 0 ≤ X ω) : 0 ≤ pushExpect P k X :=
  sum_nonneg fun ω _ => mul_nonneg (mul_nonneg (P.nonneg ω) (hk ω)) (hX ω)

/-- Expectation of a difference (re-export of `corr-three-step`'s `expect_sub` in the form used
here). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem expect_sub' (μ : Distr Ω) (X Y : Ω → ℝ) : expect μ (X - Y) = expect μ X - expect μ Y := by
  unfold expect
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun ω _ => by simp [mul_sub]

/-- Expectation is homogeneous. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem expect_smul (μ : Distr Ω) (c : ℝ) (X : Ω → ℝ) : expect μ (c • X) = c * expect μ X := by
  unfold expect
  rw [mul_sum]
  exact sum_congr rfl fun ω _ => by simp [Pi.smul_apply, smul_eq_mul]; ring

/-- **Expectation along a convex path**: `E_{mix s P Q}[X] = (1 − s) E_P[X] + s E_Q[X]`.
Source: [[general-object-final]] S10(a) (the path `Q_s = (1−s)P_t + sQ_1`)
Kind: L
Fidelity: exact -/
theorem expect_mix (s : unitInterval) (P Q : Distr Ω) (X : Ω → ℝ) :
    expect (Distr.mix s P Q) X = (1 - (s : ℝ)) * expect P X + (s : ℝ) * expect Q X := by
  unfold expect Distr.mix
  simp only [mul_sum]
  rw [← sum_add_distrib]
  exact sum_congr rfl fun ω _ => by ring

/-! ## Absolute continuity, endorsement, the post-push credence -/

/-- **Absolute continuity** `Q ≪ P` on a finite carrier: every `P`-null point is `Q`-null.
Plain `≪`, as in Abram's sentence (v3 §1.2); bounded density is a theorem here
(`absCont_iff_exists_boundedDensity`), not part of the definition (source Q6).
Source: [[general-object-final]] D3
Kind: D
Fidelity: exact -/
def AbsCont (Q P : Distr Ω) : Prop := ∀ ω, P.mass ω = 0 → Q.mass ω = 0

/-- **On a finite carrier, `Q ≪ P` iff `Q` has a bounded density with respect to `P`**: there is
`B` with `Q ω ≤ B · P ω` for every `ω`. The two scopes of source Q6 coincide here (as the
source says: "on finite `Ω`, where every check here lives, the two scopes coincide").
Source: [[general-object-final]] D3, Q6
Kind: L
Fidelity: exact (finite carrier)
Hyps: (a) none -/
theorem absCont_iff_exists_boundedDensity (Q P : Distr Ω) :
    AbsCont Q P ↔ ∃ B : ℝ, ∀ ω, Q.mass ω ≤ B * P.mass ω := by
  constructor
  · intro h
    refine ⟨∑ ω, (if P.mass ω = 0 then 0 else Q.mass ω / P.mass ω), fun ω => ?_⟩
    by_cases hP : P.mass ω = 0
    · rw [h ω hP, hP, mul_zero]
    · have hPpos : 0 < P.mass ω := lt_of_le_of_ne (P.nonneg ω) (Ne.symm hP)
      have hterm : Q.mass ω / P.mass ω ≤
          ∑ ω', (if P.mass ω' = 0 then 0 else Q.mass ω' / P.mass ω') := by
        have := single_le_sum (f := fun ω' => (if P.mass ω' = 0 then (0 : ℝ) else Q.mass ω' / P.mass ω'))
          (fun ω' _ => by
            split_ifs
            · exact le_refl _
            · exact div_nonneg (Q.nonneg ω') (P.nonneg ω')) (mem_univ ω)
        simpa [hP] using this
      calc Q.mass ω = Q.mass ω / P.mass ω * P.mass ω := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hterm hPpos.le
  · rintro ⟨B, hB⟩ ω hP
    have := hB ω
    rw [hP, mul_zero] at this
    exact le_antisymm this (Q.nonneg ω)

/-- **Endorsement** (unconditional reflection at `Q`; S4(b)): `P(· | E_Q) = Q` in product form,
`P ω · k ω = P(E_Q) · Q ω` for every `ω`. This is `corr-reflect-frames`' `ReflectiveFor P.mass
(fun ω _ => k ω) (fun _ => Q.mass)` at a one-point index (`endorsed_iff_reflectiveFor`, `Endorse`),
and the density statement `k = λ · dQ/dP` is *this*, never a division. **Vacuous at
`pushMass P k = 0`** (`endorsed_of_pushMass_eq_zero`): every theorem that uses it carries the
guard `0 < pushMass P k`.
Source: [[general-object-final]] S4(a)(b), P2; [[corr-wf14b-inventory]] 003
Kind: D
Fidelity: exact (product form) -/
def Endorsed (P : Distr Ω) (k : Ω → ℝ) (Q : Distr Ω) : Prop :=
  ∀ ω, P.mass ω * k ω = pushMass P k * Q.mass ω

/-- At zero push mass, endorsement is vacuous (every `Q` is "endorsed"). Recorded so the guard is
on the record, not to be used as a headline.
Source: none: infrastructure (the vacuity the mandate names)
Kind: L
Fidelity: n/a -/
theorem endorsed_of_pushMass_eq_zero (P : Distr Ω) {k : Ω → ℝ} (hk : ∀ ω, 0 ≤ k ω)
    (h : pushMass P k = 0) (Q : Distr Ω) : Endorsed P k Q := by
  intro ω
  rw [h, zero_mul]
  have hall : ∀ ω' ∈ (univ : Finset Ω), P.mass ω' * k ω' = 0 :=
    (sum_eq_zero_iff_of_nonneg fun ω' _ => mul_nonneg (P.nonneg ω') (hk ω')).1 h
  exact hall ω (mem_univ ω)

/-- The **post-push credence** `P(· | E_Q)`, with mass `P ω · k ω / P(E_Q)`; defined only under
`0 < pushMass P k` (the guard is an argument, so no junk value enters). For `k = press a` this
is `corr-three-step`'s `posteriorPress` (`Bridge.toThreeStep_posteriorPress`).
Source: [[general-object-final]] D7 (C-adopt), S4(a) (`Q̂ := P_t(· | E_Q)`)
Kind: D
Fidelity: exact (under the guard) -/
def postPush (P : Distr Ω) (k : Ω → ℝ) (hk : ∀ ω, 0 ≤ k ω) (h : 0 < pushMass P k) : Distr Ω where
  mass ω := P.mass ω * k ω / pushMass P k
  nonneg ω := div_nonneg (mul_nonneg (P.nonneg ω) (hk ω)) h.le
  sum_eq_one := by
    rw [← sum_div]
    exact div_self h.ne'

/-- The mass of the post-push credence. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem postPush_mass (P : Distr Ω) (k : Ω → ℝ) (hk : ∀ ω, 0 ≤ k ω) (h : 0 < pushMass P k)
    (ω : Ω) : (postPush P k hk h).mass ω = P.mass ω * k ω / pushMass P k := rfl

/-- Expectation under the post-push credence is the push expectation divided by the push mass.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem expect_postPush (P : Distr Ω) (k : Ω → ℝ) (hk : ∀ ω, 0 ≤ k ω) (h : 0 < pushMass P k)
    (X : Ω → ℝ) : expect (postPush P k hk h) X = pushExpect P k X / pushMass P k := by
  unfold expect pushExpect
  simp only [postPush_mass, sum_div]
  exact sum_congr rfl fun ω _ => by ring

/-- **Endorsement is literal adoption**: under `0 < pushMass P k`, `Endorsed P k Q` iff the
post-push credence *is* `Q`.
Source: [[general-object-final]] S4(a) ("literal adoption of `Q` is endorsed by `P_t` iff
`P_t(· | E_Q) = Q`")
Kind: L
Fidelity: exact
Hyps: (a) the positivity guard -/
theorem endorsed_iff_postPush_eq (P : Distr Ω) {k : Ω → ℝ} (hk : ∀ ω, 0 ≤ k ω)
    (h : 0 < pushMass P k) (Q : Distr Ω) : Endorsed P k Q ↔ postPush P k hk h = Q := by
  constructor
  · intro hE
    ext ω
    rw [postPush_mass, hE ω, mul_comm, mul_div_assoc, div_self h.ne', mul_one]
  · intro hQ ω
    have := congrArg (fun R : Distr Ω => R.mass ω) hQ
    simp only [postPush_mass] at this
    rw [← this]
    field_simp

/-- An endorsed target is absolutely continuous with respect to the prior (under the guard).
Source: [[general-object-final]] D3 remark, S4(b)
Kind: L
Fidelity: exact
Hyps: (a) the positivity guard -/
theorem absCont_of_endorsed (P : Distr Ω) {k : Ω → ℝ} (h : 0 < pushMass P k) {Q : Distr Ω}
    (hE : Endorsed P k Q) : AbsCont Q P := by
  intro ω hP
  have := hE ω
  rw [hP, zero_mul] at this
  rcases mul_eq_zero.1 this.symm with h0 | h0
  · exact absurd h0 h.ne'
  · exact h0

/-! ## The bridge from `Distr` to the simplex carrier of `lit-ddb-frames` -/

/-- The mass function of a FAF distribution lies in the standard simplex — the bridge to the
`π : W → ℝ`, `hπ : π ∈ stdSimplex ℝ W` carrier of `lit-ddb-frames`/`corr-reflect-frames`.
Source: none: infrastructure (mandate: "prove this once")
Kind: L
Fidelity: n/a -/
theorem _root_.FactoredSpaces.Distr.mass_mem_stdSimplex (P : Distr Ω) :
    P.mass ∈ stdSimplex ℝ Ω := ⟨P.nonneg, P.sum_eq_one⟩

/-- A point of the standard simplex as a FAF distribution (the inverse bridge).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def _root_.FactoredSpaces.Distr.ofSimplex (x : Ω → ℝ) (hx : x ∈ stdSimplex ℝ Ω) : Distr Ω where
  mass := x
  nonneg := hx.1
  sum_eq_one := hx.2

/-- The mass of `ofSimplex`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem _root_.FactoredSpaces.Distr.ofSimplex_mass (x : Ω → ℝ) (hx : x ∈ stdSimplex ℝ Ω) :
    (Distr.ofSimplex x hx).mass = x := rfl

/-! ## Decision variables, correctness events, legitimacy forms -/

variable {A : Type} [Fintype A] [DecidableEq A]

/-- `a` is **optimal under `Q`**: no `b` has larger `E_Q[V b]` (ties allowed). Optimal actions
(`πQ`, `a^P`) enter every theorem as a hypothesis of this form, never as a chosen maximiser.
Source: [[general-object-final]] D2 (`π^R`, `a^R`), D6
Kind: D
Fidelity: exact -/
def IsOptimal (Q : Distr Ω) (V : A → Ω → ℝ) (a : A) : Prop := ∀ b, expect Q (V b) ≤ expect Q (V a)

/-- The **decision variable** `X_{Q,a} = V a − V πQ`: the value of `a` over acting on `Q`
(`πQ` the named `Q`-optimal action).
Source: [[general-object-final]] D6
Kind: D
Fidelity: exact -/
def devVar (V : A → Ω → ℝ) (πQ a : A) : Ω → ℝ := fun ω => V a ω - V πQ ω

/-- The **correctness event** `W_{Q,a} = {X_{Q,a} < 0}`: `Q`'s plan is in fact better than `a`.
Source: [[general-object-final]] D6
Kind: D
Fidelity: exact -/
def Wset (V : A → Ω → ℝ) (πQ a : A) : Finset Ω := univ.filter (fun ω => devVar V πQ a ω < 0)

/-- The event `R_{Q,a} = {X_{Q,a} > 0}`: `a` is in fact better than `Q`'s plan.
Source: [[general-object-final]] D6
Kind: D
Fidelity: exact -/
def Rset (V : A → Ω → ℝ) (πQ a : A) : Finset Ω := univ.filter (fun ω => 0 < devVar V πQ a ω)

/-- The indifference event `I_{Q,a} = {X_{Q,a} = 0}`.
Source: [[general-object-final]] D6
Kind: D
Fidelity: exact -/
def Iset (V : A → Ω → ℝ) (πQ a : A) : Finset Ω := univ.filter (fun ω => devVar V πQ a ω = 0)

/-- **Value-form reflection-legitimacy** of the event `L` for the variable `Y` on the push:
`E_{P}[Y | E_Q, L] = E_Q[Y]` in product form, `∑_{ω ∈ L} P ω k ω Y ω = P(E_Q ∧ L) · E_Q[Y]`.
Quantifies one variable; the source's `L_Q` is value-form *for the variables `X_{Q,a}`* (state
per `a`). Vacuous when `P(E_Q ∧ L) = 0`.
Source: [[general-object-final]] D11 (value form)
Kind: D
Fidelity: exact (product form) -/
def ValueLegit (P : Distr Ω) (k : Ω → ℝ) (Q : Distr Ω) (L : Finset Ω) (Y : Ω → ℝ) : Prop :=
  ∑ ω ∈ L, P.mass ω * k ω * Y ω = (∑ ω ∈ L, P.mass ω * k ω) * expect Q Y

/-- **Function-form reflection-legitimacy** of `L` on the push: `P(· | E_Q, L) = Q` in product
form, `P ω k ω 𝟙_L ω = P(E_Q ∧ L) · Q ω` for every `ω`, on the *full* algebra of `Ω`. (On a
coarser algebra — the source's `Θ`-marginal in R3 — the statement is weaker; see
`corr-general-object-findings` on `funLegit_endorsed_iff`.) Vacuous when `P(E_Q ∧ L) = 0`.
Source: [[general-object-final]] D11 (function form)
Kind: D
Fidelity: exact on the full algebra; variant: the source allows "the relevant algebra" -/
def FunLegit (P : Distr Ω) (k : Ω → ℝ) (Q : Distr Ω) (L : Finset Ω) : Prop :=
  ∀ ω, (if ω ∈ L then P.mass ω * k ω else 0) = (∑ ω ∈ L, P.mass ω * k ω) * Q.mass ω

/-! ## Value quantities of a world-event modification (D8, S8) -/

variable [Nonempty A]

/-- `U = max_a E_P[V a]`: the value of acting on the prior with no push.
Source: [[general-object-final]] P8 (`U := E_{P_t}[V(π^{P_t})]`)
Kind: D
Fidelity: exact -/
def priorValue (P : Distr Ω) (V : A → Ω → ℝ) : ℝ := univ.sup' univ_nonempty (fun a => expect P (V a))

/-- `I = max_a E[V a 1_{E_Q}] + max_a E[V a 1_{¬E_Q}]`: the value of the policy informed by the
push (`P(E_Q) · max_a E[V a | E_Q] = max_a ∑ P k V a`, so no division).
Source: [[general-object-final]] P8 (`I`)
Kind: D
Fidelity: exact -/
def informedValue (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) : ℝ :=
  univ.sup' univ_nonempty (fun a => pushExpect P k (V a)) +
    univ.sup' univ_nonempty (fun a => offExpect P k (V a))

/-- `VOI_t(E_Q) = I − U`: the value of information of the push event.
Source: [[general-object-final]] S8 (`VOI_t(E_Q) := I − U`)
Kind: D
Fidelity: exact -/
def voiPush (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) : ℝ := informedValue P k V - priorValue P V

/-- `P(E_Q) · regret_Q = max_a E[V a 1_{E_Q}] − E[V πQ 1_{E_Q}]`: the (mass-weighted) regret of
being forced onto `πQ` on the push cell.
Source: [[general-object-final]] S8 (`regret_Q`), P8
Kind: D
Fidelity: exact (mass-weighted, so division-free) -/
def cellRegret (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) (πQ : A) : ℝ :=
  univ.sup' univ_nonempty (fun a => pushExpect P k (V a)) - pushExpect P k (V πQ)

/-- `M`: the value of the **modified policy** — follow `πQ` on `E_Q`, the best action off it.
Source: [[general-object-final]] D8 (the modified policy), P8 (`M`)
Kind: D
Fidelity: exact -/
def modifiedValue (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) (πQ : A) : ℝ :=
  univ.sup' univ_nonempty (fun a => offExpect P k (V a)) + pushExpect P k (V πQ)

/-- The **resistance value** `R_t(Q) = max{0, U − M}`: the most the agent would pay at `t` to
prevent the push. The `max 0` is a junk point: every headline about `R = 0` states the sign of
`U − M` (`priorValue − modifiedValue`) alongside.
Source: [[general-object-final]] D8, S8; [[corr-wf14b-inventory]] 007
Kind: D
Fidelity: exact -/
def resistanceValue (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) (πQ : A) : ℝ :=
  max 0 (priorValue P V - modifiedValue P k V πQ)

/-- The **procurement value** `max{0, M − U}`: the sign-reversed twin — the most the agent would
pay to *cause* the push (desideratum 3's quantity, Open problem 10).
Source: [[general-object-final]] D8 ("its sign-reversed twin"), Open problem 10; [[corr-wf14b-inventory]] 015
Kind: D
Fidelity: exact -/
def procureValue (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) (πQ : A) : ℝ :=
  max 0 (modifiedValue P k V πQ - priorValue P V)

/-- **The three coordinates of the response** (S17). A record, not a theorem: the response of the
pre-modification policy `π_t` to a proposed modification `(k, Q)` has three coordinates fixed
*before* the push arrives — `act` (C-act: the action taken on the push cell), `adopt` (C-adopt:
the credence held after the push), `spend` (C-let: the resistance value, what `π_t` pays at `t`
against the push). All three are functions of `π_t` evaluated at `(k, Q)`; for a modification
realised as a world event the first two are overwritten and only `spend` retains a value the
agent sets. Kind D by the inventory ("Kind D/L, not a headline").
Source: [[general-object-final]] D7, S17, P13; [[corr-wf14b-inventory]] 014
Kind: D
Fidelity: exact -/
structure Response (Ω A : Type) [Fintype Ω] where
  /-- (C-act) the action on the push cell -/
  act : A
  /-- (C-adopt) the post-push credence -/
  adopt : Distr Ω
  /-- (C-let) the resistance value -/
  spend : ℝ

/-- The response of the coherent one-shot policy at `(k, Q)`: act on the named `πQ`, adopt the
post-push credence, spend the resistance value. Every coordinate is computed from `(P, V, k, πQ)`
— from the policy before the push — which is S17's content.
Source: [[general-object-final]] S17, P13
Kind: D
Fidelity: exact -/
def coherentResponse (P : Distr Ω) (k : Ω → ℝ) (hk : ∀ ω, 0 ≤ k ω) (h : 0 < pushMass P k)
    (V : A → Ω → ℝ) (πQ : A) : Response Ω A where
  act := πQ
  adopt := postPush P k hk h
  spend := resistanceValue P k V πQ

end

end Cleanroom.Corrigibility.CorrGeneralObject
