import Cleanroom.Decision.DpTwoLesions.Lift

/-!
# T11 — Corollary D′ with a coupling: compliance types, LATE, ATE, Egan's variant

The uncoupled estimands (`Lift.lean`: first stage `κ`, ITT on cancer `0`, ITT on payoff `ακ`,
Wald `α`) need no coupling. Compliance types, the LATE and the ATE do: a v2 tree has no
canonical "same run under a different draw" (IV note, Corollary D′), so this file builds the
**coupled trees** — the forcing coin and a three-outcome **cancer-type** coin are drawn *before*
the draw, and the leaf records them — on which every run has potential acts `m(a′) = actOf`
for both draws and potential cancer `k(m) = potK c m` for both acts. **This coupling is a
modelling substitution, disclosed as `(c)`** (mandate trap 7): the note says "couple the
post-draw chance"; the *monotone* coupling (cancer type `0` = cancer under either act, `1` =
cancer only if smoking, `2` = cancer under neither; weights `(γ₀, γ₁ − γ₀, 1 − γ₁)` where the
act matters) is ours. Its honesty check is `coupled_marginal`: the coupled double lesion's law
on the full world `(s, m′, forced, m, k)` is exactly `overwriteFull`'s, for every procedure
and every event — the coupling adds potential outcomes and changes nothing observable.

* `coupledTree P T` — the tree with cancer types `T` (a `CancerTypes`: weights per state).
  `overwriteCoupled P := coupledTree P (dlTypes P)` (cancer `γ_i` under either act: type `1`
  has weight `0`); `eganCoupled P := coupledTree P (eganTypes P)` — **Egan's variant, our
  reconstruction** (dp-core-2-005's flag: the IV note describes it in a clause, "smoking causes
  cancer iff lesion"): on `L` the types have weights `(γ₀, γ₁ − γ₀, 1 − γ₁)`, elsewhere
  `(γ₀, 0, 1 − γ₀)`, so cancer has rate `γ₁` on `L ∧ smoke` and `γ₀` otherwise
  (`egan_cancer_L_smoke`, `egan_cancer_L_abstain`, `egan_cancer_notL`).
* Compliance types from the potential acts (`potAct`): `IsComplier`, `IsAlwaysTaker`,
  `IsNeverTaker`, `IsDefier`; **`noDefiers`** (forcing is to a fixed act); the complier mass is
  `κ` for every procedure (`complier_mass`).
* The estimands as quotients of `expW`/`paySum`/`nu` on the coupled tree (`late`, `ate`, `itt`,
  `firstStage`, `wald`; never closed forms by definition), their closed forms at every label
  (`late_eq`, `ate_eq`, `itt_eq`, `firstStage_eq`), and the identities **`itt = κ · late`**
  (`itt_eq_kappa_mul_late`, for every cancer-type law), **`wald = late`** (`wald_eq_late`), and
  `sign itt = sign late`. On the double lesion `late = ate = α`; on Egan's variant
  `late = α − βρ(1−δL)(γ₁−γ₀)/κ`, `ate = α − βρ(γ₁−γ₀)`, `itt = κ·late`.
* The note's fractions at the session parameters (`sessP`, `p = ½`): Egan `late = 17/36`,
  `itt = 187/400`, `ate = 9/20` (IV note (B5)); the double lesion `late = 1`, `itt = 99/100`.

Serves [[dp-two-lesions-mandate]] T11 (dp-core-095, 2-001(iii), 2-005); repair round 1 (audit
r1: fidelity B2 item 1, adversarial B2).
-/

namespace Cleanroom.Decision.DpTwoLesions

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Coupled worlds, potential outcomes, compliance types -/

/-- Coupled worlds `(s, forced, c, m′, m, k)`: state, the forcing coin's outcome, the cancer
type `c : Fin 3` (`0` = cancer under either act, `1` = cancer only if smoking, `2` = cancer
under neither), the draw, the realized act, the realized cancer.
Source: [[iv-design-draw-as-instrument]] §4 Corollary D′ ("every run has potential acts
`m(a′)` … compliance types are defined"); mandate T11 (the monotone coupling)
Kind: D
Fidelity: variant: the coupling is ours, (c) -/
abbrev DlWc : Type := DlState × Bool × Fin 3 × Bool × Bool × Bool

/-- The potential cancer outcome of type `c` under act `m`: type `0` always, type `1` iff
smoking, type `2` never.
Source: mandate T11 ("a three-outcome cancer coin `(both, only-if-smoke, neither)`")
Kind: D -/
def potK (c : Fin 3) (m : Bool) : Bool := decide (c = 0 ∨ (c = 1 ∧ m = true))

/-- Reductions of `potK`. Source: none: infrastructure. Kind: L -/
@[simp] theorem potK_zero (m : Bool) : potK 0 m = true := by cases m <;> decide
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem potK_one (m : Bool) : potK 1 m = m := by cases m <;> decide
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem potK_two (m : Bool) : potK 2 m = false := by cases m <;> decide

/-- The potential act under draw `a′` at state `s` with forcing outcome `f`: a fired forcing
writes the state's act (`smoke` iff `s = L`), otherwise the draw stands.
Source: [[iv-design-draw-as-instrument]] §4 Corollary D′ ("potential acts `m(a′)`")
Kind: D -/
def potAct (s : DlState) (f : Bool) (a' : Bool) : Bool := if f then decide (s = .L) else a'

/-- The potential act at a leaf is `actOf` at the leaf's draw. Source: none: infrastructure.
Kind: L -/
theorem potAct_eq (i : Fin 3) (j : Fin 2) (a' : Bool) :
    potAct (stateOf i) (forcedOf i j) a' = actOf i a' j := by
  fin_cases i <;> fin_cases j <;> cases a' <;> rfl

/-- **Complier**: `m(1) = 1` and `m(0) = 0`. Source: IV note Corollary D′ (Angrist–Imbens–Rubin
types). Kind: D -/
def IsComplier (w : DlWc) : Prop := potAct w.1 w.2.1 true = true ∧ potAct w.1 w.2.1 false = false
/-- **Always-taker**: `m(1) = m(0) = 1`. Source: IV note Corollary D′. Kind: D -/
def IsAlwaysTaker (w : DlWc) : Prop :=
  potAct w.1 w.2.1 true = true ∧ potAct w.1 w.2.1 false = true
/-- **Never-taker**: `m(1) = m(0) = 0`. Source: IV note Corollary D′. Kind: D -/
def IsNeverTaker (w : DlWc) : Prop :=
  potAct w.1 w.2.1 true = false ∧ potAct w.1 w.2.1 false = false
/-- **Defier**: `m(1) = 0` and `m(0) = 1`. Source: IV note Corollary D′. Kind: D -/
def IsDefier (w : DlWc) : Prop := potAct w.1 w.2.1 true = false ∧ potAct w.1 w.2.1 false = true

instance (w : DlWc) : Decidable (IsComplier w) := by unfold IsComplier; infer_instance
instance (w : DlWc) : Decidable (IsAlwaysTaker w) := by unfold IsAlwaysTaker; infer_instance
instance (w : DlWc) : Decidable (IsNeverTaker w) := by unfold IsNeverTaker; infer_instance
instance (w : DlWc) : Decidable (IsDefier w) := by unfold IsDefier; infer_instance

/-- A complier is an unforced run. Source: none: infrastructure. Kind: L -/
theorem isComplier_iff (w : DlWc) : IsComplier w ↔ w.2.1 = false := by
  rcases w with ⟨s, f, c, m', m, k⟩
  cases f <;> cases s <;> simp [IsComplier, potAct]

/-- An always-taker is a forced run in `L`. Source: none: infrastructure. Kind: L -/
theorem isAlwaysTaker_iff (w : DlWc) : IsAlwaysTaker w ↔ w.2.1 = true ∧ w.1 = .L := by
  rcases w with ⟨s, f, c, m', m, k⟩
  cases f <;> cases s <;> simp [IsAlwaysTaker, potAct]

/-- A never-taker is a forced run outside `L` (on the tree, in `A`: `N` never forces).
Source: none: infrastructure. Kind: L -/
theorem isNeverTaker_iff (w : DlWc) : IsNeverTaker w ↔ w.2.1 = true ∧ w.1 ≠ .L := by
  rcases w with ⟨s, f, c, m', m, k⟩
  cases f <;> cases s <;> simp [IsNeverTaker, potAct]

/-- **No defiers**: forcing is to a fixed act, so no world has `m(1) = 0` and `m(0) = 1`.
Source: [[iv-design-draw-as-instrument]] §4 Corollary D′ ("no run is a defier when forcing is
to a fixed action")
Kind: P
Fidelity: exact (on every coupled world, not only the reachable ones)
Hyps: none -/
theorem noDefiers : ∀ w : DlWc, ¬ IsDefier w := by
  rintro ⟨s, f, c, m', m, k⟩ ⟨h1, h2⟩
  cases f <;> cases s <;> simp [potAct] at h1 h2

/-- The complier event. Source: IV note Corollary D′. Kind: D -/
def evComplier : Finset DlWc := univ.filter IsComplier
/-- The defier event (empty, `noDefiers`). Source: IV note Corollary D′. Kind: D -/
def evDefier : Finset DlWc := univ.filter IsDefier
/-- The draw event on coupled worlds. Source: IV note §4. Kind: D -/
def evDrawC (a : Bool) : Finset DlWc := univ.filter fun w => w.2.2.2.1 = a
/-- The act event on coupled worlds. Source: doc §3. Kind: D -/
def evActC (a : Bool) : Finset DlWc := univ.filter fun w => w.2.2.2.2.1 = a
/-- The cancer event on coupled worlds. Source: doc §3. Kind: D -/
def evCancerC : Finset DlWc := univ.filter fun w => w.2.2.2.2.2 = true
/-- The state event on coupled worlds. Source: doc §3. Kind: D -/
def evStateC (s : DlState) : Finset DlWc := univ.filter fun w => w.1 = s

/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evComplier (w : DlWc) : w ∈ evComplier ↔ w.2.1 = false := by
  simp [evComplier, isComplier_iff]
/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evDrawC (a : Bool) (w : DlWc) : w ∈ evDrawC a ↔ w.2.2.2.1 = a := by
  simp [evDrawC]
/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evActC (a : Bool) (w : DlWc) : w ∈ evActC a ↔ w.2.2.2.2.1 = a := by
  simp [evActC]
/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evCancerC (w : DlWc) : w ∈ evCancerC ↔ w.2.2.2.2.2 = true := by
  simp [evCancerC]
/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evStateC (s : DlState) (w : DlWc) : w ∈ evStateC s ↔ w.1 = s := by
  simp [evStateC]

/-- The defier event is empty. Source: none: infrastructure. Kind: L -/
theorem evDefier_eq_empty : evDefier = ∅ := by
  rw [evDefier, Finset.filter_eq_empty_iff]
  intro w _
  exact noDefiers w

/-- The projection of a coupled world to the full world `(s, m′, forced, m, k)` (the cancer
type forgotten).
Source: none: infrastructure
Kind: D -/
def projW (w : DlWc) : DlWf := (w.1, w.2.2.2.1, w.2.1, w.2.2.2.2.1, w.2.2.2.2.2)

/-- The preimage of a full-world event under the projection. Source: none: infrastructure.
Kind: D -/
def preC (X : Finset DlWf) : Finset DlWc := univ.filter fun w => projW w ∈ X

/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_preC (X : Finset DlWf) (w : DlWc) : w ∈ preC X ↔ projW w ∈ X := by
  simp [preC]

/-! ## The cancer-type coin and the coupled trees -/

/-- A three-outcome coin with weights `w : Fin 3 → K`. Source: none: infrastructure. Kind: D -/
def triK (w : Fin 3 → K) (hnn : ∀ c, 0 ≤ w c) (hsum : w 0 + w 1 + w 2 = 1) :
    FinDistr K (Fin 3) where
  w := w
  nonneg := hnn
  sum_one := by rw [Fin.sum_univ_three]; exact hsum

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem triK_w (w : Fin 3 → K) (hnn : ∀ c, 0 ≤ w c) (hsum : w 0 + w 1 + w 2 = 1)
    (c : Fin 3) : (triK w hnn hsum).w c = w c := rfl

/-- **A cancer-type law**: for each state index `i`, weights `w i c` of the three cancer types
(non-negative, summing to one).
Source: mandate T11 (the three-outcome cancer coin)
Kind: D -/
structure CancerTypes (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] where
  /-- The weight of type `c` at state index `i`. -/
  w : Fin 3 → Fin 3 → K
  /-- Weights are non-negative. -/
  nonneg : ∀ i c, 0 ≤ w i c
  /-- Weights sum to one at each state. -/
  sum_one : ∀ i, w i 0 + w i 1 + w i 2 = 1

/-- `w i 2 = 1 − w i 0 − w i 1`. Source: none: infrastructure. Kind: L -/
theorem CancerTypes.w_two (T : CancerTypes K) (i : Fin 3) : T.w i 2 = 1 - T.w i 0 - T.w i 1 := by
  have := T.sum_one i; linarith

namespace DlParams

variable (P : DlParams K)

/-- **The coupled tree** with cancer-type law `T`: root chance over the state; the forcing coin
(`force i`); the cancer-type coin (`T.w i`); **then** the decision `d` draws `m′`; the leaf
records `(s, forced, c, m′, m, k)` with `m = actOf i m′ j` and `k = potK c m`, payoff
`α[m] − β[k]`. Every chance node is above the draw, so each run has potential acts `actOf i a′ j`
for both draws and potential cancer `potK c m` for both acts.
Source: [[iv-design-draw-as-instrument]] §4 Corollary D′ ("Couple the post-draw chance across
the edges"); mandate T11
Kind: D
Fidelity: variant: the monotone coupling is ours, (c); its marginal on `(s, m′, forced, m, k)`
is `overwriteFull`'s when `T = dlTypes` (`coupled_marginal`) -/
def coupledTree (T : CancerTypes K) : Tree DlWc Unit (fun _ => Bool) K :=
  .chance 3 P.stateDistr fun i =>
    .chance 2 (coinK (P.force i) (P.force_nonneg i) (P.force_le_one i)) fun j =>
      .chance 3 (triK (T.w i) (T.nonneg i) (T.sum_one i)) fun c =>
        .decision () fun m' =>
          .leaf (stateOf i, forcedOf i j, c, m', actOf i m' j, potK c (actOf i m' j))
            (P.pay (actOf i m' j) (potK c (actOf i m' j)))

/-- **The double lesion's cancer types**: cancer under either act with probability `γ_i`, under
neither otherwise — type `1` (act-dependent cancer) has weight `0`, as cancer reads only the
state.
Source: [[two-lesions-doc-2026-09-18]] §3 Definition 2 (cancer `∼ Bern(γ_s)`)
Kind: D -/
def dlTypes : CancerTypes K where
  w := fun i => ![P.gam i, 0, 1 - P.gam i]
  nonneg := by
    intro i c
    fin_cases c
    · simpa using P.gam_nonneg i
    · simp
    · simp; linarith [P.gam_le_one i]
  sum_one := by intro i; simp

/-- Reductions. Source: none: infrastructure. Kind: L -/
@[simp] theorem dlTypes_w_zero (i : Fin 3) : P.dlTypes.w i 0 = P.gam i := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem dlTypes_w_one (i : Fin 3) : P.dlTypes.w i 1 = 0 := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem dlTypes_w_two (i : Fin 3) : P.dlTypes.w i 2 = 1 - P.gam i := rfl

/-- **The coupled double lesion**: `coupledTree P (dlTypes P)`.
Source: mandate T11 (`overwriteCoupled`)
Kind: D
Fidelity: variant: (c), the coupling; marginal = `overwriteFull` (`coupled_marginal`) -/
def overwriteCoupled : Tree DlWc Unit (fun _ => Bool) K := P.coupledTree P.dlTypes

/-- **Egan's variant's cancer types** (our reconstruction of the IV note's clause "smoking
causes cancer iff lesion"): on `L` the types `(both, only-if-smoke, neither)` have weights
`(γ₀, γ₁ − γ₀, 1 − γ₁)`, so cancer has rate `γ₁` if the agent smokes and `γ₀` if not; on `A` and
`N` the weights are `(γ₀, 0, 1 − γ₀)`.
Source: [[iv-design-draw-as-instrument]] §2 (B5) ("Egan's variant: smoking causes cancer iff
lesion"); dp-core-2-005 (Egan's variant is a clause, not a tree — this tree is the
formalizer's reconstruction, pinned by the note's three fractions)
Kind: D
Fidelity: variant: a reconstruction (the note gives no tree), and the coupling is (c) -/
def eganTypes : CancerTypes K where
  w := fun i => if i = 0 then ![P.γ₀, P.γ₁ - P.γ₀, 1 - P.γ₁] else ![P.γ₀, 0, 1 - P.γ₀]
  nonneg := by
    intro i c
    by_cases hi : i = 0
    · rw [if_pos hi]
      fin_cases c
      · simpa using P.γ₀_nonneg
      · simp; linarith [P.γ₀_le_γ₁]
      · simp; linarith [P.γ₁_le_one]
    · rw [if_neg hi]
      fin_cases c
      · simpa using P.γ₀_nonneg
      · simp
      · simp; linarith [P.γ₀_le_γ₁, P.γ₁_le_one]
  sum_one := by
    intro i
    by_cases hi : i = 0
    · rw [if_pos hi]; simp
    · rw [if_neg hi]; simp

/-- Reductions. Source: none: infrastructure. Kind: L -/
@[simp] theorem eganTypes_w_L_zero : P.eganTypes.w 0 0 = P.γ₀ := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem eganTypes_w_L_one : P.eganTypes.w 0 1 = P.γ₁ - P.γ₀ := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem eganTypes_w_L_two : P.eganTypes.w 0 2 = 1 - P.γ₁ := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem eganTypes_w_A_zero : P.eganTypes.w 1 0 = P.γ₀ := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem eganTypes_w_A_one : P.eganTypes.w 1 1 = 0 := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem eganTypes_w_A_two : P.eganTypes.w 1 2 = 1 - P.γ₀ := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem eganTypes_w_N_zero : P.eganTypes.w 2 0 = P.γ₀ := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem eganTypes_w_N_one : P.eganTypes.w 2 1 = 0 := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem eganTypes_w_N_two : P.eganTypes.w 2 2 = 1 - P.γ₀ := rfl

/-- **Egan's variant, coupled**: `coupledTree P (eganTypes P)`.
Source: mandate T11 (`eganCoupled`); IV note (B5)
Kind: D
Fidelity: variant: a reconstruction, with the coupling (c) -/
def eganCoupled : Tree DlWc Unit (fun _ => Bool) K := P.coupledTree P.eganTypes

/-! ## Leaves, laws, sums -/

/-- A sum over the 36 leaves of `coupledTree P T`. Source: none: infrastructure. Kind: L -/
theorem coupled_sum (T : CancerTypes K) (f : (P.coupledTree T).Leaves → K) :
    ∑ ℓ, f ℓ = ∑ i : Fin 3, ∑ j : Fin 2, ∑ c : Fin 3, ∑ m' : Bool, f ⟨i, j, c, m', ()⟩ := by
  unfold coupledTree at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun m' _ => ?_
  exact sum_leaves_leafK _ _ _

/-- The leaf law of `coupledTree P T`: state weight, forcing coin, cancer-type weight, draw
weight.
Source: Definition 6 on the coupled tree
Kind: L -/
theorem coupled_leafLaw (T : CancerTypes K) (C : Proc Unit (fun _ => Bool) K) (i : Fin 3)
    (j : Fin 2) (c : Fin 3) (m' : Bool) :
    leafLaw C (P.coupledTree T) ⟨i, j, c, m', ()⟩ =
      P.stateW i * (if j = 0 then P.force i else 1 - P.force i) * T.w i c * (C ()).w m' := by
  unfold coupledTree
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, stateDistr_w, coinK_w, triK_w]
  ring

/-- The world at a leaf. Source: none: infrastructure. Kind: L -/
theorem coupled_world (T : CancerTypes K) (i : Fin 3) (j : Fin 2) (c : Fin 3) (m' : Bool) :
    world (P.coupledTree T) ⟨i, j, c, m', ()⟩ =
      (stateOf i, forcedOf i j, c, m', actOf i m' j, potK c (actOf i m' j)) := rfl

/-- The payoff at a leaf. Source: none: infrastructure. Kind: L -/
theorem coupled_payoff (T : CancerTypes K) (i : Fin 3) (j : Fin 2) (c : Fin 3) (m' : Bool) :
    payoff (P.coupledTree T) ⟨i, j, c, m', ()⟩ = P.pay (actOf i m' j) (potK c (actOf i m' j)) :=
  rfl

/-- `ν` on `coupledTree P T` as a 36-term sum. Source: none: infrastructure. Kind: L -/
theorem coupled_nu (T : CancerTypes K) (C : Proc Unit (fun _ => Bool) K) (X : Finset DlWc) :
    nu C (P.coupledTree T) X =
      ∑ i : Fin 3, ∑ j : Fin 2, ∑ c : Fin 3, ∑ m' : Bool,
        if (stateOf i, forcedOf i j, c, m', actOf i m' j, potK c (actOf i m' j)) ∈ X then
          leafLaw C (P.coupledTree T) ⟨i, j, c, m', ()⟩ else 0 := by
  rw [nu_eq_sum, coupled_sum]
  rfl

/-- `paySum` on `coupledTree P T` as a 36-term sum. Source: none: infrastructure. Kind: L -/
theorem coupled_paySum (T : CancerTypes K) (C : Proc Unit (fun _ => Bool) K) (X : Finset DlWc) :
    Cleanroom.Decision.DpCalibration.paySum C (P.coupledTree T) X =
      ∑ i : Fin 3, ∑ j : Fin 2, ∑ c : Fin 3, ∑ m' : Bool,
        if (stateOf i, forcedOf i j, c, m', actOf i m' j, potK c (actOf i m' j)) ∈ X then
          leafLaw C (P.coupledTree T) ⟨i, j, c, m', ()⟩ *
            P.pay (actOf i m' j) (potK c (actOf i m' j))
        else 0 := by
  rw [Cleanroom.Decision.DpCalibration.paySum_eq_sum_ite, coupled_sum]
  rfl

end DlParams

/-- **The expectation of a world function** `𝔼_{μ_{B,C}}[f ∘ λ]` (the `value` with `f` in place
of the payoff; used for potential-outcome contrasts, which are functions of the coupled world).
Source: none: infrastructure (Definition 6's `μ`, integrated against `f`)
Kind: D -/
def expW {Ω : Type} (C : Proc Unit (fun _ => Bool) K) (B : Tree Ω Unit (fun _ => Bool) K)
    (f : Ω → K) : K :=
  ∑ ℓ, leafLaw C B ℓ * f (world B ℓ)

namespace DlParams

variable (P : DlParams K)

/-- `expW` on `coupledTree P T` as a 36-term sum. Source: none: infrastructure. Kind: L -/
theorem coupled_expW (T : CancerTypes K) (C : Proc Unit (fun _ => Bool) K) (f : DlWc → K) :
    expW C (P.coupledTree T) f =
      ∑ i : Fin 3, ∑ j : Fin 2, ∑ c : Fin 3, ∑ m' : Bool,
        leafLaw C (P.coupledTree T) ⟨i, j, c, m', ()⟩ *
          f (stateOf i, forcedOf i j, c, m', actOf i m' j, potK c (actOf i m' j)) := by
  rw [expW, coupled_sum]
  rfl

/-- `#_d = 1` on every run of the coupled tree. Source: none: infrastructure. Kind: L -/
theorem coupled_count (T : CancerTypes K) (ℓ : (P.coupledTree T).Leaves) :
    count () (P.coupledTree T) ℓ = 1 := by
  unfold coupledTree at ℓ ⊢
  rcases ℓ with ⟨i, j, c, m', _⟩
  rfl

/-! ## The coupling is a coupling: the marginal law is `overwriteFull`'s -/

/-- **The coupled double lesion's marginal on `(s, m′, forced, m, k)` is `overwriteFull`'s**,
for every procedure and every event: the cancer-type coin `(γ_i, 0, 1 − γ_i)` evaluated at the
realized act reproduces the cancer coin `Bern(γ_i)`. This is what makes the coupling an honest
`(c)`: it adds potential outcomes and changes nothing observable.
Source: [[iv-design-draw-as-instrument]] §4 Corollary D′ ("Couple the post-draw chance across
the edges"), the coupling's defining property
Kind: P
Fidelity: exact
Hyps: none -/
theorem coupled_marginal (C : Proc Unit (fun _ => Bool) K) (X : Finset DlWf) :
    nu C P.overwriteCoupled (preC X) = nu C P.overwriteFull X := by
  unfold overwriteCoupled
  rw [coupled_nu, full_nu]
  simp only [mem_preC, projW, coupled_leafLaw, full_leafLaw]
  -- reorder the coupled sum to `i, m′, j, c`
  have hre : ∀ (F : Fin 2 → Fin 3 → Bool → K),
      (∑ j, ∑ c, ∑ m', F j c m') = ∑ m', ∑ j, ∑ c, F j c m' := by
    intro F
    calc (∑ j, ∑ c, ∑ m', F j c m') = ∑ j, ∑ m', ∑ c, F j c m' :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ m', ∑ j, ∑ c, F j c m' := Finset.sum_comm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hre]
  refine Finset.sum_congr rfl fun m' _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  fin_cases i <;> fin_cases j <;> cases m' <;>
  · simp only [Fin.sum_univ_three, Fin.sum_univ_two, stateW_zero, stateW_one, stateW_two,
      force_zero, force_one, force_two, gam_zero, gam_one, gam_two, dlTypes_w_zero,
      dlTypes_w_one, dlTypes_w_two, actOf_L_fire, actOf_L_still, actOf_A_fire, actOf_A_still,
      actOf_N, forcedOf_L_fire, forcedOf_L_still, forcedOf_A_fire, forcedOf_A_still, forcedOf_N,
      potK_zero, potK_one, potK_two, Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      one_ne_zero, Fin.reduceEq, if_true, if_false, decide_eq_true_eq, decide_true, decide_false]
    split_ifs <;> ring


/-! ## Egan's variant is "smoking causes cancer iff lesion" -/

/-- **Egan's cells**: on `eganCoupled P` at label `p`, cancer has rate `γ₁` on `L ∧ smoke`
(`ν(k ∧ L ∧ smoke) = γ₁·ν(L ∧ smoke)`), rate `γ₀` on `L ∧ abstain`, and rate `γ₀` on `A` and on
`N` — the clause "smoking causes cancer iff lesion", as masses from `nu`.
Source: [[iv-design-draw-as-instrument]] §2 (B5) ("Egan's variant: smoking causes cancer iff
lesion")
Kind: P
Fidelity: exact (the reconstruction's defining cells)
Hyps: none -/
theorem egan_cells (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    nu (procBoolK p h0 h1) P.eganCoupled (evCancerC ∩ evStateC .L ∩ evActC true) =
      P.γ₁ * (P.ρ * P.δL + P.ρ * (1 - P.δL) * p) ∧
    nu (procBoolK p h0 h1) P.eganCoupled (evStateC .L ∩ evActC true) =
      P.ρ * P.δL + P.ρ * (1 - P.δL) * p ∧
    nu (procBoolK p h0 h1) P.eganCoupled (evCancerC ∩ evStateC .L ∩ evActC false) =
      P.γ₀ * (P.ρ * (1 - P.δL) * (1 - p)) ∧
    nu (procBoolK p h0 h1) P.eganCoupled (evStateC .L ∩ evActC false) =
      P.ρ * (1 - P.δL) * (1 - p) ∧
    nu (procBoolK p h0 h1) P.eganCoupled (evCancerC ∩ evStateC .A) = P.γ₀ * P.ρA ∧
    nu (procBoolK p h0 h1) P.eganCoupled (evCancerC ∩ evStateC .N) =
      P.γ₀ * (1 - P.ρ - P.ρA) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · unfold eganCoupled
    rw [coupled_nu]
    simp only [coupled_leafLaw, procBoolK_w]
    conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two]
    ring

/-! ## The estimands, as quotients on the coupled tree -/

/-- The potential payoff of cancer type `c` under act `m`: `α[m] − β[potK c m]`.
Source: [[iv-design-draw-as-instrument]] §4 Corollary D′ ("potential payoffs `r(m)`")
Kind: D -/
def potPay (c : Fin 3) (m : Bool) : K := P.pay m (potK c m)

/-- The potential-payoff contrast `r(1) − r(0)` at a coupled world (a function of its cancer
type). Source: IV note Corollary D′. Kind: D -/
def contrast (w : DlWc) : K := P.potPay w.2.2.1 true - P.potPay w.2.2.1 false

/-- `r(1) − r(0) = α − β·[c = 1]`: smoking pays `α` and costs `β` exactly on the act-dependent
cancer type. Source: none: infrastructure. Kind: L -/
theorem contrast_eq (w : DlWc) : P.contrast w = P.α - P.β * (if w.2.2.1 = 1 then 1 else 0) := by
  rcases w with ⟨s, f, c, m', m, k⟩
  fin_cases c <;> simp [contrast, potPay, pay]

/-- **LATE**: `𝔼[r(1) − r(0) | complier]`, as `expW` of the complier-restricted contrast over
the complier mass, on `coupledTree P T` under `C`.
Source: [[iv-design-draw-as-instrument]] §4 Corollary D′ ("`E[r(m=1) − r(m=0) | complier]`")
Kind: D
Fidelity: exact on the coupled tree; the coupling is (c) -/
def late (T : CancerTypes K) (C : Proc Unit (fun _ => Bool) K) : K :=
  expW C (P.coupledTree T) (fun w => if IsComplier w then P.contrast w else 0) /
    nu C (P.coupledTree T) evComplier

/-- **ATE**: `𝔼[r(1) − r(0)]` over all runs.
Source: [[iv-design-draw-as-instrument]] §2 (B5) ("ATE over all runs")
Kind: D -/
def ate (T : CancerTypes K) (C : Proc Unit (fun _ => Bool) K) : K :=
  expW C (P.coupledTree T) P.contrast

/-- **ITT on payoff**: `𝔼[r | m′=1] − 𝔼[r | m′=0]` on the coupled tree.
Source: [[iv-design-draw-as-instrument]] §2 (B3), (B5)
Kind: D -/
def itt (T : CancerTypes K) (C : Proc Unit (fun _ => Bool) K) : K :=
  Cleanroom.Decision.DpCalibration.paySum C (P.coupledTree T) (evDrawC true) /
      nu C (P.coupledTree T) (evDrawC true) -
    Cleanroom.Decision.DpCalibration.paySum C (P.coupledTree T) (evDrawC false) /
      nu C (P.coupledTree T) (evDrawC false)

/-- **The first stage**: `P(m=1 | m′=1) − P(m=1 | m′=0)` on the coupled tree.
Source: [[iv-design-draw-as-instrument]] §2 (B3)
Kind: D -/
def firstStage (T : CancerTypes K) (C : Proc Unit (fun _ => Bool) K) : K :=
  nu C (P.coupledTree T) (evActC true ∩ evDrawC true) / nu C (P.coupledTree T) (evDrawC true) -
    nu C (P.coupledTree T) (evActC true ∩ evDrawC false) / nu C (P.coupledTree T) (evDrawC false)

/-- **The Wald ratio** `itt / firstStage`. Source: IV note Corollary D′. Kind: D -/
def wald (T : CancerTypes K) (C : Proc Unit (fun _ => Bool) K) : K := P.itt T C / P.firstStage T C

/-- The unnormalized mass of act-dependent-cancer runs among compliers:
`∑_i stateW i (1 − force i) T.w i 1`. Source: none: infrastructure. Kind: D -/
def typeOneCompliers (T : CancerTypes K) : K :=
  P.ρ * (1 - P.δL) * T.w 0 1 + P.ρA * (1 - P.δA) * T.w 1 1 + (1 - P.ρ - P.ρA) * T.w 2 1

/-- The mass of act-dependent-cancer runs overall: `∑_i stateW i T.w i 1`.
Source: none: infrastructure. Kind: D -/
def typeOneAll (T : CancerTypes K) : K :=
  P.ρ * T.w 0 1 + P.ρA * T.w 1 1 + (1 - P.ρ - P.ρA) * T.w 2 1

/-- A procedure's two draw weights sum to one. Source: none: infrastructure. Kind: L -/
theorem proc_w_sum (C : Proc Unit (fun _ => Bool) K) : (C ()).w true + (C ()).w false = 1 := by
  have := (C ()).sum_one
  rwa [Fintype.sum_bool] at this

/-- **The complier mass is `κ`** for every cancer-type law and every procedure: compliers are
the unforced runs.
Source: [[iv-design-draw-as-instrument]] §2 (B2) ("complier mass `κ`"); Corollary D′
Kind: P
Fidelity: exact
Hyps: none -/
theorem complier_mass (T : CancerTypes K) (C : Proc Unit (fun _ => Bool) K) :
    nu C (P.coupledTree T) evComplier = P.kappa := by
  have hC := proc_w_sum C
  rw [coupled_nu]
  simp only [coupled_leafLaw]
  conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two]
  simp only [T.w_two]
  unfold kappa
  linear_combination (1 - P.ρ * P.δL - P.ρA * P.δA) * hC

/-- **LATE, closed form**: `𝔼[r(1) − r(0) | complier] = α − β·typeOneCompliers/κ` for every
procedure (the compliers' contrast does not read the draw).
Source: [[iv-design-draw-as-instrument]] §2 (B5) ("LATE `= α − β·ρ(1−δ)(γ₁−γ₀)/κ`"), general
cancer-type law
Kind: P
Fidelity: exact
Hyps: none (the coupling (c) is in the object) -/
theorem late_eq (T : CancerTypes K) (C : Proc Unit (fun _ => Bool) K) :
    P.late T C = P.α - P.β * P.typeOneCompliers T / P.kappa := by
  have hC := proc_w_sum C
  have hκ := P.kappa_pos.ne'
  have hN : expW C (P.coupledTree T) (fun w => if IsComplier w then P.contrast w else 0) =
      P.α * P.kappa - P.β * P.typeOneCompliers T := by
    rw [coupled_expW]
    simp only [coupled_leafLaw, isComplier_iff, contrast_eq]
    conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two]
    simp only [T.w_two]
    unfold kappa typeOneCompliers
    linear_combination (P.α * (1 - P.ρ * P.δL - P.ρA * P.δA) -
      P.β * (P.ρ * (1 - P.δL) * T.w 0 1 + P.ρA * (1 - P.δA) * T.w 1 1 +
        (1 - P.ρ - P.ρA) * T.w 2 1)) * hC
  unfold late
  rw [complier_mass, hN, sub_div, mul_div_cancel_right₀ _ hκ]

/-- **ATE, closed form**: `𝔼[r(1) − r(0)] = α − β·typeOneAll`, for every procedure.
Source: [[iv-design-draw-as-instrument]] §2 (B5) ("ATE over all runs")
Kind: P
Fidelity: exact
Hyps: none -/
theorem ate_eq (T : CancerTypes K) (C : Proc Unit (fun _ => Bool) K) :
    P.ate T C = P.α - P.β * P.typeOneAll T := by
  have hC := proc_w_sum C
  unfold ate
  rw [coupled_expW]
  simp only [coupled_leafLaw, contrast_eq]
  conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two]
  simp only [T.w_two]
  unfold typeOneAll
  linear_combination (P.α - P.β * (P.ρ * T.w 0 1 + P.ρA * T.w 1 1 +
    (1 - P.ρ - P.ρA) * T.w 2 1)) * hC

/-- The draw cells on the coupled tree at label `p`: `ν(m′=1) = p`, `ν(m′=0) = 1 − p`,
`ν(m=1 ∧ m′=1) = (1 − ρAδA)p`, `ν(m=1 ∧ m′=0) = ρδL(1−p)`, and the two draw-conditional payoff
masses. Source: none: infrastructure (the coupled copy of `full_draw_cells`/`full_draw_pay`).
Kind: L -/
theorem coupled_draw_cells (T : CancerTypes K) (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    nu (procBoolK p h0 h1) (P.coupledTree T) (evDrawC true) = p ∧
    nu (procBoolK p h0 h1) (P.coupledTree T) (evDrawC false) = 1 - p ∧
    nu (procBoolK p h0 h1) (P.coupledTree T) (evActC true ∩ evDrawC true) =
      (1 - P.ρA * P.δA) * p ∧
    nu (procBoolK p h0 h1) (P.coupledTree T) (evActC true ∩ evDrawC false) =
      P.ρ * P.δL * (1 - p) ∧
    Cleanroom.Decision.DpCalibration.paySum (procBoolK p h0 h1) (P.coupledTree T) (evDrawC true) =
      (P.α * (1 - P.ρA * P.δA) -
        P.β * (P.ρ * P.δL * (T.w 0 0 + T.w 0 1) + P.ρ * (1 - P.δL) * (T.w 0 0 + T.w 0 1) +
          P.ρA * P.δA * T.w 1 0 + P.ρA * (1 - P.δA) * (T.w 1 0 + T.w 1 1) +
          (1 - P.ρ - P.ρA) * (T.w 2 0 + T.w 2 1))) * p ∧
    Cleanroom.Decision.DpCalibration.paySum (procBoolK p h0 h1) (P.coupledTree T) (evDrawC false) =
      (P.α * (P.ρ * P.δL) -
        P.β * (P.ρ * P.δL * (T.w 0 0 + T.w 0 1) + P.ρ * (1 - P.δL) * T.w 0 0 +
          P.ρA * P.δA * T.w 1 0 + P.ρA * (1 - P.δA) * T.w 1 0 +
          (1 - P.ρ - P.ρA) * T.w 2 0)) * (1 - p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [coupled_nu]
    simp only [coupled_leafLaw, procBoolK_w]
    conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two]
    simp only [T.w_two]; ring
  · rw [coupled_nu]
    simp only [coupled_leafLaw, procBoolK_w]
    conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two]
    simp only [T.w_two]; ring
  · rw [coupled_nu]
    simp only [coupled_leafLaw, procBoolK_w]
    conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two]
    simp only [T.w_two]; ring
  · rw [coupled_nu]
    simp only [coupled_leafLaw, procBoolK_w]
    conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two]
    simp only [T.w_two]; ring
  · rw [coupled_paySum]
    simp only [coupled_leafLaw, procBoolK_w]
    conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two, pay]
    simp only [T.w_two]; ring
  · rw [coupled_paySum]
    simp only [coupled_leafLaw, procBoolK_w]
    conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two, pay]
    simp only [T.w_two]; ring

/-- **The first stage is `κ`** on the coupled tree at every interior label.
Source: [[iv-design-draw-as-instrument]] §2 (B3)
Kind: P
Fidelity: exact
Hyps: none -/
theorem firstStage_eq (T : CancerTypes K) (p : K) (h0 : 0 < p) (h1 : p < 1) :
    P.firstStage T (procBoolK p h0.le h1.le) = P.kappa := by
  obtain ⟨d1, d2, d3, d4, -, -⟩ := P.coupled_draw_cells T p h0.le h1.le
  unfold firstStage
  rw [d1, d2, d3, d4, mul_div_assoc, div_self h0.ne', mul_div_assoc, div_self (sub_pos.mpr h1).ne']
  unfold kappa; ring

/-- **ITT on payoff, closed form**: `𝔼[r | m′=1] − 𝔼[r | m′=0] = ακ − β·typeOneCompliers` at every
interior label — the forced runs' contributions cancel between the two draws, the compliers'
contrast is `α − β[c = 1]`.
Source: [[iv-design-draw-as-instrument]] §2 (B3), (B5)
Kind: P
Fidelity: exact
Hyps: none -/
theorem itt_eq (T : CancerTypes K) (p : K) (h0 : 0 < p) (h1 : p < 1) :
    P.itt T (procBoolK p h0.le h1.le) = P.α * P.kappa - P.β * P.typeOneCompliers T := by
  obtain ⟨d1, d2, -, -, y1, y2⟩ := P.coupled_draw_cells T p h0.le h1.le
  unfold itt
  rw [d1, d2, y1, y2, mul_div_assoc, div_self h0.ne', mul_div_assoc, div_self (sub_pos.mpr h1).ne']
  unfold kappa typeOneCompliers; ring

/-- **`ITT = κ · LATE`**, for every cancer-type law and every interior label: the draw moves
exactly the compliers, whose mass is `κ`.
Source: [[iv-design-draw-as-instrument]] §2 (B5) ("ITT = κ·LATE exactly"); Corollary D′
Kind: C
Fidelity: exact (on the coupled tree; the coupling is (c))
Hyps: none -/
theorem itt_eq_kappa_mul_late (T : CancerTypes K) (p : K) (h0 : 0 < p) (h1 : p < 1) :
    P.itt T (procBoolK p h0.le h1.le) = P.kappa * P.late T (procBoolK p h0.le h1.le) := by
  rw [P.itt_eq T p h0 h1, P.late_eq T]
  have hκ := P.kappa_pos.ne'
  field_simp

/-- **`Wald = LATE`** at every interior label (Corollary D′, the Angrist–Imbens–Rubin
identity on the coupled tree).
Source: [[iv-design-draw-as-instrument]] §4 Corollary D′ ("the Wald ratio … equals
`E[r(m=1) − r(m=0) | complier]`")
Kind: C
Fidelity: exact (on the coupled tree; the coupling is (c))
Hyps: none -/
theorem wald_eq_late (T : CancerTypes K) (p : K) (h0 : 0 < p) (h1 : p < 1) :
    P.wald T (procBoolK p h0.le h1.le) = P.late T (procBoolK p h0.le h1.le) := by
  unfold wald
  rw [P.itt_eq_kappa_mul_late T p h0 h1, P.firstStage_eq T p h0 h1]
  exact mul_div_cancel_left₀ _ P.kappa_pos.ne'

/-- **`sign ITT = sign LATE`** (`κ > 0`): the ITT is positive, zero or negative exactly when the
LATE is.
Source: [[iv-design-draw-as-instrument]] §2 (B5) (the sign agreement behind "ITT = κ·LATE")
Kind: C
Fidelity: exact
Hyps: none -/
theorem itt_sign_iff (T : CancerTypes K) (p : K) (h0 : 0 < p) (h1 : p < 1) :
    (0 < P.itt T (procBoolK p h0.le h1.le) ↔ 0 < P.late T (procBoolK p h0.le h1.le)) ∧
    (P.itt T (procBoolK p h0.le h1.le) = 0 ↔ P.late T (procBoolK p h0.le h1.le) = 0) := by
  rw [P.itt_eq_kappa_mul_late T p h0 h1]
  have hκ := P.kappa_pos
  constructor
  · exact mul_pos_iff_of_pos_left hκ
  · constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hκ.ne'
      · exact h
    · intro h; rw [h, mul_zero]

/-! ## The double lesion and Egan's variant -/

/-- **On the double lesion, LATE = ATE = `α`**: cancer reads only the state, so smoking has no
cancer effect on anyone and the compliers' contrast is `α` (Wald = `α`, `Lift.lean`'s
`iv_wald`, is the LATE).
Source: [[iv-design-draw-as-instrument]] §2 (B3) ("Wald = α = 1, the effect of the act on
compliers")
Kind: C
Fidelity: exact
Hyps: none -/
theorem dl_late_ate (C : Proc Unit (fun _ => Bool) K) :
    P.late P.dlTypes C = P.α ∧ P.ate P.dlTypes C = P.α := by
  rw [late_eq, ate_eq]
  simp [typeOneCompliers, typeOneAll]

/-- **On the double lesion, ITT = `ακ`** on the coupled tree (as on `overwriteFull`:
`iv_ittPayoff`).
Source: [[iv-design-draw-as-instrument]] §2 (B3)
Kind: C
Fidelity: exact
Hyps: none -/
theorem dl_itt (p : K) (h0 : 0 < p) (h1 : p < 1) :
    P.itt P.dlTypes (procBoolK p h0.le h1.le) = P.α * P.kappa := by
  rw [P.itt_eq _ p h0 h1]; simp [typeOneCompliers]

/-- **Egan's variant: LATE `= α − βρ(1−δL)(γ₁−γ₀)/κ`** — the act-dependent cancer sits on the
lesion's compliers (mass `ρ(1−δL)`), who are a share `ρ(1−δL)/κ` of the compliers.
Source: [[iv-design-draw-as-instrument]] §2 (B5) ("LATE = 17/36 = α − β·ρ(1−δ)(γ₁−γ₀)/κ")
Kind: C
Fidelity: exact (general `γ`, two grips; the tree is a reconstruction, the coupling (c))
Hyps: none -/
theorem egan_late (C : Proc Unit (fun _ => Bool) K) :
    P.late P.eganTypes C = P.α - P.β * (P.ρ * (1 - P.δL) * (P.γ₁ - P.γ₀)) / P.kappa := by
  rw [late_eq]; simp [typeOneCompliers]

/-- **Egan's variant: ATE `= α − βρ(γ₁−γ₀)`** — over all runs, the act-dependent cancer has
mass `ρ(γ₁−γ₀)`; it differs from the LATE by the lesion-forced always-takers, whom the draw
cannot reach.
Source: [[iv-design-draw-as-instrument]] §2 (B5) ("ATE over all runs = 9/20"; "LATE ≠ ATE because
the lesion-forced always-takers … are not compliers")
Kind: C
Fidelity: exact
Hyps: none -/
theorem egan_ate (C : Proc Unit (fun _ => Bool) K) :
    P.ate P.eganTypes C = P.α - P.β * (P.ρ * (P.γ₁ - P.γ₀)) := by
  rw [ate_eq]; simp [typeOneAll]

/-- **Egan's variant: ITT `= ακ − βρ(1−δL)(γ₁−γ₀) = κ·LATE`**.
Source: [[iv-design-draw-as-instrument]] §2 (B5) ("ITT on payoff = 187/400 … ITT = κ·LATE")
Kind: C
Fidelity: exact
Hyps: none -/
theorem egan_itt (p : K) (h0 : 0 < p) (h1 : p < 1) :
    P.itt P.eganTypes (procBoolK p h0.le h1.le) =
      P.α * P.kappa - P.β * (P.ρ * (1 - P.δL) * (P.γ₁ - P.γ₀)) := by
  rw [P.itt_eq _ p h0 h1]; simp [typeOneCompliers]

/-- **The note's fractions at the session parameters** (`sessP`, label `½`): on Egan's variant
`LATE = 17/36`, `ITT = 187/400`, `ATE = 9/20`, and `ITT = κ·LATE` with `κ = 99/100`; on the
double lesion `LATE = 1 = α` and `ITT = 99/100 = κ`.
Source: [[iv-design-draw-as-instrument]] §2 (B5) and §9 (line 181: "ITT = 187/400; LATE = 17/36;
ATE = 9/20; ITT = kappa*LATE")
Kind: N+
Fidelity: exact -/
theorem egan_sessP_fractions :
    (sessP : DlParams ℚ).late sessP.eganTypes (procBoolK (1/2) (by norm_num) (by norm_num)) =
      17/36 ∧
    (sessP : DlParams ℚ).itt sessP.eganTypes (procBoolK (1/2) (by norm_num) (by norm_num)) =
      187/400 ∧
    (sessP : DlParams ℚ).ate sessP.eganTypes (procBoolK (1/2) (by norm_num) (by norm_num)) =
      9/20 ∧
    (sessP : DlParams ℚ).kappa = 99/100 ∧
    (sessP : DlParams ℚ).late sessP.dlTypes (procBoolK (1/2) (by norm_num) (by norm_num)) = 1 ∧
    (sessP : DlParams ℚ).itt sessP.dlTypes (procBoolK (1/2) (by norm_num) (by norm_num)) =
      99/100 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [egan_late]; simp only [kappa, sessP]; norm_num
  · have h := (sessP : DlParams ℚ).egan_itt (1/2) (by norm_num) (by norm_num)
    rw [h]; simp only [kappa, sessP]; norm_num
  · rw [egan_ate]; simp only [sessP]; norm_num
  · simp only [kappa, sessP]; norm_num
  · exact (dl_late_ate _ _).1
  · have h := (sessP : DlParams ℚ).dl_itt (1/2) (by norm_num) (by norm_num)
    rw [h]; simp only [kappa, sessP]; norm_num

end DlParams

end Cleanroom.Decision.DpTwoLesions
