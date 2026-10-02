import Cleanroom.Decision.DpTwoLesions.Defs

/-!
# T1 — Explicit forms and the one-law theorem

The leaf sums and leaf laws of `overwrite P` and `bypass P`, the twelve world masses as one
function `dlMass`, the six cells and the three observables as theorems from `nu`, the
positivity of both conditioning events on `[0, 1]`, the closed form of `Δ` (`Delta_eq`), the
one-law theorem (`oneLaw`: the two trees have the same `ν` at every label, world-level) and the
strict monotonicity of the two conditionals.
Serves [[dp-two-lesions-mandate]] T1 (dp-core-072, 083, 2-002).
-/

namespace Cleanroom.Decision.DpTwoLesions

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Sums over the (single) leaf of a leaf tree, over any `K` (the catalogue's
`Tree.sum_leaves_leaf` is `ℚ`-only). Source: none: infrastructure. Kind: L -/
theorem sum_leaves_leafK {Ω ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)]
    {M : Type} [AddCommMonoid M] (ω : Ω) (r : K)
    (f : (Tree.leaf ω r : Tree Ω ι acts K).Leaves → M) : ∑ ℓ, f ℓ = f () := by
  show ∑ ℓ : Unit, f ℓ = f ()
  simp

/-! ## Reductions on the index helpers -/

/-- `stateOf 0 = L`. Source: none: infrastructure. Kind: L -/
@[simp] theorem stateOf_zero : stateOf 0 = .L := rfl
/-- `stateOf 1 = A`. Source: none: infrastructure. Kind: L -/
@[simp] theorem stateOf_one : stateOf 1 = .A := rfl
/-- `stateOf 2 = N`. Source: none: infrastructure. Kind: L -/
@[simp] theorem stateOf_two : stateOf 2 = .N := rfl

/-- The lesion firing writes smoke. Source: none: infrastructure. Kind: L -/
@[simp] theorem actOf_L_fire (m' : Bool) : actOf 0 m' 0 = true := rfl
/-- The lesion not firing leaves the draw. Source: none: infrastructure. Kind: L -/
@[simp] theorem actOf_L_still (m' : Bool) : actOf 0 m' 1 = m' := rfl
/-- The anti-lesion firing writes abstention. Source: none: infrastructure. Kind: L -/
@[simp] theorem actOf_A_fire (m' : Bool) : actOf 1 m' 0 = false := rfl
/-- The anti-lesion not firing leaves the draw. Source: none: infrastructure. Kind: L -/
@[simp] theorem actOf_A_still (m' : Bool) : actOf 1 m' 1 = m' := rfl
/-- `N` never forces. Source: none: infrastructure. Kind: L -/
@[simp] theorem actOf_N (m' : Bool) (j : Fin 2) : actOf 2 m' j = m' := by
  fin_cases j <;> rfl

/-- `∑_{s : DlState} f s = f L + f A + f N`. Source: none: infrastructure. Kind: L -/
theorem sum_dlState (f : DlState → K) : ∑ s, f s = f .L + f .A + f .N := by
  have : (Finset.univ : Finset DlState) = {.L, .A, .N} := by
    ext s; cases s <;> simp
  rw [this, Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
  ring

namespace DlParams

variable (P : DlParams K)

/-- Equation lemmas for the state weights. Source: none: infrastructure. Kind: L -/
@[simp] theorem stateW_zero : P.stateW 0 = P.ρ := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem stateW_one : P.stateW 1 = P.ρA := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem stateW_two : P.stateW 2 = 1 - P.ρ - P.ρA := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem force_zero : P.force 0 = P.δL := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem force_one : P.force 1 = P.δA := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem force_two : P.force 2 = 0 := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem gam_zero : P.gam 0 = P.γ₁ := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem gam_one : P.gam 1 = P.γ₀ := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem gam_two : P.gam 2 = P.γ₀ := rfl

/-! ## The overwrite tree: leaves, laws -/

/-- A sum over the 24 leaves of `overwrite P`. Source: none: infrastructure. Kind: L -/
theorem overwrite_sum (f : P.overwrite.Leaves → K) :
    ∑ ℓ, f ℓ = ∑ i : Fin 3, ∑ m' : Bool, ∑ j : Fin 2, ∑ k : Fin 2, f ⟨i, m', j, k, ()⟩ := by
  unfold overwrite kBlock at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact sum_leaves_leafK _ _ _

/-- The leaf law of `overwrite P` under any procedure: state weight, draw weight, forcing
coin, cancer coin.
Source: [[decision-problems-v2]] Definition 6 on the overwrite tree
Kind: L -/
theorem overwrite_leafLaw (C : Proc Unit (fun _ => Bool) K) (i : Fin 3) (m' : Bool)
    (j k : Fin 2) :
    leafLaw C P.overwrite ⟨i, m', j, k, ()⟩ =
      P.stateW i * (C ()).w m' * (if j = 0 then P.force i else 1 - P.force i) *
        (if k = 0 then P.gam i else 1 - P.gam i) := by
  unfold overwrite kBlock
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, stateDistr_w, coinK_w]
  ring

/-- The world at a leaf of `overwrite P`. Source: none: infrastructure. Kind: L -/
theorem overwrite_world (i : Fin 3) (m' : Bool) (j k : Fin 2) :
    world P.overwrite ⟨i, m', j, k, ()⟩ = (stateOf i, actOf i m' j, decide (k = 0)) := rfl

/-- The payoff at a leaf of `overwrite P`. Source: none: infrastructure. Kind: L -/
theorem overwrite_payoff (i : Fin 3) (m' : Bool) (j k : Fin 2) :
    payoff P.overwrite ⟨i, m', j, k, ()⟩ = P.pay (actOf i m' j) (decide (k = 0)) := rfl

/-- `ν` on `overwrite P` as an explicit 24-term sum. Source: none: infrastructure. Kind: L -/
theorem overwrite_nu (C : Proc Unit (fun _ => Bool) K) (X : Finset DlW) :
    nu C P.overwrite X =
      ∑ i : Fin 3, ∑ m' : Bool, ∑ j : Fin 2, ∑ k : Fin 2,
        if (stateOf i, actOf i m' j, decide (k = 0)) ∈ X then
          leafLaw C P.overwrite ⟨i, m', j, k, ()⟩ else 0 := by
  rw [nu_eq_sum, overwrite_sum]
  rfl

/-- `#_d = 1` on every run of `overwrite P`.
Source: [[iv-design-draw-as-instrument]] §0 ("only the overwrite tree gives every episode a
draw")
Kind: L -/
theorem overwrite_count (ℓ : P.overwrite.Leaves) : count () P.overwrite ℓ = 1 := by
  unfold overwrite kBlock at ℓ ⊢
  rcases ℓ with ⟨i, m', j, k, _⟩
  rfl

/-- `occ(d) = ⊤` on `overwrite P`. Source: none: infrastructure. Kind: L -/
theorem overwrite_occ : occ () P.overwrite = Finset.univ := by
  ext ℓ; simp [overwrite_count]

/-- `overwrite P` is almost fair. Source: none: infrastructure. Kind: L -/
theorem overwrite_almostFair : AlmostFair P.overwrite := by
  intro d ℓ; cases d; rw [overwrite_count]

/-! ## The bypass tree: leaves, laws -/

/-- The sum over the forced branch of a bypass coin. Source: none: infrastructure. Kind: L -/
theorem bypassBranch_sum_fire (i : Fin 3) (fa : Bool) (f : (P.bypassBranch i fa 0).Leaves → K) :
    ∑ ℓ, f ℓ = ∑ k : Fin 2, f ⟨k, ()⟩ := by
  unfold bypassBranch kBlock at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact sum_leaves_leafK _ _ _

/-- The sum over the consulting branch of a bypass coin. Source: none: infrastructure. Kind: L -/
theorem bypassBranch_sum_still (i : Fin 3) (fa : Bool)
    (f : (P.bypassBranch i fa 1).Leaves → K) :
    ∑ ℓ, f ℓ = ∑ m : Bool, ∑ k : Fin 2, f ⟨m, k, ()⟩ := by
  unfold bypassBranch kBlock at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact sum_leaves_leafK _ _ _

/-- The sum over the `L`-subtree of the bypass tree. Source: none: infrastructure. Kind: L -/
theorem bypassState_sum_L (f : (P.bypassState 0).Leaves → K) :
    ∑ ℓ, f ℓ = (∑ k : Fin 2, f ⟨0, k, ()⟩) + ∑ m : Bool, ∑ k : Fin 2, f ⟨1, m, k, ()⟩ := by
  unfold bypassState at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_two]
  have h0 := P.bypassBranch_sum_fire 0 true (fun ℓ => f ⟨0, ℓ⟩)
  have h1 := P.bypassBranch_sum_still 0 true (fun ℓ => f ⟨1, ℓ⟩)
  dsimp only at h0 h1
  rw [h0, h1]

/-- The sum over the `A`-subtree of the bypass tree. Source: none: infrastructure. Kind: L -/
theorem bypassState_sum_A (f : (P.bypassState 1).Leaves → K) :
    ∑ ℓ, f ℓ = (∑ k : Fin 2, f ⟨0, k, ()⟩) + ∑ m : Bool, ∑ k : Fin 2, f ⟨1, m, k, ()⟩ := by
  unfold bypassState at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_two]
  have h0 := P.bypassBranch_sum_fire 1 false (fun ℓ => f ⟨0, ℓ⟩)
  have h1 := P.bypassBranch_sum_still 1 false (fun ℓ => f ⟨1, ℓ⟩)
  dsimp only at h0 h1
  rw [h0, h1]

/-- The sum over the `N`-subtree of the bypass tree. Source: none: infrastructure. Kind: L -/
theorem bypassState_sum_N (f : (P.bypassState 2).Leaves → K) :
    ∑ ℓ, f ℓ = ∑ m : Bool, ∑ k : Fin 2, f ⟨m, k, ()⟩ := by
  unfold bypassState kBlock at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact sum_leaves_leafK _ _ _

/-- A sum over the 20 leaves of `bypass P`: per state, the forced leaves (no `d`-node) and
the consulting leaves.
Source: none: infrastructure
Kind: L -/
theorem bypass_sum (f : P.bypass.Leaves → K) :
    ∑ ℓ, f ℓ =
      ((∑ k : Fin 2, f ⟨0, 0, k, ()⟩) + ∑ m : Bool, ∑ k : Fin 2, f ⟨0, 1, m, k, ()⟩) +
      ((∑ k : Fin 2, f ⟨1, 0, k, ()⟩) + ∑ m : Bool, ∑ k : Fin 2, f ⟨1, 1, m, k, ()⟩) +
      ∑ m : Bool, ∑ k : Fin 2, f ⟨2, m, k, ()⟩ := by
  unfold bypass at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_three]
  have hL := P.bypassState_sum_L (fun ℓ => f ⟨0, ℓ⟩)
  have hA := P.bypassState_sum_A (fun ℓ => f ⟨1, ℓ⟩)
  have hN := P.bypassState_sum_N (fun ℓ => f ⟨2, ℓ⟩)
  dsimp only at hL hA hN
  rw [hL, hA, hN]

/-- The leaf laws of `bypass P` under any procedure, the five leaf shapes.
Source: [[decision-problems-v2]] Definition 6 on the bypass tree
Kind: L -/
theorem bypass_leafLaw (C : Proc Unit (fun _ => Bool) K) :
    (∀ k : Fin 2, leafLaw C P.bypass ⟨0, 0, k, ()⟩ =
      P.ρ * P.δL * (if k = 0 then P.γ₁ else 1 - P.γ₁)) ∧
    (∀ (m : Bool) (k : Fin 2), leafLaw C P.bypass ⟨0, 1, m, k, ()⟩ =
      P.ρ * (1 - P.δL) * (C ()).w m * (if k = 0 then P.γ₁ else 1 - P.γ₁)) ∧
    (∀ k : Fin 2, leafLaw C P.bypass ⟨1, 0, k, ()⟩ =
      P.ρA * P.δA * (if k = 0 then P.γ₀ else 1 - P.γ₀)) ∧
    (∀ (m : Bool) (k : Fin 2), leafLaw C P.bypass ⟨1, 1, m, k, ()⟩ =
      P.ρA * (1 - P.δA) * (C ()).w m * (if k = 0 then P.γ₀ else 1 - P.γ₀)) ∧
    (∀ (m : Bool) (k : Fin 2), leafLaw C P.bypass ⟨2, m, k, ()⟩ =
      (1 - P.ρ - P.ρA) * (C ()).w m * (if k = 0 then P.γ₀ else 1 - P.γ₀)) := by
  refine ⟨fun k => ?_, fun m k => ?_, fun k => ?_, fun m k => ?_, fun m k => ?_⟩ <;>
  · unfold bypass bypassState bypassBranch kBlock
    simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, stateDistr_w, coinK_w, stateW_zero,
      stateW_one, stateW_two, gam_zero, gam_one, gam_two]
    conv_lhs => simp
    split_ifs <;> ring

/-- The worlds at the leaves of `bypass P`. Source: none: infrastructure. Kind: L -/
theorem bypass_world :
    (∀ k : Fin 2, world P.bypass ⟨0, 0, k, ()⟩ = (.L, true, decide (k = 0))) ∧
    (∀ (m : Bool) (k : Fin 2), world P.bypass ⟨0, 1, m, k, ()⟩ = (.L, m, decide (k = 0))) ∧
    (∀ k : Fin 2, world P.bypass ⟨1, 0, k, ()⟩ = (.A, false, decide (k = 0))) ∧
    (∀ (m : Bool) (k : Fin 2), world P.bypass ⟨1, 1, m, k, ()⟩ = (.A, m, decide (k = 0))) ∧
    (∀ (m : Bool) (k : Fin 2), world P.bypass ⟨2, m, k, ()⟩ = (.N, m, decide (k = 0))) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- `ν` on `bypass P` as an explicit 20-term sum. Source: none: infrastructure. Kind: L -/
theorem bypass_nu (C : Proc Unit (fun _ => Bool) K) (X : Finset DlW) :
    nu C P.bypass X =
      ((∑ k : Fin 2, if ((.L, true, decide (k = 0)) : DlW) ∈ X then
          leafLaw C P.bypass ⟨0, 0, k, ()⟩ else 0) +
        ∑ m : Bool, ∑ k : Fin 2, if ((.L, m, decide (k = 0)) : DlW) ∈ X then
          leafLaw C P.bypass ⟨0, 1, m, k, ()⟩ else 0) +
      ((∑ k : Fin 2, if ((.A, false, decide (k = 0)) : DlW) ∈ X then
          leafLaw C P.bypass ⟨1, 0, k, ()⟩ else 0) +
        ∑ m : Bool, ∑ k : Fin 2, if ((.A, m, decide (k = 0)) : DlW) ∈ X then
          leafLaw C P.bypass ⟨1, 1, m, k, ()⟩ else 0) +
      ∑ m : Bool, ∑ k : Fin 2, if ((.N, m, decide (k = 0)) : DlW) ∈ X then
          leafLaw C P.bypass ⟨2, m, k, ()⟩ else 0 := by
  rw [nu_eq_sum, bypass_sum]
  rfl

/-! ## The twelve world masses -/

/-- The cancer rate of a state. Source: doc Definition 2; [[double-lesion]]. Kind: D -/
def gamOf : DlState → K
  | .L => P.γ₁
  | .A => P.γ₀
  | .N => P.γ₀

/-- The six `(state, act)` cell masses under the label `p`: forced acts carry the grip, chosen
acts the label.
Source: [[two-lesions-doc-2026-09-18]] §3 ("Counting gives …"); [[double-lesion]]
Kind: D -/
def cellMass (p : K) : DlState → Bool → K
  | .L, true => P.ρ * (P.δL + (1 - P.δL) * p)
  | .L, false => P.ρ * (1 - P.δL) * (1 - p)
  | .A, true => P.ρA * (1 - P.δA) * p
  | .A, false => P.ρA * (P.δA + (1 - P.δA) * (1 - p))
  | .N, true => (1 - P.ρ - P.ρA) * p
  | .N, false => (1 - P.ρ - P.ρA) * (1 - p)

/-- The world mass `(s, m, k) ↦ cellMass s m · (γ_s or 1 − γ_s)`.
Source: [[two-lesions-doc-2026-09-18]] §3
Kind: D -/
def dlMass (p : K) (w : DlW) : K :=
  P.cellMass p w.1 w.2.1 * (if w.2.2 then P.gamOf w.1 else 1 - P.gamOf w.1)

/-- **The world masses of the overwrite tree are `dlMass`**: `ν_{overwrite P, p}({w}) = dlMass p w`
for every world, from `leafLaw`.
Source: [[two-lesions-doc-2026-09-18]] §3 ("Counting gives"), on the overwrite tree
Kind: P -/
theorem overwrite_nu_singleton (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) (w : DlW) :
    nu (procBoolK p h0 h1) P.overwrite {w} = P.dlMass p w := by
  rw [overwrite_nu]
  simp only [overwrite_leafLaw, procBoolK_w]
  rcases w with ⟨s, m, kk⟩
  cases s <;> cases m <;> cases kk <;>
  · conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two]
    conv_rhs => simp [dlMass, cellMass, gamOf]
    try ring

/-- **The world masses of the bypass tree are `dlMass` too**.
Source: [[two-lesions-doc-2026-09-18]] §3, on the bypass tree
Kind: P -/
theorem bypass_nu_singleton (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) (w : DlW) :
    nu (procBoolK p h0 h1) P.bypass {w} = P.dlMass p w := by
  rw [bypass_nu]
  obtain ⟨e1, e2, e3, e4, e5⟩ := P.bypass_leafLaw (procBoolK p h0 h1)
  simp only [e1, e2, e3, e4, e5, procBoolK_w]
  rcases w with ⟨s, m, kk⟩
  cases s <;> cases m <;> cases kk <;>
  · conv_lhs => simp [Fin.sum_univ_two]
    conv_rhs => simp [dlMass, cellMass, gamOf]
    try ring

/-- `ν_{overwrite}` at the label `p` of any event is the `dlMass`-sum over the event.
Source: none: infrastructure
Kind: L -/
theorem nuP_eq_sum_dlMass (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) (X : Finset DlW) :
    P.nuP p X = ∑ w ∈ X, P.dlMass p w := by
  rw [P.nuP_eq h0 h1, Cleanroom.Decision.DpCalibration.nu_eq_sum_singleton]
  exact Finset.sum_congr rfl fun w _ => P.overwrite_nu_singleton p h0 h1 w

/-- **One law (world level)**: the bypass and overwrite trees have the same `ν` at every label
and every event. (Their run laws differ: `occ` and `drew` are not events of `Ω`.)
Source: [[iv-design-draw-as-instrument]] §2 (B1) ("identical marginals over `(ℓ, m, k)` at
every `p`"); [[smoking-lesion-exploration-and-boundaries]] §1; dp-core-083
Kind: P
Fidelity: exact
Hyps: none -/
theorem oneLaw (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) (X : Finset DlW) :
    nu (procBoolK p h0 h1) P.bypass X = nu (procBoolK p h0 h1) P.overwrite X := by
  rw [Cleanroom.Decision.DpCalibration.nu_eq_sum_singleton, Cleanroom.Decision.DpCalibration.nu_eq_sum_singleton]
  exact Finset.sum_congr rfl fun w _ => by
    rw [P.bypass_nu_singleton, P.overwrite_nu_singleton]

/-! ## The cells and the observables -/

/-- A `dlMass`-sum over an act event as a sum over states and cancer.
Source: none: infrastructure
Kind: L -/
theorem sum_evAct_dlMass (a : Bool) (g : DlW → K) :
    ∑ w ∈ evAct a, g w = ∑ s, ∑ kk : Bool, g (s, a, kk) := by
  unfold evAct
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_prod_type]
  cases a <;> simp

/-- **The six cells**: `P_p(s ∧ m) = cellMass p s m` on the overwrite tree, for every state and
act.
Source: [[two-lesions-doc-2026-09-18]] §3 ("Counting gives"); [[double-lesion]]
Kind: P
Fidelity: exact (general `γ`, two grips)
Hyps: none -/
theorem nuP_cell (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) (s : DlState) (a : Bool) :
    P.nuP p (evState s ∩ evAct a) = P.cellMass p s a := by
  rw [nuP_eq_sum_dlMass P p h0 h1]
  have : evState s ∩ evAct a = {(s, a, true), (s, a, false)} := by
    ext w; rcases w with ⟨s', a', k'⟩
    simp only [Finset.mem_inter, mem_evState, mem_evAct, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    cases k' <;> simp
  rw [this, Finset.sum_pair (by simp), dlMass, dlMass]
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

/-- **`P_p(smoke) = ρδL + κp`**. Source: doc §3 (the explicit forms). Kind: P. Fidelity: exact.
Hyps: none -/
theorem nuP_smoke (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    P.nuP p evSmoke = P.ρ * P.δL + P.kappa * p := by
  rw [nuP_eq_sum_dlMass P p h0 h1, sum_evAct_dlMass, sum_dlState]
  conv_lhs => simp [Fintype.sum_bool, dlMass, cellMass, gamOf]
  unfold kappa
  ring

/-- **`P_p(abstain) = ρAδA + κ(1 − p)`**. Source: doc §3. Kind: P. Fidelity: exact. Hyps: none -/
theorem nuP_abstain (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    P.nuP p evAbstain = P.ρA * P.δA + P.kappa * (1 - p) := by
  rw [nuP_eq_sum_dlMass P p h0 h1, sum_evAct_dlMass, sum_dlState]
  conv_lhs => simp [Fintype.sum_bool, dlMass, cellMass, gamOf]
  unfold kappa
  ring

/-- A `dlMass`-sum over `cancer ∧ act` as a sum over states.
Source: none: infrastructure
Kind: L -/
theorem sum_cancer_evAct_dlMass (a : Bool) (g : DlW → K) :
    ∑ w ∈ evCancer ∩ evAct a, g w = ∑ s, g (s, a, true) := by
  have : evCancer ∩ evAct a = Finset.univ.filter fun w : DlW => w.2.2 = true ∧ w.2.1 = a := by
    ext w; simp [evCancer, evAct]
  rw [this, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fintype.sum_prod_type]
  simp [Fintype.sum_bool]

/-- **`P_p(cancer ∧ smoke) = ρδLγ₁ + κc_C·p`**. Source: doc §3; [[double-lesion]]. Kind: P.
Fidelity: exact. Hyps: none -/
theorem nuP_cancer_smoke (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    P.nuP p (evCancer ∩ evSmoke) = P.ρ * P.δL * P.γ₁ + P.kcC * p := by
  rw [nuP_eq_sum_dlMass P p h0 h1, sum_cancer_evAct_dlMass, sum_dlState]
  conv_lhs => simp [dlMass, cellMass, gamOf]
  unfold kcC
  ring

/-- **`P_p(cancer ∧ abstain) = ρAδAγ₀ + κc_C·(1 − p)`**. Source: doc §3; [[double-lesion]].
Kind: P. Fidelity: exact. Hyps: none -/
theorem nuP_cancer_abstain (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    P.nuP p (evCancer ∩ evAbstain) = P.ρA * P.δA * P.γ₀ + P.kcC * (1 - p) := by
  rw [nuP_eq_sum_dlMass P p h0 h1, sum_cancer_evAct_dlMass, sum_dlState]
  conv_lhs => simp [dlMass, cellMass, gamOf]
  unfold kcC
  ring

/-- **`P_p(cancer) = ργ₁ + (1 − ρ)γ₀`**, label-independent (the population cancer rate).
Source: [[two-lesions-exchange-2026-09-19]] line 63 ("`do(smoke) = ε_L`"); dp-core-2-027
Kind: P
Fidelity: exact
Hyps: none -/
theorem nuP_cancer (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    P.nuP p evCancer = P.ρ * P.γ₁ + (1 - P.ρ) * P.γ₀ := by
  rw [nuP_eq_sum_dlMass P p h0 h1]
  unfold evCancer
  rw [Finset.sum_filter, Fintype.sum_prod_type, sum_dlState]
  conv_lhs => simp [Fintype.sum_prod_type, Fintype.sum_bool, dlMass, cellMass, gamOf]
  ring

/-- **`P_p(state = s)`** is the state weight, label-independent.
Source: doc Definition 2
Kind: P
Fidelity: exact
Hyps: none -/
theorem nuP_state (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    P.nuP p (evState .L) = P.ρ ∧ P.nuP p (evState .A) = P.ρA ∧
      P.nuP p (evState .N) = 1 - P.ρ - P.ρA := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [nuP_eq_sum_dlMass P p h0 h1]
    unfold evState
    rw [Finset.sum_filter, Fintype.sum_prod_type, sum_dlState]
    conv_lhs => simp [Fintype.sum_prod_type, Fintype.sum_bool, dlMass, cellMass, gamOf]
    ring

/-! ## Positivity of the conditioning events -/

/-- `P_p(smoke) > 0` on `[0, 1]`, because `δL > 0`: the division in `Δ` is honest.
Source: mandate §3.4 ("the positivity lemmas … hold because `δL, δA > 0`")
Kind: L -/
theorem nuP_smoke_pos (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 < P.nuP p evSmoke := by
  rw [nuP_smoke P p h0 h1]
  have := P.kappa_pos
  nlinarith [mul_pos P.ρ_pos P.δL_pos]

/-- `P_p(abstain) > 0` on `[0, 1]`, because `δA > 0`.
Source: mandate §3.4
Kind: L -/
theorem nuP_abstain_pos (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 < P.nuP p evAbstain := by
  rw [nuP_abstain P p h0 h1]
  have := P.kappa_pos
  nlinarith [mul_pos P.ρA_pos P.δA_pos]

/-! ## The closed form of `Δ` -/

/-- The smoke conditional as a closed form. Source: doc §3. Kind: D -/
def condSmoke (p : K) : K := (P.ρ * P.δL * P.γ₁ + P.kcC * p) / (P.ρ * P.δL + P.kappa * p)

/-- The abstain conditional as a closed form. Source: doc §3. Kind: D -/
def condAbstain (p : K) : K :=
  (P.ρA * P.δA * P.γ₀ + P.kcC * (1 - p)) / (P.ρA * P.δA + P.kappa * (1 - p))

/-- **The closed form of `Δ`**: on `[0, 1]`,
`Δ(p) = β·((ρδLγ₁ + κc_C p)/(ρδL + κp) − (ρAδAγ₀ + κc_C(1−p))/(ρAδA + κ(1−p)))`.
Source: [[two-lesions-doc-2026-09-18]] §3 (the two quotients); [[double-lesion]]
Kind: P
Fidelity: exact (general `γ`, two grips; the doc's display at `γ = (1, 0)`, `δL = δA`)
Hyps: none -/
theorem Delta_eq (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    P.Delta p = P.β * (P.condSmoke p - P.condAbstain p) := by
  unfold Delta condSmoke condAbstain
  rw [nuP_cancer_smoke P p h0 h1, nuP_smoke P p h0 h1, nuP_cancer_abstain P p h0 h1,
    nuP_abstain P p h0 h1]

/-- `Δ` on the bypass tree is the same function: the quotients of `ν_{bypass}` agree with
those of `ν_{overwrite}` cell by cell.
Source: dp-core-083; mandate T1 (`Delta_bypass_eq`)
Kind: C
Fidelity: exact
Hyps: none -/
theorem Delta_bypass_eq (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    P.β * (nu (procBoolK p h0 h1) P.bypass (evCancer ∩ evSmoke) /
        nu (procBoolK p h0 h1) P.bypass evSmoke -
      nu (procBoolK p h0 h1) P.bypass (evCancer ∩ evAbstain) /
        nu (procBoolK p h0 h1) P.bypass evAbstain) = P.Delta p := by
  unfold Delta
  rw [P.oneLaw, P.oneLaw, P.oneLaw, P.oneLaw, P.nuP_eq h0 h1, P.nuP_eq h0 h1, P.nuP_eq h0 h1,
    P.nuP_eq h0 h1]

/-- The denominator of the smoke conditional is positive on `[0, 1]`. Source: none. Kind: L -/
theorem denomSmoke_pos (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 < P.ρ * P.δL + P.kappa * p := by
  have := P.nuP_smoke_pos p h0 h1; rwa [nuP_smoke P p h0 h1] at this

/-- The denominator of the abstain conditional is positive on `[0, 1]`. Source: none. Kind: L -/
theorem denomAbstain_pos (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    0 < P.ρA * P.δA + P.kappa * (1 - p) := by
  have := P.nuP_abstain_pos p h0 h1; rwa [nuP_abstain P p h0 h1] at this

/-- `κγ₁ − κc_C = (1 − ρ − ρAδA)(γ₁ − γ₀)`. Source: none: infrastructure. Kind: L -/
theorem kappa_mul_sub_kcC : P.kappa * P.γ₁ - P.kcC = (1 - P.ρ - P.ρA * P.δA) * (P.γ₁ - P.γ₀) := by
  unfold kcC kappa; ring

/-- `κc_C − κγ₀ = ρ(1 − δL)(γ₁ − γ₀)`. Source: none: infrastructure. Kind: L -/
theorem kcC_sub_kappa_mul : P.kcC - P.kappa * P.γ₀ = P.ρ * (1 - P.δL) * (P.γ₁ - P.γ₀) := by
  unfold kcC kappa; ring

/-- **The smoke conditional is strictly decreasing in `p` on `[0, 1]`** when `γ₀ < γ₁`.
Source: [[two-lesions-doc-2026-09-18]] §3 ("a short computation shows both are strictly
decreasing in `p`")
Kind: P
Fidelity: exact, with the scope `γ₀ < γ₁` explicit (the doc has `γ = (1, 0)`)
Hyps: none -/
theorem condSmoke_strictAntiOn (hγ : P.γ₀ < P.γ₁) : StrictAntiOn P.condSmoke (Set.Icc 0 1) := by
  have hc1 : P.kcC < P.kappa * P.γ₁ := by
    have h := P.kappa_mul_sub_kcC
    have hpos : 0 < (1 - P.ρ - P.ρA * P.δA) * (P.γ₁ - P.γ₀) := by
      apply mul_pos _ (sub_pos.mpr hγ)
      have : P.ρA * P.δA ≤ P.ρA := by nlinarith [P.ρA_pos, P.δA_le_one]
      linarith [P.ρ_add_ρA_lt_one]
    linarith
  intro x hx y hy hxy
  unfold condSmoke
  have hdx := P.denomSmoke_pos x hx.1 hx.2
  have hdy := P.denomSmoke_pos y hy.1 hy.2
  rw [div_lt_div_iff₀ hdy hdx]
  have ha : 0 < P.ρ * P.δL := mul_pos P.ρ_pos P.δL_pos
  nlinarith [mul_pos (mul_pos ha (sub_pos.mpr hxy)) (sub_pos.mpr hc1)]

/-- **The abstain conditional is strictly decreasing in `p` on `[0, 1]`** when `γ₀ < γ₁` and
`δL < 1`. At `δL = 1` it is the constant `γ₀` (`κc_C = κγ₀` then), so the doc's "both are
strictly decreasing" holds for `δ < 1` only — a boundary imprecision recorded in the findings.
Source: [[two-lesions-doc-2026-09-18]] §3 ("both are strictly decreasing in `p`")
Kind: P
Fidelity: exact, with the scopes `γ₀ < γ₁` and `δL < 1` explicit
Hyps: none -/
theorem condAbstain_strictAntiOn (hγ : P.γ₀ < P.γ₁) (hδ : P.δL < 1) :
    StrictAntiOn P.condAbstain (Set.Icc 0 1) := by
  have hc0 : P.kappa * P.γ₀ < P.kcC := by
    have h := P.kcC_sub_kappa_mul
    have hpos : 0 < P.ρ * (1 - P.δL) * (P.γ₁ - P.γ₀) :=
      mul_pos (mul_pos P.ρ_pos (sub_pos.mpr hδ)) (sub_pos.mpr hγ)
    linarith
  intro x hx y hy hxy
  unfold condAbstain
  have hdx := P.denomAbstain_pos x hx.1 hx.2
  have hdy := P.denomAbstain_pos y hy.1 hy.2
  rw [div_lt_div_iff₀ hdy hdx]
  have hb : 0 < P.ρA * P.δA := mul_pos P.ρA_pos P.δA_pos
  nlinarith [mul_pos (mul_pos hb (sub_pos.mpr hxy)) (sub_pos.mpr hc0)]

/-- The abstain conditional is the constant `γ₀` at `δL = 1` (the boundary of the doc's claim).
Source: [[two-lesions-doc-2026-09-18]] §3 (the second quotient at `δ = 1`)
Kind: N− (a boundary witness)
Fidelity: exact -/
theorem condAbstain_const_of_δL_eq_one (hδ : P.δL = 1) (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    P.condAbstain p = P.γ₀ := by
  have hc : P.kcC = P.kappa * P.γ₀ := by
    have := P.kcC_sub_kappa_mul; rw [hδ] at this; linarith
  unfold condAbstain
  rw [hc, div_eq_iff (P.denomAbstain_pos p h0 h1).ne']
  ring

/-! ## Witnesses (N+): the session note's numbers -/

/-- **(B1) at the session parameters, `p = ½`**: the three observables are
`(½, 431/8000, 409/8000)` on both trees.
Source: [[iv-design-draw-as-instrument]] §9 (B1) ("`p=1/2 (1/2, 431/8000, 409/8000)`")
Kind: N+ -/
theorem sessP_obs_half :
    (sessP : DlParams ℚ).nuP (1/2) evSmoke = 1/2 ∧
    (sessP : DlParams ℚ).nuP (1/2) (evCancer ∩ evSmoke) = 431/8000 ∧
    (sessP : DlParams ℚ).nuP (1/2) (evCancer ∩ evAbstain) = 409/8000 ∧
    nu (procBoolK (1/2 : ℚ) (by norm_num) (by norm_num)) (sessP : DlParams ℚ).bypass evSmoke =
      1/2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nuP_smoke _ _ (by norm_num) (by norm_num)]; simp [sessP, kappa]; norm_num
  · rw [nuP_cancer_smoke _ _ (by norm_num) (by norm_num)]; simp [sessP, kcC]; norm_num
  · rw [nuP_cancer_abstain _ _ (by norm_num) (by norm_num)]; simp [sessP, kcC]; norm_num
  · rw [oneLaw, ← nuP_eq _ (by norm_num) (by norm_num), nuP_smoke _ _ (by norm_num) (by norm_num)]
    simp [sessP, kappa]; norm_num

/-- `c_C = 37/360` at the session parameters.
Source: [[iv-design-draw-as-instrument]] §9 (B2) ("cancer | complier … = 37/360")
Kind: N+ -/
theorem sessP_cC : (sessP : DlParams ℚ).cC = 37/360 := by
  simp [cC, kcC, kappa, sessP]; norm_num

end DlParams

end Cleanroom.Decision.DpTwoLesions
