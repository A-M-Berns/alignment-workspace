import Cleanroom.Decision.DpFaithfulUdt.OnePoint

/-!
# Per-run disposition calibration, `Π_B`, and the shared argmax of Theorems 1 and 2 (T11(a)(b), T12)

`firstperson.md` D4/D5: the **per-run deviation state** at `d` for the action `a` is
`P^a(X) = μ_{C[d↦a]}({λ ⊨ X} ∣ occ(d))`, `V^a(X) = 𝔼_{C[d↦a]}[r ∣ λ ⊨ X, occ(d)]` — built here as a
genuine `State` on the tree's carrier (`occState`, averaging axiom proved) under the guard
`0 < μ_{C[d↦a]}(occ(d))` (`pdcState`, junk otherwise, never read unguarded). The PDC
counterfactual structure on the `ρ`-events is `Cf.ofEvents ρ d (pdcState C B d)`.

* **T11(a)** (`pdcState_V_eq_ssa`, `piB_eq_ssa_argmax`): wherever `ρ_d(a)` holds a.s. on `occ(d)`
  under the deviation (`SuccessOn` — success puts `P^a(ρ_d(a)) = 1`),
  `V^{ρ_d(a)}(ρ_d(a)) = 𝔼_{C[d↦a]}[r ∣ occ(d)] = ssaValue C B d δ_a`, so `Π_B(d) = cUDT_{s_d,PDC}(d)
  = Unif argmax_a ssaValue(δ_a)` — Theorem 2's EDT+SSA evaluator; `Π_B` is UDT1.0 at the point.
* **T11(b)** (`tCudtAt_pdc_iff_coherentPureAt`, `tCudtAt_pdc_iff_coherentAt_of_almostFair`): for a
  `C` deterministic at `d` with `μ_C(occ(d)) > 0`, `T_cUDT` under PDC at `d` ⟺ v2's *pure*
  Definition 22 at `d`; on almost-fair trees ⟺ the mixed Definition 22 of record. (FP-10's
  "Def-22-coherent" is the pure one in general.)
* **T12** (`siaSum_le_iff_ssa`, `siaSum_eq_mass_mul_ssa`): when `#_d ≤ 1` on every run and
  `μ_C(occ(d)) > 0`, `∑_{q : d_q = d} R_q G_q(C, a) = μ(occ(d)) · 𝔼_{C[d↦a]}[r ∣ occ(d)]`, so Theorem
  1's functional and Theorem 2's evaluator have the same argmax at `d` (FP-19′(i); the source's
  `+ const_a` is `0` once `offOcc` is split off). Two lines over `dp-local-opt`: a `C` row.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ### The occurrence-restricted world event and its masses -/

section occEv

variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-- The runs of `occ(d)` whose world satisfies `X`: `{λ ⊨ X} ∩ occ(d)`.
Source: `firstperson.md` D4 (`{λ ⊨ X} ∣ occ(d)`); [[decision-problems-v2]] Definition 13
Kind: D -/
def occEv (X : Finset Ω) : Finset B.Leaves := worldEv B X ∩ occ d B

/-- `occEv` as a filter of `occ(d)`. Source: none: infrastructure. Kind: L -/
theorem occEv_eq_filter (X : Finset Ω) : occEv B d X = (occ d B).filter fun ℓ => world B ℓ ∈ X := by
  ext ℓ; simp [occEv, worldEv, and_comm]

/-- `occEv ⊤ = occ(d)`. Source: none: infrastructure. Kind: L -/
theorem occEv_univ : occEv B d Finset.univ = occ d B := by
  rw [occEv_eq_filter]; simp

/-- `occEv` is additive. Source: none: infrastructure. Kind: L -/
theorem occEv_union (X Y : Finset Ω) : occEv B d (X ∪ Y) = occEv B d X ∪ occEv B d Y := by
  ext ℓ; simp [occEv, worldEv]; tauto

/-- `occEv` preserves disjointness. Source: none: infrastructure. Kind: L -/
theorem occEv_disjoint {X Y : Finset Ω} (h : Disjoint X Y) :
    Disjoint (occEv B d X) (occEv B d Y) := by
  rw [Finset.disjoint_left]
  intro ℓ hX hY
  simp only [occEv, Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and] at hX hY
  exact Finset.disjoint_left.mp h hX.1 hY.1

/-- The mass of `occEv X` as an indicator sum over `occ(d)`. Source: none: infrastructure. Kind: L -/
theorem mass_occEv_eq_sum (X : Finset Ω) :
    mass C B (occEv B d X) = ∑ ℓ ∈ occ d B, if world B ℓ ∈ X then leafLaw C B ℓ else 0 := by
  rw [occEv_eq_filter]; unfold mass; rw [Finset.sum_filter]

/-- Atom masses add up to the event's mass. Source: none: infrastructure. Kind: L -/
theorem sum_mass_occEv_singleton (X : Finset Ω) :
    ∑ ω ∈ X, mass C B (occEv B d {ω}) = mass C B (occEv B d X) := by
  simp only [mass_occEv_eq_sum, Finset.mem_singleton]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.sum_ite_eq]

/-- The payoff mass of `{λ ⊨ X} ∩ occ(d)`: `𝔼_μ[r · 1_{λ ⊨ X} · 1_{occ(d)}]`.
Source: `firstperson.md` D4 (`V^a`'s numerator); [[decision-problems-v2]] Definition 13
Kind: D -/
def occPay (X : Finset Ω) : K := ∑ ℓ ∈ occEv B d X, leafLaw C B ℓ * payoff B ℓ

/-- `occPay` is additive. Source: none: infrastructure. Kind: L -/
theorem occPay_union {X Y : Finset Ω} (h : Disjoint X Y) :
    occPay C B d (X ∪ Y) = occPay C B d X + occPay C B d Y := by
  unfold occPay
  rw [occEv_union, Finset.sum_union (occEv_disjoint B d h)]

/-- If a subset carries the whole mass, it carries every weighted sum.
Source: none: infrastructure
Kind: L -/
theorem sum_eq_of_mass_eq {S T : Finset B.Leaves} (hsub : S ⊆ T)
    (hmass : mass C B S = mass C B T) (f : B.Leaves → K) :
    ∑ ℓ ∈ S, leafLaw C B ℓ * f ℓ = ∑ ℓ ∈ T, leafLaw C B ℓ * f ℓ := by
  apply Finset.sum_subset hsub
  intro ℓ hT hS
  have h0 : ∑ ℓ ∈ T \ S, leafLaw C B ℓ = 0 := by
    have := Finset.sum_sdiff (f := leafLaw C B) hsub
    unfold mass at hmass
    linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg fun ℓ _ => leafLaw_nonneg C B ℓ).mp h0 ℓ
    (Finset.mem_sdiff.mpr ⟨hT, hS⟩)
  rw [this, zero_mul]

end occEv

/-! ### The per-run deviation state (D4/D5) -/

section occState

variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-- **The per-run state of `C` at `d`** (D5's self-locating state, the Definition 13 per-run
object, for a given procedure): `P(X) = μ_C({λ ⊨ X} ∣ occ(d))`, `V(X) = 𝔼_{μ_C}[r ∣ λ ⊨ X, occ(d)]`,
under the guard `0 < μ_C(occ(d))`. That this pair is a state (the averaging axiom) is proved.
Applied to `C[d ↦ a]` it is D4's PDC referent `(P^a, V^a)` (`pdcState`).
Source: `firstperson.md` D5 ("`P^{sl}_{s_d} = λ_*μ_C(· ∣ occ(d))`, `V^{sl}_{s_d}(X) = 𝔼_{μ_C}[r ∣ λ ⊨
X, occ(d)]`"), D4; [[decision-problems-v2]] §3.1 Definition 13 (per-run)
Kind: P
Fidelity: exact (Definition 6; the guard is Definition 13's)
Hyps: (a) `0 < μ_C(occ(d))` -/
noncomputable def occState (h : 0 < mass C B (occ d B)) : State Ω K where
  P :=
    { w := fun ω => mass C B (occEv B d {ω}) / mass C B (occ d B)
      nonneg := fun ω => div_nonneg (mass_nonneg C B _) (mass_nonneg C B _)
      sum_one := by
        rw [← Finset.sum_div, sum_mass_occEv_singleton, occEv_univ, div_self h.ne'] }
  V X := occPay C B d X / mass C B (occEv B d X)
  avg X Y hXY hX hY := by
    have hpr : ∀ Z : Finset Ω, probOf
        { w := fun ω => mass C B (occEv B d {ω}) / mass C B (occ d B)
          nonneg := fun ω => div_nonneg (mass_nonneg C B _) (mass_nonneg C B _)
          sum_one := by
            rw [← Finset.sum_div, sum_mass_occEv_singleton, occEv_univ, div_self h.ne'] } Z =
        mass C B (occEv B d Z) / mass C B (occ d B) := by
      intro Z
      unfold probOf
      simp only
      rw [← Finset.sum_div, sum_mass_occEv_singleton]
    rw [hpr] at hX hY
    rw [hpr, hpr, hpr]
    have hmX : 0 < mass C B (occEv B d X) := by
      by_contra hc
      rw [not_lt] at hc
      have := div_nonpos_of_nonpos_of_nonneg hc (mass_nonneg C B (occ d B))
      linarith
    have hmY : 0 < mass C B (occEv B d Y) := by
      by_contra hc
      rw [not_lt] at hc
      have := div_nonpos_of_nonpos_of_nonneg hc (mass_nonneg C B (occ d B))
      linarith
    rw [occPay_union C B d hXY, occEv_union, mass_union C B (occEv_disjoint B d hXY)]
    have hsum : 0 < mass C B (occEv B d X) + mass C B (occEv B d Y) := by linarith
    field_simp

/-- `P` of the per-run state. Source: none: infrastructure. Kind: L -/
theorem occState_pr (h : 0 < mass C B (occ d B)) (X : Finset Ω) :
    (occState C B d h).pr X = mass C B (occEv B d X) / mass C B (occ d B) := by
  unfold State.pr probOf occState
  simp only
  rw [← Finset.sum_div, sum_mass_occEv_singleton]

/-- `V` of the per-run state. Source: none: infrastructure. Kind: L -/
theorem occState_V (h : 0 < mass C B (occ d B)) (X : Finset Ω) :
    (occState C B d h).V X = occPay C B d X / mass C B (occEv B d X) := rfl

/-- **`X` holds almost surely on `occ(d)` under the deviation `C[d ↦ a]`** — the success condition
`P^a(X) = 1` of D4's PDC state in cross-multiplied form.
Source: `firstperson.md` FP-10 ("success puts `P^a(ρ_d(a)) = 1`"); v2 Definition 2 (success)
Kind: D -/
def SuccessOn (a : acts d) (X : Finset Ω) : Prop :=
  mass (C.deviatePure d a) B (occEv B d X) = mass (C.deviatePure d a) B (occ d B)

/-- **D4's PDC state at `(d, a)`**: the per-run state of the deviation `C[d ↦ a]`, junk
(`State.trivial`) when `μ_{C[d↦a]}(occ(d)) = 0`; never read unguarded (every theorem carries
`0 < μ_C(occ(d))`, which is `μ_{C[d↦a]}(occ(d))` by Lemma 1).
Source: `firstperson.md` D4 ("`cf_{s_d}(ρ_d(a)) = (P^a, V^a)` with `P^a(X) = μ_{C[d↦a]}({λ ⊨ X} ∣
occ(d))`, `V^a(X) = 𝔼_{μ_{C[d↦a]}}[r ∣ λ ⊨ X, occ(d)]`")
Kind: D
Fidelity: exact (under the guard) -/
noncomputable def pdcState [Nonempty Ω] (a : acts d) : State Ω K :=
  if h : 0 < mass (C.deviatePure d a) B (occ d B) then occState (C.deviatePure d a) B d h
  else State.trivial

/-- Under the guard, the PDC state puts probability one on an event holding a.s. on `occ(d)`.
Source: `firstperson.md` FP-10 ("success puts `P^a(ρ_d(a)) = 1`")
Kind: L -/
theorem pdcState_pr_eq_one [Nonempty Ω] (hpos : 0 < mass C B (occ d B)) (a : acts d)
    {X : Finset Ω} (hX : SuccessOn C B d a X) : (pdcState C B d a).pr X = 1 := by
  have hpos' : 0 < mass (C.deviatePure d a) B (occ d B) := by
    rw [Proc.deviatePure, occurrence_constancy]; exact hpos
  unfold pdcState
  rw [dif_pos hpos', occState_pr, hX, div_self hpos'.ne']

/-- **T11(a) — the PDC state's value of its disposition is Theorem 2's evaluator**: for `X`
holding a.s. on `occ(d)` under `C[d ↦ a]` (in particular the disposition event `ρ_d(a)` itself),
`V^a(X) = 𝔼_{C[d↦a]}[r ∣ occ(d)] = ssaValue C B d δ_a`.
Source: `firstperson.md` FP-10 ("Under PDC, `V^{ρ_d(a)}_{s_d}(ρ_d(a)) = 𝔼_{μ_{C[d↦a]}}[r ∣ occ(d)]`
(success puts `P^a(ρ_d(a)) = 1`)"); dp-cf-113
Kind: C
Fidelity: exact
Hyps: (a) `0 < μ_C(occ(d))`; (a) `SuccessOn` (the success axiom at the event) -/
theorem pdcState_V_eq_ssa [Nonempty Ω] (hpos : 0 < mass C B (occ d B)) (a : acts d)
    {X : Finset Ω} (hX : SuccessOn C B d a X) :
    (pdcState C B d a).V X = ssaValue C B d (FinDistr.pure a) := by
  have hpos' : 0 < mass (C.deviatePure d a) B (occ d B) := by
    rw [Proc.deviatePure, occurrence_constancy]; exact hpos
  unfold pdcState
  rw [dif_pos hpos', occState_V, ssaValue_eq_div]
  unfold SuccessOn at hX
  rw [hX]
  have hocc : mass (C.deviatePure d a) B (occ d B) = mass C B (occ d B) := by
    rw [Proc.deviatePure, occurrence_constancy]
  rw [hocc]
  congr 1
  unfold occPay ssaNum
  exact sum_eq_of_mass_eq (C.deviatePure d a) B (Finset.inter_subset_right) hX _

end occState

/-! ### `Π_B` is Theorem 2's evaluator; `T_cUDT` under PDC is coherence -/

section piB

variable [Nonempty Ω] (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)
  (ρ : (d : ι) → acts d → Finset Ω)

/-- The PDC counterfactual structure at `d` on the `ρ`-events. Source: `firstperson.md` D4. Kind: D -/
noncomputable def pdcCf : Cf Ω K := Cf.ofEvents ρ d fun a => pdcState C B d a

/-- **T11(a) — `Π_B` is UDT1.0 at the point**: `Π_B(d) = cUDT_{s_d,PDC}(d) = Unif argmax_a
ssaValue C B d (δ_a)`, Theorem 2's EDT+SSA evaluator, whenever the `ρ`-events are the dispositions
(`ρ_d` injective, each `ρ_d(a)` a.s. on `occ(d)` under `C[d ↦ a]`) and `μ_C(occ(d)) > 0`.
Scope: Definition 6, every tree, on-path (`μ_C(occ(d)) > 0`); off-path the PDC state is
undefined and `Π_B` outputs the junk default's tie (`PiB.lean`, FP-13′).
Source: `firstperson.md` D6 ("`Π_B(d) := Unif argmax_{a ∈ A_d} V^{ρ_d(a)}_{s_d}(ρ_d(a))`"), FP-10
("so `Π_B` is Theorem 2's EDT+SSA evaluator … it makes `Π_B` UDT1.0"); dp-cf-113
Kind: C
Fidelity: variant: `ρ` on the input carrier `Ω` with success as a hypothesis (D4/D5's stamped
`B^{pol}` is not built; `SuccessOn` is FP-10's "success puts `P^a(ρ_d(a)) = 1`", discharged on
each tree used)
Hyps: (a) `0 < μ_C(occ(d))`; (a) `ρ_d` injective and successful on `occ(d)` -/
theorem piB_eq_ssa_argmax (hinj : Function.Injective (ρ d))
    (hρ : ∀ a, SuccessOn C B d a (ρ d a)) (hpos : 0 < mass C B (occ d B)) :
    cudtProc (pdcCf C B d ρ) ρ d = uniformArgmax fun a => ssaValue C B d (FinDistr.pure a) := by
  unfold cudtProc pdcCf
  congr 1
  funext a
  rw [Cf.ofEvents_apply ρ d _ hinj, pdcState_V_eq_ssa C B d hpos a (hρ a)]

/-- `C` deviated to its own action at `d` is `C`. Source: none: infrastructure. Kind: L -/
theorem deviatePure_self {a₀ : acts d} (ha₀ : C d = FinDistr.pure a₀) :
    C.deviatePure d a₀ = C := by
  funext d'
  by_cases hd : d' = d
  · subst hd; simp [Proc.deviatePure, ha₀]
  · simp [Proc.deviatePure, Proc.deviate_ne C _ hd]

/-- **T11(b) — `T_cUDT` under PDC at `d` ⟺ v2's pure Definition 22 at `d`**, for `C` deterministic at
`d` (`C(d) = δ_{a₀}`) with `μ_C(occ(d)) > 0`: `a₀` maximises Theorem 2's evaluator iff no pure
deviation at `d` beats `C` (`ssaValue_le_iff`). The source's "Def-22-coherent" is the *pure*
Definition 22 as v2 prints it; the mixed one of record agrees on almost-fair trees
(`tCudtAt_pdc_iff_coherentAt_of_almostFair`) and differs under self-succession (`dp-local-opt`).
Source: `firstperson.md` FP-10 ("for deterministic `C`, `T_cUDT(C,B)` under PDC ⟺ `C` is
Def-22-coherent"), FP-13′ ("`Π_B` approves exactly the Def-22-coherent procedures"); dp-cf-113
Kind: C
Fidelity: variant: pure Definition 22, determinism only at `d`; `ρ` on the input carrier with
success as a hypothesis (as `piB_eq_ssa_argmax`)
Hyps: (a) `0 < μ_C(occ(d))`; (a) `C(d) = δ_{a₀}`; (a) `ρ_d` injective and successful -/
theorem tCudtAt_pdc_iff_coherentPureAt (hinj : Function.Injective (ρ d))
    (hρ : ∀ a, SuccessOn C B d a (ρ d a)) (hpos : 0 < mass C B (occ d B)) {a₀ : acts d}
    (ha₀ : C d = FinDistr.pure a₀) :
    TCudtAt (pdcCf C B d ρ) ρ C d ↔ CoherentPureAt C B d := by
  have hV : ∀ a, ((pdcCf C B d ρ) (ρ d a)).V (ρ d a) = ssaValue C B d (FinDistr.pure a) := by
    intro a
    unfold pdcCf
    rw [Cf.ofEvents_apply ρ d _ hinj, pdcState_V_eq_ssa C B d hpos a (hρ a)]
  unfold TCudtAt CoherentPureAt
  simp only [mem_argmaxFull, hV, ha₀, FinDistr.pure_w]
  constructor
  · intro h b
    have := h a₀ (by simp) b
    rw [ssaValue_le_iff C B d hpos] at this
    rwa [← Proc.deviatePure, ← Proc.deviatePure, deviatePure_self C d ha₀] at this
  · intro h a ha b
    have haa : a = a₀ := by
      by_contra hne
      rw [if_neg hne] at ha
      exact lt_irrefl _ ha
    subst haa
    rw [ssaValue_le_iff C B d hpos, ← Proc.deviatePure, ← Proc.deviatePure,
      deviatePure_self C d ha₀]
    exact h b

/-- **T11(b) on almost-fair trees: `T_cUDT` under PDC ⟺ the mixed Definition 22 of record.**
Source: `firstperson.md` FP-10; A30; `dp-local-opt` `coherentAt_iff_coherentPureAt_of_almostFair`
Kind: C
Fidelity: exact (mixed Definition 22, almost-fair scope)
Hyps: (a) `AlmostFair B`; (a) `0 < μ_C(occ(d))`; (a) `C(d) = δ_{a₀}`; (a) `ρ_d` injective and successful -/
theorem tCudtAt_pdc_iff_coherentAt_of_almostFair (hB : AlmostFair B)
    (hinj : Function.Injective (ρ d)) (hρ : ∀ a, SuccessOn C B d a (ρ d a))
    (hpos : 0 < mass C B (occ d B)) {a₀ : acts d} (ha₀ : C d = FinDistr.pure a₀) :
    TCudtAt (pdcCf C B d ρ) ρ C d ↔ CoherentAt C B d := by
  rw [tCudtAt_pdc_iff_coherentPureAt C B d ρ hinj hρ hpos ha₀,
    coherentAt_iff_coherentPureAt_of_almostFair C d hB]

end piB

/-! ### T12: Theorem 1 and Theorem 2 share their argmax when `#_d ≤ 1` -/

section anthropic

variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-- **T12, the identity**: when every run meets `d` at most once,
`∑_{q : d_q = d} R_q G_q(C, a) = μ_C(occ(d)) · 𝔼_{C[d↦a]}[r ∣ occ(d)]` — Theorem 1's fiber
functional is the occurrence mass times Theorem 2's evaluator (the source's `+ const_a` is `0`
once `offOcc` is split off, `value_deviatePure_eq_siaSum_add_offOcc`).
Source: `firstperson.md` FP-19′(i) ("on the almost-fair class no anthropic parameter exists
anywhere"), FP-17 ("at `k = 1` all coincide"); dp-cf-2-014
Kind: C
Fidelity: exact (`#_d ≤ 1` per point suffices, weaker than `AlmostFair`)
Hyps: (a) `∀ ℓ, #_d(ℓ) ≤ 1` -/
theorem siaSum_eq_mass_mul_ssa (hfair : ∀ ℓ, count d B ℓ ≤ 1) (a : acts d) :
    siaSum C B d a = mass C B (occ d B) * ssaValue C B d (FinDistr.pure a) := by
  rw [siaSum_eq_ssaNum_pure C d B hfair a, ← ssaValue_mul_mass, mul_comm]

/-- **T12 — FP-19′(i): Theorem 1's functional and Theorem 2's evaluator have the same argmax at
`d`** when `#_d ≤ 1` on every run and `μ_C(occ(d)) > 0`: `Φ_d(C, b) ≤ Φ_d(C, a) ⟺ ssaValue(δ_b) ≤
ssaValue(δ_a)`. Hence on the almost-fair class the SIA/SSA choice is inert at every point (the
`N−` boundary: on the nested AMD the two argmaxes differ, `dp-local-opt`'s `NestedWitness`).
Scope: `#_d ≤ 1` at the point, Definition 6; the normaliser `μ(occ(d))` is deviation-invariant
(Lemma 1).
Source: `firstperson.md` FP-19′(i), FP-17; dp-cf-2-014
Kind: C
Fidelity: exact
Hyps: (a) `∀ ℓ, #_d(ℓ) ≤ 1`; (a) `0 < μ_C(occ(d))` -/
theorem siaSum_le_iff_ssa (hfair : ∀ ℓ, count d B ℓ ≤ 1) (hpos : 0 < mass C B (occ d B))
    (a b : acts d) :
    siaSum C B d b ≤ siaSum C B d a ↔
      ssaValue C B d (FinDistr.pure b) ≤ ssaValue C B d (FinDistr.pure a) := by
  rw [siaSum_eq_mass_mul_ssa C B d hfair, siaSum_eq_mass_mul_ssa C B d hfair]
  exact ⟨fun h => le_of_mul_le_mul_left h hpos, fun h => mul_le_mul_of_nonneg_left h hpos.le⟩

/-- **T12, the theory form**: Theorem 1's condition at `d` is `supp C(d) ⊆ argmax_a ssaValue(δ_a)`
when `#_d ≤ 1` and `μ_C(occ(d)) > 0`.
Source: `firstperson.md` FP-19′(i)
Kind: C -/
theorem thm1At_iff_ssa (hfair : ∀ ℓ, count d B ℓ ≤ 1) (hpos : 0 < mass C B (occ d B)) :
    Thm1At C B d ↔ ∀ a, 0 < (C d).w a → ∀ b,
      ssaValue C B d (FinDistr.pure b) ≤ ssaValue C B d (FinDistr.pure a) := by
  unfold Thm1At
  refine forall₂_congr fun a _ => forall_congr' fun b => ?_
  exact siaSum_le_iff_ssa C B d hfair hpos a b

end anthropic

end Cleanroom.Decision.DpFaithfulUdt
