import Cleanroom.Decision.DpFirstpersonSc.License
import Cleanroom.Decision.DpFirstpersonSc.Refinement

/-!
# Witnesses for T2(b) and T10: the coverage-failure tree and the radical-label tree

* **`coverFail`** — FP-22′'s 3-leaf coverage-failure tree: a fair coin; branch A queries `d`
  (`a ↦ (1,a)`, `r = 1`; `b ↦ (1,b)`, `r = 0`); branch B ends in the unconsulted world `(1,a)`,
  `r = 1`. **Shape note (fidelity: variant):** branch B's leaf is placed below a node of a second
  point `e` with both edges to the same leaf, so that the two chance children share one shape (the
  tree type's `Fin 2`-indexed children must be one lambda); `e` changes nothing about `d` —
  `occ(d)`, `ν`, `O_d` and coverage of `d` are exactly the source's. Under `C = δ_a` at both
  points: `ν = δ_{(1,a)}`, the strict-OC state at `d` and the per-run state are both `δ_{(1,a)}`
  with value `1`, so the **base audit passes** (`coverFail_base_audit_passes`) while
  **coverage fails** (`coverFail_not_covers`) — the `⟹` of FP-22′ on the base algebra is refuted
  (`coverFail_license_fails`); **stamped, the strict-OC state fails** (`coverFail_stamped_fails`,
  by T2(a)): `(1,a,some a)` vs `(1,a,none)`.
* **`radicalLabel`** — AN-15's radical-label tree: evented fair chance (the world records the
  side), `d` queried on side A only, `O_d = ⊤`. `occ(d) = λ⁻¹{side = A}` exactly (expressible,
  `radicalLabel_occExpressible`) yet the density of `μ(· | occ(d))` is **not** constant on the
  observation atoms (`radicalLabel_not_occUnion`: `O_d = ⊤` makes one atom) — SC's refinement
  measure fires on an expressible relabelling; with `occ_univ_occUnion` on `mug1`/TN-V2 it is
  silent where OC and SSC differ. It tracks neither direction of expressibility.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFirstpersonSc

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFaithfulUdt
open Finset

/-- `μ(S)` as an indicator sum over all leaves. Source: none: infrastructure. Kind: L -/
theorem mass_eq_sum_ite' {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Ω ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
    (C : Proc ι acts K) (B : Tree Ω ι acts K) (S : Finset B.Leaves) :
    mass C B S = ∑ ℓ, if ℓ ∈ S then leafLaw C B ℓ else 0 := by
  unfold mass; rw [Finset.sum_ite_mem, Finset.univ_inter]

/-! ## The coverage-failure tree -/

/-- The two points of `coverFail`: `d` (consulted on branch A) and the dummy `e` (branch B).
Source: `firstperson.md` FP-22′ (the 3-leaf coverage-failure tree); shape note in the module
docstring
Kind: D -/
inductive CfPt : Type
  | d
  | e
  deriving DecidableEq, Fintype

/-- Worlds `(o, choice)`. Source: `firstperson.md` FP-22′. Kind: D -/
abbrev CfW : Type := Bool × Act2

/-- **The coverage-failure tree**: fair coin; index `0` (branch A) queries `d`, `a ↦ (1,a)` with
`r = 1`, `b ↦ (1,b)` with `r = 0`; index `1` (branch B) queries the dummy `e`, both edges to the
unconsulted `(1,a)`, `r = 1`.
Source: `firstperson.md` FP-22′ ("chance ½/½; branch A queries `d = (s, {o=1}, {a,b})` with
`a ↦ (1,a) r=1`, `b ↦ (1,b) r=0`; branch B an unconsulted leaf `(1,a) r=1`")
Kind: D
Fidelity: variant: branch B's leaf sits below a dummy point `e` (one child shape); nothing about
`d` changes -/
def coverFail : Tree CfW CfPt (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => .decision (if i = 0 then .d else .e) fun act =>
    .leaf (true, if i = 0 then act else .a) (if i = 0 ∧ act = .b then 0 else 1)

/-- `O_d = {o = 1}` (and the same for `e`, irrelevant). Source: `firstperson.md` FP-22′. Kind: D -/
def cfObs : CfPt → Finset CfW := fun _ => Finset.univ.filter fun w => w.1 = true

/-- `C = δ_a` at both points. Source: `firstperson.md` FP-22′ ("under `C = a`"). Kind: D -/
def cfProcA : Proc CfPt (fun _ => Act2) ℚ := Proc.ofFun fun _ => .a

/-- Leaf sums on `coverFail`. Source: none: infrastructure. Kind: L -/
theorem coverFail_sum {M : Type} [AddCommMonoid M] (f : coverFail.Leaves → M) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ∑ act : Act2, f ⟨i, act, ()⟩ := by
  unfold coverFail at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun act _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The leaf law on `coverFail`. Source: none: infrastructure. Kind: L -/
theorem coverFail_leafLaw (C : Proc CfPt (fun _ => Act2) ℚ) (i : Fin 2) (act : Act2) :
    leafLaw C coverFail ⟨i, act, ()⟩ =
      FinDistr.fair.w i * ((C (if i = 0 then .d else .e)).w act * 1) := by
  unfold coverFail
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf]

/-- The world at a leaf of `coverFail`. Source: none: infrastructure. Kind: L -/
theorem coverFail_world (i : Fin 2) (act : Act2) :
    world coverFail ⟨i, act, ()⟩ = (true, if i = 0 then act else .a) := by
  unfold coverFail; simp [world_chance, world_decision, world_leaf]

/-- The payoff at a leaf of `coverFail`. Source: none: infrastructure. Kind: L -/
theorem coverFail_payoff (i : Fin 2) (act : Act2) :
    payoff coverFail ⟨i, act, ()⟩ = if i = 0 ∧ act = .b then 0 else 1 := by
  unfold coverFail; simp [payoff_chance, payoff_decision, payoff_leaf]

/-- `#_d` on `coverFail`: one on branch A, zero on branch B. Source: none: infrastructure.
Kind: L -/
theorem coverFail_count_d (i : Fin 2) (act : Act2) :
    count .d coverFail ⟨i, act, ()⟩ = if i = 0 then 1 else 0 := by
  unfold coverFail
  simp only [count_chance, count_decision, count_leaf]
  fin_cases i <;> simp

/-- **Coverage fails at `d`**: the branch-B run (law `½`, world `(1,a) ∈ O_d`) passes no `d`-node.
Source: `firstperson.md` FP-22′ ("with coverage false")
Kind: N+ -/
theorem coverFail_not_covers : ¬ Covers cfObs cfProcA coverFail .d := by
  intro h
  have := h ⟨1, .a, ()⟩
    (by rw [coverFail_leafLaw]; simp [cfProcA, FinDistr.fair, FinDistr.coin]; norm_num)
    (by rw [coverFail_world]; simp [cfObs])
  rw [coverFail_count_d] at this
  simp at this

/-- `ν` under `δ_a` on `coverFail` is `δ_{(1,a)}`. Source: none: infrastructure. Kind: L -/
theorem coverFail_nu (X : Finset CfW) :
    nu cfProcA coverFail X = if (true, Act2.a) ∈ X then 1 else 0 := by
  rw [nu_eq_sum, coverFail_sum]
  simp only [coverFail_world, coverFail_leafLaw, Fin.sum_univ_two, Act2.sum_univ]
  simp [cfProcA, FinDistr.fair, FinDistr.coin] <;> split_ifs <;> norm_num

/-- The payoff mass under `δ_a`. Source: none: infrastructure. Kind: L -/
theorem coverFail_paySum (X : Finset CfW) :
    paySum cfProcA coverFail X = if (true, Act2.a) ∈ X then 1 else 0 := by
  rw [paySum_eq_sum_ite, coverFail_sum]
  simp only [coverFail_world, coverFail_leafLaw, coverFail_payoff, Fin.sum_univ_two, Act2.sum_univ]
  simp [cfProcA, FinDistr.fair, FinDistr.coin] <;> split_ifs <;> norm_num

/-- The occurrence-restricted masses under `δ_a`. Source: none: infrastructure. Kind: L -/
theorem coverFail_mass_occEv (X : Finset CfW) :
    mass cfProcA coverFail (occEv coverFail .d X) = if (true, Act2.a) ∈ X then 1 / 2 else 0 := by
  rw [mass_eq_sum_ite', coverFail_sum]
  simp only [occEv, Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_occ, coverFail_world, coverFail_leafLaw, coverFail_count_d, Fin.sum_univ_two, Act2.sum_univ]
  simp [cfProcA, FinDistr.fair, FinDistr.coin] <;> split_ifs <;> norm_num

/-- The occurrence-restricted payoff masses under `δ_a`. Source: none: infrastructure. Kind: L -/
theorem coverFail_occPay (X : Finset CfW) :
    occPay cfProcA coverFail .d X = if (true, Act2.a) ∈ X then 1 / 2 else 0 := by
  unfold occPay
  rw [sum_eq_sum_ite_mem (occEv coverFail .d X), coverFail_sum]
  simp only [occEv, Finset.mem_inter, worldEv, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_occ, coverFail_world, coverFail_leafLaw, coverFail_payoff, coverFail_count_d,
    Fin.sum_univ_two, Act2.sum_univ]
  simp [cfProcA, FinDistr.fair, FinDistr.coin] <;> split_ifs <;> norm_num

/-- `ν(O_d) = 1 > 0`. Source: none: infrastructure. Kind: L -/
theorem coverFail_nu_obs_pos : 0 < nu cfProcA coverFail (cfObs .d) := by
  rw [coverFail_nu]; simp [cfObs]

/-- `μ(occ(d)) = ½ > 0`. Source: none: infrastructure. Kind: L -/
theorem coverFail_occ_pos : 0 < mass cfProcA coverFail (occ .d coverFail) := by
  have := coverFail_mass_occEv Finset.univ
  rw [occEv_univ] at this
  rw [this]; simp

set_option maxHeartbeats 1000000 in
/-- **The base strict-OC state is per-run SSC at `d`** on `coverFail` under `δ_a`: both states
are `δ_{(1,a)}` with value `1` — the base audit passes although coverage fails.
Source: `firstperson.md` FP-22′ ("passes the audit at the strict … grade under `C = a` (both
sides `δ_{(1,a)}`)")
Kind: N+
Fidelity: exact (strict grade; the limit grade is not built) -/
theorem coverFail_oc_perRun :
    PerRunClausesAt (fun _ => calibratedState cfProcA coverFail (cfObs .d) coverFail_nu_obs_pos)
      cfProcA coverFail .d := by
  refine (agree_occState_iff_perRunClausesAt cfProcA coverFail
    (fun _ => calibratedState cfProcA coverFail (cfObs .d) coverFail_nu_obs_pos) .d
    coverFail_occ_pos).mp ?_
  have hocc := coverFail_mass_occEv Finset.univ
  rw [occEv_univ] at hocc
  refine ⟨?_, fun X hX => ?_⟩
  · apply FinDistr.ext'
    intro ω
    have h1 : (calibratedState cfProcA coverFail (cfObs .d) coverFail_nu_obs_pos).P.w ω =
        nu cfProcA coverFail ({ω} ∩ cfObs .d) / nu cfProcA coverFail (cfObs .d) := by
      have := calibratedState_pr cfProcA coverFail (cfObs .d) coverFail_nu_obs_pos {ω}
      simpa only [State.pr, probOf_singleton] using this
    have h2 : (occState cfProcA coverFail .d coverFail_occ_pos).P.w ω =
        mass cfProcA coverFail (occEv coverFail .d {ω}) /
          mass cfProcA coverFail (occ .d coverFail) := by
      have := occState_pr cfProcA coverFail .d coverFail_occ_pos {ω}
      simpa only [State.pr, probOf_singleton] using this
    rw [h1, h2, coverFail_mass_occEv, hocc, coverFail_nu, coverFail_nu]
    rcases ω with ⟨o, c⟩
    cases o <;> cases c <;> simp [cfObs]
  · rw [calibratedState_V, occState_V, coverFail_paySum, coverFail_nu, coverFail_occPay,
      coverFail_mass_occEv]
    have hpos : (true, Act2.a) ∈ X := by
      by_contra hc
      have := calibratedState_pr cfProcA coverFail (cfObs .d) coverFail_nu_obs_pos X
      simp only [State.pr] at this hX
      rw [this, coverFail_nu, coverFail_nu] at hX
      simp [cfObs, hc] at hX
    simp [hpos, cfObs]

/-- **The base audit passes on `coverFail`** (T1(a) applied). Source: `firstperson.md` FP-22′.
Kind: N+ -/
theorem coverFail_base_audit_passes
    (h : 0 < (priorState cfProcA (stamp {CfPt.d} coverFail)).pr
      (occW {CfPt.d} (Finset.mem_singleton_self _))) :
    AuditPassAt (priorState cfProcA (stamp {CfPt.d} coverFail))
      (occW {CfPt.d} (Finset.mem_singleton_self _)) h Prod.fst
      (calibratedState cfProcA coverFail (cfObs .d) coverFail_nu_obs_pos) :=
  (audit_iff_perRunClausesAt cfProcA coverFail {CfPt.d} (Finset.mem_singleton_self _)
    (fun _ => calibratedState cfProcA coverFail (cfObs .d) coverFail_nu_obs_pos) h).mpr
    coverFail_oc_perRun

/-- **FP-22′'s base-algebra `⟹` is refuted**: the license fails on `coverFail` (coverage fails)
while the base audit passes.
Source: `firstperson.md` FP-22′, Dead ("FP-22's biconditional … on the base algebra `𝓔`.
Killer: the 3-leaf coverage-failure tree")
Kind: N+ -/
theorem coverFail_license_fails : ¬ License cfObs cfProcA coverFail .d := by
  intro h
  exact coverFail_not_covers ((coversAS_iff_covers cfObs cfProcA coverFail .d).mp h.2)

/-- **Stamped, the strict-OC state fails at the strict grade** — by T2(a), since the license
fails: `(1,a,some a)` against `(1,a,none)`.
Source: `firstperson.md` FP-22′ ("stamped, it fails at every grade")
Kind: N+
Fidelity: exact at the strict grade (the limit and masked grades are not built) -/
theorem coverFail_stamped_fails
    (hO : 0 < nu cfProcA (stamp {CfPt.d} coverFail) (obsW {CfPt.d} (cfObs .d)))
    (h : 0 < (priorState cfProcA (stamp {CfPt.d} coverFail)).pr
      (occW {CfPt.d} (Finset.mem_singleton_self _))) :
    ¬ AuditPassAt (priorState cfProcA (stamp {CfPt.d} coverFail))
      (occW {CfPt.d} (Finset.mem_singleton_self _)) h id
      (calibratedState cfProcA (stamp {CfPt.d} coverFail) (obsW {CfPt.d} (cfObs .d)) hO) := by
  rw [audit_license_iff_nullDiff]
  exact coverFail_license_fails

/-- The `coverFail` occurrence guard on the stamped prior (`μ(occ(d)) = ½`).
Source: none: infrastructure. Kind: L -/
theorem coverFail_stamp_occ_pos :
    0 < (priorState cfProcA (stamp {CfPt.d} coverFail)).pr
      (occW {CfPt.d} (Finset.mem_singleton_self _)) := by
  rw [priorState_stamp_pr_occW]; exact coverFail_occ_pos

/-- The `coverFail` observation guard on the stamped problem (`ν(O_d) = 1`).
Source: none: infrastructure. Kind: L -/
theorem coverFail_stamp_nu_obs_pos :
    0 < nu cfProcA (stamp {CfPt.d} coverFail) (obsW {CfPt.d} (cfObs .d)) := by
  rw [nu_stamp_obsW {CfPt.d} cfProcA coverFail (cfObs .d)]; exact coverFail_nu_obs_pos

/-- **The base audit passes on `coverFail`, no guard left open.**
Source: `firstperson.md` FP-22′; audit r1 adversarial N3. Kind: N+ -/
theorem coverFail_base_audit_passes' :
    AuditPassAt (priorState cfProcA (stamp {CfPt.d} coverFail))
      (occW {CfPt.d} (Finset.mem_singleton_self _)) coverFail_stamp_occ_pos Prod.fst
      (calibratedState cfProcA coverFail (cfObs .d) coverFail_nu_obs_pos) :=
  coverFail_base_audit_passes _

/-- **Stamped, the strict-OC state fails on `coverFail`, no guard left open.**
Source: `firstperson.md` FP-22′ ("stamped, it fails at every grade"); audit r1 adversarial N3
Kind: N+
Fidelity: exact at the strict grade -/
theorem coverFail_stamped_fails' :
    ¬ AuditPassAt (priorState cfProcA (stamp {CfPt.d} coverFail))
      (occW {CfPt.d} (Finset.mem_singleton_self _)) coverFail_stamp_occ_pos id
      (calibratedState cfProcA (stamp {CfPt.d} coverFail) (obsW {CfPt.d} (cfObs .d))
        coverFail_stamp_nu_obs_pos) :=
  coverFail_stamped_fails _ _

/-! ## The radical-label tree -/

/-- **The radical-label tree** (AN-15): an evented fair coin — the world's first coordinate
records the side — `d` queried on side A (index `0`), the dummy `e` on side B, every leaf-world
`(side, choice)` with payoff `0`; `O_d = ⊤`.
Source: `anticipation.md` AN-15(b′) ("radical-label tree: `occ = λ⁻¹(side = A)`, `O_d = ⊤`")
Kind: D
Fidelity: variant: side B's leaves sit below a dummy point `e` (one child shape) -/
def radicalLabel : Tree CfW CfPt (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => .decision (if i = 0 then .d else .e) fun act =>
    .leaf (decide (i = 0), act) 0

/-- The radical observation `O = ⊤` at every point. Source: `anticipation.md` AN-15. Kind: D -/
def radObs : CfPt → Finset CfW := fun _ => Finset.univ

/-- The uniform procedure on the two points. Source: none: infrastructure. Kind: D -/
def cfUnif : Proc CfPt (fun _ => Act2) ℚ := fun _ => FinDistr.uniform

/-- The world at a leaf of `radicalLabel`. Source: none: infrastructure. Kind: L -/
theorem radicalLabel_world (i : Fin 2) (act : Act2) :
    world radicalLabel ⟨i, act, ()⟩ = (decide (i = 0), act) := by
  unfold radicalLabel; simp [world_chance, world_decision, world_leaf]

/-- `#_d` on `radicalLabel`. Source: none: infrastructure. Kind: L -/
theorem radicalLabel_count_d (i : Fin 2) (act : Act2) :
    count .d radicalLabel ⟨i, act, ()⟩ = if i = 0 then 1 else 0 := by
  unfold radicalLabel
  simp only [count_chance, count_decision, count_leaf]
  fin_cases i <;> simp

/-- `Fintype.card Act2 = 2`. Source: none: infrastructure. Kind: L -/
theorem act2_card : (Fintype.card Act2 : ℚ) = 2 := by
  rw [Fintype.card_eq_sum_ones, Act2.sum_univ]; norm_num

/-- The leaf law on `radicalLabel` under the uniform procedure is `¼` everywhere.
Source: none: infrastructure. Kind: L -/
theorem radicalLabel_leafLaw (i : Fin 2) (act : Act2) :
    leafLaw cfUnif radicalLabel ⟨i, act, ()⟩ = 1 / 4 := by
  unfold radicalLabel
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf]
  fin_cases i <;> simp [cfUnif, FinDistr.fair, FinDistr.coin, FinDistr.uniform_w, act2_card] <;>
    norm_num

/-- **`occ(d)` is expressible on the radical-label tree**: it is exactly `λ⁻¹{side = A}`.
Source: `anticipation.md` AN-15(b′) ("expressible")
Kind: N+ -/
theorem radicalLabel_occExpressible : OccExpressible cfUnif radicalLabel .d := by
  refine ⟨Finset.univ.filter fun w => w.1 = true, ?_, ?_⟩ <;>
  · rw [mass_eq_zero_iff]
    intro ℓ hℓ
    exfalso
    rcases ℓ with ⟨i, act, ⟨⟩⟩
    simp only [Finset.mem_sdiff, mem_occ, worldEv, Finset.mem_filter, Finset.mem_univ, true_and,
      radicalLabel_world, radicalLabel_count_d] at hℓ
    fin_cases i <;> simp at hℓ

/-- **SC's refinement measure fires on the radical-label tree**: with `O_d = ⊤` the observation
algebra has one atom, and `occ(d)` (side A) is a proper subset of positive mass — the density of
`μ(· | occ(d))` is not constant on the atom (`density_const_iff_occ_union`), although `occ(d)` is
expressible. Together with `occ_univ_occUnion` (silent on `mug1`, TN-V2): the measure does not
track `𝓔`-expressibility in either direction (finding against SC open question 1).
Source: `anticipation.md` AN-15(b′) ("radical-label tree … `1` bit"), Dead 6
Kind: N+ -/
theorem radicalLabel_not_occUnion : ¬ OccUnionOfObsAtoms radObs cfUnif radicalLabel .d := by
  intro h
  have := h ⟨0, .a, ()⟩ ⟨1, .a, ()⟩ (by rw [radicalLabel_leafLaw]; norm_num)
    (by rw [radicalLabel_leafLaw]; norm_num) (by funext e; simp [obsAtom, radObs])
  simp only [mem_occ, radicalLabel_count_d] at this
  simp at this

end Cleanroom.Decision.DpFirstpersonSc
