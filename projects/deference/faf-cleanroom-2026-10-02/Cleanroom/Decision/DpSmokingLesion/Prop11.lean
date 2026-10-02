import Cleanroom.Decision.DpSmokingLesion.Lemma3
import Cleanroom.Decision.DpCalibration.Corollaries

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

/-!
# T2: Proposition 11 refuted as printed; true under (S4)

[[dp-smoking-lesion-mandate]] T2, source [[decision-problems-v2]] §7.3 line 258.

* **(a) Refutation on E2a** (`prop11_refuted_e2a`): on the reference-class tree at S3's numbers
  (`π = 1/10`, `ρ = ½`, `γ = (99/100, 1/100)`, `σ = (9/10, 1/10)`, `α = 1000`, `β = 10⁶`) the
  strictly calibrated state at `⊤` satisfies (S2) **for every procedure** — the cross-multiplied
  gap `ν(k ∧ m=1)·ν(m=0) − ν(k ∧ m=0)·ν(m=1)` is the constant `441/2500`, whatever `C(d)`
  (`e2a_gap_const`) — so `Σ_SL(S1–S3)` is strict-, masked- (interior self-model) and
  limit-consistent for every `C` (`sigmaSL123_consistent_strict/masked/limit`), refuting
  "inconsistent for every procedure" as a claim about (S1)–(S3). At `δ_refrain` the conditionals
  are `223/250 > 493/2750` (S3's numbers), at `δ_smoke` `2257/2750 > 27/250` (S2's).
* **(b) Proposition 11 under (S4)** (`prop11_of_recordsFor`, `prop11_masked_of_recordsForDeviations`,
  `prop11_limit_of_recordsFor`): at a recorded `O_d = ⊤` point with cancer post-query independent
  of the draw, no strictly-calibrated, masked-calibrated (recording for the self-models) or
  limit-calibrated state satisfies (S2) — from `General.lean`'s post-query screening, the
  statistics' flatness, never from a stated leaf mass; on `slOne` for every procedure and every
  sense (`prop11_slOne_*`), hence `¬ Consistent κ ⊤ Σ_SL(S1–S4) C` for `κ ∈ {strict, masked, limit}`
  and every `C` (`sigmaSL1234_not_consistent_*`). Deterministic `C` needs no detour: nothing
  below assumes full support of `C`.
* **(c) N+** (`prop11_slOne_instance`): the hypothesis package is inhabited non-degenerately —
  `slOne` at the FDT numbers and `C(d) = ½`, with the strictly calibrated state, has
  `P(m=1) = P(m=0) = ½ > 0` and flat conditionals `P(k ∣ m) = ½`.
-/

namespace Cleanroom.Decision.DpSmokingLesion

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration

/-! ## Proposition 11 under recording: the general statements -/

section general

variable {ι : Type} [DecidableEq ι] (C : Proc ι (fun _ => Bool) ℚ) (B : Tree TickleW ι (fun _ => Bool) ℚ)
  (d : ι)

/-- **Proposition 11 under (S4), strict grade**: at a point recorded for `C` with `O_d = ⊤` and
cancer post-query independent of the draw, no state satisfying the strict clauses for `C` at
`d` satisfies (S2).
Source: [[decision-problems-v2]] §7.3 Proposition 11 ("the stipulated state is not a possible
worldview of any instantiation"), under (S4); `sl-synthesis.md` §1.3 ("Proposition 11 holds under
(S1)–(S4) and is a consequence of recording"); mandate T2(b)
Kind: C
Fidelity: exact (recording form: `RecordsFor` for `C`; `O_d = ⊤`; the lesion-only clause as
`PostQueryIndep`)
Hyps: (a) `RecordsFor slObs slActEv C B d`; (a) `PostQueryIndep C B d evK`; (a) strict clauses
at `d` -/
theorem prop11_of_recordsFor (hrec : RecordsFor slObs slActEv C B d)
    (hK : PostQueryIndep C B d evK) (s : ι → State TickleW ℚ)
    (hs : StrictClausesAt s slObs C B d) : ¬ S2 (s d) :=
  not_S2_of_nuFlat s C B d hs.1 (nuFlat_of_recordsFor_postQueryIndep C B d hrec hK)

/-- **Proposition 11 under (S4), masked grade**: if every point-deviation `C[d ↦ m]` records at
`d` (recording *for the self-model*, dp-sl-2-043(b)) and cancer is post-query independent of the
draw under each, then no masked-calibrated state at `d` (Definition 9, LF/vacuity) satisfies
(S2). The vacuity disjunct cannot fire (`ν(⊤) = 1` under every self-model).
Source: [[decision-problems-v2]] §7.3 Proposition 11 ("a masked-calibrated state equals
`ν_{B,C'}(· ∣ ⊤)` for some full-support `C'`, and Lemma 3 applies to `C'`"); dp-sl-2-043(b);
mandate T2(b)
Kind: C
Fidelity: exact (recording form: `RecordsForDeviations`, i.e. for every self-model `C[d ↦ m]`)
Hyps: (a) `RecordsForDeviations slObs slActEv C B d`; (a) `PostQueryIndep` for every
`C[d ↦ m]`; (a) `MaskedOCAt s slObs C B d` -/
theorem prop11_masked_of_recordsForDeviations (hdev : RecordsForDeviations slObs slActEv C B d)
    (hK : ∀ m, PostQueryIndep (C.deviate d m) B d evK) (s : ι → State TickleW ℚ)
    (hs : MaskedOCAt s slObs C B d) : ¬ S2 (s d) := by
  rcases hs with ⟨C', ⟨m, -, rfl⟩, -, hcl⟩ | ⟨-, hnull⟩
  · exact prop11_of_recordsFor (C.deviate d m) B d (hdev m) (hK m) s hcl
  · exfalso
    have := hnull (C.deviate d FinDistr.uniform)
      ⟨FinDistr.uniform, fun a => FinDistr.uniform_w_pos a, rfl⟩
    rw [slObs_apply, nu_univ] at this
    exact one_ne_zero this

/-- **Proposition 11 under (S4), limit grade**: at a recorded `O_d = ⊤` point, no
limit-calibrated state satisfies (S2) (limit calibration implies strict calibration, Lemma 2,
and `ν(⊤) = 1 > 0`).
Source: [[decision-problems-v2]] §7.3 Proposition 11 ("with no detour through limit
calibration"); mandate T2(b)
Kind: C
Fidelity: exact (recording form: `RecordsFor` for `C`)
Hyps: (a) recording for `C`; (a) `PostQueryIndep`; (a) `LimitOCAt` -/
theorem prop11_limit_of_recordsFor (hrec : RecordsFor slObs slActEv C B d)
    (hK : PostQueryIndep C B d evK) (s : ι → State TickleW ℚ)
    (hs : LimitOCAt s slObs C B d) : ¬ S2 (s d) :=
  prop11_of_recordsFor C B d hrec hK s
    (limitOCAt_imp_strictOCAt s slObs C B d hs (by rw [slObs_apply]; exact nu_univ_pos C B))

end general

/-! ## Proposition 11 on the enumerated instantiation, all three OC grades -/

section slOne

variable (L : Lesion) (α β : ℚ) (C : Proc Unit (fun _ => Bool) ℚ)

/-- Proposition 11 on `slOne`, strict grade: for every procedure and every state strictly
calibrated at `d`, (S2) fails.
Source: [[decision-problems-v2]] §7.3 Proposition 11; mandate T2(b) (shape-form corollary)
Kind: C
Fidelity: exact on the enumerated instantiation
Hyps: (a) `StrictOCAt` -/
theorem prop11_slOne_strict (s : Unit → State TickleW ℚ)
    (hs : StrictOCAt s slObs C (slOne L α β) ()) : ¬ S2 (s ()) :=
  prop11_of_recordsFor C (slOne L α β) () (slOne_recordsFor L α β C)
    (slOne_lesionOnlyAt L α β C).postQueryIndep s (hs (by rw [slObs_apply]; exact nu_univ_pos _ _))

/-- Proposition 11 on `slOne`, masked grade: `slOne` records for every procedure, so every
self-model records, and no masked-calibrated state satisfies (S2).
Source: [[decision-problems-v2]] §7.3 Proposition 11; mandate T2(b)
Kind: C
Fidelity: exact on the enumerated instantiation
Hyps: (a) `MaskedOCAt` -/
theorem prop11_slOne_masked (s : Unit → State TickleW ℚ)
    (hs : MaskedOCAt s slObs C (slOne L α β) ()) : ¬ S2 (s ()) :=
  prop11_masked_of_recordsForDeviations C (slOne L α β) ()
    ((slOne_recordsForAll L α β).deviations slObs slActEv C)
    (fun m => (slOne_lesionOnlyAt L α β (C.deviate () m)).postQueryIndep) s hs

/-- Proposition 11 on `slOne`, limit grade.
Source: [[decision-problems-v2]] §7.3 Proposition 11; mandate T2(b)
Kind: C
Fidelity: exact on the enumerated instantiation
Hyps: (a) `LimitOCAt` -/
theorem prop11_slOne_limit (s : Unit → State TickleW ℚ)
    (hs : LimitOCAt s slObs C (slOne L α β) ()) : ¬ S2 (s ()) :=
  prop11_limit_of_recordsFor C (slOne L α β) () (slOne_recordsFor L α β C)
    (slOne_lesionOnlyAt L α β C).postQueryIndep s hs

/-- `d` is queried on `slOne`. Source: none: infrastructure. Kind: L -/
theorem slOne_queried : queried (slOne L α β) = {()} := by
  unfold slOne kBlock slLeaf
  ext x; cases x; simp

/-- **`Σ_SL(S1–S4)` is strict-inconsistent for every procedure** (Proposition 11 as a
`Consistent` statement, Definition 15).
Source: [[decision-problems-v2]] §7.3 Proposition 11 ("`Σ_SL` is inconsistent for *every*
procedure"); mandate T2(b)
Kind: C
Fidelity: weaker: shape family (`Σ_SL(S1–S4)` = `slOne` at every parameter)
Hyps: none -/
theorem sigmaSL1234_not_consistent_strict : ¬ Consistent .strict slObs sigmaSL1234 C := by
  rintro ⟨I, ⟨⟨L, α, β, -, -, -, hB⟩, hS2⟩, hcal⟩
  have hs : StrictOCAt I.s slObs C I.B () := by
    apply hcal
    rw [hB, slOne_queried]; exact Finset.mem_singleton_self _
  rw [hB] at hs
  exact prop11_slOne_strict L α β C I.s hs hS2

/-- `Σ_SL(S1–S4)` is masked-inconsistent for every procedure.
Source: [[decision-problems-v2]] §7.3 Proposition 11; mandate T2(b)
Kind: C
Fidelity: weaker: shape family; masked = LF/vacuity (the vacuity disjunct never fires at `⊤`)
Hyps: none -/
theorem sigmaSL1234_not_consistent_masked : ¬ Consistent .masked slObs sigmaSL1234 C := by
  rintro ⟨I, ⟨⟨L, α, β, -, -, -, hB⟩, hS2⟩, hcal⟩
  have hs : MaskedOCAt I.s slObs C I.B () := by
    apply hcal
    rw [hB, slOne_queried]; exact Finset.mem_singleton_self _
  rw [hB] at hs
  exact prop11_slOne_masked L α β C I.s hs hS2

/-- `Σ_SL(S1–S4)` is limit-inconsistent for every procedure.
Source: [[decision-problems-v2]] §7.3 Proposition 11; mandate T2(b)
Kind: C
Fidelity: weaker: shape family
Hyps: none -/
theorem sigmaSL1234_not_consistent_limit : ¬ Consistent .limit slObs sigmaSL1234 C := by
  rintro ⟨I, ⟨⟨L, α, β, -, -, -, hB⟩, hS2⟩, hcal⟩
  have hs : LimitOCAt I.s slObs C I.B () := by
    apply hcal
    rw [hB, slOne_queried]; exact Finset.mem_singleton_self _
  rw [hB] at hs
  exact prop11_slOne_limit L α β C I.s hs hS2

/-- **N+ for Proposition 11**: on `slOne` at the FDT numbers with `C(d) = ½`, the strictly
calibrated state at `⊤` has `P(m=1) = P(m=0) = ½` (both conditionals defined, the label
interior) and `P(k ∧ m=1) = P(k ∧ m=0) = ¼` (flat conditionals `½`): the hypothesis package of
`prop11_slOne_strict` is inhabited away from the degenerate deterministic case.
Source: mandate T2(c)
Kind: N+ -/
theorem prop11_slOne_instance :
    let C₀ := procBool (1/2) (by norm_num) (by norm_num)
    let B₀ := slOne Lesion.fdt 1000 1000000
    let s₀ : Unit → State TickleW ℚ := fun _ => calibratedState C₀ B₀ Finset.univ (nu_univ_pos _ _)
    StrictOCAt s₀ slObs C₀ B₀ () ∧ (s₀ ()).pr (evM true) = 1/2 ∧ (s₀ ()).pr (evM false) = 1/2 ∧
      (s₀ ()).pr (evK ∩ evM true) = 1/4 ∧ (s₀ ()).pr (evK ∩ evM false) = 1/4 ∧ ¬ S2 (s₀ ()) := by
  intro C₀ B₀ s₀
  have hs : StrictOCAt s₀ slObs C₀ B₀ () := strictOCAt_calibratedState slObs C₀ B₀ s₀ () _ rfl
  refine ⟨hs, ?_, ?_, ?_, ?_, prop11_slOne_strict Lesion.fdt 1000 1000000 C₀ s₀ hs⟩
  · simp only [s₀, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, B₀, C₀]
    rw [slOne_nu_m]; simp [procBool]
  · simp only [s₀, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, B₀, C₀]
    rw [slOne_nu_m]; simp [procBool]; norm_num
  · simp only [s₀, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, B₀, C₀]
    rw [slOne_nu_k_m]; simp [procBool, Lesion.fdt]; norm_num
  · simp only [s₀, calibratedState_pr, Finset.inter_univ, nu_univ, div_one, B₀, C₀]
    rw [slOne_nu_k_m]; simp [procBool, Lesion.fdt]; norm_num

end slOne

/-! ## The reference class E2a at S3's numbers -/

section e2a

/-- The "me" branch of E2a at lesion index `i`: the queried `d`-node.
Source: `sl_zoo.py` line 136
Kind: D -/
def e2aMe (i : Fin 2) : Tree TickleW Unit (fun _ => Bool) ℚ :=
  .decision () fun m => kBlock Lesion.fdt 1000 1000000 (decide (i = 0)) m

/-- The "other" branch of E2a at lesion index `i`: the reference class writes `m ∼ Bern(σ_ℓ)`.
Source: `sl_zoo.py` line 137
Kind: D -/
def e2aOther (i : Fin 2) : Tree TickleW Unit (fun _ => Bool) ℚ :=
  .chance 2 (RefClass.s3.coinM (decide (i = 0))) fun j =>
    kBlock Lesion.fdt 1000 1000000 (decide (i = 0)) (decide (j = 0))

/-- **E2a at S3's numbers**: `π = 1/10`, the FDT lesion, `σ = (9/10, 1/10)`, `α = 1000`,
`β = 10⁶`.
Source: `sl-defensible-claims.md` S3; mandate §3.7
Kind: D -/
def e2a₀ : Tree TickleW Unit (fun _ => Bool) ℚ :=
  .chance 2 Lesion.fdt.coinL fun i =>
    .chance 2 (FinDistr.coin (1/10) (by norm_num) (by norm_num)) ![e2aMe i, e2aOther i]

/-- `e2a₀` is the catalogue tree `e2a` at S3's parameters. Source: none: infrastructure. Kind: L -/
theorem e2a₀_eq : e2a₀ = e2a (1/10) (by norm_num) (by norm_num) Lesion.fdt RefClass.s3 1000 1000000 :=
  rfl

/-- A sum over the leaves of `e2a₀`: per lesion branch, the four "me" leaves and the four
"other" leaves.
Source: none: infrastructure. Kind: L -/
theorem e2a_sum (f : e2a₀.Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ i : Fin 2, ((∑ m : Bool, ∑ j : Fin 2, f ⟨i, 0, m, j, ()⟩) +
      ∑ j : Fin 2, ∑ k : Fin 2, f ⟨i, 1, j, k, ()⟩) := by
  unfold e2a₀ at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_chance, Fin.sum_univ_two]
  show (∑ ℓ : (e2aMe i).Leaves, f ⟨i, 0, ℓ⟩) + (∑ ℓ : (e2aOther i).Leaves, f ⟨i, 1, ℓ⟩) = _
  congr 1
  · unfold e2aMe kBlock slLeaf
    rw [sum_leaves_decision]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Tree.sum_leaves_leaf _ _ _
  · unfold e2aOther kBlock slLeaf
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sum_leaves_chance]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact Tree.sum_leaves_leaf _ _ _

/-- The "me" leaf masses of `e2a₀`: `μ(ℓ; me; m, k) = ½ · (1/10) · C(d)(m) · γ_{ℓ,k}`.
Source: Definition 6 on E2a
Kind: L -/
theorem e2a_leafLaw_me (C : Proc Unit (fun _ => Bool) ℚ) (i : Fin 2) (m : Bool) (j : Fin 2) :
    leafLaw C e2a₀ ⟨i, 0, m, j, ()⟩ =
      (1/2 : ℚ) * (1/10) * (C ()).w m *
        (if i = 0 then (if j = 0 then 99/100 else 1/100) else (if j = 0 then 1/100 else 99/100)) := by
  unfold e2a₀
  rw [leafLaw_chance, leafLaw_chance]
  show (Lesion.fdt.coinL).w i * ((FinDistr.coin (1/10) _ _).w 0 * leafLaw C (e2aMe i) ⟨m, j, ()⟩) = _
  unfold e2aMe kBlock slLeaf
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, Lesion.coinL, Lesion.coinK,
    FinDistr.coin, tickleGamma, Lesion.fdt]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- The "other" leaf masses of `e2a₀`: `μ(ℓ; other; m, k) = ½ · (9/10) · σ_{ℓ,m} · γ_{ℓ,k}`.
Source: Definition 6 on E2a
Kind: L -/
theorem e2a_leafLaw_other (C : Proc Unit (fun _ => Bool) ℚ) (i j k : Fin 2) :
    leafLaw C e2a₀ ⟨i, 1, j, k, ()⟩ =
      (1/2 : ℚ) * (9/10) *
        (if i = 0 then (if j = 0 then 9/10 else 1/10) else (if j = 0 then 1/10 else 9/10)) *
        (if i = 0 then (if k = 0 then 99/100 else 1/100) else (if k = 0 then 1/100 else 99/100)) := by
  unfold e2a₀
  rw [leafLaw_chance, leafLaw_chance]
  show (Lesion.fdt.coinL).w i * ((FinDistr.coin (1/10) _ _).w 1 * leafLaw C (e2aOther i) ⟨j, k, ()⟩) = _
  unfold e2aOther kBlock slLeaf
  simp only [leafLaw_chance, leafLaw_leaf, Lesion.coinL, Lesion.coinK, RefClass.coinM,
    FinDistr.coin, tickleGamma, Lesion.fdt, RefClass.s3]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp <;> norm_num

/-- The worlds at the leaves of `e2a₀`. Source: none: infrastructure. Kind: L -/
theorem e2a_world :
    (∀ (i : Fin 2) (m : Bool) (j : Fin 2),
      world e2a₀ ⟨i, 0, m, j, ()⟩ = (decide (i = 0), m, decide (j = 0))) ∧
    (∀ (i j k : Fin 2),
      world e2a₀ ⟨i, 1, j, k, ()⟩ = (decide (i = 0), decide (j = 0), decide (k = 0))) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- `ν` on `e2a₀` as an explicit sixteen-term sum. Source: none: infrastructure. Kind: L -/
theorem e2a_nu (C : Proc Unit (fun _ => Bool) ℚ) (X : Finset TickleW) :
    nu C e2a₀ X =
      ∑ i : Fin 2, ((∑ m : Bool, ∑ j : Fin 2,
        if (decide (i = 0), m, decide (j = 0)) ∈ X then leafLaw C e2a₀ ⟨i, 0, m, j, ()⟩ else 0) +
      ∑ j : Fin 2, ∑ k : Fin 2,
        if (decide (i = 0), decide (j = 0), decide (k = 0)) ∈ X then
          leafLaw C e2a₀ ⟨i, 1, j, k, ()⟩ else 0) := by
  rw [nu_eq_sum, e2a_sum]
  rfl

/-- `paySum` on `e2a₀` as an explicit sixteen-term sum. Source: none: infrastructure. Kind: L -/
theorem e2a_paySum (C : Proc Unit (fun _ => Bool) ℚ) (X : Finset TickleW) :
    paySum C e2a₀ X =
      ∑ i : Fin 2, ((∑ m : Bool, ∑ j : Fin 2,
        if (decide (i = 0), m, decide (j = 0)) ∈ X then
          leafLaw C e2a₀ ⟨i, 0, m, j, ()⟩ * ticklePay 1000 1000000 (decide (i = 0), m, decide (j = 0))
        else 0) +
      ∑ j : Fin 2, ∑ k : Fin 2,
        if (decide (i = 0), decide (j = 0), decide (k = 0)) ∈ X then
          leafLaw C e2a₀ ⟨i, 1, j, k, ()⟩ *
            ticklePay 1000 1000000 (decide (i = 0), decide (j = 0), decide (k = 0))
        else 0) := by
  rw [paySum_eq_sum_ite, e2a_sum]
  rfl

variable (C : Proc Unit (fun _ => Bool) ℚ)

/-- **The four (S2) masses on E2a as closed forms in the label `q = C(d)(smoke)`**:
`ν(m=1) = q/10 + 9/20`, `ν(k ∧ m=1) = q/20 + 2007/5000`, `ν(m=0) = (1−q)/10 + 9/20`,
`ν(k ∧ m=0) = (1−q)/20 + 243/5000`.
Source: `sl-defensible-claims.md` S3 (the numbers at `δ_refrain`), S2 (at `δ_smoke`); mandate
T2(a) ("closed forms in `q`")
Kind: P
Fidelity: exact -/
theorem e2a_nu_values :
    nu C e2a₀ (evM true) = (C ()).w true / 10 + 9/20 ∧
    nu C e2a₀ (evK ∩ evM true) = (C ()).w true / 20 + 2007/5000 ∧
    nu C e2a₀ (evM false) = (1 - (C ()).w true) / 10 + 9/20 ∧
    nu C e2a₀ (evK ∩ evM false) = (1 - (C ()).w true) / 20 + 243/5000 := by
  have hw := w_false_eq_one_sub C
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [e2a_nu]
    simp only [Fin.sum_univ_two, Fintype.sum_bool, e2a_leafLaw_me, e2a_leafLaw_other,
      Finset.mem_inter, mem_evM, mem_evK]
    simp [hw]; ring

/-- **The (S2) gap on E2a is label-independent**:
`ν(k ∧ m=1)·ν(m=0) − ν(k ∧ m=0)·ν(m=1) = 441/2500` for every procedure — the correlation is
written entirely by the reference class; the agent's own draws contribute flat conditionals.
Source: mandate T2(a) ("the same for `C = δ_smoke` and for `C(d) = q`"); this constancy is the
package's observation
Kind: P
Fidelity: exact -/
theorem e2a_gap_const :
    nu C e2a₀ (evK ∩ evM true) * nu C e2a₀ (evM false) -
      nu C e2a₀ (evK ∩ evM false) * nu C e2a₀ (evM true) = 441/2500 := by
  obtain ⟨h1, h2, h3, h4⟩ := e2a_nu_values C
  rw [h1, h2, h3, h4]; ring

/-- **(S2) at the strictly calibrated state of E2a, for every procedure.**
Source: `sl-defensible-claims.md` S3 ("at `C = refrain`, (S2)"); mandate T2(a)
Kind: P
Fidelity: exact
Hyps: none -/
theorem e2a_S2_calibrated (C' : Proc Unit (fun _ => Bool) ℚ) :
    S2 (calibratedState C' e2a₀ Finset.univ (nu_univ_pos _ _)) := by
  obtain ⟨h1, h2, h3, h4⟩ := e2a_nu_values C'
  have hq0 := (C' ()).nonneg true
  have hq1 := (C' ()).w_le_one true
  unfold S2
  simp only [calibratedState_pr, Finset.inter_univ, nu_univ, div_one]
  refine ⟨by rw [h1]; linarith, by rw [h3]; linarith, ?_⟩
  have := e2a_gap_const C'
  linarith

/-- `d` is queried on `e2a₀`. Source: none: infrastructure. Kind: L -/
theorem e2a_queried : queried e2a₀ = {()} := by
  unfold e2a₀ e2aMe e2aOther kBlock slLeaf
  ext x; cases x; simp

/-- `e2a₀` is an (S1)–(S3) instantiation. Source: none: infrastructure. Kind: L -/
theorem e2a_isS123Tree : IsS123Tree e2a₀ :=
  ⟨Lesion.fdt, 1000, 1000000, by unfold Lesion.S1 Lesion.fdt; norm_num, by norm_num, by norm_num,
    Or.inr (Or.inr (Or.inl ⟨1/10, by norm_num, by norm_num, RefClass.s3, e2a₀_eq⟩))⟩

/-- **`Σ_SL(S1–S3)` is strict-consistent for every procedure** (E2a witnesses it): the
strictly calibrated state at `⊤` satisfies (S2).
Source: [[decision-problems-v2]] §7.3 Proposition 11, refuted as a claim about (S1)–(S3);
dp-sl-009; `sl-defensible-claims.md` S3; mandate T2(a)
Kind: P
Fidelity: weaker: shape family; the reading of v2's "Instantiations:" line as a stipulation is
ATTRIBUTION-UNVETTED (C1 Open 2) — under that reading this row refutes nothing
Hyps: none -/
theorem sigmaSL123_consistent_strict : Consistent .strict slObs sigmaSL123 C :=
  ⟨⟨e2a₀, fun _ => calibratedState C e2a₀ Finset.univ (nu_univ_pos _ _)⟩,
    ⟨e2a_isS123Tree, e2a_S2_calibrated C⟩,
    fun d _ => by
      cases d
      exact strictOCAt_calibratedState slObs C e2a₀ _ () _ rfl⟩

/-- **`Σ_SL(S1–S3)` is masked-consistent for every procedure**: the state calibrated to the
interior self-model `C[d ↦ (½, ½)]` satisfies (S2) (`e2a_S2_calibrated` at the self-model).
Source: [[decision-problems-v2]] §7.3 Proposition 11 (masked), refuted for (S1)–(S3); mandate
T2(a)
Kind: P
Fidelity: weaker: shape family; masked = LF/vacuity, first disjunct (the reading is inert)
Hyps: none -/
theorem sigmaSL123_consistent_masked : Consistent .masked slObs sigmaSL123 C :=
  ⟨⟨e2a₀, fun _ => calibratedState (C.deviate () (FinDistr.bool (1/2) (by norm_num) (by norm_num)))
      e2a₀ Finset.univ (nu_univ_pos _ _)⟩,
    ⟨e2a_isS123Tree, e2a_S2_calibrated _⟩,
    fun d _ => by
      cases d
      exact maskedOCAt_calibratedState slObs C e2a₀ _ () _
        (fun a => by cases a <;> norm_num [FinDistr.bool_true, FinDistr.bool_false]) _ rfl⟩

/-- **`Σ_SL(S1–S3)` is limit-consistent for every procedure**: at a realized point
(`ν(⊤) = 1`) the limit state is the strict one (`limitOCAt_of_strictOCAt_of_pos`).
Source: [[decision-problems-v2]] §7.3 Proposition 11 (limit), refuted for (S1)–(S3); mandate
T2(a)
Kind: C
Fidelity: weaker: shape family
Hyps: none -/
theorem sigmaSL123_consistent_limit : Consistent .limit slObs sigmaSL123 C :=
  ⟨⟨e2a₀, fun _ => calibratedState C e2a₀ Finset.univ (nu_univ_pos _ _)⟩,
    ⟨e2a_isS123Tree, e2a_S2_calibrated C⟩,
    fun d _ => by
      cases d
      exact limitOCAt_of_strictOCAt_of_pos _ slObs C e2a₀ () (nu_univ_pos _ _)
        (strictOCAt_calibratedState slObs C e2a₀ _ () _ rfl)⟩

/-- **Proposition 11 refuted as printed**: on (S1)–(S3) as a set of stipulations (the
four-shape family), `Σ_SL` is strict-, masked- and limit-consistent for **every** procedure —
E2a's calibrated state satisfies (S2) at all three grades — so "inconsistent for every
procedure" is false without (S4). Numbers: at `δ_refrain`, `P(k ∣ m=1) = 223/250 > 493/2750 =
P(k ∣ m=0)`; at `δ_smoke`, `2257/2750 > 27/250`.
Source: [[decision-problems-v2]] §7.3 line 258 ("Under (S3), `Σ_SL` is inconsistent for *every*
procedure, deterministic included … The stipulated state is not a possible worldview of any
instantiation"), refuted as a claim about (S1)–(S3); dp-sl-009; dp-core-045; `sl-defensible-claims.md`
S3; mandate T2(a)
Kind: P
Fidelity: exact for the refutation (the refuted sentence is `¬ Consistent κ ⊤ Σ_SL(S1–S3) C`);
weaker: shape family; whether v2's "Instantiations:" line is a stipulation is
ATTRIBUTION-UNVETTED (C1 Open 2) — under that reading Proposition 11 is true (T2(b))
Hyps: none -/
theorem prop11_refuted_e2a :
    (∀ C : Proc Unit (fun _ => Bool) ℚ, Consistent .strict slObs sigmaSL123 C ∧
      Consistent .masked slObs sigmaSL123 C ∧ Consistent .limit slObs sigmaSL123 C) ∧
    nu procRefrain e2a₀ (evK ∩ evM true) / nu procRefrain e2a₀ (evM true) = 223/250 ∧
    nu procRefrain e2a₀ (evK ∩ evM false) / nu procRefrain e2a₀ (evM false) = 493/2750 ∧
    nu procSmoke e2a₀ (evK ∩ evM true) / nu procSmoke e2a₀ (evM true) = 2257/2750 ∧
    nu procSmoke e2a₀ (evK ∩ evM false) / nu procSmoke e2a₀ (evM false) = 27/250 := by
  refine ⟨fun C => ⟨sigmaSL123_consistent_strict C, sigmaSL123_consistent_masked C,
    sigmaSL123_consistent_limit C⟩, ?_, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, -, -⟩ := e2a_nu_values procRefrain
    rw [h1, h2]; simp [procRefrain]; norm_num
  · obtain ⟨-, -, h3, h4⟩ := e2a_nu_values procRefrain
    rw [h3, h4]; simp [procRefrain]; norm_num
  · obtain ⟨h1, h2, -, -⟩ := e2a_nu_values procSmoke
    rw [h1, h2]; simp [procSmoke]; norm_num
  · obtain ⟨-, -, h3, h4⟩ := e2a_nu_values procSmoke
    rw [h3, h4]; simp [procSmoke]; norm_num

end e2a

end Cleanroom.Decision.DpSmokingLesion
