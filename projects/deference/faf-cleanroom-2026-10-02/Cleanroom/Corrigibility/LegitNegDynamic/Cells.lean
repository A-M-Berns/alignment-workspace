import Cleanroom.Corrigibility.LegitNegStatic.Readouts
import Cleanroom.Corrigibility.LegitNegStatic.Toys
import Cleanroom.Corrigibility.LegitNegPricing.Basic

/-!
# Cells and policies: the T1/T2 layer of the legitimacy decision problem

Package `legit-neg-dynamic` (faf-cleanroom run, 2026-09-30), definition (a) of the mandate and
target 2 (D2(i)). Sources: `clusters/D/NEGATIVES.md` "Conventions" (timing, dynamic consistency,
value of information) and D2(i); `clusters/D/fixtures/d2_conditioning_dynamic.py` (`cell_lottery`,
`t1_values`, `t2_values`); pinned by [[corr-legit-neg-inventory]] item 046.

The objects: an information partition `cellOf` of the starting states (three axioms, no purity),
cell-measurable policies `CellPolicy`, the T1 objectives of a policy (`policyValue` = cdot,
`policyPL`, `policyP2` under the exclusion convention, `policyShifted lam` = cdot with every void
world scored `lam`), the T2 objectives as `P.restrict (cellOf s)` (static's T2 problem), and the
tower identity that ties them. Target 2's content: for *any* per-terminal utility `U`, a
cell-optimal policy is T1-optimal among cell policies (`cellOptimal_T1_optimal`), conversely a
T1-optimal cell policy is cell-optimal on every cell (`cellOptimal_of_T1_optimal`), and Good's
theorem (`P1_le_policyValue`, `VOI_nonneg`). All of it instantiates to P1, P3 and P4b with fixed
per-terminal void grades; P2 is *not* a per-terminal utility (its T1 objective is a ratio), which is
what `Dinkelbach.lean` is about.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem

variable {S A : Type} [Fintype S] [Fintype A]

section Defs

variable [DecidableEq S]

/-- An information partition of the starting states: `s` lies in its own cell, cells are
consistent (`t ∈ cellOf s → cellOf t = cellOf s`), and every cell has positive prior mass (the
fixture `assert`s it; T2 conditions on a cell). **No purity**: a cell may leave the legitimacy of
an option open — that is the whole point of the T1/T2 distinction (D1(ii)).
Source: [[corr-legit-neg-inventory]] item 046; pricing target 9 (ii)'s partition axioms
Kind: D
Fidelity: exact -/
structure IsPartition (P : Problem S A) (cellOf : S → Finset S) : Prop where
  mem : ∀ s, s ∈ cellOf s
  cell : ∀ s t, t ∈ cellOf s → cellOf t = cellOf s
  pos : ∀ s, 0 < ∑ t ∈ cellOf s, P.prior t

/-- Membership in cells is symmetric under the partition axioms.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma IsPartition.mem_comm {P : Problem S A} {cellOf : S → Finset S} (hP : IsPartition P cellOf)
    {s t : S} : t ∈ cellOf s ↔ s ∈ cellOf t :=
  ⟨fun h => by rw [hP.cell s t h]; exact hP.mem s, fun h => by rw [hP.cell t s h]; exact hP.mem t⟩

/-- A **policy** is a map from starting states to actions; it is a **cell policy** (measurable
with respect to the agent's information) when it is constant on every cell. T1 chooses among
cell policies; T2 chooses an action after learning the cell.
Source: `clusters/D/NEGATIVES.md` "Timing"; [[corr-legit-neg-inventory]] item 046
Kind: D
Fidelity: exact -/
def CellPolicy (cellOf : S → Finset S) (π : S → A) : Prop := ∀ s t, t ∈ cellOf s → π t = π s

/-- A constant policy is a cell policy for every partition.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellPolicy_const (cellOf : S → Finset S) (a : A) : CellPolicy cellOf (fun _ => a) :=
  fun _ _ _ => rfl

/-- The T1 expected value of a policy under a per-terminal utility `U`:
`∑ s, π s · U s (π s)`. cdot is the case `U = 1_L · V`; the graded proposals are the cases with a
fixed per-terminal void grade.
Source: `clusters/D/NEGATIVES.md` D2(i) ("`u(t) = L(t) V_t(a_t)` fixed per terminal")
Kind: D
Fidelity: exact -/
def policyEU (P : Problem S A) (U : S → A → ℚ) (π : S → A) : ℚ := ∑ s, P.prior s * U s (π s)

/-- **T1 cdot value of a policy**: `∑ s, π s · [leg s (π s)] · V s (π s) (π s)` (the fixture's
`cdot` of the policy lottery, `d2_conditioning_dynamic.py:24-30`).
Source: [[corr-legit-neg-inventory]] item 046
Kind: D
Fidelity: exact -/
def policyValue (P : Problem S A) (V : MenuVec S A) (π : S → A) : ℚ :=
  ∑ s, P.prior s * ind (P.leg s (π s)) * V s (π s) (π s)

/-- **Legitimacy mass of a policy**: `∑ s, π s · [leg s (π s)]`.
Source: [[corr-legit-neg-inventory]] item 046
Kind: D
Fidelity: exact -/
def policyPL (P : Problem S A) (π : S → A) : ℚ := ∑ s, P.prior s * ind (P.leg s (π s))

/-- **T1 conditioning value of a policy**, exclusion convention: `policyValue / policyPL`, `none`
at zero legitimacy mass (the fixture's `cond` of the policy lottery).
Source: [[corr-legit-neg-inventory]] item 047
Kind: D
Fidelity: exact -/
def policyP2 (P : Problem S A) (V : MenuVec S A) (π : S → A) : Option ℚ :=
  if policyPL P π = 0 then none else some (policyValue P V π / policyPL P π)

/-- **The shifted (graded) T1 value**: cdot with every void world scored `lam`,
`∑ s, π s · ([leg] · V + [¬leg] · lam)`. Dinkelbach's form of updateless conditioning
(D2(iii)) is this value at `lam = λ*`.
Source: [[corr-legit-neg-inventory]] item 047 (D2(iii)); `d2_conditioning_dynamic.py:76-84`
Kind: D
Fidelity: exact -/
def policyShifted (P : Problem S A) (V : MenuVec S A) (lam : ℚ) (π : S → A) : ℚ :=
  ∑ s, P.prior s * (ind (P.leg s (π s)) * V s (π s) (π s) + ind (!P.leg s (π s)) * lam)

/-- The T2 expected value of an action at a cell `C` under `U`: `∑ t, cellprior C t · U t a`
(static's `cellprior`, zero outside `C`).
Source: none: infrastructure (the T2 problem is static's `P.restrict C`)
Kind: D
Fidelity: n/a -/
def cellEU (P : Problem S A) (U : S → A → ℚ) (C : Finset S) (a : A) : ℚ :=
  ∑ t, P.cellprior C t * U t a

/-- A policy is **cell-optimal** for `U` when it is a cell policy and prescribes, at every cell, a
T2-maximiser of the cell's expected `U`. (The cell-policy clause is not implied by the
maximiser clause when maximisers tie — finding 39 — so it is carried explicitly.)
Source: `clusters/D/NEGATIVES.md` D2(i) ("the T1-optimal policy prescribes a T2-optimal action at
every positive-probability cell")
Kind: D
Fidelity: exact -/
def CellOptimal (P : Problem S A) (U : S → A → ℚ) (cellOf : S → Finset S) (π : S → A) : Prop :=
  CellPolicy cellOf π ∧ ∀ s a, cellEU P U (cellOf s) a ≤ cellEU P U (cellOf s) (π s)

/-- `policyValue` is `policyEU` at the cdot utility `1_L · V`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyValue_eq_policyEU (P : Problem S A) (V : MenuVec S A) (π : S → A) :
    policyValue P V π = policyEU P (fun s a => ind (P.leg s a) * V s a a) π := by
  unfold policyValue policyEU
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- `policyShifted lam` is `policyEU` at the utility `1_L · V + 1_{¬L} · lam`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyShifted_eq_policyEU (P : Problem S A) (V : MenuVec S A) (lam : ℚ) (π : S → A) :
    policyShifted P V lam π =
      policyEU P (fun s a => ind (P.leg s a) * V s a a + ind (!P.leg s a) * lam) π := rfl

/-- **The T1 graded value of a policy** (static's `P3` with a per-terminal void grade `Wg`, weight
`lam`): `∑ s, π s · ([leg] · V + [¬leg] · lam · Wg s (π s) (π s))`.
Source: [[corr-legit-neg-inventory]] item 046 (D2(i), "P3/P4b with fixed per-terminal void grades")
Kind: D
Fidelity: exact -/
def policyP3 (P : Problem S A) (Wg : MenuVec S A) (lam : ℚ) (V : MenuVec S A) (π : S → A) : ℚ :=
  ∑ s, P.prior s * (ind (P.leg s (π s)) * V s (π s) (π s) + ind (!P.leg s (π s)) * lam * Wg s (π s) (π s))

/-- **The T1 numeric-lexical value of a policy** (static's `P4b`): `∑ s, π s · ([leg] · (κ + (1 − κ) V)
+ [¬leg] · κ' · Wg s (π s) (π s))`.
Source: [[corr-legit-neg-inventory]] item 046 (D2(i), "P3/P4b with fixed per-terminal void grades")
Kind: D
Fidelity: exact -/
def policyP4b (P : Problem S A) (Wg : MenuVec S A) (κ κ' : ℚ) (V : MenuVec S A) (π : S → A) : ℚ :=
  ∑ s, P.prior s * (ind (P.leg s (π s)) * (κ + (1 - κ) * V s (π s) (π s))
    + ind (!P.leg s (π s)) * κ' * Wg s (π s) (π s))

/-- `policyP3 Wg lam` is `policyEU` at the per-terminal utility `1_L · V + 1_{¬L} · lam · Wg`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyP3_eq_policyEU (P : Problem S A) (Wg : MenuVec S A) (lam : ℚ) (V : MenuVec S A)
    (π : S → A) :
    policyP3 P Wg lam V π =
      policyEU P (fun s a => ind (P.leg s a) * V s a a + ind (!P.leg s a) * lam * Wg s a a) π := rfl

/-- `policyP4b Wg κ κ'` is `policyEU` at the per-terminal utility
`1_L · (κ + (1 − κ) V) + 1_{¬L} · κ' · Wg`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyP4b_eq_policyEU (P : Problem S A) (Wg : MenuVec S A) (κ κ' : ℚ) (V : MenuVec S A)
    (π : S → A) :
    policyP4b P Wg κ κ' V π =
      policyEU P (fun s a => ind (P.leg s a) * (κ + (1 - κ) * V s a a)
        + ind (!P.leg s a) * κ' * Wg s a a) π := rfl

/-- The constant policy's `policyP3` is static's `P3`, and its `policyP4b` is static's `P4b`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyP3_const_policyP4b_const (P : Problem S A) (Wg : MenuVec S A) (lam κ κ' : ℚ)
    (V : MenuVec S A) (a : A) :
    policyP3 P Wg lam V (fun _ => a) = P.P3 Wg lam V a ∧
    policyP4b P Wg κ κ' V (fun _ => a) = P.P4b Wg κ κ' V a := ⟨rfl, rfl⟩

/-- The constant policy `fun _ => a` has the T1 value `EU π U a`; for cdot this is `P1 V a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyEU_const (P : Problem S A) (U : S → A → ℚ) (a : A) :
    policyEU P U (fun _ => a) = EU P.prior U a := rfl

/-- `policyValue` of a constant policy is `P1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyValue_const (P : Problem S A) (V : MenuVec S A) (a : A) :
    policyValue P V (fun _ => a) = P.P1 V a := rfl

/-- `policyPL` of a constant policy is `P(L | a)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyPL_const (P : Problem S A) (a : A) : policyPL P (fun _ => a) = P.PL a := rfl

/-- The T2 cdot value at cell `C` is `cellEU` at the cdot utility.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrict_P1_eq_cellEU (P : Problem S A) (V : MenuVec S A) (C : Finset S)
    (hC : 0 < ∑ t ∈ C, P.prior t) (a : A) :
    (P.restrict C hC).P1 V a = cellEU P (fun s a => ind (P.leg s a) * V s a a) C a := by
  unfold Problem.P1 cellEU
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [restrict_prior, restrict_leg]; ring

/-- The T2 graded value with a constant void grade `lam` (P3 with `W ≡ lam`, `λ = 1`) at cell `C`
is `cellEU` at the shifted utility.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrict_P3_const_eq_cellEU (P : Problem S A) (V : MenuVec S A) (lam : ℚ) (C : Finset S)
    (hC : 0 < ∑ t ∈ C, P.prior t) (a : A) :
    (P.restrict C hC).P3 (fun _ _ _ => lam) 1 V a =
      cellEU P (fun s a => ind (P.leg s a) * V s a a + ind (!P.leg s a) * lam) C a := by
  unfold Problem.P3 cellEU
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [restrict_prior, restrict_leg]; ring

/-- The T2 graded value with a per-terminal void grade `Wg` and weight `lam` (static's `P3`) at cell
`C` is `cellEU` at the utility `1_L · V + 1_{¬L} · lam · Wg`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrict_P3_eq_cellEU (P : Problem S A) (Wg : MenuVec S A) (lam : ℚ) (V : MenuVec S A)
    (C : Finset S) (hC : 0 < ∑ t ∈ C, P.prior t) (a : A) :
    (P.restrict C hC).P3 Wg lam V a =
      cellEU P (fun s a => ind (P.leg s a) * V s a a + ind (!P.leg s a) * lam * Wg s a a) C a := by
  unfold Problem.P3 cellEU
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [restrict_prior, restrict_leg]

/-- The T2 numeric-lexical value (static's `P4b`) at cell `C` is `cellEU` at the utility
`1_L · (κ + (1 − κ) V) + 1_{¬L} · κ' · Wg`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma restrict_P4b_eq_cellEU (P : Problem S A) (Wg : MenuVec S A) (κ κ' : ℚ) (V : MenuVec S A)
    (C : Finset S) (hC : 0 < ∑ t ∈ C, P.prior t) (a : A) :
    (P.restrict C hC).P4b Wg κ κ' V a =
      cellEU P (fun s a => ind (P.leg s a) * (κ + (1 - κ) * V s a a)
        + ind (!P.leg s a) * κ' * Wg s a a) C a := by
  unfold Problem.P4b cellEU
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [restrict_prior, restrict_leg]

/-- The cell mass times the cell expectation is the plain sum over the cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mass_mul_cellEU (P : Problem S A) (U : S → A → ℚ) (C : Finset S)
    (hC : 0 < ∑ t ∈ C, P.prior t) (a : A) :
    (∑ t ∈ C, P.prior t) * cellEU P U C a = ∑ t ∈ C, P.prior t * U t a := by
  unfold cellEU Problem.cellprior
  rw [Finset.mul_sum]
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun t => t ∈ C)]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_eq_zero (s := univ.filter fun t => t ∉ C), add_zero]
  · refine Finset.sum_congr rfl fun t ht => ?_
    rw [if_pos ht]; field_simp
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    rw [if_neg ht]; ring

/-- **The tower identity.** For a partition and a cell policy `π`, the T1 value is the
prior-weighted sum of the T2 values of the prescribed actions:
`policyEU P U π = ∑ s, π s · cellEU P U (cellOf s) (π s)`.
Source: `clusters/D/NEGATIVES.md` D2(i) proof ("`Σ_I P(I) · 𝔼[u | I, π(I)]`")
Kind: P
Fidelity: exact
Hyps: (a) the partition axioms and cell-measurability -/
theorem policyEU_tower {P : Problem S A} {cellOf : S → Finset S} (hP : IsPartition P cellOf)
    (U : S → A → ℚ) {π : S → A} (hπ : CellPolicy cellOf π) :
    policyEU P U π = ∑ s, P.prior s * cellEU P U (cellOf s) (π s) := by
  unfold policyEU cellEU Problem.cellprior
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun s => t ∈ cellOf s)]
  rw [Finset.sum_eq_zero (s := univ.filter fun s => t ∉ cellOf s), add_zero]
  · have hfilt : univ.filter (fun s => t ∈ cellOf s) = cellOf t := by
      ext s; simp only [mem_filter, mem_univ, true_and]; exact hP.mem_comm
    rw [hfilt]
    have hsum : ∑ s ∈ cellOf t, P.prior s * ((if t ∈ cellOf s then
        P.prior t / ∑ x ∈ cellOf s, P.prior x else 0) * U t (π s)) =
        ∑ s ∈ cellOf t, P.prior s * ((P.prior t / ∑ x ∈ cellOf t, P.prior x) * U t (π t)) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      have hts : t ∈ cellOf s := hP.mem_comm.2 hs
      rw [if_pos hts, hP.cell t s hs, hπ t s hs]
    rw [hsum, ← Finset.sum_mul]
    have hpos := hP.pos t
    field_simp
    try ring
  · intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs
    rw [if_neg hs]; ring

/-- **D2(i), dynamic consistency (T1 optimality of the cellwise-T2 policy).** For any per-terminal
utility `U` and any partition, a cell-optimal policy beats every cell policy at T1. So the
T1-optimal policy prescribes a T2-optimal action at every cell: no updatelessness is needed on
predictor-free problems for cdot, and for P3/P4b with fixed per-terminal void grades. `P1` is the
instance `policyValue_eq_policyEU`; `P3` with a per-terminal `Wg` and `P4b` are the instances
`cellOptimal_T1_optimal_P3` / `cellOptimal_T1_optimal_P4b` below (via `policyP3_eq_policyEU`,
`policyP4b_eq_policyEU`, with the T2 side `restrict_P3_eq_cellEU` / `restrict_P4b_eq_cellEU`).
The hypothesis package is always inhabited (`exists_cellOptimal`).
Source: [[corr-legit-neg-inventory]] item 046 (D2(i)); VERIFY D "D2 (i) survives"
Kind: P
Fidelity: exact (stronger: any partition, any per-terminal utility; the source's 7,500-instance grid
is a sanity check of this theorem)
Hyps: (a) partition axioms, cell-optimality of `π*`, cell-measurability of `π` -/
theorem cellOptimal_T1_optimal {P : Problem S A} {cellOf : S → Finset S}
    (hP : IsPartition P cellOf) (U : S → A → ℚ) {πstar : S → A}
    (hstar : CellOptimal P U cellOf πstar) {π : S → A} (hπ : CellPolicy cellOf π) :
    policyEU P U π ≤ policyEU P U πstar := by
  rw [policyEU_tower hP U hπ, policyEU_tower hP U hstar.1]
  exact Finset.sum_le_sum fun s _ =>
    mul_le_mul_of_nonneg_left (hstar.2 s (π s)) (P.prior_nonneg s)

/-- **D2(i) for P3 with a per-terminal void grade**: a policy that is cell-optimal for the graded
utility `1_L · V + 1_{¬L} · lam · Wg` beats every cell policy in the T1 graded value `policyP3`.
Source: [[corr-legit-neg-inventory]] item 046 (D2(i), P3 instance)
Kind: C
Fidelity: exact
Hyps: (a) as `cellOptimal_T1_optimal` -/
theorem cellOptimal_T1_optimal_P3 {P : Problem S A} {cellOf : S → Finset S}
    (hP : IsPartition P cellOf) (Wg : MenuVec S A) (lam : ℚ) (V : MenuVec S A) {πstar : S → A}
    (hstar : CellOptimal P (fun s a => ind (P.leg s a) * V s a a + ind (!P.leg s a) * lam * Wg s a a)
      cellOf πstar) {π : S → A} (hπ : CellPolicy cellOf π) :
    policyP3 P Wg lam V π ≤ policyP3 P Wg lam V πstar := by
  rw [policyP3_eq_policyEU, policyP3_eq_policyEU]
  exact cellOptimal_T1_optimal hP _ hstar hπ

/-- **D2(i) for P4b**: a policy that is cell-optimal for the numeric-lexical utility
`1_L · (κ + (1 − κ) V) + 1_{¬L} · κ' · Wg` beats every cell policy in `policyP4b`.
Source: [[corr-legit-neg-inventory]] item 046 (D2(i), P4b instance)
Kind: C
Fidelity: exact
Hyps: (a) as `cellOptimal_T1_optimal` -/
theorem cellOptimal_T1_optimal_P4b {P : Problem S A} {cellOf : S → Finset S}
    (hP : IsPartition P cellOf) (Wg : MenuVec S A) (κ κ' : ℚ) (V : MenuVec S A) {πstar : S → A}
    (hstar : CellOptimal P (fun s a => ind (P.leg s a) * (κ + (1 - κ) * V s a a)
      + ind (!P.leg s a) * κ' * Wg s a a) cellOf πstar) {π : S → A} (hπ : CellPolicy cellOf π) :
    policyP4b P Wg κ κ' V π ≤ policyP4b P Wg κ κ' V πstar := by
  rw [policyP4b_eq_policyEU, policyP4b_eq_policyEU]
  exact cellOptimal_T1_optimal hP _ hstar hπ

/-- **Good's theorem for cdot with fixed terminal scores**: every uninformed action is beaten by
the cellwise-T2 policy, `P1 V a ≤ policyValue P V π*`.
Source: [[corr-legit-neg-inventory]] item 046 (D2(i), "`𝔼_I max_a 𝔼[u | I, a] ≥ max_a 𝔼[u | a]`")
Kind: C
Fidelity: exact
Hyps: (a) partition axioms, cell-optimality of `π*` for the cdot utility -/
theorem P1_le_policyValue {P : Problem S A} {cellOf : S → Finset S} (hP : IsPartition P cellOf)
    (V : MenuVec S A) {πstar : S → A}
    (hstar : CellOptimal P (fun s a => ind (P.leg s a) * V s a a) cellOf πstar) (a : A) :
    P.P1 V a ≤ policyValue P V πstar := by
  rw [policyValue_eq_policyEU, ← policyValue_const P V a, policyValue_eq_policyEU]
  exact cellOptimal_T1_optimal hP _ hstar (cellPolicy_const cellOf a)

/-- **Value of information** of learning the partition, for cdot: the T1 cdot value of the
cellwise-T2 policy minus the best uninformed cdot value (NEGATIVES D "Conventions").
Source: [[corr-legit-neg-inventory]] item 046
Kind: D
Fidelity: exact -/
noncomputable def VOI [Nonempty A] (P : Problem S A) (V : MenuVec S A) (π : S → A) : ℚ :=
  policyValue P V π - univ.sup' univ_nonempty (P.P1 V)

/-- **D2(i), non-negative value of information for cdot**: `0 ≤ VOI` at every cell-optimal policy,
for every partition.
Source: [[corr-legit-neg-inventory]] item 046 (D2(i))
Kind: C
Fidelity: exact
Hyps: (a) partition axioms, cell-optimality -/
theorem VOI_nonneg [Nonempty A] {P : Problem S A} {cellOf : S → Finset S}
    (hP : IsPartition P cellOf) (V : MenuVec S A) {πstar : S → A}
    (hstar : CellOptimal P (fun s a => ind (P.leg s a) * V s a a) cellOf πstar) :
    0 ≤ VOI P V πstar := by
  unfold VOI
  have : univ.sup' univ_nonempty (P.P1 V) ≤ policyValue P V πstar :=
    Finset.sup'_le _ _ fun a _ => P1_le_policyValue hP V hstar a
  linarith

/-- **Cell-optimal policies exist** for every partition and every per-terminal utility over a
finite non-empty menu: at every cell pick a maximiser of the cell's expected `U`. So the hypothesis
package of `cellOptimal_T1_optimal`, `P1_le_policyValue` and `VOI_nonneg` is never empty.
Source: none: infrastructure (audit r1, adversarial 3.4)
Kind: L
Fidelity: n/a -/
theorem exists_cellOptimal [Nonempty A] {P : Problem S A} {cellOf : S → Finset S}
    (hP : IsPartition P cellOf) (U : S → A → ℚ) :
    ∃ π : S → A, CellOptimal P U cellOf π := by
  classical
  let pick : Finset S → A := fun C =>
    Classical.choose (Finset.exists_max_image univ (cellEU P U C) univ_nonempty)
  have hpick : ∀ C a, cellEU P U C a ≤ cellEU P U C (pick C) := fun C a =>
    (Classical.choose_spec (Finset.exists_max_image univ (cellEU P U C) univ_nonempty)).2 a
      (mem_univ a)
  refine ⟨fun s => pick (cellOf s), fun s t ht => ?_, fun s a => hpick _ a⟩
  show pick (cellOf t) = pick (cellOf s)
  rw [hP.cell s t ht]

/-! ### The converse: a T1-optimal cell policy is cell-optimal -/

/-- The policy that overrides `π` by `a` on the cell of `s₀` is again a cell policy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellPolicy_override {P : Problem S A} {cellOf : S → Finset S} (hP : IsPartition P cellOf)
    {π : S → A} (hπ : CellPolicy cellOf π) (s₀ : S) (a : A) :
    CellPolicy cellOf (fun t => if t ∈ cellOf s₀ then a else π t) := by
  intro s t hts
  by_cases hs : s ∈ cellOf s₀
  · have ht : t ∈ cellOf s₀ := by rw [← hP.cell s₀ s hs]; exact hts
    simp [hs, ht]
  · have ht : t ∉ cellOf s₀ := fun ht => hs (by
      rw [← hP.cell s₀ t ht]; exact hP.mem_comm.1 hts)
    simp [hs, ht, hπ s t hts]

/-- **Converse of D2(i)**: a cell policy that is T1-optimal among cell policies prescribes, at
every cell, a T2-maximiser (positive cell mass is what makes the converse true). With
`cellOptimal_T1_optimal` this says the T1-optimal cell policies are exactly the cell-optimal ones.
Source: [[corr-legit-neg-inventory]] item 046 (D2(i), "maximized cell by cell")
Kind: P
Fidelity: exact
Hyps: (a) partition axioms, T1 optimality among cell policies -/
theorem cellOptimal_of_T1_optimal {P : Problem S A} {cellOf : S → Finset S}
    (hP : IsPartition P cellOf) (U : S → A → ℚ) {πstar : S → A} (hstar : CellPolicy cellOf πstar)
    (hopt : ∀ π, CellPolicy cellOf π → policyEU P U π ≤ policyEU P U πstar) :
    CellOptimal P U cellOf πstar := by
  refine ⟨hstar, fun s₀ a => ?_⟩
  set π' : S → A := fun t => if t ∈ cellOf s₀ then a else πstar t with hπ'
  have hle := hopt π' (cellPolicy_override hP hstar s₀ a)
  -- the difference of the two T1 values is the cell of `s₀` times the difference of cell values
  have hdiff : policyEU P U π' - policyEU P U πstar =
      (∑ t ∈ cellOf s₀, P.prior t) * (cellEU P U (cellOf s₀) a - cellEU P U (cellOf s₀) (πstar s₀)) := by
    rw [mul_sub, mass_mul_cellEU P U _ (hP.pos s₀), mass_mul_cellEU P U _ (hP.pos s₀)]
    unfold policyEU
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun t => t ∈ cellOf s₀)]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [Finset.sum_eq_zero (s := univ.filter fun t => t ∉ cellOf s₀), add_zero]
    · refine Finset.sum_congr rfl fun t ht => ?_
      have : πstar t = πstar s₀ := hstar s₀ t ht
      simp only [hπ', if_pos ht, this]
      try ring
    · intro t ht
      simp only [mem_filter, mem_univ, true_and] at ht
      simp only [hπ', if_neg ht]
      try ring
  have hmass := hP.pos s₀
  have : (∑ t ∈ cellOf s₀, P.prior t) * (cellEU P U (cellOf s₀) a - cellEU P U (cellOf s₀) (πstar s₀)) ≤ 0 := by
    rw [← hdiff]; linarith
  by_contra hlt
  rw [not_le] at hlt
  have : 0 < (∑ t ∈ cellOf s₀, P.prior t) * (cellEU P U (cellOf s₀) a - cellEU P U (cellOf s₀) (πstar s₀)) :=
    mul_pos hmass (by linarith)
  linarith

/-! ### D1(ii): what the T2 verdict reads -/

/-- **The T2 cdot verdict at a cell reads `V` only on the cell's legitimate terminals of the
option**: two menu vectors that agree at `(s, a, a)` for every `s ∈ C` with `leg s a = true` give
the same `P1` at `P.restrict C`. In particular the T2 verdict is independent of any entry at a
terminal outside the cell (D1(i)'s "the penalty lives on an unreachable terminal") and of any entry
at a void terminal inside it (the floor). Named for what it is: a congruence, not "`p` never
enters"; the toy instance `toyD_partial_p_enters` (`T2Floor.lean`) shows `p` *does* enter as soon
as the cell leaves legitimacy open.
Source: [[corr-legit-neg-inventory]] item 045 (D1(i), (ii)); [[corr-legit-neg-2-inventory]] item 2-018
Kind: L
Fidelity: exact -/
lemma restrict_P1_congr (P : Problem S A) {V V' : MenuVec S A} (C : Finset S)
    (hC : 0 < ∑ t ∈ C, P.prior t) (a : A)
    (h : ∀ s ∈ C, P.leg s a = true → V s a a = V' s a a) :
    (P.restrict C hC).P1 V a = (P.restrict C hC).P1 V' a := by
  unfold Problem.P1
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [restrict_prior, restrict_leg, Problem.cellprior]
  by_cases hs : s ∈ C
  · by_cases hl : P.leg s a = true
    · rw [h s hs hl]
    · simp [Bool.not_eq_true] at hl; simp [hl]
  · simp [hs]

end Defs

/-! ### Cell policies as a menu: the policy problem -/

section PolicyProblem

variable [DecidableEq S] [DecidableEq A]

/-- The cell policies of a partition, as a type (a finite menu).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev CellPol (cellOf : S → Finset S) := {π : S → A // CellPolicy cellOf π}

/-- `CellPolicy` is decidable on finite types.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance (cellOf : S → Finset S) : DecidablePred (CellPolicy (A := A) cellOf) := fun _ =>
  inferInstanceAs (Decidable (∀ s t, t ∈ cellOf s → _ = _))

/-- The cell policies form a finite type.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance (cellOf : S → Finset S) : Fintype (CellPol (A := A) cellOf) := Subtype.fintype _

/-- **The policy problem**: the same prior, with the cell policies as the menu, `leg s π :=
leg s (π s)` and `u s π := u s (π s)`. Its `P1`/`PL`/`P2`/`P3` at the transported vector
`policyVec V` are exactly `policyValue`/`policyPL`/`policyP2`/`policyShifted` (the four `rfl`
lemmas below), so every single-problem theorem over `Problem` — Dinkelbach's in particular — is a
T1 theorem over policies for free.
Source: none: infrastructure (reduction device)
Kind: D
Fidelity: n/a -/
def policyProblem (P : Problem S A) (cellOf : S → Finset S) : Problem S (CellPol (A := A) cellOf) where
  prior := P.prior
  prior_nonneg := P.prior_nonneg
  prior_sum := P.prior_sum
  leg := fun s π => P.leg s (π.1 s)
  u := fun s π => P.u s (π.1 s)

/-- The menu vector transported to policies: `V s π c := V s (π s) (c s)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def policyVec (cellOf : S → Finset S) (V : MenuVec S A) : MenuVec S (CellPol (A := A) cellOf) :=
  fun s π c => V s (π.1 s) (c.1 s)

/-- `policyProblem_P1`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyProblem_P1 (P : Problem S A) (cellOf : S → Finset S) (V : MenuVec S A)
    (π : CellPol (A := A) cellOf) :
    (policyProblem P cellOf).P1 (policyVec cellOf V) π = policyValue P V π.1 := rfl

/-- `policyProblem_PL`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyProblem_PL (P : Problem S A) (cellOf : S → Finset S) (π : CellPol (A := A) cellOf) :
    (policyProblem P cellOf).PL π = policyPL P π.1 := rfl

/-- `policyProblem_P2`: supporting lemma (no headline). Exclusion convention on both sides.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyProblem_P2 (P : Problem S A) (cellOf : S → Finset S) (V : MenuVec S A)
    (π : CellPol (A := A) cellOf) :
    (policyProblem P cellOf).P2 (policyVec cellOf V) π = policyP2 P V π.1 := rfl

/-- `policyProblem_P3_const`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyProblem_P3_const (P : Problem S A) (cellOf : S → Finset S) (V : MenuVec S A)
    (lam : ℚ) (π : CellPol (A := A) cellOf) :
    (policyProblem P cellOf).P3 (fun _ _ _ => lam) 1 (policyVec cellOf V) π =
      policyShifted P V lam π.1 := by
  unfold Problem.P3 policyShifted policyProblem policyVec
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

end PolicyProblem

end Cleanroom.Corrigibility.LegitNegDynamic
