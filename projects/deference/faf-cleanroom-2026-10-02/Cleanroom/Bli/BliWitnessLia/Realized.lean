import Cleanroom.Bli.BliWitnessLia.Prior

/-!
# `bli-witness-lia` · Realized: what the witness is not — the inductor's realized next table is
uncharged (T4)

[[bli-program]] §3.9's U15 sentence reads: "the tables are the spliced inductor's possible
day-`m` tables, `μ` is `trajLaw`". Under `bli-exact-base`'s kernel this holds in **cell form** and
fails in **table form** (their findings F19/F22): the SIST prior `segmentSist` charges exactly
the two slice marginals `sliceT n` (the coin at `1`) and `sliceF n` (the coin at `0`), while the
inductor's *realized* day-`(n+1)` table `linkedTable (n+1) = actualTable … (n+1)` prices the coin
at `1/2` (`Uncharged.linkedTable_succ_fresh`) and so is neither — its prior mass is `0`
(`stateMass_realized_zero`) and it is in neither class (`realized_not_ask`, `realized_not_rec`).
The mugging's "observed table" `sliceT n` is therefore a charged candidate of the kernel, **not**
the inductor's realized next table. What *is* charged about the realized trajectory is its
**rounded cell pattern**: `Segment.linked_actual_state_charged_q` — every completed-theory world
holds the state sentence of `q₁ = (1, 0, 1)` (the realized `halfRound` cells at the three segment
coordinates) and the day-`n` superbelief gives it mass `1/2`. So "tables are the inductor's
possible day-`(n+1)` tables" is true of the *cell patterns* and false of the *full tables* under
this kernel. Filed as finding F1 of this package ([[bli-witness-lia-findings]]): severity
imprecision; blocking for the table-form reading of U15.

The witness is planted on `2 ≤ n` (as every headline of `Prior.lean`); T4 additionally needs
`n + 1 < H` (the realized day-`(n+1)` table is the kernel's only on segment days; at the boundary
`n + 1 = H` the day-`H` market is the LIA, `Segment.linked_boundary_q`). The mandate's `1 ≤ n`
form of the exclusion is `Uncharged.linkedTable_succ_ne_sliceT`/`_ne_sliceF`; the prior itself is
planted on `2 ≤ n`, so T4 is stated there.

Sources: mandate T4; [[bli-exact-base-findings]] F19, F22; [[bli-exact-base-handoff]] ("under
that law the realized trajectory has prior probability `0` from day `1` on at horizons `H ≥ 3` —
read it as the SIST prior's state mass at horizon one").
-/

namespace Cleanroom.Bli.BliWitnessLia

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite Cleanroom.Bli.BliTrajectory
open Cleanroom.Bli.BliExactBase Cleanroom.Bli.BliExactBase.Skel Cleanroom.Bli.BliLinkageB
open Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist

noncomputable section

/-- The inductor's realized day-`(n+1)` table is a grid table of `segmentMesh K` on day
`n + 0 + 1` (the linked table is dyadic, `Bli.linkedPrice_mem_gridVals`, and `k₀ (n+1) + 1 ≤ K`
on the segment).
Source: mandate T4 ("membership from `Uncharged`'s `hgrid` argument")
Kind: L
Fidelity: n/a -/
lemma realizedTable_mem_grid {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ}
    (hn1 : n + 1 < H) :
    linkedTable (n + 1) ∈ grid smallIndex (Bli.segmentMesh K).d (n + 0 + 1) := by
  rw [mem_grid_iff]
  intro φ
  show Segment.linkedPrice (n + 1) φ.1 ∈ gridVals ((Bli.segmentMesh K).d (n + 0 + 1))
  exact gridVals_mono (pow_dvd_pow 2 (by have := hK (n + 1) hn1; omega)) (Nat.two_pow_pos _)
    (Bli.linkedPrice_mem_gridVals (n + 1) φ.1)

/-- **The realized next table** of the inductor, as a grid table of the prior's day: the linked
splice's day-`(n+1)` small prices, `linkedTable (n+1) = actualTable smallIndex (spliceRat H linkedPrice) (n+1)`.
Source: mandate T4 (`⟨linkedTable (n+1), _⟩`)
Kind: D
Fidelity: exact -/
def realizedTable {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn1 : n + 1 < H) :
    ↥(grid smallIndex (Bli.segmentMesh K).d (n + 0 + 1)) :=
  ⟨linkedTable (n + 1), realizedTable_mem_grid hK hn1⟩

section Realized

variable {H K : ℕ} (hK : ∀ n < H, Segment.k₀ n + 1 ≤ K) {n : ℕ} (hn1 : n + 1 < H)

/-- The realized table's underlying table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma realizedTable_val : (realizedTable hK hn1).1 = linkedTable (n + 1) := rfl

/-- The realized next table is the inductor's realized day-`(n+1)` table
(`Skel.actualTable_eq_linkedTable` at `n + 1`).
Source: mandate T4 (`linkedTable (n+1) = actualTable … (n+1)`)
Kind: L
Fidelity: exact -/
theorem realized_eq_actual (hn1 : n + 1 < H) :
    linkedTable (n + 1) =
      BliFinite.actualTable smallIndex (spliceRat H Segment.linkedPrice) (n + 1) :=
  (actualTable_eq_linkedTable hn1).symm

/-- **The realized next table prices the coin at `1/2`** — neither `1` (the Ask table) nor `0`
(the Rec table).
Source: mandate T4 (`linkedTable_succ_fresh`); findings F19
Kind: L
Fidelity: exact -/
theorem realized_fresh (h1 : 1 ≤ n) : (realizedTable hK hn1).1 (coinAt n h1) = 1 / 2 :=
  Uncharged.linkedTable_succ_fresh n _

/-- **The realized next table has prior mass `0` under `segmentSist`**: the two-point law charges
only the two slice marginals, and the realized table is neither
(`Uncharged.linkedTable_succ_ne_sliceT`/`_ne_sliceF`: `1/2 ≠ 1`, `1/2 ≠ 0` at the coin). The
mugging's observed table `sliceT n` is the kernel's true-slice marginal, not the inductor's
realized day-`(n+1)` table; the realized *rounded cell pattern* is what the kernel charges
(`realized_pattern_charged`). Finding F1 of this package against [[bli-program]] §3.9's U15
sentence (table-form reading).
Source: mandate T4 (`stateMass_realized_zero`); [[bli-exact-base-findings]] F19, F22
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem stateMass_realized_zero (h2 : 2 ≤ n) (c V : ℚ) (r₀ : Bool → ℚ) :
    (segmentSist H K hK n (by omega) h2 c V r₀).stateMass (realizedTable hK hn1) = 0 :=
  stateMass_other_zero hK (by omega) h2 c V r₀ _
    (fun h => Uncharged.linkedTable_succ_ne_sliceT (n := n) (by omega) (congrArg Subtype.val h))
    (fun h => Uncharged.linkedTable_succ_ne_sliceF (n := n) (by omega) (congrArg Subtype.val h))

/-- **The realized next table is in no class**: not Ask (its coin is `1/2 ≠ 1`).
Source: mandate T4 (`realized_not_ask`)
Kind: L
Fidelity: exact -/
theorem realized_not_ask (h1 : 1 ≤ n) : ¬ askC n 0 (coinAt n h1) (realizedTable hK hn1) := by
  intro h
  have h' : (realizedTable hK hn1).1 (coinAt n h1) = 1 := h
  rw [realized_fresh] at h'
  norm_num at h'

/-- **The realized next table is in no class**: not Rec (its coin is `1/2 ≠ 0`).
Source: mandate T4 (`realized_not_ask`, the Rec side)
Kind: L
Fidelity: exact -/
theorem realized_not_rec (h1 : 1 ≤ n) : ¬ recC n 0 (coinAt n h1) (realizedTable hK hn1) := by
  intro h
  have h' : (realizedTable hK hn1).1 (coinAt n h1) = 0 := h
  rw [realized_fresh] at h'
  norm_num at h'

/-- **What *is* charged about the realized trajectory — the cell form** (restated from
`bli-exact-base`'s `Segment.linked_actual_state_charged_q`, for every cell quote code `q`): every
completed-theory world of `paperDP 𝗜𝚺₁` holds the state sentence of `q₁ = (1, 0, 1)`, the
realized `halfRound` cell pattern of the three segment coordinates on day `n+1`, and the day-`n`
superbelief `linkedP H n` gives it mass `1/2`.
Source: mandate T4 ("the cell-form chain `linked_actual_state_charged_q` is the statement that
charges the realized *pattern*"); [[bli-exact-base-findings]] F19
Kind: C (restatement of `Segment.linked_actual_state_charged_q`)
Fidelity: exact
Hyps: (a) -/
theorem realized_pattern_charged (h1 : 1 ≤ n) (hn1 : n + 1 < H)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H Segment.linkedPrice halfRound)) :
    (∀ v : PCWorld, v.ConsistentWithTheory (paperDP 𝗜𝚺₁) →
      v.Holds (stateOf (Segment.linkedCFq H q) (n + 1) Kernel.q₁)) ∧
    Segment.linkedP H n (stateOf (Segment.linkedCFq H q) (n + 1) Kernel.q₁) = 1 / 2 :=
  Segment.linked_actual_state_charged_q q h1 hn1

/-- **T4, bundled — what the witness is not**: under `segmentSist` the inductor's realized
day-`(n+1)` table has mass `0` and prices the coin at `1/2`, while the mugging's observed table
(the Ask table) prices it at `1`; and the realized *rounded pattern* `q₁` is charged `1/2` by the
day-`n` superbelief (cell form). So U15's "the tables are the spliced inductor's possible
day-`(n+1)` tables" holds in cell form and fails in table form under this kernel.
Source: mandate T4; [[bli-program]] §3.9 (U15); [[bli-exact-base-findings]] F19, F22
Kind: P (composition of `stateMass_realized_zero`, `realized_fresh`, `askC_askTable` and
`realized_pattern_charged`)
Fidelity: exact
Hyps: (a) -/
theorem witness_is_not_realized (h2 : 2 ≤ n) (c V : ℚ) (r₀ : Bool → ℚ)
    (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H Segment.linkedPrice halfRound)) :
    (segmentSist H K hK n (by omega) h2 c V r₀).stateMass (realizedTable hK hn1) = 0 ∧
    (realizedTable hK hn1).1 (coinAt n (by omega)) = 1 / 2 ∧
    (askTable K hK (by omega : n < H)).1 (coinAt n (by omega)) = 1 ∧
    Segment.linkedP H n (stateOf (Segment.linkedCFq H q) (n + 1) Kernel.q₁) = 1 / 2 :=
  ⟨stateMass_realized_zero hK hn1 h2 c V r₀, realized_fresh hK hn1 (by omega),
    askC_askTable hK (by omega) h2, (realized_pattern_charged (by omega) hn1 q).2⟩

end Realized

end

end Cleanroom.Bli.BliWitnessLia
