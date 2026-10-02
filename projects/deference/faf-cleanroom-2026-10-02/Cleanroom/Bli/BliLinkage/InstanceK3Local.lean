import Cleanroom.Bli.BliLinkage.LiaPackage
import Cleanroom.Bli.BliLinkage.InstanceK3Grid

/-!
# `bli-linkage` — K3 at FAF's LIA after the refutation: the vacuity made explicit, and the
local instances with content (repair round 3, audit r3 adversarial B1)

`LiaPackage.not_lia_small_coherent_mixture_exists` shows the package of every K3 instance at
FAF's LIA — `PCPσ atoms (paperDP 𝗜𝚺₁) P ∧ … ∧ E1x (liaHistory (paperDP 𝗜𝚺₁)) P ∧ …` — is empty.
This module does two things with that.

1. **Vacuity, stated.** `no_degenerate_linked_bli_LIA_vacuous`,
   `no_degenerate_linked_bli_LIA_family_vacuous` and `no_degenerate_linked_bli_LIA_oneCoord_vacuous`
   are the three instances' conclusions with *every* non-structural hypothesis dropped —
   no `hχ`, no `hmove`, no grid conditions. They are one line each from
   `LiaPackage.k3_package_at_lia_empty`, and they are the honest record of what the
   mandate's K3 shape proves at the LIA: nothing about moves.
2. **The local instances.** `Degenerate.no_degenerate_linked_bli_lit` uses `E1x` only at the
   pinned cell literals (`E1xLit`). Its LIA instances — `no_degenerate_linked_bli_LIA_family_lit`
   over any grid, `no_degenerate_linked_bli_LIA_oneCoord_lit` over the one-coordinate grid with
   every grid hypothesis discharged — have `hχ` and `hmove` as their hypotheses, exactly as the
   round-2 instances did, and a package that the counting argument does not touch: what it
   demands of the LIA (`lit_package_forces_today_listed`) is that on every day from some day
   on the literal `lit_{n+1, χ n, todayIdx n}` is a listed key of `liaStates (paperDP 𝗜𝚺₁) n`
   with exact quote `1`, and its sibling literals quote `0` — one sentence a day listed, not
   `2^(2^n − 2)`. Whether FAF's LIA ever does this is not settled here (unknown in both
   directions, not evidence of falsity); nothing in the package is counted out.

The round-2 instances (`InstanceB2`, `InstanceK3`, `InstanceK3Grid`) are kept as the mandate's
K3 shape, labelled vacuous in their docstrings and ledger rows.
-/

namespace Cleanroom.Bli.BliLinkage

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound
open Cleanroom.Bli.BliLinkageB (fixedCF fixedSystemR σB2 twoCells_eq_range halfRound_lt_two)

/-! ## 1. The round-2 instances are vacuous -/

/-- **`InstanceB2.no_degenerate_linked_bli_LIA`'s conclusion with every hypothesis dropped**:
the package is empty at FAF's LIA (no `hmove`, no `hpin`, no grid condition).
Source: this run (repair r3, audit r3 adversarial B1 fix (iii)); `LiaPackage.not_lia_small_coherent_mixture_exists`
Kind: L
Fidelity: n/a (the vacuity of the round-2 instance, stated)
Hyps: (a) -/
theorem no_degenerate_linked_bli_LIA_vacuous (rep : ℕ → ℕ → ℚ) (S : StateSystem)
    {atoms : ℕ → Finset ℕ} {P : History} (deg : ℕ → ℕ) :
    ¬ (PCPσ atoms (paperDP 𝗜𝚺₁) P ∧ E5σ (stateOf (fixedCF rep)) S P ∧
      E1x (liaHistory (paperDP 𝗜𝚺₁)) P ∧ Degenerate (stateOf (fixedCF rep)) P deg) :=
  k3_package_at_lia_empty _ _ _

/-- **`InstanceK3.no_degenerate_linked_bli_LIA_family`'s conclusion with every hypothesis
dropped** (no `hχ`, no `hmove`).
Source: this run (repair r3, audit r3 adversarial B1 fix (iii))
Kind: L
Fidelity: n/a (the vacuity of the round-2 instance, stated)
Hyps: (a) -/
theorem no_degenerate_linked_bli_LIA_family_vacuous (rep : ℕ → ℕ → ℚ) (S : StateSystem)
    {atoms : ℕ → Finset ℕ} {P : History} (deg : ℕ → ℕ) :
    ¬ (PCPσ atoms (paperDP 𝗜𝚺₁) P ∧ E5σ (stateOf (fixedCF rep)) S P ∧
      E1x (liaHistory (paperDP 𝗜𝚺₁)) P ∧ Degenerate (stateOf (fixedCF rep)) P deg) :=
  k3_package_at_lia_empty _ _ _

/-- **`InstanceK3Grid.no_degenerate_linked_bli_LIA_oneCoord`'s conclusion with `hχ` and
`hmove` dropped**: the one-coordinate package at FAF's LIA is empty for every family.
Source: this run (repair r3, audit r3 adversarial B1 fix (iii))
Kind: L
Fidelity: n/a (the vacuity of the round-2 instance, stated)
Hyps: (a) -/
theorem no_degenerate_linked_bli_LIA_oneCoord_vacuous (rep : ℕ → ℕ → ℚ) {P : History}
    (χ : ℕ → ℕ) :
    ¬ (PCPσ (stateAtoms (stateOf (fixedCF rep)) (oneSystem χ rep)) (paperDP 𝗜𝚺₁) P ∧
      E5σ (stateOf (fixedCF rep)) (oneSystem χ rep) P ∧
      E1x (liaHistory (paperDP 𝗜𝚺₁)) P ∧ Degenerate (stateOf (fixedCF rep)) P (degOne χ)) :=
  k3_package_at_lia_empty _ _ _

/-! ## 2. The local instances: `E1xLit` in place of `E1x` -/

/-- **K3 at FAF's LIA, family form, local agreement** — `InstanceK3.no_degenerate_linked_bli_LIA_family`
with `E1x (liaHistory (paperDP 𝗜𝚺₁)) P` replaced by `E1xLit (fixedCF rep) index (liaHistory (paperDP 𝗜𝚺₁)) P`
(agreement on the pinned coordinates' cell literals only). Same hypotheses `hχ`, `hmove` and
grid data; the package is not the one the counting argument empties.
Source: this run (repair r3, audit r3 adversarial B1 fix (v)); [[bli-program]] §3.6(iii); mandate K3 ("with `χ n` listed and pinned eventually")
Kind: C
Fidelity: stronger than the round-2 instance (`E1xLit` for `E1x`); `hmove` and `hχ` the hypotheses not derived; the degenerate table's shape and the grid conditions are instance data
Hyps: (a); `hmove` is the honest conditional of mandate § K3; `hχ` the family's certificate; precondition on content: the local package's satisfiability at the LIA (unknown in both directions; `lit_package_forces_today_listed` is what it needs) -/
theorem no_degenerate_linked_bli_LIA_family_lit (rep : ℕ → ℕ → ℚ) (index : ℕ → List ℕ)
    (S : StateSystem) {atoms : ℕ → Finset ℕ} {P : History} (χ : ℕ → ℕ)
    (hχ : MachineDigits fun n => Encodable.encode (sentenceOfCode (χ n))) (deg : ℕ → ℕ) (N : ℕ)
    (hpin : ∀ n ≥ N, χ n ∈ pinned (fixedCF rep) index n)
    (hdegS : ∀ n, deg n ∈ S.states (n + 1))
    (hentry : ∀ n, entryOf (χ n) (tableOfCode (deg n)) =
      some (halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode (χ n)))))))
    (hsp : ∀ n, SpuriousEntails (stateOf (fixedCF rep)) (fixedCF rep).literal S index
      (fixedCF rep).cells n)
    (hatoms : ∀ n, stateAtoms (stateOf (fixedCF rep)) S n ⊆ atoms n)
    (hmove : Set.Infinite {n |
      halfRound (n + 1) (marketValue 𝗜𝚺₁ (Nat.pair (n + 1) (Encodable.encode (sentenceOfCode (χ n))))) ≠
        halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode (χ n)))))}) :
    ¬ (PCPσ atoms (paperDP 𝗜𝚺₁) P ∧ E5σ (stateOf (fixedCF rep)) S P ∧
      E1xLit (fixedCF rep) index (liaHistory (paperDP 𝗜𝚺₁)) P ∧
      Degenerate (stateOf (fixedCF rep)) P deg) := by
  haveI : IsLogicalInductor (liaHistory (paperDP 𝗜𝚺₁)) (paperDP 𝗜𝚺₁) := paperLIA 𝗜𝚺₁
  have hψ : MachineSentenceCodes fun z =>
      (fixedCF rep).literal (z.unpair.1 + 1) (sentenceOfCode (χ z.unpair.1)) z.unpair.2 :=
    cellSentence_family_machineSentenceCodes
      (fun n => Encodable.encode (sentenceOfCode (χ n))) hχ
  refine no_degenerate_linked_bli_lit (fixedCF rep) deg χ
    (fun n => halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode (χ n))))))
    2 N (fun n => twoCells_eq_range (n + 1)) hpin hdegS (fun n => halfRound_lt_two _ _) hentry hsp
    hatoms hψ (paperDP_hworld 𝗜𝚺₁) ?_ hmove
  intro n hn
  obtain ⟨k, hk⟩ := cellSentence_neg_enters 𝗜𝚺₁ halfRound halfRound_computable hn
  exact ⟨k, fun v hv => (PCWorld.holds_neg v _).1 (hv _ hk)⟩

/-- **K3 at FAF's LIA, one-coordinate grid, local agreement** —
`InstanceK3Grid.no_degenerate_linked_bli_LIA_oneCoord` with `E1xLit` in place of `E1x`: every
grid hypothesis discharged, `hχ` and `hmove` the only hypotheses, and a package the counting
argument does not empty.
Source: this run (repair r3, audit r3 adversarial B1 fix (v)); [[bli-program]] §3.6(iii); mandate K3
Kind: C
Fidelity: stronger than the round-2 instance (`E1xLit` for `E1x`; `hχ` and `hmove` the only hypotheses)
Hyps: (a); `hmove` is the honest conditional of mandate § K3; `hχ` the family's certificate; precondition on content: the local package's satisfiability at the LIA (unknown in both directions) -/
theorem no_degenerate_linked_bli_LIA_oneCoord_lit (rep : ℕ → ℕ → ℚ) {P : History} (χ : ℕ → ℕ)
    (hχ : MachineDigits fun n => Encodable.encode (sentenceOfCode (χ n)))
    (hmove : Set.Infinite {n |
      halfRound (n + 1) (marketValue 𝗜𝚺₁ (Nat.pair (n + 1) (Encodable.encode (sentenceOfCode (χ n))))) ≠
        halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode (χ n)))))}) :
    ¬ (PCPσ (stateAtoms (stateOf (fixedCF rep)) (oneSystem χ rep)) (paperDP 𝗜𝚺₁) P ∧
      E5σ (stateOf (fixedCF rep)) (oneSystem χ rep) P ∧
      E1xLit (fixedCF rep) (oneIndex χ) (liaHistory (paperDP 𝗜𝚺₁)) P ∧
      Degenerate (stateOf (fixedCF rep)) P (degOne χ)) := by
  obtain ⟨N, hN⟩ := oneIndex_pinned_eventually rep χ hχ
  exact no_degenerate_linked_bli_LIA_family_lit rep (oneIndex χ) (oneSystem χ rep) χ hχ (degOne χ)
    N hN (degOne_mem χ rep) (degOne_entry χ) (oneStates_spuriousEntails rep χ)
    (fun _ => Finset.Subset.refl _) hmove

/-! ## 3. What the local package demands of the LIA -/

/-- **The local package's demand on the LIA is one listed sentence a day**: under
`PCPσ ∧ E5σ ∧ E1xLit (liaHistory DP) P ∧ Degenerate` on a grid with `SpuriousEntails`, for a
pinned coordinate `c` listed by the degenerate table at the cell `t`, the LIA's day-`n` belief
state lists `lit_{n+1, c, t}` with exact quote `1` (every other cell's literal quotes `0`,
listed or not). Compare `LiaPackage.lia_package_forces_support_card` for the full `E1x`: there
the demand is `2^(2^n − 2)` listed keys a day.
Source: this run (repair r3); FAF `RationalBeliefState.quote_eq_zero_of_not_mem`, `liaHistory_eq_quote_cast`
Kind: L
Fidelity: n/a -/
theorem lit_package_forces_today_listed {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) {S : StateSystem}
    {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess} {P : History} {index : ℕ → List ℕ}
    (hcoh : PCPσ atoms DP P) (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n)
    (hE5 : E5σ (stateOf C) S P) (hE1 : E1xLit C index (liaHistory DP) P) {deg : ℕ → ℕ}
    (hdegS : ∀ n, deg n ∈ S.states (n + 1)) (hdeg : Degenerate (stateOf C) P deg) (n : ℕ)
    (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n) {c : ℕ}
    (hc : c ∈ pinned C index n) {t : ℕ} (hentry : entryOf c (tableOfCode (deg n)) = some t)
    (ht : t ∈ C.cells (n + 1)) :
    (liaStates DP n).quote (C.literal (n + 1) (sentenceOfCode c) t) = 1 ∧
      C.literal (n + 1) (sentenceOfCode c) t ∈ (liaStates DP n).support := by
  have h1 := degenerate_literal_indicator_lit C hcoh hatoms hE5 hE1 hdegS hdeg n hsp hc hentry ht
  rw [if_pos rfl, liaHistory_eq_quote_cast] at h1
  change (((liaStates DP n).quote (C.literal (n + 1) (sentenceOfCode c) t) : ℚ) : ℝ) = 1 at h1
  have hq : (liaStates DP n).quote (C.literal (n + 1) (sentenceOfCode c) t) = 1 := by
    exact_mod_cast h1
  refine ⟨hq, ?_⟩
  by_contra h
  rw [RationalBeliefState.quote_eq_zero_of_not_mem _ h] at hq
  norm_num at hq

end Cleanroom.Bli.BliLinkage
