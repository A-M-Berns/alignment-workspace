import Cleanroom.Bli.BliLinkageB.Degenerate
import Cleanroom.Bli.BliLinkageB.TraderCells

/-!
# bli-linkage, angle B — K3's conclusion of record with the price-reading trader

`Degenerate.no_degenerate_linked_bli` asks for `MachineSentenceCodes` of the family
`n ↦ ∼ lit_{n+1, χ n, todayIdx n}`, whose cell index is today's rounded price — a hypothesis
no moving inductor can discharge (FB-14). This module restates the conclusion of record over
the price-reading trader `TraderCells.sellCells`: the only metering hypothesis is on the
*paired literal family* `z ↦ lit_{z.unpair.1 + 1, χ z.unpair.1, z.unpair.2}`, which carries
nothing about today's cell, and the price input is the indicator form
`Q n (lit_{n+1, χ n, r}) = [r = todayIdx n]` on every cell `r < d`, supplied by
`degenerate_literal_one` (new: the literal of today's cell is priced `1`) and
`Degenerate.degenerate_literal_zero` (the others `0`). The grid's cells are `Finset.range d`
(`hcells`); at `halfRound`, `d = 2`.

`Degenerate.no_degenerate_linked_bli` is kept: it is correct, and its `hψ` is dischargeable
for a base whose rounded price is eventually constant on the coordinate — which is exactly
when `hmove` fails. The pair is the content of FB-14.
-/

namespace Cleanroom.Bli.BliLinkageB

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

section Literal

variable {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) {S : StateSystem} {atoms : ℕ → Finset ℕ}
variable {DP : DeductiveProcess} {P Q : History} {index : ℕ → List ℕ}

/-- **K3a, the positive half**: under `PCPσ ∧ E5σ ∧ E1x ∧ Degenerate` at the B2 state sentence on
a grid with `SpuriousEntails`, for a pinned coordinate `c` and the cell `r` that `deg n` assigns
it, the base prices tomorrow's literal at `1` (the point mass is the whole cell mass).
Source: [[bli-program]] §3.6(iii); mandate K3a
Kind: C
Fidelity: exact (stage level)
Hyps: (a) -/
theorem degenerate_literal_one (hcoh : PCPσ atoms DP P)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (hE5 : E5σ (stateOf C) S P)
    (hE1 : E1x Q P) {deg : ℕ → ℕ} (hdegS : ∀ n, deg n ∈ S.states (n + 1))
    (hdeg : Degenerate (stateOf C) P deg) (n : ℕ)
    (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n) {c : ℕ}
    (hc : c ∈ pinned C index n) {r : ℕ} (hr : r ∈ C.cells (n + 1))
    (hentry : entryOf c (tableOfCode (deg n)) = some r) :
    Q n (C.literal (n + 1) (sentenceOfCode c) r) = 1 := by
  rw [forced_marginal C hcoh hatoms hE5 hE1 n hsp hc hr, cellMass]
  obtain ⟨k, W, w, -, hM⟩ :=
    (coherentOnW_iff _ _ _).1 ((coherentOn_iff_coherentOnW _ _ _).1 (hcoh n))
  have hσA : ∀ q ∈ S.states (n + 1),
      sentenceAtomCodes (stateOf C (n + 1) q) ⊆ smallAtoms n ∪ atoms n := fun q hq =>
    (atoms_subset_stateAtoms (stateOf C) S hq).trans ((hatoms n).trans Finset.subset_union_right)
  rw [Finset.sum_eq_single_of_mem (deg n) (Finset.mem_filter.2 ⟨hdegS n, hentry⟩)
    fun q hq hne => mass_eq_zero_of_degenerate (partitionAt_of_E5σ hE5 n)
      (fun q hq => hM.nonneg_of_subset (hσA q hq)) (hdegS n) (hdeg n) (Finset.mem_filter.1 hq).1 hne]
  exact hdeg n

/-- **K3a in indicator form**: on a pinned coordinate the base prices tomorrow's cell literals
as the indicator of today's cell, `Q n (lit_{n+1, c, r}) = [r = todayIdx]`, for every cell `r`.
Source: mandate K3a; this package (FB-14)
Kind: C
Fidelity: exact (stage level)
Hyps: (a) -/
theorem degenerate_literal_indicator (hcoh : PCPσ atoms DP P)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (hE5 : E5σ (stateOf C) S P)
    (hE1 : E1x Q P) {deg : ℕ → ℕ} (hdegS : ∀ n, deg n ∈ S.states (n + 1))
    (hdeg : Degenerate (stateOf C) P deg) (n : ℕ)
    (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n) {c : ℕ}
    (hc : c ∈ pinned C index n) {t : ℕ}
    (hentry : entryOf c (tableOfCode (deg n)) = some t) {r : ℕ} (hr : r ∈ C.cells (n + 1)) :
    Q n (C.literal (n + 1) (sentenceOfCode c) r) = if r = t then 1 else 0 := by
  split_ifs with h
  · subst h
    exact degenerate_literal_one C hcoh hatoms hE5 hE1 hdegS hdeg n hsp hc hr hentry
  · refine degenerate_literal_zero C hcoh hatoms hE5 hE1 hdegS hdeg n hsp hc hr ?_
    rw [hentry]
    exact fun h' => h (Option.some.inj h').symm

end Literal

section Record

variable {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) {S : StateSystem} {atoms : ℕ → Finset ℕ}
variable {DP : DeductiveProcess} {P Q : History} {index : ℕ → List ℕ}

/-- **K3, the conclusion of record (price-reading form; supersedes
`Degenerate.no_degenerate_linked_bli` as the instantiable statement).** Over a logical inductor
`Q` relative to `DP`, with a coordinate family `χ` listed by the degenerate table `deg n` at the
cell `todayIdx n` (today's rounded price), pinned from day `N` on, on a grid with cells
`Finset.range d` and `SpuriousEntails`: if the **paired literal family**
`z ↦ lit_{z.unpair.1 + 1, χ z.unpair.1, z.unpair.2}` is machine-metered (nothing about today's
cell enters it), every stage has a consistent world, a moved day's literal of today's cell is
refuted by some stage (`hdec`), and the rounded price moves infinitely often (`hmove`), then no
superbelief satisfies `PCPσ ∧ E5σ ∧ E1x Q P ∧ Degenerate` at the B2 state sentence. The trader
is `TraderCells.sellCells` (sells each cell literal in proportion to its price), which needs no
knowledge of `todayIdx`. `hmove` is a hypothesis (mandate § K3).
Source: [[bli-program]] §3.6(iii); [[bli-program-desiderata]] I2; bli-paper-043; bli-soto-a-007; mandate K3 (`no_degenerate_linked_bli`); FB-14
Kind: C
Fidelity: exact (stage level; `hmove`, `hdec`, `hworld` explicit; the metering hypothesis on the paired literal family only)
Hyps: (a); `hmove` is the honest conditional of mandate § K3 -/
theorem no_degenerate_linked_bli_cells [IsLogicalInductor Q DP] (deg χ todayIdx : ℕ → ℕ)
    (d N : ℕ) (hcells : ∀ n, C.cells (n + 1) = Finset.range d)
    (hpin : ∀ n ≥ N, χ n ∈ pinned C index n)
    (hdegS : ∀ n, deg n ∈ S.states (n + 1)) (ht : ∀ n, todayIdx n < d)
    (hentry : ∀ n, entryOf (χ n) (tableOfCode (deg n)) = some (todayIdx n))
    (hsp : ∀ n, SpuriousEntails (stateOf C) C.literal S index C.cells n)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n)
    (hψ : MachineSentenceCodes fun z =>
      C.literal (z.unpair.1 + 1) (sentenceOfCode (χ z.unpair.1)) z.unpair.2)
    (hworld : ∀ k, ∃ v : PCWorld, v.ConsistentWith (DP.D k)) {moved : ℕ → Prop}
    (hdec : ∀ n, moved n → ∃ k, ∀ v : PCWorld, v.ConsistentWith (DP.D k) →
      ¬ v.Holds (C.literal (n + 1) (sentenceOfCode (χ n)) (todayIdx n)))
    (hmove : Set.Infinite {n | moved n}) :
    ¬ (PCPσ atoms DP P ∧ E5σ (stateOf C) S P ∧ E1x Q P ∧ Degenerate (stateOf C) P deg) := by
  rintro ⟨hcoh, hE5, hE1, hdeg⟩
  refine no_inductor_prices_indicator_eventually
    (L := fun n r => C.literal (n + 1) (sentenceOfCode (χ n)) r) (d := d) hψ Q DP N todayIdx
    ?_ (fun n _ => ht n) hworld hdec hmove
  intro n hn r hr
  exact degenerate_literal_indicator C hcoh hatoms hE5 hE1 hdegS hdeg n (hsp n) (hpin n hn)
    (hentry n) (by rw [hcells]; exact Finset.mem_range.2 hr)

end Record

end Cleanroom.Bli.BliLinkageB
