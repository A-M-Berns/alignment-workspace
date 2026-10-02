import Cleanroom.Bli.BliLinkageB.Determination
import Cleanroom.Bli.BliLinkageB.Trader

/-!
# bli-linkage, angle B — no degenerate linked BLI (K3)

**K3a, under interval linkage** (`degenerate_quote_zero`): if the superbelief is the point mass
on `deg n` (`Degenerate`), every charged world of the day-`n` mixture holds the state sentence
of `deg n`, hence — linked, with interval semantics — the quote of the open cell `deg n` assigns
each listed coordinate; so a quote of an interval whose closed interval misses that closed cell
is priced `0`, and by `E1x` the base prices it `0` too. The "moves" the trader needs must now
clear the *open neighbourhood* of today's cell, not merely cross the rounding boundary: a
weaker hypothesis, `hmove` changes accordingly (see the report).

**K3a, in literal form** (`degenerate_literal_zero`): with the B2 state sentence, every cell
literal of a pinned coordinate at a cell other than `deg n`'s is priced `0` (the mandate's
form, from `determination_stage` and the point mass), so the negated literal
`ψ n := ∼ lit_{n+1,χ n,todayIdx n}` ("tomorrow's rounded price of `χ n` differs from today's")
is priced `0` whenever pinned.

**K3b, the trader** (`buyOne`, `buyOne_ec`, `buyOne_exploits`): one share of `ψ n` on day `n`,
efficiently computable by FAF's `EfficientlyComputable.ofSingleTradeBlocksBig` with the constant
coefficient `EF.const 1`; it exploits any market pricing `ψ n` below a summable `ε n` (stated
with bounded partial sums, the finite form of summability) whenever the true members of `ψ`
each enter a stage and there are infinitely many of them (`hmove`), by FAF's definitional
engine `exploits_of_bddBelow_of_unbounded`: bounded below by `−C`, unbounded above along worlds
consistent with ever-later stages. **The "moves" clause is a hypothesis**, as the mandate's
§ K3 says it must be (the program's derivation of it from `lic_provind` is a misreading; filed
in findings). The LIA instance is not built in this attempt (see the report and the handoff).

**The conclusion of record** (`no_degenerate_linked_bli`): over a logical inductor whose
rounded price of a listed, eventually pinned coordinate moves infinitely often, no superbelief
satisfies `PCPσ ∧ E5σ ∧ E1x ∧ Degenerate` at the B2 state sentence on a grid with
`SpuriousEntails`.
-/

namespace Cleanroom.Bli.BliLinkageB

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

/-! ## K3a under interval linkage -/

section Abstract

variable {k : ℕ} {W : Fin k → PCWorld} {w : Fin k → ℝ} {A : Finset ℕ} {p : Sentence → ℝ}

/-- A sentence of `p`-value `1` holds in every charged world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsMixture.holds_of_eq_one (hM : IsMixture W w A p) {ψ : Sentence}
    (hψ : sentenceAtomCodes ψ ⊆ A) (h1 : p ψ = 1) {i : Fin k} (hi : 0 < w i) :
    (W i).Holds ψ := by
  have hzero : ∑ j, w j * (1 - (W j).payout ψ) = 0 := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, hM.sum_one, ← hM.rep ψ hψ, h1, sub_self]
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin k)), 0 ≤ w j * (1 - (W j).payout ψ) :=
    fun j _ => mul_nonneg (hM.nonneg j) (sub_nonneg.2 (payout_mem_Icc _ _).2)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hzero i (Finset.mem_univ i)
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (ne_of_gt hi)
  · exact holds_of_payout_ne_zero (by rw [← sub_eq_zero.1 h]; exact one_ne_zero)

/-- A sentence refuted in every charged world has `p`-value `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsMixture.eq_zero_of_not_holds (hM : IsMixture W w A p) {ψ : Sentence}
    (hψ : sentenceAtomCodes ψ ⊆ A) (h : ∀ i, 0 < w i → ¬ (W i).Holds ψ) : p ψ = 0 := by
  rw [hM.rep ψ hψ]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases (hM.nonneg i).lt_or_eq with hi | hi
  · rw [payout_of_not_holds (h i hi), mul_zero]
  · rw [← hi, zero_mul]

/-- The payout of a negation is one minus the payout.
Source: none: infrastructure (FAF `PCWorld.holds_neg`)
Kind: L
Fidelity: n/a -/
lemma payout_neg (v : PCWorld) (ψ : Sentence) : v.payout (∼ψ) = 1 - v.payout ψ := by
  unfold PCWorld.payout
  by_cases h : v.Holds ψ
  · rw [if_pos h, if_neg (by rw [PCWorld.holds_neg]; exact not_not.2 h)]; norm_num
  · rw [if_neg h, if_pos (by rw [PCWorld.holds_neg]; exact h)]; norm_num

/-- The value of a negation under a mixture is one minus the value.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsMixture.neg (hM : IsMixture W w A p) {ψ : Sentence} (hψ : sentenceAtomCodes ψ ⊆ A) :
    p (∼ψ) = 1 - p ψ := by
  rw [hM.rep (∼ψ) (by simpa using hψ), hM.rep ψ hψ, ← hM.sum_one, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [payout_neg]; ring

variable {σ : ℕ → ℕ → Sentence} {S : StateSystem} {m : ℕ}
variable {quote : ℕ → Sentence → ℚ → ℚ → Sentence} {cellOf : ℕ → ℕ → Sentence → ℚ × ℚ}

/-- **K3a under interval linkage, mixture level.** If the degenerate candidate `d` has mass one,
every charged world holds its state sentence, hence (linked, interval semantics) the quote of
the cell it assigns `φ`; a quote of an interval `J` whose closed interval misses that closed
cell is therefore refuted in every charged world and priced `0`.
Source: [[bli-program]] §3.6(iii); [[bli-program-desiderata]] I2; mandate K3 (angle B)
Kind: P
Fidelity: variant: interval linkage — "the next price lies in the open neighbourhood of today's cell", so a quote clearing the neighbourhood is priced `0`
Hyps: (a) -/
theorem IsMixture.degenerate_quote_zero (hM : IsMixture W w A p)
    (hlink : ∀ i, 0 < w i → LinkedWorld σ quote S cellOf m (W i))
    (hsem : ∀ i, 0 < w i → IntervalSem quote (W i)) {d : ℕ} (hd : d ∈ S.states m)
    (hσA : sentenceAtomCodes (σ m d) ⊆ A) (hdeg : p (σ m d) = 1) {φ : Sentence}
    (hφ : φ ∈ smallSet m) (J : ℚ × ℚ) (hJA : sentenceAtomCodes (quote m φ J.1 J.2) ⊆ A)
    (hdisj : min J.2 (cellOf m d φ).2 < max J.1 (cellOf m d φ).1) :
    p (quote m φ J.1 J.2) = 0 := by
  refine hM.eq_zero_of_not_holds hJA fun i hi hJ => ?_
  have hs := hM.holds_of_eq_one hσA hdeg hi
  have hc := hlink i hi d hd φ hφ hs
  have := (hsem i hi).meet m φ J.1 J.2 _ _ hJ hc
  exact absurd (lt_of_lt_of_le hdisj this) (lt_irrefl _)

end Abstract

section Day

variable {σ : ℕ → ℕ → Sentence} {quote : ℕ → Sentence → ℚ → ℚ → Sentence} {S : StateSystem}
variable {cellOf : ℕ → ℕ → Sentence → ℚ × ℚ} {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess}
variable {P Q : History}

/-- **K3a under interval linkage, on the base**: over a linked coherent stage mixture that is
degenerate, the base prices at `0` every small day-`(n+1)` quote of a listed coordinate whose
closed interval misses the closed cell today's degenerate state assigns it.
Source: [[bli-program]] §3.6(iii); mandate K3 (angle B)
Kind: C
Fidelity: variant: interval linkage
Hyps: (a) -/
theorem degenerate_quote_zero_day (hcoh : PCPσLinked σ quote S cellOf atoms DP P)
    (hatoms : ∀ n, stateAtoms σ S n ⊆ atoms n) (hE1 : E1x Q P) {deg : ℕ → ℕ}
    (hdegS : ∀ n, deg n ∈ S.states (n + 1)) (hdeg : Degenerate σ P deg) (n : ℕ) {φ : Sentence}
    (hφ : φ ∈ smallSet (n + 1)) (J : ℚ × ℚ) (hsmall : quote (n + 1) φ J.1 J.2 ∈ smallSet n)
    (hdisj : min J.2 (cellOf (n + 1) (deg n) φ).2 < max J.1 (cellOf (n + 1) (deg n) φ).1) :
    Q n (quote (n + 1) φ J.1 J.2) = 0 := by
  obtain ⟨k, W, w, hM, hσA, hlink, hsem⟩ := hcoh.exists_mixture hatoms n
  rw [← hE1 n _ hsmall]
  exact hM.degenerate_quote_zero hlink hsem (hdegS n) (hσA _ (hdegS n)) (hdeg n) hφ J
    ((atoms_subset_smallAtoms hsmall).trans Finset.subset_union_left) hdisj

end Day

/-! ## K3a in literal form -/

section Literal

variable {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) {S : StateSystem} {atoms : ℕ → Finset ℕ}
variable {DP : DeductiveProcess} {P Q : History} {index : ℕ → List ℕ}

/-- Under a point mass on `d`, every other candidate has mass `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_eq_zero_of_degenerate {σ : ℕ → ℕ → Sentence} {n : ℕ}
    (hpart : PartitionAt σ S (P n) (n + 1)) (hnn : ∀ q ∈ S.states (n + 1), 0 ≤ P n (σ (n + 1) q))
    {d : ℕ} (hd : d ∈ S.states (n + 1)) (hdeg : P n (σ (n + 1) d) = 1) {q : ℕ}
    (hq : q ∈ S.states (n + 1)) (hne : q ≠ d) : P n (σ (n + 1) q) = 0 := by
  have h := hpart.mass
  rw [← Finset.add_sum_erase _ _ hd, hdeg] at h
  have hzero : ∑ q ∈ (S.states (n + 1)).erase d, P n (σ (n + 1) q) = 0 := by linarith
  exact (Finset.sum_eq_zero_iff_of_nonneg fun q hq => hnn q (Finset.mem_of_mem_erase hq)).1 hzero q
    (Finset.mem_erase.2 ⟨hne, hq⟩)

/-- **K3a in literal form**: under `PCPσ ∧ E5σ ∧ E1x ∧ Degenerate` at the B2 state sentence on a
grid with `SpuriousEntails`, for a pinned coordinate `c` and a cell `r` other than the one
`deg n` assigns `c`, the base prices tomorrow's literal at `0`.
Source: [[bli-program]] §3.6(iii); mandate K3a
Kind: C
Fidelity: exact (stage level)
Hyps: (a) -/
theorem degenerate_literal_zero (hcoh : PCPσ atoms DP P)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (hE5 : E5σ (stateOf C) S P)
    (hE1 : E1x Q P) {deg : ℕ → ℕ} (hdegS : ∀ n, deg n ∈ S.states (n + 1))
    (hdeg : Degenerate (stateOf C) P deg) (n : ℕ)
    (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n) {c : ℕ}
    (hc : c ∈ pinned C index n) {r : ℕ} (hr : r ∈ C.cells (n + 1))
    (hne : entryOf c (tableOfCode (deg n)) ≠ some r) :
    Q n (C.literal (n + 1) (sentenceOfCode c) r) = 0 := by
  rw [forced_marginal C hcoh hatoms hE5 hE1 n hsp hc hr, cellMass]
  obtain ⟨k, W, w, -, hM⟩ :=
    (coherentOnW_iff _ _ _).1 ((coherentOn_iff_coherentOnW _ _ _).1 (hcoh n))
  have hσA : ∀ q ∈ S.states (n + 1),
      sentenceAtomCodes (stateOf C (n + 1) q) ⊆ smallAtoms n ∪ atoms n := fun q hq =>
    (atoms_subset_stateAtoms (stateOf C) S hq).trans ((hatoms n).trans Finset.subset_union_right)
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Finset.mem_filter] at hq
  have hqd : q ≠ deg n := fun h => hne (by rw [← h]; exact hq.2)
  exact mass_eq_zero_of_degenerate (partitionAt_of_E5σ hE5 n)
    (fun q hq => hM.nonneg_of_subset (hσA q hq)) (hdegS n) (hdeg n) hq.1 hqd

/-- **The negated literal of today's cell is priced `0`**: with `todayIdx n` the cell `deg n`
assigns the pinned coordinate `c n`, `Q n (∼ lit_{n+1, c n, todayIdx n}) = 0`.
Source: mandate K3a (`ψ n := ∼ lit (n+1) (χ n) (todayIdx n)`)
Kind: C
Fidelity: exact (stage level)
Hyps: (a) -/
theorem degenerate_neg_literal_zero (hcoh : PCPσ atoms DP P)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n) (hE5 : E5σ (stateOf C) S P)
    (hE1 : E1x Q P) {deg : ℕ → ℕ} (hdegS : ∀ n, deg n ∈ S.states (n + 1))
    (hdeg : Degenerate (stateOf C) P deg) (n : ℕ)
    (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n) {c : ℕ}
    (hc : c ∈ pinned C index n) {t : ℕ} (ht : t ∈ C.cells (n + 1))
    (hentry : entryOf c (tableOfCode (deg n)) = some t)
    (hneg : (∼ C.literal (n + 1) (sentenceOfCode c) t) ∈ smallSet n) :
    Q n (∼ C.literal (n + 1) (sentenceOfCode c) t) = 0 := by
  obtain ⟨k, W, w, -, hM⟩ :=
    (coherentOnW_iff _ _ _).1 ((coherentOn_iff_coherentOnW _ _ _).1 (hcoh n))
  have hσA : ∀ q ∈ S.states (n + 1),
      sentenceAtomCodes (stateOf C (n + 1) q) ⊆ smallAtoms n ∪ atoms n := fun q hq =>
    (atoms_subset_stateAtoms (stateOf C) S hq).trans ((hatoms n).trans Finset.subset_union_right)
  rw [← hE1 n _ hneg, hM.neg (literal_atoms_subset C hc ht),
    determination_stage C hcoh hatoms hE5 n hsp hc ht, cellMass]
  rw [Finset.sum_eq_single_of_mem (deg n) (Finset.mem_filter.2 ⟨hdegS n, hentry⟩)
    fun q hq hne => mass_eq_zero_of_degenerate (partitionAt_of_E5σ hE5 n)
      (fun q hq => hM.nonneg_of_subset (hσA q hq)) (hdegS n) (hdeg n) (Finset.mem_filter.1 hq).1 hne]
  rw [hdeg n, sub_self]

end Literal

/-! ## The conclusions of record -/

section Record

variable {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) {S : StateSystem} {atoms : ℕ → Finset ℕ}
variable {DP : DeductiveProcess} {P Q : History} {index : ℕ → List ℕ}

/-- **K3, the conclusion of record (literal form).** Over a logical inductor `Q` relative to
`DP`, with a coordinate family `χ` listed by the degenerate table at the cell `todayIdx n`,
pinned from day `N` on (with its negated literal small), on a grid with `SpuriousEntails`: if
the negated literal family `ψ n := ∼ lit_{n+1, χ n, todayIdx n}` is machine-metered, a true
member enters a stage (`hdec`), and the rounded price moves infinitely often (`hmove`), then no
superbelief satisfies `PCPσ ∧ E5σ ∧ E1x Q P ∧ Degenerate` at the B2 state sentence.
`hmove` is a hypothesis (mandate § K3); the LIA instance is not built here.
Source: [[bli-program]] §3.6(iii); [[bli-program-desiderata]] I2; bli-paper-043; bli-soto-a-007; mandate K3 (`no_degenerate_linked_bli`)
Kind: C
Fidelity: exact (stage level; `hmove`, `hdec`, `hψ` explicit; the literal and its negation pinned)
Hyps: (a); `hmove` is the honest conditional of mandate § K3 -/
theorem no_degenerate_linked_bli [IsLogicalInductor Q DP] (deg χ todayIdx : ℕ → ℕ) (N : ℕ)
    (hpin : ∀ n ≥ N, χ n ∈ pinned C index n)
    (hneg : ∀ n ≥ N, (∼ C.literal (n + 1) (sentenceOfCode (χ n)) (todayIdx n)) ∈ smallSet n)
    (hdegS : ∀ n, deg n ∈ S.states (n + 1)) (ht : ∀ n, todayIdx n ∈ C.cells (n + 1))
    (hentry : ∀ n, entryOf (χ n) (tableOfCode (deg n)) = some (todayIdx n))
    (hsp : ∀ n, SpuriousEntails (stateOf C) C.literal S index C.cells n)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n)
    (hψ : MachineSentenceCodes fun n => ∼ C.literal (n + 1) (sentenceOfCode (χ n)) (todayIdx n))
    (hworld : ∀ k, ∃ v : PCWorld, v.ConsistentWith (DP.D k)) {moved : ℕ → Prop}
    (hdec : ∀ n, moved n → ∃ k, ∀ v : PCWorld, v.ConsistentWith (DP.D k) →
      v.Holds (∼ C.literal (n + 1) (sentenceOfCode (χ n)) (todayIdx n)))
    (hmove : Set.Infinite {n | moved n}) :
    ¬ (PCPσ atoms DP P ∧ E5σ (stateOf C) S P ∧ E1x Q P ∧ Degenerate (stateOf C) P deg) := by
  rintro ⟨hcoh, hE5, hE1, hdeg⟩
  exact no_inductor_prices_zero_eventually hψ Q DP N
    (fun n hn => degenerate_neg_literal_zero C hcoh hatoms hE5 hE1 hdegS hdeg n (hsp n) (hpin n hn)
      (ht n) (hentry n) (hneg n hn)) hworld hdec hmove

end Record

section RecordInterval

variable {σ : ℕ → ℕ → Sentence} {quote : ℕ → Sentence → ℚ → ℚ → Sentence} {S : StateSystem}
variable {cellOf : ℕ → ℕ → Sentence → ℚ × ℚ} {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess}
variable {P Q : History}

/-- **K3, the conclusion of record (interval form).** Over a logical inductor, for a coordinate
family `χ` and an interval family `J n` whose closed interval misses the closed cell today's
degenerate state assigns `χ n`, with the quotes small from day `N` on: if the quote family is
machine-metered, a true quote enters a stage, and the next-day price lands in `J n` infinitely
often (`hmove` — now "clears the open neighbourhood of today's cell", a weaker hypothesis to
discharge than crossing the rounding boundary), then no superbelief satisfies
`PCPσLinked ∧ E1x Q P ∧ Degenerate`. No partition hypothesis is needed.
Source: mandate K3 (angle B: "the same trader works; 'moves' must now clear the neighbourhood")
Kind: C
Fidelity: variant: interval linkage; `hmove` explicit
Hyps: (a) -/
theorem no_degenerate_linked_bli_interval [IsLogicalInductor Q DP] (deg : ℕ → ℕ)
    (χ : ℕ → Sentence) (J : ℕ → ℚ × ℚ) (N : ℕ)
    (hχ : ∀ n, χ n ∈ smallSet (n + 1))
    (hsmall : ∀ n ≥ N, quote (n + 1) (χ n) (J n).1 (J n).2 ∈ smallSet n)
    (hdegS : ∀ n, deg n ∈ S.states (n + 1))
    (hdisj : ∀ n, min (J n).2 (cellOf (n + 1) (deg n) (χ n)).2 <
      max (J n).1 (cellOf (n + 1) (deg n) (χ n)).1)
    (hatoms : ∀ n, stateAtoms σ S n ⊆ atoms n)
    (hψ : MachineSentenceCodes fun n => quote (n + 1) (χ n) (J n).1 (J n).2)
    (hworld : ∀ k, ∃ v : PCWorld, v.ConsistentWith (DP.D k)) {moved : ℕ → Prop}
    (hdec : ∀ n, moved n → ∃ k, ∀ v : PCWorld, v.ConsistentWith (DP.D k) →
      v.Holds (quote (n + 1) (χ n) (J n).1 (J n).2))
    (hmove : Set.Infinite {n | moved n}) :
    ¬ (PCPσLinked σ quote S cellOf atoms DP P ∧ E1x Q P ∧ Degenerate σ P deg) := by
  rintro ⟨hcoh, hE1, hdeg⟩
  exact no_inductor_prices_zero_eventually hψ Q DP N
    (fun n hn => degenerate_quote_zero_day hcoh hatoms hE1 hdegS hdeg n (hχ n) (J n) (hsmall n hn)
      (hdisj n)) hworld hdec hmove

end RecordInterval

end Cleanroom.Bli.BliLinkageB
