import Cleanroom.Bli.BliLinkageB.Mixture

/-!
# bli-linkage, angle B — the bracket determination theorem (K1/K2 in interval form)

Under **interval linkage** the superbelief's marginals are not pinned to the base's prices
but *bracketed* by them. In a world mixture `P n` whose charged worlds are linked at day `n+1`
and have interval semantics, and under the partition constraint, for every interval `I`:

* `∑_{q : cell_q ⊂ I} P n σ_q ≤ P n (quote_{n+1,φ,I})` (`bracket_lower`): a charged world
  holding `σ_q` holds the quote of `q`'s cell (linkage), hence of every strict enlargement
  (`IntervalSem.mono`);
* `P n (quote_{n+1,φ,I}) ≤ ∑_{q : cell_q meets I} P n σ_q` (`bracket_upper`): a charged world
  holding both the quote of `I` and the quote of `q`'s cell has the two closed intervals meeting
  (`IntervalSem.meet`).

With `E1x` the left-hand prices become the base's (`bracket_lower_day`, `bracket_upper_day`),
and with faith (`E2xσ`) and the representatives the **two-sided bracket balance**
`bracket_balance` follows: for an outer family `I r ⊃ cell r` and an inner family `J r` meeting
no other cell,

`∑_r rep_r · Q n (quote_{J r}) ≤ Q n φ ≤ ∑_r rep_r · Q n (quote_{I r})`.

This is the interval-linkage analogue of `D_NNUcell` — an inequality pair in place of the exact
identity (its slack is the overlap `bli-found` F-16 forces), and the natural `D_NNU`-with-width
reading of the program's `D-NNU(Q)`.

Two forms of coherence appear. `PCPσLinked` is the honest **stage-level** form: `P n` is a
mixture of worlds consistent with the stage `DP.D n` *that are linked and have interval
semantics* (both are properties of the mixture's worlds, since the stage has not decided the
day-`(n+1)` quotes). `PCPσTheory ∧ LNKcell` with an `IntervalFamily` implies it
(`pcpσLinked_of_theory`) — but at the theory level every quote is decided, so `E1x` then forces
the base to price every pinned next-day quote at `0` or `1` (`theory_coherent_e1x_decides`): the
theory-level package is degenerate for an uncertain base, which is why the stage-level form is
the one of record.
-/

namespace Cleanroom.Bli.BliLinkageB

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

/-! ## Cell–interval relations -/

/-- The closed cell `q` assigns `φ` lies strictly inside the open interval `I`.
Source: mandate § Attempt angles (B: "`cell_q(φ) ⊆ I`")
Kind: D
Fidelity: exact (strict: a forced quote is open around the cell, F-16) -/
abbrev CellInside (cellOf : ℕ → ℕ → Sentence → ℚ × ℚ) (m q : ℕ) (φ : Sentence) (I : ℚ × ℚ) :
    Prop :=
  I.1 < (cellOf m q φ).1 ∧ (cellOf m q φ).2 < I.2

/-- The closed cell `q` assigns `φ` meets the closed interval `I`.
Source: mandate § Attempt angles (B: "`cell_q(φ) ∩ I ≠ ∅`")
Kind: D
Fidelity: exact (closed intervals) -/
abbrev CellMeets (cellOf : ℕ → ℕ → Sentence → ℚ × ℚ) (m q : ℕ) (φ : Sentence) (I : ℚ × ℚ) :
    Prop :=
  max I.1 (cellOf m q φ).1 ≤ min I.2 (cellOf m q φ).2

/-! ## The brackets on an abstract mixture -/

section Abstract

variable {k : ℕ} {W : Fin k → PCWorld} {w : Fin k → ℝ} {A : Finset ℕ} {p : Sentence → ℝ}
variable {σ : ℕ → ℕ → Sentence} {S : StateSystem} {m : ℕ}
variable {quote : ℕ → Sentence → ℚ → ℚ → Sentence} {cellOf : ℕ → ℕ → Sentence → ℚ × ℚ}

/-- **Bracket, lower half**: the mass of the candidates whose cell lies strictly inside `I` is at
most the mixture's price of the quote of `I`.
Source: mandate § Attempt angles (B: the bracket determination theorem); [[bli-program]] §3.6(i)
Kind: P
Fidelity: variant: interval linkage (open cells), lower bracket in place of the exact marginal
Hyps: (a) -/
theorem IsMixture.bracket_lower (hM : IsMixture W w A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A) (hpart : PartitionAt σ S p m)
    (hlink : ∀ i, 0 < w i → LinkedWorld σ quote S cellOf m (W i))
    (hsem : ∀ i, 0 < w i → IntervalSem quote (W i))
    {φ : Sentence} (hφ : φ ∈ smallSet m) (I : ℚ × ℚ)
    (hIA : sentenceAtomCodes (quote m φ I.1 I.2) ⊆ A) :
    ∑ q ∈ (S.states m).filter (fun q => CellInside cellOf m q φ I), p (σ m q) ≤
      p (quote m φ I.1 I.2) := by
  rw [hM.sum_and_state hσA hpart hIA]
  calc ∑ q ∈ (S.states m).filter (fun q => CellInside cellOf m q φ I), p (σ m q)
      = ∑ q ∈ (S.states m).filter (fun q => CellInside cellOf m q φ I),
          p (quote m φ I.1 I.2 ⋏ σ m q) := by
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [Finset.mem_filter] at hq
        refine (hM.and_state_eq_of_forced (hσA q hq.1) hIA fun i hi hs => ?_).symm
        exact (hsem i hi).mono m φ _ _ _ _ hq.2.1 hq.2.2 (hlink i hi q hq.1 φ hφ hs)
    _ ≤ ∑ q ∈ S.states m, p (quote m φ I.1 I.2 ⋏ σ m q) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun q hq _ => hM.and_state_nonneg (hσA q hq) hIA

/-- **Bracket, upper half**: the mixture's price of the quote of `I` is at most the mass of the
candidates whose cell meets `I`.
Source: mandate § Attempt angles (B: the bracket determination theorem); [[bli-program]] §3.6(i)
Kind: P
Fidelity: variant: interval linkage (open cells), upper bracket in place of the exact marginal
Hyps: (a) -/
theorem IsMixture.bracket_upper (hM : IsMixture W w A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A) (hpart : PartitionAt σ S p m)
    (hlink : ∀ i, 0 < w i → LinkedWorld σ quote S cellOf m (W i))
    (hsem : ∀ i, 0 < w i → IntervalSem quote (W i))
    {φ : Sentence} (hφ : φ ∈ smallSet m) (I : ℚ × ℚ)
    (hIA : sentenceAtomCodes (quote m φ I.1 I.2) ⊆ A) :
    p (quote m φ I.1 I.2) ≤
      ∑ q ∈ (S.states m).filter (fun q => CellMeets cellOf m q φ I), p (σ m q) := by
  rw [hM.sum_and_state hσA hpart hIA]
  calc ∑ q ∈ S.states m, p (quote m φ I.1 I.2 ⋏ σ m q)
      = ∑ q ∈ (S.states m).filter (fun q => CellMeets cellOf m q φ I),
          p (quote m φ I.1 I.2 ⋏ σ m q) := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro q hq hnot
        rw [Finset.mem_filter, not_and] at hnot
        refine hM.and_state_eq_zero_of_excluded (hσA q hq) hIA fun i hi hs hI => hnot hq ?_
        exact (hsem i hi).meet m φ I.1 I.2 _ _ hI (hlink i hi q hq φ hφ hs)
    _ ≤ ∑ q ∈ (S.states m).filter (fun q => CellMeets cellOf m q φ I), p (σ m q) :=
        Finset.sum_le_sum fun q hq => hM.and_state_le (hσA q (Finset.mem_filter.1 hq).1) hIA

/-- **Balance from faith**: under the partition, exact faith at every candidate gives
`p φ = ∑_q val_q(φ) · p σ_q` — constraint 4 at `φ`, derived.
Source: mandate K2 (b); bli-found F-11
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem IsMixture.balance_of_faith (hM : IsMixture W w A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A) (hpart : PartitionAt σ S p m)
    {φ : Sentence} (hφA : sentenceAtomCodes φ ⊆ A)
    (hE2 : ∀ q ∈ S.states m, p (φ ⋏ σ m q) = S.val m q φ * p (σ m q)) :
    p φ = ∑ q ∈ S.states m, S.val m q φ * p (σ m q) := by
  rw [hM.sum_and_state hσA hpart hφA]
  exact Finset.sum_congr rfl fun q hq => hE2 q hq

end Abstract

/-! ## Linked coherent stage mixtures -/

/-- **The world class of a linked stage mixture at day `n`**: consistent with the stage `DP.D n`,
linked at day `n+1`, with interval semantics. The last two are properties of the worlds of the
mixture, not of the stage: `DP.D n` has not decided the day-`(n+1)` quotes, so nothing in the
stage ties a state sentence to a quote.
Source: mandate § Attempt angles (B); this package
Kind: D
Fidelity: exact -/
def LinkedStage (σ : ℕ → ℕ → Sentence) (quote : ℕ → Sentence → ℚ → ℚ → Sentence)
    (S : StateSystem) (cellOf : ℕ → ℕ → Sentence → ℚ × ℚ) (DP : DeductiveProcess) (n : ℕ)
    (v : PCWorld) : Prop :=
  v.ConsistentWith (DP.D n) ∧ LinkedWorld σ quote S cellOf (n + 1) v ∧ IntervalSem quote v

/-- **PCPσLinked — coherence over linked stage worlds**: on every day `n`, `P n` is a mixture of
worlds of `LinkedStage … n` on the algebra of the day-`n` small sentences and `atoms n`. The
stage-level rendering of "`LNKcell ∧ PCPσ`" (which, read literally, says nothing: `LNKcell`
speaks of completed-theory worlds and `PCPσ` of stage worlds). Implied by the theory-level
package (`pcpσLinked_of_theory`); implies `PCPσ` (`PCPσLinked.toPCPσ`).
Source: mandate § Attempt angles (B); this package
Kind: D
Fidelity: variant: the stage-level form of linkage-with-coherence -/
def PCPσLinked (σ : ℕ → ℕ → Sentence) (quote : ℕ → Sentence → ℚ → ℚ → Sentence)
    (S : StateSystem) (cellOf : ℕ → ℕ → Sentence → ℚ × ℚ) (atoms : ℕ → Finset ℕ)
    (DP : DeductiveProcess) (P : History) : Prop :=
  ∀ n, CoherentOnW (LinkedStage σ quote S cellOf DP n) (smallAtoms n ∪ atoms n) (P n)

/-- `PCPσLinked → PCPσ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem PCPσLinked.toPCPσ {σ : ℕ → ℕ → Sentence} {quote : ℕ → Sentence → ℚ → ℚ → Sentence}
    {S : StateSystem} {cellOf : ℕ → ℕ → Sentence → ℚ × ℚ} {atoms : ℕ → Finset ℕ}
    {DP : DeductiveProcess} {P : History} (h : PCPσLinked σ quote S cellOf atoms DP P) :
    PCPσ atoms DP P :=
  fun n => (coherentOn_iff_coherentOnW _ _ _).2 ((h n).mono fun _ hv => hv.1)

/-- **The theory-level package implies the linked stage form**: `PCPσTheory` with `LNKcell` over
an `IntervalFamily` is `PCPσLinked`.
Source: mandate § Attempt angles (B)
Kind: L
Fidelity: n/a -/
theorem pcpσLinked_of_theory {σ : ℕ → ℕ → Sentence} {S : StateSystem}
    {cellOf : ℕ → ℕ → Sentence → ℚ × ℚ} {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess}
    {P : History} (F : IntervalFamily DP) (hL : LNKcell σ F.quote S cellOf DP)
    (h : PCPσTheory atoms DP P) : PCPσLinked σ F.quote S cellOf atoms DP P := by
  intro n
  refine (h n).mono fun v hv => ⟨hv n, ?_, F.intervalSem v hv⟩
  exact (lnkcell_iff_linkedWorld _ _ _ _ _).1 hL (n + 1) v hv

section Day

variable {σ : ℕ → ℕ → Sentence} {quote : ℕ → Sentence → ℚ → ℚ → Sentence} {S : StateSystem}
variable {cellOf : ℕ → ℕ → Sentence → ℚ × ℚ} {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess}
variable {P Q : History}

/-- Unpack a linked stage mixture at day `n` into the abstract engine's hypotheses.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem PCPσLinked.exists_mixture (hcoh : PCPσLinked σ quote S cellOf atoms DP P)
    (hatoms : ∀ n, stateAtoms σ S n ⊆ atoms n) (n : ℕ) :
    ∃ (k : ℕ) (W : Fin k → PCWorld) (w : Fin k → ℝ),
      IsMixture W w (smallAtoms n ∪ atoms n) (P n) ∧
      (∀ q ∈ S.states (n + 1), sentenceAtomCodes (σ (n + 1) q) ⊆ smallAtoms n ∪ atoms n) ∧
      (∀ i, 0 < w i → LinkedWorld σ quote S cellOf (n + 1) (W i)) ∧
      (∀ i, 0 < w i → IntervalSem quote (W i)) := by
  obtain ⟨k, W, w, hW, hM⟩ := (coherentOnW_iff _ _ _).1 (hcoh n)
  refine ⟨k, W, w, hM, fun q hq => ?_, fun i _ => (hW i).2.1, fun i _ => (hW i).2.2⟩
  exact (atoms_subset_stateAtoms σ S hq).trans ((hatoms n).trans Finset.subset_union_right)

/-- **Bracket, lower half, on the base** (K1 in interval form): for a listed coordinate whose
quote of `I` is small on day `n`, the mass of the candidates whose cell lies strictly inside `I`
is at most the base's day-`n` price of tomorrow's quote of `I`.
Source: mandate § Attempt angles (B); [[bli-program]] §3.6(i); bli-slides-010/011
Kind: C
Fidelity: variant: interval linkage, lower bracket in place of constraint 4′'s equality
Hyps: (a) -/
theorem bracket_lower_day (hcoh : PCPσLinked σ quote S cellOf atoms DP P)
    (hatoms : ∀ n, stateAtoms σ S n ⊆ atoms n) (hE5 : E5σ σ S P) (hE1 : E1x Q P) (n : ℕ)
    {φ : Sentence} (hφ : φ ∈ smallSet (n + 1)) (I : ℚ × ℚ)
    (hsmall : quote (n + 1) φ I.1 I.2 ∈ smallSet n) :
    ∑ q ∈ (S.states (n + 1)).filter (fun q => CellInside cellOf (n + 1) q φ I), P n (σ (n + 1) q) ≤
      Q n (quote (n + 1) φ I.1 I.2) := by
  obtain ⟨k, W, w, hM, hσA, hlink, hsem⟩ := hcoh.exists_mixture hatoms n
  rw [← hE1 n _ hsmall]
  exact hM.bracket_lower hσA (partitionAt_of_E5σ hE5 n) hlink hsem hφ I
    ((atoms_subset_smallAtoms hsmall).trans Finset.subset_union_left)

/-- **Bracket, upper half, on the base**: the base's day-`n` price of tomorrow's quote of `I` is
at most the mass of the candidates whose cell meets `I`.
Source: mandate § Attempt angles (B); [[bli-program]] §3.6(i)
Kind: C
Fidelity: variant: interval linkage, upper bracket in place of constraint 4′'s equality
Hyps: (a) -/
theorem bracket_upper_day (hcoh : PCPσLinked σ quote S cellOf atoms DP P)
    (hatoms : ∀ n, stateAtoms σ S n ⊆ atoms n) (hE5 : E5σ σ S P) (hE1 : E1x Q P) (n : ℕ)
    {φ : Sentence} (hφ : φ ∈ smallSet (n + 1)) (I : ℚ × ℚ)
    (hsmall : quote (n + 1) φ I.1 I.2 ∈ smallSet n) :
    Q n (quote (n + 1) φ I.1 I.2) ≤
      ∑ q ∈ (S.states (n + 1)).filter (fun q => CellMeets cellOf (n + 1) q φ I),
        P n (σ (n + 1) q) := by
  obtain ⟨k, W, w, hM, hσA, hlink, hsem⟩ := hcoh.exists_mixture hatoms n
  rw [← hE1 n _ hsmall]
  exact hM.bracket_upper hσA (partitionAt_of_E5σ hE5 n) hlink hsem hφ I
    ((atoms_subset_smallAtoms hsmall).trans Finset.subset_union_left)

/-- **Balance on the base** (K2 (b)): for `φ` small on day `n` and in faith's scope
`Sminus (n+1) (n+1)`, `Q n φ = ∑_q val_q(φ) · P n σ_q`.
Source: mandate K2 (b); bli-found F-11
Kind: C
Fidelity: exact (scope: `smallSet n ∩ Sminus (n+1) (n+1)`, both stated)
Hyps: (a) -/
theorem balance_day (hcoh : PCPσ atoms DP P) (hatoms : ∀ n, stateAtoms σ S n ⊆ atoms n)
    (hE5 : E5σ σ S P) (hE2 : E2xσ σ S P) (hE1 : E1x Q P) (n : ℕ) {φ : Sentence}
    (hφn : φ ∈ smallSet n) (hφS : φ ∈ Sminus (n + 1) (n + 1)) :
    Q n φ = ∑ q ∈ S.states (n + 1), S.val (n + 1) q φ * P n (σ (n + 1) q) := by
  obtain ⟨k, W, w, -, hM⟩ := (coherentOnW_iff _ _ _).1 ((coherentOn_iff_coherentOnW _ _ _).1 (hcoh n))
  rw [← hE1 n _ hφn]
  refine hM.balance_of_faith (fun q hq => ?_) (partitionAt_of_E5σ hE5 n)
    ((atoms_subset_smallAtoms hφn).trans Finset.subset_union_left)
    (fun q hq => hE2 n (n + 1) (Nat.lt_succ_self n) q hq φ hφS)
  exact (atoms_subset_stateAtoms σ S hq).trans ((hatoms n).trans Finset.subset_union_right)

end Day

/-! ## Regrouping the balance by cells -/

/-- **The balance regrouped by cells**: when every candidate values the coordinate at the
representative of the cell it lists, `∑_q val_q · μ_q = ∑_r rep_r · cellMass_r`.
Source: mandate K2 (c) ("the sum over `q` factors through the cells")
Kind: L
Fidelity: n/a -/
theorem sum_val_eq_sum_rep_cellMass {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲)
    (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) (n : ℕ) {index : ℕ → List ℕ}
    (hval : ValuesAtRep C S index n) {c : ℕ} (hc : c ∈ index (n + 1)) :
    ∑ q ∈ S.states (n + 1), S.val (n + 1) q (sentenceOfCode c) * P n (σ (n + 1) q) =
      ∑ r ∈ C.cells (n + 1), (C.rep (n + 1) r : ℝ) * cellMass σ S P n c r := by
  have key : ∀ q ∈ S.states (n + 1),
      S.val (n + 1) q (sentenceOfCode c) * P n (σ (n + 1) q) =
        ∑ r ∈ C.cells (n + 1), if entryOf c (tableOfCode q) = some r
          then (C.rep (n + 1) r : ℝ) * P n (σ (n + 1) q) else 0 := by
    intro q hq
    obtain ⟨r₀, hr₀, he, hv⟩ := hval q hq c hc
    rw [Finset.sum_eq_single_of_mem r₀ hr₀ (fun r _ hne => if_neg (by
      rw [he]; intro h; exact hne (Option.some.inj h).symm))]
    rw [if_pos he, hv]
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [cellMass, Finset.mul_sum, Finset.sum_filter]

/-- Under `IndexCodes`, the cell `cellOfTable` assigns a listed coordinate is the cell of the
table's entry.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cellOfTable_of_entryOf (cellLo cellHi : ℕ → ℕ → ℚ) {index : ℕ → List ℕ} {m : ℕ}
    (hidx : IndexCodes index m) {c : ℕ} (hc : c ∈ index m) {q r : ℕ}
    (he : entryOf c (tableOfCode q) = some r) :
    cellOfTable cellLo cellHi m q (sentenceOfCode c) = (cellLo m r, cellHi m r) := by
  unfold cellOfTable
  rw [hidx c hc, he]

section Balance

variable {σ : ℕ → ℕ → Sentence} {quote : ℕ → Sentence → ℚ → ℚ → Sentence} {S : StateSystem}
variable {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess} {P Q : History}

/-- **The two-sided bracket balance (angle B's determination theorem).** Over a linked coherent
stage mixture with partition, faith and small agreement, on a listed coordinate `c` that is
small on day `n` and in faith's scope, with every candidate valuing it at the representative of
a legitimate cell it lists: for an outer family `I r` strictly containing the closed cell `r`
and an inner family `J r` whose closed interval meets no other cell's closed interval,

`∑_r rep_r · Q n (quote_{J r}) ≤ Q n φ ≤ ∑_r rep_r · Q n (quote_{I r})`

(all quotes small on day `n`). The interval-linkage reading of `D-NNU(Q)`: the exact identity
`D_NNUcell` is replaced by a bracket whose slack is the overlap of the forced open cells
(`bli-found` F-16). Proof: balance by faith, regrouped by cells; each cell mass sits between the
upper bracket at `J r` and the lower bracket at `I r`.
Source: mandate § Attempt angles (B: the bracket balance); [[bli-program]] §3.6(ii); bli-found `Constraints.D_NNU`
Kind: C
Fidelity: variant: interval quotes of an outer/inner family in place of cell literals; two-sided inequality in place of the identity
Hyps: (a); `hrep` (nonnegative representatives) is a condition on the instantiation -/
theorem bracket_balance {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) (cellLo cellHi : ℕ → ℕ → ℚ)
    (hcoh : PCPσLinked σ quote S (cellOfTable cellLo cellHi) atoms DP P)
    (hatoms : ∀ n, stateAtoms σ S n ⊆ atoms n) (hE5 : E5σ σ S P) (hE2 : E2xσ σ S P)
    (hE1 : E1x Q P) (n : ℕ) {index : ℕ → List ℕ} (hidx : IndexCodes index (n + 1))
    (hval : ValuesAtRep C S index n) {c : ℕ} (hc : c ∈ index (n + 1))
    (hφn : sentenceOfCode c ∈ smallSet n) (hφS : sentenceOfCode c ∈ Sminus (n + 1) (n + 1))
    (hrep : ∀ r ∈ C.cells (n + 1), (0 : ℝ) ≤ C.rep (n + 1) r) (I J : ℕ → ℚ × ℚ)
    (hI : ∀ r ∈ C.cells (n + 1), (I r).1 < cellLo (n + 1) r ∧ cellHi (n + 1) r < (I r).2)
    (hJ : ∀ r ∈ C.cells (n + 1), ∀ r' ∈ C.cells (n + 1), r' ≠ r →
      min (J r).2 (cellHi (n + 1) r') < max (J r).1 (cellLo (n + 1) r'))
    (hIs : ∀ r ∈ C.cells (n + 1), quote (n + 1) (sentenceOfCode c) (I r).1 (I r).2 ∈ smallSet n)
    (hJs : ∀ r ∈ C.cells (n + 1), quote (n + 1) (sentenceOfCode c) (J r).1 (J r).2 ∈ smallSet n) :
    ∑ r ∈ C.cells (n + 1), (C.rep (n + 1) r : ℝ) * Q n (quote (n + 1) (sentenceOfCode c) (J r).1 (J r).2)
        ≤ Q n (sentenceOfCode c) ∧
      Q n (sentenceOfCode c) ≤
        ∑ r ∈ C.cells (n + 1), (C.rep (n + 1) r : ℝ) * Q n (quote (n + 1) (sentenceOfCode c) (I r).1 (I r).2) := by
  have hbal := balance_day hcoh.toPCPσ hatoms hE5 hE2 hE1 n hφn hφS
  rw [sum_val_eq_sum_rep_cellMass C σ S P n hval hc] at hbal
  have hφ1 : sentenceOfCode c ∈ smallSet (n + 1) := smallSet_mono (Nat.le_succ n) hφn
  obtain ⟨k, W, w, hM, hσA, -, -⟩ := hcoh.exists_mixture hatoms n
  have hμ : ∀ q ∈ S.states (n + 1), 0 ≤ P n (σ (n + 1) q) :=
    fun q hq => hM.nonneg_of_subset (hσA q hq)
  rw [hbal]
  constructor
  · refine Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_left ?_ (hrep r hr)
    refine le_trans (bracket_upper_day hcoh hatoms hE5 hE1 n hφ1 (J r) (hJs r hr)) ?_
    unfold cellMass
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q hq _ => hμ q (Finset.mem_filter.1 hq).1
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨hq.1, ?_⟩
    obtain ⟨r', hr', he, -⟩ := hval q hq.1 c hc
    rw [he]
    by_contra hne
    have hne' : r' ≠ r := fun h => hne (by rw [h])
    have hmeet := hq.2
    rw [CellMeets, cellOfTable_of_entryOf cellLo cellHi hidx hc he] at hmeet
    have := hJ r hr r' hr' hne'
    exact absurd (lt_of_lt_of_le this hmeet) (lt_irrefl _)
  · refine Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_left ?_ (hrep r hr)
    refine le_trans ?_ (bracket_lower_day hcoh hatoms hE5 hE1 n hφ1 (I r) (hIs r hr))
    unfold cellMass
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q hq _ => hμ q (Finset.mem_filter.1 hq).1
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    refine ⟨hq.1, ?_⟩
    rw [CellInside, cellOfTable_of_entryOf cellLo cellHi hidx hc hq.2]
    exact hI r hr

end Balance

/-! ## Theory-level coherence decides every quote -/

/-- **Theory-level coherence decides the quotes.** If `P n` is a mixture of completed-theory
worlds of `DP` on an algebra containing the quote's atoms, then `P n (quote m φ lo hi)` is `1`
when the price lies strictly inside `(lo, hi)` and `0` when it lies strictly outside `[lo, hi]`.
Source: this package (the degeneracy of the theory-level package); mandate K1 (traps: "a mixture of theory-consistent worlds charges one state")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem theory_coherent_decides {DP : DeductiveProcess} (F : IntervalFamily DP) {A : Finset ℕ}
    {p : Sentence → ℝ} (hcoh : CoherentOnTheory DP A p) (m : ℕ) (φ : Sentence) (lo hi : ℚ)
    (hA : sentenceAtomCodes (F.quote m φ lo hi) ⊆ A) :
    (lo < F.price m φ → F.price m φ < hi → p (F.quote m φ lo hi) = 1) ∧
      ((F.price m φ < lo ∨ hi < F.price m φ) → p (F.quote m φ lo hi) = 0) := by
  obtain ⟨k, W, w, hW, hM⟩ := (coherentOnW_iff _ _ _).1 hcoh
  constructor
  · intro h1 h2
    rw [hM.rep _ hA, ← hM.sum_one]
    exact Finset.sum_congr rfl fun i _ => by
      rw [payout_of_holds (F.reflect_lt m φ lo hi h1 h2 (W i) (hW i)), mul_one]
  · intro h
    rw [hM.rep _ hA]
    exact Finset.sum_eq_zero fun i _ => by
      rw [payout_of_not_holds (F.not_holds_of_lt (W i) (hW i) h), mul_zero]

/-- **Under theory-level coherence and small agreement, the base has already decided tomorrow's
pinned quotes**: `Q n (quote (n+1) φ lo hi)` is `1` or `0` according to tomorrow's price, for
every quote small on day `n`. So `PCPσTheory ∧ E1x` is unsatisfiable over any base uncertain
about a small next-day quote — the theory-level trilemma is degenerate, and the stage-level
form (`PCPσLinked`) is the one of record. (A finding about the formulation, not about the
sources.)
Source: this package; mandate K1 (traps)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem theory_coherent_e1x_decides {DP : DeductiveProcess} (F : IntervalFamily DP)
    {atoms : ℕ → Finset ℕ} {P Q : History} (hcoh : PCPσTheory atoms DP P) (hE1 : E1x Q P)
    (n : ℕ) (φ : Sentence) (lo hi : ℚ) (hsmall : F.quote (n + 1) φ lo hi ∈ smallSet n) :
    (lo < F.price (n + 1) φ → F.price (n + 1) φ < hi → Q n (F.quote (n + 1) φ lo hi) = 1) ∧
      ((F.price (n + 1) φ < lo ∨ hi < F.price (n + 1) φ) → Q n (F.quote (n + 1) φ lo hi) = 0) := by
  rw [← hE1 n _ hsmall]
  exact theory_coherent_decides F (hcoh n) (n + 1) φ lo hi
    ((atoms_subset_smallAtoms hsmall).trans Finset.subset_union_left)

end Cleanroom.Bli.BliLinkageB
