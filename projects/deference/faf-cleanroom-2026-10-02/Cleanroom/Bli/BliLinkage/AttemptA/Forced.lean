import Cleanroom.Bli.BliLinkage.AttemptA.Defs

/-!
# `bli-linkage`, attempt A — K1: constraint 4′ is forced by coherence with the quote atoms

Under `PCPσ` (the day-`n` market is a mixture of partition-respecting stage worlds on the algebra
of the day-`n` small sentences and the day-`(n+1)` linked state sentences) and `E5σ` (partition:
mass one, pairwise exclusive), the day-`n` price of a pinned coordinate's cell literal **is** the
superbelief's marginal on that coordinate and cell: `P n (lit (n+1) c r) = cellMass … c r`. With
`E1x`, the base's own belief about tomorrow's cell is that marginal — constraint 4′ of
bli-slides-011 is a consequence of coherence, not a desideratum.

The engine is the partition argument of `bli-trajectory`'s `e4_iff_partition_mass` (⇐), isolated
here in σ-parametric form as `weight_mul_stateSum`: in every charged mixture world exactly one
day-`(n+1)` state holds. Linkage then does one step: the held state's conjunct gives the literal at
the state's own index, and the world's partition forbids every other literal of the coordinate
(`holds_lit_iff_of_partitions`).
-/

namespace Cleanroom.Bli.BliLinkage.AttemptA

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliTrajectory

open Classical

variable {DP : DeductiveProcess}

/-! ## The partition argument inside a mixture -/

section Mixture

variable {k : ℕ} (W : Fin k → PCWorld) (w : Fin k → ℝ)
  (σ : ℕ → ℕ → Sentence) (S : StateSystem) (P : History) (n : ℕ)

/-- **In every charged mixture world exactly one day-`(n+1)` state holds**, in the form
`w i * ∑_q payout_i (σ_q) = w i`: with the states' masses and pairwise conjunctions represented
by the mixture, partition mass one and pairwise exclusivity force each charged world to hold
exactly one candidate. This is the (⇐) engine of `bli-trajectory`'s `e4_iff_partition_mass`,
σ-parametric and factored out so that K1, K2, K3 and K4 can all run on it.
Source: bli-soto-a-006 (iii); `bli-trajectory` M4 (`e4_iff_partition_mass`, ⇐ direction)
Kind: P
Fidelity: exact (abstract in `σ`)
Hyps: (a) -/
theorem weight_mul_stateSum (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hrepσ : ∀ q ∈ S.states (n + 1),
      P n (σ (n + 1) q) = ∑ i, w i * (W i).payout (σ (n + 1) q))
    (hrepσσ : ∀ q ∈ S.states (n + 1), ∀ q' ∈ S.states (n + 1),
      P n (σ (n + 1) q ⋏ σ (n + 1) q') = ∑ i, w i * (W i).payout (σ (n + 1) q ⋏ σ (n + 1) q'))
    (hmass : ∑ q ∈ S.states (n + 1), P n (σ (n + 1) q) = 1)
    (hexcl : ∀ q₁ ∈ S.states (n + 1), ∀ q₂ ∈ S.states (n + 1), q₁ ≠ q₂ →
      P n (σ (n + 1) q₁ ⋏ σ (n + 1) q₂) = 0) :
    ∀ i, w i * ∑ q ∈ S.states (n + 1), (W i).payout (σ (n + 1) q) = w i := by
  set ind : Fin k → ℕ → ℝ := fun i q => (W i).payout (σ (n + 1) q) with hind
  -- each charged world holds at most one day-(n+1) state
  have hSle : ∀ i, 0 < w i → ∑ q ∈ S.states (n + 1), ind i q ≤ 1 := by
    intro i hwi
    have hcard :
        ((S.states (n + 1)).filter (fun q => (W i).Holds (σ (n + 1) q))).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro q₁ hq₁ q₂ hq₂
      rw [Finset.mem_filter] at hq₁ hq₂
      by_contra hne
      have hex := hexcl q₁ hq₁.1 q₂ hq₂.1 hne
      rw [hrepσσ q₁ hq₁.1 q₂ hq₂.1] at hex
      have hterm : 0 < w i * (W i).payout (σ (n + 1) q₁ ⋏ σ (n + 1) q₂) := by
        rw [payout_and]
        unfold PCWorld.payout
        rw [if_pos hq₁.2, if_pos hq₂.2]
        linarith
      have hnn : ∀ j ∈ (Finset.univ : Finset (Fin k)),
          0 ≤ w j * (W j).payout (σ (n + 1) q₁ ⋏ σ (n + 1) q₂) :=
        fun j _ => mul_nonneg (hw j) (payout_mem_Icc _ _).1
      have := Finset.single_le_sum
        (f := fun j => w j * (W j).payout (σ (n + 1) q₁ ⋏ σ (n + 1) q₂)) hnn (Finset.mem_univ i)
      linarith
    have hsumcard : ∑ q ∈ S.states (n + 1), ind i q =
        (((S.states (n + 1)).filter (fun q => (W i).Holds (σ (n + 1) q))).card : ℝ) := by
      simp only [hind, PCWorld.payout]
      rw [Finset.sum_boole]
    rw [hsumcard]; exact_mod_cast hcard
  have hswap : ∑ q ∈ S.states (n + 1), P n (σ (n + 1) q) =
      ∑ i, w i * ∑ q ∈ S.states (n + 1), ind i q := by
    rw [Finset.sum_congr rfl (fun q hq => hrepσ q hq), Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  have hzero : ∀ i, w i * (1 - ∑ q ∈ S.states (n + 1), ind i q) = 0 := by
    have hsum0 : ∑ i, w i * (1 - ∑ q ∈ S.states (n + 1), ind i q) = 0 := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hsum]
      rw [← hswap, hmass, sub_self]
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin k)),
        0 ≤ w i * (1 - ∑ q ∈ S.states (n + 1), ind i q) := by
      intro i _
      rcases (hw i).lt_or_eq with hwi | hwi
      · exact mul_nonneg (hw i) (by linarith [hSle i hwi])
      · rw [← hwi, zero_mul]
    exact fun i => (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 i (Finset.mem_univ i)
  intro i
  have := hzero i
  rw [mul_sub, mul_one, sub_eq_zero] at this
  exact this.symm

/-- **Total probability inside each charged world**: `w i * payout_i φ = w i * ∑_q payout_i φ ·
payout_i σ_q`.
Source: none: infrastructure (from `weight_mul_stateSum`)
Kind: L
Fidelity: n/a -/
lemma weight_mul_payout_eq_sum (key : ∀ i, w i * ∑ q ∈ S.states (n + 1), (W i).payout (σ (n + 1) q) = w i)
    (i : Fin k) (φ : Sentence) :
    w i * (W i).payout φ =
      w i * ∑ q ∈ S.states (n + 1), (W i).payout φ * (W i).payout (σ (n + 1) q) := by
  calc w i * (W i).payout φ
      = (w i * ∑ q ∈ S.states (n + 1), (W i).payout (σ (n + 1) q)) * (W i).payout φ := by
          rw [key i]
    _ = w i * ∑ q ∈ S.states (n + 1), (W i).payout φ * (W i).payout (σ (n + 1) q) := by
          rw [mul_assoc, Finset.sum_mul]
          congr 1
          exact Finset.sum_congr rfl fun q _ => mul_comm _ _

/-- **Total probability of the mixture**: `P n φ = ∑_q P n (φ ⋏ σ_q)` whenever `φ` and the
conjunctions are represented.
Source: bli-soto-a-006 (iii); `bli-trajectory` M4
Kind: L
Fidelity: n/a -/
lemma mixture_total_probability
    (key : ∀ i, w i * ∑ q ∈ S.states (n + 1), (W i).payout (σ (n + 1) q) = w i)
    {φ : Sentence} (hrepφ : P n φ = ∑ i, w i * (W i).payout φ)
    (hrepand : ∀ q ∈ S.states (n + 1),
      P n (φ ⋏ σ (n + 1) q) = ∑ i, w i * (W i).payout (φ ⋏ σ (n + 1) q)) :
    P n φ = ∑ q ∈ S.states (n + 1), P n (φ ⋏ σ (n + 1) q) := by
  calc P n φ = ∑ i, w i * (W i).payout φ := hrepφ
    _ = ∑ i, w i * ∑ q ∈ S.states (n + 1), (W i).payout φ * (W i).payout (σ (n + 1) q) :=
        Finset.sum_congr rfl fun i _ => weight_mul_payout_eq_sum W w σ S n key i φ
    _ = ∑ q ∈ S.states (n + 1), ∑ i, w i * ((W i).payout φ * (W i).payout (σ (n + 1) q)) := by
        simp only [Finset.mul_sum]; exact Finset.sum_comm
    _ = ∑ q ∈ S.states (n + 1), P n (φ ⋏ σ (n + 1) q) :=
        Finset.sum_congr rfl fun q hq => by rw [hrepand q hq]; simp only [payout_and]

end Mixture

/-! ## The per-world linkage step -/

/-- **In a partition-respecting world, the literal's payout times a state's payout is the
state's payout if the state places the coordinate in that cell, and `0` otherwise.** This is
the one step linkage adds to the partition argument.
Source: mandate § K1 ("that state's conjunct gives the literal with the state's own index, and
`C.excl` forbids any other literal")
Kind: L
Fidelity: n/a -/
lemma payout_lit_mul_payout_state (C : CellFamily DP) {n q c r r₀ : ℕ} {v : PCWorld}
    (hpart : C.Partitions (n + 1) v) (he : entryOf c (tableOfCode q) = some r₀) :
    v.payout (C.cellLit (n + 1) c r) * v.payout (stateOf C (n + 1) q) =
      if entryOf c (tableOfCode q) = some r then v.payout (stateOf C (n + 1) q) else 0 := by
  rw [he]
  by_cases hσ : v.Holds (stateOf C (n + 1) q)
  · have hiff : v.Holds (C.cellLit (n + 1) c r) ↔ r = r₀ :=
      holds_lit_iff_of_partitions hpart hσ he
    unfold PCWorld.payout
    rw [if_pos hσ]
    by_cases hr : r = r₀
    · subst hr; rw [if_pos (hiff.2 rfl), if_pos rfl]; ring
    · rw [if_neg (fun h => hr (hiff.1 h)), if_neg (fun h => hr (Option.some.inj h).symm)]; ring
  · unfold PCWorld.payout
    rw [if_neg hσ]
    split_ifs <;> ring

/-! ## K1 -/

/-- **K1, one day — constraint 4′ is forced**: on a day `n` where `P n` is a mixture of
partition-respecting stage worlds on an algebra containing the day-`n` small sentences and the
day-`(n+1)` linked states, with partition mass one and pairwise exclusivity, the price of a
pinned coordinate's cell literal is the superbelief's marginal on that coordinate and cell.
Scope: `c ∈ pinned C index n` (all of `c`'s literals small on day `n`, so in the algebra),
`r ∈ C.cells (n+1)`; the system is `Tabular` (every candidate lists `c`).
Source: [[bli-program]] §3.6(i); desiderata P5e; bli-slides-010/011; bli-soto-a-007; mandate § K1
Kind: P
Fidelity: exact (cell literals; angle B proves the interval bracket instead)
Hyps: (a) coherence, partition and `Tabular` are explicit hypotheses in the definitions of record -/
theorem forced_marginal_at (C : CellFamily DP) (index : ℕ → List ℕ) (S : StateSystem)
    (P : History) (hT : Tabular C index S) (n : ℕ) (D : Finset Sentence) (A : Finset ℕ)
    (hcoh : CoherentOnCell C D (n + 1) A (P n)) (hAsmall : smallAtoms n ⊆ A)
    (hAstate : ∀ q ∈ S.states (n + 1), sentenceAtomCodes (stateOf C (n + 1) q) ⊆ A)
    (hmass : ∑ q ∈ S.states (n + 1), P n (stateOf C (n + 1) q) = 1)
    (hexcl : ∀ q₁ ∈ S.states (n + 1), ∀ q₂ ∈ S.states (n + 1), q₁ ≠ q₂ →
      P n (stateOf C (n + 1) q₁ ⋏ stateOf C (n + 1) q₂) = 0)
    {c : ℕ} (hc : c ∈ pinned C index n) {r : ℕ} (hr : r ∈ C.cells (n + 1)) :
    P n (C.cellLit (n + 1) c r) = cellMass (stateOf C) S P n c r := by
  obtain ⟨k, W, w, hW, hw, hsum, hrep⟩ := hcoh
  set σ := stateOf C with hσ
  have hrepσ : ∀ q ∈ S.states (n + 1), P n (σ (n + 1) q) = ∑ i, w i * (W i).payout (σ (n + 1) q) :=
    fun q hq => hrep _ (hAstate q hq)
  have hrepσσ : ∀ q ∈ S.states (n + 1), ∀ q' ∈ S.states (n + 1),
      P n (σ (n + 1) q ⋏ σ (n + 1) q') = ∑ i, w i * (W i).payout (σ (n + 1) q ⋏ σ (n + 1) q') := by
    intro q hq q' hq'
    apply hrep
    rw [sentenceAtomCodes_and]
    exact Finset.union_subset (hAstate q hq) (hAstate q' hq')
  have key := weight_mul_stateSum W w σ S P n hw hsum hrepσ hrepσσ hmass hexcl
  have hlitA : sentenceAtomCodes (C.cellLit (n + 1) c r) ⊆ A :=
    (atoms_subset_smallAtoms (lit_mem_smallSet_of_mem_pinned hc hr)).trans hAsmall
  have hcidx : c ∈ index (n + 1) := (mem_pinned.1 hc).1
  calc P n (C.cellLit (n + 1) c r) = ∑ i, w i * (W i).payout (C.cellLit (n + 1) c r) := hrep _ hlitA
    _ = ∑ i, w i * ∑ q ∈ S.states (n + 1),
          (W i).payout (C.cellLit (n + 1) c r) * (W i).payout (σ (n + 1) q) :=
        Finset.sum_congr rfl fun i _ => weight_mul_payout_eq_sum W w σ S n key i _
    _ = ∑ i, w i * ∑ q ∈ S.states (n + 1),
          (if entryOf c (tableOfCode q) = some r then (W i).payout (σ (n + 1) q) else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        refine Finset.sum_congr rfl fun q hq => ?_
        obtain ⟨r₀, -, he⟩ := hT.keys (n + 1) q hq c hcidx
        exact payout_lit_mul_payout_state C (hW i).2 he
    _ = ∑ q ∈ S.states (n + 1),
          (if entryOf c (tableOfCode q) = some r then ∑ i, w i * (W i).payout (σ (n + 1) q) else 0) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun _ _ => ?_
        split_ifs <;> simp
    _ = ∑ q ∈ S.states (n + 1), (if entryOf c (tableOfCode q) = some r then P n (σ (n + 1) q) else 0) :=
        Finset.sum_congr rfl fun q hq => by rw [hrepσ q hq]
    _ = cellMass σ S P n c r := by
        unfold cellMass
        rw [Finset.sum_filter]

/-- **K1 — constraint 4′ is forced by coherence with the quote atoms** (`PCPσ ∧ E5σ`): on
every day `n`, for every pinned coordinate `c` and every cell `r`,
`P n (lit (n+1) c r) = cellMass (stateOf C) S P n c r`.
Source: [[bli-program]] §3.6(i); desiderata P5e; bli-slides-010/011; bli-soto-a-007; mandate § K1
Kind: C
Fidelity: exact (cell literals, pinned coordinates)
Hyps: (a) -/
theorem forced_marginal (C : CellFamily DP) (index : ℕ → List ℕ) (S : StateSystem) (P : History)
    (hT : Tabular C index S) (hcoh : PCPσ C (stateOf C) S P) (hE5 : E5σ (stateOf C) S P)
    (n : ℕ) {c : ℕ} (hc : c ∈ pinned C index n) {r : ℕ} (hr : r ∈ C.cells (n + 1)) :
    P n (C.cellLit (n + 1) c r) = cellMass (stateOf C) S P n c r :=
  forced_marginal_at C index S P hT n (DP.D n) _ (hcoh n) Finset.subset_union_left
    (fun _ hq => (atoms_subset_stateAtomsσ hq).trans Finset.subset_union_right)
    (hE5 n).1 (hE5 n).2 hc hr

/-- **K1 for the base (constraint 4′)**: with `E1x`, the base's small belief about tomorrow's
cell of a pinned coordinate is the superbelief's marginal: `Q n (lit (n+1) c r) = cellMass …`.
Source: bli-slides-011 (constraint 4′); [[bli-program]] §3.6(i); mandate § K1
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem forced_marginal_base (C : CellFamily DP) (index : ℕ → List ℕ) (S : StateSystem)
    (Q P : History) (hT : Tabular C index S) (hcoh : PCPσ C (stateOf C) S P)
    (hE5 : E5σ (stateOf C) S P) (hE1 : E1x Q P) (n : ℕ) {c : ℕ} (hc : c ∈ pinned C index n)
    {r : ℕ} (hr : r ∈ C.cells (n + 1)) :
    Q n (C.cellLit (n + 1) c r) = cellMass (stateOf C) S P n c r := by
  rw [← hE1 n _ (lit_mem_smallSet_of_mem_pinned hc hr)]
  exact forced_marginal C index S P hT hcoh hE5 n hc hr

/-! ## What completed-theory coherence does -/

/-- **Completed-theory coherence collapses the superbelief**: if a state sentence holds in every
completed-theory world (at B2, the actual next table: `stateSentence_actual_holds`), a market
coherent relative to the completed theory on an algebra containing it gives it mass one. So
`PCPσTheory ∧ E5σ` is the point mass on the realized next state — which is why K1/K2 are
stated at the stage form `PCPσ` and the completed-theory form is reserved for K4.
Source: mandate § K1 ("in every completed-theory world exactly the *actual* table holds, so a
mixture of *theory-consistent* worlds charges one state"); `bli-found` `fixedStates_decided`
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem theory_coherent_point_mass (A : Finset ℕ) (P : History) (n : ℕ) (ψ : Sentence)
    (hcoh : CoherentOnTheory DP A (P n)) (hA : sentenceAtomCodes ψ ⊆ A)
    (hdec : ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds ψ) : P n ψ = 1 := by
  obtain ⟨k, W, w, hW, -, hsum, hrep⟩ := hcoh
  rw [hrep ψ hA]
  calc ∑ i, w i * (W i).payout ψ = ∑ i, w i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold PCWorld.payout
        rw [if_pos (hdec (W i) (hW i)), mul_one]
    _ = 1 := hsum

end Cleanroom.Bli.BliLinkage.AttemptA
