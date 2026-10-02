import Cleanroom.Bli.BliLinkage.AttemptA.Forced

/-!
# `bli-linkage`, attempt A — K2: the linked determination theorem and the trilemma's
contrapositive

`PCPσ ∧ E5σ ∧ E1x Q P ∧ E2xσIdx (stateOf C) index S P` (faith on the written-out coordinates; `E2xσ` implies it) determines, on every pinned coordinate `c` of
every day `n` (with `sentenceOfCode c` in `smallSet n` and in `Sminus (n+1) (n+1)`):

* (a) the marginals: `Q n (lit (n+1) c r) = cellMass … c r` (K1, `Forced.lean`);
* (b) the balance: `Q n φ = ∑_q P n σ_q · S.val (n+1) q φ` — `E4σ` at `φ`, derived from `E2xσ`
  summed over the partition inside each charged world (`balance_at`);
* (c) hence `D_NNUcell` at `(n, c)`: `Q n φ = ∑_r rep r · Q n (lit (n+1) c r)` — the sum over
  states factors through the cells because a `Tabular` system's value at a listed coordinate is
  the representative of its cell (`nnu_at`, `determination`).

So a linked BLI over `Q` exists only if `Q` satisfies **exact, finite-time no-net-expected-update**
on the pinned coordinates — the first horn of the linkage trilemma (`trilemma_contrapositive`,
Kind C: the contrapositive of `determination`, not a theorem of its own).

Scope clauses copied from the mandate: `c ∈ pinned C index n`; `sentenceOfCode c ∈ smallSet n`
(so `E1x` applies to it) and `∈ Sminus (n+1) (n+1)` (so `E2xσ` applies; `Sminus` is `bli-found`'s
definition of record and under-approximates the prose scope, F-14 — a disclosed `(c)` inherited
through the faith predicate, not a hypothesis of this file's own).
-/

namespace Cleanroom.Bli.BliLinkage.AttemptA

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliTrajectory

open Classical

variable {DP : DeductiveProcess}

/-- **K2(b), one day — the balance at a small, faith-scoped sentence**: in a partition-respecting
mixture with mass one and exclusivity, constraint 2 at `(n, n+1)` on `φ` summed over the states
gives constraint 4 at `φ`: `P n φ = ∑_q P n σ_q · S.val (n+1) q φ`. Needs `φ ∈ smallSet n` (its
atoms are in the algebra) and `φ ∈ Sminus (n+1) (n+1)` (faith's scope).
Source: [[bli-program]] §3.6(ii); bli-found F-11; mandate § K2 (b)
Kind: C
Fidelity: exact (abstract; the faith scope is `Sminus (n+1) (n+1)`, a disclosed `(c)` of bli-found F-14)
Hyps: (a) -/
theorem balance_at (C : CellFamily DP) (S : StateSystem) (P : History) (n : ℕ)
    (D : Finset Sentence) (A : Finset ℕ) (hcoh : CoherentOnCell C D (n + 1) A (P n))
    (hAsmall : smallAtoms n ⊆ A)
    (hAstate : ∀ q ∈ S.states (n + 1), sentenceAtomCodes (stateOf C (n + 1) q) ⊆ A)
    (hmass : ∑ q ∈ S.states (n + 1), P n (stateOf C (n + 1) q) = 1)
    (hexcl : ∀ q₁ ∈ S.states (n + 1), ∀ q₂ ∈ S.states (n + 1), q₁ ≠ q₂ →
      P n (stateOf C (n + 1) q₁ ⋏ stateOf C (n + 1) q₂) = 0)
    {φ : Sentence}
    (hE2 : ∀ q ∈ S.states (n + 1), φ ∈ Sminus (n + 1) (n + 1) →
      P n (φ ⋏ stateOf C (n + 1) q) = S.val (n + 1) q φ * P n (stateOf C (n + 1) q))
    (hφn : φ ∈ smallSet n) (hφS : φ ∈ Sminus (n + 1) (n + 1)) :
    P n φ = ∑ q ∈ S.states (n + 1), P n (stateOf C (n + 1) q) * S.val (n + 1) q φ := by
  obtain ⟨k, W, w, _, hw, hsum, hrep⟩ := hcoh
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
  have hφA : sentenceAtomCodes φ ⊆ A := (atoms_subset_smallAtoms hφn).trans hAsmall
  have htot := mixture_total_probability W w σ S P n key (hrep φ hφA) (fun q hq => by
    apply hrep
    rw [sentenceAtomCodes_and]
    exact Finset.union_subset hφA (hAstate q hq))
  rw [htot]
  exact Finset.sum_congr rfl fun q hq => by rw [hE2 q hq hφS, mul_comm]

/-- **K2(c), one day — exact no-net-update at a pinned coordinate**: with `E1x`, the balance and
K1, `Q n φ = ∑_r rep (n+1) r · Q n (lit (n+1) c r)` for `φ = sentenceOfCode c`, `c` pinned. The
sum over states factors through the cells because the system is `Tabular`: every candidate
lists `c` with a cell in `C.cells (n+1)`, and its value there is the cell's representative.
Source: [[bli-program]] §3.6(ii); desiderata I6; mandate § K2 (c)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem nnu_at (C : CellFamily DP) (index : ℕ → List ℕ) (S : StateSystem) (Q P : History)
    (hT : Tabular C index S) (n : ℕ) (D : Finset Sentence) (A : Finset ℕ)
    (hcoh : CoherentOnCell C D (n + 1) A (P n)) (hAsmall : smallAtoms n ⊆ A)
    (hAstate : ∀ q ∈ S.states (n + 1), sentenceAtomCodes (stateOf C (n + 1) q) ⊆ A)
    (hmass : ∑ q ∈ S.states (n + 1), P n (stateOf C (n + 1) q) = 1)
    (hexcl : ∀ q₁ ∈ S.states (n + 1), ∀ q₂ ∈ S.states (n + 1), q₁ ≠ q₂ →
      P n (stateOf C (n + 1) q₁ ⋏ stateOf C (n + 1) q₂) = 0)
    (hE1 : E1x Q P) {c : ℕ}
    (hE2 : ∀ q ∈ S.states (n + 1), sentenceOfCode c ∈ Sminus (n + 1) (n + 1) →
      P n (sentenceOfCode c ⋏ stateOf C (n + 1) q) =
        S.val (n + 1) q (sentenceOfCode c) * P n (stateOf C (n + 1) q))
    (hc : c ∈ pinned C index n) (hφn : sentenceOfCode c ∈ smallSet n)
    (hφS : sentenceOfCode c ∈ Sminus (n + 1) (n + 1)) :
    Q n (sentenceOfCode c) =
      ∑ r ∈ C.cells (n + 1), (C.rep (n + 1) r : ℝ) * Q n (C.cellLit (n + 1) c r) := by
  set σ := stateOf C with hσ
  have hcidx : c ∈ index (n + 1) := (mem_pinned.1 hc).1
  -- the fiber decomposition over the cells
  have hmaps : ∀ q ∈ S.states (n + 1),
      entryOf c (tableOfCode q) ∈ (C.cells (n + 1)).image some := by
    intro q hq
    obtain ⟨r, hr, he⟩ := hT.keys (n + 1) q hq c hcidx
    rw [he]; exact Finset.mem_image_of_mem _ hr
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun q => P n (σ (n + 1) q) * S.val (n + 1) q (sentenceOfCode c))
  rw [Finset.sum_image (fun _ _ _ _ h => Option.some.inj h)] at hfib
  calc Q n (sentenceOfCode c) = P n (sentenceOfCode c) := (hE1 n _ hφn).symm
    _ = ∑ q ∈ S.states (n + 1), P n (σ (n + 1) q) * S.val (n + 1) q (sentenceOfCode c) :=
        balance_at C S P n D A hcoh hAsmall hAstate hmass hexcl hE2 hφn hφS
    _ = ∑ r ∈ C.cells (n + 1), ∑ q ∈ (S.states (n + 1)).filter
          (fun q => entryOf c (tableOfCode q) = some r),
          P n (σ (n + 1) q) * S.val (n + 1) q (sentenceOfCode c) := hfib.symm
    _ = ∑ r ∈ C.cells (n + 1), (C.rep (n + 1) r : ℝ) * cellMass σ S P n c r := by
        refine Finset.sum_congr rfl fun r _ => ?_
        unfold cellMass
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [Finset.mem_filter] at hq
        rw [hT.val (n + 1) q hq.1 c hcidx r hq.2, mul_comm]
    _ = ∑ r ∈ C.cells (n + 1), (C.rep (n + 1) r : ℝ) * P n (C.cellLit (n + 1) c r) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [forced_marginal_at C index S P hT n D A hcoh hAsmall hAstate hmass hexcl hc hr]
    _ = ∑ r ∈ C.cells (n + 1), (C.rep (n + 1) r : ℝ) * Q n (C.cellLit (n + 1) c r) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [hE1 n _ (lit_mem_smallSet_of_mem_pinned hc hr)]

/-- **K2(b) — the balance `E4σ` on the pinned coordinates**, under the full package.
Source: [[bli-program]] §3.6(ii); mandate § K2 (b)
Kind: C
Fidelity: exact (on the pinned coordinates in the faith scope)
Hyps: (a) -/
theorem determination_balance (C : CellFamily DP) (index : ℕ → List ℕ) (S : StateSystem)
    (Q P : History) (hcoh : PCPσ C (stateOf C) S P) (hE5 : E5σ (stateOf C) S P) (hE1 : E1x Q P)
    (hE2 : E2xσIdx (stateOf C) index S P) (n : ℕ) {c : ℕ} (hc : c ∈ pinned C index n)
    (hφn : sentenceOfCode c ∈ smallSet n) (hφS : sentenceOfCode c ∈ Sminus (n + 1) (n + 1)) :
    ∑ q ∈ S.states (n + 1), P n (stateOf C (n + 1) q) * S.val (n + 1) q (sentenceOfCode c) =
      Q n (sentenceOfCode c) := by
  rw [← hE1 n _ hφn]
  exact (balance_at C S P n (DP.D n) _ (hcoh n) Finset.subset_union_left
    (fun _ hq => (atoms_subset_stateAtomsσ hq).trans Finset.subset_union_right)
    (hE5 n).1 (hE5 n).2
    (fun q hq => hE2 n (n + 1) (Nat.lt_succ_self n) q hq c (mem_pinned.1 hc).1) hφn hφS).symm

/-- **K2 — the linked determination theorem**: `PCPσ ∧ E5σ ∧ E1x Q P ∧ E2xσ (stateOf C) S P`
over a `Tabular` system forces **`D_NNUcell C index Q`** — exact finite-time no-net-expected-update
on every pinned coordinate — provided every pinned coordinate's sentence is small on its day and
in faith's scope `Sminus (n+1) (n+1)` (`hscope`; at B2 over `[⌜⊥⌝, ⌜⊤⌝]` this is
`InstanceB2.scope_witnessIndex`).
Source: [[bli-program]] §3.6(ii); desiderata I6; mandate § K2 ("Theorem (determination)")
Kind: C
Fidelity: exact (cell-literal linkage, pinned coordinates, `Sminus` faith scope)
Hyps: (a); `hscope` is a condition on the index (discharged at B2) -/
theorem determination (C : CellFamily DP) (index : ℕ → List ℕ) (S : StateSystem) (Q P : History)
    (hT : Tabular C index S) (hcoh : PCPσ C (stateOf C) S P) (hE5 : E5σ (stateOf C) S P)
    (hE1 : E1x Q P) (hE2 : E2xσIdx (stateOf C) index S P)
    (hscope : ∀ n, ∀ c ∈ pinned C index n,
      sentenceOfCode c ∈ smallSet n ∧ sentenceOfCode c ∈ Sminus (n + 1) (n + 1)) :
    D_NNUcell C index Q := by
  intro n c hc
  exact nnu_at C index S Q P hT n (DP.D n) _ (hcoh n) Finset.subset_union_left
    (fun _ hq => (atoms_subset_stateAtomsσ hq).trans Finset.subset_union_right)
    (hE5 n).1 (hE5 n).2 hE1
    (fun q hq => hE2 n (n + 1) (Nat.lt_succ_self n) q hq c (mem_pinned.1 hc).1) hc
    (hscope n c hc).1 (hscope n c hc).2

/-- `determination` at `bli-found`'s full faith predicate `E2xσ` (the definition of record's
shape, for the reconciler's diff with angle B): a corollary through `e2xσIdx_of_e2xσ`. Over a
list-table system the hypothesis package of this form is unsatisfiable under coherence
(`B2.e2xσ_unsat_of_unlisted_tautology`); `determination` is the non-vacuous statement.
Source: mandate § K2 ("Theorem (determination)")
Kind: C
Fidelity: exact (as the mandate states it; vacuous over list tables — see the docstring)
Hyps: (a) -/
theorem determination_e2xσ (C : CellFamily DP) (index : ℕ → List ℕ) (S : StateSystem)
    (Q P : History) (hT : Tabular C index S) (hcoh : PCPσ C (stateOf C) S P)
    (hE5 : E5σ (stateOf C) S P) (hE1 : E1x Q P) (hE2 : E2xσ (stateOf C) S P)
    (hscope : ∀ n, ∀ c ∈ pinned C index n,
      sentenceOfCode c ∈ smallSet n ∧ sentenceOfCode c ∈ Sminus (n + 1) (n + 1)) :
    D_NNUcell C index Q :=
  determination C index S Q P hT hcoh hE5 hE1 (e2xσIdx_of_e2xσ index hE2) hscope

/-- **The trilemma, horn (T0)**: over a base violating `D_NNUcell`, no `P` satisfies all of
`PCPσ`, `E1x`, `E2xσ`, `E5σ`. This is the contrapositive of `determination` (Kind C, as the
mandate pre-labels it: not a theorem of its own). The three pairwise-consistency witnesses are
`Trilemma.lean`'s.
Source: [[bli-program]] §3.6(ii) (the linkage trilemma); mandate § K2 ("Trilemma", T0)
Kind: C
Fidelity: exact
Hyps: (a); `hscope` as in `determination` -/
theorem trilemma_contrapositive (C : CellFamily DP) (index : ℕ → List ℕ) (S : StateSystem)
    (Q : History) (hT : Tabular C index S)
    (hscope : ∀ n, ∀ c ∈ pinned C index n,
      sentenceOfCode c ∈ smallSet n ∧ sentenceOfCode c ∈ Sminus (n + 1) (n + 1))
    (hviol : ¬ D_NNUcell C index Q) (P : History) :
    ¬ (PCPσ C (stateOf C) S P ∧ E1x Q P ∧ E2xσIdx (stateOf C) index S P ∧
      E5σ (stateOf C) S P) :=
  fun ⟨hcoh, hE1, hE2, hE5⟩ => hviol (determination C index S Q P hT hcoh hE5 hE1 hE2 hscope)

end Cleanroom.Bli.BliLinkage.AttemptA
