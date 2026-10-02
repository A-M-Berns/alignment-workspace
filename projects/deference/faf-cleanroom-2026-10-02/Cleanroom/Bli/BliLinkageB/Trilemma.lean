import Cleanroom.Bli.BliLinkageB.Witness

/-!
# bli-linkage, angle B — the trilemma's three horns and its sharpness (K2)

Over the witness objects of `Witness.lean`/`Dissolve.lean` — the one-coordinate index
`dIndex = [⌜φ₀⌝]`, two cells, the cell-literal state family `wσ = stateOf wCF`, the four
price-linked worlds and their mixture `wP` — each of the trilemma's three pairwise-consistent
horns is inhabited by a two-state, distinct-table market, the joint inconsistency over a base
violating `D_NNUcell` is `Determination.trilemma_T0`, and the sharpness base (all three plus
`D_NNUcell`) is `wP` itself. The docstrings name the conjunct that fails and where.

* **T1 (drop faith)**: `wP` with the representatives moved off the conditional values
  (`t1CF`: `rep 0 = 0`, `rep 1 = 1/2`, and the system `t1S` valuing at those representatives):
  `PCPσ ∧ E1x ∧ E5σ` hold, `ValuesAtRep` holds, faith fails at `(n, m, q, φ) = (0, 1, dCode 1, φ₀)`
  (`3/8 ≠ 1/2 · 1/2`), and `D_NNUcell t1CF` fails (`1/2 ≠ 0 · 1/2 + 1/2 · 1/2`).
* **T2 (drop coherence)**: `tP`, which is `wP` except that it prices the coordinate `φ₀` at
  `1/4` instead of `1/2`: `E1x ∧ E2xσ ∧ E5σ` hold (faith and partition only read states and
  conjunctions with states, which `tP` leaves untouched), `D_NNUcell wCF` fails
  (`1/4 ≠ 1/4 · 1/2 + 3/4 · 1/2`), and coherence fails — proved from the determination theorem
  itself: a coherent `tP` would satisfy `D_NNUcell`. This is *not* the mandate's "define `P` by
  cases" recipe: with `P := Q` forced by `E1x` on small sentences, dropping coherence frees
  nothing on the eventually-small faith sentences, so the base itself must carry faith and
  partition (FB-15).
* **T3 (drop agreement)**: `wP` as superbelief over the base `dP` (the dissolution market,
  which violates `D_NNUcell wCF`): `PCPσ ∧ E2xσ ∧ E5σ` hold and `E1x dP wP` fails on the pinned
  literal `lit_{n+1, φ₀, 0}` (`1/2 ≠ 0`) from the day it is small.
* **T0** at the witness base: no `P` satisfies the full package over `dP` (`trilemma_T0`).
* **Sharpness**: `wP` satisfies all three and `D_NNUcell wCF` (`determination_package_inhabited`).
  It is a four-world mixture, not an inductor; the mandate's trajectory-law base from
  `bli-finite`'s `tentSkeleton` was not built (handoff).
-/

namespace Cleanroom.Bli.BliLinkageB

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

namespace Trilemma

open Dissolve Witness

/-! ## T1 — drop faith -/

/-- Representatives off the conditional values: `0` for cell `0`, `1/2` for cell `1`.
Source: mandate K2 (T1: "representatives chosen so the identity fails")
Kind: D
Fidelity: n/a -/
def rep1 (_m r : ℕ) : ℚ := if r = 0 then 0 else 1 / 2

/-- The witness cell family with the representatives `rep1` (same literals and cells as `wCF`).
Source: mandate K2 (T1)
Kind: D
Fidelity: n/a -/
noncomputable def t1CF :
    CellFamily (fun v => ∃ (x : ℚ) (b : Bool) (a : ℕ), a ≤ 1 ∧ v = wld x b a) :=
  { wCF with rep := rep1 }

/-- `t1CF.literal`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma t1CF_literal : t1CF.literal = dLit := rfl

/-- `t1CF.cells`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma t1CF_cells : t1CF.cells = dCells := rfl

/-- `t1CF.rep`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma t1CF_rep : t1CF.rep = rep1 := rfl

/-- The T1 values: each candidate values every sentence at its cell's `rep1`.
Source: mandate K2 (T1)
Kind: D
Fidelity: n/a -/
noncomputable def t1Val (_m q : ℕ) (_φ : Sentence) : ℝ := if q = dCode 0 then 0 else 1 / 2

/-- The T1 state system: the two witness candidates, values `t1Val`.
Source: mandate K2 (T1)
Kind: D
Fidelity: n/a -/
noncomputable def t1S : StateSystem where
  states := dStates
  val := t1Val
  actual _ := dCode 1
  actual_mem _ := by simp [dStates]

/-- `t1S.states`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma t1S_states : t1S.states = dStates := rfl

/-- `t1S.val`.
Source: none: witness
Kind: L
Fidelity: n/a -/
@[simp] lemma t1S_val : t1S.val = t1Val := rfl

/-- The T1 state family is the witness's (`t1CF` has `wCF`'s literals).
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma stateOf_t1CF (m q : ℕ) : stateOf t1CF m q = wσ m q := rfl

/-- `E5σ` at `t1S` is `E5σ` at `wS` (same states).
Source: none: witness
Kind: L
Fidelity: n/a -/
theorem t1E5σ : E5σ wσ t1S wP := by
  have h := wE5σ
  unfold E5σ at h ⊢
  simpa only [t1S_states, wS_states] using h

/-- `ValuesAtRep` holds for `t1CF`/`t1S`: each candidate values `φ₀` at `rep1` of its cell.
Source: mandate K2 (`hval`)
Kind: L
Fidelity: n/a -/
theorem t1ValuesAtRep (n : ℕ) : ValuesAtRep t1CF t1S dIndex n := by
  intro q hq c hc
  simp only [dIndex, List.mem_singleton] at hc
  subst hc
  rw [t1S_states, mem_dStates] at hq
  rcases hq with rfl | rfl
  · refine ⟨0, by simp [dCells], by simp [entryOf], ?_⟩
    norm_num [t1Val, rep1]
  · refine ⟨1, by simp [dCells], by simp [entryOf], ?_⟩
    norm_num [t1Val, rep1, dCode_zero_ne_one.symm]

/-- **Faith fails for T1** at `(n, m, q, φ) = (0, 1, dCode 1, φ₀)`: `wP 0 (φ₀ ⋏ σ_1) = 3/8` but
`t1Val · wP 0 σ_1 = 1/2 · 1/2`.
Source: mandate K2 (T1: "names which conjunct fails and at which `(n, φ, r)`")
Kind: L
Fidelity: n/a -/
theorem t1_not_e2xσ : ¬ E2xσ wσ t1S wP := by
  intro h
  have h01 : (0 : ℕ) ≠ 1 := by norm_num
  have := h 0 1 (by norm_num) (dCode 1) (by simp [dStates]) dPhi (dPhi_mem_Sminus le_rfl)
  rw [t1S_val, wP_eq, wP_eq] at this
  simp only [payout_and, payout_wσ_self, payout_wσ_ne _ _ h01.symm, payout_dPhi_true,
    payout_dPhi_false, t1Val, dCode_zero_ne_one.symm, if_false] at this
  norm_num at this

/-- **`D_NNUcell t1CF` fails for `wP`**: `1/2 ≠ 0 · 1/2 + 1/2 · 1/2`.
Source: mandate K2 (T1)
Kind: L
Fidelity: n/a -/
theorem t1_not_d_nnucell : ¬ D_NNUcell t1CF dIndex wP := by
  intro h
  obtain ⟨N, hN⟩ := wPinned_eventually
  have := h N dC0 (hN N le_rfl)
  rw [sentenceOfCode_dC0, wP_dPhi, t1CF_cells, dCells, t1CF_literal, t1CF_rep,
    Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1), (wP_dLit N (N + 1) dPhi).1,
    (wP_dLit N (N + 1) dPhi).2] at this
  norm_num [rep1] at this

/-- **Trilemma, horn T1 (drop faith), inhabited (N+)**: the witness mixture `wP` over the
representatives `rep1` satisfies `PCPσ ∧ E1x ∧ E5σ` with values at the representatives, two
candidates of distinct tables each of mass `1/2`, violates `D_NNUcell t1CF`, and faith fails at
`(0, 1, dCode 1, φ₀)`.
Source: [[bli-program]] §3.6(ii) (the linkage trilemma); mandate K2 (T1)
Kind: N+
Fidelity: exact (a world-mixture base violating `D_NNUcell` through its representatives)
Hyps: (a) -/
theorem trilemma_T1 (atoms : ℕ → Finset ℕ) :
    PCPσ atoms dDP wP ∧ E1x wP wP ∧ E5σ wσ t1S wP ∧ (∀ n, ValuesAtRep t1CF t1S dIndex n) ∧
      ¬ E2xσ wσ t1S wP ∧ ¬ D_NNUcell t1CF dIndex wP ∧
      (∀ n, wP n (wσ (n + 1) (dCode 0)) = 1 / 2 ∧ wP n (wσ (n + 1) (dCode 1)) = 1 / 2) :=
  ⟨wPCPσ atoms, wE1x, t1E5σ, t1ValuesAtRep, t1_not_e2xσ, t1_not_d_nnucell,
    fun n => wP_state n (n + 1)⟩

/-! ## T2 — drop coherence -/

/-- **The T2 market**: `wP` with the coordinate `φ₀` repriced at `1/4`.
Source: mandate K2 (T2; the shape differs from the mandate's, FB-15)
Kind: D
Fidelity: variant: `wP` with one small price moved, in place of the mandate's case-defined market (which `E1x` forbids, FB-15) -/
noncomputable def tP : History := fun n ψ => if ψ = dPhi then 1 / 4 else wP n ψ

/-- `tP` at the coordinate.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma tP_dPhi (n : ℕ) : tP n dPhi = 1 / 4 := by simp [tP]

/-- `tP` elsewhere is `wP`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma tP_of_ne {n : ℕ} {ψ : Sentence} (h : ψ ≠ dPhi) : tP n ψ = wP n ψ := by simp [tP, h]

/-- A conjunction is not the atom `φ₀`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma and_ne_dPhi (φ ψ : Sentence) : φ ⋏ ψ ≠ dPhi := by simp [dPhi]

/-- A candidate's state sentence is not the atom `φ₀`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wσ_ne_dPhi (m q : ℕ) (hq : q = dCode 0 ∨ q = dCode 1) : wσ m q ≠ dPhi := by
  rcases hq with rfl | rfl <;> rw [wσ_dCode] <;> exact and_ne_dPhi _ _

/-- A literal is not the atom `φ₀` (its index is nonzero).
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma dLit_ne_dPhi (m : ℕ) (φ : Sentence) (r : ℕ) : dLit m φ r ≠ dPhi := by
  intro h
  exact lIdx_ne_zero m (Encodable.encode φ) r (by simpa [dLit, dPhi] using h)

/-- `E1x` for `tP` as its own base.
Source: none: witness
Kind: L
Fidelity: n/a -/
theorem tE1x : E1x tP tP := fun _ _ _ => rfl

/-- `E5σ` holds for `tP`: it agrees with `wP` on states and their conjunctions.
Source: mandate K2 (T2)
Kind: L
Fidelity: n/a -/
theorem tE5σ : E5σ wσ wS tP := by
  intro n
  obtain ⟨h1, h2⟩ := wE5σ n
  refine ⟨?_, fun q₁ hq₁ q₂ hq₂ hne => ?_⟩
  · rw [← h1]
    exact Finset.sum_congr rfl fun q hq =>
      tP_of_ne (wσ_ne_dPhi _ _ ((mem_dStates (m := n + 1)).1 hq))
  · rw [tP_of_ne (and_ne_dPhi _ _)]
    exact h2 q₁ hq₁ q₂ hq₂ hne

/-- `E2xσ` holds for `tP`: faith reads only conjunctions with states and the states.
Source: mandate K2 (T2)
Kind: L
Fidelity: n/a -/
theorem tE2xσ : E2xσ wσ wS tP := by
  intro n m hnm q hq φ hφ
  rw [tP_of_ne (and_ne_dPhi _ _), tP_of_ne (wσ_ne_dPhi _ _ ((mem_dStates (m := m)).1 hq))]
  exact wE2xσ n m hnm q hq φ hφ

/-- **`D_NNUcell wCF` fails for `tP`**: `1/4 ≠ 1/4 · 1/2 + 3/4 · 1/2`.
Source: mandate K2 (T2)
Kind: L
Fidelity: n/a -/
theorem tNot_d_nnucell : ¬ D_NNUcell wCF dIndex tP := by
  intro h
  obtain ⟨N, hN⟩ := wPinned_eventually
  have := h N dC0 (hN N le_rfl)
  rw [sentenceOfCode_dC0, tP_dPhi, wCF_cells, dCells, wCF_literal, wCF_rep,
    Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1), tP_of_ne (dLit_ne_dPhi _ _ _),
    tP_of_ne (dLit_ne_dPhi _ _ _), (wP_dLit N (N + 1) dPhi).1, (wP_dLit N (N + 1) dPhi).2] at this
  norm_num [dRep] at this

/-- **Coherence fails for `tP`** (on any atom set containing the state atoms): a coherent `tP`
would, with `E1x ∧ E2xσ ∧ E5σ`, satisfy `D_NNUcell wCF` by the determination theorem.
Source: mandate K2 (T2: "say in the docstring it is not coherent and why")
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem tNot_PCPσ (atoms : ℕ → Finset ℕ) (hatoms : ∀ n, stateAtoms wσ wS n ⊆ atoms n) :
    ¬ PCPσ atoms dDP tP := fun hcoh =>
  tNot_d_nnucell (d_nnucell_of_package wCF hcoh hatoms tE5σ tE1x tE2xσ wSpuriousEntails
    wValuesAtRep wScope)

/-- **Trilemma, horn T2 (drop coherence), inhabited (N+)**: `tP` satisfies `E1x ∧ E2xσ ∧ E5σ`
with two candidates of distinct tables each of mass `1/2`, violates `D_NNUcell wCF`, and is not
coherent on any atom set containing the state atoms.
Source: [[bli-program]] §3.6(ii); mandate K2 (T2)
Kind: N+
Fidelity: variant: `wP` with one small price moved (FB-15: the mandate's case-defined market violates `E1x` once the faith sentences are small)
Hyps: (a) -/
theorem trilemma_T2 :
    E1x tP tP ∧ E2xσ wσ wS tP ∧ E5σ wσ wS tP ∧
      (∀ atoms, (∀ n, stateAtoms wσ wS n ⊆ atoms n) → ¬ PCPσ atoms dDP tP) ∧
      ¬ D_NNUcell wCF dIndex tP ∧
      (∀ n, tP n (wσ (n + 1) (dCode 0)) = 1 / 2 ∧ tP n (wσ (n + 1) (dCode 1)) = 1 / 2) :=
  ⟨tE1x, tE2xσ, tE5σ, tNot_PCPσ, tNot_d_nnucell, fun n => by
    rw [tP_of_ne (wσ_ne_dPhi _ _ (Or.inl rfl)), tP_of_ne (wσ_ne_dPhi _ _ (Or.inr rfl))]
    exact wP_state n (n + 1)⟩

/-! ## T3 — drop agreement -/

/-- **`E1x dP wP` fails** on the pinned literal `lit_{n+1, φ₀, 0}` once it is small:
`wP n lit = 1/2`, `dP n lit = 0`.
Source: mandate K2 (T3: "`P` disagrees with `Q` on the pinned quote atoms")
Kind: L
Fidelity: n/a -/
theorem dNot_E1x_wP : ¬ E1x dP wP := by
  intro h
  obtain ⟨N, hN⟩ := dLit_eventually_small 0
  have := h N (dLit (N + 1) dPhi 0) (by rw [mem_smallSet]; exact hN N le_rfl)
  rw [(wP_dLit N (N + 1) dPhi).1, (dP_dLit N (N + 1) dPhi).1] at this
  norm_num at this

/-- The dissolution base violates `D_NNUcell` at `wCF` (same literals, cells and representatives
as `dCF`).
Source: `Dissolve.dNot_D_NNUcell`
Kind: L
Fidelity: n/a -/
theorem dNot_d_nnucell_wCF : ¬ D_NNUcell wCF dIndex dP := dNot_D_NNUcell

/-- **Trilemma, horn T3 (drop agreement), inhabited (N+)**: over the base `dP` (which violates
`D_NNUcell wCF`), the superbelief `wP` satisfies `PCPσ ∧ E2xσ ∧ E5σ` with two candidates of
distinct tables each of mass `1/2`, and disagrees with the base on the pinned literal
`lit_{n+1, φ₀, 0}` (`1/2 ≠ 0`) from the day it is small.
Source: [[bli-program]] §3.6(ii); mandate K2 (T3)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem trilemma_T3 (atoms : ℕ → Finset ℕ) :
    PCPσ atoms dDP wP ∧ E2xσ wσ wS wP ∧ E5σ wσ wS wP ∧ ¬ E1x dP wP ∧
      ¬ D_NNUcell wCF dIndex dP ∧
      (∀ n, wP n (wσ (n + 1) (dCode 0)) = 1 / 2 ∧ wP n (wσ (n + 1) (dCode 1)) = 1 / 2) :=
  ⟨wPCPσ atoms, wE2xσ, wE5σ, dNot_E1x_wP, dNot_d_nnucell_wCF, fun n => wP_state n (n + 1)⟩

/-! ## T0 at the witness base, and sharpness -/

/-- **Trilemma, horn T0 at the witness base**: over `dP` no superbelief satisfies the full
package at `(wCF, wS, dIndex)`.
Source: [[bli-program]] §3.6(ii); mandate K2 (T0); `Determination.trilemma_T0`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem trilemma_T0_witness (atoms : ℕ → Finset ℕ) (hatoms : ∀ n, stateAtoms wσ wS n ⊆ atoms n)
    (P : History) :
    ¬ (PCPσ atoms dDP P ∧ E1x dP P ∧ E2xσ wσ wS P ∧ E5σ wσ wS P) :=
  trilemma_T0 wCF dNot_d_nnucell_wCF wSpuriousEntails wValuesAtRep wScope hatoms

/-- **Sharpness**: all three constraints and `D_NNUcell wCF` hold together for `wP` — the
trilemma's three horns are each necessary. The base is a four-world mixture (a non-inductor;
disclosed); the mandate's trajectory-law base was not built.
Source: [[bli-program-desiderata]] I6; mandate K2 (sharpness)
Kind: N+
Fidelity: variant: a world-mixture base in place of the mandate's `tentSkeleton` trajectory law
Hyps: (a) -/
theorem trilemma_sharp (atoms : ℕ → Finset ℕ) :
    PCPσ atoms dDP wP ∧ E1x wP wP ∧ E2xσ wσ wS wP ∧ E5σ wσ wS wP ∧ D_NNUcell wCF dIndex wP ∧
      (∀ n, wP n (wσ (n + 1) (dCode 0)) = 1 / 2 ∧ wP n (wσ (n + 1) (dCode 1)) = 1 / 2) :=
  ⟨wPCPσ atoms, wE1x, wE2xσ, wE5σ,
    d_nnucell_of_package wCF (wPCPσ _) (fun _ => subset_rfl) wE5σ wE1x wE2xσ wSpuriousEntails
      wValuesAtRep wScope,
    fun n => wP_state n (n + 1)⟩

/-! ## FB-15 — "drop coherence" is not a free horn: `E1x` transfers faith to the base -/

/-- **Faith transfers to the base through small agreement**: under `E1x Q P ∧ E2xσ σ S P`, at
any `(n, m, q, φ)` where both the faith conjunction and the state sentence are day-`n` small,
the *base* satisfies the faith identity. So on eventually-small state sentences the "drop
coherence" horn constrains `Q`, not `P` (FB-15).
Source: this package (FB-15); mandate K2 (T2)
Kind: L
Fidelity: n/a -/
theorem faith_transfers_to_base {σ : ℕ → ℕ → Sentence} {S : StateSystem} {P Q : History}
    (hE1 : E1x Q P) (hE2 : E2xσ σ S P) {n m q : ℕ} (hnm : n < m) (hq : q ∈ S.states m)
    {φ : Sentence} (hφ : φ ∈ Sminus m m) (h1 : (φ ⋏ σ m q) ∈ smallSet n)
    (h2 : σ m q ∈ smallSet n) :
    Q n (φ ⋏ σ m q) = S.val m q φ * Q n (σ m q) := by
  rw [← hE1 n _ h1, ← hE1 n _ h2]
  exact hE2 n m hnm q hq φ hφ

/-- The literal family at the coordinate is machine-metered (as in `Dissolve.dLit_eventually_small`).
Source: bli-leak `machineSentenceCodes_atom_of_machineDigits` (re-proved inline)
Kind: L
Fidelity: n/a -/
theorem dLit_machineSentenceCodes (r : ℕ) : MachineSentenceCodes fun n => dLit (n + 1) dPhi r := by
  have hd : MachineDigits fun n => lIdx (n + 1) dC0 r :=
    (MachineDigits.natPair (MachineDigits.const (cleanroomBaseTag + litFam))
      (MachineDigits.natPair ((MachineDigits.ofUnaryRuler UnaryRuler.id).add (MachineDigits.const 1))
        (MachineDigits.const (Nat.pair dC0 r)))).of_eq (fun _ => rfl)
  exact MachineSentenceCodes.ofCanonical
    (MachineTokenStream.of_eq (hd.add (MachineDigits.const 5)) (fun _ => rfl))

/-- The literal state sentence of `dCode r` at `dCF` (as `wσ_dCode`).
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma stateOf_dCF_dCode (m r : ℕ) : stateOf dCF m (dCode r) = dLit m dPhi r ⋏ ⊤ := by
  simp [stateOf, conjList]

/-- **No "drop coherence" horn over the dissolution base**: no `P` satisfies `E1x dP P ∧ E2xσ`
at the literal state family `stateOf dCF` — once the faith sentences `φ₀ ⋏ σ_{n+1, dCode 1}`
and `σ_{n+1, dCode 1}` are small, `E1x` pins them to `dP`, which violates faith there
(`1/2 ≠ 3/4 · 1`). The mandate's T2 recipe ("define `P` by cases") therefore cannot be run over
a base that does not itself satisfy faith on its small sentences (FB-15).
Source: this package (FB-15); mandate K2 (T2)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem no_T2_over_dP (P : History) : ¬ (E1x dP P ∧ E2xσ (stateOf dCF) dS P) := by
  rintro ⟨hE1, hE2⟩
  have hσ : MachineSentenceCodes fun n => dLit (n + 1) dPhi 1 ⋏ ⊤ :=
    (dLit_machineSentenceCodes 1).and (MachineSentenceCodes.const ⊤)
  have hφσ : MachineSentenceCodes fun n => dPhi ⋏ (dLit (n + 1) dPhi 1 ⋏ ⊤) :=
    (MachineSentenceCodes.const dPhi).and hσ
  obtain ⟨N₁, hN₁⟩ := machineSentenceCodes_eventually_small hσ
  obtain ⟨N₂, hN₂⟩ := machineSentenceCodes_eventually_small hφσ
  set n := max N₁ N₂ with hn
  have h := faith_transfers_to_base hE1 hE2 (Nat.lt_succ_self n) (q := dCode 1)
    (by simp [dStates]) (dPhi_mem_Sminus (by omega))
    (by rw [stateOf_dCF_dCode, mem_smallSet]; exact hN₂ n (le_max_right _ _))
    (by rw [stateOf_dCF_dCode, mem_smallSet]; exact hN₁ n (le_max_left _ _))
  have htop : ∀ v : PCWorld, v.payout ⊤ = 1 := fun v => payout_of_holds (PCWorld.holds_top v)
  rw [stateOf_dCF_dCode, dS_val, (dVal_dPhi _).2, dP_eq, dP_eq] at h
  simp only [payout_and, payout_dPhi_true, payout_dPhi_false, payout_dLit_self, htop] at h
  norm_num at h

end Trilemma

end Cleanroom.Bli.BliLinkageB
