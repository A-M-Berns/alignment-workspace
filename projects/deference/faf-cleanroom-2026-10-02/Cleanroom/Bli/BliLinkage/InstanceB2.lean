import Cleanroom.Bli.BliLinkage.Determination
import Cleanroom.Bli.BliLinkageB.InstanceB2
import Cleanroom.Bli.BliLinkageB.InstanceCells
import Cleanroom.Bli.BliLinkage.AttemptA.InstanceB2

/-!
# `bli-linkage` — the B2 instances at `𝗜𝚺₁`, `halfRound`, the fixed four-table grid (of record)

The construction-facing module: K1/K2 instantiated over FAF's `paperDP 𝗜𝚺₁` at the B2 state
sentence of record (`σB2 = stateSentence 𝗜𝚺₁ halfRound _`), the cell family `fixedCF rep`
(attempt B's `cellFamilyB2` at `halfRound`, cells `{0, 1}`, representatives a parameter) and the
grid `fixedSystemR rep` (`bli-found`'s `fixedSystem` is `rep := witnessRep`); the pinned set
eventually non-empty; K3 at FAF's LIA; and the two refutations that decide **which faith
predicate a B2 instance can carry**.

**The reconciliation finding of this module** (merging A's F-A1/F-A2 with B's FB-4):

1. `bli-found`'s full `E2xσ` is unsatisfiable over the fixed grid, for **every** `rep`, by any
   coherent `P` with partition mass one from day `n = 1` on: the scope `Sminus (n+1) (n+1)`
   contains from `n+1 = 2` the unlisted tautology `⊤ ⋏ ⊤`, valued at the junk `0`
   (`e2xσ_unsat_of_unlisted_tautology`, `fixedSystemR_e2xσ_unsat`; attempt A's F-A1 re-proved
   over the record coherence). So attempt B's `d_nnucell_B2` (restated as `d_nnucell_B2_e2xσ`)
   has an empty hypothesis package at every `rep` — a stronger vacuity than its own flag (FB-4:
   `witnessRep` only). The faith predicate a list-table B2 system can carry is `E2xσIdx`, and
   the B2 determination theorem of record is `determination_B2` over it.
2. Even over `E2xσIdx`, the index `[⌜⊥⌝, ⌜⊤⌝]` admits **at most a point mass**: faith at the
   listed `⊥` (never true) pins every charged candidate's `⊥`-entry to the cell with
   representative `0`, faith at the listed `⊤` (always true) pins its `⊤`-entry to the cell with
   representative `1`; with `witnessRep` no cell has representative `0`, so nothing is charged
   (`fixedSystem_witnessRep_unsat_idx`, A's F-A2 over the record coherence); with the endpoint
   representatives `rep01 = (0, 1)` the only chargeable table is `tbl 0 1`
   (`charged_eq_tbl01`). So the mandate's "N+: `Grid.fixedSystem` with ≥ 2 states charged" is
   impossible on this index — a non-degenerate instance needs an *uncertain* coordinate, which
   is what attempt B's abstract witness uses (`Trilemma.determination_package_inhabited`), and
   neither attempt built it over `paperDP 𝗜𝚺₁`'s stages (the day-`(n+1)` literals would have
   to be shown absent from `D n`). **The B2 instance of record is therefore N− at best.** The
   point mass itself is built in `InstanceB2Point` (repair round 1): it inhabits the package at
   `rep01` whenever the LIA's rounded prices of `⊥`/`⊤` are `0`/`1` on every day `m ≥ 1`, which
   holds from some day on (`tbl01_eventually`) and is not established on the initial segment
   — so the inhabitation is conditional, and the ledger says so.
3. (Repair round 1, audit r1 fidelity B2.) `no_degenerate_linked_bli_LIA` below is K3 at a
   **fixed** coordinate `c`. For a fixed sentence the LIA's price converges, so its `hmove` can
   hold only if the limit is exactly `1/2` (`InstanceK3.hmove_fixed_forces_limit_half`), and at
   the fixed grid's own coordinates `⌜⊥⌝`/`⌜⊤⌝` it is false (`InstanceK3.not_hmove_falsum`/
   `_verum`). The mandate's K3 instance is over a coordinate *family* `χ n`; that form is
   `InstanceK3.no_degenerate_linked_bli_LIA_family`, of which the theorem below is the constant
   case. The OPEN `leakQ_rounded_price_moves` is over a different process and family and
   instantiates neither as stated.
-/

namespace Cleanroom.Bli.BliLinkage

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound
open Cleanroom.Bli.BliLinkageB (fixedCF fixedSystemR σB2 stateOf_fixedCF_eq E5σ_congr
  stateAtoms_congr fixedStates_spuriousEntails fixedSystem_valuesAtRep fixed_scope IsMixture
  PartitionAt coherentOnW_iff partitionAt_of_E5σ)

section Transport

variable {σ σ' : ℕ → ℕ → Sentence} {S : StateSystem} {P : History} {index : ℕ → List ℕ}

/-- `E2xσIdx` depends on `σ` only on the candidates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E2xσIdx_congr (h : ∀ m, ∀ q ∈ S.states m, σ m q = σ' m q) :
    E2xσIdx σ index S P ↔ E2xσIdx σ' index S P := by
  constructor <;> intro H n m hnm q hq c hc hS
  · rw [← h m q hq]; exact H n m hnm q hq c hc hS
  · rw [h m q hq]; exact H n m hnm q hq c hc hS

end Transport

section B2

/-- **K1 at B2**: over `paperDP 𝗜𝚺₁`, `halfRound`, the fixed grid with representatives `rep`,
under `PCPσ ∧ E5σ` at the B2 state sentence: `P n (cellSentence (n+1) ⌜φ_c⌝ r) = cellMass`.
Source: mandate K1 (instance); attempt A `B2.forced_marginal_B2`
Kind: C
Fidelity: exact (stage level)
Hyps: (a) -/
theorem forced_marginal_B2 (rep : ℕ → ℕ → ℚ) {atoms : ℕ → Finset ℕ} {P : History}
    (hatoms : ∀ n, stateAtoms σB2 (fixedSystemR rep) n ⊆ atoms n)
    (hcoh : PCPσ atoms (paperDP 𝗜𝚺₁) P) (hE5 : E5σ σB2 (fixedSystemR rep) P) (n : ℕ) {c : ℕ}
    (hc : c ∈ pinned (fixedCF rep) witnessIndex n) {r : ℕ} (hr : r ∈ (fixedCF rep).cells (n + 1)) :
    P n ((fixedCF rep).literal (n + 1) (sentenceOfCode c) r) = cellMass σB2 (fixedSystemR rep) P n c r := by
  have hσ : ∀ m, ∀ q ∈ (fixedSystemR rep).states m, stateOf (fixedCF rep) m q = σB2 m q :=
    fun m q hq => stateOf_fixedCF_eq rep m hq
  rw [forced_marginal (fixedCF rep) hcoh (fun n => by rw [stateAtoms_congr hσ]; exact hatoms n)
    ((E5σ_congr hσ).2 hE5) n (fixedStates_spuriousEntails rep n) hc hr]
  unfold cellMass
  exact Finset.sum_congr rfl fun q hq => by rw [hσ (n + 1) q (Finset.mem_filter.1 hq).1]

/-- **K2 at B2 (the determination theorem of record, instantiated; judged item 1).** Over
`paperDP 𝗜𝚺₁`, the two-cell rounding and the fixed four-table grid over `[⌜⊥⌝, ⌜⊤⌝]` with
representatives `rep`: if a superbelief `P` is a stage-level world mixture on the day-`n` small
sentences and the B2 state sentences (`PCPσ`), partitions (`E5σ`), agrees with a base `Q` on
the small sentences (`E1x`) and has exact faith in the written-out states on the listed
coordinates (`E2xσIdx`), then `Q` satisfies exact finite-time no-net-expected-update on every
pinned coordinate — and from some day on both coordinates are pinned (`pinned_eventually_B2`).
Any `Q`, FAF's LIA included; nothing says the LIA is linked. **Non-vacuity**: the package is
inhabited at most by a point mass on `tbl 0 1` (`charged_eq_tbl01`); the point mass on a
completed-theory world inhabits it at `rep01` under the rounded-price condition on every day
`m ≥ 1` (`InstanceB2Point.determination_B2_pointMass`; the condition holds from some day on,
`tbl01_eventually`, and is open on the initial segment), so the instance is N− by necessity on
this index and its inhabitation is conditional; the N+ inhabitant of the abstract theorem is
`Trilemma.determination_package_inhabited`.
Source: [[bli-program]] §3.6(ii); desiderata I6; mandate K2 (judged item 1); attempt A `B2.determination_B2` (over its own coherence), attempt B `d_nnucell_B2` (over `E2xσ`, vacuous)
Kind: C
Fidelity: exact (stage level, `E2xσIdx`, on the fixed grid; `∃ N` for the pinned set)
Hyps: (a) -/
theorem determination_B2 (rep : ℕ → ℕ → ℚ) {atoms : ℕ → Finset ℕ} {P Q : History}
    (hatoms : ∀ n, stateAtoms σB2 (fixedSystemR rep) n ⊆ atoms n)
    (hcoh : PCPσ atoms (paperDP 𝗜𝚺₁) P) (hE5 : E5σ σB2 (fixedSystemR rep) P) (hE1 : E1x Q P)
    (hE2 : E2xσIdx σB2 witnessIndex (fixedSystemR rep) P) :
    D_NNUcell (fixedCF rep) witnessIndex Q := by
  have hσ : ∀ m, ∀ q ∈ (fixedSystemR rep).states m, stateOf (fixedCF rep) m q = σB2 m q :=
    fun m q hq => stateOf_fixedCF_eq rep m hq
  exact determination (fixedCF rep) hcoh (fun n => by rw [stateAtoms_congr hσ]; exact hatoms n)
    ((E5σ_congr hσ).2 hE5) hE1 ((E2xσIdx_congr hσ).2 hE2) (fixedStates_spuriousEntails rep)
    (fixedSystem_valuesAtRep rep) (fixed_scope rep)

/-- **K2 at B2 at `bli-found`'s full `E2xσ`** (attempt B's `d_nnucell_B2`, restated). **Vacuous
for every `rep`**: `fixedSystemR_e2xσ_unsat`. Kept because it is the mandate's literal shape.
Source: mandate K2; attempt B `d_nnucell_B2`
Kind: C
Fidelity: exact as stated; flagged: hypothesis package empty for every `rep` (F-A1)
Hyps: (a) -/
theorem d_nnucell_B2_e2xσ (rep : ℕ → ℕ → ℚ) {atoms : ℕ → Finset ℕ} {P Q : History}
    (hatoms : ∀ n, stateAtoms σB2 (fixedSystemR rep) n ⊆ atoms n)
    (hcoh : PCPσ atoms (paperDP 𝗜𝚺₁) P) (hE5 : E5σ σB2 (fixedSystemR rep) P) (hE1 : E1x Q P)
    (hE2 : E2xσ σB2 (fixedSystemR rep) P) :
    D_NNUcell (fixedCF rep) witnessIndex Q :=
  Cleanroom.Bli.BliLinkageB.d_nnucell_B2 rep hatoms hcoh hE5 hE1 hE2

/-- **The trilemma's horn (0) at B2**: over a base violating `D_NNUcell` on the fixed grid, no
superbelief satisfies `PCPσ ∧ E1x ∧ E2xσIdx ∧ E5σ` at the B2 state sentence.
Source: [[bli-program]] §3.6(ii); mandate K2 (T0); attempt B `trilemma_T0_B2`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem trilemma_T0_B2 (rep : ℕ → ℕ → ℚ) {atoms : ℕ → Finset ℕ} {P Q : History}
    (hatoms : ∀ n, stateAtoms σB2 (fixedSystemR rep) n ⊆ atoms n)
    (hviol : ¬ D_NNUcell (fixedCF rep) witnessIndex Q) :
    ¬ (PCPσ atoms (paperDP 𝗜𝚺₁) P ∧ E1x Q P ∧ E2xσIdx σB2 witnessIndex (fixedSystemR rep) P ∧
      E5σ σB2 (fixedSystemR rep) P) := by
  rintro ⟨hcoh, hE1, hE2, hE5⟩
  exact hviol (determination_B2 rep hatoms hcoh hE5 hE1 hE2)

/-- **The pinned set is eventually non-empty** (K1's deliverable): from some day on both
`⌜⊥⌝` and `⌜⊤⌝` are pinned on the fixed grid at `𝗜𝚺₁`. Attempt B's route: the cell literal is an
atom over a `Nat.pair`-nest of constants and the day, a machine-metered family, hence eventually
day-small (`bli-found`'s `machineSentenceCodes_eventually_small`). Attempt A proved the same by
explicit size bounds (`B2.exists_pinned_from`: from day `K₁ + 10`, `K₁` the base-4 length of the
quote program's codes), over its own family. `∃ N` only — the quote code's constant is opaque.
Source: mandate K1 ("Pinned set non-empty"); attempt B `pinned_eventually_B2`; attempt A `B2.exists_pinned_from`
Kind: C
Fidelity: exact (`∃ N`, no numeral)
Hyps: (a) -/
theorem pinned_eventually_B2 (rep : ℕ → ℕ → ℚ) :
    ∃ N, ∀ n ≥ N, Encodable.encode (⊥ : Sentence) ∈ pinned (fixedCF rep) witnessIndex n ∧
      Encodable.encode (⊤ : Sentence) ∈ pinned (fixedCF rep) witnessIndex n :=
  Cleanroom.Bli.BliLinkageB.pinned_eventually_B2 rep

end B2

/-! ## Which faith predicate a B2 instance can carry -/

section Refutations

variable {σ : ℕ → ℕ → Sentence} {S : StateSystem} {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess}
variable {P : History}

/-- **Full faith over a system valuing an unlisted tautology at `0` is unsatisfiable under
coherence with partition mass one**: if `ψ` holds in every world, lies in `Sminus (n+1) (n+1)`
and every day-`(n+1)` candidate values it at `0`, then `E2xσ` fails for every `P` coherent on
day `n` with mass one on the candidates — faith demands `P n (ψ ⋏ σ_q) = 0 · P n σ_q = 0` while
the mixture gives `P n σ_q`. Attempt A's F-A1 engine, over the record (plain stage) coherence.
Source: this run (A's F-A1); bli-found F-2/F-12 (the junk value `0` off the index)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem e2xσ_unsat_of_unlisted_tautology (n : ℕ)
    (hcoh : CoherentOn (DP.D n) (smallAtoms n ∪ atoms n) (P n))
    (hatoms : stateAtoms σ S n ⊆ atoms n)
    (hmass : ∑ q ∈ S.states (n + 1), P n (σ (n + 1) q) = 1)
    (ψ : Sentence) (htaut : ∀ v : PCWorld, v.Holds ψ)
    (hψA : sentenceAtomCodes ψ ⊆ smallAtoms n ∪ atoms n)
    (hψS : ψ ∈ Sminus (n + 1) (n + 1)) (hval : ∀ q ∈ S.states (n + 1), S.val (n + 1) q ψ = 0) :
    ¬ E2xσ σ S P := by
  intro hE2
  obtain ⟨k, W, w, -, hM⟩ :=
    (coherentOnW_iff _ _ _).1 ((coherentOn_iff_coherentOnW _ _ _).1 hcoh)
  have hσA : ∀ q ∈ S.states (n + 1),
      sentenceAtomCodes (σ (n + 1) q) ⊆ smallAtoms n ∪ atoms n := fun q hq =>
    (atoms_subset_stateAtoms σ S hq).trans (hatoms.trans Finset.subset_union_right)
  have hzero : ∀ q ∈ S.states (n + 1), P n (σ (n + 1) q) = 0 := fun q hq => by
    have h1 : P n (ψ ⋏ σ (n + 1) q) = P n (σ (n + 1) q) :=
      hM.and_state_eq_of_forced (hσA q hq) hψA fun i _ _ => htaut (W i)
    have h2 := hE2 n (n + 1) (Nat.lt_succ_self n) q hq ψ hψS
    rw [hval q hq, zero_mul] at h2
    rw [← h1, h2]
  rw [Finset.sum_eq_zero hzero] at hmass
  exact zero_ne_one hmass

/-- Every fixed table values the unlisted `⊤ ⋏ ⊤` at the junk `0`, whatever `rep`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma fixedSystemR_val_verum_and_verum (rep : ℕ → ℕ → ℚ) (m : ℕ) {q : ℕ}
    (hq : q ∈ fixedStates m) : (fixedSystemR rep).val m q ((⊤ : Sentence) ⋏ ⊤) = 0 := by
  obtain ⟨a, b, -, -, rfl⟩ := (Cleanroom.Bli.BliLinkageB.mem_fixedStates_iff (m := m)).1 hq
  show ((((entryOf (Encodable.encode ((⊤ : Sentence) ⋏ ⊤)) (tableOfCode _)).map (rep m)).getD 0 :
    ℚ) : ℝ) = 0
  rw [tableOfCode_encode]
  simp [tbl, entryOf]

/-- **`bli-found`'s full faith `E2xσ` is unsatisfiable over the fixed grid for every `rep`**, by
any `P` coherent at day `n ≥ 1` with partition mass one: `⊤ ⋏ ⊤ ∈ Sminus (n+1) (n+1)` is unlisted
and valued at `0`. So the hypothesis package of `d_nnucell_B2_e2xσ` is empty at every `rep`, and
`E2xσIdx` is the faith predicate a list-table B2 system can carry.
Source: this run (A's F-A1, strengthening B's FB-4 from `witnessRep` to every `rep`)
Kind: P (refutation)
Fidelity: exact
Hyps: (a) -/
theorem fixedSystemR_e2xσ_unsat (rep : ℕ → ℕ → ℚ) {atoms : ℕ → Finset ℕ} {P : History} {n : ℕ}
    (hn : 1 ≤ n) (hatoms : ∀ n, stateAtoms σB2 (fixedSystemR rep) n ⊆ atoms n)
    (hcoh : PCPσ atoms (paperDP 𝗜𝚺₁) P) (hE5 : E5σ σB2 (fixedSystemR rep) P) :
    ¬ E2xσ σB2 (fixedSystemR rep) P :=
  e2xσ_unsat_of_unlisted_tautology n (hcoh n) (hatoms n) (hE5 n).1 _
    (fun v => (PCWorld.holds_and v _ _).2 ⟨PCWorld.holds_top v, PCWorld.holds_top v⟩)
    (by simp) (AttemptA.B2.verum_and_verum_facts (m := n + 1) (by omega)).2.1
    (fun q hq => fixedSystemR_val_verum_and_verum rep (n + 1) hq)

/-- **`witnessRep` cannot carry faith even on the index** (A's F-A2 over the record coherence):
with `bli-found`'s representatives `(1/4, 3/4)`, `PCPσ ∧ E5σ ∧ E2xσIdx` at the B2 state sentence
over `fixedSystem` is unsatisfiable on every day — faith at the listed `⊥` pins every charged
candidate's value at `⊥` to `0`, and `witnessRep` never is `0`. Strengthens attempt B's
`fixedSystem_witnessRep_unsat` (which refutes the full `E2xσ`).
Source: this run (A's F-A2, B's FB-4); mandate § K4c (whose "faith at `⊥`/`⊤` is `0`/`1`" presumes endpoint representatives)
Kind: P (refutation)
Fidelity: exact
Hyps: (a) -/
theorem fixedSystem_witnessRep_unsat_idx {atoms : ℕ → Finset ℕ} {P : History} (n : ℕ)
    (hatoms : ∀ n, stateAtoms σB2 fixedSystem n ⊆ atoms n)
    (hcoh : PCPσ atoms (paperDP 𝗜𝚺₁) P) (hE5 : E5σ σB2 fixedSystem P) :
    ¬ E2xσIdx σB2 witnessIndex fixedSystem P := by
  intro hE2
  have hσA : ∀ q ∈ fixedSystem.states (n + 1),
      sentenceAtomCodes (σB2 (n + 1) q) ⊆ smallAtoms n ∪ atoms n := fun q hq =>
    (atoms_subset_stateAtoms σB2 _ hq).trans ((hatoms n).trans Finset.subset_union_right)
  have hfaith : ∀ q ∈ fixedSystem.states (n + 1),
      P n (⊥ ⋏ σB2 (n + 1) q) = fixedSystem.val (n + 1) q ⊥ * P n (σB2 (n + 1) q) := fun q hq => by
    have := hE2 n (n + 1) (Nat.lt_succ_self n) q hq (Encodable.encode (⊥ : Sentence))
      (by simp [witnessIndex]) (by rw [sentenceOfCode_encode]; exact falsum_mem_Sminus _ _)
    rwa [sentenceOfCode_encode] at this
  refine Cleanroom.Bli.BliLinkageB.no_partition_of_val_falsum_ne_zero
    ((coherentOn_iff_coherentOnW _ _ _).1 (hcoh n)) hσA (partitionAt_of_E5σ hE5 n) hfaith
    fun q hq => ?_
  rw [Cleanroom.Bli.BliLinkageB.fixedSystem_eq] at hq ⊢
  obtain ⟨a, ha, hv⟩ := Cleanroom.Bli.BliLinkageB.fixedSystemR_val_falsum witnessRep (n + 1) hq
  rw [hv]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;> norm_num [witnessRep]

/-- **On `[⌜⊥⌝, ⌜⊤⌝]` with the endpoint representatives, the only chargeable table is
`tbl 0 1`**: under `PCPσ ∧ E2xσIdx`, a candidate of positive day-`n` mass has `⊥`-entry `0`
(faith at `⊥`, never true, pins its value to `0 = rep01 0`) and `⊤`-entry `1` (faith at `⊤`,
always true, pins its value to `1 = rep01 1`). Hence every superbelief satisfying the B2 package
of `determination_B2` at `rep01` is a point mass on `tbl 0 1`: **no two-state instance exists on
this index**, and the mandate's K1/K4c witness prescription cannot be met (B's FB-4, made exact).
Source: this run (A's F-A2 and B's FB-4, merged); mandate K1 (witness), K4c
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem charged_eq_tbl01 {atoms : ℕ → Finset ℕ} {P : History} (n : ℕ)
    (hatoms : ∀ n, stateAtoms σB2 (fixedSystemR AttemptA.B2.rep01) n ⊆ atoms n)
    (hcoh : PCPσ atoms (paperDP 𝗜𝚺₁) P)
    (hE2 : E2xσIdx σB2 witnessIndex (fixedSystemR AttemptA.B2.rep01) P) {q : ℕ}
    (hq : q ∈ fixedStates (n + 1)) (hpos : P n (σB2 (n + 1) q) ≠ 0) :
    q = Encodable.encode (tbl 0 1) := by
  have hcohW := (coherentOn_iff_coherentOnW _ _ _).1 (hcoh n)
  have hσA : ∀ q ∈ (fixedSystemR AttemptA.B2.rep01).states (n + 1),
      sentenceAtomCodes (σB2 (n + 1) q) ⊆ smallAtoms n ∪ atoms n := fun q hq =>
    (atoms_subset_stateAtoms σB2 _ hq).trans ((hatoms n).trans Finset.subset_union_right)
  have hf₀ : ∀ q ∈ (fixedSystemR AttemptA.B2.rep01).states (n + 1),
      P n (⊥ ⋏ σB2 (n + 1) q) =
        (fixedSystemR AttemptA.B2.rep01).val (n + 1) q ⊥ * P n (σB2 (n + 1) q) := fun q hq => by
    have := hE2 n (n + 1) (Nat.lt_succ_self n) q hq (Encodable.encode (⊥ : Sentence))
      (by simp [witnessIndex]) (by rw [sentenceOfCode_encode]; exact falsum_mem_Sminus _ _)
    rwa [sentenceOfCode_encode] at this
  have hf₁ : ∀ q ∈ (fixedSystemR AttemptA.B2.rep01).states (n + 1),
      P n (⊤ ⋏ σB2 (n + 1) q) =
        (fixedSystemR AttemptA.B2.rep01).val (n + 1) q ⊤ * P n (σB2 (n + 1) q) := fun q hq => by
    have := hE2 n (n + 1) (Nat.lt_succ_self n) q hq (Encodable.encode (⊤ : Sentence))
      (by simp [witnessIndex])
      (by rw [sentenceOfCode_encode]
          exact Cleanroom.Bli.BliLinkageB.verum_mem_Sminus (by omega) _)
    rwa [sentenceOfCode_encode] at this
  have h0 := Cleanroom.Bli.BliLinkageB.faith_at_falsum hcohW hσA hf₀ hq hpos
  have h1 := Cleanroom.Bli.BliLinkageB.faith_at_verum hcohW hσA hf₁ hq hpos
  obtain ⟨a, b, -, hb, rfl⟩ := (Cleanroom.Bli.BliLinkageB.mem_fixedStates_iff (m := n + 1)).1 hq
  have hva : (fixedSystemR AttemptA.B2.rep01).val (n + 1) (Encodable.encode (tbl a b)) ⊥ =
      ((AttemptA.B2.rep01 (n + 1) a : ℚ) : ℝ) := by
    show ((((entryOf (Encodable.encode (⊥ : Sentence)) (tableOfCode _)).map
      (AttemptA.B2.rep01 (n + 1))).getD 0 : ℚ) : ℝ) = _
    rw [tableOfCode_encode, Cleanroom.Bli.BliLinkageB.entryOf_tbl_bot]
    rfl
  have hvb : (fixedSystemR AttemptA.B2.rep01).val (n + 1) (Encodable.encode (tbl a b)) ⊤ =
      ((AttemptA.B2.rep01 (n + 1) b : ℚ) : ℝ) := by
    show ((((entryOf (Encodable.encode (⊤ : Sentence)) (tableOfCode _)).map
      (AttemptA.B2.rep01 (n + 1))).getD 0 : ℚ) : ℝ) = _
    rw [tableOfCode_encode, Cleanroom.Bli.BliLinkageB.entryOf_tbl_top]
    rfl
  rw [hva] at h0
  rw [hvb] at h1
  have ha0 : a = 0 := by
    by_contra h
    simp [AttemptA.B2.rep01, h] at h0
  have hb1 : b = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
    · simp [AttemptA.B2.rep01] at h1
    · rfl
  subst ha0
  subst hb1
  rfl

end Refutations

/-! ## K3 at FAF's LIA -/

/-- **K3 at FAF's LIA over `paperDP 𝗜𝚺₁` (the instance of record; judged item 3).** With
`Q := liaHistory (paperDP 𝗜𝚺₁)` (FAF's unconditional `paperLIA`), the B2 cell family at
`halfRound` with any representatives, a listed coordinate `c` pinned from day `N` on, and the
degenerate table listing `c` at today's rounding of the LIA's exact quote `marketValue`
(`hentry`): **if the LIA's rounded price of `c` moves infinitely often (`hmove`)**, no `P`
satisfies `PCPσ ∧ E5σ ∧ E1x ∧ Degenerate` at the B2 state sentence. Metering
(`cellSentence_pair_machineSentenceCodes`), stage entry (`cellSentence_neg_enters`) and
`hworld` (`paperDP_hworld`) are discharged from FAF and `bli-found`; `hmove` is the only
hypothesis not about instance data; no T7 is involved (the quoted market is `paperDP`'s own).
**Fixed coordinate (audit r1 fidelity B2)**: for a fixed sentence the LIA's price converges,
so `hmove` holds only if the limit is exactly `1/2` and the price crosses it infinitely often
(`InstanceK3.hmove_fixed_forces_limit_half`); at the fixed grid's coordinates `⌜⊥⌝`/`⌜⊤⌝` it is
false (`InstanceK3.not_hmove_falsum`/`_verum`). This is therefore not the mandate's K3
instance over a coordinate *family* `χ n`; that is `InstanceK3.no_degenerate_linked_bli_LIA_family`,
of which this theorem is the constant case. The OPEN `leakQ_rounded_price_moves` (over
`leakQ`/`leakDP`, family `memberAtom n`) is not a candidate for this theorem's `hmove`.
Source: [[bli-program]] §3.6(iii); desiderata I2; mandate K3; attempt B `InstanceCells.no_degenerate_linked_bli_LIA` (FB-16); audit r1 fidelity B2
Kind: C
Fidelity: weaker: a fixed coordinate in place of the mandate's family `χ n` (`hmove` then confined to the limit-`1/2` boundary and false at the witness index); the degenerate table's shape and the grid conditions are instance data
Hyps: (a); `hmove` is a hypothesis of the statement (the honest form) -/
theorem no_degenerate_linked_bli_LIA (rep : ℕ → ℕ → ℚ) (index : ℕ → List ℕ) (S : StateSystem)
    {atoms : ℕ → Finset ℕ} {P : History} (c : ℕ) (deg : ℕ → ℕ) (N : ℕ)
    (hpin : ∀ n ≥ N, c ∈ pinned (fixedCF rep) index n)
    (hdegS : ∀ n, deg n ∈ S.states (n + 1))
    (hentry : ∀ n, entryOf c (tableOfCode (deg n)) =
      some (halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode c))))))
    (hsp : ∀ n, SpuriousEntails (stateOf (fixedCF rep)) (fixedCF rep).literal S index
      (fixedCF rep).cells n)
    (hatoms : ∀ n, stateAtoms (stateOf (fixedCF rep)) S n ⊆ atoms n)
    (hmove : Set.Infinite {n |
      halfRound (n + 1) (marketValue 𝗜𝚺₁ (Nat.pair (n + 1) (Encodable.encode (sentenceOfCode c)))) ≠
        halfRound n (marketValue 𝗜𝚺₁ (Nat.pair n (Encodable.encode (sentenceOfCode c))))}) :
    ¬ (PCPσ atoms (paperDP 𝗜𝚺₁) P ∧ E5σ (stateOf (fixedCF rep)) S P ∧
      E1x (liaHistory (paperDP 𝗜𝚺₁)) P ∧ Degenerate (stateOf (fixedCF rep)) P deg) :=
  Cleanroom.Bli.BliLinkageB.no_degenerate_linked_bli_LIA rep index S c deg N hpin hdegS hentry hsp
    hatoms hmove

end Cleanroom.Bli.BliLinkage
