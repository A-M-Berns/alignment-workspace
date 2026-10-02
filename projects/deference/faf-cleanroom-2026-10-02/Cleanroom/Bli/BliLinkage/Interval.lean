import Cleanroom.Bli.BliLinkage.Determination
import Cleanroom.Bli.BliLinkageB.Witness

/-!
# `bli-linkage` — interval-state linkage: the dissolution artifact made exact, and the
transfer theorem (the trilemma stands under interval linkage with price-reflected literals)

Written in repair round 1 (2026-10-01), answering blocking issue B1 of both round-1 audits
([[bli-linkage-audit-r1-fidelity]] § 2, [[bli-linkage-audit-r1-adversarial]] § 2). The two
auditors' probes (`run/wp/bli-linkage/audit-r1-probes/DissolutionArtifact.lean`,
`DissolutionDecoupled.lean`) are adopted here as library theorems, and the general claim both
sketched is proved.

## What was wrong

`Trilemma.dissolution` (attempt B's `Dissolve.dissolution`) exhibits the market `dP` satisfying
the interval-state package `LNKcell ∧ PCPσTheory ∧ PCPσLinked ∧ E5σ ∧ E1x ∧ E2xσ` at the
interval states `dσ` with `¬ D_NNUcell dCF dIndex dP`. But `dCF`'s literals are fresh atoms
that hold in a world `wld x b a` iff `r = a`, **whatever the price `x`**, and every world of
`dP` has `a = 1` (`dWorld_eq`): the literal "cell 1" holds at price `1/8` (cell 0) as at `7/8`.
So `¬ D_NNUcell dCF dIndex dP` is the equation `1/2 ≠ 1/4 · 0 + 3/4 · 1`
(`dissolution_violation_is_decoupling`), an identity about atoms the quotes never constrain.
The witness shows that *unreflected* literals are unconstrained — not that interval linkage
dissolves the trilemma. The round-0 ledger graded it N+/exact and the report called it "the
headline negative result"; both were wrong, and are corrected in this round.

## What is true

1. **The same market with price-coupled literals satisfies the same interval-state package
   with `D_NNUcell` TRUE** (`dissolution_package_with_coupled_literals`): attempt B's `wP`
   (worlds `wld (1/8) _ 0`, `wld (7/8) _ 1`, the literal index the cell of the price), the same
   interval states `dσ`, the same quote family, the same process `dDP`, the same conditioning
   values. The only difference between the two witnesses is whether the literal atoms mean
   "the price is in cell `r`".
2. **The transfer theorem** (`interval_determination`, the general statement): over a mixture of
   worlds in a class `𝒱 n` on which the literal state of a candidate entails its interval state
   (`hLI`: the closed cell lies inside the open cell) and a *uniquely held* interval state
   entails the literal state (`hIL`: a price in exactly one open cell lies in that cell's closed
   cell), the interval-state package `E5σ σI ∧ E1x ∧ E2xσIdx σI` forces the exact identity
   `D_NNUcell C index Q` on the cell literals. The mechanism: exclusivity in `P`-measure at the
   interval states (`E5σ`) removes the overlaps from the support — a charged world holds exactly
   one interval state (`IsMixture.charged_unique_state`) — and off the overlaps the open cells
   behave as the closed partition, so the per-day engine (`Determination.nnu_day`) applies to
   the literal states. **Angle B's decisive question is therefore answered in the negative,
   over mixtures of worlds that reflect the literals**: with price-reflected literals the
   trilemma stands under interval linkage; the overlaps are not a resource because the
   partition constraint forbids charging them. The qualifier matters (audit r2 fidelity N1):
   the world class `𝒱 n` with `hLI`/`hIL` is strictly stronger than plain stage coherence
   `PCPσ` and strictly weaker than `PCPσTheory`; at the stage level the question is which
   stages link the day-`(n+1)` literals to the quotes, and until they do the decoupled-literal
   market of round 0 is a legitimate stage-level inhabitant. No B2 instance of the transfer
   theorem is shipped: at `paperDP 𝗜𝚺₁` the reflection facts are completed-theory facts, and
   the completed-theory class collapses the mixture to a point mass under `E5σ` (FB-3), so an
   intermediate class would be needed (audit r2 adversarial N2; not built).
3. `interval_determination_witness` (N+): the transfer theorem's hypotheses are inhabited by
   `wP` over the class of price-coupled witness worlds, with both candidates charged `1/2`.

The dissolution witness itself is kept (relabelled N− in `Trilemma.lean` and the ledger): it is
the honest record that a cell-literal family *not* reflected to the quoted price is not
constrained by the quotes.
-/

namespace Cleanroom.Bli.BliLinkage

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound
open Cleanroom.Bli.BliLinkageB (IsMixture PartitionAt coherentOnW_iff partitionAt_of_E5σ
  payout_and payout_of_holds payout_of_not_holds)
open Cleanroom.Bli.BliLinkageB.Dissolve Cleanroom.Bli.BliLinkageB.Witness

/-! ## 1. The artifact, stated -/

section Artifact

/-- **The dissolution's cell literals are decoupled from the price**: in every world of `dCF`'s
class, the literal of cell `1` holds and the literal of cell `0` fails, whatever the price.
Source: this run (audit r1 B1; probe `DissolutionArtifact.dCF_literals_decoupled`)
Kind: L
Fidelity: n/a -/
theorem dCF_literals_decoupled (v : PCWorld) (hv : ∃ (x : ℚ) (b : Bool), v = wld x b 1)
    (m : ℕ) (φ : Sentence) : v.Holds (dCF.literal m φ 1) ∧ ¬ v.Holds (dCF.literal m φ 0) := by
  obtain ⟨x, b, rfl⟩ := hv
  rw [dCF_literal, wld_holds_dLit, wld_holds_dLit]
  exact ⟨rfl, by norm_num⟩

/-- **The dissolution's violation is the decoupling**: `dP` prices literal `0` at `0` and
literal `1` at `1` on every day, so `¬ D_NNUcell dCF dIndex dP` is `1/2 ≠ 1/4 · 0 + 3/4 · 1`.
Source: this run (audit r1 B1; probe `DissolutionArtifact.dissolution_violation_is_decoupling`)
Kind: L
Fidelity: n/a -/
theorem dissolution_violation_is_decoupling (n m : ℕ) (φ : Sentence) :
    dP n (dCF.literal m φ 0) = 0 ∧ dP n (dCF.literal m φ 1) = 1 := by
  rw [dCF_literal]; exact dP_dLit n m φ

/-- **`dP` is certain of the literal "cell 1" while giving the interval state "price ∈ (−1, 1/2)"
mass `1/2`** — impossible for a literal reflected to the quoted price (cell `1` is `[1/2, 1]`,
disjoint from `(−1, 1/2)`).
Source: this run (audit r1 B1; probe `DissolutionDecoupled.dP_certain_of_literal`)
Kind: L
Fidelity: n/a -/
theorem dP_certain_of_literal (n m : ℕ) :
    dP n (dLit m dPhi 1) = 1 ∧ dP n (dLit m dPhi 0) = 0 ∧ dP n (dσ m (dCode 0)) = 1 / 2 :=
  ⟨(dP_dLit n m dPhi).2, (dP_dLit n m dPhi).1, (dP_state n m).1⟩

end Artifact

/-! ## 2. The same interval-state package over the price-coupled market, `D_NNUcell` true -/

section Coupled

/-- On the four price-coupled worlds, the interval state of `dCode r` and the literal state of
`dCode r` have the same payout (`r ≤ 1`).
Source: this run (probe `DissolutionArtifact.wWorld_payout_dσ`)
Kind: L
Fidelity: n/a -/
lemma wWorld_payout_dσ (i : Fin 4) (m : ℕ) :
    (wWorld i).payout (dσ m (dCode 0)) = (wWorld i).payout (wσ m (dCode 0)) ∧
      (wWorld i).payout (dσ m (dCode 1)) = (wWorld i).payout (wσ m (dCode 1)) := by
  obtain ⟨h00, h01, h10, h11⟩ := cell_facts m
  have h01' : (0 : ℕ) ≠ 1 := by norm_num
  match i with
  | 0 =>
    refine ⟨?_, ?_⟩
    · show (wld (1 / 8) true 0).payout _ = (wld (1 / 8) true 0).payout _
      rw [payout_dσ_of_mem h00, payout_wσ_self]
    · show (wld (1 / 8) true 0).payout _ = (wld (1 / 8) true 0).payout _
      rw [payout_dσ_of_not_mem h01, payout_wσ_ne _ _ h01'.symm]
  | 1 =>
    refine ⟨?_, ?_⟩
    · show (wld (1 / 8) false 0).payout _ = (wld (1 / 8) false 0).payout _
      rw [payout_dσ_of_mem h00, payout_wσ_self]
    · show (wld (1 / 8) false 0).payout _ = (wld (1 / 8) false 0).payout _
      rw [payout_dσ_of_not_mem h01, payout_wσ_ne _ _ h01'.symm]
  | 2 =>
    refine ⟨?_, ?_⟩
    · show (wld (7 / 8) true 1).payout _ = (wld (7 / 8) true 1).payout _
      rw [payout_dσ_of_not_mem h10, payout_wσ_ne _ _ h01']
    · show (wld (7 / 8) true 1).payout _ = (wld (7 / 8) true 1).payout _
      rw [payout_dσ_of_mem h11, payout_wσ_self]
  | 3 =>
    refine ⟨?_, ?_⟩
    · show (wld (7 / 8) false 1).payout _ = (wld (7 / 8) false 1).payout _
      rw [payout_dσ_of_not_mem h10, payout_wσ_ne _ _ h01']
    · show (wld (7 / 8) false 1).payout _ = (wld (7 / 8) false 1).payout _
      rw [payout_dσ_of_mem h11, payout_wσ_self]

/-- The same, over the candidates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wWorld_payout_dσ' (i : Fin 4) (m : ℕ) {q : ℕ} (hq : q ∈ dStates m) :
    (wWorld i).payout (dσ m q) = (wWorld i).payout (wσ m q) := by
  rw [mem_dStates] at hq
  rcases hq with rfl | rfl
  · exact (wWorld_payout_dσ i m).1
  · exact (wWorld_payout_dσ i m).2

/-- `wP` prices a candidate's interval state as its literal state.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wP_dσ_eq (n m : ℕ) {q : ℕ} (hq : q ∈ dStates m) : wP n (dσ m q) = wP n (wσ m q) := by
  unfold wP
  exact Finset.sum_congr rfl fun i _ => by rw [wWorld_payout_dσ' i m hq]

/-- The same under a conjunct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wP_and_dσ_eq (n m : ℕ) {q : ℕ} (hq : q ∈ dStates m) (φ : Sentence) :
    wP n (φ ⋏ dσ m q) = wP n (φ ⋏ wσ m q) := by
  unfold wP
  exact Finset.sum_congr rfl fun i _ => by rw [payout_and, payout_and, wWorld_payout_dσ' i m hq]

/-- The same for two candidates' conjunction.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma wP_dσ_and_dσ_eq (n m : ℕ) {q₁ q₂ : ℕ} (h₁ : q₁ ∈ dStates m) (h₂ : q₂ ∈ dStates m) :
    wP n (dσ m q₁ ⋏ dσ m q₂) = wP n (wσ m q₁ ⋏ wσ m q₂) := by
  unfold wP
  exact Finset.sum_congr rfl fun i _ => by
    rw [payout_and, payout_and, wWorld_payout_dσ' i m h₁, wWorld_payout_dσ' i m h₂]

/-- `E5σ` at the interval states over `wP`.
Source: this run (probe `DissolutionArtifact.wE5σ_dσ`)
Kind: L
Fidelity: n/a -/
theorem wE5σ_dσ : E5σ dσ wS wP := by
  intro n
  obtain ⟨hmass, hexcl⟩ := wE5σ n
  constructor
  · rw [← hmass]
    exact Finset.sum_congr rfl fun q hq => wP_dσ_eq n (n + 1) (by simpa using hq)
  · intro q₁ hq₁ q₂ hq₂ hne
    rw [wP_dσ_and_dσ_eq n (n + 1) (by simpa using hq₁) (by simpa using hq₂)]
    exact hexcl q₁ hq₁ q₂ hq₂ hne

/-- `E2xσ` at the interval states over `wP` (faith as conditioning, the same values `wVal`).
Source: this run (probe `DissolutionArtifact.wE2xσ_dσ`)
Kind: L
Fidelity: n/a -/
theorem wE2xσ_dσ : E2xσ dσ wS wP := by
  intro n m hnm q hq φ hφ
  rw [wP_and_dσ_eq n m (by simpa using hq) φ, wP_dσ_eq n m (by simpa using hq)]
  exact wE2xσ n m hnm q hq φ hφ

/-- A price-coupled witness world is linked at the interval state family `dσ`.
Source: this run (probe `DissolutionArtifact.wld_linkedWorld_dσ`)
Kind: L
Fidelity: n/a -/
lemma wld_linkedWorld_dσ {x : ℚ} (h1 : -1 < x) (h2 : x < 2) (b : Bool) (a m : ℕ) :
    Cleanroom.Bli.BliLinkageB.LinkedWorld dσ dQuote wS (cellOfTable dLo dHi) m (wld x b a) := by
  intro q hq φ _ hs
  rw [wS_states, mem_dStates] at hq
  rcases hq with rfl | rfl <;>
  · rw [cellOfTable_dCode]
    rw [wld_holds_dσ] at hs
    by_cases h : Encodable.encode φ = dC0
    · rw [if_pos h]; exact (wld_holds_dQuote _ _ _ _ _ _ _).2 hs
    · rw [if_neg h]; exact (wld_holds_dQuote _ _ _ _ _ _ _).2 ⟨h1, h2⟩

/-- `LNKcell` at the interval states over `wS`.
Source: this run (probe `DissolutionArtifact.wLNKcell_dσ`)
Kind: L
Fidelity: n/a -/
theorem wLNKcell_dσ : LNKcell dσ dQuote wS (cellOfTable dLo dHi) dDP := by
  intro m q hq φ hφ v hv hs
  rw [wS_states, mem_dStates] at hq
  have hdef : v.Holds (dQuote m φ (-1) 2) := hv m _ (mem_dDP.2 ⟨m, le_rfl, φ, hφ, rfl⟩)
  rcases hq with rfl | rfl <;>
  · rw [cellOfTable_dCode]
    by_cases h : Encodable.encode φ = dC0
    · rw [if_pos h, eq_dPhi_of_encode h]
      rw [dσ_dCode, PCWorld.holds_and] at hs
      exact hs.1
    · rw [if_neg h]; exact hdef

/-- `PCPσLinked` at the interval states over `wP`.
Source: this run (probe `DissolutionArtifact.wPCPσLinked_dσ`)
Kind: L
Fidelity: n/a -/
theorem wPCPσLinked_dσ (atoms : ℕ → Finset ℕ) :
    Cleanroom.Bli.BliLinkageB.PCPσLinked dσ dQuote wS (cellOfTable dLo dHi) atoms dDP wP := by
  intro n
  refine ⟨4, wWorld, dW, fun i => ?_, dW_nonneg, dW_sum, fun _ _ => rfl⟩
  obtain ⟨x, b, a, -, h1, h2, -, h⟩ := wWorld_eq i
  rw [h]
  exact ⟨wld_consistentWithTheory h1 h2 b a n, wld_linkedWorld_dσ h1 h2 b a _,
    wld_intervalSem x b a⟩

/-- **The dissolution's package, verbatim, over the price-coupled market `wP` — with
`D_NNUcell` TRUE.** Same prices, same weights, same interval state family `dσ`, same quote
family, same process `dDP`, same conditioning values; the literal atoms now mean "the price is
in cell `r`" (`wCF`). Together with `dissolution_violation_is_decoupling` this makes the
round-0 "dissolution" exact: its violation is carried by the decoupling of the literals from the
quoted price alone, not by interval linkage.
Source: this run (audit r1 B1, both lenses; probes `DissolutionArtifact.dissolution_package_with_coupled_literals`, `DissolutionDecoupled.interval_package_over_linked_literals`)
Kind: N+
Fidelity: exact (the conjunct list of `Trilemma.dissolution` with `dCF`/`dS`/`dP` replaced by `wCF`/`wS`/`wP` and the last conjunct negated)
Hyps: (a) -/
theorem dissolution_package_with_coupled_literals :
    LNKcell dσ dQuote wS (cellOfTable dLo dHi) dDP ∧
      PCPσTheory (stateAtoms dσ wS) dDP wP ∧
      Cleanroom.Bli.BliLinkageB.PCPσLinked dσ dQuote wS (cellOfTable dLo dHi) (stateAtoms dσ wS)
        dDP wP ∧
      E5σ dσ wS wP ∧ E1x wP wP ∧ E2xσ dσ wS wP ∧
      (∃ N, ∀ n ≥ N, dC0 ∈ pinned wCF dIndex n) ∧
      (∀ n, wP n dPhi = 1 / 2 ∧ wP n (dσ (n + 1) (dCode 0)) = 1 / 2 ∧
        wP n (dσ (n + 1) (dCode 1)) = 1 / 2) ∧
      D_NNUcell wCF dIndex wP :=
  ⟨wLNKcell_dσ, wPCPσTheory _, wPCPσLinked_dσ _, wE5σ_dσ, wE1x, wE2xσ_dσ, wPinned_eventually,
    fun n => ⟨wP_dPhi n,
      by rw [wP_dσ_eq n (n + 1) (by simp [dStates])]; exact (wP_state n (n + 1)).1,
      by rw [wP_dσ_eq n (n + 1) (by simp [dStates])]; exact (wP_state n (n + 1)).2⟩,
    Cleanroom.Bli.BliLinkageB.Witness.determination_package_inhabited.2.2.2.2.2.2.2.2.2.2⟩

end Coupled

/-! ## 3. The transfer theorem: an interval-state package with price-reflected literals forces
the exact identity on the literals -/

section Transfer

variable {𝒲 : PCWorld → Prop} (C : CellFamily 𝒲) {S : StateSystem} {atoms : ℕ → Finset ℕ}
variable {DP : DeductiveProcess} {P Q : History} {index : ℕ → List ℕ}
variable {k : ℕ} {W : Fin k → PCWorld} {w : Fin k → ℝ} {A : Finset ℕ} {p : Sentence → ℝ}
variable {σI : ℕ → ℕ → Sentence} {m : ℕ} {𝒱 : PCWorld → Prop}

/-- **In a charged world of a mixture partitioned at the interval states, the literal state of
a candidate holds iff its interval state holds.** (→) is `hLI` (the closed cell lies inside the
open cell). (←) the charged world holds exactly one interval state
(`IsMixture.charged_unique_state`: exclusivity in `p`-measure keeps the overlaps uncharged), so
the held interval state is uniquely held and `hIL` gives the literal state. This is where
interval linkage loses its slack: the partition constraint forbids charging the overlaps.
Source: this run (audit r1 B1, the sketch of both lenses); mandate § Attempt angles (B)
Kind: L
Fidelity: n/a -/
theorem charged_holds_literal_iff (hM : IsMixture W w A p) (hW : ∀ i, 𝒱 (W i))
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σI m q) ⊆ A) (hpart : PartitionAt σI S p m)
    (hLI : ∀ v, 𝒱 v → ∀ q ∈ S.states m, v.Holds (stateOf C m q) → v.Holds (σI m q))
    (hIL : ∀ v, 𝒱 v → ∀ q ∈ S.states m, v.Holds (σI m q) →
      (∀ q' ∈ S.states m, q' ≠ q → ¬ v.Holds (σI m q')) → v.Holds (stateOf C m q))
    {i : Fin k} (hi : 0 < w i) {q : ℕ} (hq : q ∈ S.states m) :
    (W i).Holds (stateOf C m q) ↔ (W i).Holds (σI m q) := by
  constructor
  · exact hLI (W i) (hW i) q hq
  · intro hI
    obtain ⟨q₀, hq₀, -, huniq⟩ := hM.charged_unique_state hσA hpart hi
    have hq0 : q = q₀ := huniq q hq hI
    refine hIL (W i) (hW i) q hq hI fun q' hq' hne hh' => hne ?_
    rw [huniq q' hq' hh', hq0]

/-- Payouts of the literal and interval states agree in charged worlds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem charged_payout_literal_eq (hM : IsMixture W w A p) (hW : ∀ i, 𝒱 (W i))
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σI m q) ⊆ A) (hpart : PartitionAt σI S p m)
    (hLI : ∀ v, 𝒱 v → ∀ q ∈ S.states m, v.Holds (stateOf C m q) → v.Holds (σI m q))
    (hIL : ∀ v, 𝒱 v → ∀ q ∈ S.states m, v.Holds (σI m q) →
      (∀ q' ∈ S.states m, q' ≠ q → ¬ v.Holds (σI m q')) → v.Holds (stateOf C m q))
    {i : Fin k} (hi : 0 < w i) {q : ℕ} (hq : q ∈ S.states m) :
    (W i).payout (stateOf C m q) = (W i).payout (σI m q) := by
  by_cases h : (W i).Holds (σI m q)
  · rw [payout_of_holds h,
      payout_of_holds ((charged_holds_literal_iff C hM hW hσA hpart hLI hIL hi hq).2 h)]
  · rw [payout_of_not_holds h, payout_of_not_holds
      (fun h' => h ((charged_holds_literal_iff C hM hW hσA hpart hLI hIL hi hq).1 h'))]

/-- The mixture prices a candidate's literal state as its interval state.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mixture_literal_eq_interval (hM : IsMixture W w A p) (hW : ∀ i, 𝒱 (W i))
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σI m q) ⊆ A)
    (hσLA : ∀ q ∈ S.states m, sentenceAtomCodes (stateOf C m q) ⊆ A)
    (hpart : PartitionAt σI S p m)
    (hLI : ∀ v, 𝒱 v → ∀ q ∈ S.states m, v.Holds (stateOf C m q) → v.Holds (σI m q))
    (hIL : ∀ v, 𝒱 v → ∀ q ∈ S.states m, v.Holds (σI m q) →
      (∀ q' ∈ S.states m, q' ≠ q → ¬ v.Holds (σI m q')) → v.Holds (stateOf C m q))
    {q : ℕ} (hq : q ∈ S.states m) : p (stateOf C m q) = p (σI m q) := by
  rw [hM.rep _ (hσLA q hq), hM.rep _ (hσA q hq)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases (hM.nonneg i).lt_or_eq with hi | hi
  · rw [charged_payout_literal_eq C hM hW hσA hpart hLI hIL hi hq]
  · rw [← hi, zero_mul, zero_mul]

/-- The same under a represented conjunct.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mixture_and_literal_eq_interval (hM : IsMixture W w A p) (hW : ∀ i, 𝒱 (W i))
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σI m q) ⊆ A)
    (hσLA : ∀ q ∈ S.states m, sentenceAtomCodes (stateOf C m q) ⊆ A)
    (hpart : PartitionAt σI S p m)
    (hLI : ∀ v, 𝒱 v → ∀ q ∈ S.states m, v.Holds (stateOf C m q) → v.Holds (σI m q))
    (hIL : ∀ v, 𝒱 v → ∀ q ∈ S.states m, v.Holds (σI m q) →
      (∀ q' ∈ S.states m, q' ≠ q → ¬ v.Holds (σI m q')) → v.Holds (stateOf C m q))
    {ψ : Sentence} (hψ : sentenceAtomCodes ψ ⊆ A) {q : ℕ} (hq : q ∈ S.states m) :
    p (ψ ⋏ stateOf C m q) = p (ψ ⋏ σI m q) := by
  have hA1 : sentenceAtomCodes (ψ ⋏ stateOf C m q) ⊆ A := by
    rw [sentenceAtomCodes_and]; exact Finset.union_subset hψ (hσLA q hq)
  have hA2 : sentenceAtomCodes (ψ ⋏ σI m q) ⊆ A := by
    rw [sentenceAtomCodes_and]; exact Finset.union_subset hψ (hσA q hq)
  rw [hM.rep _ hA1, hM.rep _ hA2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases (hM.nonneg i).lt_or_eq with hi | hi
  · rw [payout_and, payout_and, charged_payout_literal_eq C hM hW hσA hpart hLI hIL hi hq]
  · rw [← hi, zero_mul, zero_mul]

/-- The same for two candidates' conjunction.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mixture_literal_and_literal_eq_interval (hM : IsMixture W w A p) (hW : ∀ i, 𝒱 (W i))
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σI m q) ⊆ A)
    (hσLA : ∀ q ∈ S.states m, sentenceAtomCodes (stateOf C m q) ⊆ A)
    (hpart : PartitionAt σI S p m)
    (hLI : ∀ v, 𝒱 v → ∀ q ∈ S.states m, v.Holds (stateOf C m q) → v.Holds (σI m q))
    (hIL : ∀ v, 𝒱 v → ∀ q ∈ S.states m, v.Holds (σI m q) →
      (∀ q' ∈ S.states m, q' ≠ q → ¬ v.Holds (σI m q')) → v.Holds (stateOf C m q))
    {q₁ q₂ : ℕ} (hq₁ : q₁ ∈ S.states m) (hq₂ : q₂ ∈ S.states m) :
    p (stateOf C m q₁ ⋏ stateOf C m q₂) = p (σI m q₁ ⋏ σI m q₂) := by
  have hA1 : sentenceAtomCodes (stateOf C m q₁ ⋏ stateOf C m q₂) ⊆ A := by
    rw [sentenceAtomCodes_and]; exact Finset.union_subset (hσLA q₁ hq₁) (hσLA q₂ hq₂)
  have hA2 : sentenceAtomCodes (σI m q₁ ⋏ σI m q₂) ⊆ A := by
    rw [sentenceAtomCodes_and]; exact Finset.union_subset (hσA q₁ hq₁) (hσA q₂ hq₂)
  rw [hM.rep _ hA1, hM.rep _ hA2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases (hM.nonneg i).lt_or_eq with hi | hi
  · rw [payout_and, payout_and, charged_payout_literal_eq C hM hW hσA hpart hLI hIL hi hq₁,
      charged_payout_literal_eq C hM hW hσA hpart hLI hIL hi hq₂]
  · rw [← hi, zero_mul, zero_mul]

/-- **The partition transfers from the interval states to the literal states.**
Source: this run (audit r1 B1)
Kind: L
Fidelity: n/a -/
theorem partitionAt_literal_of_interval (hM : IsMixture W w A p) (hW : ∀ i, 𝒱 (W i))
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σI m q) ⊆ A)
    (hσLA : ∀ q ∈ S.states m, sentenceAtomCodes (stateOf C m q) ⊆ A)
    (hpart : PartitionAt σI S p m)
    (hLI : ∀ v, 𝒱 v → ∀ q ∈ S.states m, v.Holds (stateOf C m q) → v.Holds (σI m q))
    (hIL : ∀ v, 𝒱 v → ∀ q ∈ S.states m, v.Holds (σI m q) →
      (∀ q' ∈ S.states m, q' ≠ q → ¬ v.Holds (σI m q')) → v.Holds (stateOf C m q)) :
    PartitionAt (stateOf C) S p m where
  mass := by
    rw [← hpart.mass]
    exact Finset.sum_congr rfl fun q hq =>
      mixture_literal_eq_interval C hM hW hσA hσLA hpart hLI hIL hq
  excl := fun q₁ hq₁ q₂ hq₂ hne => by
    rw [mixture_literal_and_literal_eq_interval C hM hW hσA hσLA hpart hLI hIL hq₁ hq₂]
    exact hpart.excl q₁ hq₁ q₂ hq₂ hne

/-- **One day of the transfer**: a mixture of `𝒱`-worlds (each consistent with the stage) that
partitions at the interval states, agrees with the base on the small sentences, and has faith
at the pinned coordinate on every candidate *at the interval states*, forces the exact identity
on the cell literals at that coordinate — `Determination.nnu_day` applied after the partition
and the faith clause are transferred to the literal states.
Source: this run (audit r1 B1); mandate K2 (b)/(c), § Attempt angles (B)
Kind: C
Fidelity: exact (one day; faith at the interval states)
Hyps: (a); `hLI`/`hIL` are reflection facts about the mixture's world class (instance data) -/
theorem interval_nnu_day {n : ℕ} (h𝒱 : ∀ v, 𝒱 v → v.ConsistentWith (DP.D n))
    (hcoh : CoherentOnW 𝒱 (smallAtoms n ∪ atoms n) (P n))
    (hatomsI : stateAtoms σI S n ⊆ atoms n) (hatoms : stateAtoms (stateOf C) S n ⊆ atoms n)
    (hpart : PartitionAt σI S (P n) (n + 1)) (hE1 : E1x Q P)
    (hLI : ∀ v, 𝒱 v → ∀ q ∈ S.states (n + 1),
      v.Holds (stateOf C (n + 1) q) → v.Holds (σI (n + 1) q))
    (hIL : ∀ v, 𝒱 v → ∀ q ∈ S.states (n + 1), v.Holds (σI (n + 1) q) →
      (∀ q' ∈ S.states (n + 1), q' ≠ q → ¬ v.Holds (σI (n + 1) q')) →
        v.Holds (stateOf C (n + 1) q))
    (hsp : SpuriousEntails (stateOf C) C.literal S index C.cells n)
    (hval : ValuesAtRep C S index n) {c : ℕ} (hc : c ∈ pinned C index n)
    (hfaith : ∀ q ∈ S.states (n + 1),
      P n (sentenceOfCode c ⋏ σI (n + 1) q) =
        S.val (n + 1) q (sentenceOfCode c) * P n (σI (n + 1) q))
    (hφn : sentenceOfCode c ∈ smallSet n) :
    Q n (sentenceOfCode c) =
      ∑ r ∈ C.cells (n + 1), (C.rep (n + 1) r : ℝ) * Q n (C.literal (n + 1) (sentenceOfCode c) r) := by
  obtain ⟨k, W, w, hW, hM⟩ := (coherentOnW_iff _ _ _).1 hcoh
  have hσA : ∀ q ∈ S.states (n + 1), sentenceAtomCodes (σI (n + 1) q) ⊆ smallAtoms n ∪ atoms n :=
    fun q hq => (atoms_subset_stateAtoms σI S hq).trans (hatomsI.trans Finset.subset_union_right)
  have hσLA : ∀ q ∈ S.states (n + 1),
      sentenceAtomCodes (stateOf C (n + 1) q) ⊆ smallAtoms n ∪ atoms n := fun q hq =>
    (atoms_subset_stateAtoms (stateOf C) S hq).trans (hatoms.trans Finset.subset_union_right)
  have hcA : sentenceAtomCodes (sentenceOfCode c) ⊆ smallAtoms n ∪ atoms n :=
    (atoms_subset_smallAtoms hφn).trans Finset.subset_union_left
  have hcoh' : CoherentOn (DP.D n) (smallAtoms n ∪ atoms n) (P n) :=
    (coherentOn_iff_coherentOnW _ _ _).2 (Cleanroom.Bli.BliLinkageB.CoherentOnW.mono h𝒱 hcoh)
  have hpartL : PartitionAt (stateOf C) S (P n) (n + 1) :=
    partitionAt_literal_of_interval C hM hW hσA hσLA hpart hLI hIL
  have hfaithL : ∀ q ∈ S.states (n + 1),
      P n (sentenceOfCode c ⋏ stateOf C (n + 1) q) =
        S.val (n + 1) q (sentenceOfCode c) * P n (stateOf C (n + 1) q) := fun q hq => by
    rw [mixture_and_literal_eq_interval C hM hW hσA hσLA hpart hLI hIL hcA hq,
      mixture_literal_eq_interval C hM hW hσA hσLA hpart hLI hIL hq]
    exact hfaith q hq
  exact nnu_day C hcoh' hatoms hpartL hE1 hsp hval hc hfaithL hφn

/-- **The transfer theorem — angle B's decisive question, answered over mixtures of worlds that
reflect the literals: the trilemma stands under interval linkage with price-reflected
literals.** Let `σI` be an interval state family and `C`
a cell-literal family, and let every day's superbelief `P n` be a mixture of worlds of a class
`𝒱 n` (each consistent with the stage `DP.D n`) on which (`hLI`) a candidate's literal state
entails its interval state — the closed cell lies inside the open cell — and (`hIL`) a
*uniquely held* interval state entails the literal state — a price in exactly one open cell
lies in that cell's closed cell. Then the interval-state package `E5σ σI ∧ E1x Q P ∧ E2xσIdx σI`
(partition and faith at the *interval* states, as angle B's linkage prescribes), over a grid
with `SpuriousEntails`/`ValuesAtRep` and pinned coordinates in scope, forces the **exact**
identity `D_NNUcell C index Q` on the cell literals. The overlaps of the forced open cells
(bli-found F-16) are no resource: exclusivity in `P`-measure at the interval states keeps every
charged world off them, and off the overlaps the open cells behave as the closed partition.
What the round-0 "dissolution" exhibited is the complement: literals *not* reflected to the
price (no `hLI`/`hIL`) are unconstrained. Both auditors sketched this; here it is a theorem.
Source: this run (audit r1 B1, fidelity § 2 and adversarial § 2 sketches); mandate § Attempt angles (B, "if it does not … prove that and the trilemma stands under both linkages"); [[bli-program]] §3.6(ii)
Kind: C
Fidelity: exact (faith at the interval states, index-restricted `E2xσIdx`; the mixture's world class is a parameter with the two reflection facts as hypotheses)
Hyps: (a); (c) inherited: `Sminus` scope through `E2xσIdx` (bli-found F-14); `hLI`/`hIL` are reflection facts about the world class (instance data, discharged at the witness by `wClass_LI`/`wClass_IL`) -/
theorem interval_determination (σI : ℕ → ℕ → Sentence) (𝒱 : ℕ → PCWorld → Prop)
    (h𝒱 : ∀ n v, 𝒱 n v → v.ConsistentWith (DP.D n))
    (hcoh : ∀ n, CoherentOnW (𝒱 n) (smallAtoms n ∪ atoms n) (P n))
    (hatomsI : ∀ n, stateAtoms σI S n ⊆ atoms n)
    (hatoms : ∀ n, stateAtoms (stateOf C) S n ⊆ atoms n)
    (hE5 : E5σ σI S P) (hE1 : E1x Q P) (hE2 : E2xσIdx σI index S P)
    (hLI : ∀ n v, 𝒱 n v → ∀ q ∈ S.states (n + 1),
      v.Holds (stateOf C (n + 1) q) → v.Holds (σI (n + 1) q))
    (hIL : ∀ n v, 𝒱 n v → ∀ q ∈ S.states (n + 1), v.Holds (σI (n + 1) q) →
      (∀ q' ∈ S.states (n + 1), q' ≠ q → ¬ v.Holds (σI (n + 1) q')) →
        v.Holds (stateOf C (n + 1) q))
    (hsp : ∀ n, SpuriousEntails (stateOf C) C.literal S index C.cells n)
    (hval : ∀ n, ValuesAtRep C S index n)
    (hscope : ∀ n, ∀ c ∈ pinned C index n,
      sentenceOfCode c ∈ smallSet n ∧ sentenceOfCode c ∈ Sminus (n + 1) (n + 1)) :
    D_NNUcell C index Q := by
  intro n c hc
  have hcidx : c ∈ index (n + 1) := ((mem_pinned C index n c).1 hc).1
  exact interval_nnu_day C (h𝒱 n) (hcoh n) (hatomsI n) (hatoms n) (partitionAt_of_E5σ hE5 n)
    hE1 (hLI n) (hIL n) (hsp n) (hval n) hc
    (fun q hq => hE2 n (n + 1) (Nat.lt_succ_self n) q hq c hcidx (hscope n c hc).2)
    (hscope n c hc).1

end Transfer

/-! ## 4. The transfer theorem's hypotheses are inhabited (N+): the price-coupled witness -/

section WitnessInstance

/-- **The class of price-coupled witness worlds**: `wld x b a` with the literal index `a` the
cell of the price `x` (the price strictly inside cell `a`'s open neighbourhood), `a ≤ 1`,
`x ∈ (−1, 2)`. Every world of `wP` is one (`wWorld_eq`).
Source: none: witness
Kind: D
Fidelity: n/a -/
def wClass (v : PCWorld) : Prop :=
  ∃ (x : ℚ) (b : Bool) (a : ℕ), a ≤ 1 ∧ -1 < x ∧ x < 2 ∧ (∀ m, dLo m a < x ∧ x < dHi m a) ∧
    v = wld x b a

/-- Every world of `wP` is in the class.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wWorld_wClass (i : Fin 4) : wClass (wWorld i) := by
  obtain ⟨x, b, a, ha, h1, h2, hcell, h⟩ := wWorld_eq i
  exact ⟨x, b, a, ha, h1, h2, hcell, h⟩

/-- `wP n` is a mixture of class worlds on every atom set.
Source: none: witness
Kind: L
Fidelity: n/a -/
theorem wCoherentOnW (A : Finset ℕ) (n : ℕ) : CoherentOnW wClass A (wP n) :=
  ⟨4, wWorld, dW, wWorld_wClass, dW_nonneg, dW_sum, fun _ _ => rfl⟩

/-- Class worlds are consistent with every stage of `dDP`.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wClass_consistent (n : ℕ) (v : PCWorld) (hv : wClass v) : v.ConsistentWith (dDP.D n) := by
  obtain ⟨x, b, a, -, h1, h2, -, rfl⟩ := hv
  exact wld_consistentWithTheory h1 h2 b a n

/-- A class world holds the literal state of `dCode r` iff `r` is its literal index.
Source: none: witness
Kind: L
Fidelity: n/a -/
lemma wld_holds_wσ (x : ℚ) (b : Bool) (a m r : ℕ) :
    (wld x b a).Holds (wσ m (dCode r)) ↔ r = a := by
  rw [wσ_dCode, PCWorld.holds_and, wld_holds_dLit]
  exact ⟨fun h => h.1, fun h => ⟨h, PCWorld.holds_top _⟩⟩

/-- **`hLI` at the witness**: a class world holding the literal state of a candidate holds its
interval state (the price lies in the open neighbourhood of its own cell).
Source: none: witness
Kind: L
Fidelity: n/a -/
theorem wClass_LI (m : ℕ) (v : PCWorld) (hv : wClass v) :
    ∀ q ∈ wS.states m, v.Holds (wσ m q) → v.Holds (dσ m q) := by
  obtain ⟨x, b, a, -, -, -, hcell, rfl⟩ := hv
  intro q hq hL
  rw [wS_states, mem_dStates] at hq
  rcases hq with rfl | rfl <;>
  · rw [wld_holds_wσ] at hL
    rw [wld_holds_dσ, hL]
    exact hcell m

/-- **`hIL` at the witness**: a class world holding the interval state of a candidate and no
other candidate's interval state holds the candidate's literal state (the price is in the open
neighbourhood of its own cell `a`, so by uniqueness the candidate is `dCode a`).
Source: none: witness
Kind: L
Fidelity: n/a -/
theorem wClass_IL (m : ℕ) (v : PCWorld) (hv : wClass v) :
    ∀ q ∈ wS.states m, v.Holds (dσ m q) →
      (∀ q' ∈ wS.states m, q' ≠ q → ¬ v.Holds (dσ m q')) → v.Holds (wσ m q) := by
  obtain ⟨x, b, a, ha, -, -, hcell, rfl⟩ := hv
  intro q hq _ huniq
  have haS : dCode a ∈ wS.states m := by
    rw [wS_states, mem_dStates]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hIa : (wld x b a).Holds (dσ m (dCode a)) := (wld_holds_dσ _ _ _ _ _).2 (hcell m)
  have hqa : dCode a = q := by
    by_contra hne
    exact huniq (dCode a) haS hne hIa
  rw [← hqa, wld_holds_wσ]

/-- **The transfer theorem's hypotheses are inhabited (N+)**: `wP` over the class of
price-coupled witness worlds, at the interval states `dσ` and the literal family `wCF`,
satisfies every hypothesis of `interval_determination` — `E5σ dσ`, `E1x`, `E2xσIdx dσ`
(from `E2xσ dσ`), the two reflection facts, the grid conditions and the scope — with both
candidates charged `1/2` and the base at `1/2` on the coordinate; and the conclusion
`D_NNUcell wCF dIndex wP` is the identity `1/2 = 1/4 · 1/2 + 3/4 · 1/2`, checked independently
by `dissolution_package_with_coupled_literals`.
Source: this run (audit r1 B1); [[STANDARDS]] §3
Kind: N+
Fidelity: n/a (abstract worlds; the process `dDP` decides no price; `P = Q`)
Hyps: (a) -/
theorem interval_determination_witness :
    D_NNUcell wCF dIndex wP ∧
      (∀ n, wP n (dσ (n + 1) (dCode 0)) = 1 / 2 ∧ wP n (dσ (n + 1) (dCode 1)) = 1 / 2) ∧
      (∀ n, wP n dPhi = 1 / 2) := by
  refine ⟨?_, fun n => ⟨?_, ?_⟩, wP_dPhi⟩
  · exact interval_determination wCF dσ (fun _ => wClass) wClass_consistent
      (fun n => wCoherentOnW (smallAtoms n ∪ (stateAtoms dσ wS n ∪ stateAtoms wσ wS n)) n)
      (fun n => Finset.subset_union_left) (fun n => Finset.subset_union_right)
      wE5σ_dσ wE1x (e2xσIdx_of_e2xσ dIndex wE2xσ_dσ) (fun n => wClass_LI (n + 1))
      (fun n => wClass_IL (n + 1)) wSpuriousEntails wValuesAtRep wScope
  · rw [wP_dσ_eq n (n + 1) (by simp [dStates])]; exact (wP_state n (n + 1)).1
  · rw [wP_dσ_eq n (n + 1) (by simp [dStates])]; exact (wP_state n (n + 1)).2

end WitnessInstance

end Cleanroom.Bli.BliLinkage
