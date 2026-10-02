import Cleanroom.Bli.BliLinkage.Defs
import Cleanroom.Bli.BliLinkageB.Trilemma
import Cleanroom.Bli.BliLinkage.AttemptA.Trilemma

/-!
# `bli-linkage` — K2's trilemma: the three horns, sharpness, and the dissolution under
interval-only linkage (of record)

The witnesses of record are **attempt B's** (`BliLinkageB.Trilemma`, `Witness`, `Dissolve`),
restated here over the record definitions: one coordinate `φ₀`, two cells with the `halfRound`
neighbourhoods and representatives `1/4, 3/4`, two candidate tables of distinct code, a
four-world market `wP` charging each candidate `1/2`. Attempt A built an independent second
set over its own abstract instance (`AttemptA.Trilemma`: `T1_coherent_agreeing_not_faithful`,
`T3_coherent_faithful_not_agreeing`, `T2_agreeing_faithful_not_coherent`, `sharp`,
`free_marginal_day_zero`; two tables charged `1/4`/`3/4`, pinned day `2`) — cited in the ledger
as corroboration, not restated (they are over attempt A's family, which converts only with
genuineness side conditions).

**What the two attempts agree on, independently** (the reconciliation's most robust output):
the mandate's T2 recipe ("the degenerate `P` by cases, `small ψ ↦ Q n ψ`") cannot work, because
`E1x` transfers faith and partition to the base once the state sentences are small
(`Determination.no_T2_over_coherent_base`, B's `no_T2_over_dP`); the honest T2 is over an
*incoherent base* (`P = Q`). Both sharpness witnesses are four-world mixtures, not the
mandate's `tentSkeleton` trajectory law (not built by either attempt; disclosed).

**Angle B's decisive question** — corrected in repair round 1 (audit r1 B1, both lenses).
Round 0 read `dissolution` as "the trilemma dissolves under interval-only linkage". It does
not: the dissolution witness's cell literals are fresh atoms that hold in every world of `dP`
whatever the price (`Interval.dCF_literals_decoupled`), so its `¬ D_NNUcell` is the equation
`1/2 ≠ 1/4 · 0 + 3/4 · 1` about atoms the quotes never constrain
(`Interval.dissolution_violation_is_decoupling`). The same market with price-coupled literals
satisfies the identical interval-state package with `D_NNUcell` **true**
(`Interval.dissolution_package_with_coupled_literals`), and the general transfer theorem
`Interval.interval_determination` shows that with price-reflected literals the interval-state
package `E5σ ∧ E1x ∧ E2xσIdx` at the interval states forces the exact identity: the trilemma
**stands** under interval linkage. `dissolution` is kept, relabelled **N−**, as the record that
unreflected literals are unconstrained.
-/

namespace Cleanroom.Bli.BliLinkage

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound
open Cleanroom.Bli.BliLinkageB.Dissolve Cleanroom.Bli.BliLinkageB.Witness

/-- **The determination theorem's hypothesis package is inhabited (N+)** by a two-state,
distinct-table, two-cell market with faith as conditioning (`wP` over `wS`, process `dDP`):
`PCPσ ∧ E5σ ∧ E1x ∧ E2xσ`, `SpuriousEntails`, `ValuesAtRep`, the pinned set eventually
non-empty, both candidates charged `1/2`, the base at `1/2` on the coordinate; and `D_NNUcell`
holds. Abstract worlds (the process `dDP` decides no price); the B2 instance over `paperDP`'s
stages is not built (see `InstanceB2` for why no two-state instance exists on `[⌜⊥⌝, ⌜⊤⌝]`).
Source: mandate K2 (N+); [[STANDARDS]] §3; attempt B `Witness.determination_package_inhabited`
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem determination_package_inhabited :
    PCPσ (stateAtoms wσ wS) dDP wP ∧ E5σ wσ wS wP ∧ E1x wP wP ∧ E2xσ wσ wS wP ∧
      (∀ n, SpuriousEntails wσ dLit wS dIndex dCells n) ∧ (∀ n, ValuesAtRep wCF wS dIndex n) ∧
      (∃ N, ∀ n ≥ N, dC0 ∈ pinned wCF dIndex n) ∧
      dCode 0 ≠ dCode 1 ∧ (∀ n, 0 < wP n (wσ (n + 1) (dCode 0)) ∧ 0 < wP n (wσ (n + 1) (dCode 1))) ∧
      (∀ n, wP n dPhi = 1 / 2) ∧
      D_NNUcell wCF dIndex wP :=
  Cleanroom.Bli.BliLinkageB.Witness.determination_package_inhabited

/-- **T1 — drop faith.** `wP` over the representatives `rep1` (`0`, `1/2`) moved off the
conditional values and the system `t1S` valuing at them: `PCPσ ∧ E1x ∧ E5σ` hold with
`ValuesAtRep`, both candidates charged `1/2`; faith fails at `(n, m, q, φ) = (0, 1, dCode 1, φ₀)`
(`3/8 ≠ 1/2 · 1/2`) and `D_NNUcell` fails (`1/2 ≠ 0 · 1/2 + 1/2 · 1/2`).
Source: [[bli-program]] §3.6(ii); mandate K2 (T1); attempt B `Trilemma.trilemma_T1`
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem trilemma_T1 (atoms : ℕ → Finset ℕ) :
    PCPσ atoms dDP wP ∧ E1x wP wP ∧ E5σ wσ Cleanroom.Bli.BliLinkageB.Trilemma.t1S wP ∧
      (∀ n, ValuesAtRep Cleanroom.Bli.BliLinkageB.Trilemma.t1CF
        Cleanroom.Bli.BliLinkageB.Trilemma.t1S dIndex n) ∧
      ¬ E2xσ wσ Cleanroom.Bli.BliLinkageB.Trilemma.t1S wP ∧
      ¬ D_NNUcell Cleanroom.Bli.BliLinkageB.Trilemma.t1CF dIndex wP ∧
      (∀ n, wP n (wσ (n + 1) (dCode 0)) = 1 / 2 ∧ wP n (wσ (n + 1) (dCode 1)) = 1 / 2) :=
  Cleanroom.Bli.BliLinkageB.Trilemma.trilemma_T1 atoms

/-- **T2 — drop coherence.** `tP` (`wP` with the coordinate `φ₀` repriced at `1/4`) over itself:
`E1x ∧ E2xσ ∧ E5σ` hold, both candidates charged `1/2`, `D_NNUcell wCF` fails
(`1/4 ≠ 1/4 · 1/2 + 3/4 · 1/2`), and coherence fails on every atom set containing the state
atoms, on some day (`¬ PCPσ` is an existential over days) — derived from the determination
theorem. **Not the mandate's case-defined market**, which
violates `E1x` (`Determination.no_T2_over_coherent_base`; B's FB-15, A's F-A4).
Source: mandate K2 (T2); attempt B `Trilemma.trilemma_T2`
Kind: N+
Fidelity: variant: an incoherent base in place of the mandate's case-defined market over a coherent base (which cannot exist)
Hyps: (a) -/
theorem trilemma_T2 :
    E1x Cleanroom.Bli.BliLinkageB.Trilemma.tP Cleanroom.Bli.BliLinkageB.Trilemma.tP ∧
      E2xσ wσ wS Cleanroom.Bli.BliLinkageB.Trilemma.tP ∧
      E5σ wσ wS Cleanroom.Bli.BliLinkageB.Trilemma.tP ∧
      (∀ atoms, (∀ n, stateAtoms wσ wS n ⊆ atoms n) →
        ¬ PCPσ atoms dDP Cleanroom.Bli.BliLinkageB.Trilemma.tP) ∧
      ¬ D_NNUcell wCF dIndex Cleanroom.Bli.BliLinkageB.Trilemma.tP ∧
      (∀ n, Cleanroom.Bli.BliLinkageB.Trilemma.tP n (wσ (n + 1) (dCode 0)) = 1 / 2 ∧
        Cleanroom.Bli.BliLinkageB.Trilemma.tP n (wσ (n + 1) (dCode 1)) = 1 / 2) :=
  Cleanroom.Bli.BliLinkageB.Trilemma.trilemma_T2

/-- **T3 — drop agreement.** `wP` as superbelief over the base `dP` (which violates
`D_NNUcell wCF`): `PCPσ ∧ E2xσ ∧ E5σ` hold, both candidates charged `1/2`, and `E1x dP wP` fails
on the pinned literal `lit_{n+1, φ₀, 0}` (`1/2 ≠ 0`) from the day it is small.
Source: mandate K2 (T3); attempt B `Trilemma.trilemma_T3`
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem trilemma_T3 (atoms : ℕ → Finset ℕ) :
    PCPσ atoms dDP wP ∧ E2xσ wσ wS wP ∧ E5σ wσ wS wP ∧ ¬ E1x dP wP ∧
      ¬ D_NNUcell wCF dIndex dP ∧
      (∀ n, wP n (wσ (n + 1) (dCode 0)) = 1 / 2 ∧ wP n (wσ (n + 1) (dCode 1)) = 1 / 2) :=
  Cleanroom.Bli.BliLinkageB.Trilemma.trilemma_T3 atoms

/-- **T0 at the witness base**: over `dP` (violating `D_NNUcell wCF`), no `P` satisfies the full
package at `(wCF, wS, dIndex)`.
Source: mandate K2 (T0); attempt B `Trilemma.trilemma_T0_witness`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem trilemma_T0_witness (atoms : ℕ → Finset ℕ) (hatoms : ∀ n, stateAtoms wσ wS n ⊆ atoms n)
    (P : History) :
    ¬ (PCPσ atoms dDP P ∧ E1x dP P ∧ E2xσ wσ wS P ∧ E5σ wσ wS P) :=
  Cleanroom.Bli.BliLinkageB.Trilemma.trilemma_T0_witness atoms hatoms P

/-- **Sharpness**: all three constraints and `D_NNUcell wCF` hold together for `wP` — each horn is
necessary. A four-world mixture, not an inductor (disclosed: the mandate's `tentSkeleton`
trajectory-law base was not built by either attempt).
Source: [[bli-program-desiderata]] I6; mandate K2 ("Sharpness"); attempt B `Trilemma.trilemma_sharp`
Kind: N+
Fidelity: variant: a four-world mixture base in place of the trajectory law
Hyps: (a) -/
theorem trilemma_sharp (atoms : ℕ → Finset ℕ) :
    PCPσ atoms dDP wP ∧ E1x wP wP ∧ E2xσ wσ wS wP ∧ E5σ wσ wS wP ∧ D_NNUcell wCF dIndex wP ∧
      (∀ n, wP n (wσ (n + 1) (dCode 0)) = 1 / 2 ∧ wP n (wσ (n + 1) (dCode 1)) = 1 / 2) :=
  Cleanroom.Bli.BliLinkageB.Trilemma.trilemma_sharp atoms

/-- **"Drop coherence" is empty over the dissolution base**: no `P` satisfies `E1x dP P ∧ E2xσ`
at the literal states — `E1x` transfers faith to the base once the faith sentences are small, and
`dP n (φ₀ ⋏ σ_1) = 1/2 ≠ 3/4 = val · dP n σ_1`.
Source: this run (B's FB-15); attempt B `Trilemma.no_T2_over_dP`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem no_T2_over_dP (P : History) : ¬ (E1x dP P ∧ E2xσ (stateOf dCF) dS P) :=
  Cleanroom.Bli.BliLinkageB.Trilemma.no_T2_over_dP P

/-- **The interval-state package with cell literals decoupled from the price (N−; not a
dissolution).** With the interval state sentence `dσ = intervalState dQuote dLo dHi` (linked
to the quotes only), the package `LNKcell ∧ PCPσTheory ∧ PCPσLinked ∧ E5σ ∧ E1x ∧ E2xσ` holds
over `dP`, the pinned set is eventually non-empty, and `D_NNUcell dCF dIndex dP` is false —
**because `dCF`'s literals are fresh atoms the process never relates to the quoted price**:
the literal of cell `1` holds in every world of `dP`, including the two priced in cell `0`
(`Interval.dCF_literals_decoupled`), so the violation is `1/2 ≠ 1/4 · 0 + 3/4 · 1`
(`Interval.dissolution_violation_is_decoupling`). The quotes *are* reflected to each world's
price (`wld_holds_dQuote`). What the witness shows is that unreflected literals are
unconstrained by the quotes; it shows nothing about interval linkage. With price-coupled
literals the same package holds with `D_NNUcell` true
(`Interval.dissolution_package_with_coupled_literals`), and in general price-reflected literals
make the interval-state package force the exact identity (`Interval.interval_determination`).
Round 0 called this "the headline negative result"; that reading was an artifact of the
encoding (audit r1 B1, both lenses) and is withdrawn.
Source: mandate § Attempt angles (B, decisive question); attempt B `Dissolve.dissolution`; audit r1 B1
Kind: N-
Fidelity: variant: the cell literals are atoms decoupled from the price (literal `1` holds in every world of `dCF`'s class), so `¬ D_NNUcell` is `1/2 ≠ 3/4`; the quotes are reflected to the world's price; `P = Q`
Hyps: (a) -/
theorem dissolution :
    LNKcell dσ dQuote dS (cellOfTable dLo dHi) dDP ∧
      PCPσTheory (stateAtoms dσ dS) dDP dP ∧
      Cleanroom.Bli.BliLinkageB.PCPσLinked dσ dQuote dS (cellOfTable dLo dHi) (stateAtoms dσ dS) dDP dP ∧
      E5σ dσ dS dP ∧ E1x dP dP ∧ E2xσ dσ dS dP ∧
      (∃ N, ∀ n ≥ N, dC0 ∈ pinned dCF dIndex n) ∧
      ¬ D_NNUcell dCF dIndex dP :=
  Cleanroom.Bli.BliLinkageB.Dissolve.dissolution

/-- **Charge profile of the decoupled witness**: two candidates of distinct code, each charged
`1/2`, two cells, the base at `1/2` on the coordinate. Two states are charged, but the witness
is N− for the reason in `dissolution`'s docstring: its literals do not mean "the price is in
cell `r`", so the two-state charge exercises nothing about the identity.
Source: mandate K2 (witness grades); attempt B `Dissolve.dissolution_nondegenerate`; audit r1 B1
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem dissolution_nondegenerate (n : ℕ) :
    dCode 0 ≠ dCode 1 ∧ 0 < dP n (dσ (n + 1) (dCode 0)) ∧ 0 < dP n (dσ (n + 1) (dCode 1)) ∧
      (dCells (n + 1)).card = 2 ∧ dP n dPhi = 1 / 2 :=
  Cleanroom.Bli.BliLinkageB.Dissolve.dissolution_nondegenerate n

/-- **The bracket determination theorem (angle B's K1, interval form), lower bracket**: over a
linked coherent stage mixture (`PCPσLinked`) with partition and small agreement, the mass of the
candidates whose closed cell lies strictly inside the open `I` is at most the base's price of
tomorrow's quote of `I`. Equality 4′ fails for interval quotes (bli-found F-16); the bracket is
what survives.
Source: mandate § Attempt angles (B); [[bli-program]] §3.6(i); attempt B `Bracket.bracket_lower_day`
Kind: C
Fidelity: variant: interval linkage, lower bracket in place of 4′'s equality
Hyps: (a) -/
theorem bracket_lower_day {σ : ℕ → ℕ → Sentence} {quote : ℕ → Sentence → ℚ → ℚ → Sentence}
    {S : StateSystem} {cellOf : ℕ → ℕ → Sentence → ℚ × ℚ} {atoms : ℕ → Finset ℕ}
    {DP : DeductiveProcess} {P Q : History}
    (hcoh : Cleanroom.Bli.BliLinkageB.PCPσLinked σ quote S cellOf atoms DP P)
    (hatoms : ∀ n, stateAtoms σ S n ⊆ atoms n) (hE5 : E5σ σ S P) (hE1 : E1x Q P) (n : ℕ)
    {φ : Sentence} (hφ : φ ∈ smallSet (n + 1)) (I : ℚ × ℚ)
    (hsmall : quote (n + 1) φ I.1 I.2 ∈ smallSet n) :
    ∑ q ∈ (S.states (n + 1)).filter
        (fun q => Cleanroom.Bli.BliLinkageB.CellInside cellOf (n + 1) q φ I), P n (σ (n + 1) q) ≤
      Q n (quote (n + 1) φ I.1 I.2) :=
  Cleanroom.Bli.BliLinkageB.bracket_lower_day hcoh hatoms hE5 hE1 n hφ I hsmall

/-- **The bracket determination theorem, upper bracket.**
Source: mandate § Attempt angles (B); attempt B `Bracket.bracket_upper_day`
Kind: C
Fidelity: variant: interval linkage, upper bracket
Hyps: (a) -/
theorem bracket_upper_day {σ : ℕ → ℕ → Sentence} {quote : ℕ → Sentence → ℚ → ℚ → Sentence}
    {S : StateSystem} {cellOf : ℕ → ℕ → Sentence → ℚ × ℚ} {atoms : ℕ → Finset ℕ}
    {DP : DeductiveProcess} {P Q : History}
    (hcoh : Cleanroom.Bli.BliLinkageB.PCPσLinked σ quote S cellOf atoms DP P)
    (hatoms : ∀ n, stateAtoms σ S n ⊆ atoms n) (hE5 : E5σ σ S P) (hE1 : E1x Q P) (n : ℕ)
    {φ : Sentence} (hφ : φ ∈ smallSet (n + 1)) (I : ℚ × ℚ)
    (hsmall : quote (n + 1) φ I.1 I.2 ∈ smallSet n) :
    Q n (quote (n + 1) φ I.1 I.2) ≤
      ∑ q ∈ (S.states (n + 1)).filter
        (fun q => Cleanroom.Bli.BliLinkageB.CellMeets cellOf (n + 1) q φ I), P n (σ (n + 1) q) :=
  Cleanroom.Bli.BliLinkageB.bracket_upper_day hcoh hatoms hE5 hE1 n hφ I hsmall

/-- **Theory-level coherence plus small agreement decides tomorrow's quotes** (B's FB-3): for any
`IntervalFamily` (any quote family reflected to a fixed price, FAF's `quoteAt` included), under
`PCPσTheory ∧ E1x` the base prices every small next-day quote at `1` (price strictly inside) or
`0` (strictly outside). So the theory-level package is degenerate over any base uncertain about a
small next-day quote; the stage-level forms are the ones of record.
Source: this run (B's FB-3); mandate § Definitions (`PCPσTheory`), K4; attempt B `Bracket.theory_coherent_e1x_decides`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem theory_coherent_e1x_decides {DP : DeductiveProcess} (F : IntervalFamily DP)
    {atoms : ℕ → Finset ℕ} {P Q : History} (hcoh : PCPσTheory atoms DP P) (hE1 : E1x Q P)
    (n : ℕ) (φ : Sentence) (lo hi : ℚ) (hsmall : F.quote (n + 1) φ lo hi ∈ smallSet n) :
    (lo < F.price (n + 1) φ → F.price (n + 1) φ < hi → Q n (F.quote (n + 1) φ lo hi) = 1) ∧
      ((F.price (n + 1) φ < lo ∨ hi < F.price (n + 1) φ) → Q n (F.quote (n + 1) φ lo hi) = 0) :=
  Cleanroom.Bli.BliLinkageB.theory_coherent_e1x_decides F hcoh hE1 n φ lo hi hsmall

end Cleanroom.Bli.BliLinkage
