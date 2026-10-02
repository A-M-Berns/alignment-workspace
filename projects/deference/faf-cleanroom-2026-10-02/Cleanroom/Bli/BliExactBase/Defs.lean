import Cleanroom.Bli.BliLinkage.Defs
import Cleanroom.Bli.BliLinkageB.Mixture

/-!
# `bli-exact-base` — definitions of record: the segment forms of the base constraints

The package's claims about the splice (`Splice.lean`) are about a **finite segment** of days
`[0, H)` (and, for the linked claims, `[N₀, H)`). This module fixes the segment forms of
`bli-found`'s base predicates `D_PC` and `D_ND`, with `∀ n` replaced by `∀ n < H`, proves that the
all-horizons forms are the originals (`D_PC_on_forall_iff`, `D_ND_on_forall_iff`), and introduces
the **small-sentence coherence** `CoherentOnSmall` that the segment claim of record uses.

**Why a small-sentence form.** `bli-found`'s `CoherentOn D A p` asks `p` to be a stage mixture
on *every* sentence whose atoms lie in `A` — the whole (infinite) Boolean algebra over `A`,
including the atom-free tautologies `⊤ ⋎ ⊥ ⋎ … ⋎ ⊥` of every length. A finite-support
perturbation of FAF's LIA prices all but finitely many of those at the LIA's `0`
(`Tables.not_coherentOn_of_finiteSupportPerturbation`), so **no splice is `D_PC_on H` for any
`H ≥ 1`, and FAF's LIA is `D_PC` over no process** (`Tables.not_D_PC_lia`). The program's words
— "propositionally coherent *on the small sentences*" ([[bli-program]] §2.6) — are
`CoherentOnSmall D n p`: a stage mixture that agrees with `p` on `smallSet n`. It is exactly what
`bli-linkage`'s package `PCPσ ∧ E1x` forces on the base on one day
(`coherentOnSmall_iff_exists_mixture_agree`), and it is what the splice carries on its segment.
-/

namespace Cleanroom.Bli.BliExactBase

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliLinkageB

/-! ## Segment forms -/

/-- **`D_PC` on the segment `[0, H)`**: `bli-found`'s `D_PC` with `∀ n` replaced by `∀ n < H`
(coherence on the whole algebra over the day-`n` small atoms, relative to `DP.D n`).
Source: mandate § Definitions (`D_PC_on`); bli-found `Constraints.D_PC`
Kind: D
Fidelity: exact (segment form) -/
def D_PC_on (H : ℕ) (Q : History) (DP : DeductiveProcess) : Prop :=
  ∀ n, n < H → CoherentOn (DP.D n) (smallAtoms n) (Q n)

/-- **`D_ND` on the segment `[0, H)`**: every day-`n` small sentence, `n < H`, is decided true by
the stage, decided false by it, or priced strictly inside `(0, 1)`.
Source: mandate § Definitions (`D_ND_on`); bli-found `Constraints.D_ND`
Kind: D
Fidelity: exact (segment form) -/
def D_ND_on (H : ℕ) (Q : History) (DP : DeductiveProcess) : Prop :=
  ∀ n, n < H → ∀ φ ∈ smallSet n,
    (∀ v : PCWorld, v.ConsistentWith (DP.D n) → v.Holds φ) ∨
    (∀ v : PCWorld, v.ConsistentWith (DP.D n) → ¬ v.Holds φ) ∨
    (0 < Q n φ ∧ Q n φ < 1)

/-- The all-horizons segment form is `D_PC`.
Source: mandate § Definitions ("prove `D_PC_on`-for-all-`H` ↔ `D_PC`")
Kind: L
Fidelity: n/a -/
theorem D_PC_on_forall_iff (Q : History) (DP : DeductiveProcess) :
    (∀ H, D_PC_on H Q DP) ↔ D_PC Q DP :=
  ⟨fun h n => h (n + 1) n (Nat.lt_succ_self n), fun h _ n _ => h n⟩

/-- The all-horizons segment form is `D_ND`.
Source: mandate § Definitions
Kind: L
Fidelity: n/a -/
theorem D_ND_on_forall_iff (Q : History) (DP : DeductiveProcess) :
    (∀ H, D_ND_on H Q DP) ↔ D_ND Q DP :=
  ⟨fun h n => h (n + 1) n (Nat.lt_succ_self n), fun h _ n _ => h n⟩

/-! ## Small-sentence coherence -/

/-- **Coherence on the day-`n` small sentences**: `p` agrees, on `smallSet n`, with a convex
combination of the payouts of finitely many worlds consistent with the stage `D`. The
small-sentence restriction of `bli-found`'s `CoherentOn D (smallAtoms n)` (which quantifies over
the whole algebra over the small atoms); see the module docstring for why the restriction is the
statement of record for a finite-support perturbation of the LIA.
Source: [[bli-program]] §2.6 ("propositionally coherent on the small sentences"); mandate § 2
Kind: D
Fidelity: weaker: agreement with a stage mixture on `smallSet n` only, not on the algebra it generates -/
def CoherentOnSmall (D : Finset Sentence) (n : ℕ) (p : Sentence → ℝ) : Prop :=
  ∃ (k : ℕ) (W : Fin k → PCWorld) (w : Fin k → ℝ),
    (∀ i, (W i).ConsistentWith D) ∧ (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    ∀ φ ∈ smallSet n, p φ = ∑ i, w i * (W i).payout φ

/-- **`D_PC` in small-sentence form, all days.**
Source: [[bli-program]] §2.6; mandate § 2
Kind: D
Fidelity: weaker: small sentences only -/
def D_PCsmall (Q : History) (DP : DeductiveProcess) : Prop :=
  ∀ n, CoherentOnSmall (DP.D n) n (Q n)

/-- **`D_PC` in small-sentence form on the segment `[0, H)`** — the segment claim of record for
the splice (`Tables.segment_D_PCsmall_on`).
Source: [[bli-program]] §2.6; mandate § 2
Kind: D
Fidelity: weaker: small sentences only; segment form -/
def D_PCsmall_on (H : ℕ) (Q : History) (DP : DeductiveProcess) : Prop :=
  ∀ n, n < H → CoherentOnSmall (DP.D n) n (Q n)

/-- The all-horizons segment form is `D_PCsmall`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem D_PCsmall_on_forall_iff (Q : History) (DP : DeductiveProcess) :
    (∀ H, D_PCsmall_on H Q DP) ↔ D_PCsmall Q DP :=
  ⟨fun h n => h (n + 1) n (Nat.lt_succ_self n), fun h _ n _ => h n⟩

/-- Full coherence over the small atoms implies small-sentence coherence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem CoherentOn.toSmall {D : Finset Sentence} {n : ℕ} {p : Sentence → ℝ}
    (h : CoherentOn D (smallAtoms n) p) : CoherentOnSmall D n p := by
  obtain ⟨k, W, w, hW, hw0, hw1, hrep⟩ := h
  exact ⟨k, W, w, hW, hw0, hw1, fun φ hφ => hrep φ (atoms_subset_smallAtoms hφ)⟩

/-- `D_PC_on H` implies `D_PCsmall_on H`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem D_PC_on.toSmall {H : ℕ} {Q : History} {DP : DeductiveProcess} (h : D_PC_on H Q DP) :
    D_PCsmall_on H Q DP :=
  fun n hn => CoherentOn.toSmall (h n hn)

/-- **Small-sentence coherence is agreement with a fully coherent market on the small
sentences** — on one day, exactly the base clause of `bli-linkage`'s package
`PCPσ atoms DP P ∧ E1x Q P` (`CoherentOn (DP.D n) (smallAtoms n ∪ atoms n) (P n)` with
`P n φ = Q n φ` on `smallSet n`), with `P n` the stage mixture itself.
Source: bli-linkage `LiaPackage` (the package's base clause); mandate § 2
Kind: L
Fidelity: n/a -/
theorem coherentOnSmall_iff_exists_mixture_agree (D : Finset Sentence) (n : ℕ)
    (p : Sentence → ℝ) :
    CoherentOnSmall D n p ↔
      ∃ P : Sentence → ℝ, CoherentOn D (smallAtoms n) P ∧ ∀ φ ∈ smallSet n, P φ = p φ := by
  constructor
  · rintro ⟨k, W, w, hW, hw0, hw1, hrep⟩
    exact ⟨fun φ => ∑ i, w i * (W i).payout φ, ⟨k, W, w, hW, hw0, hw1, fun _ _ => rfl⟩,
      fun φ hφ => (hrep φ hφ).symm⟩
  · rintro ⟨P, ⟨k, W, w, hW, hw0, hw1, hrep⟩, hagree⟩
    exact ⟨k, W, w, hW, hw0, hw1, fun φ hφ =>
      (hagree φ hφ).symm.trans (hrep φ (atoms_subset_smallAtoms hφ))⟩

/-- A small-sentence mixture prices a small tautology at `1`.
Source: bli-linkage `LiaPackage.coherentOn_valid_one` (the small form)
Kind: L
Fidelity: n/a -/
theorem CoherentOnSmall.valid_one {D : Finset Sentence} {n : ℕ} {p : Sentence → ℝ}
    (h : CoherentOnSmall D n p) {φ : Sentence} (hφs : φ ∈ smallSet n)
    (hφ : ∀ v : PCWorld, v.Holds φ) : p φ = 1 := by
  obtain ⟨k, W, w, -, -, hsum, hrep⟩ := h
  rw [hrep φ hφs, ← hsum]
  exact Finset.sum_congr rfl fun i _ => by rw [payout_of_holds (hφ (W i)), mul_one]

/-- A small-sentence mixture prices every small sentence in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem CoherentOnSmall.mem_Icc {D : Finset Sentence} {n : ℕ} {p : Sentence → ℝ}
    (h : CoherentOnSmall D n p) {φ : Sentence} (hφs : φ ∈ smallSet n) :
    0 ≤ p φ ∧ p φ ≤ 1 := by
  obtain ⟨k, W, w, -, hw0, hsum, hrep⟩ := h
  rw [hrep φ hφs]
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (payout_nonneg _ _)
  · calc ∑ i, w i * (W i).payout φ ≤ ∑ i, w i * 1 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (payout_mem_Icc _ _).2 (hw0 i)
      _ = 1 := by simp [hsum]

end Cleanroom.Bli.BliExactBase
