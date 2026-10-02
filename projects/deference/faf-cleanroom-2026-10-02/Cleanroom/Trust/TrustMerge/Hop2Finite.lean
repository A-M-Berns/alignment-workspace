import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# `trust-merge` · Hop2Finite: the two-weighting-class lemma (T4(c))

**trust-lab-2-008 / `run2/brainstorm/real-gaps.md` §5 — the Hop-2 substitution shadow, settled.**
On a finite world set `W` with two full-support priors `πA, πH` (the two standpoints), two weight
classes `VA, VH ⊆ (W → ℝ)` and a residual `r`, does "`r` is `πA`-mean-zero on every `VA`-weight"
imply "`r` is `πH`-mean-zero on every `VH`-weight"? **Answer (for subspaces): iff the
`πH/πA`-reweighting of `VH` lies in `VA`** — `meanZero_transfer_iff`. The sufficient direction
is the change-of-measure identity `⟨r, v⟩_{πH} = ⟨r, (πH/πA)·v⟩_{πA}` (`wpair_reweight`); the
necessary direction separates a vector outside `VA` from `VA` by a dual functional
(`Submodule.exists_dual_map_eq_bot_of_notMem`) and realizes the functional as a residual through
the positive weighting. The brainstorm's prediction — "the honest deliverable may be one lemma
plus the observation that the LI content is entirely in the change of measure `π_A → π_H`" — is
exactly what the kernel checks.

**N+ frame where the classes differ and the transfer fails** (`meanZero_transfer_fails`):
`W = Fin 2`, `πA` uniform, `πH = (1/4, 3/4)`, `VA = span{(1,0)}`, `VH = span{(1,1)}`, residual
`r = (0,1)`: `πA`-mean-zero on `VA`, `πH`-pairing with `(1,1)` equal to `3/4`. The brainstorm's
**pre-registered fake** — frames with `VA = VH` (and equal priors), where the swap is trivially
legal — is `meanZero_transfer_of_eq`, a corollary of the sufficient direction with `πH/πA ≡ 1`.

**What this says about Hop 2.** In the LI setting (`Hop2.lean`) the two "classes" are the
`A`-generable and `H`-generable weightings realized on their own markets, the "change of measure"
is the standpoint shift, and `hop2_avg_of_bigenerable` is the sufficient direction at
bi-generable weights; the finite lemma says that in general nothing less than an inclusion of the
reweighted class will do. Mathlib only; no FAF object.
-/

namespace Cleanroom.Trust.TrustMerge

open Finset

noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **The weighted pairing** `⟨r, v⟩_π := Σ_w π_w r_w v_w` — the `π`-expectation of the product
of a residual and a weight; "`r` is `π`-mean-zero on `v`" is `⟨r, v⟩_π = 0`.
Source: trust-lab-2-008; `run2/brainstorm/real-gaps.md` §5
Kind: D
Fidelity: exact -/
def wpair (π r v : W → ℝ) : ℝ := ∑ w, π w * r w * v w

/-- **Mean-zero on a class**: `⟨r, v⟩_π = 0` for every weight `v` in the class `V`.
Source: trust-lab-2-008 ("`r` is `A`-mean-zero on every `𝒢_A`-weight")
Kind: D
Fidelity: exact -/
def MeanZeroOn (π : W → ℝ) (V : Set (W → ℝ)) (r : W → ℝ) : Prop :=
  ∀ v ∈ V, wpair π r v = 0

/-- **The reweighting** `(πH/πA) · v` of a weight: the change of measure from standpoint `A` to
standpoint `H`, applied to the weight.
Source: trust-lab-2-008 ("under a change of measure"); real-gaps §5 ("after the standpoint shift")
Kind: D
Fidelity: exact -/
def reweight (πA πH : W → ℝ) (v : W → ℝ) : W → ℝ := fun w => πH w / πA w * v w

omit [DecidableEq W] in
/-- **The change-of-measure identity**: `⟨r, v⟩_{πH} = ⟨r, (πH/πA)·v⟩_{πA}` when `πA > 0`.
Source: trust-lab-2-008 (the "linear-algebra fact about two subspaces")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem wpair_reweight {πA πH : W → ℝ} (hA : ∀ w, 0 < πA w) (r v : W → ℝ) :
    wpair πH r v = wpair πA r (reweight πA πH v) := by
  unfold wpair reweight
  refine sum_congr rfl (fun w _ => ?_)
  have := (hA w).ne'
  field_simp

omit [DecidableEq W] in
/-- **Sufficient direction (the standpoint shift is free on reweighted-included classes):** if
every reweighted `VH`-weight lies in `VA`, `πA`-mean-zero on `VA` implies `πH`-mean-zero on `VH`.
Source: trust-lab-2-008 ("yes iff `𝒢_H ⊆ 𝒢_A` after the standpoint shift", the `if` half)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem meanZero_transfer_of_subset {πA πH : W → ℝ} (hA : ∀ w, 0 < πA w)
    {VA VH : Set (W → ℝ)} (h : ∀ v ∈ VH, reweight πA πH v ∈ VA) (r : W → ℝ)
    (hr : MeanZeroOn πA VA r) : MeanZeroOn πH VH r := by
  intro v hv
  rw [wpair_reweight hA]
  exact hr _ (h v hv)

/-- A residual realizing a dual functional through a positive weighting:
`⟨ℓ♯, x⟩_{πA} = ℓ x` with `ℓ♯ w := ℓ(e_w)/πA w`.
Source: none: infrastructure (the Riesz step of the necessary direction)
Kind: L
Fidelity: n/a -/
theorem wpair_dualResidual {πA : W → ℝ} (hA : ∀ w, 0 < πA w) (ℓ : Module.Dual ℝ (W → ℝ))
    (x : W → ℝ) : wpair πA (fun w => ℓ (Pi.single w 1) / πA w) x = ℓ x := by
  unfold wpair
  have hsingle : ∀ w, Pi.single w (x w) = x w • (Pi.single w (1 : ℝ) : W → ℝ) := by
    intro w
    funext j
    by_cases h : j = w
    · subst h; simp
    · simp [h]
  conv_rhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine sum_congr rfl (fun w _ => ?_)
  rw [hsingle w, map_smul, smul_eq_mul]
  have := (hA w).ne'
  field_simp

/-- **Necessary direction:** if `πA`-mean-zero on the subspace `VA` implies `πH`-mean-zero on the
subspace `VH` for *every* residual, then every reweighted `VH`-weight lies in `VA`. Contrapositive:
a reweighted weight `u ∉ VA` is separated from `VA` by a dual functional `ℓ` (`ℓ u ≠ 0`, `ℓ = 0`
on `VA`), whose residual `ℓ♯` is `πA`-mean-zero on `VA` yet pairs with the original weight to
`ℓ u ≠ 0` under `πH`.
Source: trust-lab-2-008 (the `only if` half); real-gaps §5 ("the answer is NO in general")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem subset_of_meanZero_transfer {πA πH : W → ℝ} (hA : ∀ w, 0 < πA w)
    {VA VH : Submodule ℝ (W → ℝ)}
    (h : ∀ r : W → ℝ, MeanZeroOn πA (VA : Set (W → ℝ)) r → MeanZeroOn πH (VH : Set (W → ℝ)) r) :
    ∀ v ∈ VH, reweight πA πH v ∈ VA := by
  intro v hv
  by_contra hu
  obtain ⟨ℓ, hℓu, hℓVA⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hu inferInstance
  have hzero : MeanZeroOn πA (VA : Set (W → ℝ)) (fun w => ℓ (Pi.single w 1) / πA w) := by
    intro x hx
    rw [wpair_dualResidual hA]
    have hmem : ℓ x ∈ VA.map ℓ := Submodule.mem_map_of_mem hx
    rw [hℓVA] at hmem
    simpa using hmem
  have hH := h _ hzero v hv
  rw [wpair_reweight hA, wpair_dualResidual hA] at hH
  exact hℓu hH

/-- **T4(c) (headline). The two-weighting-class lemma:** for full-support `πA` and subspaces
`VA, VH`, "`πA`-mean-zero on `VA` implies `πH`-mean-zero on `VH`, for every residual" **iff** the
`πH/πA`-reweighting of `VH` lies in `VA`. The Hop-2 substitution obligation, in its finite shadow,
is exactly an inclusion of weight classes after the change of measure; the LI content is the
change of measure.
Source: trust-lab-2-008 ("Conjecture: no in general, yes iff `𝒢_H ⊆ 𝒢_A` after the standpoint
shift"); `run2/brainstorm/real-gaps.md` §5
Kind: P
Fidelity: exact (the condition stated precisely: `{(πH/πA)·v : v ∈ VH} ⊆ VA`)
Hyps: (a) none -/
theorem meanZero_transfer_iff {πA πH : W → ℝ} (hA : ∀ w, 0 < πA w)
    (VA VH : Submodule ℝ (W → ℝ)) :
    (∀ r : W → ℝ, MeanZeroOn πA (VA : Set (W → ℝ)) r → MeanZeroOn πH (VH : Set (W → ℝ)) r) ↔
      ∀ v ∈ VH, reweight πA πH v ∈ VA :=
  ⟨subset_of_meanZero_transfer hA, fun h r hr => meanZero_transfer_of_subset hA h r hr⟩

/-- **The pre-registered fake, as a corollary:** with equal classes and equal priors the swap is
trivially legal — the reweighting is the identity. A search over such frames proves nothing
(real-gaps §5: "the FAKE version: searching frames where `𝒢_A = 𝒢_H` by construction").
Source: real-gaps §5 (the pre-registered fake)
Kind: T
Fidelity: exact
Hyps: (a) none -/
theorem meanZero_transfer_of_eq {π : W → ℝ} (hπ : ∀ w, 0 < π w) (V : Set (W → ℝ)) (r : W → ℝ)
    (hr : MeanZeroOn π V r) : MeanZeroOn π V r :=
  meanZero_transfer_of_subset hπ (VA := V) (VH := V) (fun v hv => by
    have : reweight π π v = v := by
      funext w
      unfold reweight
      rw [div_self (hπ w).ne', one_mul]
    rw [this]; exact hv) r hr

/-! ## The N+ frame: distinct classes, transfer fails -/

/-- The uniform prior on two worlds (standpoint `A`).
Source: trust-lab-2-008 (the N+ frame); mandate T4(c)
Kind: D
Fidelity: n/a -/
def πA₂ : Fin 2 → ℝ := fun _ => 1 / 2

/-- The skewed prior `(1/4, 3/4)` (standpoint `H`).
Source: mandate T4(c)
Kind: D
Fidelity: n/a -/
def πH₂ : Fin 2 → ℝ := ![1 / 4, 3 / 4]

/-- `A`'s weight class: the span of `(1, 0)` (weights supported on world `0`).
Source: mandate T4(c)
Kind: D
Fidelity: n/a -/
def VA₂ : Submodule ℝ (Fin 2 → ℝ) := ℝ ∙ (![1, 0] : Fin 2 → ℝ)

/-- `H`'s weight class: the span of `(1, 1)` (constant weights).
Source: mandate T4(c)
Kind: D
Fidelity: n/a -/
def VH₂ : Submodule ℝ (Fin 2 → ℝ) := ℝ ∙ (![1, 1] : Fin 2 → ℝ)

/-- **N+: the transfer fails where the classes differ.** The residual `r = (0, 1)` is
`πA`-mean-zero on `VA₂ = span{(1,0)}` but its `πH`-pairing with the `VH₂`-weight `(1,1)` is
`3/4 ≠ 0`. Computed by `norm_num` from the data; the classes genuinely differ (`VA₂ ≠ VH₂`, which
the failure itself certifies through `meanZero_transfer_iff`).
Source: trust-lab-2-008; real-gaps §5 ("the search must include frames where the two weight
classes genuinely differ")
Kind: N+
Fidelity: exact
Hyps: n/a -/
theorem meanZero_transfer_fails :
    ∃ r : Fin 2 → ℝ, MeanZeroOn πA₂ (VA₂ : Set (Fin 2 → ℝ)) r ∧
      ¬ MeanZeroOn πH₂ (VH₂ : Set (Fin 2 → ℝ)) r := by
  refine ⟨![0, 1], ?_, ?_⟩
  · intro v hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    simp [wpair, πA₂, Fin.sum_univ_two]
  · intro h
    have hmem : (![1, 1] : Fin 2 → ℝ) ∈ (VH₂ : Set (Fin 2 → ℝ)) :=
      Submodule.mem_span_singleton_self _
    have := h _ hmem
    simp [wpair, πH₂, Fin.sum_univ_two] at this

/-- The N+ frame's reweighted `VH₂`-weight `(1/2, 3/2)` is not in `VA₂`: the condition of
`meanZero_transfer_iff` fails there, as it must.
Source: mandate T4(c)
Kind: N+
Fidelity: exact
Hyps: n/a -/
theorem reweight_not_mem_VA₂ : ¬ (reweight πA₂ πH₂ ![1, 1] ∈ VA₂) := by
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp [reweight, πA₂, πH₂] at h0 h1

end

end Cleanroom.Trust.TrustMerge
