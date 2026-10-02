import Cleanroom.Udt.UdtPaperTiling.Rules

/-!
# `udt-paper-tiling` · PolicyLevel: the policy-level modification model and its tiling theorem
(T12, load-bearing 5)

The working notes' "new idea" (l5 b.161–175, bli-paper-2-001): start from the agent's
distribution `P(effective policy | chosen policy)`. Over `udt-bli-core`'s prior, `pp` is the
effective policy `π#` and a `ModLayer` adds the chosen policy `π*` as a coordinate — with **no**
`pp_eff` clause: modification is stochastic, the environment's kernel `ker π' π = P(π# = π | π* = π')`
is whatever the joint law says.

* Definitions (2-001): `chosenMass`, `cellMass`, `ker` (junk `0` at a null chosen policy),
  `Modifying`, `Reachable`, `chosenEU`, `effEU`, `cellEU`.
* Fairness three ways (2-003, bli-paper-091): `CIFair` (the notes' conditional independence
  `P(U = u, π* = π | π# = π') = P(U = u | π# = π') · P(π* = π | π# = π')`, in product form over the
  finitely many values of `U`), `MeanFair` (the cell mean equals the effective-policy mean on
  positive cells), `DistFair` (equal kernels give equal chosen-policy values). Proved:
  `meanFair_of_ciFair`, `mixture_of_meanFair` (**the content**: `𝔼[U | π* = π₁] = ∑_π ker π₁ π ·
  𝔼[U | π# = π]`), `distFair_of_meanFair`.
* `Avoidable` (2-002(a), the notes' literal: every reachable effective policy is implemented by
  some non-modifying chosen policy) and `avoidable_iff` (the implementing policy must be `π`
  itself: every reachable policy is positively chosen and non-modifying).
* **`policyLevel_tiling`** (2-002(c)): `MeanFair → Avoidable → 0 < chosenMass π₁ → ∃ π,
  ¬ Modifying π ∧ 0 < chosenMass π ∧ chosenEU π₁ ≤ chosenEU π`. The content is the mixture
  identity plus `effEU π = chosenEU π` for non-modifying positive `π`; this is the
  probabilistic-modification generalisation of Theorem 1, and near a squeeze by the inventory's
  own reading (the docstring says so).
* **The bridge to the run's `PolicyFair`**: a paper layer (deterministic `eff`) is a `ModLayer`
  with `chosen := Λ.chosen`, and `policyFair_iff_meanFair` identifies the paper's Policy Fairness
  with mean-conditional-independence fairness on it — a genuine `P` in both directions.
* 2-004: `KerIdempotent`, and `kerIdempotent_of_avoidable`: under Avoidability every reachable
  policy is a fixed point of the kernel, so idempotence *holds* — the inventory's question
  "does CI-fairness imply idempotence?" needs `¬ Avoidable` for its countermodel
  (`PolicyLevelWitness.lean`). Both readings of "stationary distribution" are recorded there.

Witnesses: `PolicyLevelWitness.lean`.

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {Act : Type} [Fintype Act]
  [DecidableEq Act] {P : FiniteBLIPrior 𝒮 m 𝒟 Act}

/-! ## A generic lemma: `μ(E ∧ G) + μ(E ∧ ¬G) = μ(E)` -/

/-- Splitting an event by a second one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_and_add_massOf_and_not {Ω : Type} [Fintype Ω] (μ : Ω → ℚ) (E G : Ω → Prop)
    [DecidablePred E] [DecidablePred G] :
    massOf μ (fun ω => E ω ∧ G ω) + massOf μ (fun ω => E ω ∧ ¬ G ω) = massOf μ E := by
  unfold massOf
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hE : E ω <;> by_cases hG : G ω <;> simp [hE, hG]

/-- The integral of `f` over `E` decomposed by the values of `f`.
Source: none: infrastructure (CI-fairness in product form over the values of `U`)
Kind: L
Fidelity: n/a -/
lemma integralOf_eq_sum_values {Ω : Type} [Fintype Ω] (μ f : Ω → ℚ) (E : Ω → Prop)
    [DecidablePred E] :
    integralOf μ f E = ∑ u ∈ Finset.univ.image f, u * massOf μ (fun ω => f ω = u ∧ E ω) := by
  unfold integralOf massOf
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hE : E ω
  · simp only [hE, and_true, if_true, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq (Finset.univ.image f) (f ω)]
    simp [Finset.mem_image_of_mem f (Finset.mem_univ ω), mul_comm]
  · simp [hE]

/-! ## The modification layer -/

/-- **A modification layer**: the chosen policy `π*` as a coordinate, with `pp` the effective
policy `π#` — no deterministic link between them (modification is stochastic; the kernel is
whatever the joint law says).
Source: [[udt-tiling-working-notes-2025-06-30]] l5 b.133–147, b.161–170 (bli-paper-2-001)
Kind: D
Fidelity: exact -/
structure ModLayer (P : FiniteBLIPrior 𝒮 m 𝒟 Act) where
  /-- The chosen policy in each world. -/
  chosen : P.Ω → Policy 𝒟 Act

namespace ModLayer

variable (M : ModLayer P)

/-- `μ(π* = π)`. Source: bli-paper-2-001. Kind: D. Fidelity: exact -/
def chosenMass (π : Policy 𝒟 Act) : ℚ := massOf P.μ (fun ω => M.chosen ω = π)

/-- `μ(π* = π' ∧ π# = π)`. Source: bli-paper-2-001. Kind: D. Fidelity: exact -/
def cellMass (π' π : Policy 𝒟 Act) : ℚ := massOf P.μ (fun ω => M.chosen ω = π' ∧ P.pp ω = π)

/-- **The environment's kernel** `ker π' π := P(π# = π | π* = π')` (junk `0` at a null chosen
policy).
Source: l5 b.136, b.139 (`e(π') = P(π^† = π | π* = π')`) (bli-paper-2-001)
Kind: D
Fidelity: exact (with the disclosed junk value) -/
def ker (π' π : Policy 𝒟 Act) : ℚ := M.cellMass π' π / M.chosenMass π'

/-- **Modifying policy**: `P(π* = π ∧ π# ≠ π) > 0`.
Source: l5 b.143–144 (bli-paper-2-001)
Kind: D
Fidelity: exact (the notes' `P(π* ≠ π# | π* = π) > 0` in joint form) -/
def Modifying (π : Policy 𝒟 Act) : Prop := 0 < massOf P.μ (fun ω => M.chosen ω = π ∧ P.pp ω ≠ π)

/-- **Reachable policy**: some chosen policy makes it the effective policy with positive
probability.
Source: l5 b.146–147 (bli-paper-2-001)
Kind: D
Fidelity: exact (joint form) -/
def Reachable (π : Policy 𝒟 Act) : Prop := ∃ π', 0 < M.cellMass π' π

/-- `𝔼[U | π* = π]`. Source: bli-paper-2-002. Kind: D. Fidelity: exact -/
def chosenEU (π : Policy 𝒟 Act) : ℚ := condExp P.μ P.U (fun ω => M.chosen ω = π)

/-- `𝔼[U | π# = π]` (the layer argument is unused: the effective policy is `pp`; it is there so
that `M.effEU` reads alongside `M.chosenEU`). Source: bli-paper-2-002. Kind: D. Fidelity: exact -/
def effEU (_M : ModLayer P) (π : Policy 𝒟 Act) : ℚ := condExp P.μ P.U (fun ω => P.pp ω = π)

/-- `𝔼[U | π* = π' ∧ π# = π]`. Source: bli-paper-2-003. Kind: D. Fidelity: exact -/
def cellEU (π' π : Policy 𝒟 Act) : ℚ :=
  condExp P.μ P.U (fun ω => M.chosen ω = π' ∧ P.pp ω = π)

/-- **CI-fairness**: utility and chosen policy are conditionally independent given the effective
policy, `P(U = u, π* = π | π# = π') = P(U = u | π# = π') · P(π* = π | π# = π')`, in product form
over the finitely many values of `U` (no division).
Source: l5 b.153–154 (bli-paper-2-003)
Kind: D
Fidelity: exact (product form) -/
def CIFair : Prop :=
  ∀ (π π' : Policy 𝒟 Act) (u : ℚ),
    massOf P.μ (fun ω => P.U ω = u ∧ M.chosen ω = π ∧ P.pp ω = π') * massOf P.μ (fun ω => P.pp ω = π') =
      massOf P.μ (fun ω => P.U ω = u ∧ P.pp ω = π') * M.cellMass π π'

/-- **Mean fairness**: on every positive cell `π* = π ∧ π# = π'`, the cell mean is the
effective-policy mean `𝔼[U | π# = π']`.
Source: mandate T12 (the mean form of CI-fairness)
Kind: D
Fidelity: exact -/
def MeanFair : Prop :=
  ∀ π π', 0 < M.cellMass π π' → M.cellEU π π' = M.effEU π'

/-- **Distributional fairness** (bli-paper-091's form): chosen policies with the same kernel have
the same value.
Source: l5 b.151–152 (bli-paper-2-003(b), 091)
Kind: D
Fidelity: exact -/
def DistFair : Prop :=
  ∀ π₁ π₂, (∀ π, M.ker π₁ π = M.ker π₂ π) → 0 < M.chosenMass π₁ → 0 < M.chosenMass π₂ →
    M.chosenEU π₁ = M.chosenEU π₂

/-- **Avoidability** (the notes' literal): every reachable effective policy is implemented, with
probability one, by some non-modifying chosen policy of positive mass. The notes give two
phrasings — "implemented by some non-modifying policy" and "non-modifying ⊇ reachable"; under the
joint-form `Modifying`, a never-chosen policy is vacuously non-modifying, so the superset phrasing
is weaker than this definition, which demands positive mass (needed: without it the conclusion's
`chosenEU π` is junk; `avoidable_iff` makes the reading explicit; audit r1).
Source: l5 b.171–175 (bli-paper-2-002(a))
Kind: D
Fidelity: variant: the implementing policy is required to have positive mass -/
def Avoidable : Prop :=
  ∀ π, M.Reachable π →
    ∃ π', ¬ M.Modifying π' ∧ 0 < M.chosenMass π' ∧ massOf P.μ (fun ω => M.chosen ω = π' ∧ P.pp ω ≠ π) = 0

/-- **Kernel idempotence** (`e ∘ e = e` row-wise): a modified agent is not modified again.
Source: l5 b.137–140 (bli-paper-2-004), the "idempotent kernel" reading
Kind: D
Fidelity: variant: one of the two readings of "stationary distribution" -/
def KerIdempotent : Prop := ∀ π π', ∑ π'', M.ker π π'' * M.ker π'' π' = M.ker π π'

/-! ## Basic facts -/

/-- Non-modifying as a null event.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_modifying_iff (π : Policy 𝒟 Act) :
    ¬ M.Modifying π ↔ massOf P.μ (fun ω => M.chosen ω = π ∧ P.pp ω ≠ π) = 0 := by
  unfold Modifying
  constructor
  · intro h
    exact le_antisymm (not_lt.mp h) (massOf_nonneg _ P.μ_nonneg _)
  · intro h
    rw [h]
    exact lt_irrefl 0

/-- A cell is bounded by its chosen policy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellMass_le_chosenMass (π' π : Policy 𝒟 Act) : M.cellMass π' π ≤ M.chosenMass π' :=
  massOf_mono P.μ P.μ_nonneg (fun _ h => h.1)

/-- A positive cell has a positive chosen policy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma chosenMass_pos_of_cellMass_pos {π' π : Policy 𝒟 Act} (h : 0 < M.cellMass π' π) :
    0 < M.chosenMass π' :=
  lt_of_lt_of_le h (M.cellMass_le_chosenMass π' π)

/-- The kernel is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ker_nonneg (π' π : Policy 𝒟 Act) : 0 ≤ M.ker π' π :=
  div_nonneg (massOf_nonneg _ P.μ_nonneg _) (massOf_nonneg _ P.μ_nonneg _)

/-- A positive kernel entry is a positive cell (hence reachable).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellMass_pos_of_ker_pos {π' π : Policy 𝒟 Act} (h : 0 < M.ker π' π) : 0 < M.cellMass π' π := by
  by_contra hc
  have hz : M.cellMass π' π = 0 := le_antisymm (not_lt.mp hc) (massOf_nonneg _ P.μ_nonneg _)
  unfold ker at h
  rw [hz, zero_div] at h
  exact lt_irrefl _ h

/-- The kernel is zero exactly at a null cell (given a positive chosen policy).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ker_eq_zero_of_cellMass_eq_zero {π' π : Policy 𝒟 Act} (h : M.cellMass π' π = 0) :
    M.ker π' π = 0 := by
  unfold ker; rw [h, zero_div]

/-- The kernel rows sum to one on positive chosen policies.
Source: none: infrastructure (the kernel is a Markov kernel)
Kind: L
Fidelity: n/a -/
lemma sum_ker (π' : Policy 𝒟 Act) (h : 0 < M.chosenMass π') : ∑ π, M.ker π' π = 1 := by
  unfold ker
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  have : ∑ π, M.cellMass π' π = M.chosenMass π' := by
    unfold cellMass chosenMass
    rw [massOf_fiberwise P.μ (fun ω => M.chosen ω = π') P.pp]
  rw [this, mul_inv_cancel₀ (ne_of_gt h)]

/-- **On a non-modifying positive chosen policy, the diagonal cell carries everything**:
`cellMass π π = chosenMass π`, `chosenEU π = cellEU π π`, and `ker π π = 1`.
Source: none: infrastructure (the step `effEU π = chosenEU π` of the tiling theorem)
Kind: L
Fidelity: n/a -/
lemma diag_of_not_modifying {π : Policy 𝒟 Act} (hnm : ¬ M.Modifying π) :
    M.cellMass π π = M.chosenMass π ∧ M.chosenEU π = M.cellEU π π := by
  rw [not_modifying_iff] at hnm
  constructor
  · have := massOf_and_add_massOf_and_not P.μ (fun ω => M.chosen ω = π) (fun ω => P.pp ω = π)
    unfold cellMass chosenMass
    rw [hnm, add_zero] at this
    exact this
  · unfold chosenEU cellEU
    apply condExp_congr_null P.μ P.U P.μ_nonneg
    apply le_antisymm _ (massOf_nonneg _ P.μ_nonneg _)
    rw [← hnm]
    apply massOf_mono P.μ P.μ_nonneg
    intro ω hω
    by_cases hc : M.chosen ω = π
    · refine ⟨hc, fun hp => hω ⟨fun _ => ⟨hc, hp⟩, fun h => h.1⟩⟩
    · exact absurd ⟨fun h => absurd h hc, fun h => absurd h.1 hc⟩ hω

/-- A non-modifying positive policy has `ker π π = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ker_self_of_not_modifying {π : Policy 𝒟 Act} (hnm : ¬ M.Modifying π) (hpos : 0 < M.chosenMass π) :
    M.ker π π = 1 := by
  unfold ker
  rw [(M.diag_of_not_modifying hnm).1, div_self (ne_of_gt hpos)]

/-- A non-modifying policy reaches nothing else: `ker π π' = 0` for `π' ≠ π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ker_eq_zero_of_not_modifying {π π' : Policy 𝒟 Act} (hnm : ¬ M.Modifying π) (hne : π' ≠ π) :
    M.ker π π' = 0 := by
  apply M.ker_eq_zero_of_cellMass_eq_zero
  rw [not_modifying_iff] at hnm
  apply le_antisymm _ (massOf_nonneg _ P.μ_nonneg _)
  rw [← hnm]
  apply massOf_mono P.μ P.μ_nonneg
  intro ω hω
  exact ⟨hω.1, fun h => hne (h ▸ hω.2 ▸ rfl)⟩

/-! ## Avoidability -/

/-- **`avoidable_iff`**: the implementing policy of a reachable `π` must be `π` itself, so
Avoidability says exactly that every reachable policy is positively chosen and non-modifying.
Source: bli-paper-2-002(a) (mandate T12)
Kind: L
Fidelity: exact
Hyps: none -/
theorem avoidable_iff : M.Avoidable ↔ ∀ π, M.Reachable π → 0 < M.chosenMass π ∧ ¬ M.Modifying π := by
  constructor
  · intro h π hr
    obtain ⟨π', hnm, hpos, hnull⟩ := h π hr
    have hnm' := (M.not_modifying_iff π').mp hnm
    rw [massOf_eq_zero_iff P.μ P.μ_nonneg] at hnm' hnull
    obtain ⟨ω, hω, hμ⟩ := (massOf_pos_iff P.μ P.μ_nonneg _).mp hpos
    have h1 : P.pp ω = π' := by
      by_contra hne
      exact ne_of_gt hμ (hnm' ω ⟨hω, hne⟩)
    have h2 : P.pp ω = π := by
      by_contra hne
      exact ne_of_gt hμ (hnull ω ⟨hω, hne⟩)
    have : π' = π := h1.symm.trans h2
    subst this
    exact ⟨hpos, hnm⟩
  · intro h π hr
    obtain ⟨hpos, hnm⟩ := h π hr
    exact ⟨π, hnm, hpos, (M.not_modifying_iff π).mp hnm⟩

/-! ## The mixture identity and the three fairness notions -/

/-- **The chosen-policy value is the kernel mixture of the cell values** (the tower identity over
the effective policy; unconditional, with the junk conventions).
Source: bli-paper-2-003(a)
Kind: L
Fidelity: exact -/
theorem chosenEU_eq_sum_ker_cellEU (π₁ : Policy 𝒟 Act) :
    M.chosenEU π₁ = ∑ π, M.ker π₁ π * M.cellEU π₁ π := by
  unfold chosenEU ker cellMass chosenMass cellEU
  exact condExp_fiberwise P.μ P.U P.μ_nonneg (fun ω => M.chosen ω = π₁) P.pp

/-- **The mixture form under mean fairness** (the content of the policy-level program):
`𝔼[U | π* = π₁] = ∑_π P(π# = π | π* = π₁) · 𝔼[U | π# = π]` for every chosen policy. No
positivity is needed (repair round 2, fidelity N-8): at a null chosen policy both sides are the
junk `0` (`chosenEU` and every `ker π₁ π`), and the identity is meaningful at the positive ones.
Source: l5 b.150–154; bli-paper-2-002(c), 2-003(a)
Kind: P
Fidelity: exact
Hyps: (a) `MeanFair` -/
theorem mixture_of_meanFair (hF : M.MeanFair) (π₁ : Policy 𝒟 Act) :
    M.chosenEU π₁ = ∑ π, M.ker π₁ π * M.effEU π := by
  rw [M.chosenEU_eq_sum_ker_cellEU]
  apply Finset.sum_congr rfl
  intro π _
  by_cases hc : 0 < M.cellMass π₁ π
  · rw [hF π₁ π hc]
  · have hz : M.cellMass π₁ π = 0 := le_antisymm (not_lt.mp hc) (massOf_nonneg _ P.μ_nonneg _)
    rw [M.ker_eq_zero_of_cellMass_eq_zero hz, zero_mul, zero_mul]

/-- **CI-fairness implies mean fairness**: on a positive cell, cross-multiplying the product form
over the values of `U` gives `∫_{cell} U · μ(π# = π') = ∫_{π# = π'} U · μ(cell)`.
Source: bli-paper-2-003(a)
Kind: C
Fidelity: exact
Hyps: (a) `CIFair` -/
theorem meanFair_of_ciFair (hCI : M.CIFair) : M.MeanFair := by
  intro π π' hpos
  have hpos' : 0 < massOf P.μ (fun ω => P.pp ω = π') :=
    lt_of_lt_of_le hpos (massOf_mono P.μ P.μ_nonneg (fun _ h => h.2))
  have hpos₁ : 0 < massOf P.μ (fun ω => M.chosen ω = π ∧ P.pp ω = π') := hpos
  unfold cellEU effEU condExp
  rw [div_eq_div_iff (ne_of_gt hpos₁) (ne_of_gt hpos')]
  rw [integralOf_eq_sum_values, integralOf_eq_sum_values, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u _
  rw [mul_assoc, mul_assoc]
  congr 1
  exact hCI π π' u

/-- **Mean fairness implies distributional fairness**: both values are the same kernel mixture.
Source: bli-paper-2-003(b)
Kind: C
Fidelity: exact
Hyps: (a) `MeanFair` -/
theorem distFair_of_meanFair (hF : M.MeanFair) : M.DistFair := by
  intro π₁ π₂ hker _ _
  rw [M.mixture_of_meanFair hF π₁, M.mixture_of_meanFair hF π₂]
  apply Finset.sum_congr rfl
  intro π _
  rw [hker π]

/-! ## The policy-level tiling theorem -/

/-- A convex combination with positive weights summing to one is bounded by one of its terms.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exists_le_of_sum_eq_one {ι : Type} [Fintype ι] (w f : ι → ℚ) (hw : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) (x : ℚ) (hx : x = ∑ i, w i * f i) : ∃ i, 0 < w i ∧ x ≤ f i := by
  by_contra hcon
  push Not at hcon
  have hex : ∃ i, 0 < w i := by
    by_contra hall
    push Not at hall
    have : ∑ i, w i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (hall i) (hw i)
    rw [this] at h1
    exact zero_ne_one h1
  obtain ⟨i₀, hi₀⟩ := hex
  have hlt : ∑ i, w i * f i < ∑ i, w i * x := by
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : 0 < w i
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hcon i hi)) (hw i)
      · have : w i = 0 := le_antisymm (not_lt.mp hi) (hw i)
        rw [this, zero_mul, zero_mul]
    · exact ⟨i₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hcon i₀ hi₀) hi₀⟩
  rw [← Finset.sum_mul, h1, one_mul, ← hx] at hlt
  exact lt_irrefl _ hlt

/-- **The policy-level tiling theorem** (bli-paper-2-002(c)): under mean fairness and
Avoidability, no positive chosen policy is strictly better than every non-modifying positive
chosen policy: for every `π₁` of positive mass there is a non-modifying `π` of positive mass
with `𝔼[U | π* = π₁] ≤ 𝔼[U | π* = π]`. **The content is the mixture identity**
(`mixture_of_meanFair`: the value of `π₁` is a convex combination of the effective-policy values
over the policies it reaches) **plus `effEU π = chosenEU π` for a non-modifying positive `π`**
(`diag_of_not_modifying` with mean fairness on the diagonal cell); Avoidability supplies that every
reached policy is such a `π`. This is the probabilistic-modification generalisation of Theorem 1
and is near a squeeze by the inventory's own reading: CI-fairness makes utility a mixture over
effective policies, Avoidability makes every mixture component attainable without modification.
Source: l5 b.171–175; bli-paper-2-002(c)
Kind: C
Fidelity: exact
Hyps: (a) `MeanFair`, `Avoidable`, `0 < chosenMass π₁` -/
theorem policyLevel_tiling (hF : M.MeanFair) (hA : M.Avoidable) (π₁ : Policy 𝒟 Act)
    (h₁ : 0 < M.chosenMass π₁) :
    ∃ π, ¬ M.Modifying π ∧ 0 < M.chosenMass π ∧ M.chosenEU π₁ ≤ M.chosenEU π := by
  obtain ⟨π, hker, hle⟩ := exists_le_of_sum_eq_one (M.ker π₁) M.effEU (M.ker_nonneg π₁)
    (M.sum_ker π₁ h₁) (M.chosenEU π₁) (M.mixture_of_meanFair hF π₁)
  have hr : M.Reachable π := ⟨π₁, M.cellMass_pos_of_ker_pos hker⟩
  obtain ⟨hpos, hnm⟩ := (M.avoidable_iff.mp hA) π hr
  refine ⟨π, hnm, hpos, ?_⟩
  obtain ⟨hcell, hval⟩ := M.diag_of_not_modifying hnm
  rw [hval, hF π π (hcell ▸ hpos)]
  exact hle

/-! ## Kernel idempotence under Avoidability (2-004) -/

/-- **Under Avoidability the kernel is idempotent**: every reached policy is a fixed point of the
kernel (`ker π'' π'' = 1`, `ker π'' π' = 0` for `π' ≠ π''`), so `∑_{π''} ker π π'' · ker π'' π' =
ker π π'`. Hence the inventory's "CI-fairness ⇏ idempotence" countermodel needs `¬ Avoidable`
(`PolicyLevelWitness.lean`); "stationary distribution of `e`" in the other reading (the law of
`π#` given `π* = π'` is `e`-invariant) is the same statement row by row.
Source: l5 b.137–140 (bli-paper-2-004)
Kind: P
Fidelity: n/a (the inventory's question answered; both readings recorded)
Hyps: (a) `Avoidable` -/
theorem kerIdempotent_of_avoidable (hA : M.Avoidable) : M.KerIdempotent := by
  intro π π'
  rw [Finset.sum_eq_single π']
  · by_cases h : 0 < M.ker π π'
    · have hr : M.Reachable π' := ⟨π, M.cellMass_pos_of_ker_pos h⟩
      obtain ⟨hpos, hnm⟩ := (M.avoidable_iff.mp hA) π' hr
      rw [M.ker_self_of_not_modifying hnm hpos, mul_one]
    · have hz : M.ker π π' = 0 := le_antisymm (not_lt.mp h) (M.ker_nonneg π π')
      rw [hz, zero_mul]
  · intro π'' _ hne
    by_cases h : 0 < M.ker π π''
    · have hr : M.Reachable π'' := ⟨π, M.cellMass_pos_of_ker_pos h⟩
      obtain ⟨_, hnm⟩ := (M.avoidable_iff.mp hA) π'' hr
      rw [M.ker_eq_zero_of_not_modifying hnm (Ne.symm hne), mul_zero]
    · have hz : M.ker π π'' = 0 := le_antisymm (not_lt.mp h) (M.ker_nonneg π π'')
      rw [hz, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ π') h

end ModLayer

/-! ## The bridge: a paper layer is a modification layer, and `PolicyFair ↔ MeanFair` -/

namespace PaperLayer

variable (Λ : PaperLayer P)

/-- A paper layer (deterministic `eff`) as a modification layer: `chosen := Λ.chosen`, and
`pp = eff ∘ chosen` makes the kernel deterministic.
Source: mandate T12 (the bridge)
Kind: D
Fidelity: exact -/
def toModLayer : ModLayer P where
  chosen := Λ.chosen

/-- On a paper layer, a positive cell `(π, π')` has `π' = eff π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma eff_eq_of_cellMass_pos {π π' : Policy 𝒟 Act} (h : 0 < Λ.toModLayer.cellMass π π') :
    π' = Λ.eff π := by
  obtain ⟨ω, ⟨hc, hp⟩, _⟩ := (massOf_pos_iff P.μ P.μ_nonneg _).mp h
  have hω : Λ.chosen ω = π := hc
  rw [← hp, Λ.pp_eff ω, hω]

/-- On a paper layer, the diagonal-type cell `(π, eff π)` is the whole chosen-policy event.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellEU_eff (π : Policy 𝒟 Act) : Λ.toModLayer.cellEU π (Λ.eff π) = Λ.procEU π := by
  unfold ModLayer.cellEU
  rw [Λ.procEU_eq]
  apply condExp_congr
  intro ω
  constructor
  · exact And.left
  · intro h
    have hω : Λ.chosen ω = π := h
    exact ⟨h, by rw [Λ.pp_eff ω, hω]⟩

/-- **Policy Fairness is mean fairness on the paper layer**: `→` because the cell `(π, eff π)` is
the chosen event and `𝔼[U | π# = eff π]` is the `procMass`-weighted average of the equal values
`procEU p` over `{p | eff p = eff π}` (`condExp_eq_of_fibers`); `←` because `procEU p` is the cell
mean at `(p, eff p)`, which mean fairness equates to `effEU (eff p) = effEU (eff q)`. This
identifies the paper's Policy Fairness with mean-conditional-independence fairness; the
non-trivial content of the policy-level program is this bridge.
Source: mandate T12 (the bridge); `main.tex` 145–147; l5 b.150–154
Kind: P
Fidelity: exact
Hyps: none (an equivalence) -/
theorem policyFair_iff_meanFair : P.PolicyFair Λ.toProcLayer ↔ Λ.toModLayer.MeanFair := by
  constructor
  · intro hF π π' hcell
    have hπ' : π' = Λ.eff π := Λ.eff_eq_of_cellMass_pos hcell
    subst hπ'
    rw [Λ.cellEU_eff]
    have hπpos : 0 < Λ.procMass π := Λ.toModLayer.chosenMass_pos_of_cellMass_pos hcell
    unfold ModLayer.effEU
    symm
    apply condExp_eq_of_fibers P.μ P.U P.μ_nonneg _ Λ.chosen
    · exact lt_of_lt_of_le hcell (massOf_mono P.μ P.μ_nonneg (fun _ h => h.2))
    · intro p hp
      obtain ⟨ω, ⟨hpp, hc⟩, _⟩ := (massOf_pos_iff P.μ P.μ_nonneg _).mp hp
      have hω : Λ.chosen ω = p := hc
      have heff : Λ.eff p = Λ.eff π := by rw [← hpp, Λ.pp_eff ω, hω]
      have hppos : 0 < Λ.procMass p :=
        lt_of_lt_of_le hp (massOf_mono P.μ P.μ_nonneg (fun _ h => h.2))
      have : condExp P.μ P.U (fun ω => P.pp ω = Λ.eff π ∧ Λ.chosen ω = p) = Λ.procEU p := by
        rw [Λ.procEU_eq]
        apply condExp_congr
        intro ω
        constructor
        · exact And.right
        · intro h
          have hω' : Λ.chosen ω = p := h
          exact ⟨by rw [Λ.pp_eff ω, hω', heff], h⟩
      rw [this]
      exact hF p π heff hppos hπpos
  · intro hM p q hpq hp hq
    have hcellp : 0 < Λ.toModLayer.cellMass p (Λ.eff p) := by
      unfold ModLayer.cellMass
      refine lt_of_lt_of_le hp (massOf_mono P.μ P.μ_nonneg (fun ω h => ?_))
      have hω : Λ.chosen ω = p := h
      exact ⟨h, by rw [Λ.pp_eff ω, hω]⟩
    have hcellq : 0 < Λ.toModLayer.cellMass q (Λ.eff q) := by
      unfold ModLayer.cellMass
      refine lt_of_lt_of_le hq (massOf_mono P.μ P.μ_nonneg (fun ω h => ?_))
      have hω : Λ.chosen ω = q := h
      exact ⟨h, by rw [Λ.pp_eff ω, hω]⟩
    have h1 := hM p (Λ.eff p) hcellp
    have h2 := hM q (Λ.eff q) hcellq
    rw [Λ.cellEU_eff] at h1 h2
    have hpq' : Λ.eff p = Λ.eff q := hpq
    show Λ.procEU p = Λ.procEU q
    rw [h1, h2, hpq']

end PaperLayer

end Cleanroom.Udt.UdtPaperTiling
