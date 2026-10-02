import Cleanroom.Bli.BliTrajectory.Partition

/-!
# `bli-trajectory` · Pinning: with two *distinct* tables, faith in the marginal pins faith in
the state (repair round 2)

Adopted from audit r2's adversarial probe `audit-r2-probes/Pinning.lean` (the auditor's
`two_state_pinning`, reproduced with its proof), and extended to a Boolean-closed scope
(`two_state_pinning_scope`). The point: the refutations `Refutations.faithMarginal_not_imp_e2x`
and `Coherent.faithMarginal_coherent_not_imp_e2x` need their two candidate tables to be
**identical** — and this file shows why. Over a two-state system whose tables are distinct and
finitely additive, with the market a finite mixture of FAF worlds, faith in the marginals on a
scope closed under `⋏` and `∼` forces constraint 2 on that scope. So the `p ± δ` counterexample
with two states lives on the non-injectivity of `bli-found`'s abstract `StateSystem`; the
refutation that survives the injective reading needs three states (`TriState.lean`).

Hypotheses are stated at the instances used (not as `FaithMarginal` on `Sminus m m`), with `hP`
the explicit world mixture (`CoherentOn ∅` unpacked), to keep the size bookkeeping out.
-/

namespace Cleanroom.Bli.BliTrajectory

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

open Classical

noncomputable section

/-- **Two distinct tables pin the conditional** (audit r2 adversarial probe, adopted). Over a
two-state system whose tables differ on a sentence `ψ` that one table decides true and the
other false, with the tables multiplicative at `φ ⋏ ψ` and the market a finite mixture of FAF
worlds, faith in the marginal at `ψ` and at `φ ⋏ ψ` forces constraint 2 at `φ` for the first
state: `𝐏_n(φ ⋏ σ₁) = 𝑸̂₁[φ] · 𝐏_n(σ₁)`. Mechanism: faith at `ψ` (value `1` only on `q₁`) makes
every charged world holding `σ₁` hold `ψ`; faith at `φ ⋏ ψ` (table value `𝑸̂₁[φ]`, unique to
`q₁` when nonzero) then pins `𝐏_n(φ ⋏ ψ ⋏ σ₁) = 𝐏_n(φ ⋏ σ₁)`.
Source: audit r2 adversarial B1 (probe `Pinning.lean`); bli-slides-015 (b); mandate M7 (ii)/(iii)
Kind: P
Fidelity: exact (abstract; hypotheses at the instances used)
Hyps: (a) all explicit: the two-state system, the world mixture, the decided sentence, the
multiplicative tables, faith at the two instances -/
theorem two_state_pinning (S : StateSystem) (P : History) (n m : ℕ) (q₁ q₂ : ℕ)
    (hq : S.states m = {q₁, q₂}) (hne : q₁ ≠ q₂)
    (k : ℕ) (W : Fin k → PCWorld) (w : Fin k → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hP : ∀ χ, P n χ = ∑ i, w i * (W i).payout χ)
    (φ ψ : Sentence)
    (hψ₁ : S.val m q₁ ψ = 1) (hψ₂ : S.val m q₂ ψ = 0)
    (hmul : ∀ q, S.val m q (φ ⋏ ψ) = S.val m q φ * S.val m q ψ)
    (hFMψ : ∀ x, marginalJoint S P n m ψ x = x * marginalMass S P n m ψ x)
    (hFMφψ : ∀ x, marginalJoint S P n m (φ ⋏ ψ) x = x * marginalMass S P n m (φ ⋏ ψ) x) :
    P n (φ ⋏ stateAtom m q₁) = S.val m q₁ φ * P n (stateAtom m q₁) := by
  set σ₁ := stateAtom m q₁ with hσ₁
  set σ₂ := stateAtom m q₂ with hσ₂
  -- the mixture is nonnegative
  have hnonneg : ∀ χ, 0 ≤ P n χ := by
    intro χ; rw [hP]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (payout_mem_Icc (W i) χ).1
  -- the marginals over the two codes
  have hJ : ∀ χ x, marginalJoint S P n m χ x =
      (if S.val m q₁ χ = x then P n (χ ⋏ σ₁) else 0) +
        (if S.val m q₂ χ = x then P n (χ ⋏ σ₂) else 0) := by
    intro χ x; unfold marginalJoint; rw [Finset.sum_filter, hq, Finset.sum_pair hne]
  have hM : ∀ χ x, marginalMass S P n m χ x =
      (if S.val m q₁ χ = x then P n σ₁ else 0) + (if S.val m q₂ χ = x then P n σ₂ else 0) := by
    intro χ x; unfold marginalMass; rw [Finset.sum_filter, hq, Finset.sum_pair hne]
  -- step 1: faith at `ψ`, value `1`: `𝐏_n(ψ ⋏ σ₁) = 𝐏_n(σ₁)`
  have h1 := hFMψ 1
  rw [hJ, hM, if_pos hψ₁, if_neg (by rw [hψ₂]; norm_num), if_pos hψ₁,
    if_neg (by rw [hψ₂]; norm_num)] at h1
  -- hence every charged world holding `σ₁` holds `ψ`
  have hterm : ∀ i, w i * ((1 - (W i).payout ψ) * (W i).payout σ₁) = 0 := by
    have hsum : ∑ i, w i * ((1 - (W i).payout ψ) * (W i).payout σ₁) = 0 := by
      have e : ∑ i, w i * ((1 - (W i).payout ψ) * (W i).payout σ₁) =
          P n σ₁ - P n (ψ ⋏ σ₁) := by
        rw [hP σ₁, hP (ψ ⋏ σ₁), ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [payout_and]; ring
      rw [e]; linarith
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin k)),
        0 ≤ w i * ((1 - (W i).payout ψ) * (W i).payout σ₁) := by
      intro i _
      have hψi := payout_mem_Icc (W i) ψ
      have hσi := payout_mem_Icc (W i) σ₁
      exact mul_nonneg (hw i) (mul_nonneg (by linarith) hσi.1)
    have key := (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset (Fin k)))
      (f := fun i => w i * ((1 - (W i).payout ψ) * (W i).payout σ₁)) hnn).mp hsum
    exact fun i => key i (Finset.mem_univ i)
  -- step 2: `𝐏_n(φ ⋏ σ₁) = 𝐏_n((φ ⋏ ψ) ⋏ σ₁)`
  have h2 : P n (φ ⋏ σ₁) = P n ((φ ⋏ ψ) ⋏ σ₁) := by
    rw [hP, hP]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [payout_and, payout_and, payout_and]
    linear_combination (W i).payout φ * hterm i
  -- step 3: faith at `φ ⋏ ψ`
  have hv₁ : S.val m q₁ (φ ⋏ ψ) = S.val m q₁ φ := by rw [hmul, hψ₁, mul_one]
  have hv₂ : S.val m q₂ (φ ⋏ ψ) = 0 := by rw [hmul, hψ₂, mul_zero]
  by_cases ha : S.val m q₁ φ = 0
  · have h3 := hFMφψ 0
    rw [hJ, hM, if_pos (by rw [hv₁, ha]), if_pos hv₂, zero_mul] at h3
    have := hnonneg ((φ ⋏ ψ) ⋏ σ₁)
    have := hnonneg ((φ ⋏ ψ) ⋏ σ₂)
    rw [h2, ha, zero_mul]; linarith
  · have h3 := hFMφψ (S.val m q₁ φ)
    rw [hJ, hM, if_pos hv₁, if_neg (by rw [hv₂]; exact fun h => ha h.symm), if_pos hv₁,
      if_neg (by rw [hv₂]; exact fun h => ha h.symm)] at h3
    rw [h2]; linarith

/-! ## Boolean-closed scope: distinct additive tables are pinned everywhere -/

/-- Faith in the marginal at one sentence, for a two-state system, in the only two shapes it can
take: if the tables agree at `χ`, the two joints sum to the common value times the two masses;
if they differ, each joint is its own table value times its own mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma two_state_faith_cases (S : StateSystem) (P : History) (n m : ℕ) (q₁ q₂ : ℕ)
    (hq : S.states m = {q₁, q₂}) (hne : q₁ ≠ q₂) (χ : Sentence)
    (hFM : ∀ x, marginalJoint S P n m χ x = x * marginalMass S P n m χ x) :
    (S.val m q₁ χ = S.val m q₂ χ →
      P n (χ ⋏ stateAtom m q₁) + P n (χ ⋏ stateAtom m q₂) =
        S.val m q₁ χ * (P n (stateAtom m q₁) + P n (stateAtom m q₂))) ∧
    (S.val m q₁ χ ≠ S.val m q₂ χ →
      P n (χ ⋏ stateAtom m q₁) = S.val m q₁ χ * P n (stateAtom m q₁) ∧
      P n (χ ⋏ stateAtom m q₂) = S.val m q₂ χ * P n (stateAtom m q₂)) := by
  have hJ : ∀ x, marginalJoint S P n m χ x =
      (if S.val m q₁ χ = x then P n (χ ⋏ stateAtom m q₁) else 0) +
        (if S.val m q₂ χ = x then P n (χ ⋏ stateAtom m q₂) else 0) := by
    intro x; unfold marginalJoint; rw [Finset.sum_filter, hq, Finset.sum_pair hne]
  have hM : ∀ x, marginalMass S P n m χ x =
      (if S.val m q₁ χ = x then P n (stateAtom m q₁) else 0) +
        (if S.val m q₂ χ = x then P n (stateAtom m q₂) else 0) := by
    intro x; unfold marginalMass; rw [Finset.sum_filter, hq, Finset.sum_pair hne]
  constructor
  · intro heq
    have h := hFM (S.val m q₁ χ)
    rw [hJ, hM, if_pos rfl, if_pos heq.symm, if_pos rfl, if_pos heq.symm] at h
    linarith
  · intro hd
    constructor
    · have h := hFM (S.val m q₁ χ)
      rw [hJ, hM, if_pos rfl, if_neg (Ne.symm hd), if_pos rfl, if_neg (Ne.symm hd)] at h
      linarith
    · have h := hFM (S.val m q₂ χ)
      rw [hJ, hM, if_neg hd, if_pos rfl, if_neg hd, if_pos rfl] at h
      linarith

/-- One state, one cell: from constraint 2 at `α` and at `∼χ ⋏ α`, constraint 2 at `α ⋏ χ`
(additivity and commutativity of the table and of the market inside the state).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pin_and_of_pin (S : StateSystem) (P : History) (n m q : ℕ) (Γ : Set Sentence)
    (hadd : ∀ φ ∈ Γ, ∀ χ ∈ Γ, S.val m q (φ ⋏ χ) + S.val m q (∼φ ⋏ χ) = S.val m q χ)
    (hcomm : ∀ φ ∈ Γ, ∀ χ ∈ Γ, S.val m q (φ ⋏ χ) = S.val m q (χ ⋏ φ))
    (hPadd : ∀ φ ∈ Γ, ∀ χ ∈ Γ,
      P n ((φ ⋏ χ) ⋏ stateAtom m q) + P n ((∼φ ⋏ χ) ⋏ stateAtom m q) = P n (χ ⋏ stateAtom m q))
    (hPcomm : ∀ φ ∈ Γ, ∀ χ ∈ Γ,
      P n ((φ ⋏ χ) ⋏ stateAtom m q) = P n ((χ ⋏ φ) ⋏ stateAtom m q))
    {α χ : Sentence} (hα : α ∈ Γ) (hχ : χ ∈ Γ)
    (h1 : P n (α ⋏ stateAtom m q) = S.val m q α * P n (stateAtom m q))
    (h2 : P n ((∼χ ⋏ α) ⋏ stateAtom m q) = S.val m q (∼χ ⋏ α) * P n (stateAtom m q)) :
    P n ((α ⋏ χ) ⋏ stateAtom m q) = S.val m q (α ⋏ χ) * P n (stateAtom m q) := by
  have a := hadd χ hχ α hα
  have b := hPadd χ hχ α hα
  have c := hcomm α hα χ hχ
  have d := hPcomm α hα χ hχ
  rw [d, c]
  linear_combination b + h1 - h2 - P n (stateAtom m q) * a

/-- **Two distinct additive tables are pinned on a Boolean-closed scope.** Let `Γ` be a family of
sentences closed under `⋏` and `∼`; let both tables be finitely additive and commutative on `Γ`
(`val (φ ⋏ χ) + val (∼φ ⋏ χ) = val χ`, `val (∼φ) = 1 − val φ`, `val (φ ⋏ χ) = val (χ ⋏ φ)`) and the
market additive and commutative there inside each state (`𝐏_n((φ ⋏ χ) ⋏ σ) + 𝐏_n((∼φ ⋏ χ) ⋏ σ) =
𝐏_n(χ ⋏ σ)`, `𝐏_n((φ ⋏ χ) ⋏ σ) = 𝐏_n((χ ⋏ φ) ⋏ σ)`) — all true of FAF world mixtures; let faith
in the marginal hold at every sentence of `Γ`, and let the tables differ at some `φ ∈ Γ`. Then
constraint 2 holds at every `χ ∈ Γ`, for both states. Proof: where the tables differ at `χ`,
faith pins directly (`two_state_faith_cases`); where they agree, split `χ` along `φ`. If the
tables differ at the cell `φ ⋏ χ` they differ at `∼φ ⋏ χ` too, and both cells are pinned. If
they agree at `φ ⋏ χ`, then they differ at `∼χ ⋏ φ` (since they differ at `φ`) and at
`∼χ ⋏ ∼φ` (since they differ at `∼φ` and agree at `∼φ ⋏ χ`), so `φ` and `∼φ` and those two
cells are pinned, and `pin_and_of_pin` pins `φ ⋏ χ` and `∼φ ⋏ χ` by subtraction. Either way
`χ ⋏ σ` is the sum of its two pinned cells. So with two states the `p ± δ` counterexample needs
identical tables (`Coherent.cohSystem`, `Refutations.twoSystem`) — or three states
(`TriState.lean`).
Source: audit r2 adversarial B1 (the probe's remark "the general case is open"); mandate M7 (iii)
Kind: P
Fidelity: exact (abstract; `Γ` and the Boolean laws are explicit hypotheses — `CoherentOn ∅` for
the market and the tables supplies them on any `⋏`/`∼`-closed family)
Hyps: (a) all explicit: `Γ` closed under `⋏` and `∼`; the Boolean laws of tables and market;
faith on `Γ`; a sentence of `Γ` where the tables differ -/
theorem two_state_pinning_scope (S : StateSystem) (P : History) (n m : ℕ) (q₁ q₂ : ℕ)
    (hq : S.states m = {q₁, q₂}) (hne : q₁ ≠ q₂)
    (Γ : Set Sentence) (hΓand : ∀ φ ∈ Γ, ∀ χ ∈ Γ, φ ⋏ χ ∈ Γ) (hΓneg : ∀ φ ∈ Γ, ∼φ ∈ Γ)
    (hadd : ∀ q, ∀ φ ∈ Γ, ∀ χ ∈ Γ, S.val m q (φ ⋏ χ) + S.val m q (∼φ ⋏ χ) = S.val m q χ)
    (hneg : ∀ q, ∀ φ ∈ Γ, S.val m q (∼φ) = 1 - S.val m q φ)
    (hcomm : ∀ q, ∀ φ ∈ Γ, ∀ χ ∈ Γ, S.val m q (φ ⋏ χ) = S.val m q (χ ⋏ φ))
    (hPadd : ∀ q, ∀ φ ∈ Γ, ∀ χ ∈ Γ,
      P n ((φ ⋏ χ) ⋏ stateAtom m q) + P n ((∼φ ⋏ χ) ⋏ stateAtom m q) = P n (χ ⋏ stateAtom m q))
    (hPcomm : ∀ q, ∀ φ ∈ Γ, ∀ χ ∈ Γ,
      P n ((φ ⋏ χ) ⋏ stateAtom m q) = P n ((χ ⋏ φ) ⋏ stateAtom m q))
    (hFM : ∀ χ ∈ Γ, ∀ x, marginalJoint S P n m χ x = x * marginalMass S P n m χ x)
    (φ : Sentence) (hφ : φ ∈ Γ) (hdiff : S.val m q₁ φ ≠ S.val m q₂ φ) :
    ∀ χ ∈ Γ, P n (χ ⋏ stateAtom m q₁) = S.val m q₁ χ * P n (stateAtom m q₁) ∧
      P n (χ ⋏ stateAtom m q₂) = S.val m q₂ χ * P n (stateAtom m q₂) := by
  intro χ hχ
  have pin : ∀ ψ ∈ Γ, S.val m q₁ ψ ≠ S.val m q₂ ψ →
      P n (ψ ⋏ stateAtom m q₁) = S.val m q₁ ψ * P n (stateAtom m q₁) ∧
      P n (ψ ⋏ stateAtom m q₂) = S.val m q₂ ψ * P n (stateAtom m q₂) :=
    fun ψ hψ hd => (two_state_faith_cases S P n m q₁ q₂ hq hne ψ (hFM ψ hψ)).2 hd
  by_cases hd : S.val m q₁ χ = S.val m q₂ χ
  swap
  · exact pin χ hχ hd
  have hnφ := hΓneg φ hφ
  have hnχ := hΓneg χ hχ
  have hφχ := hΓand φ hφ χ hχ
  have hnφχ := hΓand (∼φ) hnφ χ hχ
  have hnχφ := hΓand (∼χ) hnχ φ hφ
  have hnχnφ := hΓand (∼χ) hnχ (∼φ) hnφ
  -- the split of `χ` along `φ`, for both tables
  have s1 := hadd q₁ φ hφ χ hχ
  have s2 := hadd q₂ φ hφ χ hχ
  -- once both cells `φ ⋏ χ`, `∼φ ⋏ χ` are pinned, `χ` is
  have finish :
      (P n ((φ ⋏ χ) ⋏ stateAtom m q₁) = S.val m q₁ (φ ⋏ χ) * P n (stateAtom m q₁) ∧
        P n ((φ ⋏ χ) ⋏ stateAtom m q₂) = S.val m q₂ (φ ⋏ χ) * P n (stateAtom m q₂)) →
      (P n ((∼φ ⋏ χ) ⋏ stateAtom m q₁) = S.val m q₁ (∼φ ⋏ χ) * P n (stateAtom m q₁) ∧
        P n ((∼φ ⋏ χ) ⋏ stateAtom m q₂) = S.val m q₂ (∼φ ⋏ χ) * P n (stateAtom m q₂)) →
      P n (χ ⋏ stateAtom m q₁) = S.val m q₁ χ * P n (stateAtom m q₁) ∧
        P n (χ ⋏ stateAtom m q₂) = S.val m q₂ χ * P n (stateAtom m q₂) := by
    rintro ⟨c1, c2⟩ ⟨d1, d2⟩
    have p1 := hPadd q₁ φ hφ χ hχ
    have p2 := hPadd q₂ φ hφ χ hχ
    constructor
    · linear_combination -p1 + c1 + d1 + P n (stateAtom m q₁) * s1
    · linear_combination -p2 + c2 + d2 + P n (stateAtom m q₂) * s2
  by_cases hc : S.val m q₁ (φ ⋏ χ) = S.val m q₂ (φ ⋏ χ)
  · -- the tables agree at `φ ⋏ χ` (hence at `∼φ ⋏ χ`): go through `∼χ ⋏ φ` and `∼χ ⋏ ∼φ`
    have hc' : S.val m q₁ (∼φ ⋏ χ) = S.val m q₂ (∼φ ⋏ χ) := by linarith
    -- `∼χ ⋏ φ` differs: `val (χ ⋏ φ) + val (∼χ ⋏ φ) = val φ`, and `val (χ ⋏ φ) = val (φ ⋏ χ)` agrees
    have t1 := hadd q₁ χ hχ φ hφ
    have t2 := hadd q₂ χ hχ φ hφ
    have u1 := hcomm q₁ χ hχ φ hφ
    have u2 := hcomm q₂ χ hχ φ hφ
    have hA : S.val m q₁ (∼χ ⋏ φ) ≠ S.val m q₂ (∼χ ⋏ φ) := by
      intro h; apply hdiff; linarith
    -- `∼χ ⋏ ∼φ` differs: `val (χ ⋏ ∼φ) + val (∼χ ⋏ ∼φ) = val (∼φ) = 1 − val φ`, and
    -- `val (χ ⋏ ∼φ) = val (∼φ ⋏ χ)` agrees
    have v1 := hadd q₁ χ hχ (∼φ) hnφ
    have v2 := hadd q₂ χ hχ (∼φ) hnφ
    have w1 := hcomm q₁ χ hχ (∼φ) hnφ
    have w2 := hcomm q₂ χ hχ (∼φ) hnφ
    have n1 := hneg q₁ φ hφ
    have n2 := hneg q₂ φ hφ
    have hB : S.val m q₁ (∼χ ⋏ ∼φ) ≠ S.val m q₂ (∼χ ⋏ ∼φ) := by
      intro h; apply hdiff; linarith
    have hnφd : S.val m q₁ (∼φ) ≠ S.val m q₂ (∼φ) := by
      intro h; apply hdiff; linarith
    obtain ⟨pφ1, pφ2⟩ := pin φ hφ hdiff
    obtain ⟨pA1, pA2⟩ := pin _ hnχφ hA
    obtain ⟨pnφ1, pnφ2⟩ := pin _ hnφ hnφd
    obtain ⟨pB1, pB2⟩ := pin _ hnχnφ hB
    apply finish
    · exact ⟨pin_and_of_pin S P n m q₁ Γ (hadd q₁) (hcomm q₁) (hPadd q₁) (hPcomm q₁) hφ hχ pφ1 pA1,
        pin_and_of_pin S P n m q₂ Γ (hadd q₂) (hcomm q₂) (hPadd q₂) (hPcomm q₂) hφ hχ pφ2 pA2⟩
    · exact ⟨pin_and_of_pin S P n m q₁ Γ (hadd q₁) (hcomm q₁) (hPadd q₁) (hPcomm q₁) hnφ hχ pnφ1 pB1,
        pin_and_of_pin S P n m q₂ Γ (hadd q₂) (hcomm q₂) (hPadd q₂) (hPcomm q₂) hnφ hχ pnφ2 pB2⟩
  · -- the tables differ at `φ ⋏ χ`, hence at `∼φ ⋏ χ`: both cells pinned directly
    have hc' : S.val m q₁ (∼φ ⋏ χ) ≠ S.val m q₂ (∼φ ⋏ χ) := by
      intro h; apply hc; linarith
    exact finish (pin _ hφχ hc) (pin _ hnφχ hc')

end

end Cleanroom.Bli.BliTrajectory
