import Cleanroom.Corrigibility.CorrScimCid.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

/-!
# The Eisenstat observation node: "I now believe this" as an observation (T10)

The CID form of `corr-reflect-frames`' probability-frame twin (corr-wf13-032). On the two-node DAG
`ω → O`, let `P : Distr Ω` be the prior, `b : B → Distr Ω` a finite family of candidate next
beliefs with weights `q : Distr B`. The observation node `O` with values in `B` has a CPD
(likelihood) `φ : Ω → Distr B`; its joint with `P` is `J(ω, β) = P(ω) φ(ω)(β)`.

* **Theorem (`exists_likelihood_iff`)**: there is a likelihood `φ` whose joint has `B`-marginal `q`
  and posterior `P(ω | O = β) = b β ω` at every `β ∈ supp q` **iff** the next beliefs are calibrated,
  `∀ ω, ∑_β q(β) b_β(ω) = P(ω)` (the martingale / reflection condition). The construction is
  `φ(ω)(β) := q(β) b_β(ω) / P(ω)`, which needs `P` strictly positive (the junk point; ⇒ does not).
* **Null case (`next_belief_null_of_null`)**: if `P(ω₀) = 0` then under the martingale condition no
  next belief in the support of `q` puts mass on `ω₀` — the opiates/stimulants agent of the sources.

ATTRIBUTION-UNVETTED: the sources attribute the "observation node = next belief" reading to
Eisenstat (corr-reflect-frames mandate, known issue 10); nothing here vets that attribution.

Source: positive/causal.md I3.2–I3.3 (corr-wf13-2-041).
-/

namespace Cleanroom.Corrigibility.CorrScimCid

open FactoredSpaces Finset

set_option linter.unusedSectionVars false

variable {Ω B : Type} [Fintype Ω] [Fintype B] [DecidableEq Ω] [DecidableEq B]

/-- The joint `J(ω, β) = P(ω) φ(ω)(β)` of a prior and a likelihood (the law of the two-node DAG
`ω → O` with CPD `φ` at `O`).
Source: causal.md I3.2
Kind: D -/
noncomputable def jointOf (P : Distr Ω) (φ : Ω → Distr B) : Distr (Ω × B) where
  mass p := P.mass p.1 * (φ p.1).mass p.2
  nonneg p := mul_nonneg (P.nonneg _) ((φ p.1).nonneg _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, Distr.sum_eq_one, mul_one]

/-- The `B`-marginal of the joint: `∑_ω P(ω) φ(ω)(β)`.
Source: causal.md I3.2
Kind: D -/
noncomputable def margB (P : Distr Ω) (φ : Ω → Distr B) (β : B) : ℝ :=
  ∑ ω, P.mass ω * (φ ω).mass β

/-- The posterior `P(ω | O = β)` as FAF's `condProb` on the joint.
Source: causal.md I3.2
Kind: D -/
noncomputable def posterior (P : Distr Ω) (φ : Ω → Distr B) (β : B) (ω : Ω) : ℝ :=
  (jointOf P φ).condProb {p | p.1 = ω} {p | p.2 = β}

lemma prob_snd_eq (P : Distr Ω) (φ : Ω → Distr B) (β : B) :
    (jointOf P φ).prob {p | p.2 = β} = margB P φ β := by
  classical
  unfold Distr.prob margB
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.sum_eq_single β]
  · simp [jointOf]
  · intro β' _ hβ'
    simp [Set.indicator_apply, hβ']
  · intro h
    exact absurd (Finset.mem_univ β) h

lemma prob_fst_snd_eq (P : Distr Ω) (φ : Ω → Distr B) (β : B) (ω : Ω) :
    (jointOf P φ).prob ({p | p.1 = ω} ∩ {p | p.2 = β}) = P.mass ω * (φ ω).mass β := by
  classical
  unfold Distr.prob
  rw [Fintype.sum_prod_type, Finset.sum_eq_single ω]
  · rw [Finset.sum_eq_single β]
    · simp [jointOf]
    · intro β' _ hβ'
      simp [Set.indicator_apply, hβ']
    · intro h
      exact absurd (Finset.mem_univ β) h
  · intro ω' _ hω'
    refine Finset.sum_eq_zero fun β' _ => ?_
    simp [Set.indicator_apply, hω']
  · intro h
    exact absurd (Finset.mem_univ ω) h

lemma posterior_eq (P : Distr Ω) (φ : Ω → Distr B) (β : B) (ω : Ω) :
    posterior P φ β ω = P.mass ω * (φ ω).mass β / margB P φ β := by
  unfold posterior Distr.condProb
  rw [prob_fst_snd_eq, prob_snd_eq]

/-- **The martingale (reflection) condition**: the weighted next beliefs average to the prior.
Source: causal.md I3.2 ("the calibration / martingale condition `E[B_{t+1}] = P`")
Kind: D -/
def Calibrated (P : Distr Ω) (b : B → Distr Ω) (q : Distr B) : Prop :=
  ∀ ω, ∑ β, q.mass β * (b β).mass ω = P.mass ω

/-- **The likelihood is representable as an observation node with marginal `q` and posteriors `b`.**
Source: causal.md I3.2
Kind: D -/
def Representable (P : Distr Ω) (b : B → Distr Ω) (q : Distr B) : Prop :=
  ∃ φ : Ω → Distr B, (∀ β, margB P φ β = q.mass β) ∧
    ∀ β, 0 < q.mass β → ∀ ω, posterior P φ β ω = (b β).mass ω

/-- **⇒: representability forces calibration** (no positivity needed): the joint mass at `(ω, β)`
is `q(β) b_β(ω)` on the support of `q` and `0` off it, and summing over `β` gives `P(ω)`.
Source: causal.md I3.2
Kind: P -/
theorem calibrated_of_representable {P : Distr Ω} {b : B → Distr Ω} {q : Distr B}
    (h : Representable P b q) : Calibrated P b q := by
  obtain ⟨φ, hm, hpost⟩ := h
  intro ω
  have hJ : ∀ β, q.mass β * (b β).mass ω = P.mass ω * (φ ω).mass β := by
    intro β
    rcases (q.nonneg β).lt_or_eq with hq | hq
    · have hp := hpost β hq ω
      rw [posterior_eq, hm β] at hp
      rw [← hp, mul_div_cancel₀ _ hq.ne']
    · have hmarg : margB P φ β = 0 := by rw [hm, hq]
      have hterm : P.mass ω * (φ ω).mass β = 0 := by
        have hsum : ∑ ω', P.mass ω' * (φ ω').mass β = 0 := hmarg
        exact (Finset.sum_eq_zero_iff_of_nonneg fun ω' _ =>
          mul_nonneg (P.nonneg _) ((φ ω').nonneg _)).mp hsum ω (Finset.mem_univ _)
      rw [← hq, zero_mul, hterm]
  calc ∑ β, q.mass β * (b β).mass ω = ∑ β, P.mass ω * (φ ω).mass β := Finset.sum_congr rfl fun β _ => hJ β
    _ = P.mass ω * ∑ β, (φ ω).mass β := by rw [Finset.mul_sum]
    _ = P.mass ω := by rw [(φ ω).sum_eq_one, mul_one]

/-- **The Eisenstat likelihood** `φ(ω)(β) = q(β) b_β(ω) / P(ω)`, a `Distr B` for each `ω` when `P` is
strictly positive and the beliefs are calibrated.
Source: causal.md I3.2 ("set `P(b | ω) := P(b) b(ω) / P(ω)`")
Kind: D -/
noncomputable def eisenstatLik (P : Distr Ω) (b : B → Distr Ω) (q : Distr B)
    (hP : P.StrictlyPositive) (hc : Calibrated P b q) (ω : Ω) : Distr B where
  mass β := q.mass β * (b β).mass ω / P.mass ω
  nonneg β := div_nonneg (mul_nonneg (q.nonneg _) ((b β).nonneg _)) (hP ω).le
  sum_eq_one := by
    rw [← Finset.sum_div, hc ω, div_self (hP ω).ne']

/-- **⇐: calibration gives the representation** (with `P` strictly positive): the Eisenstat
likelihood has `B`-marginal `q` and posterior `b_β` at every `β` in the support of `q`.
Source: causal.md I3.2
Kind: P -/
theorem representable_of_calibrated {P : Distr Ω} {b : B → Distr Ω} {q : Distr B}
    (hP : P.StrictlyPositive) (hc : Calibrated P b q) : Representable P b q := by
  refine ⟨eisenstatLik P b q hP hc, fun β => ?_, fun β hq ω => ?_⟩
  · unfold margB
    simp only [eisenstatLik]
    have : ∀ ω, P.mass ω * (q.mass β * (b β).mass ω / P.mass ω) = q.mass β * (b β).mass ω :=
      fun ω => mul_div_cancel₀ _ (hP ω).ne'
    simp only [this, ← Finset.mul_sum, (b β).sum_eq_one, mul_one]
  · have hm : margB P (eisenstatLik P b q hP hc) β = q.mass β := by
      unfold margB
      simp only [eisenstatLik]
      have : ∀ ω, P.mass ω * (q.mass β * (b β).mass ω / P.mass ω) = q.mass β * (b β).mass ω :=
        fun ω => mul_div_cancel₀ _ (hP ω).ne'
      simp only [this, ← Finset.mul_sum, (b β).sum_eq_one, mul_one]
    rw [posterior_eq, hm]
    simp only [eisenstatLik]
    rw [mul_div_cancel₀ _ (hP ω).ne', mul_comm, mul_div_assoc, div_self hq.ne', mul_one]

/-- **T10, the iff**: with a strictly positive prior, "I now believe this" is representable as an
observation node iff the next beliefs satisfy the martingale condition.
Source: causal.md I3.2 (corr-wf13-2-041)
Kind: P
Fidelity: exact (strict positivity assumed for the construction; the null case is
`next_belief_null_of_null`)
Hyps: — -/
theorem exists_likelihood_iff {P : Distr Ω} (hP : P.StrictlyPositive) (b : B → Distr Ω)
    (q : Distr B) : Representable P b q ↔ Calibrated P b q :=
  ⟨calibrated_of_representable, representable_of_calibrated hP⟩

/-- **The null case (I3.3)**: if the prior gives `ω₀` no mass, no calibrated next belief in the
support of `q` reaches it.
Source: causal.md I3.3 ("no `b ≪ P` puts mass on it")
Kind: P
Fidelity: exact
Hyps: — -/
theorem next_belief_null_of_null {P : Distr Ω} {b : B → Distr Ω} {q : Distr B}
    (hc : Calibrated P b q) {ω₀ : Ω} (h0 : P.mass ω₀ = 0) {β : B} (hq : 0 < q.mass β) :
    (b β).mass ω₀ = 0 := by
  have hsum : ∑ β', q.mass β' * (b β').mass ω₀ = 0 := by rw [hc ω₀, h0]
  have := (Finset.sum_eq_zero_iff_of_nonneg fun β' _ =>
    mul_nonneg (q.nonneg _) ((b β').nonneg _)).mp hsum β (Finset.mem_univ _)
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hq.ne'
  · exact h

end Cleanroom.Corrigibility.CorrScimCid
