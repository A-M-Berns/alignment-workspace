import Cleanroom.Bli.UdtBliCore.Basic

/-!
# `udt-bli-core` · Decomposition: the branch decomposition and the three influences (T4a, T4b)

(a) The one-step value decomposes over the branches (`EU_eq_sum_branch`) and, more generally,
over **any** finite partition of the outcome space (`EU_eq_sum_partition`): the tower identity
`𝔼_P(u | φ) = ∑_o P(o | φ) 𝔼_P(u | φ, o)` of bli-slides-037, the "weighted sum over any
partition" of bli-soto-b-2-023. Both are one `Finset.sum_comm` and are labelled `L`.

(b) The difference of two one-step values splits additively into the three named influences
of bli-soto-b-2-001 / bli-soto-a-019: **branch re-weighting** (the policy point changes the
relative probabilities of the other branches), **cross-branch utility** (it changes what the other
branches expect), and the **home-branch** term. This is the algebraic identity the updateful-
behaviour lemma (T5, `Updateful.lean`) and its ε-form rest on.

The refutation of the latest-common-ancestor rule (T4c) is in `Lca.lean`.
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

namespace FiniteBLIPrior

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A]
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A)

/-- **The branch decomposition of the one-step value**:
`EU T a = ∑_{T'} μ(state = T' | pp · T = a) · 𝔼[U | state = T' ∧ pp · T = a]`. Holds
unconditionally with the junk conventions (both sides are `0` at a null point); `NDPOL` is what
makes it the law of total probability.
Source: bli-soto-a-2-012 (ii); bli-soto-b-2-004 (iii); bli-slides-037 (the display)
Kind: L
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem EU_eq_sum_branch (T : ↥𝒟) (a : A) :
    P.EU T a = ∑ T', P.branchProb T' T a * P.condEU T' T a := by
  unfold EU
  rw [condExp_fiberwise P.μ P.U P.μ_nonneg _ P.state]
  have hc : ∀ T', massOf P.μ (fun ω => P.pp ω T = a ∧ P.state ω = T') = P.jointMass T' T a :=
    fun T' => massOf_congr _ (fun ω => and_comm)
  have hd : ∀ T', condExp P.μ P.U (fun ω => P.pp ω T = a ∧ P.state ω = T') = P.condEU T' T a :=
    fun T' => condExp_congr _ _ (fun ω => and_comm)
  simp only [hc, hd]
  rfl

/-- **Partition invariance**: the one-step value decomposes over *any* finite partition
`β : Ω → B` of the outcome space, as `∑_b μ(β = b | pp · T = a) · 𝔼[U | pp · T = a ∧ β = b]`.
So the verdict of the one-step rule does not depend on which observation partition one
decomposes over; the branch decomposition is the case `β = state`.
Source: bli-soto-b-2-023 ("UDT cares about a weighted sum over any *partition*"; the write-up's
"Decomposition-Invariance"); bli-soto-a-012 ("we can partition the expectation into any set of
mutually exclusive and jointly exhaustive observations we like")
Kind: L
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem EU_eq_sum_partition {B : Type} [Fintype B] [DecidableEq B] (β : P.Ω → B) (T : ↥𝒟)
    (a : A) :
    P.EU T a = ∑ b, massOf P.μ (fun ω => P.pp ω T = a ∧ β ω = b) / P.ppMass T a *
      condExp P.μ P.U (fun ω => P.pp ω T = a ∧ β ω = b) :=
  condExp_fiberwise P.μ P.U P.μ_nonneg _ β

/-! ## The three influences -/

/-- **Branch re-weighting influence** of choosing `a` over `b` at `T`: the change in the other
branches' probabilities, weighted by what those branches expect under `a`.
Source: bli-soto-b-2-001 (category (2)); bli-soto-a-019
Kind: D
Fidelity: exact -/
def reweightInfluence (T : ↥𝒟) (a b : A) : ℚ :=
  ∑ T' ∈ univ.erase T, (P.branchProb T' T a - P.branchProb T' T b) * P.condEU T' T a

/-- **Cross-branch utility influence** of choosing `a` over `b` at `T`: the change in what the
other branches expect, weighted by their probabilities under `b`.
Source: bli-soto-b-2-001 (category (1)); bli-soto-a-019
Kind: D
Fidelity: exact -/
def crossUtilInfluence (T : ↥𝒟) (a b : A) : ℚ :=
  ∑ T' ∈ univ.erase T, P.branchProb T' T b * (P.condEU T' T a - P.condEU T' T b)

/-- **Home-branch influence** of choosing `a` over `b` at `T`: the change in the home term
`μ(state = T | pp · T = ·) · homeEU T ·`.
Source: bli-soto-b-2-001 (category (3), "updateful impacts"); bli-soto-a-019
Kind: D
Fidelity: exact -/
def homeInfluence (T : ↥𝒟) (a b : A) : ℚ :=
  P.branchProb T T a * P.homeEU T a - P.branchProb T T b * P.homeEU T b

/-- **The three-influence split**: the difference of two one-step values is the sum of the
branch re-weighting, cross-branch utility and home-branch influences. Pure algebra on top of the
branch decomposition; it holds with the junk conventions at null points.
Source: bli-soto-b-2-001 (the three categories); bli-soto-a-019 (corollary: "the three
categories decompose additively"); journal ll. 141–145 ("what we throw away … correlations
between actions and the probability of branches … and the utility of other branches")
Kind: L (split the sum of `EU_eq_sum_branch` and `ring`; the content of T4(b) is the three
definitions)
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem EU_sub_EU_eq_three_influences (T : ↥𝒟) (a b : A) :
    P.EU T a - P.EU T b =
      P.reweightInfluence T a b + P.crossUtilInfluence T a b + P.homeInfluence T a b := by
  rw [P.EU_eq_sum_branch T a, P.EU_eq_sum_branch T b,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ T),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ T)]
  unfold reweightInfluence crossUtilInfluence homeInfluence homeEU
  have key : (∑ T' ∈ univ.erase T, (P.branchProb T' T a - P.branchProb T' T b) * P.condEU T' T a)
      + (∑ T' ∈ univ.erase T, P.branchProb T' T b * (P.condEU T' T a - P.condEU T' T b)) =
      ∑ T' ∈ univ.erase T,
        (P.branchProb T' T a * P.condEU T' T a - P.branchProb T' T b * P.condEU T' T b) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T' _
    ring
  rw [key, Finset.sum_sub_distrib]
  ring

end FiniteBLIPrior

end Cleanroom.Bli.UdtBliCore
