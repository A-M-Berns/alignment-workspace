import Cleanroom.Bli.UdtBliTiling.Defs
import Cleanroom.Bli.UdtBliCore.ProductUtil

/-!
# `udt-bli-tiling` · IndepCalc: values of an `IndepData` prior for a utility that reads the whole
policy (infrastructure for `SingleCoin.lean`)

`udt-bli-core`'s `ProductUtil` computes the values of `IndepData.toPrior` for utilities that read
the policy at **one** reference table (`EU_single`, `exAnteValue_single`, …). The sequential
single-coin model reads the policy at every `Ask_k` (that is the point: F17's sequential tree),
so the four lemmas here state the same values for a general `U₀ : Ω₀ → Policy → ℚ`:

* `exAnteValue_toPrior` — `𝔼[U | pp = π] = ∑_{ω₀} μ₀ ω₀ · U₀ ω₀ π` at a positive policy;
* `EU_toPrior` — `𝔼[U | pp · Q = a]` as the base sum of the policy-law conditional sums;
* `condExp_base_point`, `condExp_base_policy` — the same two with a base event `E₀` added to the
  conditional (what the two-step value and the re-frozen prior need);
* `conditionOn_exAnteValue_toPrior` — the ex-ante value under the prior re-frozen on a class of
  states, for an `IndepData` prior: the base is conditioned, the policy law is untouched.

All are `L`: bookkeeping over `massOf_rect` / `integralOf_U_rect`.
-/

namespace Cleanroom.Bli.UdtBliTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

namespace IndepCalc

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [Fintype A] [DecidableEq A]
variable (D : IndepData 𝒮 m 𝒟 A)

/-- The ex-ante value of a positive policy under an `IndepData` prior, for any utility:
`𝔼[U | pp = π] = ∑_{ω₀} μ₀ ω₀ · U₀ ω₀ π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exAnteValue_toPrior (π : Policy 𝒟 A) (hπ : 0 < D.ν π) :
    D.toPrior.exAnteValue π = ∑ ω₀, D.μ₀ ω₀ * D.U₀ ω₀ π := by
  unfold FiniteBLIPrior.exAnteValue condExp
  change D.toPrior.policyUtil π / D.toPrior.policyMass π = _
  rw [D.policyUtil_toPrior, D.policyMass_toPrior, mul_div_cancel_left₀ _ (ne_of_gt hπ)]

/-- The one-step value under an `IndepData` prior, for any utility: the base average of the
policy-law conditional sums, over the point mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EU_toPrior (Q : ↥𝒟) (a : A) :
    D.toPrior.EU Q a =
      (∑ ω₀, D.μ₀ ω₀ * ∑ π, (if π Q = a then D.ν π * D.U₀ ω₀ π else 0)) /
        massOf D.ν (fun π => π Q = a) := by
  unfold FiniteBLIPrior.EU condExp
  change D.toPrior.ppUtil Q a / D.toPrior.ppMass Q a = _
  rw [D.ppUtil_toPrior, D.ppMass_toPrior]

/-- The conditional expectation of the utility on `E₀ ∧ pp · Q = a`, for a base event `E₀`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condExp_base_point (E₀ : D.Ω₀ → Prop) [DecidablePred E₀] (Q : ↥𝒟) (a : A) :
    condExp D.μ (fun ω => D.U₀ ω.1 ω.2) (fun ω => E₀ ω.1 ∧ ω.2 Q = a) =
      (∑ ω₀, if E₀ ω₀ then D.μ₀ ω₀ * ∑ π, (if π Q = a then D.ν π * D.U₀ ω₀ π else 0) else 0) /
        (massOf D.μ₀ E₀ * massOf D.ν (fun π => π Q = a)) := by
  unfold condExp
  rw [D.integralOf_U_rect E₀ (fun π => π Q = a), D.massOf_rect E₀ (fun π => π Q = a)]

/-- The conditional expectation of the utility on `E₀ ∧ pp = π`, for a base event `E₀` and a
positive policy: the policy law cancels.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condExp_base_policy (E₀ : D.Ω₀ → Prop) [DecidablePred E₀] (π : Policy 𝒟 A)
    (hπ : 0 < D.ν π) :
    condExp D.μ (fun ω => D.U₀ ω.1 ω.2) (fun ω => E₀ ω.1 ∧ ω.2 = π) =
      (∑ ω₀, if E₀ ω₀ then D.μ₀ ω₀ * D.U₀ ω₀ π else 0) / massOf D.μ₀ E₀ := by
  unfold condExp
  rw [D.integralOf_U_rect E₀ (fun π' => π' = π), D.massOf_rect E₀ (fun π' => π' = π)]
  have hm : massOf D.ν (fun π' => π' = π) = D.ν π := by
    unfold massOf; simp
  have hi : ∀ ω₀, (∑ π', if π' = π then D.ν π' * D.U₀ ω₀ π' else 0) = D.ν π * D.U₀ ω₀ π := by
    intro ω₀; simp
  simp only [hi, hm]
  have hs : (∑ ω₀, if E₀ ω₀ then D.μ₀ ω₀ * (D.ν π * D.U₀ ω₀ π) else 0) =
      (∑ ω₀, if E₀ ω₀ then D.μ₀ ω₀ * D.U₀ ω₀ π else 0) * D.ν π := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ω₀ _
    split_ifs <;> ring
  rw [hs, mul_div_mul_right _ _ (ne_of_gt hπ)]

/-- The class mass of an `IndepData` prior is the base class mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma stateClassMass_toPrior (𝒞 : Finset ↥𝒟) :
    stateClassMass D.toPrior 𝒞 = massOf D.μ₀ (fun ω₀ => D.state₀ ω₀ ∈ 𝒞) := by
  have := D.massOf_rect (fun ω₀ => D.state₀ ω₀ ∈ 𝒞) (fun _ => True)
  have hν : massOf D.ν (fun _ => True) = 1 := by unfold massOf; simp [D.ν_sum_one]
  simp only [and_true, hν, mul_one] at this
  exact this

/-- **The ex-ante value under the re-frozen prior, for an `IndepData` prior**: the base is
conditioned on `state₀ ∈ 𝒞`, the policy law cancels.
Source: mandate T4(d) (`exAnteValue'`)
Kind: L
Fidelity: n/a -/
lemma conditionOn_exAnteValue_toPrior (𝒞 : Finset ↥𝒟) (h : 0 < stateClassMass D.toPrior 𝒞)
    (π : Policy 𝒟 A) (hπ : 0 < D.ν π) :
    (conditionOn D.toPrior 𝒞 h).exAnteValue π =
      (∑ ω₀, if D.state₀ ω₀ ∈ 𝒞 then D.μ₀ ω₀ * D.U₀ ω₀ π else 0) /
        massOf D.μ₀ (fun ω₀ => D.state₀ ω₀ ∈ 𝒞) := by
  rw [conditionOn_exAnteValue]
  exact condExp_base_policy D (fun ω₀ => D.state₀ ω₀ ∈ 𝒞) π hπ

/-- The one-step value under the re-frozen prior, for an `IndepData` prior.
Source: mandate T4(c)
Kind: L
Fidelity: n/a -/
lemma conditionOn_EU_toPrior (𝒞 : Finset ↥𝒟) (h : 0 < stateClassMass D.toPrior 𝒞) (Q : ↥𝒟)
    (a : A) :
    (conditionOn D.toPrior 𝒞 h).EU Q a =
      (∑ ω₀, if D.state₀ ω₀ ∈ 𝒞 then
          D.μ₀ ω₀ * ∑ π, (if π Q = a then D.ν π * D.U₀ ω₀ π else 0) else 0) /
        (massOf D.μ₀ (fun ω₀ => D.state₀ ω₀ ∈ 𝒞) * massOf D.ν (fun π => π Q = a)) := by
  rw [conditionOn_EU]
  exact condExp_base_point D (fun ω₀ => D.state₀ ω₀ ∈ 𝒞) Q a

end IndepCalc

end Cleanroom.Bli.UdtBliTiling
