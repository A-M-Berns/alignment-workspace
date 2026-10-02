import Cleanroom.Bli.UdtBliCore.Updateful

/-!
# `udt-bli-core` · Good: Good's theorem for actual policies, and the one-level
"updateless ⊇ updateful" (T6, load-bearing 2; U4 + U11)

Everything here is about `exAnteValue π = 𝔼_μ[U | pp = π]`, the value of an **actual** policy
under the one measure `μ`, never about an array. The step that makes it so is
`cellEU_eq_homeEU`: under `LocalUtility` and `ReflectivePolicy`, what branch `T` expects given
the whole policy `π` is what it expects given only its own point `π T` — proved by averaging
(`condExp_eq_of_fibers`), not assumed. From it:

* `exAnteValue_eq_sepValue` — `exAnteValue π = ∑_T μ(state = T) · homeEU T (π T)` for every
  positive-mass policy (the program's array formula, *derived*);
* `good` — **Good's theorem**: deferring to any updateful policy weakly dominates every constant
  policy (precommitment);
* `good_strict_iff` — strict for every constant policy **iff no single action is an updateful
  choice at every positive-mass table** (the precise form of "the argmax varies");
* `priorOptimal_iff_updateful_on_support` — the prior-optimal policies are exactly the pointwise
  updateful ones on the support (bli-soto-b-2-016 (T1), one level);
* the corollary with T5: under the point-level predicates too, the one-step policy is prior-optimal.

Guards: the hypotheses are checked false on the mugging prior, where `LocalUtility` fails and a
precommitment beats every updateful policy (`Mugging.lean`); the XOR prior (`WitnessXor.lean`)
shows that the **point-level** package `Reflective ∧ NoCrossBranch` (with full positivity) does
not give `exAnteValue = sepValue`, nor Good's conclusion: `LocalUtility` is the hypothesis that
carries it; the correlated-points prior (`WitnessCorr.lean`) shows the converse gap, that
`ReflectivePolicy ∧ LocalUtility` does not give `NoCrossBranch`; the N+ inhabitant with a varying
maximizer is the tent prior (`OfSkeleton.lean`). The corollary with T5
(`priorOptimal_of_oneStepPolicy`) lives in `Bridges.lean`, after `reflective_of_reflectivePolicy`.
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

namespace FiniteBLIPrior

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A] [Fintype A]
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A)

/-- Under `ReflectivePolicy`, the cell mass factorizes: `cellMass T π = stateMass T · policyMass π`
for positive policies.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellMass_eq_of_reflectivePolicy (hR : P.ReflectivePolicy) (T : ↥𝒟) (π : Policy 𝒟 A)
    (hπ : 0 < P.policyMass π) : P.cellMass T π = P.stateMass T * P.policyMass π := by
  have := hR T π hπ
  rw [div_eq_iff (ne_of_gt hπ)] at this
  exact this

/-- A cell of a policy with `π T = a` sits inside the home cell `state = T ∧ pp · T = a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellMass_le_jointMass (T : ↥𝒟) (π : Policy 𝒟 A) (a : A) (h : π T = a) :
    P.cellMass T π ≤ P.jointMass T T a := by
  rw [P.jointMass_eq_sum_cellMass T T a]
  have : (if π T = a then P.cellMass T π else 0) = P.cellMass T π := if_pos h
  rw [← this]
  apply Finset.single_le_sum (f := fun π' => if π' T = a then P.cellMass T π' else 0)
    (fun π' _ => by split_ifs; exact P.cellMass_nonneg T π'; exact le_rfl) (Finset.mem_univ π)

/-- **The averaging step**: under `LocalUtility` and `ReflectivePolicy`, what branch `T` expects
given the whole policy `π` equals its updateful value `homeEU T (π T)`, at every positive policy
and positive table. Proof: the home cell `state = T ∧ pp · T = π T` is the union over the policies
`π'` with `π' T = π T` of the cells `state = T ∧ pp = π'`, all of which have the same conditional
expectation by `LocalUtility`, so the average equals it (`condExp_eq_of_fibers`).
Source: mandate T6(i) ("the step that makes the theorem about `μ`, not about an array");
bli-soto-b-2-016 (T1); bli-soto-a-011
Kind: P
Fidelity: exact
Hyps: (a) `ReflectivePolicy`, `LocalUtility`, `0 < policyMass π`, `0 < stateMass T`; does not
use faith -/
theorem cellEU_eq_homeEU (hR : P.ReflectivePolicy) (hL : P.LocalUtility) (π : Policy 𝒟 A)
    (hπ : 0 < P.policyMass π) (T : ↥𝒟) (hT : 0 < P.stateMass T) :
    P.cellEU T π = P.homeEU T (π T) := by
  have hcell : 0 < P.cellMass T π := by
    rw [P.cellMass_eq_of_reflectivePolicy hR T π hπ]; exact mul_pos hT hπ
  have hhome : 0 < P.jointMass T T (π T) :=
    lt_of_lt_of_le hcell (P.cellMass_le_jointMass T π (π T) rfl)
  symm
  unfold homeEU condEU
  apply condExp_eq_of_fibers P.μ P.U P.μ_nonneg _ P.pp (P.cellEU T π) hhome
  intro π' hπ'
  by_cases he : π' T = π T
  · have hcongr : condExp P.μ P.U (fun ω => (P.state ω = T ∧ P.pp ω T = π T) ∧ P.pp ω = π') =
        P.cellEU T π' := by
      apply condExp_congr
      intro ω
      constructor
      · rintro ⟨⟨hs, _⟩, hp⟩; exact ⟨hs, hp⟩
      · rintro ⟨hs, hp⟩; exact ⟨⟨hs, hp ▸ he⟩, hp⟩
    have hmass : P.cellMass T π' = massOf P.μ (fun ω => (P.state ω = T ∧ P.pp ω T = π T) ∧
        P.pp ω = π') := by
      apply massOf_congr
      intro ω
      constructor
      · rintro ⟨hs, hp⟩; exact ⟨⟨hs, hp ▸ he⟩, hp⟩
      · rintro ⟨⟨hs, _⟩, hp⟩; exact ⟨hs, hp⟩
    rw [hcongr]
    exact hL T π' π he (hmass ▸ hπ') hcell
  · exfalso
    have : massOf P.μ (fun ω => (P.state ω = T ∧ P.pp ω T = π T) ∧ P.pp ω = π') = 0 := by
      unfold massOf
      apply Finset.sum_eq_zero
      intro ω _
      rw [if_neg]
      rintro ⟨⟨_, hpa⟩, hp⟩
      exact he (hp ▸ hpa)
    rw [this] at hπ'
    exact lt_irrefl _ hπ'

/-- **The ex-ante value is the separable value** under the policy-level predicates:
`𝔼_μ[U | pp = π] = ∑_T μ(state = T) · homeEU T (π T)` for every positive-mass policy.
Source: [[bli-program]] §3.9 U4 (its array formula, derived here); mandate T6(i)
Kind: C
Fidelity: exact
Hyps: (a) `ReflectivePolicy`, `LocalUtility`, `0 < policyMass π`; does not use faith -/
theorem exAnteValue_eq_sepValue (hR : P.ReflectivePolicy) (hL : P.LocalUtility)
    (π : Policy 𝒟 A) (hπ : 0 < P.policyMass π) : P.exAnteValue π = P.sepValue π := by
  unfold exAnteValue sepValue
  rw [condExp_fiberwise P.μ P.U P.μ_nonneg _ P.state]
  apply Finset.sum_congr rfl
  intro T _
  have hc : massOf P.μ (fun ω => P.pp ω = π ∧ P.state ω = T) = P.cellMass T π :=
    massOf_congr _ (fun ω => and_comm)
  have hd : condExp P.μ P.U (fun ω => P.pp ω = π ∧ P.state ω = T) = P.cellEU T π :=
    condExp_congr _ _ (fun ω => and_comm)
  rw [hc, hd]
  change P.cellMass T π / P.policyMass π * P.cellEU T π = _
  rw [hR T π hπ]
  by_cases hT : 0 < P.stateMass T
  · rw [P.cellEU_eq_homeEU hR hL π hπ T hT]
  · have hz : P.stateMass T = 0 := le_antisymm (not_lt.mp hT) (P.stateMass_nonneg T)
    rw [hz, zero_mul, zero_mul]

/-- **Good's theorem** (load-bearing 2): under `ReflectivePolicy` and `LocalUtility`, every
updateful policy of positive mass weakly dominates, in ex-ante value, every constant policy of
positive mass. Deferral to the updateful rule is never worse than precommitment.
Source: [[bli-program]] §3.9 U4 ("deferring … weakly dominates every precommitted action");
bli-slides-032 (the diagnosis); bli-soto-b-2-016 ("optimal updateless behavior is a
generalization of optimal updateful behavior")
Kind: C (one `Finset.sum_le_sum` over `exAnteValue_eq_sepValue`; the P content is
`cellEU_eq_homeEU`)
Fidelity: exact (about `exAnteValue` of actual policies, both of positive mass)
Hyps: (a) `ReflectivePolicy`, `LocalUtility`, positivity of the two policies; does not use faith -/
theorem good (hR : P.ReflectivePolicy) (hL : P.LocalUtility) (πu : Policy 𝒟 A)
    (hu : P.IsUpdatefulPolicy πu) (hπu : 0 < P.policyMass πu) (a : A)
    (ha : 0 < P.policyMass (fun _ => a)) :
    P.exAnteValue (fun _ => a) ≤ P.exAnteValue πu := by
  rw [P.exAnteValue_eq_sepValue hR hL _ ha, P.exAnteValue_eq_sepValue hR hL _ hπu]
  unfold sepValue
  apply Finset.sum_le_sum
  intro T _
  exact mul_le_mul_of_nonneg_left (hu T a) (P.stateMass_nonneg T)

/-- **Strictness**: under `NDPOLICY` and the policy-level predicates, an updateful policy strictly
beats **every** constant policy iff **no single action is an updateful choice at every table of
positive mass**. (The program's "strict iff the argmax varies" is imprecise when maximizers are
not unique: what matters is the absence of a common maximizer over the support.)
Source: [[bli-program]] §3.9 U4 ("strictly iff the argmax varies across positive-mass tables");
mandate T6(iii)
Kind: P
Fidelity: variant: "the argmax varies" made precise as "no common updateful choice on the
support" (disclosed; presentation finding)
Hyps: (a) `NDPOLICY`, `ReflectivePolicy`, `LocalUtility`; does not use faith -/
theorem good_strict_iff (hpol : P.NDPOLICY) (hR : P.ReflectivePolicy) (hL : P.LocalUtility)
    (πu : Policy 𝒟 A) (hu : P.IsUpdatefulPolicy πu) :
    (∀ a, P.exAnteValue (fun _ => a) < P.exAnteValue πu) ↔
      ¬ ∃ a, ∀ T, 0 < P.stateMass T → P.IsUpdatefulChoice T a := by
  have hsep : ∀ π, P.exAnteValue π = P.sepValue π := fun π =>
    P.exAnteValue_eq_sepValue hR hL π (hpol π)
  simp only [hsep]
  unfold sepValue
  constructor
  · rintro hstrict ⟨a, hcommon⟩
    have heq : ∑ T, P.stateMass T * P.homeEU T a = ∑ T, P.stateMass T * P.homeEU T (πu T) := by
      apply Finset.sum_congr rfl
      intro T _
      by_cases hT : 0 < P.stateMass T
      · rw [le_antisymm (hu T a) (hcommon T hT (πu T))]
      · have hz : P.stateMass T = 0 := le_antisymm (not_lt.mp hT) (P.stateMass_nonneg T)
        rw [hz, zero_mul, zero_mul]
    exact lt_irrefl _ (heq ▸ hstrict a)
  · intro hno a
    have : ¬ ∀ T, 0 < P.stateMass T → P.IsUpdatefulChoice T a := fun h => hno ⟨a, h⟩
    obtain ⟨T, hT, hnot⟩ : ∃ T, 0 < P.stateMass T ∧ ¬ P.IsUpdatefulChoice T a := by
      by_contra hcon
      apply this
      intro T hT
      by_contra hn
      exact hcon ⟨T, hT, hn⟩
    obtain ⟨b, hb⟩ : ∃ b, P.homeEU T a < P.homeEU T b := by
      unfold IsUpdatefulChoice at hnot
      push_cast at hnot
      by_contra hcon
      apply hnot
      intro b
      by_contra hb
      exact hcon ⟨b, lt_of_not_ge hb⟩
    apply Finset.sum_lt_sum
    · intro T' _
      exact mul_le_mul_of_nonneg_left (hu T' a) (P.stateMass_nonneg T')
    · refine ⟨T, Finset.mem_univ T, ?_⟩
      apply mul_lt_mul_of_pos_left _ hT
      exact lt_of_lt_of_le hb (hu T b)

/-- **U11, one level: the prior-optimal policies are exactly the pointwise updateful ones on the
support.** Under `NDPOLICY`, `ReflectivePolicy`, `LocalUtility`:
`IsPriorOptimal π ↔ ∀ T, 0 < stateMass T → IsUpdatefulChoice T (π T)`.
Source: bli-soto-b-2-016 (T1) — the journal's words (ll. 643–645) are "optimal updateless
behavior is a generalization of optimal updateful behavior" and "classical UDT … achieves the
optimal policy for any single player game tree"; "the prior-optimal policy coincides at every
reachable node with the backward-induction (updateful) policy" is [[bli-soto-b-2-inventory]]'s
paraphrase, clause (T1) — on a one-level tree; [[bli-program]] §3.9 U11
Kind: P
Fidelity: exact (one level)
Hyps: (a) `NDPOLICY`, `ReflectivePolicy`, `LocalUtility`; does not use faith -/
theorem priorOptimal_iff_updateful_on_support (hpol : P.NDPOLICY) (hR : P.ReflectivePolicy)
    (hL : P.LocalUtility) (π : Policy 𝒟 A) :
    P.IsPriorOptimal π ↔ ∀ T, 0 < P.stateMass T → P.IsUpdatefulChoice T (π T) := by
  have hsep : ∀ π', P.exAnteValue π' = P.sepValue π' := fun π' =>
    P.exAnteValue_eq_sepValue hR hL π' (hpol π')
  constructor
  · intro hopt T hT b
    by_contra hlt
    have hlt' : P.homeEU T (π T) < P.homeEU T b := lt_of_not_ge hlt
    have := hopt (Function.update π T b)
    rw [hsep, hsep] at this
    unfold sepValue at this
    have hstrict : ∑ T', P.stateMass T' * P.homeEU T' (π T') <
        ∑ T', P.stateMass T' * P.homeEU T' (Function.update π T b T') := by
      apply Finset.sum_lt_sum
      · intro T' _
        by_cases h : T' = T
        · subst h
          rw [Function.update_self]
          exact mul_le_mul_of_nonneg_left hlt'.le (P.stateMass_nonneg T')
        · rw [Function.update_of_ne h]
      · refine ⟨T, Finset.mem_univ T, ?_⟩
        rw [Function.update_self]
        exact mul_lt_mul_of_pos_left hlt' hT
    exact lt_irrefl _ (lt_of_lt_of_le hstrict this)
  · intro hupd π'
    rw [hsep, hsep]
    unfold sepValue
    apply Finset.sum_le_sum
    intro T _
    by_cases hT : 0 < P.stateMass T
    · exact mul_le_mul_of_nonneg_left (hupd T hT (π' T)) (P.stateMass_nonneg T)
    · have hz : P.stateMass T = 0 := le_antisymm (not_lt.mp hT) (P.stateMass_nonneg T)
      rw [hz, zero_mul, zero_mul]

/-- Every updateful policy is prior-optimal (under `NDPOLICY` and the policy-level predicates).
Source: bli-soto-b-2-016 (T1); [[bli-program]] §3.9 U11
Kind: C
Fidelity: exact
Hyps: (a) `NDPOLICY`, `ReflectivePolicy`, `LocalUtility`; does not use faith -/
theorem priorOptimal_of_updatefulPolicy (hpol : P.NDPOLICY) (hR : P.ReflectivePolicy)
    (hL : P.LocalUtility) (π : Policy 𝒟 A) (hu : P.IsUpdatefulPolicy π) : P.IsPriorOptimal π :=
  (P.priorOptimal_iff_updateful_on_support hpol hR hL π).mpr (fun T _ => hu T)

/-! ## The guarded prior-optimality predicate and shift invariance (repair round 1) -/

/-- Under `NDPOLICY` the guarded and unguarded prior-optimality predicates agree.
Source: none: infrastructure (mandate T7, the policy-level junk case)
Kind: L
Fidelity: n/a -/
lemma isPriorOptimalOnSupport_iff (hpol : P.NDPOLICY) (π : Policy 𝒟 A) :
    P.IsPriorOptimalOnSupport π ↔ P.IsPriorOptimal π :=
  ⟨fun h π' => h π' (hpol π'), fun h π' _ => h π'⟩

/-- `IsPriorOptimal` implies the guarded form on every prior.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma isPriorOptimalOnSupport_of_isPriorOptimal {π : Policy 𝒟 A} (h : P.IsPriorOptimal π) :
    P.IsPriorOptimalOnSupport π :=
  fun π' _ => h π'

/-- **The prior with every utility raised by `c`** (same `μ`, `state`, `pp`, `small`; faith is
untouched). Adding a constant to `U` changes nothing about the decision problem, so an honest
optimality predicate must be invariant under it.
Source: none: infrastructure (audit r1 adversarial B1: the shift test)
Kind: D
Fidelity: n/a -/
def shiftU (c : ℚ) : FiniteBLIPrior 𝒮 m 𝒟 A :=
  { P with U := fun ω => P.U ω + c }

/-- The policy masses of the shifted prior are those of `P`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma policyMass_shiftU (c : ℚ) (π : Policy 𝒟 A) : (P.shiftU c).policyMass π = P.policyMass π :=
  rfl

/-- The ex-ante value of a **positive** policy shifts by `c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exAnteValue_shiftU (c : ℚ) (π : Policy 𝒟 A) (hπ : 0 < P.policyMass π) :
    (P.shiftU c).exAnteValue π = P.exAnteValue π + c := by
  have hm : massOf P.μ (fun ω => P.pp ω = π) ≠ 0 := ne_of_gt hπ
  change integralOf P.μ (fun ω => P.U ω + c) (fun ω => P.pp ω = π) /
      massOf P.μ (fun ω => P.pp ω = π) =
    integralOf P.μ P.U (fun ω => P.pp ω = π) / massOf P.μ (fun ω => P.pp ω = π) + c
  rw [integralOf_add, integralOf_const, add_div, mul_div_assoc, div_self hm, mul_one]

/-- **The guarded predicate is invariant under shifting `U` by a constant** (for a positive
policy). The unguarded `IsPriorOptimal` is not, on a prior with null policies: the correlated-points
prior shifted by `−2` (`WitnessGap.lean`, `Shift.corrShift_junk`).
Source: none: infrastructure (audit r1 adversarial B1)
Kind: P
Fidelity: n/a
Hyps: (a) `0 < policyMass π`; does not use faith -/
theorem isPriorOptimalOnSupport_shiftU_iff (c : ℚ) (π : Policy 𝒟 A) (hπ : 0 < P.policyMass π) :
    (P.shiftU c).IsPriorOptimalOnSupport π ↔ P.IsPriorOptimalOnSupport π := by
  unfold IsPriorOptimalOnSupport
  constructor
  · intro h π' hπ'
    have := h π' hπ'
    rw [P.exAnteValue_shiftU c π' hπ', P.exAnteValue_shiftU c π hπ] at this
    linarith
  · intro h π' hπ'
    have hπ'' : 0 < P.policyMass π' := hπ'
    rw [P.exAnteValue_shiftU c π' hπ'', P.exAnteValue_shiftU c π hπ]
    linarith [h π' hπ'']

end FiniteBLIPrior

end Cleanroom.Bli.UdtBliCore
