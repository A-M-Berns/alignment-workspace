import Cleanroom.Bli.UdtBliCore.Bridges
import Mathlib.Algebra.BigOperators.Field

/-!
# `udt-bli-tiling` · Defs: no strict preference for precommitment, the conditioned prior,
self-trust (T1 D; mandate §3.1, §3.4, T8)

The definitions of record of this package, all over `udt-bli-core`'s `FiniteBLIPrior`:

* `NoStrictPrecommitAt P π T` / `NoStrictPrecommit P π` — **tiling as a comparison of
  `exAnteValue` between positive-mass policies under one prior** (mandate §3.1): the policy `π`
  has positive mass, and no one-point precommitment `Function.update π T b` of positive mass has
  a strictly larger ex-ante value. The guards keep the junk `0` of a null policy out (core F-4);
  under `NDPOLICY` they are discharged (`noStrictPrecommitAt_iff_of_ndpolicy`).
* The policy-level fact `IsPriorOptimalOnSupport π → NoStrictPrecommit π` is one line
  (`noStrictPrecommit_of_priorOptimalOnSupport`): **Kind `T`, never a headline** (mandate §3.2).
* `conditionOn P 𝒞 h` — **the prior re-frozen on a class of states** `𝒞` (mandate §3.4 D): the
  same outcome space, `μ` restricted to `state ∈ 𝒞` and renormalized, `pp`, `U`, `small`
  unchanged; faith is *proved* preserved (the identity is homogeneous in `μ`). Its conditionals
  are the original prior's conditionals with `state ∈ 𝒞` added to the event
  (`conditionOn_condExp`).
* `SelfTrustAgainst P 𝒞 h π*` — the finite shadow of bli-soto-a-016's self-trust: no one-step
  policy of the re-frozen prior looks better to `P` than `π*` (T8).
* `sepValue_update` and `noStrictPrecommit_iff_updateful_of_separable` — over a prior where the
  ex-ante value is separable (`ReflectivePolicy ∧ LocalUtility ∧ NDPOLICY`, core's
  `exAnteValue_eq_sepValue`), no strict preference for precommitment is the same as pointwise
  updateful optimality on the support, hence the same as prior-optimality (T4(f), tie-aware).

Sources: [[bli-program]] §3.9 U9 (the definition "no strict preference for precommitment at
`T`: `V(π*) ≥ V(π*[T ↦ b])` for every `b`"); [[bli-program-desiderata]] U6; bli-soto-a-024
(Desideratum 2, one-level finite form); bli-soto-a-2-016 (`P_σ`, the re-frozen agent);
bli-soto-a-016 (self-trust). Nothing here uses faith beyond preserving it in `conditionOn`.
-/

namespace Cleanroom.Bli.UdtBliTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A]
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A)

/-! ## No strict preference for precommitment -/

/-- **No strict preference for precommitment at `T`** (definition of record): `π` has positive
ex-ante mass, and for every action `b`, the one-point precommitment `π[T ↦ b]`, when it has
positive mass, has ex-ante value at most `π`'s:
`0 < μ(pp = π) ∧ ∀ b, 0 < μ(pp = π[T ↦ b]) → 𝔼[U | pp = π[T ↦ b]] ≤ 𝔼[U | pp = π]`.
Both sides are actual `exAnteValue`s of positive-mass policies under the one prior `μ`; the
junk `0` of a null policy never enters (core finding F-4). Nothing here says `π` is one-step:
the predicate is about any policy, and the theorems say which policies satisfy it.
Source: [[bli-program]] §3.9 U9 ("`V(π*) ≥ V(π*[T ↦ b])` for every `b`"); bli-soto-a-024
(Desideratum 2: "does not strictly prefer `a`", one level); mandate §3.1
Kind: D
Fidelity: exact (finite, one level; the source's `k` forced actions are `SingleCoin.lean`'s
rounds) -/
def NoStrictPrecommitAt (π : Policy 𝒟 A) (T : ↥𝒟) : Prop :=
  0 < P.policyMass π ∧ ∀ b, 0 < P.policyMass (Function.update π T b) →
    P.exAnteValue (Function.update π T b) ≤ P.exAnteValue π

/-- **No strict preference for precommitment** (at every table).
Source: [[bli-program]] §3.9 U9; [[bli-program-desiderata]] U6; mandate §3.1
Kind: D
Fidelity: exact (one level) -/
def NoStrictPrecommit (π : Policy 𝒟 A) : Prop := ∀ T, NoStrictPrecommitAt P π T

variable {P}

/-- **Policy-level tiling is one line**: a policy that is prior-optimal among positive-mass
policies and has positive mass has no strict preference for precommitment. This is the UDT 1.1
tiling of [[bli-program]] §3.9 U9(1): Kind `T`, never a headline (mandate §3.2).
Source: [[bli-program]] §3.9 U9(1) ("policy-level tiling holds by `argmax`")
Kind: T
Fidelity: exact
Hyps: (a) `0 < policyMass π`, `IsPriorOptimalOnSupport π` -/
theorem noStrictPrecommit_of_priorOptimalOnSupport {π : Policy 𝒟 A} (hπ : 0 < P.policyMass π)
    (h : P.IsPriorOptimalOnSupport π) : NoStrictPrecommit P π :=
  fun _ => ⟨hπ, fun b hb => h _ hb⟩

/-- Under `NDPOLICY`, a prior-optimal policy has no strict preference for precommitment.
Source: [[bli-program]] §3.9 U9(1)
Kind: T
Fidelity: exact
Hyps: (a) `NDPOLICY`, `IsPriorOptimal π` -/
theorem noStrictPrecommit_of_priorOptimal (hpol : P.NDPOLICY) {π : Policy 𝒟 A}
    (h : P.IsPriorOptimal π) : NoStrictPrecommit P π :=
  fun _ => ⟨hpol π, fun b _ => h _⟩

/-- Under `NDPOLICY` the positivity guards are discharged: no strict preference for
precommitment at `T` is the plain comparison `∀ b, exAnteValue π[T ↦ b] ≤ exAnteValue π`.
Source: mandate §3.1
Kind: L
Fidelity: n/a -/
theorem noStrictPrecommitAt_iff_of_ndpolicy (hpol : P.NDPOLICY) (π : Policy 𝒟 A) (T : ↥𝒟) :
    NoStrictPrecommitAt P π T ↔
      ∀ b, P.exAnteValue (Function.update π T b) ≤ P.exAnteValue π :=
  ⟨fun h b => h.2 b (hpol _), fun h => ⟨hpol π, fun b _ => h b⟩⟩

/-- A strictly better positive-mass one-point precommitment refutes no-strict-preference at `T`.
Source: mandate §3.1
Kind: L
Fidelity: n/a -/
theorem not_noStrictPrecommitAt_of_lt {π : Policy 𝒟 A} {T : ↥𝒟} {b : A}
    (hb : 0 < P.policyMass (Function.update π T b))
    (hlt : P.exAnteValue π < P.exAnteValue (Function.update π T b)) :
    ¬ NoStrictPrecommitAt P π T :=
  fun h => absurd (h.2 b hb) (not_le.mpr hlt)

/-! ## The separable form: one-point precommitment under `ReflectivePolicy ∧ LocalUtility` -/

/-- **One-point update of the separable value**: `sepValue π[T ↦ b] = sepValue π +
μ(state = T) · (homeEU T b − homeEU T (π T))`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sepValue_update (π : Policy 𝒟 A) (T : ↥𝒟) (b : A) :
    P.sepValue (Function.update π T b) =
      P.sepValue π + P.stateMass T * (P.homeEU T b - P.homeEU T (π T)) := by
  unfold FiniteBLIPrior.sepValue
  have key : ∑ T', P.stateMass T' * P.homeEU T' (Function.update π T b T') -
      ∑ T', P.stateMass T' * P.homeEU T' (π T') =
      P.stateMass T * (P.homeEU T b - P.homeEU T (π T)) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single T]
    · rw [Function.update_self]; ring
    · intro T' _ hne
      rw [Function.update_of_ne hne]; ring
    · intro habs; exact absurd (Finset.mem_univ _) habs
  linarith

section Separable

variable [Fintype A]

/-- **Over a separable prior, no strict preference for precommitment is pointwise updateful
optimality on the support** — hence (`priorOptimal_iff_updateful_on_support`) the same as
prior-optimality: tiling with respect to a policy holds iff that policy's decisions are
updateful-optimal (= one-step-optimal, under the two-level bridges) at every positive table,
*ties allowed*. This is the tie-aware form of bli-soto-a-2-016's "`P` tiles with respect to
`P_σ` only if `P_σ`'s decisions coincide with `P`'s" (finding: "coincide" is too strong by the
tie case, `MuggingTiles.tie_witness`).
Source: bli-soto-a-2-016 (Soto's conjecture, tie-aware reading — ATTRIBUTION-UNVETTED);
[[bli-program]] §3.9 U9; mandate T4(f)
Kind: C (`exAnteValue_eq_sepValue`, `sepValue_update`, `priorOptimal_iff_updateful_on_support`)
Fidelity: variant: "coincide" rendered as "is an updateful choice at every positive table"
(ties allowed)
Hyps: (a) `NDPOLICY`, `ReflectivePolicy`, `LocalUtility`; does not use faith -/
theorem noStrictPrecommit_iff_updateful_of_separable (hpol : P.NDPOLICY) (hR : P.ReflectivePolicy)
    (hL : P.LocalUtility) (π : Policy 𝒟 A) :
    NoStrictPrecommit P π ↔ ∀ T, 0 < P.stateMass T → P.IsUpdatefulChoice T (π T) := by
  have hsep : ∀ π', P.exAnteValue π' = P.sepValue π' := fun π' =>
    P.exAnteValue_eq_sepValue hR hL π' (hpol π')
  constructor
  · intro h T hT b
    have := (h T).2 b (hpol _)
    rw [hsep, hsep, sepValue_update] at this
    have h2 : P.stateMass T * (P.homeEU T b - P.homeEU T (π T)) ≤ 0 := by linarith
    have h3 := (mul_nonpos_iff_pos_imp_nonpos.mp h2).1 hT
    linarith
  · intro h
    exact noStrictPrecommit_of_priorOptimal hpol
      ((P.priorOptimal_iff_updateful_on_support hpol hR hL π).mpr h)

/-- Over a separable prior, no strict preference for precommitment is prior-optimality.
Source: bli-soto-a-2-016; mandate T4(f)
Kind: C
Fidelity: exact
Hyps: (a) `NDPOLICY`, `ReflectivePolicy`, `LocalUtility`; does not use faith -/
theorem noStrictPrecommit_iff_priorOptimal_of_separable (hpol : P.NDPOLICY)
    (hR : P.ReflectivePolicy) (hL : P.LocalUtility) (π : Policy 𝒟 A) :
    NoStrictPrecommit P π ↔ P.IsPriorOptimal π := by
  rw [noStrictPrecommit_iff_updateful_of_separable hpol hR hL]
  exact (P.priorOptimal_iff_updateful_on_support hpol hR hL π).symm

end Separable

/-! ## The prior re-frozen on a class of states -/

variable (P)

/-- The mass of the class of states `𝒞`: `μ(state ∈ 𝒞)`.
Source: mandate §3.4
Kind: D
Fidelity: exact -/
def stateClassMass (𝒞 : Finset ↥𝒟) : ℚ := massOf P.μ (fun ω => P.state ω ∈ 𝒞)

/-- **The prior re-frozen on the class `𝒞`** (`conditionOn`): the same outcome space, the measure
`μ · [state ∈ 𝒞] / μ(state ∈ 𝒞)`, and `state`, `pp`, `U`, `small` unchanged. This is
bli-soto-a-2-016's `P_σ` read as a prior: the finite shadow of "re-freeze on the day the coin is
decided" is "condition on the class of tables that decide it". Faith is preserved (proved below
in the structure: the faith identity is homogeneous in `μ`, and both sides vanish at `T ∉ 𝒞`).
Source: bli-soto-a-2-016/017 (the re-frozen prior `ext(Q_{t_k})`); mandate §3.4
Kind: D
Fidelity: variant: the re-frozen prior is the conditional of the frozen one on the class of
written-out states that carry the update (finite shadow; disclosed) -/
def conditionOn (𝒞 : Finset ↥𝒟) (h : 0 < stateClassMass P 𝒞) : FiniteBLIPrior 𝒮 m 𝒟 A where
  Ω := P.Ω
  μ := fun ω => if P.state ω ∈ 𝒞 then P.μ ω / stateClassMass P 𝒞 else 0
  μ_nonneg := fun ω => by
    split_ifs
    · exact div_nonneg (P.μ_nonneg ω) h.le
    · exact le_rfl
  μ_sum_one := by
    have e : ∀ ω, (if P.state ω ∈ 𝒞 then P.μ ω / stateClassMass P 𝒞 else 0) =
        (if P.state ω ∈ 𝒞 then P.μ ω else 0) / stateClassMass P 𝒞 := by
      intro ω; split_ifs <;> simp
    simp only [e, ← Finset.sum_div]
    exact div_self (ne_of_gt h)
  state := P.state
  pp := P.pp
  U := P.U
  small := P.small
  faith := by
    intro T φ
    by_cases hT : T ∈ 𝒞
    · have e1 : ∀ ω, (if P.state ω = T then
          (if P.state ω ∈ 𝒞 then P.μ ω / stateClassMass P 𝒞 else 0) * ind (P.small ω φ) else 0) =
          (if P.state ω = T then P.μ ω * ind (P.small ω φ) else 0) / stateClassMass P 𝒞 := by
        intro ω
        by_cases hω : P.state ω = T
        · rw [if_pos hω, if_pos hω, if_pos (hω ▸ hT)]; ring
        · simp [hω]
      have e2 : ∀ ω, (if P.state ω = T then
          (if P.state ω ∈ 𝒞 then P.μ ω / stateClassMass P 𝒞 else 0) else 0) =
          (if P.state ω = T then P.μ ω else 0) / stateClassMass P 𝒞 := by
        intro ω
        by_cases hω : P.state ω = T
        · rw [if_pos hω, if_pos hω, if_pos (hω ▸ hT)]
        · simp [hω]
      simp only [e1, e2, ← Finset.sum_div]
      rw [P.faith T φ]; ring
    · have e1 : ∀ ω, (if P.state ω = T then
          (if P.state ω ∈ 𝒞 then P.μ ω / stateClassMass P 𝒞 else 0) * ind (P.small ω φ) else 0) =
          0 := by
        intro ω
        by_cases hω : P.state ω = T
        · rw [if_pos hω, if_neg (hω ▸ hT)]; ring
        · simp [hω]
      have e2 : ∀ ω, (if P.state ω = T then
          (if P.state ω ∈ 𝒞 then P.μ ω / stateClassMass P 𝒞 else 0) else 0) = 0 := by
        intro ω
        by_cases hω : P.state ω = T
        · rw [if_pos hω, if_neg (hω ▸ hT)]
        · simp [hω]
      simp only [e1, e2, Finset.sum_const_zero, mul_zero]

variable {P}

/-- The mass of an event under the re-frozen prior: `μ(state ∈ 𝒞 ∧ E) / μ(state ∈ 𝒞)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma conditionOn_massOf (𝒞 : Finset ↥𝒟) (h : 0 < stateClassMass P 𝒞) (E : P.Ω → Prop)
    [DecidablePred E] :
    massOf (conditionOn P 𝒞 h).μ E =
      massOf P.μ (fun ω => P.state ω ∈ 𝒞 ∧ E ω) / stateClassMass P 𝒞 := by
  unfold massOf
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  change (if E ω then (if P.state ω ∈ 𝒞 then P.μ ω / stateClassMass P 𝒞 else 0) else 0) = _
  by_cases hE : E ω <;> by_cases hC : P.state ω ∈ 𝒞 <;> simp [hE, hC]

/-- The integral of `f` over an event under the re-frozen prior.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma conditionOn_integralOf (𝒞 : Finset ↥𝒟) (h : 0 < stateClassMass P 𝒞) (f : P.Ω → ℚ)
    (E : P.Ω → Prop) [DecidablePred E] :
    integralOf (conditionOn P 𝒞 h).μ f E =
      integralOf P.μ f (fun ω => P.state ω ∈ 𝒞 ∧ E ω) / stateClassMass P 𝒞 := by
  unfold integralOf
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  change (if E ω then (if P.state ω ∈ 𝒞 then P.μ ω / stateClassMass P 𝒞 else 0) * f ω else 0) = _
  by_cases hE : E ω <;> by_cases hC : P.state ω ∈ 𝒞 <;> simp [hE, hC] <;> ring

/-- **Conditioning on the class and then on `E` is conditioning on both**: every conditional
expectation of the re-frozen prior is the frozen prior's with `state ∈ 𝒞` added to the event.
Source: none: infrastructure (the one lemma behind every value of `conditionOn`)
Kind: L
Fidelity: n/a -/
theorem conditionOn_condExp (𝒞 : Finset ↥𝒟) (h : 0 < stateClassMass P 𝒞) (f : P.Ω → ℚ)
    (E : P.Ω → Prop) [DecidablePred E] :
    condExp (conditionOn P 𝒞 h).μ f E = condExp P.μ f (fun ω => P.state ω ∈ 𝒞 ∧ E ω) := by
  unfold condExp
  rw [conditionOn_massOf, conditionOn_integralOf, div_div_div_cancel_right₀ (ne_of_gt h)]

/-- The ex-ante value of a policy under the re-frozen prior.
Source: mandate T4(d) (`exAnteValue'`)
Kind: L
Fidelity: n/a -/
lemma conditionOn_exAnteValue (𝒞 : Finset ↥𝒟) (h : 0 < stateClassMass P 𝒞) (π : Policy 𝒟 A) :
    (conditionOn P 𝒞 h).exAnteValue π =
      condExp P.μ P.U (fun ω => P.state ω ∈ 𝒞 ∧ P.pp ω = π) :=
  conditionOn_condExp 𝒞 h P.U (fun ω => P.pp ω = π)

/-- The one-step value under the re-frozen prior.
Source: mandate T4(c)
Kind: L
Fidelity: n/a -/
lemma conditionOn_EU (𝒞 : Finset ↥𝒟) (h : 0 < stateClassMass P 𝒞) (T : ↥𝒟) (a : A) :
    (conditionOn P 𝒞 h).EU T a = condExp P.μ P.U (fun ω => P.state ω ∈ 𝒞 ∧ P.pp ω T = a) :=
  conditionOn_condExp 𝒞 h P.U (fun ω => P.pp ω T = a)

/-- The policy mass under the re-frozen prior.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma conditionOn_policyMass (𝒞 : Finset ↥𝒟) (h : 0 < stateClassMass P 𝒞) (π : Policy 𝒟 A) :
    (conditionOn P 𝒞 h).policyMass π =
      massOf P.μ (fun ω => P.state ω ∈ 𝒞 ∧ P.pp ω = π) / stateClassMass P 𝒞 :=
  conditionOn_massOf 𝒞 h (fun ω => P.pp ω = π)

/-! ## Self-trust of the prior against a re-frozen belief state -/

/-- **Self-trust of `P` against the re-frozen prior `P|𝒞`, for the policy `π*`**: no policy that
is one-step for the re-frozen prior and has positive `P`-mass looks better to `P` than `π*` —
the finite shadow of bli-soto-a-016's "the small beliefs do not believe that some other
already-computable belief state, plugged into UDT, yields higher expected utility", with the
other belief state being `P` re-frozen on `𝒞`. `π*` is a parameter (the one-step policy of `P`
in the intended use); the predicate says nothing about `π*` being optimal.
Source: bli-soto-a-016 (Notion 286–288); mandate T8
Kind: D
Fidelity: weaker: the alternative belief states are the re-freezings of `P` on a class, not
every computable `Q̂'` (finite shadow, disclosed) -/
def SelfTrustAgainst (𝒞 : Finset ↥𝒟) (h : 0 < stateClassMass P 𝒞) (πstar : Policy 𝒟 A) : Prop :=
  ∀ π', (conditionOn P 𝒞 h).IsOneStepPolicy π' → 0 < P.policyMass π' →
    P.exAnteValue π' ≤ P.exAnteValue πstar

/-- A prior-optimal `π*` is trusted against every re-freezing (the predicate quantifies over
fewer policies than prior-optimality does): Kind `T`.
Source: mandate T8
Kind: T
Fidelity: n/a
Hyps: (a) `IsPriorOptimalOnSupport π*` -/
theorem selfTrustAgainst_of_priorOptimalOnSupport (𝒞 : Finset ↥𝒟) (h : 0 < stateClassMass P 𝒞)
    {πstar : Policy 𝒟 A} (hs : P.IsPriorOptimalOnSupport πstar) : SelfTrustAgainst 𝒞 h πstar :=
  fun π' _ hπ' => hs π' hπ'

end Cleanroom.Bli.UdtBliTiling
