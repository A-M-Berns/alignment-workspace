import Cleanroom.Bli.UdtBliCore.Bridges
import Cleanroom.Bli.UdtBliCore.Updateful

/-!
# `udt-bli-core` · Desiderata: Soto's desiderata as data and as derived predicates (T10)

The finite one-level rendering of the tree-with-entanglements vocabulary (bli-soto-a-020/021,
bli-soto-b-028/035): an `Entangled` structure over a prior records, for each table `T`, which
other tables' policy points branch `T`'s **utility** may mention (`dep T`) and which may enter
branch `T`'s **probability** (`depP T`), with soundness clauses saying the utility on `state = T`
and the branch probability of `T` are functions of the policy restricted to those points. The
dependency maps are index sets; the soundness clauses are **semantic** (invariance of `U` and of
the cell masses under changes of the points outside the set), so this is a dependency-set
structure with semantic soundness clauses, not a syntactic object.

* `CoordinationFree E := ∀ T, dep T ⊆ {T} ∧ depP T = ∅` — Def 3 at one level, as dependency sets.
* `reflectivePolicy_of_coordinationFree`, `localUtility_of_coordinationFree` (**S**): at one
  level the coordination-free case *is* the policy-level predicates — `mass_sound` with
  `depP T = ∅` is `ReflectivePolicy` in product form, and `U_sound` with `dep T ⊆ {T}` is the
  pointwise home-locality of `U`, which trivially implies `LocalUtility`; the converse is one
  line each (audit r1 adversarial, probe `Squeeze`). They are labelled squeezes, not shipped as
  content. The content of T10 is `d3_finite` — **Desideratum 3 in finite form**: under
  `CoordinationFree`, independent points given the state, and positivity, the one-step and
  updateful maximizer sets coincide (T5 as a corollary) — together with
  `noCrossBranch_of_coordinationFree` (through the real bridge
  `noCrossBranch_of_localUtility_indepGivenState`) and the `NDPOLICY` refinement below. The
  countable-tree conjecture is not attempted.
* The mandate's single-map formulation (`EntangledMandate`, `MandateCoordinationFree`): its
  clause gives `ReflectivePolicy` **under `NDPOLICY`** (`reflectivePolicy_of_mandateCoordinationFree`,
  the sum-to-one argument) and **not without it** (`WitnessLayers.lean`, `CorrTN.mandate_gap`:
  two perfectly correlated policies satisfy the clause vacuously and are not `Reflective`). The
  Transparent-Newcomb-shaped prior is *not* an instance of the clause with `dep = ∅` (its point at
  `T1` moves `T2`'s branch probability too, F-11). Without independence of the points given the
  state, `CoordinationFree` does not give `NoCrossBranch`: the correlated-points prior is
  `CoordinationFree` (`WitnessLayers.lean`, `corrEntangled`, F-11).
* `SensibleWithinBranch`, `SensibleCrossBranch`, `SensibleReweighing` (bli-soto-a-011/012) as
  predicates **relative to a supplied specification** of what the small beliefs say (the finite
  model has no small beliefs about large policy points, F-15); their invariance readings are
  exactly `NoCrossBranch` and `Reflective`.
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

namespace FiniteBLIPrior

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A] [Fintype A]
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A)

/-- **A one-level entanglement structure** over a prior: dependency sets `dep`, `depP` with
semantic soundness clauses (invariance of `U` on `state = T`, and of the cell masses of `T`, under
changes of the points outside the set). Nothing here is syntactic. **Limitation (F-18):** the
utility clause is *pointwise*, so with full agreement of the points it makes `U` a function of
`(state, pp)` (`U_eq_of_entangled`); a prior whose utility carries world randomness beyond the
policy — the tent prior — admits no `Entangled` at all (`Tent.no_entangled`). The
expectation-level `EntangledExp` below is the form the bridges use and the tent prior inhabits.
Source: bli-soto-a-020 (Def 1, entanglements), bli-soto-a-021 (Def 3); bli-soto-b-028; mandate T10
Kind: D
Fidelity: variant: one level, finite, dependency sets with semantic soundness clauses; the
probability dependency is a separate map `depP` (the mandate's single map cannot express "the
branch probability does not depend on the home point" without `NDPOLICY`, F-11); the utility
clause pointwise, which excludes world-random utilities (F-18; `EntangledExp` for those) -/
structure Entangled where
  /-- Which tables' points branch `T`'s utility may mention. -/
  dep : ↥𝒟 → Finset ↥𝒟
  /-- Which tables' points branch `T`'s probability may mention. -/
  depP : ↥𝒟 → Finset ↥𝒟
  /-- On `state = T`, the utility is a function of the policy restricted to `dep T ∪ {T}`. -/
  U_sound : ∀ ω ω', P.state ω = P.state ω' →
    (∀ T' ∈ insert (P.state ω) (dep (P.state ω)), P.pp ω T' = P.pp ω' T') → P.U ω = P.U ω'
  /-- The branch probability of `T` depends on the policy only through `depP T`
  (product form: `μ(T ∧ π) · μ(π') = μ(T ∧ π') · μ(π)` when `π, π'` agree on `depP T`). -/
  mass_sound : ∀ (T : ↥𝒟) (π π' : Policy 𝒟 A), (∀ T' ∈ depP T, π T' = π' T') →
    P.cellMass T π * P.policyMass π' = P.cellMass T π' * P.policyMass π

/-- **Coordination-free**, one level: no branch's utility depends on another branch's point, and
no branch's probability depends on any point. For some `E` this is equivalent to
`ReflectivePolicy ∧ (U is a function of (state, home point))` (audit r1 adversarial, probe
`Squeeze`): at one level the condition *is* the policy-level predicates.
Source: bli-soto-a-021 (Def 3); bli-soto-b-035; mandate T10
Kind: D
Fidelity: variant: dependency sets, one level -/
def CoordinationFree (E : P.Entangled) : Prop := ∀ T, E.dep T ⊆ {T} ∧ E.depP T = ∅

/-- The policy masses sum to one.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_policyMass : ∑ π, P.policyMass π = 1 := by
  have := massOf_fiberwise P.μ (fun _ => True) P.pp
  rw [P.massOf_true] at this
  rw [this]
  apply Finset.sum_congr rfl
  intro π _
  unfold policyMass
  exact massOf_congr _ (fun ω => by simp)

/-- **`CoordinationFree → ReflectivePolicy`**: summing the product-form clause over the second
policy. A squeeze: with `depP T = ∅`, `mass_sound` is verbatim `ReflectivePolicy` in product form
(`∀ π π', cellMass T π · policyMass π' = cellMass T π' · policyMass π`), and the converse is one
line. Kept as the bridge `d3_finite` composes through, not as content.
Source: mandate T10
Kind: S
Fidelity: exact
Hyps: (a) `CoordinationFree`; does not use faith -/
theorem reflectivePolicy_of_coordinationFree (E : P.Entangled) (h : P.CoordinationFree E) :
    P.ReflectivePolicy := by
  intro T π hπ
  have hsound : ∀ π', P.cellMass T π * P.policyMass π' = P.cellMass T π' * P.policyMass π := by
    intro π'
    apply E.mass_sound T π π'
    intro T' hT'
    rw [(h T).2] at hT'
    exact absurd hT' (Finset.notMem_empty T')
  have hsum : P.cellMass T π * ∑ π', P.policyMass π' = (∑ π', P.cellMass T π') * P.policyMass π := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun π' _ => hsound π')
  rw [P.sum_policyMass, mul_one, ← P.stateMass_eq_sum_cellMass] at hsum
  rw [div_eq_iff (ne_of_gt hπ)]
  exact hsum

/-- The conditional expectation of a function constant on a positive event.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma condExp_eq_of_const_on {Ω : Type} [Fintype Ω] (μ f : Ω → ℚ) (E : Ω → Prop)
    [DecidablePred E] (hpos : 0 < massOf μ E) (c : ℚ) (h : ∀ ω, E ω → f ω = c) :
    condExp μ f E = c := by
  unfold condExp
  rw [integralOf_congr_fun μ f (fun _ => c) E h, integralOf_const, mul_div_assoc,
    div_self (ne_of_gt hpos), mul_one]

/-- **`CoordinationFree → LocalUtility`**: on `state = T` the utility depends only on `π T`. A
squeeze: with `dep T ⊆ {T}`, `U_sound` says `U` is a function of `(state, home point)`, which
trivially implies `LocalUtility` (equal pointwise ⟹ equal averages); the converse to the
pointwise form is one line. Kept as the bridge `d3_finite` composes through, not as content.
Source: mandate T10; bli-soto-b-2-016 (T1)
Kind: S
Fidelity: exact
Hyps: (a) `CoordinationFree`; does not use faith -/
theorem localUtility_of_coordinationFree (E : P.Entangled) (h : P.CoordinationFree E) :
    P.LocalUtility := by
  intro T π π' he hπ hπ'
  obtain ⟨ω₀, hω₀, _⟩ := (massOf_pos_iff P.μ P.μ_nonneg _).mp hπ
  have hconst : ∀ (σ : Policy 𝒟 A), σ T = π T → ∀ ω, (P.state ω = T ∧ P.pp ω = σ) →
      P.U ω = P.U ω₀ := by
    intro σ hσ ω hω
    apply E.U_sound ω ω₀ (by rw [hω.1, hω₀.1])
    intro T' hT'
    have hT'T : T' = T := by
      rw [hω.1] at hT'
      rcases Finset.mem_insert.mp hT' with h' | h'
      · exact h'
      · exact Finset.mem_singleton.mp ((h T).1 h')
    rw [hT'T, hω.2, hω₀.2, hσ]
  unfold cellEU
  rw [condExp_eq_of_const_on P.μ P.U _ hπ (P.U ω₀) (hconst π rfl),
    condExp_eq_of_const_on P.μ P.U _ hπ' (P.U ω₀) (hconst π' he.symm)]

/-- **`CoordinationFree → Reflective`** (through `ReflectivePolicy`).
Source: mandate T10
Kind: C
Fidelity: exact
Hyps: (a) `CoordinationFree`; does not use faith -/
theorem reflective_of_coordinationFree (E : P.Entangled) (h : P.CoordinationFree E) :
    P.Reflective :=
  P.reflective_of_reflectivePolicy (P.reflectivePolicy_of_coordinationFree E h)

/-- **`CoordinationFree ∧ IndependentPointsGivenState → NoCrossBranch`** — the independence
clause is needed (the correlated-points prior is `CoordinationFree` and not `NoCrossBranch`).
Source: mandate T10
Kind: C
Fidelity: exact
Hyps: (a) `CoordinationFree`, `IndependentPointsGivenState`; does not use faith -/
theorem noCrossBranch_of_coordinationFree (E : P.Entangled) (h : P.CoordinationFree E)
    (hI : P.IndependentPointsGivenState) : P.NoCrossBranch :=
  P.noCrossBranch_of_localUtility_indepGivenState (P.localUtility_of_coordinationFree E h) hI

/-- **Desideratum 3, finite one-level form**: under `CoordinationFree`, independent points given
the state, and positivity, the one-step and updateful maximizer sets coincide at every
positive-mass table — T5 as a corollary of the dependency-set condition. (The countable-tree
conjecture "replicates LIDT" is not attempted.)
Source: bli-soto-a-025 (Desideratum 3); mandate T10
Kind: C
Fidelity: variant: finite, one level, with `IndependentPointsGivenState` added (disclosed: needed)
Hyps: (a) `CoordinationFree`, `IndependentPointsGivenState`, `NDPOL`, `0 < stateMass T`; does
not use faith -/
theorem d3_finite (E : P.Entangled) (h : P.CoordinationFree E) (hI : P.IndependentPointsGivenState)
    (hpol : P.NDPOL) (T : ↥𝒟) (hT : 0 < P.stateMass T) (a : A) :
    P.IsOneStepChoice T a ↔ P.IsUpdatefulChoice T a :=
  P.oneStep_iff_updateful hpol (P.reflective_of_coordinationFree E h)
    (P.noCrossBranch_of_coordinationFree E h hI) T hT a

/-! ## What `Entangled` forces, and the expectation-level variant (repair round 2; audit r2
adversarial N2; finding F-18)

`Entangled.U_sound` is pointwise: with full agreement of the points it says `U` is a function of
`(state, pp)`. A prior whose utility carries world randomness beyond the policy — the tent prior,
whose bet is judged in the world — therefore admits **no** `Entangled` structure at all
(`WitnessLayers.lean`, `Tent.no_entangled`), and the mandate's checklist item "`CoordinationFree`
inhabited on a prior built from the tent skeleton" cannot be met by `Entangled`. The bridges only
ever use the *expected* utility of a cell, so the natural repair is a variant whose utility
clause is in expectation: `EntangledExp`. `Entangled` implies it (`entangledToExp`), the
bridges and Desideratum 3 go through unchanged (`*_of_coordinationFreeExp`, `d3_finite_exp`),
and every `ReflectivePolicy ∧ LocalUtility` prior carries one with empty maps
(`entangledExpOfPolicyLevel`) — the tent prior in particular (`Tent.tentEntangledExp`). -/

/-- **Any `Entangled` structure makes `U` a function of `(state, pp)`**: `U_sound` with full
agreement of the points. So no `Entangled` exists on a prior whose `U` varies with anything else
(`Tent.no_entangled`, F-18).
Source: none: infrastructure (audit r2 adversarial N2)
Kind: L
Fidelity: n/a -/
lemma U_eq_of_entangled (E : P.Entangled) (ω ω' : P.Ω) (hs : P.state ω = P.state ω')
    (hp : P.pp ω = P.pp ω') : P.U ω = P.U ω' :=
  E.U_sound ω ω' hs (fun T' _ => by rw [hp])

/-- **A one-level entanglement structure in expectation**: the same dependency sets and the same
probability clause as `Entangled`, but the utility clause is about the branch's *expected*
utility given the policy, on positive cells, rather than pointwise — so `U` may carry world
randomness beyond the policy. `Entangled` implies it (`entangledToExp`); with `dep = depP = ∅` it
is exactly `ReflectivePolicy ∧ LocalUtility` (`entangledExpOfPolicyLevel` and the two `S` bridges
below), so at one level the coordination-free case is the policy-level predicates, as before.
Source: bli-soto-a-020 (Def 1, entanglements), bli-soto-a-021 (Def 3); bli-soto-b-028; mandate
T10; audit r2 adversarial N2
Kind: D
Fidelity: variant: one level, finite, dependency sets; the utility dependency stated in
expectation on positive cells (weaker than `Entangled`'s pointwise clause; it is all the bridges
use) -/
structure EntangledExp where
  /-- Which tables' points branch `T`'s expected utility may depend on. -/
  dep : ↥𝒟 → Finset ↥𝒟
  /-- Which tables' points branch `T`'s probability may mention. -/
  depP : ↥𝒟 → Finset ↥𝒟
  /-- On positive cells of `state = T`, the expected utility given the policy depends on the
  policy only through `dep T ∪ {T}`. -/
  cellEU_sound : ∀ (T : ↥𝒟) (π π' : Policy 𝒟 A), (∀ T' ∈ insert T (dep T), π T' = π' T') →
    0 < P.cellMass T π → 0 < P.cellMass T π' → P.cellEU T π = P.cellEU T π'
  /-- The branch probability of `T` depends on the policy only through `depP T` (product form). -/
  mass_sound : ∀ (T : ↥𝒟) (π π' : Policy 𝒟 A), (∀ T' ∈ depP T, π T' = π' T') →
    P.cellMass T π * P.policyMass π' = P.cellMass T π' * P.policyMass π

/-- **Coordination-free, expectation level**: `dep T ⊆ {T}` and `depP T = ∅`.
Source: bli-soto-a-021 (Def 3); mandate T10; audit r2 adversarial N2
Kind: D
Fidelity: variant: dependency sets, one level, in expectation -/
def CoordinationFreeExp (E : P.EntangledExp) : Prop := ∀ T, E.dep T ⊆ {T} ∧ E.depP T = ∅

/-- **Pointwise soundness implies soundness in expectation**: `U` is constant on each cell and
equal across cells whose policies agree on `dep T ∪ {T}`, so the cell expectations agree.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
def entangledToExp (E : P.Entangled) : P.EntangledExp where
  dep := E.dep
  depP := E.depP
  cellEU_sound := by
    intro T π π' hagree hπ hπ'
    obtain ⟨ω₀, hω₀, _⟩ := (massOf_pos_iff P.μ P.μ_nonneg _).mp hπ
    have hconst : ∀ (σ : Policy 𝒟 A), (∀ T' ∈ insert T (E.dep T), σ T' = π T') →
        ∀ ω, (P.state ω = T ∧ P.pp ω = σ) → P.U ω = P.U ω₀ := by
      intro σ hσ ω hω
      apply E.U_sound ω ω₀ (by rw [hω.1, hω₀.1])
      intro T' hT'
      rw [hω.1] at hT'
      rw [hω.2, hω₀.2]
      exact hσ T' hT'
    unfold cellEU
    rw [condExp_eq_of_const_on P.μ P.U _ hπ (P.U ω₀) (hconst π (fun _ _ => rfl)),
      condExp_eq_of_const_on P.μ P.U _ hπ' (P.U ω₀)
        (hconst π' (fun T' hT' => (hagree T' hT').symm))]
  mass_sound := E.mass_sound

/-- `ReflectivePolicy` from the product form of the probability clause with no dependency.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma reflectivePolicy_of_productForm
    (h : ∀ (T : ↥𝒟) (π π' : Policy 𝒟 A),
      P.cellMass T π * P.policyMass π' = P.cellMass T π' * P.policyMass π) :
    P.ReflectivePolicy := by
  intro T π hπ
  have hsum : P.cellMass T π * ∑ π', P.policyMass π' =
      (∑ π', P.cellMass T π') * P.policyMass π := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun π' _ => h T π π')
  rw [P.sum_policyMass, mul_one, ← P.stateMass_eq_sum_cellMass] at hsum
  rw [div_eq_iff (ne_of_gt hπ)]
  exact hsum

/-- **`CoordinationFreeExp → ReflectivePolicy`**. A squeeze, as at the pointwise level: with
`depP T = ∅` the probability clause is `ReflectivePolicy` in product form.
Source: mandate T10; audit r2 adversarial N2
Kind: S
Fidelity: exact
Hyps: (a) `CoordinationFreeExp`; does not use faith -/
theorem reflectivePolicy_of_coordinationFreeExp (E : P.EntangledExp)
    (h : P.CoordinationFreeExp E) : P.ReflectivePolicy :=
  P.reflectivePolicy_of_productForm (fun T π π' => E.mass_sound T π π' (fun T' hT' => by
    rw [(h T).2] at hT'
    exact absurd hT' (Finset.notMem_empty T')))

/-- **`CoordinationFreeExp → LocalUtility`**. A squeeze: with `dep T ⊆ {T}` the utility clause
*is* `LocalUtility`.
Source: mandate T10; bli-soto-b-2-016 (T1); audit r2 adversarial N2
Kind: S
Fidelity: exact
Hyps: (a) `CoordinationFreeExp`; does not use faith -/
theorem localUtility_of_coordinationFreeExp (E : P.EntangledExp) (h : P.CoordinationFreeExp E) :
    P.LocalUtility := by
  intro T π π' he hπ hπ'
  apply E.cellEU_sound T π π' _ hπ hπ'
  intro T' hT'
  rcases Finset.mem_insert.mp hT' with rfl | h'
  · exact he
  · rw [Finset.mem_singleton.mp ((h T).1 h')]; exact he

/-- **`CoordinationFreeExp ∧ IndependentPointsGivenState → NoCrossBranch`** (through the real
bridge; the independence clause is needed, `coordinationFree_not_noCrossBranch`).
Source: mandate T10
Kind: C
Fidelity: exact
Hyps: (a) `CoordinationFreeExp`, `IndependentPointsGivenState`; does not use faith -/
theorem noCrossBranch_of_coordinationFreeExp (E : P.EntangledExp) (h : P.CoordinationFreeExp E)
    (hI : P.IndependentPointsGivenState) : P.NoCrossBranch :=
  P.noCrossBranch_of_localUtility_indepGivenState (P.localUtility_of_coordinationFreeExp E h) hI

/-- **Desideratum 3, finite one-level form, at the expectation level**: under
`CoordinationFreeExp`, independent points given the state, and positivity, the one-step and
updateful maximizer sets coincide at every positive-mass table. Inhabited non-degenerately by the
tent prior (`Tent.tentEntangledExp`, `Tent.d3_on_tent`), where the maximizer varies.
Source: bli-soto-a-025 (Desideratum 3); mandate T10; audit r2 adversarial N2
Kind: C
Fidelity: variant: finite, one level, in expectation, with `IndependentPointsGivenState` added
Hyps: (a) `CoordinationFreeExp`, `IndependentPointsGivenState`, `NDPOL`, `0 < stateMass T`;
does not use faith -/
theorem d3_finite_exp (E : P.EntangledExp) (h : P.CoordinationFreeExp E)
    (hI : P.IndependentPointsGivenState) (hpol : P.NDPOL) (T : ↥𝒟) (hT : 0 < P.stateMass T)
    (a : A) : P.IsOneStepChoice T a ↔ P.IsUpdatefulChoice T a :=
  P.oneStep_iff_updateful hpol
    (P.reflective_of_reflectivePolicy (P.reflectivePolicy_of_coordinationFreeExp E h))
    (P.noCrossBranch_of_coordinationFreeExp E h hI) T hT a

/-- **The converse: every `ReflectivePolicy ∧ LocalUtility` prior carries an `EntangledExp`
with empty maps** (the probability clause from `ReflectivePolicy`, null policies contributing `0`
to both sides; the utility clause is `LocalUtility`). With `coordinationFreeExp_ofPolicyLevel`
this closes the squeeze at the expectation level: coordination-free in expectation ⟺
`ReflectivePolicy ∧ LocalUtility`.
Source: none: infrastructure (audit r2 adversarial N2; audit r1 adversarial probe `Squeeze`)
Kind: L
Fidelity: n/a -/
def entangledExpOfPolicyLevel (hR : P.ReflectivePolicy) (hL : P.LocalUtility) :
    P.EntangledExp where
  dep := fun _ => ∅
  depP := fun _ => ∅
  cellEU_sound := fun T π π' hagree hπ hπ' =>
    hL T π π' (hagree T (Finset.mem_insert_self T ∅)) hπ hπ'
  mass_sound := by
    intro T π π' _
    by_cases hπ : 0 < P.policyMass π
    · by_cases hπ' : 0 < P.policyMass π'
      · have h1 := hR T π hπ
        have h2 := hR T π' hπ'
        rw [div_eq_iff (ne_of_gt hπ)] at h1
        rw [div_eq_iff (ne_of_gt hπ')] at h2
        rw [h1, h2]; ring
      · have hz : P.policyMass π' = 0 :=
          le_antisymm (not_lt.mp hπ') (P.policyMass_nonneg π')
        have hz' : P.cellMass T π' = 0 :=
          le_antisymm (hz ▸ P.cellMass_le_policyMass T π') (P.cellMass_nonneg T π')
        rw [hz, hz', mul_zero, zero_mul]
    · have hz : P.policyMass π = 0 := le_antisymm (not_lt.mp hπ) (P.policyMass_nonneg π)
      have hz' : P.cellMass T π = 0 :=
        le_antisymm (hz ▸ P.cellMass_le_policyMass T π) (P.cellMass_nonneg T π)
      rw [hz, hz', mul_zero, zero_mul]

/-- The empty-map structure of a policy-level prior is coordination-free in expectation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem coordinationFreeExp_ofPolicyLevel (hR : P.ReflectivePolicy) (hL : P.LocalUtility) :
    P.CoordinationFreeExp (P.entangledExpOfPolicyLevel hR hL) :=
  fun _ => ⟨Finset.empty_subset _, rfl⟩

/-! ## The mandate's single-map formulation (recorded; its claim proved under `NDPOLICY`, refuted
without it in `WitnessLayers.lean`) -/

/-- **The mandate's formulation**: one dependency map, with both clauses over `dep T ∪ {T}`.
Kept to state precisely what its coordination-free clause `dep T ⊆ {T}` gives: `ReflectivePolicy`
**under `NDPOLICY`** (`reflectivePolicy_of_mandateCoordinationFree`: each branch's probability
depends only on its own point, and the branch probabilities sum to one, so each is constant) and
**not without it** (`CorrTN.mandate_gap`: two perfectly correlated policies satisfy the clause
vacuously and are not `Reflective`). The Transparent-Newcomb-shaped prior is *not* an instance of
the clause with `dep = ∅` — its point at `T1` moves `T2`'s branch probability too, so the clause
forces `dep T2 ∋ T1` (F-11, corrected).
Source: mandate T10 (its soundness clause, verbatim); finding F-11
Kind: D
Fidelity: exact (the mandate's clause) -/
structure EntangledMandate where
  /-- The single dependency map. -/
  dep : ↥𝒟 → Finset ↥𝒟
  /-- On `state = T`, the utility is a function of the policy restricted to `dep T ∪ {T}`. -/
  U_sound : ∀ ω ω', P.state ω = P.state ω' →
    (∀ T' ∈ insert (P.state ω) (dep (P.state ω)), P.pp ω T' = P.pp ω' T') → P.U ω = P.U ω'
  /-- The branch probability of `T` depends on the policy only through `dep T ∪ {T}`. -/
  mass_sound : ∀ (T : ↥𝒟) (π π' : Policy 𝒟 A), (∀ T' ∈ insert T (dep T), π T' = π' T') →
    P.cellMass T π * P.policyMass π' = P.cellMass T π' * P.policyMass π

/-- The mandate's coordination-free condition: `dep T ⊆ {T}`.
Source: mandate T10; finding F-11
Kind: D
Fidelity: exact (the mandate's clause) -/
def MandateCoordinationFree (E : P.EntangledMandate) : Prop := ∀ T, E.dep T ⊆ {T}

/-- **The mandate's `CoordinationFree → ReflectivePolicy` holds under `NDPOLICY`**: if every branch's
probability depends on the policy only through the branch's own point, then, because the branch
probabilities sum to one for every policy, varying one point alone shows each of them is
constant. Without `NDPOLICY` it fails (`WitnessLayers.lean`, `CorrTN.mandate_gap`).
Source: mandate T10; finding F-11
Kind: C
Fidelity: exact (the mandate's clause plus `NDPOLICY`)
Hyps: (a) `MandateCoordinationFree`, `NDPOLICY`; does not use faith -/
theorem reflectivePolicy_of_mandateCoordinationFree (E : P.EntangledMandate)
    (h : P.MandateCoordinationFree E) (hpol : P.NDPOLICY) : P.ReflectivePolicy := by
  have hg : ∀ (T : ↥𝒟) (π π' : Policy 𝒟 A), π T = π' T →
      P.cellMass T π / P.policyMass π = P.cellMass T π' / P.policyMass π' := by
    intro T π π' he
    have hms := E.mass_sound T π π' (fun T' hT' => by
      rcases Finset.mem_insert.mp hT' with rfl | h'
      · exact he
      · rw [Finset.mem_singleton.mp (h T h')]; exact he)
    rw [div_eq_div_iff (ne_of_gt (hpol π)) (ne_of_gt (hpol π'))]
    exact hms
  have hsum : ∀ π : Policy 𝒟 A, ∑ T, P.cellMass T π / P.policyMass π = 1 := by
    intro π
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← P.policyMass_eq_sum_cellMass, mul_inv_cancel₀ (ne_of_gt (hpol π))]
  have hconst : ∀ (T : ↥𝒟) (π : Policy 𝒟 A) (b : A),
      P.cellMass T π / P.policyMass π =
        P.cellMass T (Function.update π T b) / P.policyMass (Function.update π T b) := by
    intro T π b
    have h1 := hsum π
    have h2 := hsum (Function.update π T b)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ T)] at h1 h2
    have hrest : ∑ T' ∈ univ.erase T, P.cellMass T' π / P.policyMass π =
        ∑ T' ∈ univ.erase T, P.cellMass T' (Function.update π T b) /
          P.policyMass (Function.update π T b) := by
      apply Finset.sum_congr rfl
      intro T' hT'
      exact hg T' π _ (by rw [Function.update_of_ne (Finset.ne_of_mem_erase hT')])
    linarith [h1, h2, hrest]
  have hall : ∀ (T : ↥𝒟) (π π' : Policy 𝒟 A),
      P.cellMass T π / P.policyMass π = P.cellMass T π' / P.policyMass π' := by
    intro T π π'
    rw [hconst T π (π' T)]
    exact hg T _ π' (Function.update_self T (π' T) π)
  intro T π _
  symm
  rw [P.stateMass_eq_sum_cellMass T]
  have hc : ∀ π', P.cellMass T π' = (P.cellMass T π / P.policyMass π) * P.policyMass π' := by
    intro π'
    rw [hall T π π', div_mul_cancel₀ _ (ne_of_gt (hpol π'))]
  rw [Finset.sum_congr rfl (fun π' _ => hc π'), ← Finset.mul_sum, P.sum_policyMass, mul_one]

/-! ## The "sensible" desiderata as predicates relative to a specification -/

/-- **Sensible within-branch consequences**: faith inside every positive home cell
`state = T ∧ pp · T = a` (`FaithGivenPoints` restricted to the home cell).
Source: bli-soto-a-011 (Notion 226–235: "the consequences of an action within its own branch
should just be the updateful picture")
Kind: D
Fidelity: variant: the finite rendering (faith on the home cell) -/
def SensibleWithinBranch : Prop :=
  ∀ (T : ↥𝒟) (a : A) (φ : ↥(𝒮.S m)), 0 < P.jointMass T T a →
    integralOf P.μ (fun ω => ind (P.small ω φ)) (fun ω => P.state ω = T ∧ P.pp ω T = a) =
      T.1 φ * P.jointMass T T a

/-- `FaithGivenPoints` implies `SensibleWithinBranch`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sensibleWithinBranch_of_faithGivenPoints (h : P.FaithGivenPoints) :
    P.SensibleWithinBranch := fun T a φ hpos => h T T a φ hpos

/-- **Sensible cross-branch consequences, relative to a specification** `cross T' T a` of what
branch `T'`'s small beliefs say `U` is given the point `A(T) = a`: the large conditional agrees
with it on positive cells.
Source: bli-soto-a-012 (i) (Notion 236–247); the specification is external because the finite
model carries no small beliefs about large policy points (Notion 244–247: "What would a small
belief *about* the correlations of the large branches even look like?")
Kind: D
Fidelity: variant: relative to a supplied specification (disclosed) -/
def SensibleCrossBranch (cross : ↥𝒟 → ↥𝒟 → A → ℚ) : Prop :=
  ∀ (T' T : ↥𝒟) (a : A), T' ≠ T → 0 < P.jointMass T' T a → P.condEU T' T a = cross T' T a

/-- **Sensible branch re-weighting, relative to a specification** `w T' T a` of what the small
beliefs say `μ(state = T' | pp · T = a)` is.
Source: bli-soto-a-012 (ii) (Notion 248–253, Transparent Newcomb)
Kind: D
Fidelity: variant: relative to a supplied specification (disclosed) -/
def SensibleReweighing (w : ↥𝒟 → ↥𝒟 → A → ℚ) : Prop :=
  ∀ (T' T : ↥𝒟) (a : A), 0 < P.ppMass T a → P.branchProb T' T a = w T' T a

/-- **The invariance reading of cross-branch sensibility is `NoCrossBranch`**: if the specification
says the point does not matter (`cross T' T a = cross T' T b`), sensibility is exactly the
absence of cross-branch utility influence on positive cells.
Source: bli-soto-a-012 (i), invariance reading; bli-slides-037
Kind: L
Fidelity: exact -/
lemma noCrossBranch_of_sensibleCrossBranch (cross : ↥𝒟 → ↥𝒟 → A → ℚ)
    (hinv : ∀ T' T a b, cross T' T a = cross T' T b) (h : P.SensibleCrossBranch cross) :
    P.NoCrossBranch := by
  intro T T' a b hne hpa hpb
  rw [h T' T a hne hpa, h T' T b hne hpb, hinv]

/-- **The invariance reading of re-weighting sensibility is `Reflective`**: if the specification
is the unconditional branch probability, sensibility is exactly `Reflective`.
Source: bli-soto-a-012 (ii), invariance reading; bli-slides-037
Kind: L
Fidelity: exact -/
lemma reflective_iff_sensibleReweighing :
    P.Reflective ↔ P.SensibleReweighing (fun T' _ _ => P.stateMass T') := by
  unfold Reflective SensibleReweighing
  constructor
  · intro h T' T a hpos; exact h T' T a hpos
  · intro h T T' a hpos; exact h T T' a hpos

end FiniteBLIPrior

end Cleanroom.Bli.UdtBliCore
