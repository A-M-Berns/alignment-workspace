import Cleanroom.Fixpoint.FixOraclesCorresp.NashReflective
import SafeParetoImprovements.Coordination

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.CorrelatedEq`: correlated equilibria as a definition, and the bridge

Target 8 (fixpoint-lit-011 (iii)). Over a finite game with action sets `𝒜 i` (every action available,
i.e. FAF's `SafeParetoImprovements.Game` with `S i = univ`), a **correlated equilibrium** is a
probability weight `w` on pure profiles such that no player gains by deviating from any recommended
action: `∀ i (a a' : 𝒜 i), 0 ≤ ∑ b, [b i = a] * w b * (u b i − u (update b i a') i)`.

Proved: the CE set is convex (`convex_ceSet`); the product weight of a mixed Nash equilibrium is a CE
(`isCorrelatedEquilibrium_prodWeight`, via the general linearity `expectedPayoff_eq_sum_deviate'` and
the support lemma `expectedPayoff_deviate_eq_of_pos`); the CE set of a two-action game is nonempty
(`ceSet_nonempty_twoAction`, from `exists_isMixedNashEq`, grade (a)); the bridge to FAF's
`Game.Correlated` (`Correlated.weight_mem_stdSimplex`, `Correlated.ofWeight`).

The notes' "fixed points of the game oracle are correlated equilibria" has no oracle definition and is
recorded as ill-posed (finding F5); nothing here claims it.
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set StrategicGame Finset

section General

variable {N : Type*} [Fintype N] [DecidableEq N] {𝒜 : N → Type*} [∀ i, Fintype (𝒜 i)]
  [∀ i, DecidableEq (𝒜 i)]

/-- **Correlated equilibrium** of the payoff `u` on pure profiles `∀ i, 𝒜 i`: for every player `i`,
recommended action `a` and deviation `a'`, the recommendation is (weakly) obeyed in expectation.
Source: [[fixpoint-lit-inventory]] 011 (iii) (the CE inequalities
`∑_{a₋ᵢ} ν(aᵢ, a₋ᵢ)(uᵢ(aᵢ, a₋ᵢ) − uᵢ(aᵢ', a₋ᵢ)) ≥ 0`); Aumann 1974
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsCorrelatedEquilibrium (u : (∀ i, 𝒜 i) → N → ℝ) (w : (∀ i, 𝒜 i) → ℝ) : Prop :=
  ∀ (i : N) (a a' : 𝒜 i),
    0 ≤ ∑ b, if b i = a then w b * (u b i - u (Function.update b i a') i) else 0

/-- **The CE set**: probability weights on profiles that are correlated equilibria.
Source: [[fixpoint-lit-inventory]] 011 (iii) ("the correlated-equilibrium set … is a nonempty convex
polytope")
Kind: D
Fidelity: exact
Hyps: n/a -/
def ceSet (u : (∀ i, 𝒜 i) → N → ℝ) : Set ((∀ i, 𝒜 i) → ℝ) :=
  {w | w ∈ stdSimplex ℝ (∀ i, 𝒜 i) ∧ IsCorrelatedEquilibrium u w}

/-- **The CE set is convex** (each CE inequality is linear in `w`).
Source: [[fixpoint-lit-inventory]] 011 (iii)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem convex_ceSet (u : (∀ i, 𝒜 i) → N → ℝ) : Convex ℝ (ceSet u) := by
  intro w₁ ⟨h₁, hce₁⟩ w₂ ⟨h₂, hce₂⟩ α β hα hβ hαβ
  refine ⟨convex_stdSimplex ℝ _ h₁ h₂ hα hβ hαβ, fun i a a' => ?_⟩
  have hsplit : ∀ b, (if b i = a then (α • w₁ + β • w₂) b * (u b i - u (Function.update b i a') i)
      else 0) = α * (if b i = a then w₁ b * (u b i - u (Function.update b i a') i) else 0) +
        β * (if b i = a then w₂ b * (u b i - u (Function.update b i a') i) else 0) := by
    intro b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  exact add_nonneg (mul_nonneg hα (hce₁ i a a')) (mul_nonneg hβ (hce₂ i a a'))

/-! ### The general linearity and support lemmas for `IsMixedNashEq` -/

/-- The direct strategic game with strategy types `𝒜` and payoff `u`.
Source: none: infrastructure (cf. `twoActionGame`)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev directGame (u : (∀ i, 𝒜 i) → N → ℝ) : StrategicGame N ℝ where
  strategy := 𝒜
  payoff := u

omit [Fintype N] in
/-- The weight vectors of a deviation are the `update` of the weight vectors (general strategy types).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem val_deviateMixed' (u : (∀ i, 𝒜 i) → N → ℝ) (σ : MixedProfile (directGame u)) (i : N)
    (s : 𝒜 i) :
    (fun j => (deviateMixed (directGame u) σ i s j).val) =
      Function.update (fun j => (σ j).val) i (fun t => if t = s then 1 else 0) := by
  funext j
  by_cases h : j = i
  · subst h
    simp only [deviateMixed, Function.update_self]
    rfl
  · simp [deviateMixed, Function.update_of_ne h]

/-- Raw expected payoff on weight vectors (general strategy types).
Source: none: infrastructure (cf. `rawEP`)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def rawEP' (u : (∀ i, 𝒜 i) → N → ℝ) (ρ : ∀ i, 𝒜 i → ℝ) (j : N) : ℝ :=
  ∑ τ : ∀ i, 𝒜 i, (∏ i, ρ i (τ i)) * u τ j

/-- **Linearity of the expected payoff in one player's strategy** (general strategy types).
Source: FTC 2015 Theorem 4.1 (proof); MSZ 5.5
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem expectedPayoff_eq_sum_deviate' (u : (∀ i, 𝒜 i) → N → ℝ) (σ : MixedProfile (directGame u))
    (i : N) :
    expectedPayoff (directGame u) σ i =
      ∑ s, (σ i).val s * expectedPayoff (directGame u) (deviateMixed (directGame u) σ i s) i := by
  have hdev : ∀ s, expectedPayoff (directGame u) (deviateMixed (directGame u) σ i s) i =
      ∑ τ, ((if τ i = s then (1 : ℝ) else 0) * ∏ j ∈ univ.erase i, (σ j).val (τ j)) * u τ i := by
    intro s
    change rawEP' u (fun j => (deviateMixed (directGame u) σ i s j).val) i = _
    rw [val_deviateMixed']
    unfold rawEP'
    refine Finset.sum_congr rfl fun τ _ => ?_
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hσ : expectedPayoff (directGame u) σ i =
      ∑ τ, ((σ i).val (τ i) * ∏ j ∈ univ.erase i, (σ j).val (τ j)) * u τ i := by
    change rawEP' u (fun j => (σ j).val) i = _
    unfold rawEP'
    refine Finset.sum_congr rfl fun τ _ => ?_
    congr 1
    exact (Finset.mul_prod_erase Finset.univ (fun j => (σ j).val (τ j)) (Finset.mem_univ i)).symm
  simp only [hdev, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_eq_single (τ i)]
  · rw [if_pos rfl]; ring
  · intro s _ hs
    rw [if_neg (Ne.symm hs)]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Support lemma**: at a mixed Nash equilibrium, every action played with positive probability
achieves the equilibrium payoff.
Source: FTC 2015 Theorem 4.1 (proof: "a pure strategy `aᵢ` can only be assigned positive probability
if it maximizes …")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem expectedPayoff_deviate_eq_of_pos (u : (∀ i, 𝒜 i) → N → ℝ) {σ : MixedProfile (directGame u)}
    (h : IsMixedNashEq (directGame u) σ) (i : N) {a : 𝒜 i} (ha : 0 < (σ i).val a) :
    expectedPayoff (directGame u) (deviateMixed (directGame u) σ i a) i =
      expectedPayoff (directGame u) σ i := by
  have hlin := expectedPayoff_eq_sum_deviate' u σ i
  have hnn := (σ i).2.1
  have hsum := (σ i).2.2
  have hle : ∀ s, expectedPayoff (directGame u) (deviateMixed (directGame u) σ i s) i ≤
      expectedPayoff (directGame u) σ i := fun s => h i s
  -- `∑ s, σ s * (EP σ - EP s) = 0` with nonnegative terms
  have hz : ∑ s, (σ i).val s * (expectedPayoff (directGame u) σ i -
      expectedPayoff (directGame u) (deviateMixed (directGame u) σ i s) i) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
    rw [hlin, sub_self]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun s _ => mul_nonneg (hnn s) (by linarith [hle s]))] at hz
  have := hz a (Finset.mem_univ _)
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 ha.ne'
  · linarith

/-! ### The product of a mixed Nash equilibrium is a correlated equilibrium -/

/-- The product weight of a mixed profile: `w b = ∏ i, (σ i).val (b i)`.
Source: [[fixpoint-lit-inventory]] 011 (iii) ("CE is the convex relaxation" of Nash)
Kind: D
Fidelity: exact
Hyps: n/a -/
def prodWeight (u : (∀ i, 𝒜 i) → N → ℝ) (σ : MixedProfile (directGame u)) (b : ∀ i, 𝒜 i) : ℝ :=
  ∏ i, (σ i).val (b i)

omit [∀ i, DecidableEq (𝒜 i)] in
/-- The product weight is a probability weight on profiles.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prodWeight_mem_stdSimplex (u : (∀ i, 𝒜 i) → N → ℝ) (σ : MixedProfile (directGame u)) :
    prodWeight u σ ∈ stdSimplex ℝ (∀ i, 𝒜 i) := by
  refine ⟨fun b => Finset.prod_nonneg fun i _ => (σ i).2.1 _, ?_⟩
  unfold prodWeight
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun i _ => (σ i).2.2

/-- Reindexing a sum over profiles with `b i = a'` as a sum over profiles with `b i = a` (the bijection
`update · i a'`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_update_reindex (F : (∀ i, 𝒜 i) → ℝ) (i : N) (a a' : 𝒜 i) :
    ∑ b, (if b i = a' then F b else 0) = ∑ b, (if b i = a then F (Function.update b i a') else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun b => Function.update b i a) (fun b => Function.update b i a') ?_ ?_ ?_
    ?_ ?_
  · intro b hb; simp
  · intro b hb; simp
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    rw [Function.update_idem, ← hb, Function.update_eq_self]
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    rw [Function.update_idem, ← hb, Function.update_eq_self]
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    rw [Function.update_idem, ← hb, Function.update_eq_self]

/-- **The product weight of a mixed Nash equilibrium is a correlated equilibrium.** For each `i`, `a`,
`a'`, the CE sum is `(σ i).val a * (EP(dev i a) − EP(dev i a'))`; if `(σ i).val a = 0` it vanishes, and
otherwise `EP(dev i a) = EP σ ≥ EP(dev i a')` by the support lemma and Nash.
Source: [[fixpoint-lit-inventory]] 011 (iii); Aumann 1974 (Nash ⊆ CE)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem isCorrelatedEquilibrium_prodWeight (u : (∀ i, 𝒜 i) → N → ℝ)
    {σ : MixedProfile (directGame u)} (h : IsMixedNashEq (directGame u) σ) :
    IsCorrelatedEquilibrium u (prodWeight u σ) := by
  intro i a a'
  -- the two deviation payoffs as sums over profiles with `b i = a`
  have hdev : ∀ s : 𝒜 i, expectedPayoff (directGame u) (deviateMixed (directGame u) σ i s) i =
      ∑ b, (if b i = s then (∏ j ∈ univ.erase i, (σ j).val (b j)) * u b i else 0) := by
    intro s
    change ∑ τ : ∀ i, 𝒜 i, (∏ j, (deviateMixed (directGame u) σ i s j).val (τ j)) *
      u τ i = _
    refine Finset.sum_congr rfl fun τ _ => ?_
    have : (fun j => (deviateMixed (directGame u) σ i s j).val) =
        Function.update (fun j => (σ j).val) i (fun t => if t = s then 1 else 0) :=
      val_deviateMixed' u σ i s
    have hprod : ∏ j, (deviateMixed (directGame u) σ i s j).val (τ j) =
        (if τ i = s then (1 : ℝ) else 0) * ∏ j ∈ univ.erase i, (σ j).val (τ j) := by
      rw [show (fun j => (deviateMixed (directGame u) σ i s j).val (τ j)) =
          fun j => Function.update (fun j => (σ j).val) i (fun t => if t = s then 1 else 0) j (τ j)
          from by rw [← this]]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun j hj => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hprod]
    split_ifs <;> ring
  have hoff : ∀ b : ∀ i, 𝒜 i, ∏ j ∈ univ.erase i, (σ j).val (Function.update b i a' j) =
      ∏ j ∈ univ.erase i, (σ j).val (b j) :=
    fun b => Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  -- the CE sum equals `σ i a * (EP(dev a) − EP(dev a'))`
  have key : (∑ b, if b i = a then prodWeight u σ b * (u b i - u (Function.update b i a') i) else 0) =
      (σ i).val a * (expectedPayoff (directGame u) (deviateMixed (directGame u) σ i a) i -
        expectedPayoff (directGame u) (deviateMixed (directGame u) σ i a') i) := by
    rw [hdev, hdev, sum_update_reindex (fun b => (∏ j ∈ univ.erase i, (σ j).val (b j)) * u b i) i a a',
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold prodWeight
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), hoff]
    split_ifs with hb
    · rw [hb]; ring
    · ring
  rw [key]
  rcases lt_or_eq_of_le ((σ i).2.1 a) with hpos | hzero
  · rw [expectedPayoff_deviate_eq_of_pos u h i hpos]
    exact mul_nonneg hpos.le (by linarith [h i a'])
  · rw [← hzero, zero_mul]

end General

/-! ### Two-action games: nonempty CE set, and the FAF bridge -/

section TwoAction

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- **The CE set of a finite two-action game is nonempty** (from two-action Nash existence, grade
(a), and Nash ⊆ CE).
Source: [[fixpoint-lit-inventory]] 011 (iii) ("nonempty convex polytope"); mandate target 8
Kind: C
Fidelity: variant: two actions per player (general finite games: not done, see the report)
Hyps: (a) all -/
theorem ceSet_nonempty_twoAction (u : (N → Fin 2) → N → ℝ) :
    (ceSet (𝒜 := fun _ => Fin 2) u).Nonempty := by
  obtain ⟨σ, hσ⟩ := exists_isMixedNashEq u
  exact ⟨prodWeight (𝒜 := fun _ => Fin 2) u σ, prodWeight_mem_stdSimplex u σ,
    isCorrelatedEquilibrium_prodWeight u hσ⟩

end TwoAction

section FAFBridge

variable {N : Type*} [Fintype N] [DecidableEq N] {𝒜 : N → Type*} [∀ i, Fintype (𝒜 i)]
  [∀ i, DecidableEq (𝒜 i)]

omit [∀ i, DecidableEq (𝒜 i)] in
/-- **Bridge to FAF's `Game.Correlated`**: when every action set is `univ`, the weight of a FAF
correlated strategy is a probability weight on all profiles.
Source: FAF `SafeParetoImprovements/Coordination.lean:70` (`Game.Correlated`); mandate target 8
Kind: L
Fidelity: n/a
Hyps: none -/
theorem correlated_weight_mem_stdSimplex (Γ : SafeParetoImprovements.Game N 𝒜)
    (hS : ∀ i, Γ.S i = Finset.univ) (p : Γ.Correlated) : p.weight ∈ stdSimplex ℝ (∀ i, 𝒜 i) := by
  refine ⟨p.nonneg, ?_⟩
  have := p.sum_eq_one
  have huniv : Γ.profilesFinset = Finset.univ := by
    ext a; simp [SafeParetoImprovements.Game.mem_profilesFinset, hS]
  rwa [huniv] at this

/-- **Bridge to FAF's `Game.Correlated`**, the other way: a probability weight on all profiles is a
FAF correlated strategy of a game with every action set `univ`.
Source: FAF `SafeParetoImprovements/Coordination.lean:70`; mandate target 8
Kind: D
Fidelity: n/a
Hyps: n/a -/
def correlatedOfWeight (Γ : SafeParetoImprovements.Game N 𝒜) (hS : ∀ i, Γ.S i = Finset.univ)
    (w : (∀ i, 𝒜 i) → ℝ) (hw : w ∈ stdSimplex ℝ (∀ i, 𝒜 i)) : Γ.Correlated where
  weight := w
  nonneg := hw.1
  support := fun a ha => absurd (fun i => by rw [hS]; exact Finset.mem_univ _) ha
  sum_eq_one := by
    have huniv : Γ.profilesFinset = Finset.univ := by
      ext a; simp [SafeParetoImprovements.Game.mem_profilesFinset, hS]
    rw [huniv]; exact hw.2

/-- **Correlated equilibrium of a FAF game** (with every action set `univ`): its weight satisfies the
CE inequalities for `Γ.u`.
Source: mandate target 8 ("over FAF's `SafeParetoImprovements.Game` … and `Game.Correlated`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsCorrelatedEq (Γ : SafeParetoImprovements.Game N 𝒜) (p : Γ.Correlated) : Prop :=
  IsCorrelatedEquilibrium Γ.u p.weight

end FAFBridge

end Cleanroom.Fixpoint.FixOraclesCorresp
