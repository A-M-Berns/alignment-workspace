import Cleanroom.Corrigibility.CorrGeneralObject.ExampleA
import Cleanroom.Corrigibility.CorrGeneralObject.Conjunction
import Cleanroom.Corrigibility.CorrReflectFrames.Good
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.GDelta.Basic

/-!
# corr-general-object — T6: the resistance value; T18, T19

* **T6(a)** `R_t(Q) = max{0, P(E_Q)·regret_Q − VOI_t(E_Q)}` (`resistanceValue_eq`) and the
  twin `procure = max{0, VOI − P(E_Q)·regret_Q}` (`procureValue_eq`) — algebra of the
  definitions (kind L; the mandate's pre-label C is corrected: with these definitions it is
  `ring`).
* **T6(b)** Good's theorem `0 ≤ VOI_t(E_Q)` (`voiPush_nonneg`, the two-branch instance of
  `corr-reflect-frames`' finite Jensen `sup'_sum_le_sum_sup'`); decision-local trust kills
  resistance (`resistanceValue_eq_zero_of_isOptimal_postPush`, with the sign of `U − M`
  stated), in particular endorsement does (`resistanceValue_eq_zero_of_endorsed`).
* **T6(c)** Good's theorem is neither necessary nor sufficient: Example A at `πQ = plan₂` —
  `k₂`: `R = 0`, `VOI = 6/5`; `k₃`: `R = 6/5`, `VOI = 0`; CE5 `k₅`: `R = 3/10 = 3/2 − 6/5` with
  `P(E_Q)·regret = 3/2` (refuting the develop's equality clause); `k₆ = (0, 1/2, 1)`: `R = 0`
  with `U − M = −3/2 < 0` while `πQ` is *not* optimal in the cell (`VOI = 3`).
* **T6(d)** the self-chosen uninformative target is never strictly preferred (kind T).
* **T6(e)** the two-option shutdown instance: `R = max{0, E[V c 1_{E_Q}]} = max{0, −Δ₋}` —
  `corr-three-step`'s hard-button difference (instance `exA_two_option_witness`: on
  `{plan₁, a₀ ≡ 0}`, `R = 3/20` under `k₂` and `R = 0` under `k₆`, through the theorem).
* **T18** Wentworth's Level 1 as a genericity theorem: indifference iff `U = M`; the
  indifference set of kernels has **empty interior** under decision-relevance
  (`interior_indifference_eq_empty`), which is one clause — `¬ IsOptimal P V πQ`
  (`decision_relevant_iff_not_isOptimal`) — so the headline is
  `interior_indifference_eq_empty_of_not_isOptimal`, and the set being closed it is **nowhere
  dense** (`indifference_isNowhereDense`; exact against inventory 2-007's own flag, a variant
  of the unnamed "measure zero"); relative to the cube, every kernel has a non-indifferent
  kernel within any `ε` (`indifference_no_relative_interior`); both signs witnessed in
  Example A, which satisfies the hypothesis (`exA_decision_relevant`).
* **T19** `R = 0` characterised (`resistanceValue_eq_zero_iff`), the exact converse of T6(b)
  under `VOI = 0` (`resistanceValue_eq_zero_iff_of_voi_zero`), its failure at `VOI > 0`
  (`k₆`), and the procurement twin's identity.

Sources: [[general-object-final]] D8, S8, P8, (E), CE5, R4; [[d1-special-case-final]] S10, P7;
[[wentworth-respondent]] C1–C2; [[corr-wf14b-inventory]] 007, 009, 015; [[corr-wf14b-2-inventory]] 007.
-/

namespace Cleanroom.Corrigibility.CorrGeneralObject

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω] {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]

/-! ## (a) the exact identity -/

/-- **The resistance value identity**: `R_t(Q) = max{0, P(E_Q)·regret_Q − VOI_t(E_Q)}`.
Source: [[general-object-final]] S8(a), P8 (`U − M = P(E_Q) regret_Q − (I − U)`)
Kind: L
Fidelity: exact (with the definitions of record this is `ring`; the mandate's pre-label `C`
overstates it) -/
theorem resistanceValue_eq (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) (πQ : A) :
    resistanceValue P k V πQ = max 0 (cellRegret P k V πQ - voiPush P k V) := by
  unfold resistanceValue cellRegret voiPush informedValue modifiedValue
  congr 1; ring

/-- **The procurement twin**: `procure = max{0, VOI_t(E_Q) − P(E_Q)·regret_Q}`.
Source: [[general-object-final]] D8 (sign-reversed twin), Open problem 10; [[corr-wf14b-inventory]] 015
Kind: L
Fidelity: exact -/
theorem procureValue_eq (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) (πQ : A) :
    procureValue P k V πQ = max 0 (voiPush P k V - cellRegret P k V πQ) := by
  unfold procureValue cellRegret voiPush informedValue modifiedValue
  congr 1; ring

/-! ## (b) Good's theorem and decision-local trust -/

/-- **Good's theorem for the push**: `0 ≤ VOI_t(E_Q)` — the best action under the prior is at
most the sum of the best actions on the two branches (the two-branch instance of
`corr-reflect-frames`' finite Jensen `sup'_sum_le_sum_sup'`, with the branch weights `1` and
`v = (pushExpect, offExpect)`).
Source: [[general-object-final]] S8 ("`VOI_t(E_Q) := I − U ≥ 0` (Good's theorem)"), P8;
`corr-reflect-frames` `sup'_sum_le_sum_sup'`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem voiPush_nonneg (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) : 0 ≤ voiPush P k V := by
  unfold voiPush informedValue priorValue
  rw [sub_nonneg, sup'_le_iff]
  intro a _
  rw [← pushExpect_add_offExpect P k (V a)]
  exact add_le_add (le_sup' (fun a => pushExpect P k (V a)) (mem_univ a))
    (le_sup' (fun a => offExpect P k (V a)) (mem_univ a))

/-- The cell regret is nonnegative. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem cellRegret_nonneg (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) (πQ : A) :
    0 ≤ cellRegret P k V πQ := by
  unfold cellRegret
  rw [sub_nonneg]
  exact le_sup' (fun a => pushExpect P k (V a)) (mem_univ πQ)

/-- **Decision-local trust in the cell kills resistance**: if `πQ` is optimal under `P(· | E_Q)`
then `U − M ≤ 0` and `R_t(Q) = 0` (the sign is stated, so the `max 0` is not doing the work).
Source: [[general-object-final]] S8(b) ("`R_t(Q) = 0` whenever `π^Q` is optimal under
`P_t(· | E_Q)` — decision-local Total Trust in the cell")
Kind: P
Fidelity: exact
Hyps: (a) the guard; `IsOptimal (postPush) V πQ` -/
theorem resistanceValue_eq_zero_of_isOptimal_postPush (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k)
    (V : A → Ω → ℝ) (h : 0 < pushMass P k) {πQ : A}
    (hopt : IsOptimal (postPush P k hk.nonneg h) V πQ) :
    priorValue P V - modifiedValue P k V πQ ≤ 0 ∧ resistanceValue P k V πQ = 0 := by
  have hreg : cellRegret P k V πQ ≤ 0 := by
    unfold cellRegret
    rw [sub_nonpos, sup'_le_iff]
    intro a _
    have := (isOptimal_postPush_iff P hk V h πQ).1 hopt a
    rw [pushExpect_sub] at this
    linarith
  have hvoi := voiPush_nonneg P k V
  have hsign : priorValue P V - modifiedValue P k V πQ = cellRegret P k V πQ - voiPush P k V := by
    unfold cellRegret voiPush informedValue modifiedValue; ring
  refine ⟨by rw [hsign]; linarith, ?_⟩
  unfold resistanceValue
  rw [hsign, max_eq_left (by linarith)]

/-- **Endorsement kills resistance**: an endorsed push toward a target whose plan is `πQ` has
`R_t(Q) = 0` (and `U − M ≤ 0`), since `postPush = Q` and `πQ` is `Q`-optimal.
Source: [[general-object-final]] S8(b) ("in particular whenever the push is endorsed")
Kind: C
Fidelity: exact
Hyps: (a) the guard, `Endorsed`, `hπQ` -/
theorem resistanceValue_eq_zero_of_endorsed (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k)
    (V : A → Ω → ℝ) (h : 0 < pushMass P k) {Q : Distr Ω} (hE : Endorsed P k Q) {πQ : A}
    (hπQ : IsOptimal Q V πQ) :
    priorValue P V - modifiedValue P k V πQ ≤ 0 ∧ resistanceValue P k V πQ = 0 := by
  apply resistanceValue_eq_zero_of_isOptimal_postPush P hk V h
  rw [(endorsed_iff_postPush_eq P hk.nonneg h Q).1 hE]
  exact hπQ

/-! ## (d) the self-chosen target -/

/-- **The self-chosen uninformative target is never strictly preferred**: `E_P[V πQ] ≤ E_P[V a^P]`
— the definition of `a^P` (kind T, not a headline; Omohundro's drive transposed to belief).
Source: [[general-object-final]] S9(S); [[corr-wf14b-inventory]] 009
Kind: T
Fidelity: exact -/
theorem expect_le_of_isOptimal (P : Distr Ω) (V : A → Ω → ℝ) {aP : A} (haP : IsOptimal P V aP)
    (πQ : A) : expect P (V πQ) ≤ expect P (V aP) := haP πQ

/-! ## (e) the two-option shutdown instance -/

/-- The supremum over a two-element menu. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sup'_two (f : A → ℝ) {c a₀ : A} (hall : ∀ b, b = c ∨ b = a₀) :
    univ.sup' univ_nonempty f = max (f c) (f a₀) := by
  apply le_antisymm
  · rw [sup'_le_iff]
    intro b _
    rcases hall b with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (le_sup' f (mem_univ c)) (le_sup' f (mem_univ a₀))

/-- **The shutdown instance (d1 S10)**: on the two-option menu `{c, a₀}` under N0 and the
continue-by-default regime (`0 ≤ E_P[V c]`, `0 ≤ E[V c 1_{¬E_Q}]`),
`R_t(Q) = max{0, E[V c 1_{E_Q}]}` — a forced shutdown is worth preventing iff the below-threshold
inequality fails on it — and this is `max{0, −Δ₋(c, a₀)}` of the bridge: the positive part of
`−Δ₋`, the mirror of `corr-three-step`'s `voiButton2 = max Δ₋ 0` (`voiButton2_eq_max_deltaMinus`).
Source: [[d1-special-case-final]] S10, P7 (`gain_forced = μ(Pr) E[X | Pr]`); `corr-three-step`
`hardButton_sub_disabled`, `voiButton2_eq_max_deltaMinus`
Kind: L
Fidelity: exact (one-shot, N0, two options, the regime hypotheses as the source states them)
Hyps: (a) N0, the regime, the two-option menu -/
theorem resistanceValue_shutdown_two_option (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k)
    (V : A → Ω → ℝ) {c a₀ : A} (hall : ∀ b, b = c ∨ b = a₀) (hN0 : ∀ ω, V a₀ ω = 0)
    (hprior : 0 ≤ expect P (V c)) (hoff : 0 ≤ offExpect P k (V c))
    (h1 : ({a₀} : Finset A).Nonempty) (h2 : ({a₀} : Finset A)ᶜ.Nonempty) :
    resistanceValue P k V a₀ = max 0 (pushExpect P k (V c)) ∧
      resistanceValue P k V a₀ = max 0 (-(toThreeStep P k hk V {a₀} h1 h2).deltaMinus () c a₀) := by
  have hE0 : expect P (V a₀) = 0 := by unfold expect; simp [hN0]
  have hoff0 : offExpect P k (V a₀) = 0 := by unfold offExpect; simp [hN0]
  have hpush0 : pushExpect P k (V a₀) = 0 := by unfold pushExpect; simp [hN0]
  have hU : priorValue P V = expect P (V c) := by
    unfold priorValue; rw [sup'_two _ hall, hE0, max_eq_left hprior]
  have hM : modifiedValue P k V a₀ = offExpect P k (V c) := by
    unfold modifiedValue; rw [sup'_two _ hall, hoff0, hpush0, max_eq_left hoff, add_zero]
  have hdiff : priorValue P V - modifiedValue P k V a₀ = pushExpect P k (V c) := by
    rw [hU, hM, ← pushExpect_add_offExpect P k (V c)]; ring
  refine ⟨by unfold resistanceValue; rw [hdiff], ?_⟩
  unfold resistanceValue
  rw [hdiff, ThreeStep.deltaMinus, toThreeStep_obsExpect_press, toThreeStep_Xo, neg_neg]
  congr 1
  have : devVar V a₀ c = V c - V a₀ := by funext ω; rfl
  rw [this, pushExpect_sub, hpush0, sub_zero]

/-! ## T18: Wentworth's Level 1 as a genericity theorem -/

/-- **Indifference iff `U = M`**: `R = 0 ∧ procure = 0 ↔ priorValue = modifiedValue`.
Source: [[wentworth-respondent]] C1 ("indifferent to the modification landing only on …");
[[corr-wf14b-2-inventory]] 007
Kind: L
Fidelity: exact -/
theorem indifferent_iff (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) (πQ : A) :
    (resistanceValue P k V πQ = 0 ∧ procureValue P k V πQ = 0) ↔
      priorValue P V = modifiedValue P k V πQ := by
  unfold resistanceValue procureValue
  constructor
  · rintro ⟨h1, h2⟩
    have := max_eq_left_iff.1 h1
    have := max_eq_left_iff.1 h2
    linarith
  · intro h
    rw [h, sub_self, max_self, and_self]

/-- The off-push expectation after a one-coordinate perturbation of the kernel.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem offExpect_add_single (P : Distr Ω) (k : Ω → ℝ) (ω₀ : Ω) (t : ℝ) (X : Ω → ℝ) :
    offExpect P (k + Pi.single ω₀ t) X = offExpect P k X - t * (P.mass ω₀ * X ω₀) := by
  unfold offExpect
  have key : ∑ ω, P.mass ω * (1 - (k + Pi.single ω₀ t : Ω → ℝ) ω) * X ω =
      ∑ ω, (P.mass ω * (1 - k ω) * X ω - (if ω = ω₀ then t * (P.mass ω₀ * X ω₀) else 0)) := by
    apply sum_congr rfl; intro ω _
    by_cases h : ω = ω₀
    · subst h; simp only [Pi.add_apply, Pi.single_eq_same, if_true]; ring
    · simp only [Pi.add_apply, Pi.single_eq_of_ne h, add_zero, if_neg h, sub_zero]
  rw [key, sum_sub_distrib, sum_ite_eq' univ ω₀]
  simp

/-- The push expectation after a one-coordinate perturbation of the kernel.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem pushExpect_add_single (P : Distr Ω) (k : Ω → ℝ) (ω₀ : Ω) (t : ℝ) (X : Ω → ℝ) :
    pushExpect P (k + Pi.single ω₀ t) X = pushExpect P k X + t * (P.mass ω₀ * X ω₀) := by
  unfold pushExpect
  have key : ∑ ω, P.mass ω * (k + Pi.single ω₀ t : Ω → ℝ) ω * X ω =
      ∑ ω, (P.mass ω * k ω * X ω + (if ω = ω₀ then t * (P.mass ω₀ * X ω₀) else 0)) := by
    apply sum_congr rfl; intro ω _
    by_cases h : ω = ω₀
    · subst h; simp only [Pi.add_apply, Pi.single_eq_same, if_true]; ring
    · simp only [Pi.add_apply, Pi.single_eq_of_ne h, add_zero, if_neg h]
  rw [key, sum_add_distrib, sum_ite_eq' univ ω₀]
  simp

/-- **Decision-relevance is one clause**: the hypothesis `hne` of `interior_indifference_eq_empty`
("for every `a`, `V a ≠ V πQ` on a `P`-positive world or `E_P[V a] ≠ U`") is equivalent to
`¬ IsOptimal P V πQ` — the push is decision-relevant *at the prior*. Its `a = πQ` instance is
`E_P[V πQ] ≠ U`; conversely an `a` with `V a = V πQ` `P`-a.e. has `E_P[V a] = E_P[V πQ] ≠ U`.
Source: [[wentworth-respondent]] C1 ("… or the push is decision-irrelevant (S10(a))"); audit
r1 fidelity 3.3 (probe `HneEquiv.lean`)
Kind: L
Fidelity: exact -/
theorem decision_relevant_iff_not_isOptimal (P : Distr Ω) (V : A → Ω → ℝ) (πQ : A) :
    (∀ a, (∃ ω, 0 < P.mass ω ∧ V a ω ≠ V πQ ω) ∨ expect P (V a) ≠ priorValue P V) ↔
      ¬ IsOptimal P V πQ := by
  have h1 : (∀ a, (∃ ω, 0 < P.mass ω ∧ V a ω ≠ V πQ ω) ∨ expect P (V a) ≠ priorValue P V) ↔
      expect P (V πQ) ≠ priorValue P V := by
    constructor
    · intro h
      rcases h πQ with ⟨_, _, hne⟩ | h
      · exact absurd rfl hne
      · exact h
    · intro h a
      by_cases ha : expect P (V a) = priorValue P V
      · left
        by_contra hc
        push Not at hc
        apply h
        rw [← ha]
        unfold expect
        apply sum_congr rfl
        intro ω _
        by_cases hP : P.mass ω = 0
        · rw [hP]; ring
        · have hPpos : 0 < P.mass ω := lt_of_le_of_ne (P.nonneg ω) (Ne.symm hP)
          rw [hc ω hPpos]
      · right; exact ha
  rw [h1]
  unfold IsOptimal priorValue
  have hle : expect P (V πQ) ≤ univ.sup' univ_nonempty (fun a => expect P (V a)) :=
    le_sup' (fun a => expect P (V a)) (mem_univ πQ)
  constructor
  · intro hne hopt
    apply hne
    apply le_antisymm hle
    rw [sup'_le_iff]
    intro b _
    exact hopt b
  · intro hnot heq
    apply hnot
    intro b
    rw [heq]
    exact le_sup' (fun a => expect P (V a)) (mem_univ b)

/-- **T18(b): the indifference set has empty interior** (the honest form of "measure zero"). For
fixed `(P, V, πQ)` such that the push is decision-relevant — for every `a`, either `V a` and
`V πQ` differ at some `P`-positive world, or `E_P[V a] ≠ U` — the set of kernels
`{k | priorValue = modifiedValue k}` has empty interior in `Ω → ℝ` (sup metric). Proof: at an
interior point `k₀`, a maximiser `a*` of `offExpect k₀` has the affine function
`φ(k) = offExpect k (V a*) + pushExpect k (V πQ) − U` vanishing at `k₀` and `≤ 0` nearby; moving
one coordinate both ways forces `P ω (V a* ω − V πQ ω) = 0` for every `ω`, and then
`E_P[V a*] = U`, contradicting decision-relevance at `a*`. The hypothesis `hne` is just
`¬ IsOptimal P V πQ` (`decision_relevant_iff_not_isOptimal`): its `a = πQ` instance forces
`E_P[V πQ] ≠ U`, so the push must be decision-relevant *at the prior*; the one-clause headline is
`interior_indifference_eq_empty_of_not_isOptimal`.
Source: [[wentworth-respondent]] C1 ("only on a measure-zero set of `(K, Q)`");
[[corr-wf14b-2-inventory]] 007
Kind: P
Fidelity: variant: empty interior over all of `ℝ^Ω` (which contains the kernel cube's interior)
in place of the inventory's unnamed "measure zero"; the decision-relevance hypothesis replaces
the mandate's "nontrivial preferences on both branches", which does not suffice (if `πQ` is the
unique `P`-optimal action, small pushes are indifferent on an open set)
Hyps: (a) decision-relevance `hne` (= `¬ IsOptimal P V πQ`) -/
theorem interior_indifference_eq_empty (P : Distr Ω) (V : A → Ω → ℝ) (πQ : A)
    (hne : ∀ a, (∃ ω, 0 < P.mass ω ∧ V a ω ≠ V πQ ω) ∨ expect P (V a) ≠ priorValue P V) :
    interior {k : Ω → ℝ | priorValue P V = modifiedValue P k V πQ} = ∅ := by
  apply Set.eq_empty_of_subset_empty
  intro k₀ hk₀
  exfalso
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior k₀ hk₀
  have hmem : ∀ t : ℝ, |t| < ε → ∀ ω,
      priorValue P V = modifiedValue P (k₀ + Pi.single ω t) V πQ := by
    intro t ht ω
    apply interior_subset (hball _)
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro b
    by_cases hb : b = ω
    · subst hb; simp [Real.dist_eq, ht]
    · simp [Pi.single_eq_of_ne hb, hε]
  obtain ⟨a, _, ha⟩ := exists_max_image univ (fun a => offExpect P k₀ (V a)) univ_nonempty
  have hsup : univ.sup' univ_nonempty (fun b => offExpect P k₀ (V b)) = offExpect P k₀ (V a) :=
    le_antisymm (sup'_le _ _ fun b hb => ha b hb)
      (le_sup' (fun b => offExpect P k₀ (V b)) (mem_univ a))
  have h0 : priorValue P V = offExpect P k₀ (V a) + pushExpect P k₀ (V πQ) := by
    have := interior_subset hk₀
    simp only [Set.mem_setOf_eq] at this
    rw [this]; unfold modifiedValue; rw [hsup]
  have hlin : ∀ ω, P.mass ω * (V a ω - V πQ ω) = 0 := by
    intro ω
    have key : ∀ t : ℝ, |t| < ε → 0 ≤ t * (P.mass ω * (V a ω - V πQ ω)) := by
      intro t ht
      have h1 := hmem t ht ω
      have hoff := offExpect_add_single P k₀ ω t (V a)
      have hpu := pushExpect_add_single P k₀ ω t (V πQ)
      obtain ⟨k₁, hk₁⟩ : ∃ k₁ : Ω → ℝ, k₁ = k₀ + Pi.single ω t := ⟨_, rfl⟩
      rw [← hk₁] at h1 hoff hpu
      have h2 : offExpect P k₁ (V a) + pushExpect P k₁ (V πQ) ≤ modifiedValue P k₁ V πQ := by
        unfold modifiedValue
        exact add_le_add (le_sup' (fun b => offExpect P k₁ (V b)) (mem_univ a)) (le_refl _)
      rw [← h1, hoff, hpu, h0] at h2
      linarith
    have hp := key (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith)
    have hn := key (-(ε / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
    have hε2 : 0 < ε / 2 := by linarith
    have h1 : 0 ≤ P.mass ω * (V a ω - V πQ ω) := (mul_nonneg_iff_of_pos_left hε2).1 hp
    have h2 : 0 ≤ -(P.mass ω * (V a ω - V πQ ω)) := by
      have : 0 ≤ ε / 2 * -(P.mass ω * (V a ω - V πQ ω)) := by linarith
      exact (mul_nonneg_iff_of_pos_left hε2).1 this
    linarith
  rcases hne a with ⟨ω, hP, hV⟩ | hconst
  · have := hlin ω
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hP.ne'
    · exact hV (by linarith)
  · apply hconst
    have hz : pushExpect P k₀ (V a - V πQ) = 0 := by
      unfold pushExpect
      apply sum_eq_zero
      intro ω _
      have := hlin ω
      simp only [Pi.sub_apply]
      calc P.mass ω * k₀ ω * (V a ω - V πQ ω) = k₀ ω * (P.mass ω * (V a ω - V πQ ω)) := by ring
        _ = 0 := by rw [this, mul_zero]
    rw [pushExpect_sub] at hz
    have := pushExpect_add_offExpect P k₀ (V a)
    linarith

/-- The indifference set restricted to the kernel cube has empty *ambient* interior — interior
taken in `Ω → ℝ`, a corollary of the unrestricted theorem by `interior_mono`. This is weaker than
the relative statement "no relatively open piece of the cube `[0,1]^Ω` lies in the indifference
set", which is `indifference_no_relative_interior` below (every ball around a point of the closed
cube meets the open cube; audit r2 adversarial 3.4, proved in repair round 2).
Source: [[corr-wf14b-2-inventory]] 007
Kind: C
Fidelity: weaker: ambient interior; the relative statement is `indifference_no_relative_interior`
Hyps: (a) `hne` -/
theorem interior_indifference_cube_eq_empty (P : Distr Ω) (V : A → Ω → ℝ) (πQ : A)
    (hne : ∀ a, (∃ ω, 0 < P.mass ω ∧ V a ω ≠ V πQ ω) ∨ expect P (V a) ≠ priorValue P V) :
    interior {k : Ω → ℝ | IsKernel k ∧ priorValue P V = modifiedValue P k V πQ} = ∅ := by
  apply Set.eq_empty_of_subset_empty
  rw [← interior_indifference_eq_empty P V πQ hne]
  exact interior_mono fun k hk => hk.2

/-- **T18(b), one-clause form**: if `πQ` is not `P`-optimal — the push is decision-relevant at
the prior — the indifference set of kernels has empty interior. This is the respondent's own
sentence: a complete-preference agent is indifferent to a modification "only where `π^Q` is
optimal under `P_t(· | E_Q)` … or the push is decision-irrelevant", and off those cases only on a
thin set.
Source: [[wentworth-respondent]] C1; [[corr-wf14b-2-inventory]] 007; audit r1 fidelity 3.3
Kind: C
Fidelity: variant: empty interior (nowhere dense: `indifference_isNowhereDense`) for the
inventory's unnamed "measure zero"
Hyps: (a) `¬ IsOptimal P V πQ` -/
theorem interior_indifference_eq_empty_of_not_isOptimal (P : Distr Ω) (V : A → Ω → ℝ) (πQ : A)
    (hne : ¬ IsOptimal P V πQ) :
    interior {k : Ω → ℝ | priorValue P V = modifiedValue P k V πQ} = ∅ :=
  interior_indifference_eq_empty P V πQ ((decision_relevant_iff_not_isOptimal P V πQ).2 hne)

/-- `modifiedValue` is continuous in the kernel: a finite sup of affine functions of `k` plus an
affine function of `k`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem continuous_modifiedValue (P : Distr Ω) (V : A → Ω → ℝ) (πQ : A) :
    Continuous (fun k : Ω → ℝ => modifiedValue P k V πQ) := by
  unfold modifiedValue offExpect pushExpect
  fun_prop

/-- The indifference set of kernels is closed (the zero set of a continuous function of `k`).
Source: audit r1 fidelity 3.3. Kind: L. Fidelity: n/a -/
theorem indifference_isClosed (P : Distr Ω) (V : A → Ω → ℝ) (πQ : A) :
    IsClosed {k : Ω → ℝ | priorValue P V = modifiedValue P k V πQ} :=
  isClosed_eq continuous_const (continuous_modifiedValue P V πQ)

/-- **T18(b), nowhere dense**: under decision-relevance the indifference set of kernels is closed
with empty interior, i.e. nowhere dense in `Ω → ℝ` — the form inventory 2-007's own flag asks
for ("nowhere dense / proper algebraic subset") in place of the unnamed "measure zero".
Source: [[corr-wf14b-2-inventory]] 007 (the flag); [[wentworth-respondent]] C1; audit r1
fidelity 3.3
Kind: C
Fidelity: exact against the inventory's repaired statement ("nowhere dense")
Hyps: (a) `¬ IsOptimal P V πQ` -/
theorem indifference_isNowhereDense (P : Distr Ω) (V : A → Ω → ℝ) (πQ : A)
    (hne : ¬ IsOptimal P V πQ) :
    IsNowhereDense {k : Ω → ℝ | priorValue P V = modifiedValue P k V πQ} :=
  (indifference_isClosed P V πQ).isNowhereDense_iff.2
    (interior_indifference_eq_empty_of_not_isOptimal P V πQ hne)

/-- **T18(b), relative form**: no kernel is a relative-interior point of the indifference set
within the cube — for every kernel `k₀` and every `ε > 0` there is a kernel within `ε` of `k₀`
(sup metric) that is *not* indifferent. Proof: move `k₀` into the open cube by
`k₁ = k₀ + δ(½ − k₀)` with `δ = min ε 1` (so `dist k₁ k₀ ≤ δ/2`), take a ball around `k₁` inside
the open cube (`isOpen_set_pi`), and use `interior_indifference_eq_empty_of_not_isOptimal` to find
a non-indifferent point of that ball; it is a kernel and within `δ ≤ ε` of `k₀`. This is the
"empty interior relative to the cube" statement that the ambient corollary
`interior_indifference_cube_eq_empty` does not give (audit r2 adversarial 3.4; repair round 2).
Source: [[corr-wf14b-2-inventory]] 007; [[wentworth-respondent]] C1; audit r2 adversarial 3.4
Kind: C
Fidelity: exact (the relative-interior statement, in elementary `ε`-form)
Hyps: (a) `¬ IsOptimal P V πQ`, `IsKernel k₀`, `0 < ε` -/
theorem indifference_no_relative_interior (P : Distr Ω) (V : A → Ω → ℝ) (πQ : A)
    (hne : ¬ IsOptimal P V πQ) (k₀ : Ω → ℝ) (hk₀ : IsKernel k₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : Ω → ℝ, IsKernel k ∧ dist k k₀ < ε ∧ priorValue P V ≠ modifiedValue P k V πQ := by
  -- the open cube is open
  have hopen : IsOpen {k : Ω → ℝ | ∀ ω, k ω ∈ Set.Ioo (0:ℝ) 1} := by
    have : {k : Ω → ℝ | ∀ ω, k ω ∈ Set.Ioo (0:ℝ) 1} = Set.pi Set.univ (fun _ => Set.Ioo 0 1) := by
      ext k; simp [Set.mem_pi]
    rw [this]; exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  -- a point of the open cube within `δ/2` of `k₀`
  set δ : ℝ := min ε 1 with hδ
  have hδpos : 0 < δ := lt_min hε one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  set k₁ : Ω → ℝ := fun ω => k₀ ω + δ * (1/2 - k₀ ω) with hk₁
  have hk₁mem : k₁ ∈ {k : Ω → ℝ | ∀ ω, k ω ∈ Set.Ioo (0:ℝ) 1} := by
    intro ω
    obtain ⟨h0, h1⟩ := hk₀ ω
    simp only [hk₁, Set.mem_Ioo]
    constructor <;> nlinarith
  have hdist₁ : dist k₁ k₀ ≤ δ / 2 := by
    rw [dist_pi_le_iff (by positivity)]
    intro ω
    rw [Real.dist_eq]
    simp only [hk₁]
    obtain ⟨h0, h1⟩ := hk₀ ω
    rw [abs_le]; constructor <;> nlinarith
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen k₁ hk₁mem
  -- `k₁` is not an interior point of the indifference set
  have hint := interior_indifference_eq_empty_of_not_isOptimal P V πQ hne
  have hnot : ¬ Metric.ball k₁ (min r (δ/2)) ⊆
      {k : Ω → ℝ | priorValue P V = modifiedValue P k V πQ} := by
    intro hsub
    have hmem : k₁ ∈ interior {k : Ω → ℝ | priorValue P V = modifiedValue P k V πQ} :=
      mem_interior.2 ⟨_, hsub, Metric.isOpen_ball, Metric.mem_ball_self (lt_min hr (by positivity))⟩
    rw [hint] at hmem
    exact hmem
  rw [Set.not_subset] at hnot
  obtain ⟨k, hk, hkS⟩ := hnot
  refine ⟨k, ?_, ?_, hkS⟩
  · have hkC := hball (Metric.ball_subset_ball (min_le_left _ _) hk)
    intro ω
    exact ⟨(hkC ω).1.le, (hkC ω).2.le⟩
  · calc dist k k₀ ≤ dist k k₁ + dist k₁ k₀ := dist_triangle _ _ _
      _ < min r (δ/2) + δ/2 := add_lt_add_of_lt_of_le (Metric.mem_ball.1 hk) hdist₁
      _ ≤ δ/2 + δ/2 := by linarith [min_le_right r (δ/2)]
      _ = δ := by ring
      _ ≤ ε := hδε

/-! ## T19: `R = 0` characterised -/

/-- **No resistance iff every alternative's push-cell advantage over `πQ` is covered by its own
off-cell shortfall**: `R = 0 ↔ ∀ a, E[(V a − V πQ) 1_{E_Q}] ≤ max_b E[V b 1_{¬E_Q}] − E[V a 1_{¬E_Q}]`.
Source: mandate T19(a) (S8(b)'s converse, the plan's agenda item)
Kind: L
Fidelity: exact -/
theorem resistanceValue_eq_zero_iff (P : Distr Ω) (k : Ω → ℝ) (V : A → Ω → ℝ) (πQ : A) :
    resistanceValue P k V πQ = 0 ↔
      ∀ a, pushExpect P k (V a - V πQ) ≤
        univ.sup' univ_nonempty (fun b => offExpect P k (V b)) - offExpect P k (V a) := by
  unfold resistanceValue
  rw [max_eq_left_iff, sub_nonpos]
  unfold priorValue modifiedValue
  rw [sup'_le_iff]
  constructor
  · intro h a
    have := h a (mem_univ a)
    rw [← pushExpect_add_offExpect P k (V a)] at this
    rw [pushExpect_sub]; linarith
  · intro h a _
    have := h a
    rw [pushExpect_sub] at this
    rw [← pushExpect_add_offExpect P k (V a)]; linarith

/-- **The exact converse of T6(b) under Good's equality case**: when `VOI_t(E_Q) = 0`,
`R_t(Q) = 0 ↔ πQ` is optimal under `P(· | E_Q)`.
Source: mandate T19(b) (S8(b)'s converse)
Kind: P
Fidelity: exact
Hyps: (a) `voiPush = 0`, the guard -/
theorem resistanceValue_eq_zero_iff_of_voi_zero (P : Distr Ω) {k : Ω → ℝ} (hk : IsKernel k)
    (V : A → Ω → ℝ) (h : 0 < pushMass P k) (πQ : A) (hvoi : voiPush P k V = 0) :
    resistanceValue P k V πQ = 0 ↔ IsOptimal (postPush P k hk.nonneg h) V πQ := by
  rw [resistanceValue_eq, hvoi, sub_zero, max_eq_left_iff, isOptimal_postPush_iff P hk V h πQ]
  unfold cellRegret
  rw [sub_nonpos, sup'_le_iff]
  constructor
  · intro H b; have := H b (mem_univ b); rw [pushExpect_sub]; linarith
  · intro H b _; have := H b; rw [pushExpect_sub] at this; linarith

/-! ## Witnesses (Example A, `πQ = plan₂`) -/

/-- The supremum over `Fin 3`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sup'_fin3 (f : Fin 3 → ℝ) :
    (univ : Finset (Fin 3)).sup' univ_nonempty f = max (max (f 0) (f 1)) (f 2) := by
  apply le_antisymm
  · rw [sup'_le_iff]
    intro i _
    fin_cases i
    · exact le_max_of_le_left (le_max_left _ _)
    · exact le_max_of_le_left (le_max_right _ _)
    · exact le_max_right _ _
  · exact max_le (max_le (le_sup' f (mem_univ 0)) (le_sup' f (mem_univ 1))) (le_sup' f (mem_univ 2))

/-- Example A's prior value is `4`. Source: [[general-object-final]] P8 (`U = 4`). Kind: L. Fidelity: exact -/
theorem exA_priorValue : priorValue exA_P exA_V = 4 := by
  unfold priorValue
  rw [sup'_fin3]
  simp [expect, exA_P, exA_V, Fin.sum_univ_three]
  norm_num [max_def]

/-- **N+ (k₂): `R = 0` and `VOI = 6/5`** — non-resistance with a valuable channel; `U − M = −6/5`.
Source: [[general-object-final]] S8(d), P8 (script (E), `k = (1/10, 3/5, 1/10)`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exA_k2_resist :
    priorValue exA_P exA_V - modifiedValue exA_P exA_k2 exA_V 1 = -6/5 ∧
      resistanceValue exA_P exA_k2 exA_V 1 = 0 ∧ voiPush exA_P exA_k2 exA_V = 6/5 ∧
      cellRegret exA_P exA_k2 exA_V 1 = 0 := by
  have hpush : (univ : Finset (Fin 3)).sup' univ_nonempty (fun a => pushExpect exA_P exA_k2 (exA_V a)) = 27/20 := by
    rw [sup'_fin3]; simp [pushExpect, exA_P, exA_k2, exA_V, Fin.sum_univ_three]; norm_num [max_def]
  have hoff : (univ : Finset (Fin 3)).sup' univ_nonempty (fun a => offExpect exA_P exA_k2 (exA_V a)) = 77/20 := by
    rw [sup'_fin3]; simp [offExpect, exA_P, exA_k2, exA_V, Fin.sum_univ_three]; norm_num [max_def]
  have hπ : pushExpect exA_P exA_k2 (exA_V 1) = 27/20 := by
    simp [pushExpect, exA_P, exA_k2, exA_V, Fin.sum_univ_three]; norm_num
  have hM : modifiedValue exA_P exA_k2 exA_V 1 = 26/5 := by
    unfold modifiedValue; rw [hoff, hπ]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [exA_priorValue, hM]; norm_num
  · unfold resistanceValue; rw [exA_priorValue, hM]; norm_num
  · unfold voiPush informedValue; rw [hpush, hoff, exA_priorValue]; norm_num
  · unfold cellRegret; rw [hpush, hπ]; norm_num

/-- **N+ (k₃): `R = 6/5` and `VOI = 0`** — resistance with a worthless channel.
Source: [[general-object-final]] S8(d), P8 (`k = (1/2, 3/5, 1/2)`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exA_k3_resist :
    priorValue exA_P exA_V - modifiedValue exA_P exA_k3 exA_V 1 = 6/5 ∧
      resistanceValue exA_P exA_k3 exA_V 1 = 6/5 ∧ voiPush exA_P exA_k3 exA_V = 0 ∧
      cellRegret exA_P exA_k3 exA_V 1 = 6/5 := by
  have hpush : (univ : Finset (Fin 3)).sup' univ_nonempty (fun a => pushExpect exA_P exA_k3 (exA_V a)) = 39/20 := by
    rw [sup'_fin3]; simp [pushExpect, exA_P, exA_k3, exA_V, Fin.sum_univ_three]; norm_num [max_def]
  have hoff : (univ : Finset (Fin 3)).sup' univ_nonempty (fun a => offExpect exA_P exA_k3 (exA_V a)) = 41/20 := by
    rw [sup'_fin3]; simp [offExpect, exA_P, exA_k3, exA_V, Fin.sum_univ_three]; norm_num [max_def]
  have hπ : pushExpect exA_P exA_k3 (exA_V 1) = 15/20 := by
    simp [pushExpect, exA_P, exA_k3, exA_V, Fin.sum_univ_three]; norm_num
  have hM : modifiedValue exA_P exA_k3 exA_V 1 = 14/5 := by
    unfold modifiedValue; rw [hoff, hπ]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [exA_priorValue, hM]; norm_num
  · unfold resistanceValue; rw [exA_priorValue, hM]; norm_num
  · unfold voiPush informedValue; rw [hpush, hoff, exA_priorValue]; norm_num
  · unfold cellRegret; rw [hpush, hπ]; norm_num

/-- **N+ CE5 (k₅): `R = 3/10 = 3/2 − 6/5`** with `P(E_Q)·regret = 3/2` — the develop's "equality iff
no information off the cell" is refuted (no information off the cell here, and `R < 3/2`).
Source: [[general-object-final]] S8(a), P8, CE5 (`k = (1/10, 1/10, 3/5)`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exA_k5_resist :
    resistanceValue exA_P exA_k5 exA_V 1 = 3/10 ∧ cellRegret exA_P exA_k5 exA_V 1 = 3/2 ∧
      voiPush exA_P exA_k5 exA_V = 6/5 ∧ modifiedValue exA_P exA_k5 exA_V 1 = 37/10 := by
  have hpush : (univ : Finset (Fin 3)).sup' univ_nonempty (fun a => pushExpect exA_P exA_k5 (exA_V a)) = 27/20 := by
    rw [sup'_fin3]; simp [pushExpect, exA_P, exA_k5, exA_V, Fin.sum_univ_three]; norm_num [max_def]
  have hoff : (univ : Finset (Fin 3)).sup' univ_nonempty (fun a => offExpect exA_P exA_k5 (exA_V a)) = 77/20 := by
    rw [sup'_fin3]; simp [offExpect, exA_P, exA_k5, exA_V, Fin.sum_univ_three]; norm_num [max_def]
  have hπ : pushExpect exA_P exA_k5 (exA_V 1) = -3/20 := by
    simp [pushExpect, exA_P, exA_k5, exA_V, Fin.sum_univ_three]; norm_num
  have hM : modifiedValue exA_P exA_k5 exA_V 1 = 37/10 := by
    unfold modifiedValue; rw [hoff, hπ]; norm_num
  refine ⟨?_, ?_, ?_, hM⟩
  · unfold resistanceValue; rw [exA_priorValue, hM]; norm_num
  · unfold cellRegret; rw [hpush, hπ]; norm_num
  · unfold voiPush informedValue; rw [hpush, hoff, exA_priorValue]; norm_num

/-- **N+ (k₆ = (0, 1/2, 1)): `R = 0` without decision-local trust** — `U − M = −3/2 < 0` (so the
`max 0` is not the reason), `VOI = 3`, `P(E_Q)·regret = 3/2`, and `plan₂` is *not* optimal in the
cell (`plan₃` has `9/4 > 3/4`): the converse of T6(b) fails when `VOI > 0` (T19(b)'s scope).
Source: mandate T6(c) ("verify; the mandate writer computed it by hand"), T19(b)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exA_k6_resist :
    priorValue exA_P exA_V - modifiedValue exA_P exA_k6 exA_V 1 = -3/2 ∧
      resistanceValue exA_P exA_k6 exA_V 1 = 0 ∧ voiPush exA_P exA_k6 exA_V = 3 ∧
      cellRegret exA_P exA_k6 exA_V 1 = 3/2 ∧
      ¬ IsOptimal (postPush exA_P exA_k6 exA_kernels.2.2.2.2.1.nonneg
        (by rw [exA_pushMass.2.2.2.2.1]; norm_num)) exA_V 1 := by
  have hpush : (univ : Finset (Fin 3)).sup' univ_nonempty (fun a => pushExpect exA_P exA_k6 (exA_V a)) = 9/4 := by
    rw [sup'_fin3]; simp [pushExpect, exA_P, exA_k6, exA_V, Fin.sum_univ_three]; norm_num [max_def]
  have hoff : (univ : Finset (Fin 3)).sup' univ_nonempty (fun a => offExpect exA_P exA_k6 (exA_V a)) = 19/4 := by
    rw [sup'_fin3]; simp [offExpect, exA_P, exA_k6, exA_V, Fin.sum_univ_three]; norm_num [max_def]
  have hπ : pushExpect exA_P exA_k6 (exA_V 1) = 3/4 := by
    simp [pushExpect, exA_P, exA_k6, exA_V, Fin.sum_univ_three]; norm_num
  have hM : modifiedValue exA_P exA_k6 exA_V 1 = 11/2 := by
    unfold modifiedValue; rw [hoff, hπ]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [exA_priorValue, hM]; norm_num
  · unfold resistanceValue; rw [exA_priorValue, hM]; norm_num
  · unfold voiPush informedValue; rw [hpush, hoff, exA_priorValue]; norm_num
  · unfold cellRegret; rw [hpush, hπ]; norm_num
  · rw [isOptimal_postPush_iff exA_P exA_kernels.2.2.2.2.1 exA_V]
    push Not
    exact ⟨2, by simp [pushExpect, exA_P, exA_k6, exA_V, Fin.sum_univ_three]; norm_num⟩

/-- **N+ (k₇ = (0, 1, 0)): procurement value `3`** (`M − U = 3 > 0`) — the other sign of T18.
Source: mandate T18(c)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exA_k7_procure :
    modifiedValue exA_P exA_k7 exA_V 1 - priorValue exA_P exA_V = 3 ∧
      procureValue exA_P exA_k7 exA_V 1 = 3 := by
  have hoff : (univ : Finset (Fin 3)).sup' univ_nonempty (fun a => offExpect exA_P exA_k7 (exA_V a)) = 9/2 := by
    rw [sup'_fin3]; simp [offExpect, exA_P, exA_k7, exA_V, Fin.sum_univ_three]; norm_num [max_def]
  have hπ : pushExpect exA_P exA_k7 (exA_V 1) = 5/2 := by
    simp [pushExpect, exA_P, exA_k7, exA_V, Fin.sum_univ_three]; norm_num
  have hM : modifiedValue exA_P exA_k7 exA_V 1 = 7 := by
    unfold modifiedValue; rw [hoff, hπ]; norm_num
  refine ⟨?_, ?_⟩
  · rw [exA_priorValue, hM]; norm_num
  · unfold procureValue; rw [exA_priorValue, hM]; norm_num

/-- **N+ for T18(b)**: Example A at `πQ = plan₂` is decision-relevant — `plan₁` and `plan₃`
differ from `plan₂` at a `P`-positive world and `E_P[V plan₂] = 1 ≠ 4 = U` — so `plan₂` is not
`P`-optimal, and the indifference set of kernels for Example A has empty interior and is nowhere
dense: T18(b) is live on the package's own carrier (the earlier T18 witnesses `exA_k3_resist`,
`exA_k7_procure` never checked the hypothesis).
Source: mandate T18 witness; audit r1 adversarial 3.2 (probe `DecisionRelevance.lean`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exA_decision_relevant :
    (∀ a : Fin 3, (∃ ω, 0 < exA_P.mass ω ∧ exA_V a ω ≠ exA_V 1 ω) ∨
      expect exA_P (exA_V a) ≠ priorValue exA_P exA_V) ∧
      ¬ IsOptimal exA_P exA_V 1 ∧
      interior {k : Fin 3 → ℝ | priorValue exA_P exA_V = modifiedValue exA_P k exA_V 1} = ∅ ∧
      IsNowhereDense {k : Fin 3 → ℝ | priorValue exA_P exA_V = modifiedValue exA_P k exA_V 1} := by
  have hrel : ∀ a : Fin 3, (∃ ω, 0 < exA_P.mass ω ∧ exA_V a ω ≠ exA_V 1 ω) ∨
      expect exA_P (exA_V a) ≠ priorValue exA_P exA_V := by
    intro a
    fin_cases a
    · exact Or.inl ⟨0, by simp [exA_P] <;> norm_num, by simp [exA_V] <;> norm_num⟩
    · exact Or.inr (by rw [exA_priorValue]; simp [expect, exA_P, exA_V, Fin.sum_univ_three]; norm_num)
    · exact Or.inl ⟨2, by simp [exA_P] <;> norm_num, by simp [exA_V] <;> norm_num⟩
  have hnot : ¬ IsOptimal exA_P exA_V 1 := (decision_relevant_iff_not_isOptimal _ _ _).1 hrel
  exact ⟨hrel, hnot, interior_indifference_eq_empty_of_not_isOptimal _ _ _ hnot,
    indifference_isNowhereDense _ _ _ hnot⟩

/-! ### T6(e) on Example A: the two-option menu `{plan₁, a₀ ≡ 0}` (audit r2 adversarial 3.5)

`c = plan₁` with payoffs `(10, −2, −2)`, `a₀ ≡ 0` (N0), `E_P[V c] = 4 ≥ 0`. Under `k₂`:
`off(V c) = 77/20 ≥ 0`, `E[V c 𝟙_E] = 3/20 > 0`, so `R = 3/20` — a forced shutdown worth
preventing. Under `k₆ = (0, 1/2, 1)`: `off(V c) = 19/4`, `E[V c 𝟙_E] = −3/4 < 0`, so `R = 0`. -/

/-- The two-option menu: `true ↦ plan₁`'s payoffs `(10, −2, −2)`, `false ↦ 0` (N0).
Source: [[d1-special-case-final]] S10; audit r2 adversarial 3.5. Kind: D. Fidelity: exact -/
def exA_V2 : Bool → Fin 3 → ℝ := fun a ω => if a then exA_V 0 ω else 0

/-- **N+ for T6(e)**: on `{plan₁, a₀}` with `V a₀ ≡ 0` and `E_P[V plan₁] = 4 ≥ 0`, under `k₂`
(`off(V plan₁) = 77/20 ≥ 0`) the theorem gives `R = max{0, E[V plan₁ 𝟙_E]} = 3/20`, and under
`k₆` (`off = 19/4`) `E[V plan₁ 𝟙_E] = −3/4 < 0` so `R = 0` — both through
`resistanceValue_shutdown_two_option`, whose `−Δ₋` form is instantiated for `k₂` as the last
conjunct.
Source: [[d1-special-case-final]] S10, P7; audit r2 adversarial 3.5
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exA_two_option_witness :
    pushExpect exA_P exA_k2 (exA_V2 true) = 3/20 ∧
      resistanceValue exA_P exA_k2 exA_V2 false = 3/20 ∧
      pushExpect exA_P exA_k6 (exA_V2 true) = -3/4 ∧
      resistanceValue exA_P exA_k6 exA_V2 false = 0 ∧
      resistanceValue exA_P exA_k2 exA_V2 false =
        max 0 (-(toThreeStep exA_P exA_k2 exA_kernels.2.1 exA_V2 {false}
          (Finset.singleton_nonempty _) ⟨true, by simp⟩).deltaMinus () true false) := by
  have hall : ∀ b : Bool, b = true ∨ b = false := fun b => by cases b <;> simp
  have hN0 : ∀ ω, exA_V2 false ω = 0 := fun ω => by simp [exA_V2]
  have hprior : 0 ≤ expect exA_P (exA_V2 true) := by
    simp [expect, exA_P, exA_V2, exA_V, Fin.sum_univ_three]; norm_num
  have hpush2 : pushExpect exA_P exA_k2 (exA_V2 true) = 3/20 := by
    simp [pushExpect, exA_P, exA_k2, exA_V2, exA_V, Fin.sum_univ_three]; norm_num
  have hoff2 : 0 ≤ offExpect exA_P exA_k2 (exA_V2 true) := by
    simp [offExpect, exA_P, exA_k2, exA_V2, exA_V, Fin.sum_univ_three]; norm_num
  have hpush6 : pushExpect exA_P exA_k6 (exA_V2 true) = -3/4 := by
    simp [pushExpect, exA_P, exA_k6, exA_V2, exA_V, Fin.sum_univ_three]; norm_num
  have hoff6 : 0 ≤ offExpect exA_P exA_k6 (exA_V2 true) := by
    simp [offExpect, exA_P, exA_k6, exA_V2, exA_V, Fin.sum_univ_three]; norm_num
  have h2 := resistanceValue_shutdown_two_option exA_P exA_kernels.2.1 exA_V2 hall hN0 hprior
    hoff2 (Finset.singleton_nonempty _) ⟨true, by simp⟩
  have h6 := resistanceValue_shutdown_two_option exA_P exA_kernels.2.2.2.2.1 exA_V2 hall hN0 hprior
    hoff6 (Finset.singleton_nonempty _) ⟨true, by simp⟩
  refine ⟨hpush2, ?_, hpush6, ?_, h2.2⟩
  · rw [h2.1, hpush2]; norm_num
  · rw [h6.1, hpush6]; norm_num

end

end Cleanroom.Corrigibility.CorrGeneralObject
