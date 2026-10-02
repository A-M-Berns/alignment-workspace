import Cleanroom.Bli.UdtBliSist.SistWitness

/-!
# `udt-bli-sist` · Crux: one-step = two-step = `N`-step under the independence hypotheses (T5, U8)

**The crux theorem** (bli-soto-b-2-008's precise finite form, `oneStep_iff_twoStep`): for a finite
set `Σ` of small sentences and an observed table `Q`, under `ReflectiveAt P Q` (no action at `Q`
moves a branch weight), `ClassInert P (sigmaClass Σ Q) Q` (the tables disagreeing with `Q` on `Σ`
are inert) and positivity of the `Σ`-class under every action, an action is a one-step choice at
`Q` iff it is a two-step choice with `σ(Σ, Q)` added to the conditional. The engine is the exact
identity `EU Q a − EU Q b = classProb (Σ-class) Q a · (twoStepEU Σ Q a − twoStepEU Σ Q b)`
(`EU_sub_eq_twoStep`): the class-cut plus `classProb · classEU = ∑ branchProb · condEU`. **The
hypotheses are the independence assumptions; nothing equates the two values.**

**`N`-step** (`oneStep_iff_nStep`): for any family `Σ_k` each satisfying the hypotheses, every
level's rule has the maximizer set of the one-step rule, hence all levels agree. The chain
condition `Σ₁ ⊆ … ⊆ Σ_N` of the source plays no role in the finite statement (finding F9).

**The N−** (`Mugging.crux_fails_on_coin`): the mugging with `Σ = {coin}` — the `Σ`-class of `Ask`
is `{Ask}`, the two-step rule is the updateful rule and refuses, the one-step rule pays, and
`ClassInert` fails: "`P` would not endorse updating on the coin" is exactly the failed hypothesis.

**The two senses** (bli-soto-b-2-009): `IndGood` (the independence sense: the hypotheses of the
crux at `Q`) and `EVGood` (the expected-utility sense: every two-step policy ex-ante dominates
every one-step policy). `twoStepPolicy_iff_oneStepPolicy` under `IndGood` everywhere;
`evGood_of_indGood_tieFree`: with unique maximizers the two senses agree. The converse direction
and the tied case are recorded as open questions in the findings, not as `sorry`s.

**FIST, abstract** (`partitionCut`): the class-cut over any intermediate coordinate `β : Ω → B`
with a distinguished set `𝒳` of its values — the LTP route of bli-soto-a-079 with `𝒳` the values
reached from an `X`-table; Soto's objection (the hypotheses are about `P`'s conditionals and nothing
in the theorem produces them) is a finding, not a refutation.

Sources: bli-soto-b-2-008, bli-soto-b-2-009, bli-soto-b-2-010, bli-soto-a-079, bli-soto-a-080,
bli-soto-b-048, mandate T5.
-/

namespace Cleanroom.Bli.UdtBliSist

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

section Crux

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A]
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A) (Sig : Finset ↥(𝒮.S m)) (Q : ↥𝒟)

/-- **Positivity of the `Σ`-class under an action**: `0 < μ(pp·Q = a ∧ σ(Σ, Q))` — the honest
scope of `twoStepEU`.
Source: mandate T5(a) ("positivity of the `Σ`-class under each action")
Kind: D
Fidelity: exact -/
def SigmaClassPos (a : A) : Prop :=
  0 < massOf P.μ (fun ω => P.pp ω Q = a ∧ agreesOn Sig Q (P.state ω))

/-- A positive `Σ`-class has positive class weight.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma classProb_sigma_pos (a : A) (h : SigmaClassPos P Sig Q a) :
    0 < classProb P (sigmaClass Sig Q) Q a := by
  have hm : 0 < massOf P.μ (fun ω => P.pp ω Q = a ∧ P.state ω ∈ sigmaClass Sig Q) := by
    unfold SigmaClassPos at h
    rw [massOf_congr P.μ (fun ω => by rw [mem_sigmaClass_iff])]
    exact h
  rw [massOf_class] at hm
  have hpp : 0 < P.ppMass Q a := by
    rw [P.ppMass_eq_sum_jointMass Q a]
    exact lt_of_lt_of_le hm (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun T _ _ => P.jointMass_nonneg T Q a))
  have := classProb_mul_ppMass P (sigmaClass Sig Q) Q a
  rw [← this] at hm
  exact pos_of_mul_pos_left hm (le_of_lt hpp)

/-- **The one-step/two-step identity** under the independence hypotheses:
`EU Q a − EU Q b = classProb (Σ-class) Q a · (twoStepEU Σ Q a − twoStepEU Σ Q b)`.
Source: bli-soto-b-2-008 (the crux, finite form); mandate T5(a)
Kind: C (`classCut_of` + `classProb_mul_classEU`, with the class weight action-invariant)
Fidelity: exact
Hyps: (a) `ReflectiveAt`, `ClassInert` at the `Σ`-class; does not use faith -/
theorem EU_sub_eq_twoStep (hR : ReflectiveAt P Q) (hI : ClassInert P (sigmaClass Sig Q) Q)
    (a b : A) :
    P.EU Q a - P.EU Q b =
      classProb P (sigmaClass Sig Q) Q a * (twoStepEU P Sig Q a - twoStepEU P Sig Q b) := by
  rw [classCut_of P _ Q hR hI a b, twoStepEU_eq_classEU, twoStepEU_eq_classEU]
  have hcp : classProb P (sigmaClass Sig Q) Q a = classProb P (sigmaClass Sig Q) Q b := by
    unfold classProb
    apply Finset.sum_congr rfl
    intro T _
    exact hR T a b
  rw [mul_sub, classProb_mul_classEU, hcp, classProb_mul_classEU, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro T _
  rw [hR T a b]
  ring

/-- **The crux theorem** (load-bearing 4): under `ReflectiveAt P Q`, `ClassInert P (Σ-class) Q` and
positivity of the `Σ`-class under every action, **an action is a one-step choice at `Q` iff it is a
two-step choice** — "any further updatefulness which `P` would endorse via the two-step procedure
is already rolled into the one-step procedure" (Abram), as an equality of maximizer sets.
Source: bli-soto-b-2-008 (Abram's crux conjecture, finite form); bli-soto-a-080 (Conjecture A);
mandate T5(a)
Kind: C
Fidelity: exact (sets of maximizers, ties allowed; `Σ` finite — the "boundedly knowable" class is
fixed as a finite set of day-`m` sentences, finding F9)
Hyps: (a) `ReflectiveAt`, `ClassInert`, `SigmaClassPos` for every action; does not use faith -/
theorem oneStep_iff_twoStep (hR : ReflectiveAt P Q) (hI : ClassInert P (sigmaClass Sig Q) Q)
    (hpos : ∀ a, SigmaClassPos P Sig Q a) (a : A) :
    P.IsOneStepChoice Q a ↔ IsTwoStepChoice P Sig Q a := by
  unfold FiniteBLIPrior.IsOneStepChoice IsTwoStepChoice
  apply forall_congr'
  intro b
  rw [← sub_nonneg, EU_sub_eq_twoStep P Sig Q hR hI a b,
    mul_nonneg_iff_of_pos_left (classProb_sigma_pos P Sig Q a (hpos a)), sub_nonneg]

/-- **`N`-step**: for any family of sentence sets `Σ_k` each satisfying the crux hypotheses at `Q`,
every level's rule has the maximizer set of the one-step rule, so all levels agree — the `N`-step
regress collapses level by level. The chain condition of the source is not needed (finding F9).
Source: bli-soto-b-2-010 (iii) (one-step = `N`-step on a finite tree); mandate T5(b)
Kind: C
Fidelity: variant: the `N`-step rule is rendered as the two-step rule at the `k`-th sentence set
(the source's `N`-step is via programs, PDF 19 Appendix E — finding F9)
Hyps: (a) as `oneStep_iff_twoStep` at each level; does not use faith -/
theorem oneStep_iff_nStep {N : ℕ} (Sigs : Fin N → Finset ↥(𝒮.S m)) (hR : ReflectiveAt P Q)
    (hI : ∀ k, ClassInert P (sigmaClass (Sigs k) Q) Q)
    (hpos : ∀ k a, SigmaClassPos P (Sigs k) Q a) (a : A) :
    (∀ k, P.IsOneStepChoice Q a ↔ IsTwoStepChoice P (Sigs k) Q a) ∧
      ∀ k l, IsTwoStepChoice P (Sigs k) Q a ↔ IsTwoStepChoice P (Sigs l) Q a := by
  have h : ∀ k, P.IsOneStepChoice Q a ↔ IsTwoStepChoice P (Sigs k) Q a :=
    fun k => oneStep_iff_twoStep P (Sigs k) Q hR (hI k) (hpos k) a
  exact ⟨h, fun k l => (h k).symm.trans (h l)⟩

/-! ## The two senses of "good to update on" (bli-soto-b-2-009) -/

/-- **The independence sense**: `Σ` is good to update on at `Q` iff the crux hypotheses hold
there — `ReflectiveAt P Q ∧ ClassInert P (Σ-class) Q`. A meta-property of `P`'s conditionals; no
sentence expresses it (bli-soto-b-2-009 (i)).
Source: bli-soto-b-2-009 (Ind); bli-soto-a-071 (`C(n,m)`)
Kind: D
Fidelity: exact -/
def IndGood : Prop := ReflectiveAt P Q ∧ ClassInert P (sigmaClass Sig Q) Q

/-- A **two-step policy**: pointwise a two-step choice with `Σ`.
Source: bli-soto-b-023 (`Policy(Σ, Q)`); mandate T5(d)
Kind: D
Fidelity: exact -/
def IsTwoStepPolicy (π : Policy 𝒟 A) : Prop := ∀ T, IsTwoStepChoice P Sig T (π T)

/-- **The expected-utility sense**: `Σ` is good to update on iff every two-step policy ex-ante
dominates every one-step policy, `exAnteValue π₁ ≤ exAnteValue π₂` (both policies as predicates;
with ties this compares every selection — see the findings).
Source: bli-soto-b-2-009 (EV) ("`P` believes the policy 'follow `P` but update on `X`' has
higher expected `U` than 'follow `P`'"); mandate T5(d)
Kind: D
Fidelity: variant: the junk-free form compares positive-mass policies only (disclosed) -/
def EVGood : Prop :=
  ∀ π₁ π₂ : Policy 𝒟 A, P.IsOneStepPolicy π₁ → IsTwoStepPolicy P Sig π₂ →
    0 < P.policyMass π₁ → 0 < P.policyMass π₂ → P.exAnteValue π₁ ≤ P.exAnteValue π₂

/-- **Under `IndGood` at every table (with positivity), the two-step policies are the one-step
policies.**
Source: bli-soto-b-2-008; mandate T5(d)
Kind: C
Fidelity: exact
Hyps: (a) `IndGood` and `SigmaClassPos` at every table and action; does not use faith -/
theorem twoStepPolicy_iff_oneStepPolicy (hind : ∀ T, IndGood P Sig T)
    (hpos : ∀ T a, SigmaClassPos P Sig T a) (π : Policy 𝒟 A) :
    IsTwoStepPolicy P Sig π ↔ P.IsOneStepPolicy π := by
  unfold IsTwoStepPolicy FiniteBLIPrior.IsOneStepPolicy
  apply forall_congr'
  intro T
  exact (oneStep_iff_twoStep P Sig T (hind T).1 (hind T).2 (hpos T) (π T)).symm

/-- **`IndGood` everywhere implies `EVGood` when the one-step maximizer is unique at every table**:
then the one-step and two-step policies are the same single policy, and the comparison is an
equality.
Source: bli-soto-b-2-009 (the relation between the two senses); mandate T5(d) (`stretch`)
Kind: C
Fidelity: exact (the tie-free case; the tied case is an open question, findings)
Hyps: (a) `IndGood`, positivity, uniqueness of the one-step choice at every table; does not use faith -/
theorem evGood_of_indGood_tieFree (hind : ∀ T, IndGood P Sig T)
    (hpos : ∀ T a, SigmaClassPos P Sig T a)
    (huniq : ∀ T a b, P.IsOneStepChoice T a → P.IsOneStepChoice T b → a = b) :
    EVGood P Sig := by
  intro π₁ π₂ h₁ h₂ _ _
  have h₂' : P.IsOneStepPolicy π₂ := (twoStepPolicy_iff_oneStepPolicy P Sig hind hpos π₂).mp h₂
  have : π₁ = π₂ := funext (fun T => huniq T _ _ (h₁ T) (h₂' T))
  rw [this]

end Crux

/-! ## The N−: the mugging with `Σ = {coin}` -/

namespace Mugging

open Cleanroom.Bli.UdtBliCore.Mugging Sist3

variable (r : Bool → ℚ)

/-- The `{coin}`-class of `Ask` on the mugging's tables is `{Ask}`.
Source: mandate T5(c)
Kind: L
Fidelity: exact -/
lemma sigmaClass_coin : sigmaClass ({coin} : Finset ↥(witIndex.S 1)) askT = {askT} := by
  ext T
  rw [mem_sigmaClass_iff, Finset.mem_singleton]
  unfold agreesOn
  constructor
  · intro h
    have := h coin (Finset.mem_singleton_self _)
    have hask : askP T := by
      unfold askP; rw [this]; simp [mAsk]
    exact (askP_iff T).mp hask
  · intro h; subst h; intro φ _; rfl

/-- **The two-step value with `Σ = {coin}` at `Ask` is the updateful value** (the class is `{Ask}`).
Source: mandate T5(c) ("two-step = updateful refuses")
Kind: L
Fidelity: exact -/
lemma twoStepEU_coin (a : Bool) :
    twoStepEU (muggingPrior r) {coin} askT a = (muggingPrior r).homeEU askT a := by
  rw [twoStepEU_eq_classEU, sigmaClass_coin]
  unfold classEU FiniteBLIPrior.homeEU FiniteBLIPrior.condEU
  apply condExp_congr
  intro ω
  rw [Finset.mem_singleton]
  exact and_comm

/-- **The crux fails on the mugging with `Σ = {coin}`**: the two-step rule (= the updateful rule)
refuses, the one-step rule pays, so the maximizer sets differ; and `ClassInert {Ask} Ask` fails —
the hypothesis the crux needs is exactly "`P` endorses updating on the coin", which the mugging
prior does not (the Rec branch cares about the Ask point). Also `ReflectiveAt Ask` holds, so the
failure is the inertness clause alone.
Source: bli-soto-b-2-009 (Ind) ("`P` would not endorse updating on the coin"); mandate T5(c)
Kind: N−
Fidelity: exact
Hyps: (a) `|r| ≤ 10`; does not use faith -/
theorem crux_fails_on_coin (hr : ∀ a, |r a| ≤ 10) :
    IsTwoStepChoice (muggingPrior r) {coin} askT false ∧
      ¬ IsTwoStepChoice (muggingPrior r) {coin} askT true ∧
      (muggingPrior r).IsOneStepChoice askT true ∧
      ¬ (muggingPrior r).IsOneStepChoice askT false ∧
      ¬ ClassInert (muggingPrior r) (sigmaClass {coin} askT) askT ∧
      ReflectiveAt (muggingPrior r) askT := by
  refine ⟨?_, ?_, isOneStepChoice_ask_pay r hr, not_isOneStepChoice_ask_refuse r hr, ?_,
    reflectiveAt_ask r⟩
  · intro b
    rw [twoStepEU_coin, twoStepEU_coin]
    exact isUpdatefulChoice_ask_refuse r b
  · intro h
    have := h false
    rw [twoStepEU_coin, twoStepEU_coin] at this
    exact not_isUpdatefulChoice_ask_pay r (fun b => by
      cases b
      · exact this
      · exact le_rfl)
  · rw [sigmaClass_coin]
    exact not_classInert_ask r

end Mugging

/-! ## FIST, abstract: the partition cut over an intermediate coordinate -/

section Fist

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A]
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A) {B : Type} [Fintype B] [DecidableEq B] (β : P.Ω → B)

/-- The weight of the fiber `β = x` under the point `pp·Q = a`: `μ(β = x | pp·Q = a)`.
Source: bli-soto-a-079 (`P(Q_c = Q̂_c | A(Q̂) = a)`); mandate T5(e)
Kind: D
Fidelity: exact -/
def fiberW (Q : ↥𝒟) (a : A) (x : B) : ℚ :=
  massOf P.μ (fun ω => P.pp ω Q = a ∧ β ω = x) / P.ppMass Q a

/-- The value of the fiber `β = x` under the point: `𝔼[U | pp·Q = a ∧ β = x]`.
Source: bli-soto-a-079 (`E(U | A(Q̂) = a ∧ Q_c = Q̂_c)`)
Kind: D
Fidelity: exact -/
def fiberV (Q : ↥𝒟) (a : A) (x : B) : ℚ :=
  condExp P.μ P.U (fun ω => P.pp ω Q = a ∧ β ω = x)

/-- **The partition cut** (FIST's LTP route, abstract): over any intermediate coordinate `β`, if
no action at `Q` moves any fiber weight and the fibers outside `𝒳` have action-invariant values on
positive cells, then `EU Q a − EU Q b = ∑_{x ∈ 𝒳} μ(β = x | pp·Q = a) · (fiberV a x − fiberV b x)`.
With `β = state` and `𝒳 = 𝒞` it is the class-cut; with `β` the day-`c` table and `𝒳` the tables
believing `X(node)` it is bli-soto-a-079's "branch probabilities from `extrapolate(Q_c)`". The
hypotheses are about `P`'s conditionals at the intermediate coordinate — nothing in the theorem
produces them (Soto's objection, bli-soto-b-048, recorded as finding F11).
Source: bli-soto-a-079 ("precise route": the LTP over `Q_c`, independence makes the weights
constant in `a`); bli-soto-b-048; mandate T5(e)
Kind: C (`EU_eq_sum_partition` twice, the off-`𝒳` terms killed with the junk cases)
Fidelity: exact
Hyps: (a) none; does not use faith -/
theorem partitionCut (𝒳 : Finset B) (Q : ↥𝒟) (a b : A)
    (hw : ∀ x, fiberW P β Q a x = fiberW P β Q b x)
    (hv : ∀ x ∉ 𝒳, 0 < massOf P.μ (fun ω => P.pp ω Q = a ∧ β ω = x) →
      0 < massOf P.μ (fun ω => P.pp ω Q = b ∧ β ω = x) → fiberV P β Q a x = fiberV P β Q b x) :
    P.EU Q a - P.EU Q b = ∑ x ∈ 𝒳, fiberW P β Q a x * (fiberV P β Q a x - fiberV P β Q b x) := by
  rw [P.EU_eq_sum_partition β Q a, P.EU_eq_sum_partition β Q b]
  change (∑ x, fiberW P β Q a x * fiberV P β Q a x) - (∑ x, fiberW P β Q b x * fiberV P β Q b x) = _
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_sum_compl 𝒳]
  have hoff : ∑ x ∈ 𝒳ᶜ, (fiberW P β Q a x * fiberV P β Q a x -
      fiberW P β Q b x * fiberV P β Q b x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hx' : x ∉ 𝒳 := Finset.mem_compl.mp hx
    by_cases ha : 0 < massOf P.μ (fun ω => P.pp ω Q = a ∧ β ω = x)
    · by_cases hb : 0 < massOf P.μ (fun ω => P.pp ω Q = b ∧ β ω = x)
      · rw [hv x hx' ha hb, hw x, sub_self]
      · have hzb : massOf P.μ (fun ω => P.pp ω Q = b ∧ β ω = x) = 0 :=
          le_antisymm (not_lt.mp hb) (massOf_nonneg _ P.μ_nonneg _)
        have hwb : fiberW P β Q b x = 0 := by unfold fiberW; rw [hzb, zero_div]
        rw [hw x, hwb, zero_mul, zero_mul, sub_self]
    · have hza : massOf P.μ (fun ω => P.pp ω Q = a ∧ β ω = x) = 0 :=
        le_antisymm (not_lt.mp ha) (massOf_nonneg _ P.μ_nonneg _)
      have hwa : fiberW P β Q a x = 0 := by unfold fiberW; rw [hza, zero_div]
      rw [← hw x, hwa, zero_mul, zero_mul, sub_self]
  rw [hoff, add_zero]
  apply Finset.sum_congr rfl
  intro x _
  rw [hw x]
  ring

end Fist

end Cleanroom.Bli.UdtBliSist
