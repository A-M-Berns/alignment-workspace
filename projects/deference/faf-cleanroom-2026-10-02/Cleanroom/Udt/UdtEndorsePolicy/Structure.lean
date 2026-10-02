import Cleanroom.Udt.UdtCommTrust.Determination
import Cleanroom.Udt.UdtCommTrust.Count
import Cleanroom.Udt.UdtEndorsePolicy.Defs
import Cleanroom.Udt.UdtEndorsePolicy.Transitive
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# T4: control endorsement and the UDT rule over decision structures; support collapse

Sources: [[agency-via-endorsement]] §Control Endorsement, §The UDT Connection, §Summary (the
corpus's condensation gloss — the AI's, ATTRIBUTION-UNVETTED); [[cleanup-audit-2026-08-05]] item 1;
udt-rep-050/051.

Over `udt-comm-trust`'s `AbstractDS`, the observer's value of a realized external policy `π̈` is
`policyUtility π̈ = E[U | Π̈ = π̈]` (junk `−1` off the range).

* `PolicyEndorsed S` (D): every realized external policy is optimal among realized external
  policies — the corpus's "full control endorsement: every policy in the support is optimal",
  stated directly over `E[U | Π̈ = π]`. The corpus's route to this form ("`Π` is independent of
  `(B, Ξ)` in support, so conditioning on `Π = π` doesn't change the distribution of `(B, Ξ)`")
  is invalid as written (udt-rep-050) and is **not** reproduced; its `Π` (the residual of `A`
  given `E`) is not `Π̈`.
* `polE_const_of_strictArgmax` (L, T4(b), support collapse): under `PolicyEndorsed`, a strict
  argmax among realized policies is the only realized policy. "`H(Π) = 0`" is "`polE` constant";
  no entropy here (the package is FAF-free).
* T4(c): the pointwise `UdtRule` and `PolicyEndorsed` are incomparable **on `AbstractDS` as
  given**, and the reason is instructive: `CB8` (Coordinated Buttons with prior weights
  `3, 3, 3, 1` on the four policies) satisfies the pointwise rule by ties and is not policy
  endorsed; `IA4` is policy endorsed (two realized external policies of equal utility) and fails
  the pointwise rule through the *internal* action, which the external policy utility does not
  see. `udtRule_of_policyEndorsed` (P) shows that with a constant internal action and
  `Π* = (ȧ₀, Π̈)`, policy endorsement *does* imply the pointwise rule — so the second separation
  lives entirely in the internal action.
* The corpus's "an agent following UDT is control-endorsed by its own prior" is, for the
  policy-level rule, the restatement `policyEndorsed_iff_isOptimal_on_range` (T: optimality
  *among realized policies* — `AbstractDS` has no utility for an unrealized policy, so no
  all-policies UDT1.1 rule is formalized here) — and false for the pointwise rule (`CB8`).

**Repair round 1** (audit r1). Neither `CB8` nor `IA4` is `udt-comm-trust`'s `DecisionDetermined`
(`CB8.not_decisionDetermined`, `IA4.not_decisionDetermined`: in each, two worlds share
`E = (Ä, D_E)` and differ in `U`), so the pointwise refutation lives outside the regime in which
the corpus's UDT theorem is stated. The natural next question — does the pointwise rule force
equal policy utilities on decision-determined, external-only structures? — is answered **yes**
whenever the policy utility is additively separable across inputs, `E[U | Π̈ = π] = ∑_ö X(ö, π ö)`
(which is what decision-determination gives in the Coordinated-Buttons pattern when the input is
independent of the policy): `policyEndorsed_of_udtRule_of_separable` (P), by the covariance
identity `Var(f) = ∑_ö Cov(f, X_ö)` with each covariance killed by the rule's forced ties
(`score_eq_of_udtRule`). So on that regime the two rules are *equivalent*
(`udtRule_of_policyEndorsed` is the other direction), and `CB8` escapes exactly because its
policy utility is the non-separable Coordinated-Buttons table. `CB8X` (from the adversarial
probe) inhabits `udtRule_of_policyEndorsed`'s full hypothesis package with four distinct realized
policies and a utility that depends on the policy, and is the honest T4(d) witness. `CBD4` is the
decision-determined instance of the equivalence: two anti-coordinated policies, `U = [Ä = 1]`,
policy utility separable with the action-dependent table `½·[ä = 1]`, the rule holding by the
forced tie, policy endorsement holding as the theorem says (`CBD4.separable_dd_witness`,
`CBD4.decisionDetermined` by the count identity).
-/

namespace Cleanroom.Udt.UdtEndorsePolicy

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

noncomputable section

/-- Supporting lemma: a sum over an event as an `if`-sum over the carrier (witness toolkit).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_event_eq {Ω : Type} [Fintype Ω] (g : Ω → ℝ) (P : Ω → Prop) [DecidablePred P] :
    ∑ ω ∈ event P, g ω = ∑ ω, if P ω then g ω else 0 := by
  rw [event, Finset.sum_filter]

/-- **Constant conditional means along every coordinate force a separable function to be constant
on the support** (the covariance identity, finite form): if `f ω = ∑ e, X e (Π ω e)` and, for each
coordinate `e`, the conditional mean `E[f | Π(·)(e) = a]` is the same for every realized `a`, then
`f` is constant on `{w > 0}`. Proof: with `c` the global mean, `∑ w (f − c)² = ∑_e ∑ w · X_e · (f − c)`
and each coordinate's sum vanishes class by class (on `{Π(·)(e) = a}` the factor `X e a` is
constant and `∑ w (f − c) = 0` there), so every positive-weight point has `f = c`.
Source: audit r1 fidelity N1 (does the pointwise rule force equal policy utilities?); infrastructure for `policyEndorsed_of_udtRule_of_separable`
Kind: P
Fidelity: n/a
Hyps: (a) all -/
theorem eq_on_support_of_condMean_const {Ω E A : Type} [Fintype Ω] [Fintype E] [DecidableEq A]
    {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (pol : Ω → E → A) (X : E → A → ℝ) {f : Ω → ℝ}
    (hf : ∀ ω, f ω = ∑ e, X e (pol ω e))
    (h : ∀ e ω ω', 0 < w ω → 0 < w ω' →
      wsum w f (cls (fun ω => pol ω e) (pol ω e)) / mass w (cls (fun ω => pol ω e) (pol ω e)) =
        wsum w f (cls (fun ω => pol ω e) (pol ω' e)) / mass w (cls (fun ω => pol ω e) (pol ω' e))) :
    ∀ ω ω', 0 < w ω → 0 < w ω' → f ω = f ω' := by
  intro ω₀ ω₁ h₀ h₁
  have hm : 0 < mass w univ := mass_pos_of_mem hw (mem_univ ω₀) h₀
  set c := wsum w f univ / mass w univ with hc
  -- on every positive class of every coordinate, the conditional mean is the global mean `c`
  have hcls : ∀ e ω, 0 < w ω →
      wsum w f (cls (fun ω => pol ω e) (pol ω e)) = c * mass w (cls (fun ω => pol ω e) (pol ω e)) := by
    intro e ω hω
    set d := wsum w f (cls (fun ω => pol ω e) (pol ω₀ e)) / mass w (cls (fun ω => pol ω e) (pol ω₀ e))
      with hd
    have hdall : ∀ ω', 0 < w ω' →
        wsum w f (cls (fun ω => pol ω e) (pol ω' e)) = d * mass w (cls (fun ω => pol ω e) (pol ω' e)) := by
      intro ω' hω'
      have hpos := mass_cls_pos hw (fun ω => pol ω e) hω'
      rw [hd, ← h e ω' ω₀ hω' h₀, div_mul_cancel₀ _ hpos.ne']
    have htot : wsum w f univ = d * mass w univ := by
      rw [← wsum_const_on (w := w) (f := fun _ => d) (E := univ) (fun _ _ => rfl)]
      refine wsum_eq_of_fibres hw f (fun _ => d) univ (fun ω => pol ω e) fun x hx => ?_
      obtain ⟨ω', hω'mem, hω'⟩ := exists_pos_of_mass_pos hw hx
      have hx' : pol ω' e = x := by simpa using hω'mem
      subst hx'
      rw [wsum_const_on (f := fun _ => d) (fun _ _ => rfl)]
      exact hdall ω' hω'
    have hdc : d = c := by
      rw [hc, htot, mul_div_cancel_right₀ _ hm.ne']
    rw [← hdc]
    exact hdall ω hω
  -- the deviations from `c` sum to zero
  have hdev : wsum w (fun ω => f ω - c) univ = 0 := by
    have : wsum w (fun ω => f ω - c) univ = wsum w f univ - c * mass w univ := by
      simp only [wsum, mass, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun ω _ => by ring
    rw [this, hc, div_mul_cancel₀ _ hm.ne', sub_self]
  -- each coordinate's covariance term vanishes
  have hcoord : ∀ e, wsum w (fun ω => X e (pol ω e) * (f ω - c)) univ = 0 := by
    intro e
    have h0 : wsum w (fun _ => (0 : ℝ)) univ = 0 := by simp [wsum]
    rw [← h0]
    refine wsum_eq_of_fibres hw _ _ univ (fun ω => pol ω e) fun x hx => ?_
    obtain ⟨ω', hω'mem, hω'⟩ := exists_pos_of_mass_pos hw hx
    have hx' : pol ω' e = x := by simpa using hω'mem
    subst hx'
    have hconst : wsum w (fun ω => X e (pol ω e) * (f ω - c)) (univ.filter fun ω => pol ω e = pol ω' e) =
        X e (pol ω' e) * wsum w (fun ω => f ω - c) (univ.filter fun ω => pol ω e = pol ω' e) := by
      simp only [wsum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω hω => ?_
      rw [(Finset.mem_filter.1 hω).2]
      ring
    have hsub : wsum w (fun ω => f ω - c) (univ.filter fun ω => pol ω e = pol ω' e) =
        wsum w f (univ.filter fun ω => pol ω e = pol ω' e) -
          c * mass w (univ.filter fun ω => pol ω e = pol ω' e) := by
      simp only [wsum, mass, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun ω _ => by ring
    have hev : (univ.filter fun ω => pol ω e = pol ω' e) = cls (fun ω => pol ω e) (pol ω' e) := rfl
    rw [hconst, hsub, hev, hcls e ω' hω', sub_self, mul_zero]
    simp [wsum]
  -- so the weighted sum of squared deviations vanishes, and `f = c` on the support
  have hsq : wsum w (fun ω => (f ω - c) ^ 2) univ = 0 := by
    have e1 : wsum w (fun ω => (f ω - c) ^ 2) univ =
        wsum w (fun ω => f ω * (f ω - c)) univ - c * wsum w (fun ω => f ω - c) univ := by
      simp only [wsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun ω _ => by ring
    have e2 : wsum w (fun ω => f ω * (f ω - c)) univ =
        ∑ e, wsum w (fun ω => X e (pol ω e) * (f ω - c)) univ := by
      simp only [wsum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [← Finset.mul_sum, ← Finset.sum_mul, ← hf ω]
    rw [e1, e2, hdev, mul_zero, sub_zero]
    exact Finset.sum_eq_zero fun e _ => hcoord e
  have hz := eq_zero_on_support_of_wsum_sq_eq_zero hw hsq
  have hz₀ : f ω₀ - c = 0 := hz ω₀ h₀
  have hz₁ : f ω₁ - c = 0 := hz ω₁ h₁
  linarith

section General

variable {Ω OI OE AI AE DI DE DB OH OC : Type}
variable [Fintype Ω] [DecidableEq Ω] [Fintype OE] [DecidableEq OE] [DecidableEq AE]
variable (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC)

/-- **Policy endorsement of a decision structure** (the corpus's "full control endorsement: every
policy in the support is optimal"): every realized external policy has policy utility at least
that of every other realized external policy. Stated directly over `policyUtility π = E[U | Π̈ = π]`
on realized policies; the corpus's independence route to this form is not reproduced.
Source: [[agency-via-endorsement]] §Control Endorsement, §Summary ("every policy in the support is optimal") | udt-rep-050
Kind: D
Fidelity: variant: over `udt-comm-trust`'s `Π̈` and realized policies; the corpus's `Π` is a different variable (ATTRIBUTION-UNVETTED that this is the intended object)
Scope: finite support (`AbstractDS`); FAF-free
Hyps: n/a -/
def PolicyEndorsed : Prop :=
  ∀ ω ω', S.policyUtility (S.polE ω') ≤ S.policyUtility (S.polE ω)

omit [DecidableEq Ω] [DecidableEq OE] in
/-- **Policy endorsement is `IsOptimal` on the range of `Π̈`** (T): the corpus's "an agent
following UDT is control-endorsed by its own prior" is this restatement *if* "following UDT" is
read as "every realized policy is an optimum among the realized policies" — which is the
definition of `PolicyEndorsed`. No all-policies (UDT1.1) rule is formalized: `AbstractDS` has no
utility for an unrealized policy (`policyUtility` is the junk `−1` off the range), so the
corpus's `argmax_f E[U(f(B), B, Ξ)]` over *all* `f` is not an object here (audit r1 N3).
Source: [[agency-via-endorsement]] §The UDT Connection ("Claim: An agent following UDT is control-endorsed by its own prior") | udt-rep-050
Kind: T
Fidelity: variant: optimality among realized policies only; the pointwise reading is refuted by `CB8`
Hyps: (a) none -/
theorem policyEndorsed_iff_isOptimal_on_range :
    PolicyEndorsed S ↔ ∀ ω, ∀ π ∈ Set.range S.polE, S.policyUtility π ≤ S.policyUtility (S.polE ω) := by
  constructor
  · rintro h ω π ⟨ω', rfl⟩
    exact h ω ω'
  · intro h ω ω'
    exact h ω _ ⟨ω', rfl⟩

omit [DecidableEq Ω] [DecidableEq OE] in
/-- **T4(b), support collapse** (udt-rep-051): under policy endorsement, a realized policy `π₀`
that is a strict argmax among realized policies is the *only* realized policy — `Π̈` is constant
(the audit's "`H(Π) = 0`", entropy-free).
Source: [[cleanup-audit-2026-08-05]] item 1 ("full control endorsement forces `H(Π)=0` if the argmax is unique") | udt-rep-051
Kind: L
Fidelity: variant: "`H(Π) = 0`" rendered as constancy of `Π̈`; no entropy
Hyps: (a) all -/
theorem polE_const_of_strictArgmax (h : PolicyEndorsed S) {π₀ : OE → AE}
    (hreal : ∃ ω₀, S.polE ω₀ = π₀)
    (hstrict : ∀ ω, S.polE ω ≠ π₀ → S.policyUtility (S.polE ω) < S.policyUtility π₀) :
    ∀ ω, S.polE ω = π₀ := by
  intro ω
  by_contra hne
  obtain ⟨ω₀, hω₀⟩ := hreal
  have h1 := hstrict ω hne
  have h2 := h ω ω₀
  rw [hω₀] at h2
  exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)

omit [DecidableEq Ω] [DecidableEq OE] in
/-- Supporting lemma: on the support, a non-empty policy event has positive mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_evPolE_pos (ω : Ω) : 0 < mass S.μ.w (S.evPolE (S.polE ω)) :=
  mass_pos_of_nonempty S.pos ⟨ω, by simp [AbstractDS.evPolE]⟩

omit [DecidableEq Ω] [DecidableEq OE] in
/-- Supporting lemma: the sum of `w · U` over a realized policy event is `policyUtility · mass`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_evPolE_eq (ω : Ω) :
    ∑ ω' ∈ S.evPolE (S.polE ω), S.μ.w ω' * S.U ω' =
      S.policyUtility (S.polE ω) * mass S.μ.w (S.evPolE (S.polE ω)) := by
  unfold AbstractDS.policyUtility
  rw [condExpJunk_of_pos (mass_evPolE_pos S ω), div_mul_cancel₀ _ (mass_evPolE_pos S ω).ne']

/-- **Policy endorsement implies the pointwise UDT rule when the chosen policy is external-only**
(P): if `Π*(ȯ, ö) = (ȧ₀, Π̈(ö))` with a constant internal action, then under `PolicyEndorsed` every
realized action at every input is an argmax of the score. The event `{Π*(ȯ, ö) = (ȧ₀, ä)}` is the
union of the realized policy events `{Π̈ = π}` with `π ö = ä`, each with conditional utility equal
to the common maximum `c`, so its score is `c`; an unrealized action scores the junk `−1 < 0 ≤ c`.
Hence the second separation of T4(c) must run through the internal action (`IA4`), and the two
notions are comparable one way on external-only structures. The shape of the implication is
*universal ties*: the proof shows every realized action at every input scores the common `c`, so
on an external-only structure policy endorsement yields the pointwise rule only through ties —
which is also the only way the pointwise rule can hold with two realized actions at one input
(`score_eq_of_udtRule`). Witness of the full package: `CB8X` (four distinct realized policies,
utility depending on the policy, every realized policy of conditional utility `1/2`).
Source: mandate T4(c) (the finding behind "neither implies the other")
Kind: P
Fidelity: n/a (a structural theorem about `AbstractDS`; `hcons` restricts to external-only chosen policies)
Hyps: (a) all; `hcons` is a hypothesis on the structure, disclosed -/
theorem udtRule_of_policyEndorsed [DecidableEq AI] (h : PolicyEndorsed S) (aI₀ : AI)
    (hcons : ∀ ω o e, S.polS ω (o, e) = (aI₀, S.polE ω e)) : S.UdtRule := by
  intro ω o e a
  -- the common value of the policy utility on the support
  set c := S.policyUtility (S.polE ω) with hc
  have hscore_realized : ∀ ω', S.score o e (S.polS ω' (o, e)) = c := by
    intro ω'
    have hne : (S.evS o e (S.polS ω' (o, e))).Nonempty := S.evS_self_nonempty ω' o e
    unfold AbstractDS.score
    rw [condExpJunk_of_pos (mass_pos_of_nonempty S.pos hne)]
    rw [div_eq_iff (mass_pos_of_nonempty S.pos hne).ne']
    -- fibre the event by the external policy
    have hfib : ∀ g : Ω → ℝ, ∑ x ∈ S.evS o e (S.polS ω' (o, e)), g x =
        ∑ π ∈ (S.evS o e (S.polS ω' (o, e))).image S.polE,
          ∑ x ∈ (S.evS o e (S.polS ω' (o, e))).filter (fun x => S.polE x = π), g x := fun g =>
      (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem S.polE hx) g).symm
    have hfilter : ∀ π ∈ (S.evS o e (S.polS ω' (o, e))).image S.polE,
        (S.evS o e (S.polS ω' (o, e))).filter (fun x => S.polE x = π) = S.evPolE π := by
      intro π hπ
      obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hπ
      ext x
      simp only [Finset.mem_filter, AbstractDS.mem_evS, AbstractDS.evPolE, Finset.mem_univ,
        true_and]
      constructor
      · exact And.right
      · intro hx
        refine ⟨?_, hx⟩
        rw [AbstractDS.mem_evS, hcons, hcons] at hx₀
        rw [hcons, hcons, hx]
        exact hx₀
    rw [mass, hfib, hfib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun π hπ => ?_
    rw [hfilter π hπ]
    obtain ⟨x₀, _, rfl⟩ := Finset.mem_image.1 hπ
    rw [sum_evPolE_eq S x₀, ← mass]
    have h1 := h ω x₀
    have h2 := h x₀ ω
    rw [← hc] at h1 h2
    rw [le_antisymm h1 h2]
  -- the realized action scores `c`; an unrealized one scores `−1`
  rw [hscore_realized ω]
  by_cases hreal : (S.evS o e a).Nonempty
  · obtain ⟨x, hx⟩ := hreal
    rw [AbstractDS.mem_evS] at hx
    rw [← hx, hscore_realized x]
  · rw [Finset.not_nonempty_iff_eq_empty] at hreal
    have hlt := S.score_lt_of_empty hreal (S.evS_self_nonempty ω o e)
    rw [hscore_realized ω] at hlt
    exact hlt.le

omit [DecidableEq Ω] [DecidableEq OE] in
/-- **The pointwise rule forces ties between realized actions**: under `UdtRule`, any two realized
actions at the same input `(ȯ, ö)` have equal score, since each is an argmax of the same score
function. So a witness of `UdtRule` with two realized actions at one input (`CB8`) is a tie
witness of necessity, not by a choice of weights.
Source: audit r1 N4/N9 (the tie is forced)
Kind: L
Fidelity: exact
Hyps: none -/
theorem score_eq_of_udtRule [DecidableEq AI] (h : S.UdtRule) (ω ω' : Ω) (o : OI) (e : OE) :
    S.score o e (S.polS ω (o, e)) = S.score o e (S.polS ω' (o, e)) :=
  le_antisymm (h ω' o e _) (h ω o e _)

omit [DecidableEq Ω] [DecidableEq OE] in
/-- Supporting lemma: on an event closed under "same external policy", the weighted sum of `U`
is the weighted sum of the policy utility of the realized policy (fibre by `Π̈`; on each fibre
`∑ w·U = policyUtility · mass`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_U_eq_sum_policyUtility {E : Finset Ω}
    (hE : ∀ ω ∈ E, ∀ ω', S.polE ω' = S.polE ω → ω' ∈ E) :
    ∑ ω ∈ E, S.μ.w ω * S.U ω = ∑ ω ∈ E, S.μ.w ω * S.policyUtility (S.polE ω) := by
  have hfib : ∀ g : Ω → ℝ, ∑ x ∈ E, g x =
      ∑ π ∈ E.image S.polE, ∑ x ∈ E.filter (fun x => S.polE x = π), g x := fun g =>
    (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem S.polE hx) g).symm
  rw [hfib, hfib (fun ω => S.μ.w ω * S.policyUtility (S.polE ω))]
  refine Finset.sum_congr rfl fun π hπ => ?_
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hπ
  have hfilter : E.filter (fun x => S.polE x = S.polE x₀) = S.evPolE (S.polE x₀) := by
    ext x
    simp only [Finset.mem_filter, AbstractDS.evPolE, event, Finset.mem_univ, true_and]
    exact ⟨And.right, fun hx => ⟨hE x₀ hx₀ x hx, hx⟩⟩
  have hconst : ∀ x ∈ S.evPolE (S.polE x₀),
      S.μ.w x * S.policyUtility (S.polE x) = S.μ.w x * S.policyUtility (S.polE x₀) := by
    intro x hx
    simp only [Finset.mem_filter, AbstractDS.evPolE, event, Finset.mem_univ, true_and] at hx
    rw [hx]
  rw [hfilter, sum_evPolE_eq S x₀, Finset.sum_congr rfl hconst, ← Finset.sum_mul]
  unfold mass
  ring

omit [DecidableEq Ω] [DecidableEq OE] in
/-- Supporting lemma: with an external-only chosen policy, the score of the realized action at
`(ȯ, ö)` is the conditional mean, on the class `{Π̈(·)(ö) = Π̈(ω)(ö)}`, of the policy utility of the
realized policy.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem score_eq_condMean_policyUtility [DecidableEq AI] (aI₀ : AI)
    (hcons : ∀ ω o e, S.polS ω (o, e) = (aI₀, S.polE ω e)) (ω : Ω) (o : OI) (e : OE) :
    S.score o e (S.polS ω (o, e)) =
      wsum S.μ.w (fun ω' => S.policyUtility (S.polE ω'))
          (cls (fun ω' => S.polE ω' e) (S.polE ω e)) /
        mass S.μ.w (cls (fun ω' => S.polE ω' e) (S.polE ω e)) := by
  have hev : S.evS o e (S.polS ω (o, e)) = cls (fun ω' => S.polE ω' e) (S.polE ω e) := by
    ext ω'
    simp only [AbstractDS.mem_evS, cls, mem_event, hcons, Prod.mk.injEq, true_and]
  have hpos : 0 < mass S.μ.w (cls (fun ω' => S.polE ω' e) (S.polE ω e)) :=
    mass_cls_pos (fun ω => (S.pos ω).le) (fun ω' => S.polE ω' e) (S.pos ω)
  unfold AbstractDS.score
  rw [hev, condExpJunk_of_pos hpos]
  congr 1
  refine sum_U_eq_sum_policyUtility S fun ω₁ hω₁ ω₂ hω₂ => ?_
  simp only [cls, mem_event] at hω₁ ⊢
  rw [hω₂]
  exact hω₁

omit [DecidableEq Ω] [DecidableEq OE] in
/-- **The pointwise UDT rule implies policy endorsement when the policy utility is additively
separable across inputs** (P, repair round 1 — the converse of `udtRule_of_policyEndorsed` on
the regime the corpus's UDT theorem lives in): if the chosen policy is external-only
(`Π* = (ȧ₀, Π̈)`) and `E[U | Π̈ = π] = ∑_ö X(ö, π ö)` for some table `X`, then `UdtRule` forces every
realized external policy to have the same policy utility. Proof: the rule's forced ties
(`score_eq_of_udtRule`) say the conditional mean of `f := E[U | Π̈ = Π̈(·)]` given `Π̈(·)(ö) = ä` is
the same for every realized `ä`, at every `ö`; then `Var(f) = ∑_ö Cov(f, X(ö, Π̈(·)(ö))) = 0`
(`eq_on_support_of_condMean_const`). The separability hypothesis is exactly what
decision-determination supplies in the Coordinated-Buttons pattern (`U = u(Ä, D_E)` with
`Ä = Π̈(D_E)` and `D_E` independent of `Π̈`), and exactly what `CB8` lacks: its policy utility is
the non-separable Coordinated-Buttons table, which is why its ties coexist with unequal policy
utilities. Together with `udtRule_of_policyEndorsed`: on external-only structures with a separable
policy utility the pointwise rule and policy endorsement are **equivalent**. Needs an input `ȯ`
to exist (`o₀`), else the rule is vacuous.
Source: audit r1 fidelity N1 ("on external-only DD structures, does the pointwise rule force equal policy utilities across realized policies?") | [[agency-via-endorsement]] §The UDT Connection
Kind: P
Fidelity: n/a (a structural theorem about `AbstractDS`; `hcons` and `hsep` are hypotheses on the structure, disclosed; decision-determination itself is not assumed — see the module docstring for the link)
Hyps: (a) all; `hcons` (external-only chosen policy) and `hsep` (separable policy utility, with its table `X`) are hypotheses on the structure, disclosed -/
theorem policyEndorsed_of_udtRule_of_separable [DecidableEq AI] (h : S.UdtRule) (o₀ : OI)
    (aI₀ : AI) (hcons : ∀ ω o e, S.polS ω (o, e) = (aI₀, S.polE ω e)) (X : OE → AE → ℝ)
    (hsep : ∀ ω, S.policyUtility (S.polE ω) = ∑ e, X e (S.polE ω e)) : PolicyEndorsed S := by
  intro ω ω'
  have key := eq_on_support_of_condMean_const (w := S.μ.w) (fun ω => (S.pos ω).le) S.polE X hsep
    (fun e ω₁ ω₂ _ _ => by
      rw [← score_eq_condMean_policyUtility S aI₀ hcons ω₁ o₀ e,
        ← score_eq_condMean_policyUtility S aI₀ hcons ω₂ o₀ e]
      exact score_eq_of_udtRule S h ω₁ ω₂ o₀ e)
  exact (key ω ω' (S.pos ω) (S.pos ω')).ge

/-- **On external-only structures with a separable policy utility, the pointwise rule and policy
endorsement coincide** (C): `udtRule_of_policyEndorsed` and `policyEndorsed_of_udtRule_of_separable`.
Source: audit r1 fidelity N1 | [[agency-via-endorsement]] §The UDT Connection
Kind: C
Fidelity: n/a (as for the two components)
Hyps: (a) all; `hcons`, `hsep` as above -/
theorem udtRule_iff_policyEndorsed_of_separable [DecidableEq AI] (o₀ : OI) (aI₀ : AI)
    (hcons : ∀ ω o e, S.polS ω (o, e) = (aI₀, S.polE ω e)) (X : OE → AE → ℝ)
    (hsep : ∀ ω, S.policyUtility (S.polE ω) = ∑ e, X e (S.polE ω e)) :
    S.UdtRule ↔ PolicyEndorsed S :=
  ⟨fun h => policyEndorsed_of_udtRule_of_separable S h o₀ aI₀ hcons X hsep,
    fun h => udtRule_of_policyEndorsed S h aI₀ hcons⟩

end General

/-! ### `CB8`: the pointwise rule holds, policy endorsement fails -/

namespace CB8

/-- Worlds: an external observation `e : Fin 2` (the room) and the chosen policy
`(b₀, b₁) : Fin 2 × Fin 2` (button pressed in room `0`, room `1`).
Source: mandate T4(c) (the Coordinated-Buttons pattern)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := Fin 2 × (Fin 2 × Fin 2)

/-- The policy `(b₀, b₁)` as a function of the room.
Source: mandate T4(c)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pol (b : Fin 2 × Fin 2) (e : Fin 2) : Fin 2 := if e = 0 then b.1 else b.2

/-- Prior weights `3, 3, 3, 1` on the policies `(0,0), (0,1), (1,0), (1,1)`, in each room
(total `20`): chosen so that `E[U | Π*(ö) = ä] = 1/4` for every realized `(ö, ä)`.
Source: mandate T4(c)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt ω := if ω.2 = (1, 1) then 1 else 3
  pos ω := by split_ifs <;> norm_num
  N := 20
  sum_eq := by decide +kernel

/-- Coordinated Buttons, scaled to `[0, 1]`: `(0,0) ↦ 1/2`, `(1,1) ↦ 1`, mismatch `↦ 0`.
Source: mandate T4(c)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def U (ω : Ω) : ℝ := if ω.2 = (0, 0) then 1 / 2 else if ω.2 = (1, 1) then 1 else 0

/-- **The `CB8` decision structure**: `Ö` = the room, `D_B` = the policy, `Ä = pol D_B Ö`,
`D_E = Ö` (the environment decides the room), everything internal trivial,
`Π*(ȯ, ö) = (0, pol D_B ö)`.
Source: mandate T4(c)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def absDS : AbstractDS Ω (Fin 1) (Fin 2) (Fin 1) (Fin 2) (Fin 1) (Fin 2) (Fin 2 × Fin 2) (Fin 1)
    (Fin 1) where
  μ := weights.dist
  pos := weights.w_pos
  oI _ := 0
  oE ω := ω.1
  aI _ := 0
  aE ω := pol ω.2 ω.1
  dI _ := 0
  dE ω := ω.1
  dB ω := ω.2
  oH _ := 0
  oC _ := 0
  polS ω := fun oe => (0, pol ω.2 oe.2)
  U := U
  U_mem ω := by
    unfold U
    split_ifs <;> norm_num
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := (factorsAs_iff _ _).2 (by decide +kernel)
  B_fac := (factorsAs_iff _ _).2 (by decide +kernel)
  IB_fac := (factorsAs_iff _ _).2 (by decide +kernel)
  IB_det := by decide +kernel
  O_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- Supporting lemma: `Π̈` is the chosen policy.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : absDS.polE ω = pol ω.2 :=
  absDS.polE_eq_of (fun ω e => pol ω.2 e) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ω

/-- Supporting lemma: the weights, as reals.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem w_eq (ω : Ω) : absDS.μ.w ω = (if ω.2 = (1, 1) then 1 else 3) / 20 := by
  show weights.w ω = _
  unfold IntWeights.w weights
  simp only
  split_ifs <;> norm_num

/-- Supporting lemma: the chosen policy, read off the structure.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polS_eq (ω : Ω) (oe : Fin 1 × Fin 2) : absDS.polS ω oe = (0, pol ω.2 oe.2) := rfl

/-- Supporting lemma: the utility, read off the structure.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem U_eq (ω : Ω) : absDS.U ω = U ω := rfl

/-- Supporting lemma: every realized action scores `1/4` at every input (the tie).
Source: mandate T4(c)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem score_eq (o : Fin 1) (e : Fin 2) (b : Fin 2) : absDS.score o e (0, b) = 1 / 4 := by
  unfold AbstractDS.score AbstractDS.evS
  rw [condExpJunk, mass_event_eq, sum_event_eq]
  fin_cases e <;> fin_cases b <;>
  · simp +decide only [polS_eq, U_eq, pol, U, w_eq, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.isValue]
    norm_num

/-- **`CB8` satisfies the pointwise UDT rule** (every score is `1/4`).
Source: mandate T4(c)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem udtRule : absDS.UdtRule := by
  intro ω o e
  show IsArgmax (absDS.score o e) (absDS.polS ω (o, e))
  intro a
  obtain ⟨i, b⟩ := a
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  show absDS.score o e (0, b) ≤ absDS.score o e (0, pol ω.2 e)
  rw [score_eq, score_eq]

/-- **`CB8` is not policy endorsed**: `E[U | Π̈ = (0,0)] = 1/2 < 1 = E[U | Π̈ = (1,1)]`.
Source: mandate T4(c)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem not_policyEndorsed : ¬ PolicyEndorsed absDS := by
  intro h
  have := h (0, (0, 0)) (0, (1, 1))
  rw [polE_eq, polE_eq] at this
  unfold AbstractDS.policyUtility AbstractDS.evPolE at this
  rw [condExpJunk, condExpJunk, mass_event_eq, mass_event_eq, sum_event_eq,
    sum_event_eq] at this
  simp +decide only [polE_eq, U_eq, U, w_eq, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
    at this
  norm_num at this

/-- **T4(c), first separation** (N+): the pointwise UDT rule does not imply policy endorsement —
`CB8` has two realized external policies each pointwise unimprovable (all scores tie at `1/4`)
yet of different policy utility (`1/2` versus `1`). (i) The refuted sentence:
[[agency-via-endorsement]] §The UDT Connection, "Claim: An agent following UDT is
control-endorsed by its own prior", read with the pointwise rule; (ii) reading: `UdtRule`
(pointwise, `E[U | Π*(ȯ,ö) = a]`) versus `PolicyEndorsed` (`E[U | Π̈ = π]`); (iii) survivor:
`policyEndorsed_iff_isOptimal_on_range` (the policy-level reading is definitional) and
`udtRule_of_policyEndorsed` (the converse direction on external-only structures). Two caveats of
record (repair round 1): the universal tie is *forced*, not an accident of the weights `3,3,3,1`
— with two realized actions at one input the pointwise rule can only hold by a tie
(`score_eq_of_udtRule`), so this is the generic shape of any such witness; and the structure is
**not** `DecisionDetermined` (`not_decisionDetermined`: the utility depends on the other room's
button, which lives in `D_B`, not in `E`), so the refutation is carried outside the regime of the
corpus's UDT theorem — inside it, with a separable policy utility, the rule *does* force policy
endorsement (`policyEndorsed_of_udtRule_of_separable`).
Source: [[agency-via-endorsement]] §The UDT Connection | udt-rep-050 (mandate T4(c))
Kind: N+
Fidelity: n/a (eight worlds, two rooms, four realized policies, every factorization field checked by `decide`; not decision-determined, disclosed)
Hyps: none -/
theorem udtRule_not_policyEndorsed_witness : absDS.UdtRule ∧ ¬ PolicyEndorsed absDS :=
  ⟨udtRule, not_policyEndorsed⟩

/-- **`CB8` is not decision-determined**: worlds `(room 0, policy (0,0))` and
`(room 0, policy (0,1))` have the same `E = (Ä, D_E)` (button `0` pressed, room `0`) but
utilities `1/2` and `0` — the utility depends on the other room's button, which the structure
keeps in `D_B`. So the first clause `IsSubvariable E U` of `udt-comm-trust`'s `DecisionDetermined`
fails. The pointwise refutation above is therefore outside the decision-determined regime.
Source: audit r1 fidelity N1 (probe `NotDecisionDetermined.lean`)
Kind: N+ (component: scope of `udtRule_not_policyEndorsed_witness`)
Fidelity: n/a
Hyps: none -/
theorem not_decisionDetermined : ¬ absDS.DecisionDetermined := by
  intro h
  have := h.1 (0, (0, 0)) (0, (0, 1)) rfl
  rw [U_eq, U_eq] at this
  simp [U] at this

end CB8

/-! ### `IA4`: policy endorsed, the pointwise rule fails through the internal action -/

namespace IA4

/-- Worlds: an external policy index `p : Fin 2` and an internal action `i : Fin 2`.
Source: mandate T4(c)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := Fin 2 × Fin 2

/-- Uniform weights on the four worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt _ := 1
  pos _ := by norm_num
  N := 4
  sum_eq := by decide +kernel

/-- **The `IA4` decision structure**: one external observation, `Ä = p`, `Ȧ = i`, `D_B = (p, i)`,
`U = [i = 1]` — the internal action pays, the external policy is inert.
Source: mandate T4(c)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def absDS : AbstractDS Ω (Fin 1) (Fin 1) (Fin 2) (Fin 2) (Fin 1) (Fin 1) (Fin 2 × Fin 2) (Fin 1)
    (Fin 1) where
  μ := weights.dist
  pos := weights.w_pos
  oI _ := 0
  oE _ := 0
  aI ω := ω.2
  aE ω := ω.1
  dI _ := 0
  dE _ := 0
  dB ω := ω
  oH _ := 0
  oC _ := 0
  polS ω := fun _ => (ω.2, ω.1)
  U ω := if ω.2 = 1 then 1 else 0
  U_mem ω := by split_ifs <;> norm_num
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  I_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  E_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  B_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  IB_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  IB_det := by decide +kernel
  O_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  A_fac := (factorsAs_iff _ _).2 (by decide +kernel)

/-- Supporting lemma: `Π̈` is the constant external policy `p`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : absDS.polE ω = fun _ => ω.1 :=
  absDS.polE_eq_of (fun ω _ => ω.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) ω

/-- Supporting lemma: the weights, as reals.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem w_eq (ω : Ω) : absDS.μ.w ω = 1 / 4 := by
  show weights.w ω = _
  unfold IntWeights.w weights
  norm_num

/-- Supporting lemma: the chosen policy, read off the structure.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polS_eq (ω : Ω) (oe : Fin 1 × Fin 1) : absDS.polS ω oe = (ω.2, ω.1) := rfl

/-- Supporting lemma: the utility, read off the structure.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem U_eq (ω : Ω) : absDS.U ω = if ω.2 = 1 then 1 else 0 := rfl

/-- **`IA4` is policy endorsed**: both realized external policies have policy utility `1/2`.
Source: mandate T4(c)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem policyEndorsed : PolicyEndorsed absDS := by
  intro ω ω'
  have hpu : ∀ ω : Ω, absDS.policyUtility (absDS.polE ω) = 1 / 2 := by
    intro ω
    rw [polE_eq]
    unfold AbstractDS.policyUtility AbstractDS.evPolE
    rw [condExpJunk, mass_event_eq, sum_event_eq]
    obtain ⟨p, i⟩ := ω
    fin_cases p <;> fin_cases i <;>
    · simp +decide only [polE_eq, U_eq, w_eq, Fintype.sum_prod_type, Fin.sum_univ_two,
        Fin.isValue, funext_iff, Fin.forall_fin_one]
      norm_num
  rw [hpu, hpu]

/-- **`IA4` fails the pointwise UDT rule**: at a world with internal action `0`, the chosen
`(0, p)` scores `0` while `(1, p)` scores `1`.
Source: mandate T4(c)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem not_udtRule : ¬ absDS.UdtRule := by
  intro h
  have := h (0, 0) 0 0 (1, 0)
  unfold AbstractDS.score AbstractDS.evS at this
  rw [condExpJunk, condExpJunk, mass_event_eq, mass_event_eq, sum_event_eq,
    sum_event_eq] at this
  simp +decide only [polS_eq, U_eq, w_eq, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue,
    Prod.mk.injEq] at this
  norm_num at this

/-- **T4(c), second separation** (N+): policy endorsement does not imply the pointwise UDT rule —
`IA4` has two realized external policies of equal utility (endorsed) but the pointwise rule fails
through the internal action, which `policyUtility` does not see. By `udtRule_of_policyEndorsed`
this is the only way it can fail: with an external-only chosen policy the implication holds.
(i)–(iii) as for `udtRule_not_policyEndorsed_witness`; the survivor here is
`udtRule_of_policyEndorsed`.
Source: [[agency-via-endorsement]] §The UDT Connection | udt-rep-050 (mandate T4(c))
Kind: N+
Fidelity: n/a (two realized external policies; the internal action is the whole mechanism, disclosed; policy endorsement holds because `U` ignores the external policy — the tie is by inertness; not decision-determined, `not_decisionDetermined`)
Hyps: none -/
theorem policyEndorsed_not_udtRule_witness : PolicyEndorsed absDS ∧ ¬ absDS.UdtRule :=
  ⟨policyEndorsed, not_udtRule⟩

/-- **T4(d), weak form: a policy-endorsed structure with two distinct realized policies of equal
utility** — `IA4`'s `Π̈` is non-constant. **Graded N−** (repair round 1, audit r1 N2): the two
realized policies tie because `U = [i = 1]` ignores the external policy altogether, the way a
constant sequence ties. The honest T4(d) witness, where the tie is between policies the utility
genuinely depends on, is `CB8X.policyEndorsed_nonconstant_witness`.
Source: mandate T4(d) | udt-rep-051
Kind: N−
Fidelity: n/a (the external policy is inert in `U`)
Hyps: none -/
theorem policyEndorsed_nonconstant_witness :
    PolicyEndorsed absDS ∧ absDS.polE (0, 0) ≠ absDS.polE (1, 0) := by
  refine ⟨policyEndorsed, ?_⟩
  rw [polE_eq, polE_eq]
  intro h
  have := congrFun h 0
  simp at this

/-- **`IA4` is not decision-determined**: worlds `(0, 0)` and `(0, 1)` share
`E = (Ä, D_E) = (0, 0)` but have utilities `0` and `1` (the utility is the internal action's).
Source: audit r1 fidelity N1 (probe `NotDecisionDetermined.lean`)
Kind: N+ (component: scope of `policyEndorsed_not_udtRule_witness`)
Fidelity: n/a
Hyps: none -/
theorem not_decisionDetermined : ¬ absDS.DecisionDetermined := by
  intro h
  have := h.1 (0, 0) (0, 1) rfl
  rw [U_eq, U_eq] at this
  simp at this

end IA4

/-! ### `CB8X`: the full hypothesis package of `udtRule_of_policyEndorsed`, inhabited -/

namespace CB8X

/-- `U` depends on the room and on the policy: policy `(0,0)` pays in room `1`, policy `(1,1)`
pays in room `0`, the mismatched policies pay `1/2` in both rooms — arranged so that every
realized policy has conditional utility `1/2` under `CB8`'s weights.
Source: audit r1 adversarial N1 (probe `UdtRuleWitness.lean`)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def U (ω : CB8.Ω) : ℝ :=
  if ω.2 = (0, 0) then (if ω.1 = 1 then 1 else 0)
  else if ω.2 = (1, 1) then (if ω.1 = 0 then 1 else 0) else 1 / 2

/-- **The `CB8X` decision structure**: `CB8`'s eight worlds, weights and factorization fields
(unchanged, so every `decide +kernel` proof carries over) with the utility `CB8X.U`.
Source: audit r1 adversarial N1
Kind: D
Fidelity: n/a
Hyps: n/a -/
def absDS : AbstractDS CB8.Ω (Fin 1) (Fin 2) (Fin 1) (Fin 2) (Fin 1) (Fin 2) (Fin 2 × Fin 2) (Fin 1)
    (Fin 1) :=
  { CB8.absDS with
    U := U
    U_mem := fun ω => by unfold U; split_ifs <;> norm_num }

/-- Supporting lemma: `Π̈` is the chosen policy.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : CB8.Ω) : absDS.polE ω = CB8.pol ω.2 :=
  absDS.polE_eq_of (fun ω e => CB8.pol ω.2 e) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ω

/-- Supporting lemma: the weights, as reals (`CB8`'s).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem w_eq (ω : CB8.Ω) : absDS.μ.w ω = (if ω.2 = (1, 1) then 1 else 3) / 20 := CB8.w_eq ω

/-- Supporting lemma: the utility, read off the structure.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem U_eq (ω : CB8.Ω) : absDS.U ω = U ω := rfl

/-- **Every realized policy has conditional utility `1/2`** (16 cells: room × policy).
Source: audit r1 adversarial N1
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem policyUtility_eq (ω : CB8.Ω) : absDS.policyUtility (absDS.polE ω) = 1 / 2 := by
  rw [polE_eq]
  unfold AbstractDS.policyUtility AbstractDS.evPolE
  rw [condExpJunk, mass_event_eq, sum_event_eq]
  obtain ⟨e, b₀, b₁⟩ := ω
  fin_cases e <;> fin_cases b₀ <;> fin_cases b₁ <;>
  · simp +decide only [polE_eq, U_eq, U, w_eq, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.isValue, Prod.mk.injEq]
    norm_num

/-- **`CB8X` is policy endorsed.**
Source: audit r1 adversarial N1
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem policyEndorsed : PolicyEndorsed absDS := fun _ _ => by
  rw [policyUtility_eq, policyUtility_eq]

/-- Supporting lemma: the chosen policy is external-only, `Π* = (0, Π̈)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hcons (ω : CB8.Ω) (o : Fin 1) (e : Fin 2) : absDS.polS ω (o, e) = (0, absDS.polE ω e) := by
  show (0, CB8.pol ω.2 e) = (0, absDS.polE ω e)
  rw [polE_eq]

/-- **The theorem fires: `CB8X` satisfies the pointwise UDT rule.**
Source: audit r1 adversarial N1
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem udtRule : absDS.UdtRule := udtRule_of_policyEndorsed absDS policyEndorsed 0 hcons

/-- **Non-vacuity witness for `udtRule_of_policyEndorsed`** (N+): the full hypothesis package
`PolicyEndorsed ∧ hcons` is inhabited with four distinct realized policies and a utility that
depends on the policy (so the tie is not by inertness), and the conclusion `UdtRule` holds.
Source: audit r1 adversarial N1
Kind: N+
Fidelity: n/a (four realized policies, `U` non-constant across policies in a fixed room, external-only chosen policy)
Hyps: none -/
theorem udtRule_of_policyEndorsed_witness :
    PolicyEndorsed absDS ∧ (∀ ω o e, absDS.polS ω (o, e) = (0, absDS.polE ω e)) ∧
      absDS.polE (0, (0, 0)) ≠ absDS.polE (0, (1, 1)) ∧
      absDS.U (0, (0, 0)) ≠ absDS.U (0, (0, 1)) ∧ absDS.UdtRule := by
  refine ⟨policyEndorsed, hcons, ?_, ?_, udtRule⟩
  · rw [polE_eq, polE_eq]
    decide
  · norm_num [U_eq, U]

/-- **T4(d): a policy-endorsed structure with distinct realized policies of equal utility, where
the utility genuinely depends on the policy** (N+, the honest T4(d) witness; `IA4`'s is the
inert-policy N− form): the non-unique optimum keeps `Π̈` non-constant — the case the support
collapse (`polE_const_of_strictArgmax`) leaves open.
Source: mandate T4(d) | udt-rep-051 | audit r1 adversarial N2
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem policyEndorsed_nonconstant_witness :
    PolicyEndorsed absDS ∧ absDS.polE (0, (0, 0)) ≠ absDS.polE (0, (1, 1)) ∧
      absDS.U (0, (0, 0)) ≠ absDS.U (0, (0, 1)) :=
  ⟨policyEndorsed, udtRule_of_policyEndorsed_witness.2.2.1, udtRule_of_policyEndorsed_witness.2.2.2.1⟩

/-- **`CB8X` has a (trivially) separable policy utility**, `E[U | Π̈ = π] = ∑_ö 1/4`, so it also
inhabits the hypothesis package of `policyEndorsed_of_udtRule_of_separable` — with the inert
table `X ≡ 1/4`, which is all a *full-support* structure allows: with every policy realized, a
separable policy utility that is constant on the support has a table constant in the action.
A witness with an action-dependent table needs a restricted support (`CBD4`).
Source: audit r1 fidelity N1
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem policyUtility_separable (ω : CB8.Ω) :
    absDS.policyUtility (absDS.polE ω) = ∑ e : Fin 2, (fun _ _ => (1 / 4 : ℝ)) e (absDS.polE ω e) := by
  rw [policyUtility_eq, Fin.sum_univ_two]
  norm_num

/-- **`CB8X` is not decision-determined** either (`U` depends on the room *and* the whole policy).
Source: audit r1 fidelity N1
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem not_decisionDetermined : ¬ absDS.DecisionDetermined := by
  intro h
  have := h.1 (0, (0, 0)) (0, (0, 1)) rfl
  rw [U_eq, U_eq] at this
  simp [U] at this

end CB8X

/-! ### `CBD4`: a decision-determined structure in the separable regime (N+ for the equivalence) -/

namespace CBD4

/-- Worlds: a room `e : Fin 2` and a policy index `k : Fin 2` encoding the policy `(k, k + 1)`:
`k = 0 ↦ (0, 1)`, `k = 1 ↦ (1, 0)` — the two "anti-coordinated" policies only (restricted support;
on a full-support structure the equivalence's conclusion forces an action-inert table).
Source: audit r1 fidelity N1 (the decision-determined regime); repair round 1
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := Fin 2 × Fin 2

/-- The policy encoded by `k`: press `k` in room `0` and `k + 1` in room `1`.
Source: repair round 1 (`CBD4`)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pol (k : Fin 2) (e : Fin 2) : Fin 2 := if e = 0 then k else k + 1

/-- Uniform weights on the four worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt _ := 1
  pos _ := by norm_num
  N := 4
  sum_eq := by decide +kernel

/-- `U = [Ä = 1]`: pressing button `1` pays, in either room — a function of `(Ä, D_E)`, so
decision-determined, and a function of the policy *through the room*, so not inert.
Source: repair round 1 (`CBD4`)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def U (ω : Ω) : ℝ := if pol ω.2 ω.1 = 1 then 1 else 0

/-- **The `CBD4` decision structure**: `Ö = D_E` = the room, `D_B = k`, `Ä = pol k Ö`, everything
internal trivial, `Π*(ȯ, ö) = (0, pol k ö)`.
Source: repair round 1 (`CBD4`)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def absDS : AbstractDS Ω (Fin 1) (Fin 2) (Fin 1) (Fin 2) (Fin 1) (Fin 2) (Fin 2) (Fin 1) (Fin 1) where
  μ := weights.dist
  pos := weights.w_pos
  oI _ := 0
  oE ω := ω.1
  aI _ := 0
  aE ω := pol ω.2 ω.1
  dI _ := 0
  dE ω := ω.1
  dB ω := ω.2
  oH _ := 0
  oC _ := 0
  polS ω := fun oe => (0, pol ω.2 oe.2)
  U := U
  U_mem ω := by
    unfold U
    split_ifs <;> norm_num
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := (factorsAs_iff _ _).2 (by decide +kernel)
  B_fac := (factorsAs_iff _ _).2 (by decide +kernel)
  IB_fac := (factorsAs_iff _ _).2 (by decide +kernel)
  IB_det := by decide +kernel
  O_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- Supporting lemma: `Π̈` is the encoded policy.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : absDS.polE ω = pol ω.2 :=
  absDS.polE_eq_of (fun ω e => pol ω.2 e) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ω

/-- Supporting lemma: the weights, as reals.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem w_eq (ω : Ω) : absDS.μ.w ω = 1 / 4 := by
  show weights.w ω = _
  unfold IntWeights.w weights
  simp only
  norm_num

/-- Supporting lemma: the utility, read off the structure.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem U_eq (ω : Ω) : absDS.U ω = U ω := rfl

/-- Supporting lemma: the chosen policy is external-only, `Π* = (0, Π̈)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hcons (ω : Ω) (o : Fin 1) (e : Fin 2) : absDS.polS ω (o, e) = (0, absDS.polE ω e) := by
  show (0, pol ω.2 e) = (0, absDS.polE ω e)
  rw [polE_eq]

/-- **Every realized policy has conditional utility `1/2`** (each policy presses `1` in exactly
one room).
Source: repair round 1 (`CBD4`)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem policyUtility_eq (ω : Ω) : absDS.policyUtility (absDS.polE ω) = 1 / 2 := by
  rw [polE_eq]
  unfold AbstractDS.policyUtility AbstractDS.evPolE
  rw [condExpJunk, mass_event_eq, sum_event_eq]
  obtain ⟨e, k⟩ := ω
  fin_cases e <;> fin_cases k <;>
  · simp +decide only [polE_eq, U_eq, U, pol, w_eq, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.isValue]
    norm_num

/-- **`CBD4` is policy endorsed.**
Source: repair round 1 (`CBD4`)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem policyEndorsed : PolicyEndorsed absDS := fun _ _ => by
  rw [policyUtility_eq, policyUtility_eq]

/-- **`CBD4`'s policy utility is separable with the action-dependent table `X(ö, ä) = ½·[ä = 1]`.**
Source: repair round 1 (`CBD4`)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem policyUtility_separable (ω : Ω) :
    absDS.policyUtility (absDS.polE ω) =
      ∑ e : Fin 2, (fun (_ : Fin 2) (a : Fin 2) => if a = 1 then (1 / 2 : ℝ) else 0) e
        (absDS.polE ω e) := by
  rw [policyUtility_eq, polE_eq, Fin.sum_univ_two]
  obtain ⟨e, k⟩ := ω
  fin_cases k <;> simp [pol] <;> norm_num

/-- **`CBD4` satisfies the pointwise UDT rule** (by the forced tie at `1/2`).
Source: repair round 1 (`CBD4`)
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem udtRule : absDS.UdtRule := udtRule_of_policyEndorsed absDS policyEndorsed 0 hcons

/-- Supporting lemma: the realized-policy event, read off the structure.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evPolE_eq (π : Fin 2 → Fin 2) : absDS.evPolE π = event fun ω => pol ω.2 = π := by
  unfold AbstractDS.evPolE
  exact event_congr fun ω => by rw [polE_eq]

/-- Supporting lemma: `[[d]]_Π̈` is the encoded policy.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polOf_eq (d : Fin 1 × Fin 2) : absDS.polOf d = pol d.2 := by
  obtain ⟨d1, d2⟩ := d
  have : d1 = 0 := Subsingleton.elim _ _
  subst this
  exact polE_eq (0, d2)

/-- **`CBD4` is decision-determined**: `U` is a function of `E = (Ä, D_E)` (clause (1)), and the
product identity of clause (2) holds by counting (the policy is a bijective function of
`D_{I,B}`, so `{Π̈ = [[d]]}` is `{D_{I,B} = d}`).
Source: repair round 1 (`CBD4`); audit r1 fidelity N1
Kind: N+ (component)
Fidelity: n/a
Hyps: none -/
theorem decisionDetermined : absDS.DecisionDetermined := by
  refine ⟨fun ω ω' h => ?_, fun e d => ?_⟩
  · have h1 : pol ω.2 ω.1 = pol ω'.2 ω'.1 := (Prod.mk.inj h).1
    show (if pol ω.2 ω.1 = 1 then (1 : ℝ) else 0) = if pol ω'.2 ω'.1 = 1 then 1 else 0
    rw [h1]
  · have hev : (event fun ω => absDS.E ω = e ∧ absDS.polE ω = absDS.polOf d) =
        event fun ω => absDS.E ω = e ∧ pol ω.2 = pol d.2 :=
      event_congr fun ω => by rw [polE_eq, polOf_eq]
    rw [hev, evPolE_eq, polOf_eq]
    exact weights.mass_mul_eq_of_cnt (dd_key e d)
where
  /-- the count identity behind clause (2) -/
  dd_key : ∀ (e : Fin 2 × Fin 2) (d : Fin 1 × Fin 2),
      weights.cnt (event fun ω : Ω => absDS.E ω = e ∧ absDS.DIB ω = d) *
          weights.cnt (event fun ω : Ω => pol ω.2 = pol d.2) =
        weights.cnt (event fun ω : Ω => absDS.E ω = e ∧ pol ω.2 = pol d.2) *
          weights.cnt (absDS.evDIB d) := by decide +kernel

/-- **N+ witness for `policyEndorsed_of_udtRule_of_separable` in the decision-determined regime**:
`CBD4` is decision-determined, external-only, its policy utility is separable with the
action-dependent table `X(ö, ä) = ½·[ä = 1]`, the pointwise rule holds, two distinct policies are
realized, and the utility varies with the policy in a fixed room — and policy endorsement holds,
as the theorem says it must. The contrast with `CB8` is exactly decision-determination: there the
utility depends on the *other* room's button, so `E[U | Π̈ = π]` is the non-separable
Coordinated-Buttons table and the rule's ties coexist with unequal policy utilities.
Source: audit r1 fidelity N1; [[agency-via-endorsement]] §The UDT Connection (repair round 1)
Kind: N+
Fidelity: n/a (four worlds, two realized policies, action-dependent table, decision-determined)
Hyps: none -/
theorem separable_dd_witness :
    absDS.DecisionDetermined ∧ (∀ ω o e, absDS.polS ω (o, e) = (0, absDS.polE ω e)) ∧
      (∀ ω, absDS.policyUtility (absDS.polE ω) =
        ∑ e : Fin 2, (fun (_ : Fin 2) (a : Fin 2) => if a = 1 then (1 / 2 : ℝ) else 0) e
          (absDS.polE ω e)) ∧
      absDS.UdtRule ∧ PolicyEndorsed absDS ∧
      absDS.polE (0, 0) ≠ absDS.polE (0, 1) ∧ absDS.U (0, 0) ≠ absDS.U (0, 1) := by
  refine ⟨decisionDetermined, hcons, policyUtility_separable, udtRule, policyEndorsed, ?_, ?_⟩
  · rw [polE_eq, polE_eq]
    decide
  · norm_num [U_eq, U, pol]

end CBD4

end

end Cleanroom.Udt.UdtEndorsePolicy
