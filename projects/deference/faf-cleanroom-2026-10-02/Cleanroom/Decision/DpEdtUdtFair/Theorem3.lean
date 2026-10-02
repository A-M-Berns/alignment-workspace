import Cleanroom.Decision.DpEdtUdtFair.Limit

/-!
# FR-11 / A36 Theorem 3: event-tremble-EDT-consistency implies optimality on `𝔉` (T4)

* `stronglyFair_isOptimal_of_pointwise_best` — **Step 3**: on a strongly fair tree, a procedure
  whose mixed action at every queried point maximises `m ↦ ∑_a m(a) Q_C(d, a)` is optimal. This
  is `dp-local-opt`'s `key` induction (`stronglyFair_strictLocalMax_isOptimal`, repair round 2)
  with the pointwise-best hypothesis in place of strictness: induction on the set of points
  allowed to move, at the node with the smallest subtree, using the gated shape
  `value_deviate_eq_gated` and `Q`'s fiber-constancy.
* `eventTrembleEdt_isOptimal_of_fairClass` — **Theorem 3**: `FairClass → D2 → IsOptimal`,
  `C` mixed allowed. Steps 1–2 (`FairClass.Q_le_Q_of_eventTremble`) make every supported action
  a maximiser of `Q_C(d, ·)`, so `C(d)` maximises the affine map; Step 3 closes.
* `FairClass.eventTremble_iff_Q` — on `𝔉`, D2 is exactly "for all small `ε`, at every queried
  point, `supp C(d) ⊆ argmax_a Q_{C^ε}(d, a)`": the form every concrete witness is checked in.

**Scope (critique §3, dp-cf-139).** Fair class `𝔉` = strongly fair ∧ recording at every queried
point for every procedure ∧ pruned ∧ every queried observation realized; device =
event-tremble-EDT (D2, `EventTrembleEdtConsistent`, Definition 6 independent redraws);
optimality = `IsOptimal`. Not "EDT = UDT on fair problems" in email 4's sense: the inclusion is
strict (`fr12_outY_isOptimal_not_eventTremble`, `FairWitnesses.lean`); strict, masked and
limit-state EDT, Definition 22, Theorem 1 and Theorem 2 approve `(a, y)` on `threat ∈ 𝔉`
(`threat_outY_untrembled_all`, `LimitState.lean`; the limit-state clause is `outY_limitStateEdt`,
critique C9's pinned-state `A_d^+` collapse); on the almost-fair class D2 approves `(H, H)` on
`twoStag` (`Necessity.lean`); the individuation question is touched by nothing here. The
untrembled counterpart of Theorem 3 is CA-2′ (`fairClass_dfMasked_isOptimal`, `DfTheorem.lean`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpEdtUdtFair

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt
open Cleanroom.Decision.DpCalibration

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι]

/-! ### Step 3: the pointwise-best induction -/

section step3

omit [Fintype Ω] [DecidableEq Ω] in
/-- **Step 3 of FR-11 (the induction)**: on a strongly fair tree, if at every queried `d` the
mixed action `C(d)` maximises `m ↦ ∑_a m(a) Q_C(d, a)`, then `C` is optimal. Proof: induction
on the set `S` of points allowed to move (`Finset.strongInduction`); at the `S`-node `q₀` with the
smallest subtree no `S`-point lies below a `d_{q₀}`-node, so the gated shape
`V(C'[d ↦ m]) = offOcc_d(C') + fiberMass_d(C') · ∑_a m(a) V_{c₀ a}(C')` has `C'`-independent
reference values `V_{c₀ a}(C') = V_{c₀ a}(C) = Q_C(d, a)`; the hypothesis says resetting `C'(d)`
to `C(d)` does not lower `V`, and the induction hypothesis on `S ∖ {d}` finishes. Re-proved here
from `dp-local-opt`'s `value_deviate_eq_gated` (its `key` induction is inside a proof and cannot
be imported).
Source: `fair-repair.md` FR-11 Step 3 ("Height induction"); `adversary-repair.md` Claim A Step 3;
`dp-local-opt` `GatedInduction.lean` (the induction's shape)
Kind: P
Fidelity: variant: induction on the set of moving points at the smallest-subtree node rather
than on height; no assignment lemma used (as GR-10 remarks)
Hyps: (a) `StronglyFair B`, (a) pointwise best response in `Q` -/
theorem stronglyFair_isOptimal_of_pointwise_best {B : Tree Ω ι acts K} (hB : StronglyFair B)
    (C : Proc ι acts K)
    (hbest : ∀ d ∈ queried B, ∀ m : FinDistr K (acts d),
      ∑ a, m.w a * Q C B d a ≤ ∑ a, (C d).w a * Q C B d a) : IsOptimal C B := by
  have key : ∀ S : Finset ι, ∀ C' : Proc ι acts K, (∀ e, e ∉ S → C' e = C e) →
      value C' B ≤ value C B := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
      intro C' hC'
      by_cases hN : (Finset.univ.filter fun q : B.DecNode => pt B q ∈ S).Nonempty
      · obtain ⟨q₀, hq₀mem, hq₀min⟩ := Finset.exists_min_image
          (Finset.univ.filter fun q : B.DecNode => pt B q ∈ S) (fun q => size (subtreeAt B q)) hN
        obtain ⟨d, hq₀⟩ : ∃ d, pt B q₀ = d := ⟨_, rfl⟩
        have hdS : d ∈ S := hq₀ ▸ (Finset.mem_filter.mp hq₀mem).2
        have hdQ : d ∈ queried B := hq₀ ▸ pt_mem_queried B q₀
        obtain ⟨c₀, hc₀⟩ := subtreeAt_eq_decision' B q₀ d hq₀
        have shape := fun (C'' : Proc ι acts K) (m : FinDistr K (acts d)) =>
          value_deviate_eq_gated C'' hB q₀ d hq₀ c₀ hc₀ m
        -- no `S`-point below a `d`-node: the reference values do not depend on `C'`
        have hchild : ∀ a, value C' (c₀ a) = value C (c₀ a) := by
          intro a
          apply value_congr_queried
          intro e he
          by_contra hne
          have heS : e ∈ S := by
            by_contra h'
            exact hne (hC' e h')
          obtain ⟨q, hq, hlt⟩ := exists_node_lt_of_mem_queried_child' B q₀ d hq₀ c₀ hc₀ a e he
          have := hq₀min q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq ▸ heS⟩)
          omega
        have hQ : ∀ a, value C (c₀ a) = Q C B d a := fun a => stronglyFair_value_eq_Q hB C hc₀ a
        have hf : ∀ m : FinDistr K (acts d),
            ∑ a, m.w a * value C (c₀ a) ≤ ∑ a, (C d).w a * value C (c₀ a) := by
          intro m
          simp only [hQ]
          exact hbest d hdQ m
        have h1 : value C' B =
            offOcc C' B d + fiberMass C' B d * ∑ a, (C' d).w a * value C (c₀ a) := by
          have := shape C' (C' d)
          rw [Proc.deviate_self] at this
          simpa only [hchild] using this
        have h2 : value (C'.deviate d (C d)) B =
            offOcc C' B d + fiberMass C' B d * ∑ a, (C d).w a * value C (c₀ a) := by
          simpa only [hchild] using shape C' (C d)
        have h3 : value (C'.deviate d (C d)) B ≤ value C B := by
          refine ih (S.erase d) (Finset.erase_ssubset hdS) _ fun e he => ?_
          by_cases hed : e = d
          · subst hed; simp
          · rw [Proc.deviate_ne C' _ hed]
            exact hC' e fun heS => he (Finset.mem_erase.mpr ⟨hed, heS⟩)
        have hF := fiberMass_nonneg C' B d
        have := mul_le_mul_of_nonneg_left (hf (C' d)) hF
        linarith
      · have hagree : ∀ e ∈ queried B, C' e = C e := by
          intro e he
          by_contra hne
          have heS : e ∈ S := by
            by_contra h'
            exact hne (hC' e h')
          obtain ⟨q, hq⟩ := exists_decNode_of_mem_queried B e he
          exact hN ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq ▸ heS⟩⟩
        exact (value_congr_queried B hagree).le
  intro C'
  have hagree : ∀ e ∈ queried B,
      C' e = (fun e => if e ∈ queried B then C' e else C e : Proc ι acts K) e :=
    fun e he => by simp [he]
  rw [value_congr_queried B hagree]
  exact key (queried B) _ fun e he => by simp [he]

omit [Fintype Ω] [DecidableEq Ω] [∀ d, DecidableEq (acts d)] [DecidableEq ι] in
/-- If every supported action of `m₀` attains the maximum of `f`, then `m₀` maximises the affine
map `m ↦ ∑_a m(a) f(a)` over all distributions.
Source: none: infrastructure (FR-11 Step 3: "mixed maximizers land on ties")
Kind: L -/
theorem sum_w_mul_le_of_support_max {α : Type} [Fintype α] (m₀ : FinDistr K α) (f : α → K)
    (hmax : ∀ a, 0 < m₀.w a → ∀ b, f b ≤ f a) (m : FinDistr K α) :
    ∑ a, m.w a * f a ≤ ∑ a, m₀.w a * f a := by
  obtain ⟨a₀, ha₀⟩ : ∃ a, 0 < m₀.w a := by
    by_contra hcon
    push Not at hcon
    have : ∑ a, m₀.w a = 0 :=
      Finset.sum_eq_zero fun a _ => le_antisymm (hcon a) (m₀.nonneg a)
    rw [m₀.sum_one] at this
    exact one_ne_zero this
  have hsupp : ∀ a, 0 < m₀.w a → f a = f a₀ :=
    fun a ha => le_antisymm (hmax a₀ ha₀ a) (hmax a ha a₀)
  have h0 : ∑ a, m₀.w a * f a = f a₀ := by
    calc ∑ a, m₀.w a * f a = ∑ a, m₀.w a * f a₀ := Finset.sum_congr rfl fun a _ => by
            rcases (m₀.nonneg a).lt_or_eq with ha | ha
            · rw [hsupp a ha]
            · rw [← ha]; simp
      _ = f a₀ := by rw [← Finset.sum_mul, m₀.sum_one, one_mul]
  rw [h0]
  calc ∑ a, m.w a * f a ≤ ∑ a, m.w a * f a₀ :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hmax a₀ ha₀ a) (m.nonneg a)
    _ = f a₀ := by rw [← Finset.sum_mul, m.sum_one, one_mul]

end step3

/-! ### Theorem 3 -/

section theorem3

variable {obs : ι → Finset Ω} {actEv : (d : ι) → acts d → Finset Ω}

/-- **FR-11 / A36 Theorem 3 — evidential optimality on the fair class.** On `𝔉`,
event-tremble-EDT-consistency (D2) implies `V`-optimality; `C` may be mixed.
Scope: fair class `𝔉` = strongly fair ∧ recording at every queried point for every procedure ∧
pruned ∧ every queried observation realized; device = event-tremble-EDT (D2,
`EventTrembleEdtConsistent`, Definition 6 independent redraws); optimality = `IsOptimal`. Not
"EDT = UDT on fair problems" in email 4's sense (critique §3): the inclusion `{D2} ⊆ {optimal}` is
strict (`fr12_outY_isOptimal_not_eventTremble`); strict, masked and limit-state EDT, Definition 22,
Theorem 1 and Theorem 2 approve `(a, y)` on `threat ∈ 𝔉` (`threat_outY_untrembled_all`,
`LimitState.lean`; limit-state EDT by the pinned state, `outY_limitStateEdt`); on the almost-fair
class D2 approves `(H, H)` on `twoStag` (`twoStag_HH_eventTremble_not_optimal`); the
individuation question is touched by nothing here. Route: Step 1 (`FairClass.condExp_eq_Q`),
Step 2 (`FairClass.Q_le_Q_of_eventTremble`), Step 3 (`stronglyFair_isOptimal_of_pointwise_best`).
Source: `fair-repair.md` FR-11 (l. 95); `v2-amendments.md` A36 Theorem 3; `adversary-repair.md`
Claim A (the repaired hypothesis (O)); dp-cf-022, dp-cf-2-053, L4
Kind: C
Fidelity: exact
Hyps: (a) all (`FairClass` and `dp-calibration`'s D2 unchanged) -/
theorem eventTrembleEdt_isOptimal_of_fairClass [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) {C : Proc ι acts K}
    (hC : EventTrembleEdtConsistent obs actEv C B) : IsOptimal C B := by
  apply stronglyFair_isOptimal_of_pointwise_best h.stronglyFair C
  intro d hd m
  exact sum_w_mul_le_of_support_max (C d) (Q C B d)
    (fun a ha b => h.Q_le_Q_of_eventTremble hC hd a ha b) m

/-- **D2 on `𝔉` in `Q`-form**: `C` is event-tremble-EDT-consistent iff for all sufficiently small
`ε > 0`, at every queried `d`, every supported action of `C(d)` maximises `Q_{C^ε}(d, ·)`. (Step 1
identifies the calibrated act values with `Q_{C^ε}`; the guard and escape clause are discharged
by `FairClass.nuPoly_obs_ne_zero`, `fairClass_escape_never_fires` and
`FairClass.nu_actEv_inter_obs_pos`.) This is the form the concrete witnesses are checked in.
Source: `fair-repair.md` FR-11 Step 2 ("`T_EDT` reads: `supp C(d) ⊆ argmax_a v_ε(d, a)`");
`calibration.md` CA-16′
Kind: C
Fidelity: exact
Hyps: (a) `FairClass` -/
theorem FairClass.eventTremble_iff_Q [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) (C : Proc ι acts K) :
    EventTrembleEdtConsistent obs actEv C B ↔
      ∃ ε₀ > (0 : K), ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε ≤ 1), ε < ε₀ →
        ∀ d ∈ queried B, ∀ a, 0 < (C d).w a → ∀ b,
          Q (tremble C ε h0.le h1) B d b ≤ Q (tremble C ε h0.le h1) B d a := by
  constructor
  · rintro ⟨ε₀, hε₀, hD2⟩
    refine ⟨ε₀, hε₀, fun ε h0 h1 hlt d hd a ha b => ?_⟩
    have hfull := tremble_fullSupport C ε h0 h1
    obtain ⟨-, hle⟩ := hD2 ε h0 h1 hlt d hd (h.nuPoly_obs_ne_zero C hd)
      (fairClass_escape_never_fires h C ε h0 h1 hd) a ha
    have hb := hle b (h.nu_actEv_inter_obs_pos hfull hd b)
    rwa [h.condExp_eq_Q hfull hd a (hfull d a), h.condExp_eq_Q hfull hd b (hfull d b)] at hb
  · rintro ⟨ε₀, hε₀, hQ⟩
    refine ⟨ε₀, hε₀, fun ε h0 h1 hlt d hd _ _ a ha => ?_⟩
    have hfull := tremble_fullSupport C ε h0 h1
    refine ⟨h.nu_actEv_inter_obs_pos hfull hd a, fun b _ => ?_⟩
    rw [h.condExp_eq_Q hfull hd a (hfull d a), h.condExp_eq_Q hfull hd b (hfull d b)]
    exact hQ ε h0 h1 hlt d hd a ha b

/-- On `𝔉`, D2 in `Q`-form implies optimality (Theorem 3 through the characterisation).
Source: `fair-repair.md` FR-11
Kind: C -/
theorem FairClass.isOptimal_of_Q [∀ d, Nonempty (acts d)] {B : Tree Ω ι acts K}
    (h : FairClass obs actEv B) (C : Proc ι acts K)
    (hQ : ∃ ε₀ > (0 : K), ∀ ε, ∀ (h0 : 0 < ε) (h1 : ε ≤ 1), ε < ε₀ →
      ∀ d ∈ queried B, ∀ a, 0 < (C d).w a → ∀ b,
        Q (tremble C ε h0.le h1) B d b ≤ Q (tremble C ε h0.le h1) B d a) : IsOptimal C B :=
  eventTrembleEdt_isOptimal_of_fairClass h ((h.eventTremble_iff_Q C).mpr hQ)

end theorem3

end Cleanroom.Decision.DpEdtUdtFair
