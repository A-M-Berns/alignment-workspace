import Cleanroom.Udt.UdtCommTrust.Fairness
import Cleanroom.Udt.UdtCommTrust.Count
import Cleanroom.Udt.UdtCommTrust.Witness

/-!
# Audit r2 (adversarial) probe: the fairness conjunction does not force `P(Π̈ = R) = 1` for a
two-valued recommendation (T15(a), negative half — the findings' eight-world design, built)

Not imported by the library. The findings (§B, T15) record the design and label it "unverified";
this probe builds it. Worlds `((m, k), ö)`, uniform: message `m`, chosen (= external) policy `k`
constant in the observation, realized instance `ö`; `R = (m, m)`, `Π̈ = (k, k)`, `U = 𝟙[ö = 1]`,
nothing ever forced. Then `DecisionDetermined`, `HasCA` (every action is its own communicative
alternative), `Stable r` for both realized `r` (strict *only* through the junk `−1` on the empty
deviating event), `UdtRule` (every attained action scores `1/2`) and `P(Π̈ = R) = P(m = k) = 1/2`.
So `DecisionDetermined ∧ HasCA ∧ (∀ r ∈ range R, Stable r) ∧ UdtRule` does not yield the
self-esteem condition. Also recorded: `StableR` fails on the same structure, so the Π-form
stability here is entirely the junk artifact the findings describe.
-/

namespace Cleanroom.Udt.UdtCommTrust.AuditR2.F8

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

/-- Worlds `((m, k), ö)`. -/
abbrev Ω : Type := (Fin 2 × Fin 2) × Fin 2

/-- Uniform weights on eight worlds. -/
def weights : IntWeights Ω where
  wt _ := 1
  pos _ := by norm_num
  N := 8
  sum_eq := by decide +kernel

/-- The utility indicator: the realized instance is `1`. -/
def Q (ω : Ω) : Prop := ω.2 = 1

instance (ω : Ω) : Decidable (Q ω) := by unfold Q; infer_instance

/-- The abstract structure. -/
noncomputable def absDS : AbstractDS Ω (Fin 2) (Fin 2) (Fin 1) (Fin 2) (Fin 2) (Fin 2) (Fin 2)
    (Fin 2) (Fin 1) where
  μ := weights.dist
  pos := weights.w_pos
  oI ω := ω.1.1
  oE ω := ω.2
  aI _ := 0
  aE ω := ω.1.2
  dI ω := ω.1.1
  dE ω := ω.2
  dB ω := ω.1.2
  oH ω := ω.1.1
  oC _ := 0
  polS ω := fun _ => (0, ω.1.2)
  U ω := if Q ω then 1 else 0
  U_mem ω := by split_ifs <;> simp
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  B_fac := factorsAs_of_fun (fun ω₁ ω₂ => ((ω₁.1.1, ω₂.1.2), ω₁.2)) (by decide +kernel)
  IB_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₂.1, ω₁.2)) (by decide +kernel)
  IB_det := by decide +kernel
  O_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- The concrete structure: the semantics recommend the message at every instance; nothing is
forced. -/
noncomputable def S : ConcreteDS Ω (Fin 2) (Fin 2) (Fin 1) (Fin 2) (Fin 2) (Fin 2) (Fin 2)
    (Fin 2) (Fin 1) where
  toAbstractDS := absDS
  s _ h := some h
  p _ _ := none

theorem polE_eq (ω : Ω) : S.polE ω = fun _ => ω.1.2 :=
  S.polE_eq_of (fun ω _ => ω.1.2) (by decide +kernel) (by decide +kernel) (by decide +kernel) ω

theorem evPolE_eq (π : Fin 2 → Fin 2) : S.evPolE π = event fun ω => (fun _ => ω.1.2) = π := by
  unfold AbstractDS.evPolE
  exact event_congr fun ω => by rw [polE_eq]

theorem polOf_eq (d : Fin 2 × Fin 2) : S.polOf d = fun _ => d.2 := by
  obtain ⟨d1, d2⟩ := d
  exact polE_eq ((d1, d2), 0)

theorem projOH_eq (o : Fin 2) : S.projOH o = o := S.projOH_oI (((o, 0), 0) : Ω)

theorem evFollowsR_eq :
    S.evFollowsR = event fun ω : Ω => ConcreteDS.Follows (fun _ => ω.1.2) (S.R ω) := by
  unfold ConcreteDS.evFollowsR
  exact event_congr fun ω => by rw [polE_eq]

theorem evFollowsMinus_eq (r : Fin 2 → Option (Fin 2)) (e : Fin 2) :
    S.evFollowsMinus r e = event fun ω : Ω => ∀ e' ≠ e, ∀ a, r e' = some a → ω.1.2 = a := by
  ext ω
  simp only [ConcreteDS.evFollowsMinus, mem_event, polE_eq]

theorem R_nonsilent (ω : Ω) (e : Fin 2) : (S.R ω e).isSome := rfl

/-! ### Decision-determination -/

theorem decisionDetermined : S.DecisionDetermined := by
  refine ⟨fun ω ω' h => ?_, fun e d => ?_⟩
  · have h2 : ω.2 = ω'.2 := (Prod.mk.inj h).2
    show (if Q ω then (1 : ℝ) else 0) = if Q ω' then 1 else 0
    have hq : Q ω ↔ Q ω' := by unfold Q; rw [h2]
    exact if_congr hq rfl rfl
  · have hev : (event fun ω => S.E ω = e ∧ S.polE ω = S.polOf d) =
        event fun ω => S.E ω = e ∧ (fun _ : Fin 2 => ω.1.2) = fun _ => d.2 :=
      event_congr fun ω => by rw [polE_eq, polOf_eq]
    rw [hev, evPolE_eq, polOf_eq]
    exact weights.mass_mul_eq_of_cnt (dd_key e d)
where
  dd_key : ∀ (e : Fin 2 × Fin 2) (d : Fin 2 × Fin 2),
      weights.cnt (event fun ω : Ω => S.E ω = e ∧ S.DIB ω = d) *
          weights.cnt (event fun ω : Ω => (fun _ : Fin 2 => ω.1.2) = fun _ => d.2) =
        weights.cnt (event fun ω : Ω => S.E ω = e ∧ (fun _ : Fin 2 => ω.1.2) = fun _ => d.2) *
          weights.cnt (S.evDIB d) := by decide +kernel

/-! ### Communicative alternatives (every action is its own) -/

theorem evS_nonempty (o e a : Fin 2) : (S.evS o e (0, a)).Nonempty :=
  weights.nonempty_of_cnt_pos (by revert o e a; decide +kernel)

theorem evS_follows_nonempty (o e a : Fin 2) :
    (S.evS o e (0, a) ∩ event fun ω : Ω => ConcreteDS.Follows (fun _ => ω.1.2) (S.R ω)).Nonempty :=
  weights.nonempty_of_cnt_pos (by revert o e a; decide +kernel)

theorem modS_zero (o e : Fin 2) (a : Fin 1 × Fin 2) : S.modS o e a = 0 := by
  unfold ConcreteDS.modS ConcreteDS.modProb
  have hmod : S.evMod = ∅ := by decide +kernel
  rw [hmod]
  by_cases h : (S.evS o e a).Nonempty
  · rw [condProbJunk_of_nonempty S.pos h, Finset.empty_inter]
    simp [mass]
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h]
    exact condProbJunk_of_empty _ _

theorem hasCA : S.HasCA := by
  intro o e a _
  obtain ⟨ai, a⟩ := a
  have hai : ai = 0 := Subsingleton.elim _ _
  subst hai
  refine ⟨(0, a), fun a' _ => by rw [modS_zero, modS_zero], W2.forall_fun2 fun x y => ?_⟩
  rw [evPolE_eq, evFollowsR_eq]
  exact weights.condProbJunk_eq_of_cnt (evS_nonempty o e a) (evS_follows_nonempty o e a)
    (ca_key o e a x y)
where
  ca_key : ∀ (o e a x y : Fin 2),
      weights.cnt ((event fun ω : Ω => (fun _ : Fin 2 => ω.1.2) = fun e' => if e' = 0 then x else y) ∩
            S.evS o e (0, a)) *
          weights.cnt (S.evS o e (0, a) ∩
            event fun ω : Ω => ConcreteDS.Follows (fun _ => ω.1.2) (S.R ω)) =
        weights.cnt ((event fun ω : Ω => (fun _ : Fin 2 => ω.1.2) = fun e' => if e' = 0 then x else y) ∩
            (S.evS o e (0, a) ∩
              event fun ω : Ω => ConcreteDS.Follows (fun _ => ω.1.2) (S.R ω))) *
          weights.cnt (S.evS o e (0, a)) := by decide +kernel

/-! ### Stability (Π-form): strict only through the junk `−1` -/

theorem stable_key_empty : ∀ (ω₀ : Ω) (e o a₀ : Fin 2) (ai : Fin 1) (a' : Fin 2),
    ω₀.1.1 = a₀ → o = a₀ → a' ≠ a₀ →
    S.evS o e (ai, a') ∩
      (event fun ω : Ω => ∀ e' ≠ e, ∀ a, S.R ω₀ e' = some a → ω.1.2 = a) = ∅ := by
  decide +kernel

theorem stable_key_pos : ∀ (ω₀ : Ω) (e o a₀ : Fin 2) (ai : Fin 1),
    ω₀.1.1 = a₀ → o = a₀ →
    0 < weights.cnt (S.evS o e (ai, a₀) ∩
      event fun ω : Ω => ∀ e' ≠ e, ∀ a, S.R ω₀ e' = some a → ω.1.2 = a) := by
  decide +kernel

theorem stable : ∀ r ∈ Set.range S.R, S.Stable r := by
  rintro r ⟨ω₀, rfl⟩ e a₀ hra o ho ai a' ha'
  rw [projOH_eq] at ho
  have ha₀ : ω₀.1.1 = a₀ := Option.some.inj hra
  have hoa : o = a₀ := Option.some.inj ho
  rw [evFollowsMinus_eq, stable_key_empty ω₀ e o a₀ ai a' ha₀ hoa ha', condExpJunk_of_empty]
  exact junk_lt_of_nonempty S.pos S.U_nonneg
    (weights.nonempty_of_cnt_pos (stable_key_pos ω₀ e o a₀ ai ha₀ hoa))

/-! ### The pointwise UDT rule: every attained action scores `1/2` -/

theorem score_tie (o e : Fin 2) : S.score o e (0, 0) = S.score o e (0, 1) := by
  unfold AbstractDS.score
  exact weights.condExpJunk_indicator_eq Q (evS_nonempty o e 0) (evS_nonempty o e 1)
    (by revert o e; decide +kernel) (-1)

theorem udtRule : S.UdtRule := by
  intro ω o e x
  have hall : ∀ a : Fin 1 × Fin 2, a = (0, 0) ∨ a = (0, 1) := by decide
  have hsc : ∀ a : Fin 1 × Fin 2, S.score o e a = S.score o e (0, 0) := fun a => by
    rcases hall a with rfl | rfl
    · rfl
    · exact (score_tie o e).symm
  show S.score o e x ≤ S.score o e (S.polS ω (o, e))
  rw [hsc x, hsc (S.polS ω (o, e))]

/-! ### `P(Π̈ = R) = 1/2` -/

theorem followsR_half : mass S.μ.w S.evFollowsR = 1 / 2 := by
  rw [evFollowsR_eq]
  have hc : weights.cnt (event fun ω : Ω => ConcreteDS.Follows (fun _ => ω.1.2) (S.R ω)) = 4 := by
    decide +kernel
  show mass weights.w _ = _
  rw [weights.mass_eq_cnt, hc]
  show ((4 : ℕ) : ℝ) / ((8 : ℕ) : ℝ) = 1 / 2
  norm_num

/-- **The fairness conjunction does not imply the self-esteem condition** (T15(a), negative
half): this structure has DD, communicative alternatives, stability of every realized
recommendation and the pointwise UDT rule, and `P(Π̈ = R) = 1/2 ≠ 1`. -/
theorem fairness_conjunction_not_sufficient :
    S.DecisionDetermined ∧ S.HasCA ∧ (∀ r ∈ Set.range S.R, S.Stable r) ∧ S.UdtRule ∧
      mass S.μ.w S.evFollowsR ≠ 1 :=
  ⟨decisionDetermined, hasCA, stable, udtRule, by rw [followsR_half]; norm_num⟩

/-! ### The told-form stability fails here: the Π-form's strictness is the junk `−1` -/

theorem told_key_pos : ∀ (o e a : Fin 2),
    0 < weights.cnt (S.evS o e (0, a) ∩ S.evToldMinus (S.R (((0, 0), 0) : Ω)) e) := by
  decide +kernel

theorem told_key_cnt : ∀ (e : Fin 2),
    weights.cnt ((S.evS 0 e (0, 0) ∩ S.evToldMinus (S.R (((0, 0), 0) : Ω)) e).filter Q) *
        weights.cnt (S.evS 0 e (0, 1) ∩ S.evToldMinus (S.R (((0, 0), 0) : Ω)) e) =
      weights.cnt ((S.evS 0 e (0, 1) ∩ S.evToldMinus (S.R (((0, 0), 0) : Ω)) e).filter Q) *
        weights.cnt (S.evS 0 e (0, 0) ∩ S.evToldMinus (S.R (((0, 0), 0) : Ω)) e) := by
  decide +kernel

/-- `StableR` fails for the realized recommendation `(0, 0)`: with the other instance *told* `0`
rather than *following* `0`, the deviating event is non-empty and both sides score `1/2`. -/
theorem not_stableR : ¬ S.StableR (S.R (((0, 0), 0) : Ω)) := by
  intro h
  have := h 0 0 rfl 0 (by rw [projOH_eq]; rfl) 0 1 (by decide)
  have heq : condExpJunk S.μ.w S.U (S.evS 0 0 (0, 0) ∩ S.evToldMinus (S.R (((0, 0), 0) : Ω)) 0) (-1) =
      condExpJunk S.μ.w S.U (S.evS 0 0 (0, 1) ∩ S.evToldMinus (S.R (((0, 0), 0) : Ω)) 0) (-1) :=
    weights.condExpJunk_indicator_eq Q (weights.nonempty_of_cnt_pos (told_key_pos 0 0 0))
      (weights.nonempty_of_cnt_pos (told_key_pos 0 0 1)) (told_key_cnt 0) (-1)
  exact lt_irrefl _ (heq ▸ this)

end Cleanroom.Udt.UdtCommTrust.AuditR2.F8
