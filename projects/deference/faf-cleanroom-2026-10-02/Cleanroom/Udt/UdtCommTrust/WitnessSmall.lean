import Cleanroom.Udt.UdtCommTrust.Advice
import Cleanroom.Udt.UdtCommTrust.Count
import Mathlib.Tactic.FinCases

/-!
# `Cleanroom.Udt.UdtCommTrust.WitnessSmall`: the small witnesses

Work package `udt-comm-trust`. Three tiny structures:

* `W2m` (four worlds `(m, k)`): the Self-Trust witness (T11(c), T17). One instance; the message
  `m` recommends action `m`; the chosen policy `k` follows (`k = 0`) or flips (`k = 1`); the side
  channel is neutral when the policy follows and forces the recommended action when it flips, so
  `Π̈ = R` everywhere, the flipping action is modifying with `m = 1 > 0`, decision-determination
  holds non-trivially, every attained action has a communicative alternative, and the two actions
  tie at `1/2` — the "weakly best" conclusion is exercised, not forced.
* `Two` (two worlds): the deterministic reading of decision-determination fails while the
  environment fixed-point equation has two solutions (T5(b)).
* `NoSub` (four worlds `(k, j)`): `Π*` is not a function of `D_{I,B}` and the decomposition over
  external policies fails by `0 ≠ 1/2` (T7).
-/

namespace Cleanroom.Udt.UdtCommTrust

open Cleanroom.Udt.UdtPolicyCalc Finset

/-! ### `W2m`: modification, communicative alternatives, a tie -/

namespace W2m

/-- Worlds `(m, k)`: the message and the chosen policy.
Source: none: infrastructure (mandate T11(c))
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := Fin 2 × Fin 2

/-- The side-channel value: `0` neutral when the policy follows, `m + 1` (forcing `m`) when it flips.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def chan (ω : Ω) : Fin 3 := if ω.2 = 0 then 0 else if ω.1 = 0 then 1 else 2

/-- Uniform integer weights.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt _ := 1
  pos _ := by norm_num
  N := 4
  sum_eq := by decide +kernel

/-- The utility indicator: `m = 1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Q (ω : Ω) : Prop := ω.1 = 1

instance (ω : Ω) : Decidable (Q ω) := by unfold Q; infer_instance

/-- **`W2m` as an abstract decision structure.**
Source: mandate T11(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def absDS : AbstractDS Ω (Fin 2 × Fin 3) (Fin 1) (Fin 1) (Fin 2) (Fin 2 × Fin 2)
    (Fin 1) (Fin 1) (Fin 2) (Fin 3) where
  μ := weights.dist
  pos := weights.w_pos
  oI ω := (ω.1, chan ω)
  oE _ := 0
  aI _ := 0
  aE ω := ω.1
  dI ω := ω
  dE _ := 0
  dB _ := 0
  oH ω := ω.1
  oC := chan
  polS ω := fun oe => (0, oe.1.1 + ω.2)
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
  E_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  B_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  IB_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  IB_det := by decide +kernel
  O_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- **`W2m` as a concrete decision structure**: the semantics recommend the message; the side
channel `c = x + 1` forces action `x`.
Source: mandate T11(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def S : ConcreteDS Ω (Fin 2 × Fin 3) (Fin 1) (Fin 1) (Fin 2) (Fin 2 × Fin 2)
    (Fin 1) (Fin 1) (Fin 2) (Fin 3) where
  toAbstractDS := absDS
  s _ h := some h
  p _ c := if c = 0 then none else some (if c = 1 then 0 else 1)

/-- `Π̈` on `W2m`: every instance's action is the message.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : S.polE ω = fun _ => ω.1 :=
  S.polE_eq_of (fun ω _ => ω.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) ω

/-- Supporting lemma `evPolE_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evPolE_eq (π : Fin 1 → Fin 2) : S.evPolE π = event fun ω => (fun _ => ω.1) = π := by
  unfold AbstractDS.evPolE
  exact event_congr fun ω => by rw [polE_eq]

/-- Supporting lemma `polOf_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polOf_eq (d : (Fin 2 × Fin 2) × Fin 1) : S.polOf d = fun _ => d.1.1 := by
  obtain ⟨d1, d2⟩ := d
  have : d2 = 0 := Subsingleton.elim _ _
  subst this
  exact polE_eq d1

/-- **`P(Π̈ = R) = 1` on `W2m`.**
Source: mandate T11(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem followsR : mass S.μ.w S.evFollowsR = 1 := by
  have : S.evFollowsR = univ := by
    rw [Finset.eq_univ_iff_forall]
    intro ω
    rw [ConcreteDS.mem_evFollowsR, polE_eq]
    revert ω
    decide
  rw [this]
  exact mass_univ S.μ

/-- **`W2m` is decision-determined**, non-trivially (`(m, k) ↦ Π̈` is 2-to-1).
Source: mandate T11(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem decisionDetermined : S.DecisionDetermined := by
  refine ⟨fun ω ω' h => ?_, fun e d => ?_⟩
  · have h1 : ω.1 = ω'.1 := (Prod.mk.inj h).1
    show (if Q ω then (1 : ℝ) else 0) = if Q ω' then 1 else 0
    have hq : Q ω ↔ Q ω' := by unfold Q; rw [h1]
    exact if_congr hq rfl rfl
  · have hev : (event fun ω => S.E ω = e ∧ S.polE ω = S.polOf d) =
        event fun ω => S.E ω = e ∧ (fun _ => ω.1) = fun _ => d.1.1 :=
      event_congr fun ω => by rw [polE_eq, polOf_eq]
    rw [hev, evPolE_eq, polOf_eq]
    exact weights.mass_mul_eq_of_cnt (dd_key e d)
where
  /-- the count identity behind clause (2) -/
  dd_key : ∀ (e : Fin 2 × Fin 1) (d : (Fin 2 × Fin 2) × Fin 1),
      weights.cnt (event fun ω : Ω => S.E ω = e ∧ S.DIB ω = d) *
          weights.cnt (event fun ω : Ω => (fun _ : Fin 1 => ω.1) = fun _ => d.1.1) =
        weights.cnt (event fun ω : Ω => S.E ω = e ∧ (fun _ : Fin 1 => ω.1) = fun _ => d.1.1) *
          weights.cnt (S.evDIB d) := by decide +kernel

/-- **`Π* ⊑ D_{I,B}` on `W2m`.**
Source: mandate T11(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem polS_sub : IsSubvariable S.DIB S.polS := by decide +kernel

/-- **`R ⊑ D_{I,B}` on `W2m`.**
Source: mandate T11(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem R_sub_DIB : IsSubvariable S.DIB S.R := by decide +kernel

/-- Supporting: the two actions at any input are attained.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_nonempty (o : Fin 2 × Fin 3) (e : Fin 1) (a : Fin 2) : (S.evS o e (0, a)).Nonempty :=
  weights.nonempty_of_cnt_pos (by revert o e a; decide)

/-- **The flipping action is modifying with probability `1`, the following action with
probability `0`**: at input `(m', c')`, `m(Π* = (0, m'+1)) = 1 > 0 = m(Π* = (0, m'))`.
Source: mandate T11(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem modS_values (o : Fin 2 × Fin 3) :
    S.modS o 0 (0, o.1) = 0 ∧ S.modS o 0 (0, o.1 + 1) = 1 := by
  unfold ConcreteDS.modS ConcreteDS.modProb
  rw [condProbJunk_of_nonempty S.pos (evS_nonempty o 0 _),
    condProbJunk_of_nonempty S.pos (evS_nonempty o 0 _)]
  have h1 : S.evMod ∩ S.evS o 0 (0, o.1) = ∅ := by revert o; decide +kernel
  have h2 : S.evMod ∩ S.evS o 0 (0, o.1 + 1) = S.evS o 0 (0, o.1 + 1) := by revert o; decide +kernel
  rw [h1, h2]
  refine ⟨by simp [mass], div_self ?_⟩
  exact (mass_pos_of_nonempty S.pos (evS_nonempty o 0 _)).ne'

/-- **The following action is minimally modifying; the flipping action is not.**
Source: mandate T11(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem minMod_follow (o : Fin 2 × Fin 3) : S.MinMod o 0 (0, o.1) := by
  intro a' _
  rw [(modS_values o).1]
  unfold ConcreteDS.modS ConcreteDS.modProb
  exact ConcreteDS.condProbJunk_nonneg S.pos _ _

/-- **`W2m` has communicative alternatives**: the following action is its own alternative, and it is
the alternative of the flipping action (the law of `Π̈` given either action is the law of `m`).
Source: mandate T11(c)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem hasCA : S.HasCA := by
  intro o e a ha
  have hne : ∀ a : Fin 1 × Fin 2, (S.evS o e a).Nonempty := fun a => by
    obtain ⟨ai, a⟩ := a
    have : ai = 0 := Subsingleton.elim _ _
    subst this
    exact evS_nonempty o e a
  obtain ⟨ai, a⟩ := a
  have hai : ai = 0 := Subsingleton.elim _ _
  subst hai
  refine ⟨(0, o.1), minMod_follow o, forall_fun_fin1 fun x => ?_⟩
  rw [(ConcreteDS.evFollowsR_eq_univ_iff S).1 followsR, Finset.inter_univ, evPolE_eq]
  exact weights.condProbJunk_eq_of_cnt (hne _) (hne _) (ca_key o e a x)
where
  /-- a universal over `Fin 1 → Fin 2` is a universal over one value -/
  forall_fun_fin1 {P : (Fin 1 → Fin 2) → Prop} (h : ∀ x, P fun _ => x) : ∀ π, P π := fun π => by
    have : π = fun _ => π 0 := by funext e; fin_cases e; rfl
    rw [this]; exact h _
  /-- the count identity behind the CA condition -/
  ca_key : ∀ (o : Fin 2 × Fin 3) (e : Fin 1) (a x : Fin 2),
      weights.cnt ((event fun ω : Ω => (fun _ : Fin 1 => ω.1) = fun _ => x) ∩ S.evS o e (0, a)) *
          weights.cnt (S.evS o e (0, o.1)) =
        weights.cnt ((event fun ω : Ω => (fun _ : Fin 1 => ω.1) = fun _ => x) ∩ S.evS o e (0, o.1)) *
          weights.cnt (S.evS o e (0, a)) := by decide +kernel

/-- **The tie**: at every input, following and flipping score the same (`1/2`), so the repaired
Self-Trust conclusion is exercised (the argmax contains the minimally modifying action) and no
strict version separates them (T17).
Source: mandate T11(c), T17
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem score_tie (o : Fin 2 × Fin 3) : S.score o 0 (0, o.1) = S.score o 0 (0, o.1 + 1) := by
  unfold AbstractDS.score
  exact weights.condExpJunk_indicator_eq Q (evS_nonempty o 0 _) (evS_nonempty o 0 _)
    (by revert o; decide) (-1)

/-- **Both actions are UDT argmaxes on `W2m`**, one modifying and one not: the strict-argmax ceiling
(T17(ii)) is tight.
Source: mandate T17
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem both_argmax (o : Fin 2 × Fin 3) :
    IsArgmax (S.score o 0) (0, o.1) ∧ IsArgmax (S.score o 0) (0, o.1 + 1) := by
  have hall : ∀ a : Fin 1 × Fin 2, a = (0, o.1) ∨ a = (0, o.1 + 1) := by
    rintro ⟨ai, a⟩
    have : ai = 0 := Subsingleton.elim _ _
    subst this
    revert a o
    decide +kernel
  constructor
  · intro a'
    rcases hall a' with rfl | rfl
    · exact le_rfl
    · exact (score_tie o).ge
  · intro a'
    rcases hall a' with rfl | rfl
    · exact (score_tie o).le
    · exact le_rfl

end W2m

/-! ### `Two`: the deterministic reading of DD fails (T5(b)) -/

namespace Two

/-- Uniform weights on two worlds.
Source: none: infrastructure (mandate T5(b))
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights (Fin 2) where
  wt _ := 1
  pos _ := by norm_num
  N := 2
  sum_eq := by decide +kernel

/-- **Two worlds, observation = action = the world, trivial dynamics**: `Π̈` is the identity in both
worlds and `D_E` is constant, yet `E` differs.
Source: mandate T5(b)
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def absDS : AbstractDS (Fin 2) (Fin 1) (Fin 2) (Fin 1) (Fin 2) (Fin 1) (Fin 1) (Fin 1)
    (Fin 1) (Fin 1) where
  μ := weights.dist
  pos := weights.w_pos
  oI _ := 0
  oE ω := ω
  aI _ := 0
  aE ω := ω
  dI _ := 0
  dE _ := 0
  dB _ := 0
  oH _ := 0
  oC _ := 0
  polS _ := fun oe => (0, oe.2)
  U _ := 0
  U_mem _ := by simp
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  B_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  IB_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  IB_det := by decide +kernel
  O_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- **The deterministic reading fails on `Two`**: the two worlds have the same `Π̈` and `D_E` but
different `E`.
Source: mandate T5(b) (witness of failure)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_detDD : ¬ absDS.DetDD :=
  absDS.not_detDD_of_two_worlds (ω := 0) (ω' := 1)
    (by rw [absDS.polE_eq_of (fun _ e => e) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      absDS.polE_eq_of (fun _ e => e) (by decide +kernel) (by decide +kernel) (by decide +kernel)])
    rfl (by decide +kernel)

/-- **The environment fixed-point equation has two solutions on `Two`**: `UniqueFix` fails.
Source: mandate T5(b)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_uniqueFix : ¬ absDS.UniqueFix := by
  intro h
  have hproj : ∀ x : Fin 2 × Fin 1, absDS.projOE x = x.1 := fun x => by
    obtain ⟨a, b⟩ := x
    have hb : b = 0 := Subsingleton.elim _ _
    subst hb
    exact absDS.projOE_E a
  have := h (fun e => e) 0 (0, 0) (1, 0) (by rw [hproj]) (by rw [hproj])
  exact absurd this (by decide +kernel)

end Two

/-! ### `NoSub`: the decomposition needs `Π* ⊑ D_{I,B}` (T7) -/

namespace NoSub

/-- Worlds `(k, j)`: `k` the boundary dynamic (the policy the world sees), `j` a coordinate the
dynamics ignore that decides both `Π*` and `U`.
Source: none: infrastructure (mandate T7)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := Fin 2 × Fin 2

/-- Uniform weights.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt _ := 1
  pos _ := by norm_num
  N := 4
  sum_eq := by decide +kernel

/-- The utility indicator `j = 1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Q (ω : Ω) : Prop := ω.2 = 1

instance (ω : Ω) : Decidable (Q ω) := by unfold Q; infer_instance

/-- **`NoSub` as an abstract decision structure**: `Ä = k`, `D_B = k`, `D_E = j`, `U = j`,
`Π* = (0, j)` at every input.
Source: mandate T7 (witness of necessity)
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def absDS : AbstractDS Ω (Fin 1) (Fin 1) (Fin 1) (Fin 2) (Fin 1) (Fin 2) (Fin 2)
    (Fin 1) (Fin 1) where
  μ := weights.dist
  pos := weights.w_pos
  oI _ := 0
  oE _ := 0
  aI _ := 0
  aE ω := ω.1
  dI _ := 0
  dE ω := ω.2
  dB ω := ω.1
  oH _ := 0
  oC _ := 0
  polS ω := fun _ => (0, ω.2)
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
  B_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  IB_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  IB_det := by decide +kernel
  O_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- `Π̈` on `NoSub`: the constant policy `k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : absDS.polE ω = fun _ => ω.1 :=
  absDS.polE_eq_of (fun ω _ => ω.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) ω

/-- Supporting lemma `evPolE_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evPolE_eq (π : Fin 1 → Fin 2) : absDS.evPolE π = event fun ω => (fun _ => ω.1) = π := by
  unfold AbstractDS.evPolE
  exact event_congr fun ω => by rw [polE_eq]

/-- Supporting lemma `polOf_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polOf_eq (d : Fin 1 × Fin 2) : absDS.polOf d = fun _ => d.2 := by
  obtain ⟨d1, d2⟩ := d
  have : d1 = 0 := Subsingleton.elim _ _
  subst this
  exact polE_eq (d2, 0)

/-- **`NoSub` is decision-determined.**
Source: mandate T7
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem decisionDetermined : absDS.DecisionDetermined := by
  refine ⟨fun ω ω' h => ?_, fun e d => ?_⟩
  · have h2 : ω.2 = ω'.2 := (Prod.mk.inj h).2
    show (if Q ω then (1 : ℝ) else 0) = if Q ω' then 1 else 0
    have hq : Q ω ↔ Q ω' := by unfold Q; rw [h2]
    exact if_congr hq rfl rfl
  · have hev : (event fun ω => absDS.E ω = e ∧ absDS.polE ω = absDS.polOf d) =
        event fun ω => absDS.E ω = e ∧ (fun _ => ω.1) = fun _ => d.2 :=
      event_congr fun ω => by rw [polE_eq, polOf_eq]
    rw [hev, evPolE_eq, polOf_eq]
    exact weights.mass_mul_eq_of_cnt (dd_key e d)
where
  /-- the count identity behind clause (2) -/
  dd_key : ∀ (e : Fin 2 × Fin 2) (d : Fin 1 × Fin 2),
      weights.cnt (event fun ω : Ω => absDS.E ω = e ∧ absDS.DIB ω = d) *
          weights.cnt (event fun ω : Ω => (fun _ : Fin 1 => ω.1) = fun _ => d.2) =
        weights.cnt (event fun ω : Ω => absDS.E ω = e ∧ (fun _ : Fin 1 => ω.1) = fun _ => d.2) *
          weights.cnt (absDS.evDIB d) := by decide +kernel

/-- **`Π*` is not a function of `D_{I,B}` on `NoSub`.**
Source: mandate T7 (udt-rep-016)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_polS_sub : ¬ IsSubvariable absDS.DIB absDS.polS := by decide +kernel

/-- **The decomposition over external policies fails on `NoSub`**: the left side of T7's display
at action `(0, 0)` is `0`, the right side is `1/2`.
Source: mandate T7 (witness of necessity, udt-rep-016)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem decomposition_fails :
    absDS.score 0 0 (0, 0) ≠ ∑ π ∈ Finset.univ.image absDS.polE,
      absDS.policyUtility π * condProbJunk absDS.μ.w (absDS.evPolE π) (absDS.evS 0 0 (0, 0)) 0 := by
  have himg : Finset.univ.image absDS.polE = {fun _ => 0, fun _ => 1} := by
    ext π
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨ω, rfl⟩
      rw [polE_eq]
      revert ω; decide +kernel
    · rintro (rfl | rfl)
      · exact ⟨(0, 0), by rw [polE_eq]⟩
      · exact ⟨(1, 0), by rw [polE_eq]⟩
  rw [himg, Finset.sum_pair (by decide)]
  unfold AbstractDS.score AbstractDS.policyUtility
  rw [evPolE_eq, evPolE_eq]
  have hU : absDS.U = fun ω => if Q ω then (1 : ℝ) else 0 := rfl
  have hw : absDS.μ.w = weights.w := rfl
  rw [hU, hw]
  have hne : ∀ a : Fin 2, (absDS.evS 0 0 (0, a)).Nonempty := fun a =>
    weights.nonempty_of_cnt_pos (by revert a; decide)
  have hne' : ∀ x : Fin 2, (event fun ω : Ω => (fun _ : Fin 1 => ω.1) = fun _ => x).Nonempty :=
    fun x => weights.nonempty_of_cnt_pos (by revert x; decide)
  rw [weights.condExpJunk_indicator Q (hne 0), weights.condExpJunk_indicator Q (hne' 0),
    weights.condExpJunk_indicator Q (hne' 1),
    condProbJunk_of_nonempty weights.w_pos (hne 0), condProbJunk_of_nonempty weights.w_pos (hne 0),
    IntWeights.mass_eq_cnt, IntWeights.mass_eq_cnt, IntWeights.mass_eq_cnt]
  have c1 : weights.cnt ((absDS.evS 0 0 (0, 0)).filter Q) = 0 := by decide +kernel
  have c2 : weights.cnt (absDS.evS 0 0 (0, 0)) = 2 := by decide +kernel
  have c3 : weights.cnt ((event fun ω : Ω => (fun _ : Fin 1 => ω.1) = fun _ => 0).filter Q) = 1 := by
    decide
  have c4 : weights.cnt (event fun ω : Ω => (fun _ : Fin 1 => ω.1) = fun _ => 0) = 2 := by decide +kernel
  have c5 : weights.cnt ((event fun ω : Ω => (fun _ : Fin 1 => ω.1) = fun _ => 1).filter Q) = 1 := by
    decide
  have c6 : weights.cnt (event fun ω : Ω => (fun _ : Fin 1 => ω.1) = fun _ => 1) = 2 := by decide +kernel
  have c7 : weights.cnt ((event fun ω : Ω => (fun _ : Fin 1 => ω.1) = fun _ => 0) ∩
      absDS.evS 0 0 (0, 0)) = 1 := by decide +kernel
  have c8 : weights.cnt ((event fun ω : Ω => (fun _ : Fin 1 => ω.1) = fun _ => 1) ∩
      absDS.evS 0 0 (0, 0)) = 1 := by decide +kernel
  rw [c1, c2, c3, c4, c5, c6, c7, c8]
  have hN : weights.N = 4 := rfl
  rw [hN]
  norm_num

end NoSub

end Cleanroom.Udt.UdtCommTrust
