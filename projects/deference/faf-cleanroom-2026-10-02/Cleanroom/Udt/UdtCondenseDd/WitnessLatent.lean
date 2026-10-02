import Cleanroom.Udt.UdtCondenseDd.Markov
import Cleanroom.Udt.UdtCommTrust.Count
import Cleanroom.Udt.UdtCommTrust.WitnessSmall

/-!
# `Cleanroom.Udt.UdtCondenseDd.WitnessLatent`: the T9 refutation witness

Work package `udt-condense-dd`, target T9(a) (udt-rep-045): a decision-determined abstract decision
structure whose external policy `Π̈` is **not** a function of the environment `E`, so that the
policy latent model does not perfectly condense `(D_{I,B}, E)` (`Latent.lean`,
`not_perfectlyCondenses_of_not_isSubvariable`).

## The structure `Three` (12 worlds, uniform)

Worlds `(k, i, j)`: `k : Fin 3` the boundary dynamic (which of three external policies the agent
runs), `i : Fin 2` an internal dynamic the environment ignores, `j : Fin 2` the external
observation, which is also the environment dynamic (`D_E = Ö = j`). The three policies are
`k = 0 : (0 ↦ 0, 1 ↦ 0)`, `k = 1 : (0 ↦ 0, 1 ↦ 1)`, `k = 2 : (0 ↦ 1, 1 ↦ 1)`; `Ä = Π̈_k(j)`;
`E = (Ä, j)`. Every `(Ä, D_E)` pair is realized (the environment-dynamic factorization holds), and
the worlds `(0, i, 0)` and `(1, i, 0)` have the same `E = (0, 0)` but different `Π̈`.

* **DD holds and is non-trivial**: `D_{I,B} = (i, k)` has six values, `Π̈` three; `E` ignores `i`.
* **`Π̈` is non-constant, and not a function of `E`** — so `¬ PerfectlyCondenses`.
* The mandate's "environment ignores the agent" witness is impossible
  (`Latent.lean`, `polE_const_of_indep_E_DIB`); here `E` *does* depend on `Π̈` (`Ä = Π̈(Ö)`),
  which is what any such witness must have.

## The positive instance `Xor` (repair round 2) and the satisfiability check `NoSubPerfect`

The refutation would also follow from an over-strong encoding that nothing satisfies. It does not,
and the positive instance of record is **`Xor`** (8 worlds `(k, i, j)` uniform, two *non-constant*
external policies — `k = 0` the identity `j ↦ j`, `k = 1` the flip — `Ä = Π̈_k(j)`, `E = (Ä, j)`):
decision-determined, `Π̈ ⊑ E` (the policy is recovered from the pair as `k = [Ä ≠ Ö]`), and
non-degenerate in every respect `NoSub` lacks — `E` is not injective (it ignores `i`), `Π̈` is a
function neither of `Ä` alone nor of `D_E` alone, `D_{I,B}` has four values against `Π̈`'s two, both
policies are non-constant. By `perfectlyCondenses_polLatent_iff_isSubvariable_of_dd`,
`polLatent Xor.absDS` perfectly condenses `(D_{I,B}, E)`: the same encoding admits both verdicts,
and the dividing line is exactly `Π̈ ⊑ E`. (The r2 adversarial audit's probe
`PerfectNondegenerate.lean`, lifted.)

`NoSubPerfect` (repair round 1) is kept as the *satisfiability* check it is, regraded **N−**:
`udt-comm-trust`'s `NoSub` is decision-determined with `Π̈` non-constant, but `E ω = ω` is
injective there, so *every* variable is a subvariable of `E` (`everything_sub_E`) and
`D_{I,B} ⊑ Π̈` (`DIB_sub_polE`), i.e. the latent model is `(X₀, id, X₀)` up to relabelling: the
function clause holds for a reason that has nothing to do with the policy (r2 adversarial audit B1).
-/

namespace Cleanroom.Udt.UdtCondenseDd

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset
open Condensation

noncomputable section

namespace Three

/-- Worlds `(k, i, j)`.
Source: mandate T9(a) (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := Fin 3 × Fin 2 × Fin 2

/-- The three external policies, indexed by `k`.
Source: mandate T9(a) (witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def polTable (k : Fin 3) (e : Fin 2) : Fin 2 :=
  if k = 0 then 0 else if k = 1 then e else 1

/-- Uniform weights on the twelve worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt _ := 1
  pos _ := by norm_num
  N := 12
  sum_eq := by decide +kernel

/-- The utility indicator `j = 1` (a function of `E`).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Q (ω : Ω) : Prop := ω.2.2 = 1

instance (ω : Ω) : Decidable (Q ω) := by unfold Q; infer_instance

/-- A policy index realizing action `a` at observation `e` (used for the environment-dynamic
factorization): `a = 0 ↦ k = 0`; `a = 1 ↦ k = 2` at `e = 0`, `k = 1` at `e = 1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def kFor (a e : Fin 2) : Fin 3 := if a = 0 then 0 else if e = 0 then 2 else 1

/-- **`Three` as an abstract decision structure**.
Source: mandate T9(a) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
def absDS : AbstractDS Ω (Fin 1) (Fin 2) (Fin 1) (Fin 2) (Fin 2) (Fin 2) (Fin 3) (Fin 1) (Fin 1)
    where
  μ := weights.dist
  pos := weights.w_pos
  oI _ := 0
  oE ω := ω.2.2
  aI _ := 0
  aE ω := polTable ω.1 ω.2.2
  dI ω := ω.2.1
  dE ω := ω.2.2
  dB ω := ω.1
  oH _ := 0
  oC _ := 0
  polS ω := fun _ => (0, polTable ω.1 0)
  U ω := if Q ω then 1 else 0
  U_mem ω := by split_ifs <;> simp
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_chain (by decide +kernel) (by decide +kernel)
    (fun ω ω' => (ω'.1, ω.2.1, ω'.2.2)) (by decide +kernel)
  BE_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := factorsAs_of_fun (fun ω₁ ω₂ => (kFor (polTable ω₁.1 ω₁.2.2) ω₂.2.2, 0, ω₂.2.2))
    (by decide +kernel)
  B_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₂.1, 0, ω₁.2.2)) (by decide +kernel)
  IB_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₂.1, ω₂.2.1, ω₁.2.2)) (by decide +kernel)
  IB_det := by decide +kernel
  O_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- `Π̈` on `Three`: the policy table at `k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : absDS.polE ω = fun e => polTable ω.1 e :=
  absDS.polE_eq_of (fun ω e => polTable ω.1 e) (fun _ => rfl) (by decide +kernel)
    (by decide +kernel) ω

/-- Supporting lemma: `Π̈` as a function.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_fun : absDS.polE = fun ω e => polTable ω.1 e := funext polE_eq

/-- Supporting lemma `polOf_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polOf_eq (d : Fin 2 × Fin 3) : absDS.polOf d = fun e => polTable d.2 e := by
  obtain ⟨i, k⟩ := d
  exact polE_eq (k, i, 0)

/-- Supporting lemma `evPolE_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evPolE_eq (π : Fin 2 → Fin 2) :
    absDS.evPolE π = event fun ω => (fun e => polTable ω.1 e) = π := by
  unfold AbstractDS.evPolE
  exact event_congr fun ω => by rw [polE_eq]

/-- **`Three` is decision-determined**: `U` is a function of `E`, and `E ⊥ D_{I,B} ∣ Π̈` (the
internal coordinate `i` is ignored by the environment).
Source: mandate T9(a) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem decisionDetermined : absDS.DecisionDetermined := by
  refine ⟨fun ω ω' h => ?_, fun e d => ?_⟩
  · have h2 : ω.2.2 = ω'.2.2 := (Prod.mk.inj h).2
    show (if Q ω then (1 : ℝ) else 0) = if Q ω' then 1 else 0
    have hq : Q ω ↔ Q ω' := by unfold Q; rw [h2]
    exact if_congr hq rfl rfl
  · have hev : (event fun ω => absDS.E ω = e ∧ absDS.polE ω = absDS.polOf d) =
        event fun ω => absDS.E ω = e ∧ (fun e' => polTable ω.1 e') = fun e' => polTable d.2 e' :=
      event_congr fun ω => by rw [polE_eq, polOf_eq]
    rw [hev, evPolE_eq, polOf_eq]
    exact weights.mass_mul_eq_of_cnt (dd_key e d)
where
  /-- the count identity behind clause (2) -/
  dd_key : ∀ (e : Fin 2 × Fin 2) (d : Fin 2 × Fin 3),
      weights.cnt (event fun ω : Ω => absDS.E ω = e ∧ absDS.DIB ω = d) *
          weights.cnt (event fun ω : Ω => (fun e' => polTable ω.1 e') = fun e' => polTable d.2 e') =
        weights.cnt (event fun ω : Ω =>
            absDS.E ω = e ∧ (fun e' => polTable ω.1 e') = fun e' => polTable d.2 e') *
          weights.cnt (absDS.evDIB d) := by decide +kernel

/-- **`Π̈` is not a function of `E` on `Three`**: the worlds `(0, 0, 0)` and `(1, 0, 0)` share
`E = (0, 0)` and run different policies.
Source: mandate T9(a) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_isSubvariable : ¬ IsSubvariable absDS.E absDS.polE := by
  rw [polE_fun]
  decide +kernel

/-- **Non-degeneracy**: `Π̈` is non-constant; `D_{I,B}` has more values than `Π̈` (DD is not the
trivial identity of atoms); two worlds differ in both `Π̈` and `E` (weaker than "`E` depends on
`Π̈`", which holds by construction, `Ä = Π̈(Ö)`, but is not what this clause states).
Source: mandate T9(a) (witness, N+)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem nondegenerate :
    (∃ ω ω', absDS.polE ω ≠ absDS.polE ω') ∧
      (∃ ω ω', absDS.DIB ω ≠ absDS.DIB ω' ∧ absDS.polE ω = absDS.polE ω') ∧
      (∃ ω ω', absDS.polE ω ≠ absDS.polE ω' ∧ absDS.E ω ≠ absDS.E ω') := by
  rw [polE_fun]
  refine ⟨⟨(0, 0, 0), (1, 0, 0), by decide +kernel⟩, ⟨(0, 0, 0), (0, 1, 0), by decide +kernel,
    by decide +kernel⟩, ⟨(0, 0, 1), (1, 0, 1), by decide +kernel, by decide +kernel⟩⟩

/-- **"`Π̈` is a perfect condensation variable" is false on a decision-determined structure
(T9(a), load-bearing 3, refutation)**: `Three` is decision-determined, `Π̈` is non-constant, and the
policy latent model does not perfectly condense `(D_{I,B}, E)`, because `Π̈` is not a function of
`E` while perfect condensation forces it to be one (`aeFunctionOf_polE_of_perfectlyCondenses`).
Reading of record as in `Latent.lean` (ATTRIBUTION-UNVETTED).
Source: [[topics/decision-determination]] line 99 (udt-rep-045; findings §6.5)
Kind: N+
Fidelity: exact (refutation of the quoted sentence in Eisenstat's sense)
Hyps: none -/
theorem dd_not_perfectlyCondenses :
    absDS.DecisionDetermined ∧ ¬ (polLatent absDS).PerfectlyCondenses :=
  ⟨decisionDetermined, not_perfectlyCondenses_of_not_isSubvariable absDS not_isSubvariable⟩

/-- **`H[Π̈ | E] > 0` on `Three`** is what fails; stated in the form the refutation actually uses
(`Π̈` not a.e. a function of `E`, by T7(a)).
Source: mandate T9(a)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_aeFunctionOf : ¬ AEFunctionOf absDS.E absDS.polE (dsMeasure absDS) :=
  fun h => not_isSubvariable ((isSubvariable_iff_aeFunctionOf absDS _ _).2 h)

end Three

/-! ### The positive instance: `polLatent` of `Xor` perfectly condenses, non-degenerately -/

namespace Xor

/-- Worlds `(k, i, j)`: policy index, internal dynamic, external observation.
Source: mandate T9(a),(b) (positive instance); r2 adversarial audit B1
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := Fin 2 × Fin 2 × Fin 2

/-- The two non-constant policies: `k = 0` the identity, `k = 1` the flip.
Source: mandate T9(a),(b) (positive instance)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def polTable (k : Fin 2) (e : Fin 2) : Fin 2 :=
  if k = 0 then e else if e = 0 then 1 else 0

/-- Uniform weights on the eight worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt _ := 1
  pos _ := by norm_num
  N := 8
  sum_eq := by decide +kernel

/-- The utility indicator `j = 1` (a function of `E`).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Q (ω : Ω) : Prop := ω.2.2 = 1

instance (ω : Ω) : Decidable (Q ω) := by unfold Q; infer_instance

/-- A policy index realizing action `a` at observation `e` (for the environment-dynamic
factorization): the identity if `a = e`, the flip otherwise.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def kFor (a e : Fin 2) : Fin 2 := if a = e then 0 else 1

/-- **`Xor` as an abstract decision structure** (the fields mirror `Three`'s).
Source: mandate T9(a),(b) (positive instance); r2 adversarial audit B1
Kind: N+
Fidelity: n/a
Hyps: none -/
def absDS : AbstractDS Ω (Fin 1) (Fin 2) (Fin 1) (Fin 2) (Fin 2) (Fin 2) (Fin 2) (Fin 1) (Fin 1)
    where
  μ := weights.dist
  pos := weights.w_pos
  oI _ := 0
  oE ω := ω.2.2
  aI _ := 0
  aE ω := polTable ω.1 ω.2.2
  dI ω := ω.2.1
  dE ω := ω.2.2
  dB ω := ω.1
  oH _ := 0
  oC _ := 0
  polS ω := fun _ => (0, polTable ω.1 0)
  U ω := if Q ω then 1 else 0
  U_mem ω := by split_ifs <;> simp
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_chain (by decide +kernel) (by decide +kernel)
    (fun ω ω' => (ω'.1, ω.2.1, ω'.2.2)) (by decide +kernel)
  BE_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := factorsAs_of_fun (fun ω₁ ω₂ => (kFor (polTable ω₁.1 ω₁.2.2) ω₂.2.2, 0, ω₂.2.2))
    (by decide +kernel)
  B_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₂.1, 0, ω₁.2.2)) (by decide +kernel)
  IB_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₂.1, ω₂.2.1, ω₁.2.2)) (by decide +kernel)
  IB_det := by decide +kernel
  O_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- `Π̈` on `Xor`: the policy table at `k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : absDS.polE ω = fun e => polTable ω.1 e :=
  absDS.polE_eq_of (fun ω e => polTable ω.1 e) (fun _ => rfl) (by decide +kernel)
    (by decide +kernel) ω

/-- Supporting lemma: `Π̈` as a function.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_fun : absDS.polE = fun ω e => polTable ω.1 e := funext polE_eq

/-- Supporting lemma `polOf_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polOf_eq (d : Fin 2 × Fin 2) : absDS.polOf d = fun e => polTable d.2 e := by
  obtain ⟨i, k⟩ := d
  exact polE_eq (k, i, 0)

/-- Supporting lemma `evPolE_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evPolE_eq (π : Fin 2 → Fin 2) :
    absDS.evPolE π = event fun ω => (fun e => polTable ω.1 e) = π := by
  unfold AbstractDS.evPolE
  exact event_congr fun ω => by rw [polE_eq]

/-- **`Xor` is decision-determined**: `U` is a function of `E`, and `E ⊥ D_{I,B} ∣ Π̈` (the
internal coordinate `i` is ignored by the environment).
Source: mandate T9(a),(b) (positive instance)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem decisionDetermined : absDS.DecisionDetermined := by
  refine ⟨fun ω ω' h => ?_, fun e d => ?_⟩
  · have h2 : ω.2.2 = ω'.2.2 := (Prod.mk.inj h).2
    show (if Q ω then (1 : ℝ) else 0) = if Q ω' then 1 else 0
    have hq : Q ω ↔ Q ω' := by unfold Q; rw [h2]
    exact if_congr hq rfl rfl
  · have hev : (event fun ω => absDS.E ω = e ∧ absDS.polE ω = absDS.polOf d) =
        event fun ω => absDS.E ω = e ∧ (fun e' => polTable ω.1 e') = fun e' => polTable d.2 e' :=
      event_congr fun ω => by rw [polE_eq, polOf_eq]
    rw [hev, evPolE_eq, polOf_eq]
    exact weights.mass_mul_eq_of_cnt (dd_key e d)
where
  /-- the count identity behind clause (2) -/
  dd_key : ∀ (e : Fin 2 × Fin 2) (d : Fin 2 × Fin 2),
      weights.cnt (event fun ω : Ω => absDS.E ω = e ∧ absDS.DIB ω = d) *
          weights.cnt (event fun ω : Ω => (fun e' => polTable ω.1 e') = fun e' => polTable d.2 e') =
        weights.cnt (event fun ω : Ω =>
            absDS.E ω = e ∧ (fun e' => polTable ω.1 e') = fun e' => polTable d.2 e') *
          weights.cnt (absDS.evDIB d) := by decide +kernel

/-- **`Π̈ ⊑ E` on `Xor`**: the policy is recovered from `(Ä, Ö)` as `k = [Ä ≠ Ö]`.
Source: mandate T9(a),(b) (positive instance)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem isSubvariable : IsSubvariable absDS.E absDS.polE := by
  rw [polE_fun]
  decide +kernel

/-- **Non-degeneracy, in the respects `NoSub` lacks.** (1) `E` is not injective; (2) `Π̈` is not a
function of `Ä` alone; (3) `Π̈` is not a function of `D_E` alone; (4) `D_{I,B}` has more values
than `Π̈` (DD is not the identity of atoms); (5) both policies are non-constant; (6) `Π̈` is
non-constant.
Source: mandate T9(a),(b) (positive instance, N+); r2 adversarial audit B1
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem nondegenerate :
    (∃ ω ω', ω ≠ ω' ∧ absDS.E ω = absDS.E ω') ∧
      ¬ IsSubvariable absDS.aE absDS.polE ∧
      ¬ IsSubvariable absDS.dE absDS.polE ∧
      (∃ ω ω', absDS.DIB ω ≠ absDS.DIB ω' ∧ absDS.polE ω = absDS.polE ω') ∧
      (polTable 0 0 ≠ polTable 0 1 ∧ polTable 1 0 ≠ polTable 1 1) ∧
      (∃ ω ω', absDS.polE ω ≠ absDS.polE ω') := by
  rw [polE_fun]
  refine ⟨⟨(0, 0, 0), (0, 1, 0), by decide, by decide +kernel⟩, by decide +kernel, by decide +kernel,
    ⟨(0, 0, 0), (0, 1, 0), by decide +kernel, by decide +kernel⟩, by decide,
    ⟨(0, 0, 0), (1, 0, 0), by decide +kernel⟩⟩

/-- **The policy latent of `Xor` perfectly condenses `(D_{I,B}, E)` (T9, positive instance)** — a
decision-determined structure with `Π̈ ⊑ E` in which neither `E = id` nor `Π̈ ≅ D_{I,B}` does the
work (`nondegenerate`). So `Three.dd_not_perfectlyCondenses` is not an artifact of an encoding
nothing satisfies: the same `polLatent` admits both verdicts, and the dividing line is exactly
`Π̈ ⊑ E` (`perfectlyCondenses_polLatent_iff_isSubvariable_of_dd`).
Source: [[topics/decision-determination]] line 99 (udt-rep-045); mandate T9(a),(b); r2 adversarial audit B1
Kind: N+
Fidelity: n/a (the positive instance of the T9(b) equivalence)
Hyps: none -/
theorem perfectlyCondenses : (polLatent absDS).PerfectlyCondenses :=
  (perfectlyCondenses_polLatent_iff_isSubvariable_of_dd absDS decisionDetermined).2 isSubvariable

end Xor

/-! ### The satisfiability check `NoSubPerfect` (N−: `E` is the identity on `NoSub`) -/

namespace NoSubPerfect

/-- On `udt-comm-trust`'s `NoSub`, `Π̈` is a function of `E` (everywhere on the support).
Source: mandate T9(a) (satisfiability check); r1 adversarial audit §3.2
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem isSubvariable : IsSubvariable NoSub.absDS.E NoSub.absDS.polE := by
  rw [show NoSub.absDS.polE = fun ω _ => ω.1 from funext NoSub.polE_eq]
  decide +kernel

/-- `Π̈` is non-constant on `NoSub`.
Source: mandate T9(a) (satisfiability check)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem polE_nonconst : ∃ ω ω', NoSub.absDS.polE ω ≠ NoSub.absDS.polE ω' := by
  refine ⟨(0, 0), (1, 0), ?_⟩
  rw [NoSub.polE_eq, NoSub.polE_eq]
  decide

/-- **The degeneracy, stated**: on `NoSub`, `E` is injective (`E ω = (ω.1, ω.2)`).
Source: r2 adversarial audit B1 (probe `PerfectNondegenerate.lean`, lifted)
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem E_injective : Function.Injective NoSub.absDS.E := by
  intro ω ω' h
  exact Prod.ext (Prod.mk.inj h).1 (Prod.mk.inj h).2

/-- Hence on `NoSub` the function clause `Π̈ ⊑ E` holds for *any* variable, not because of anything
about the policy: every `Ω`-indexed variable is a subvariable of `E`.
Source: r2 adversarial audit B1
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem everything_sub_E {V : Type} (X : NoSub.Ω → V) : IsSubvariable NoSub.absDS.E X :=
  fun ω ω' h => by rw [E_injective h]

/-- And `D_{I,B}` is a function of `Π̈` on `NoSub`: DD there is the identity of atoms up to
relabelling, so the Markov clause is the trivial one too.
Source: r2 adversarial audit B1
Kind: N−
Fidelity: n/a
Hyps: none -/
theorem DIB_sub_polE : IsSubvariable NoSub.absDS.polE NoSub.absDS.DIB := by
  rw [show NoSub.absDS.polE = fun ω _ => ω.1 from funext NoSub.polE_eq]
  decide +kernel

/-- **`polLatent NoSub.absDS` perfectly condenses `(D_{I,B}, E)` (T9, satisfiability check, N−)**:
`NoSub` is decision-determined with `Π̈ ⊑ E` and `Π̈` non-constant, so the encoding is satisfiable
by a DD structure. **Degenerate** (regraded N− in repair round 2): `E` is injective on `NoSub`
(`E_injective`), so the function clause holds for every variable (`everything_sub_E`) and
`D_{I,B} ⊑ Π̈` (`DIB_sub_polE`) — the verdict is forced by `E = id`, not by the policy. The
non-degenerate positive instance is `Xor.perfectlyCondenses`.
Source: [[topics/decision-determination]] line 99 (udt-rep-045); mandate T9(a); r1 adversarial audit §3.2; r2 adversarial audit B1
Kind: N−
Fidelity: n/a (satisfiability only; `E = id` on `NoSub`)
Hyps: none -/
theorem perfectlyCondenses : (polLatent NoSub.absDS).PerfectlyCondenses :=
  (perfectlyCondenses_polLatent_iff_isSubvariable_of_dd NoSub.absDS NoSub.decisionDetermined).2
    isSubvariable

end NoSubPerfect

end

end Cleanroom.Udt.UdtCondenseDd
