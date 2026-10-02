import Cleanroom.Udt.UdtCondenseDd.Entropy
import Cleanroom.Udt.UdtCondenseDd.WitnessLatent

/-!
# `Cleanroom.Udt.UdtCondenseDd.WitnessEntropy`: the N+ witness of the entropy-level approximate DD

Work package `udt-condense-dd`, target T11(c) (repair round 2). `approxDD_entropy`'s hypothesis
`U ⊑ E` is inhabited by every decision-determined structure, but there `I[E : D_{I,B} | Π̈] = 0` and
both sides of the bound vanish (N− for the content). This module builds an instance with `I > 0`
and a positive left-hand side: **`XorSkew`** is `WitnessLatent.Xor` (worlds `(k, i, j)`, two
non-constant policies, `E = (Π̈_k(j), j)`, `U = [j = 1]`) with the prior skewed to correlate the
internal dynamic `i` with the observation `j` (weight `2` on `i = j`, `1` otherwise; total `12`).

* `U ⊑ E` still holds (`U_sub_E`), so the theorem applies (`instance_bound`).
* DD fails (`not_decisionDetermined`): given `Π̈` (i.e. `k`), `E ↔ j` is correlated with
  `D_{I,B} = (i, k)` through `i` — at `e = (1, 1)`, `d = (0, 0)` the division-free identity would
  read `(1/12)(6/12) = (3/12)(3/12)`.
* Hence `I[E : D_{I,B} | Π̈] > 0` (`condMutualInfo_pos`), through the package's own bridge
  `decisionDetermined_iff_condMutualInfo_eq_zero` and FAF's `condMutualInfo_nonneg` — no `log` is
  evaluated.
* The left-hand side is positive (`lhs_pos`): on the atom `d = (0, 0)`, `E[U | D_{I,B} = d] = 1/3`
  (`condExp_atom`) while `E[U | Π̈ = [[d]]] = 1/2` (`policyUtility_atom`).

By hand (not machine-checked): every atom has `P(d) = 1/4` and gap `1/6`, so the left-hand side is
`1/6 ≈ 0.1667`; `I = KL((2/3, 1/3) ‖ (1/2, 1/2)) ≈ 0.0566` nats, so `√(I/2) ≈ 0.1683`; the instance
sits within one percent of the bound, and since `U` is an indicator the mean-shift step is an
equality there, so the only slack is Pinsker's. (The r2 adversarial audit's probe
`EntropyPositive.lean`, lifted.)
-/

namespace Cleanroom.Udt.UdtCondenseDd

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset
open Condensation MeasureTheory ProbabilityTheory

noncomputable section

namespace XorSkew

open Xor

/-- Skewed weights on `Xor`'s eight worlds: `2` on worlds with `i = j`, `1` otherwise (total `12`).
Source: mandate T11(c) (witness); r2 adversarial audit §3.1
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt ω := if ω.2.1 = ω.2.2 then 2 else 1
  pos ω := by split_ifs <;> norm_num
  N := 12
  sum_eq := by decide +kernel

/-- **`XorSkew` as an abstract decision structure** (support-level fields identical to `Xor`'s;
only the prior differs).
Source: mandate T11(c) (witness); r2 adversarial audit §3.1
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

/-- `Π̈` on `XorSkew`: the policy table at `k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : absDS.polE ω = fun e => polTable ω.1 e :=
  absDS.polE_eq_of (fun ω e => polTable ω.1 e) (fun _ => rfl) (by decide +kernel)
    (by decide +kernel) ω

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

/-- DD's clause (1), `U ⊑ E`: the hypothesis of `approxDD_entropy`.
Source: mandate T11(c) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem U_sub_E : IsSubvariable absDS.E absDS.U := by
  intro ω ω' h
  have h2 : ω.2.2 = ω'.2.2 := (Prod.mk.inj h).2
  show (if Q ω then (1 : ℝ) else 0) = if Q ω' then 1 else 0
  have hq : Q ω ↔ Q ω' := by unfold Q; rw [h2]
  exact if_congr hq rfl rfl

/-- **`XorSkew` is not decision-determined**: at `e = (1, 1)`, `d = (0, 0)` the division-free
identity would read `(1/12)(6/12) = (3/12)(3/12)`.
Source: mandate T11(c) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_decisionDetermined : ¬ absDS.DecisionDetermined := by
  intro h
  have key := h.2 (1, 1) (0, 0)
  have hev : (event fun ω => absDS.E ω = (1, 1) ∧ absDS.polE ω = absDS.polOf (0, 0)) =
      event fun ω => absDS.E ω = (1, 1) ∧ (fun e' => polTable ω.1 e') = fun e' => polTable 0 e' :=
    event_congr fun ω => by rw [polE_eq, polOf_eq]
  have hw : absDS.μ.w = weights.w := rfl
  rw [hev, evPolE_eq, polOf_eq, hw, weights.mass_eq_cnt, weights.mass_eq_cnt, weights.mass_eq_cnt,
    weights.mass_eq_cnt] at key
  have c1 : weights.cnt (event fun ω : Ω => absDS.E ω = (1, 1) ∧ absDS.DIB ω = (0, 0)) = 1 := by
    decide +kernel
  have c2 : weights.cnt (event fun ω : Ω => (fun e' => polTable ω.1 e') = fun e' => polTable 0 e') = 6 := by
    decide +kernel
  have c3 : weights.cnt (event fun ω : Ω =>
      absDS.E ω = (1, 1) ∧ (fun e' => polTable ω.1 e') = fun e' => polTable 0 e') = 3 := by
    decide +kernel
  have c4 : weights.cnt (absDS.evDIB (0, 0)) = 3 := by decide +kernel
  rw [c1, c2, c3, c4] at key
  norm_num [weights] at key

/-- **`I[E : D_{I,B} | Π̈] > 0` on `XorSkew`**, through the package's bridge
`decisionDetermined_iff_condMutualInfo_eq_zero` and FAF's `condMutualInfo_nonneg`.
Source: mandate T11(c) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem condMutualInfo_pos : 0 < I[absDS.E : absDS.DIB | absDS.polE ; dsMeasure absDS] := by
  refine lt_of_le_of_ne (ShannonInformation.condMutualInfo_nonneg (measurable_of_countable _)
    (measurable_of_countable _)) fun h0 => ?_
  exact not_decisionDetermined
    ((decisionDetermined_iff_condMutualInfo_eq_zero absDS).2 ⟨U_sub_E, h0.symm⟩)

/-- On the atom `d = (0, 0)`: `E[U | D_{I,B} = d] = 1/3`.
Source: mandate T11(c) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem condExp_atom :
    condExpJunk absDS.μ.w absDS.U (absDS.evDIB (0, 0)) (-1) = 1 / 3 := by
  have h := weights.condExpJunk_indicator Q (E := absDS.evDIB (0, 0)) ⟨(0, 0, 0), by decide⟩ (-1)
  have c1 : weights.cnt ((absDS.evDIB (0, 0)).filter Q) = 1 := by decide +kernel
  have c2 : weights.cnt (absDS.evDIB (0, 0)) = 3 := by decide +kernel
  rw [c1, c2] at h
  rw [show absDS.U = fun ω => if Q ω then (1 : ℝ) else 0 from rfl,
    show absDS.μ.w = weights.w from rfl, h]
  norm_num

/-- On the policy atom `[[d]] = Π̈_0`: `E[U | Π̈ = [[d]]] = 1/2`.
Source: mandate T11(c) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem policyUtility_atom : absDS.policyUtility (absDS.polOf (0, 0)) = 1 / 2 := by
  rw [AbstractDS.policyUtility, polOf_eq, evPolE_eq]
  have h := weights.condExpJunk_indicator Q
    (E := event fun ω : Ω => (fun e => polTable ω.1 e) = fun e => polTable (0, 0).2 e)
    ⟨(0, 0, 0), by decide⟩ (-1)
  have c1 : weights.cnt ((event fun ω : Ω =>
      (fun e => polTable ω.1 e) = fun e => polTable (0, 0).2 e).filter Q) = 3 := by decide +kernel
  have c2 : weights.cnt (event fun ω : Ω =>
      (fun e => polTable ω.1 e) = fun e => polTable (0, 0).2 e) = 6 := by decide +kernel
  rw [c1, c2] at h
  rw [show absDS.U = fun ω => if Q ω then (1 : ℝ) else 0 from rfl,
    show absDS.μ.w = weights.w from rfl, h]
  norm_num

/-- **The left-hand side of `approxDD_entropy` is positive on `XorSkew`**: the `d = (0, 0)` term is
`(3/12) · |1/3 − 1/2| = 1/24 > 0`, and every term is non-negative.
Source: mandate T11(c) (witness)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem lhs_pos :
    0 < ∑ d, mass absDS.μ.w (absDS.evDIB d) *
        |condExpJunk absDS.μ.w absDS.U (absDS.evDIB d) (-1) - absDS.policyUtility (absDS.polOf d)| := by
  have hterm : (0 : ℝ) < mass absDS.μ.w (absDS.evDIB (0, 0)) *
      |condExpJunk absDS.μ.w absDS.U (absDS.evDIB (0, 0)) (-1) -
        absDS.policyUtility (absDS.polOf (0, 0))| := by
    rw [condExp_atom, policyUtility_atom, show absDS.μ.w = weights.w from rfl, weights.mass_eq_cnt]
    have c : weights.cnt (absDS.evDIB (0, 0)) = 3 := by decide +kernel
    rw [c]
    norm_num [weights]
  refine lt_of_lt_of_le hterm (Finset.single_le_sum (f := fun d => mass absDS.μ.w (absDS.evDIB d) *
    |condExpJunk absDS.μ.w absDS.U (absDS.evDIB d) (-1) - absDS.policyUtility (absDS.polOf d)|)
    (fun d _ => mul_nonneg (mass_nonneg (fun ω => absDS.μ.nonneg ω) _) (abs_nonneg _))
    (Finset.mem_univ (0, 0)))

/-- **`approxDD_entropy` instantiated on `XorSkew` (T11(c), N+)**: the full hypothesis package is
inhabited by a structure with `I > 0` (`condMutualInfo_pos`) and a positive left-hand side
(`lhs_pos`), so the instance exercises the bound's content.
Source: mandate T11(c) (witness); r2 adversarial audit §3.1
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem instance_bound :
    ∑ d, mass absDS.μ.w (absDS.evDIB d) *
        |condExpJunk absDS.μ.w absDS.U (absDS.evDIB d) (-1) - absDS.policyUtility (absDS.polOf d)| ≤
      Real.sqrt (I[absDS.E : absDS.DIB | absDS.polE ; dsMeasure absDS] / 2) :=
  approxDD_entropy absDS U_sub_E

end XorSkew

end

end Cleanroom.Udt.UdtCondenseDd
