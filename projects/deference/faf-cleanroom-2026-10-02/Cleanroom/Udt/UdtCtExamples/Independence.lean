import Cleanroom.Udt.UdtCommTrust.Determination
import Cleanroom.Udt.UdtCommTrust.Count
import Cleanroom.Udt.UdtCtExamples.CountExt
import Cleanroom.Udt.UdtCtExamples.Infra
import Cleanroom.Udt.UdtCtExamples.NonInterference

/-!
# `Cleanroom.Udt.UdtCtExamples.Independence`: the write-up's independence packages (T7(a))

Work package `udt-ct-examples`, target T7(a) (bli-paper-2-017). Source: the Claude write-up in
[[udt-tiling-working-notes-2025-06-30]] lines 260–267 and 324–326 (the independence assumptions
`I ⊥ E ∣ B` and `I ⊥ E ∣ Π†` that the write-up states and the LaTeX drops), against the LaTeX's
decision-determination (`DecisionDetermined` of `udt-comm-trust`: `U ⊑ E` and `E ⊥ D_{I,B} ∣ Π̈`).

* `IEIndepB` (`I ⊥ E ∣ B`) and `IEIndepEff` (`I ⊥ E ∣ Π†`), division-free on the support in the
  shape of `DecisionDetermined` clause (2).
* (i) `IEIndepEff` and `DecisionDetermined` are incomparable. The witnesses of record (repair
  round 1, after audit r1 adversarial B3 found the first pair's `Π†` constant): `EffVary`
  (sixteen worlds `((d, k), c)`: `Π† = (k, ·)` varies with the boundary dynamic `k`, `I = (k, d)`,
  `E = (0, c)` with `c` correlated `3 : 1` with `k`; `I ⊥ E ∣ Π†` holds because `d ⊥ c` given `k`,
  `U ⊑ E` holds, and clause (2) of decision-determination fails because `Π̈` is constant while
  `D_B` matters to `E` — the interesting direction) has the first and not the second;
  `DDnotEff` (eight worlds `((d, k), c)`: `Ȯ = d`, `Ä = act d k` with `act d 0 = d`,
  `act d 1 = 0`, so `Π†` is "report the internal observation" at `k = 0` and constant at `k = 1`;
  `c` uniform) has the second and not the first: `Π̈` carries `(d, k)` up to the atom where `Ä`
  agrees, while `Π†` conditions on `k` only and `Ä = d` there. The earlier pair is kept and
  regraded `N−`: `EffNotDD` (four worlds, `Π†` constant, decision-determination failing through
  clause (1) only) and `NI4` (`Π†` the same function at every world).

  A structural remark the witnesses make visible (findings F-8): since `Ä = Π†(Ȯ, Ö)` and
  `Ȯ ⊑ I`, `I ⊥ E ∣ Π†` can only hold when, given `Π†`, the external action does not depend on
  the internal observation — the write-up's independence assumption silently forbids `Π†` from
  reading `Ȯ` at the realized inputs.
* (ii) `IEIndepB` is not implied by the factorization fields: `CorrDyn` (four worlds, `D_I` and
  `D_E` correlated `3 : 1` in law, everything else constant) satisfies every field of
  `AbstractDS` and fails `IEIndepB` (and, for the record, decision-determination's clause (2)).
  The fields are support-level; independence is in law; the LaTeX dropped an underivable
  assumption (findings F-8).
* (iii) What the Communicative Expectation proof needs is `R ⊑ D_{I,B}` (`udt-comm-trust`
  finding 2′); neither package yields it — prose in the report (§T7(a)); no Lean.
-/

namespace Cleanroom.Udt.UdtCtExamples

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

section General

variable {Ω OI OE AI AE DI DE DB OH OC : Type} [Fintype Ω] [DecidableEq Ω]
  [Fintype OI] [Fintype OE] [DecidableEq OI] [DecidableEq OE] [DecidableEq AI] [DecidableEq AE]
  [DecidableEq DI] [DecidableEq DE] [DecidableEq DB]
variable (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC)

/-- **`I ⊥ E ∣ B`**, division-free on the support:
`P(I = i, B = b, E = e) · P(B = b) = P(I = i, B = b) · P(B = b, E = e)`.
Source: [[udt-tiling-working-notes-2025-06-30]] lines 260–267 (bli-paper-2-017)
Kind: D
Fidelity: exact (division-free form)
Hyps: n/a -/
def IEIndepB : Prop := ∀ (i : AI × DI) (b : (OI × OE) × DB) (e : AE × DE),
  mass S.μ.w (event fun ω => S.I ω = i ∧ S.B ω = b ∧ S.E ω = e) *
      mass S.μ.w (event fun ω => S.B ω = b) =
    mass S.μ.w (event fun ω => S.I ω = i ∧ S.B ω = b) *
      mass S.μ.w (event fun ω => S.B ω = b ∧ S.E ω = e)

/-- **`I ⊥ E ∣ Π†`**, division-free on the support.
Source: [[udt-tiling-working-notes-2025-06-30]] lines 324–326 (bli-paper-2-017)
Kind: D
Fidelity: exact (division-free form)
Hyps: n/a -/
noncomputable def IEIndepEff : Prop := ∀ (i : AI × DI) (π : Policy (OI × OE) (AI × AE)) (e : AE × DE),
  mass S.μ.w (event fun ω => S.I ω = i ∧ S.polD ω = π ∧ S.E ω = e) *
      mass S.μ.w (event fun ω => S.polD ω = π) =
    mass S.μ.w (event fun ω => S.I ω = i ∧ S.polD ω = π) *
      mass S.μ.w (event fun ω => S.polD ω = π ∧ S.E ω = e)

end General

/-! ### `EffNotDD`: `I ⊥ E ∣ Π†` without decision-determination -/

namespace EffNotDD

/-- Worlds `(d, e)`: `d` the internal dynamic, `e` the environment dynamic, independent and
uniform; the utility is `d`.
Source: none: infrastructure (mandate T7(a)(i))
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := Fin 2 × Fin 2

/-- Uniform weights on four worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt _ := 1
  pos _ := by norm_num
  N := 4
  sum_eq := by decide +kernel

/-- The utility numerator: the internal dynamic.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def u (ω : Ω) : ℕ := if ω.1 = 1 then 1 else 0

/-- **`EffNotDD` as an abstract decision structure**: `Ȯ = D_I = d`, `D_E = e`, every action and
observation constant, `U = 𝟙[d = 1]`.
Source: mandate T7(a)(i)
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def S : AbstractDS Ω (Fin 2) (Fin 1) (Fin 1) (Fin 1) (Fin 2) (Fin 2) (Fin 1)
    (Fin 1) (Fin 1) where
  μ := weights.dist
  pos := weights.w_pos
  oI ω := ω.1
  oE _ := 0
  aI _ := 0
  aE _ := 0
  dI ω := ω.1
  dE ω := ω.2
  dB _ := 0
  oH _ := 0
  oC _ := 0
  polS _ := fun _ => (0, 0)
  U := natDiv u 1
  U_mem := natDiv_mem u (by norm_num) (fun ω => by unfold u; split_ifs <;> omega)
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_chain (by decide +kernel) (by decide +kernel)
    (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  B_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  IB_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  IB_det := by decide +kernel
  O_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- **`Π†` on `EffNotDD`** is the constant policy.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polD_eq (ω : Ω) : S.polD ω = fun _ => (0, 0) :=
  polD_eq_of S (fun _ _ => (0, 0)) (fun _ => rfl) (fun _ _ _ => rfl) (by decide +kernel) ω

/-- **`I ⊥ E ∣ Π†` holds on `EffNotDD`**: `Π†` is constant and `D_I ⊥ D_E` in law. Degenerate:
the conditioning variable is constant, so the identity is `I ⊥ E` in law (audit r1 adversarial
B3); the non-degenerate witness is `EffVary.ieIndepEff`.
Source: mandate T7(a)(i)
Kind: N−
Fidelity: n/a (`Π†` constant; superseded by `EffVary`)
Hyps: none -/
theorem ieIndepEff : IEIndepEff S := by
  intro i π e
  have h1 : (event fun ω => S.I ω = i ∧ S.polD ω = π ∧ S.E ω = e) =
      event fun ω : Ω => ((0 : Fin 1), ω.1) = i ∧ (fun _ : Fin 2 × Fin 1 => ((0 : Fin 1), (0 : Fin 1))) = π ∧
        ((0 : Fin 1), ω.2) = e :=
    event_congr fun ω => by rw [polD_eq]; rfl
  have h2 : (event fun ω => S.polD ω = π) =
      event fun _ : Ω => (fun _ : Fin 2 × Fin 1 => ((0 : Fin 1), (0 : Fin 1))) = π :=
    event_congr fun ω => by rw [polD_eq]
  have h3 : (event fun ω => S.I ω = i ∧ S.polD ω = π) =
      event fun ω : Ω => ((0 : Fin 1), ω.1) = i ∧ (fun _ : Fin 2 × Fin 1 => ((0 : Fin 1), (0 : Fin 1))) = π :=
    event_congr fun ω => by rw [polD_eq]; rfl
  have h4 : (event fun ω => S.polD ω = π ∧ S.E ω = e) =
      event fun ω : Ω => (fun _ : Fin 2 × Fin 1 => ((0 : Fin 1), (0 : Fin 1))) = π ∧ ((0 : Fin 1), ω.2) = e :=
    event_congr fun ω => by rw [polD_eq]; rfl
  rw [h1, h2, h3, h4]
  exact weights.mass_mul_eq_of_cnt (key i π e)
where
  key : ∀ (i : Fin 1 × Fin 2) (π : Policy (Fin 2 × Fin 1) (Fin 1 × Fin 1)) (e : Fin 1 × Fin 2),
      weights.cnt (event fun ω : Ω => ((0 : Fin 1), ω.1) = i ∧
          (fun _ : Fin 2 × Fin 1 => ((0 : Fin 1), (0 : Fin 1))) = π ∧ ((0 : Fin 1), ω.2) = e) *
        weights.cnt (event fun _ : Ω => (fun _ : Fin 2 × Fin 1 => ((0 : Fin 1), (0 : Fin 1))) = π) =
      weights.cnt (event fun ω : Ω => ((0 : Fin 1), ω.1) = i ∧
          (fun _ : Fin 2 × Fin 1 => ((0 : Fin 1), (0 : Fin 1))) = π) *
        weights.cnt (event fun ω : Ω => (fun _ : Fin 2 × Fin 1 => ((0 : Fin 1), (0 : Fin 1))) = π ∧
          ((0 : Fin 1), ω.2) = e) := by decide +kernel

/-- **Decision-determination fails on `EffNotDD`**: `U` is not a function of `E` (two worlds
with the same environment and different utilities) — clause (1) only; the witness where
`U ⊑ E` holds and clause (2) fails is `EffVary.not_decisionDetermined`.
Source: mandate T7(a)(i)
Kind: N−
Fidelity: n/a (`Π†` constant; fails through clause (1); superseded by `EffVary`)
Hyps: none -/
theorem not_decisionDetermined : ¬ S.DecisionDetermined := fun h => by
  have := h.1 (0, 0) (1, 0) rfl
  have h' : natDiv u 1 (0, 0) = natDiv u 1 (1, 0) := this
  unfold natDiv u at h'
  norm_num at h'

end EffNotDD

/-! ### `NI4` again: decision-determination without `I ⊥ E ∣ Π†` -/

namespace NI4

/-- **`Π̈` on `NI4`**: the constant external policy pressing `k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : S.polE ω = fun _ => ω.1 :=
  S.polE_eq_of (fun ω _ => ω.1) (fun _ => rfl) (by decide +kernel) (by decide +kernel) ω

/-- **`NI4` is decision-determined**: `U = 𝟙[Ä = coin]` is a function of `E = (Ä, coin)`, and
`Π̈` determines `D_{I,B}`.
Source: mandate T7(a)(i)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem decisionDetermined : S.DecisionDetermined := by
  refine ⟨fun ω ω' h => ?_, fun e d => ?_⟩
  · have h' : (ω.1, ω.2) = (ω'.1, ω'.2) := h
    show natDiv u 1 ω = natDiv u 1 ω'
    have : ω = ω' := by rw [← Prod.mk.eta (p := ω), ← Prod.mk.eta (p := ω'), h']
    rw [this]
  · have hpol : ∀ d : Fin 2 × Fin 1, S.polOf d = fun _ => d.1 := fun d => by
      obtain ⟨d1, d2⟩ := d
      have : d2 = 0 := Subsingleton.elim _ _
      subst this
      exact polE_eq (d1, 0)
    have h1 : (event fun ω => S.E ω = e ∧ S.polE ω = S.polOf d) =
        event fun ω : Ω => (ω.1, ω.2) = e ∧ (fun _ : Fin 1 => ω.1) = fun _ => d.1 :=
      event_congr fun ω => by rw [polE_eq, hpol]; rfl
    have h2 : S.evPolE (S.polOf d) = event fun ω : Ω => (fun _ : Fin 1 => ω.1) = fun _ => d.1 := by
      unfold AbstractDS.evPolE
      exact event_congr fun ω => by rw [polE_eq, hpol]
    rw [h1, h2]
    exact weights.mass_mul_eq_of_cnt (dd_key e d)
where
  dd_key : ∀ (e : Fin 2 × Fin 2) (d : Fin 2 × Fin 1),
      weights.cnt (event fun ω : Ω => (ω.1, ω.2) = e ∧ (ω.1, (0 : Fin 1)) = d) *
          weights.cnt (event fun ω : Ω => (fun _ : Fin 1 => ω.1) = fun _ => d.1) =
        weights.cnt (event fun ω : Ω => (ω.1, ω.2) = e ∧ (fun _ : Fin 1 => ω.1) = fun _ => d.1) *
          weights.cnt (event fun ω : Ω => (ω.1, (0 : Fin 1)) = d) := by decide +kernel

/-- **`I ⊥ E ∣ Π†` fails on `NI4`**: `Π†` is the same function at every world while `I = (0, k)`
and `E = (k, coin)` share `k`. Degenerate for the same reason as `EffNotDD` (the conditioning
variable does not vary; audit r1 adversarial B3); the witness with `Π†` varying is
`DDnotEff.not_ieIndepEff`.
Source: mandate T7(a)(i)
Kind: N−
Fidelity: n/a (`Π†` constant; superseded by `DDnotEff`)
Hyps: none -/
theorem not_ieIndepEff : ¬ IEIndepEff S.toAbstractDS := fun h => by
  have := h (0, 0) (fun o => (0, o.1)) (0, 0)
  have h1 : (event fun ω => S.I ω = (0, 0) ∧ S.polD ω = (fun o => (0, o.1)) ∧ S.E ω = (0, 0)) =
      event fun ω : Ω => ω.1 = 0 ∧ ω.2 = 0 :=
    event_congr fun ω => by
      rw [polD_eq]
      show ((0 : Fin 1), ω.1) = (0, 0) ∧ (fun o : Fin 2 × Fin 1 => ((0 : Fin 1), o.1)) = (fun o => (0, o.1)) ∧
        (ω.1, ω.2) = (0, 0) ↔ ω.1 = 0 ∧ ω.2 = 0
      revert ω; decide
  have h2 : (event fun ω => S.polD ω = fun o => (0, o.1)) = (univ : Finset Ω) :=
    event_congr (fun ω => by rw [polD_eq]; exact ⟨fun _ => trivial, fun _ => rfl⟩) |>.trans
      (Finset.filter_true_of_mem fun _ _ => trivial)
  have h3 : (event fun ω => S.I ω = (0, 0) ∧ S.polD ω = fun o => (0, o.1)) =
      event fun ω : Ω => ω.1 = 0 :=
    event_congr fun ω => by
      rw [polD_eq]
      show ((0 : Fin 1), ω.1) = (0, 0) ∧ (fun o : Fin 2 × Fin 1 => ((0 : Fin 1), o.1)) = (fun o => (0, o.1)) ↔
        ω.1 = 0
      revert ω; decide
  have h4 : (event fun ω => S.polD ω = (fun o => (0, o.1)) ∧ S.E ω = (0, 0)) =
      event fun ω : Ω => ω.1 = 0 ∧ ω.2 = 0 :=
    event_congr fun ω => by
      rw [polD_eq]
      show (fun o : Fin 2 × Fin 1 => ((0 : Fin 1), o.1)) = (fun o => (0, o.1)) ∧ (ω.1, ω.2) = (0, 0) ↔
        ω.1 = 0 ∧ ω.2 = 0
      revert ω; decide
  rw [h1, h2, h3, h4] at this
  have hc : weights.cnt (event fun ω : Ω => ω.1 = 0 ∧ ω.2 = 0) * weights.cnt univ ≠
      weights.cnt (event fun ω : Ω => ω.1 = 0) * weights.cnt (event fun ω : Ω => ω.1 = 0 ∧ ω.2 = 0) := by
    decide +kernel
  apply hc
  have := congrArg (fun x => x * (weights.N : ℝ) * weights.N) this
  simp only [show S.μ.w = weights.w from rfl, weights.mass_eq_cnt] at this
  have hN : (weights.N : ℝ) ≠ 0 := by exact_mod_cast weights.N_pos.ne'
  field_simp at this
  exact_mod_cast this

end NI4

/-! ### `EffVary`: `I ⊥ E ∣ Π†` with `Π†` varying, `U ⊑ E`, and clause (2) failing -/

namespace EffVary

/-- Worlds `((d, k), c)`: `d` the internal dynamic (unobserved), `k` the boundary dynamic — which
is also the internal action, so `Π†` varies with it — and `c` the environment dynamic, weighted
`3 : 1` towards `c = k`. The external action is constant, so `Π̈` is constant.
Source: none: infrastructure (mandate T7(a)(i); audit r1 adversarial B3's design)
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := (Fin 2 × Fin 2) × Fin 2

/-- Weights `3 : 1` towards `c = k`; `d` uniform and independent. Total `16`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt ω := if ω.1.2 = ω.2 then 3 else 1
  pos ω := by revert ω; decide
  N := 16
  sum_eq := by decide +kernel

/-- The utility numerator: the environment dynamic `c`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def u (ω : Ω) : ℕ := if ω.2 = 1 then 1 else 0

/-- **`EffVary` as an abstract decision structure**: `Ȧ = D_B = k`, `D_I = d`, `D_E = c`,
observations and the external action constant, `U = 𝟙[c = 1]`, chosen policy `(k, 0)` at every
input.
Source: mandate T7(a)(i); audit r1 adversarial B3
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def S : AbstractDS Ω (Fin 1) (Fin 1) (Fin 2) (Fin 1) (Fin 2) (Fin 2) (Fin 2)
    (Fin 1) (Fin 1) where
  μ := weights.dist
  pos := weights.w_pos
  oI _ := 0
  oE _ := 0
  aI ω := ω.1.2
  aE _ := 0
  dI ω := ω.1.1
  dE ω := ω.2
  dB ω := ω.1.2
  oH _ := 0
  oC _ := 0
  polS ω := fun _ => (ω.1.2, 0)
  U := natDiv u 1
  U_mem := natDiv_mem u (by norm_num) (fun ω => by unfold u; split_ifs <;> omega)
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_chain (by decide +kernel) (by decide +kernel)
    (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  I_fac := factorsAs_of_fun (fun ω₁ ω₂ => ((ω₂.1.1, ω₁.1.2), ω₁.2)) (by decide +kernel)
  E_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  B_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  IB_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  IB_det := by decide +kernel
  O_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  A_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm

/-- **`Π†` on `EffVary`** is `(k, 0)` at every input: it varies with the boundary dynamic.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polD_eq (ω : Ω) : S.polD ω = fun _ => (ω.1.2, 0) :=
  polD_eq_of S (fun ω _ => (ω.1.2, 0)) (fun _ => rfl)
    (fun ω ω' h => by have h' : ω.1.2 = ω'.1.2 := h; simp only [h'])
    (by
      show ∀ (ω : Ω) (o : Fin 1 × Fin 1), ∃ ω' : Ω, ω'.1.2 = ω.1.2 ∧ ((0 : Fin 1), (0 : Fin 1)) = o
      decide +kernel) ω

/-- **`Π†` is not constant on `EffVary`** (the non-degeneracy the audit asked for).
Source: audit r1 adversarial B3
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polD_varies : S.polD ((0, 0), 0) ≠ S.polD ((0, 1), 0) := by
  rw [polD_eq, polD_eq]; decide

/-- **`Π̈` on `EffVary`** is constant.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : S.polE ω = fun _ => 0 :=
  S.polE_eq_of (fun _ _ => 0) (fun _ => rfl) (fun _ _ _ => rfl)
    (by
      show ∀ (ω : Ω) (e : Fin 1), ∃ ω' : Ω, (ω'.1.1, ω'.1.2) = (ω.1.1, ω.1.2) ∧ (0 : Fin 1) = e
      decide +kernel) ω

/-- **`I ⊥ E ∣ Π†` holds on `EffVary`**, with `Π†`, `I` and `E` all varying: given `Π† = (k, ·)`,
`I = (k, d)` and `E = (0, c)` are independent because `d ⊥ c` given `k`.
Source: [[udt-tiling-working-notes-2025-06-30]] lines 324–326; mandate T7(a)(i)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem ieIndepEff : IEIndepEff S := by
  intro i π e
  have h1 : (event fun ω => S.I ω = i ∧ S.polD ω = π ∧ S.E ω = e) =
      event fun ω : Ω => (ω.1.2, ω.1.1) = i ∧
        (fun _ : Fin 1 × Fin 1 => (ω.1.2, (0 : Fin 1))) = π ∧ ((0 : Fin 1), ω.2) = e :=
    event_congr fun ω => by rw [polD_eq]; try exact Iff.rfl
  have h2 : (event fun ω => S.polD ω = π) =
      event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => (ω.1.2, (0 : Fin 1))) = π :=
    event_congr fun ω => by rw [polD_eq]
  have h3 : (event fun ω => S.I ω = i ∧ S.polD ω = π) =
      event fun ω : Ω => (ω.1.2, ω.1.1) = i ∧ (fun _ : Fin 1 × Fin 1 => (ω.1.2, (0 : Fin 1))) = π :=
    event_congr fun ω => by rw [polD_eq]; try exact Iff.rfl
  have h4 : (event fun ω => S.polD ω = π ∧ S.E ω = e) =
      event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => (ω.1.2, (0 : Fin 1))) = π ∧ ((0 : Fin 1), ω.2) = e :=
    event_congr fun ω => by rw [polD_eq]; try exact Iff.rfl
  rw [h1, h2, h3, h4]
  exact weights.mass_mul_eq_of_cnt (key i π e)
where
  key : ∀ (i : Fin 2 × Fin 2) (π : Policy (Fin 1 × Fin 1) (Fin 2 × Fin 1)) (e : Fin 1 × Fin 2),
      weights.cnt (event fun ω : Ω => (ω.1.2, ω.1.1) = i ∧
          (fun _ : Fin 1 × Fin 1 => (ω.1.2, (0 : Fin 1))) = π ∧ ((0 : Fin 1), ω.2) = e) *
        weights.cnt (event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => (ω.1.2, (0 : Fin 1))) = π) =
      weights.cnt (event fun ω : Ω => (ω.1.2, ω.1.1) = i ∧
          (fun _ : Fin 1 × Fin 1 => (ω.1.2, (0 : Fin 1))) = π) *
        weights.cnt (event fun ω : Ω => (fun _ : Fin 1 × Fin 1 => (ω.1.2, (0 : Fin 1))) = π ∧
          ((0 : Fin 1), ω.2) = e) := by decide +kernel

/-- Supporting lemma: `U` is a function of `E`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_of_E : ∀ ω ω' : Ω, ((0 : Fin 1), ω.2) = ((0 : Fin 1), ω'.2) → u ω = u ω' := by
  decide +kernel

/-- **Clause (1) of decision-determination holds on `EffVary`**: `U ⊑ E`.
Source: mandate T7(a)(i)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem U_sub_E : IsSubvariable S.E S.U := by
  intro ω ω' h
  show natDiv u 1 ω = natDiv u 1 ω'
  unfold natDiv
  rw [u_of_E ω ω' h]

/-- **Decision-determination fails on `EffVary` through clause (2)** while clause (1) holds:
`Π̈` is constant, so its atom is `Ω`, where `E = (0, c)` is correlated with `D_{I,B} = (d, k)`
(`c` leans `3 : 1` towards `k`). At `e = (0, c = 1)`, `d = (0, 1)` the identity reads
`3 · 16 = 8 · 4`. `D_B` matters to `E` beyond `Π̈` — exactly what `I ⊥ E ∣ Π†` does not exclude.
Source: mandate T7(a)(i); audit r1 adversarial B3
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_decisionDetermined : ¬ S.DecisionDetermined := fun h => by
  have := h.2 (0, 1) (0, 1)
  have hpol : S.polOf (0, 1) = fun _ => 0 := polE_eq ((0, 1), 0)
  have h1 : (event fun ω => S.E ω = (0, 1) ∧ S.DIB ω = (0, 1)) =
      event fun ω : Ω => ((0 : Fin 1), ω.2) = (0, 1) ∧ (ω.1.1, ω.1.2) = (0, 1) :=
    event_congr fun ω => Iff.rfl
  have h2 : S.evPolE (S.polOf (0, 1)) =
      event fun ω : Ω => (fun _ : Fin 1 => (0 : Fin 1)) = fun _ => 0 := by
    unfold AbstractDS.evPolE
    exact event_congr fun ω => by rw [polE_eq, hpol]
  have h3 : (event fun ω => S.E ω = (0, 1) ∧ S.polE ω = S.polOf (0, 1)) =
      event fun ω : Ω => ((0 : Fin 1), ω.2) = (0, 1) ∧
        (fun _ : Fin 1 => (0 : Fin 1)) = fun _ => 0 :=
    event_congr fun ω => by rw [polE_eq, hpol]; try exact Iff.rfl
  have h4 : S.evDIB (0, 1) = event fun ω : Ω => (ω.1.1, ω.1.2) = (0, 1) :=
    event_congr fun ω => Iff.rfl
  rw [h1, h2, h3, h4] at this
  have hc : weights.cnt (event fun ω : Ω => ((0 : Fin 1), ω.2) = (0, 1) ∧ (ω.1.1, ω.1.2) = (0, 1)) *
      weights.cnt (event fun ω : Ω => (fun _ : Fin 1 => (0 : Fin 1)) = fun _ => 0) ≠
    weights.cnt (event fun ω : Ω => ((0 : Fin 1), ω.2) = (0, 1) ∧
        (fun _ : Fin 1 => (0 : Fin 1)) = fun _ => 0) *
      weights.cnt (event fun ω : Ω => (ω.1.1, ω.1.2) = (0, 1)) := by
    decide +kernel
  apply hc
  have := congrArg (fun x => x * (weights.N : ℝ) * weights.N) this
  simp only [show S.μ.w = weights.w from rfl, weights.mass_eq_cnt] at this
  have hN : (weights.N : ℝ) ≠ 0 := by exact_mod_cast weights.N_pos.ne'
  field_simp at this
  exact_mod_cast this

/-- `I` on `EffVary` is `(k, d)` (by definition).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem I_eq (ω : Ω) : S.I ω = (ω.1.2, ω.1.1) := rfl

/-- `E` on `EffVary` is `(0, c)` (by definition).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem E_eq (ω : Ω) : S.E ω = (0, ω.2) := rfl

/-- **`I` and `E` are dependent unconditionally on `EffVary`**: at `i = (0, 0)`, `e = (0, 0)`,
`P(I = i, E = e) · N ≠ P(I = i) · P(E = e)` in count units (`3 · 16 ≠ 4 · 8`). So `ieIndepEff`'s
identity holds *because* conditioning on `Π†` fixes `k` — the conditioning does real work, not a
reason unrelated to it. Lifted from the audit-r2 probe `EffVaryUnconditional` (repair round 2).
Source: audit r2 (adversarial N2); findings F-8
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem I_E_dependent :
    weights.cnt (event fun ω : Ω =>
        (ω.1.2, ω.1.1) = ((0 : Fin 2), (0 : Fin 2)) ∧ ((0 : Fin 1), ω.2) = ((0 : Fin 1), (0 : Fin 2))) *
      weights.N ≠
    weights.cnt (event fun ω : Ω => (ω.1.2, ω.1.1) = ((0 : Fin 2), (0 : Fin 2))) *
      weights.cnt (event fun ω : Ω => ((0 : Fin 1), ω.2) = ((0 : Fin 1), (0 : Fin 2))) := by
  decide +kernel

end EffVary

/-! ### `DDnotEff`: decision-determination with `Π†` varying, without `I ⊥ E ∣ Π†` -/

namespace DDnotEff

/-- Worlds `((d, k), c)`: `d` the internal dynamic and internal observation, `k` the boundary
dynamic selecting the chosen policy, `c` the environment dynamic (a coin). Uniform.
Source: none: infrastructure (mandate T7(a)(i))
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := (Fin 2 × Fin 2) × Fin 2

/-- Uniform weights on eight worlds.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt _ := 1
  pos _ := by norm_num
  N := 8
  sum_eq := by decide +kernel

/-- The external action of dynamics `(d, k)`: report the internal observation `d` when `k = 0`,
press `0` when `k = 1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def act (d k : Fin 2) : Fin 2 := if k = 0 then d else 0

/-- The utility numerator: `1` iff the external action matches the coin.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def u (ω : Ω) : ℕ := if act ω.1.1 ω.1.2 = ω.2 then 1 else 0

/-- **`DDnotEff` as an abstract decision structure**: `Ȯ = D_I = d`, `D_B = k`, `D_E = c`,
`Ä = act d k`, chosen policy `o ↦ (0, act o.1 k)`, `U = 𝟙[Ä = c]`.
Source: mandate T7(a)(i)
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def S : AbstractDS Ω (Fin 2) (Fin 1) (Fin 1) (Fin 2) (Fin 2) (Fin 2) (Fin 2)
    (Fin 1) (Fin 1) where
  μ := weights.dist
  pos := weights.w_pos
  oI ω := ω.1.1
  oE _ := 0
  aI _ := 0
  aE ω := act ω.1.1 ω.1.2
  dI ω := ω.1.1
  dE ω := ω.2
  dB ω := ω.1.2
  oH _ := 0
  oC _ := 0
  polS ω := fun o => (0, act o.1 ω.1.2)
  U := natDiv u 1
  U_mem := natDiv_mem u (by norm_num) (fun ω => by unfold u; split_ifs <;> omega)
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_chain (by decide +kernel) (by decide +kernel)
    (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := factorsAs_of_fun (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  B_fac := factorsAs_of_fun (fun ω₁ ω₂ => ((ω₁.1.1, ω₂.1.2), ω₁.2)) (by decide +kernel)
  IB_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  IB_det := by decide +kernel
  O_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- **`Π̈` on `DDnotEff`**: the constant external policy pressing `act d k`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polE_eq (ω : Ω) : S.polE ω = fun _ => act ω.1.1 ω.1.2 :=
  S.polE_eq_of (fun ω _ => act ω.1.1 ω.1.2) (fun _ => rfl)
    (by
      show ∀ ω ω' : Ω, (ω.1.1, ω.1.2) = (ω'.1.1, ω'.1.2) →
        (fun _ : Fin 1 => act ω.1.1 ω.1.2) = fun _ => act ω'.1.1 ω'.1.2
      decide +kernel)
    (by
      show ∀ (ω : Ω) (e : Fin 1), ∃ ω' : Ω, (ω'.1.1, ω'.1.2) = (ω.1.1, ω.1.2) ∧ (0 : Fin 1) = e
      decide +kernel) ω

/-- Supporting lemma `polOf_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polOf_eq (d : Fin 2 × Fin 2) : S.polOf d = fun _ => act d.1 d.2 := by
  obtain ⟨d1, d2⟩ := d
  exact polE_eq ((d1, d2), 0)

/-- Supporting lemma `evPolE_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evPolE_eq (π : Fin 1 → Fin 2) :
    S.evPolE π = event fun ω : Ω => (fun _ : Fin 1 => act ω.1.1 ω.1.2) = π := by
  unfold AbstractDS.evPolE
  exact event_congr fun ω => by rw [polE_eq]

/-- **`Π†` on `DDnotEff`**: `o ↦ (0, act o.1 k)` — "report what you observe" at `k = 0`,
constant at `k = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polD_eq (ω : Ω) : S.polD ω = fun o => (0, act o.1 ω.1.2) :=
  polD_eq_of S (fun ω o => (0, act o.1 ω.1.2)) (fun _ => rfl)
    (fun ω ω' h => by have h' : ω.1.2 = ω'.1.2 := h; simp only [h'])
    (by
      show ∀ (ω : Ω) (o : Fin 2 × Fin 1), ∃ ω' : Ω, ω'.1.2 = ω.1.2 ∧ (ω'.1.1, (0 : Fin 1)) = o
      decide +kernel) ω

/-- **`Π†` is not constant on `DDnotEff`**.
Source: audit r1 adversarial B3
Kind: L
Fidelity: n/a
Hyps: none -/
theorem polD_varies : S.polD ((0, 0), 0) ≠ S.polD ((0, 1), 0) := by
  rw [polD_eq, polD_eq]; decide

/-- Supporting lemma: `U` is a function of `E`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem u_of_E : ∀ ω ω' : Ω,
    (act ω.1.1 ω.1.2, ω.2) = (act ω'.1.1 ω'.1.2, ω'.2) → u ω = u ω' := by decide +kernel

/-- Supporting lemma: clause (2) as a count identity.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem dd_key : ∀ (e : Fin 2 × Fin 2) (d : Fin 2 × Fin 2),
    weights.cnt (event fun ω : Ω => (act ω.1.1 ω.1.2, ω.2) = e ∧ (ω.1.1, ω.1.2) = d) *
        weights.cnt (event fun ω : Ω => (fun _ : Fin 1 => act ω.1.1 ω.1.2) = fun _ => act d.1 d.2) =
      weights.cnt (event fun ω : Ω => (act ω.1.1 ω.1.2, ω.2) = e ∧
          (fun _ : Fin 1 => act ω.1.1 ω.1.2) = fun _ => act d.1 d.2) *
        weights.cnt (event fun ω : Ω => (ω.1.1, ω.1.2) = d) := by
  decide +kernel

/-- **`DDnotEff` is decision-determined**: `U = 𝟙[Ä = c]` is a function of `E = (Ä, c)`, and
the coin is independent of everything, so `E ⊥ D_{I,B} ∣ Π̈`.
Source: mandate T7(a)(i)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem decisionDetermined : S.DecisionDetermined := by
  refine ⟨fun ω ω' h => ?_, fun e d => ?_⟩
  · show natDiv u 1 ω = natDiv u 1 ω'
    unfold natDiv
    rw [u_of_E ω ω' h]
  · have hev : (event fun ω => S.E ω = e ∧ S.polE ω = S.polOf d) =
        event fun ω : Ω => (act ω.1.1 ω.1.2, ω.2) = e ∧
          (fun _ : Fin 1 => act ω.1.1 ω.1.2) = fun _ => act d.1 d.2 :=
      event_congr fun ω => by rw [polE_eq, polOf_eq]; try exact Iff.rfl
    rw [hev, evPolE_eq, polOf_eq]
    exact weights.mass_mul_eq_of_cnt (dd_key e d)

/-- **`I ⊥ E ∣ Π†` fails on `DDnotEff`** with `Π†` varying: given `Π† = "report the
observation"` (`k = 0`), `I = (0, d)` and `E = (d, c)` share `d`. At `i = (0, 0)`, `e = (0, 0)`
the identity reads `1 · 4 = 2 · 1`. (`Π̈` carries `d` on the `k = 0` atom; `Π†` does not.)
Source: mandate T7(a)(i); audit r1 adversarial B3
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_ieIndepEff : ¬ IEIndepEff S := fun h => by
  have := h (0, 0) (fun o => (0, o.1)) (0, 0)
  have h1 : (event fun ω => S.I ω = (0, 0) ∧ S.polD ω = (fun o => (0, o.1)) ∧ S.E ω = (0, 0)) =
      event fun ω : Ω => ((0 : Fin 1), ω.1.1) = (0, 0) ∧
        (fun o : Fin 2 × Fin 1 => ((0 : Fin 1), act o.1 ω.1.2)) = (fun o => (0, o.1)) ∧
        (act ω.1.1 ω.1.2, ω.2) = (0, 0) :=
    event_congr fun ω => by rw [polD_eq]; try exact Iff.rfl
  have h2 : (event fun ω => S.polD ω = fun o => (0, o.1)) =
      event fun ω : Ω =>
        (fun o : Fin 2 × Fin 1 => ((0 : Fin 1), act o.1 ω.1.2)) = (fun o => (0, o.1)) :=
    event_congr fun ω => by rw [polD_eq]
  have h3 : (event fun ω => S.I ω = (0, 0) ∧ S.polD ω = fun o => (0, o.1)) =
      event fun ω : Ω => ((0 : Fin 1), ω.1.1) = (0, 0) ∧
        (fun o : Fin 2 × Fin 1 => ((0 : Fin 1), act o.1 ω.1.2)) = (fun o => (0, o.1)) :=
    event_congr fun ω => by rw [polD_eq]; try exact Iff.rfl
  have h4 : (event fun ω => S.polD ω = (fun o => (0, o.1)) ∧ S.E ω = (0, 0)) =
      event fun ω : Ω =>
        (fun o : Fin 2 × Fin 1 => ((0 : Fin 1), act o.1 ω.1.2)) = (fun o => (0, o.1)) ∧
        (act ω.1.1 ω.1.2, ω.2) = (0, 0) :=
    event_congr fun ω => by rw [polD_eq]; try exact Iff.rfl
  rw [h1, h2, h3, h4] at this
  have hc : weights.cnt (event fun ω : Ω => ((0 : Fin 1), ω.1.1) = (0, 0) ∧
        (fun o : Fin 2 × Fin 1 => ((0 : Fin 1), act o.1 ω.1.2)) = (fun o => (0, o.1)) ∧
        (act ω.1.1 ω.1.2, ω.2) = (0, 0)) *
      weights.cnt (event fun ω : Ω =>
        (fun o : Fin 2 × Fin 1 => ((0 : Fin 1), act o.1 ω.1.2)) = (fun o => (0, o.1))) ≠
    weights.cnt (event fun ω : Ω => ((0 : Fin 1), ω.1.1) = (0, 0) ∧
        (fun o : Fin 2 × Fin 1 => ((0 : Fin 1), act o.1 ω.1.2)) = (fun o => (0, o.1))) *
      weights.cnt (event fun ω : Ω =>
        (fun o : Fin 2 × Fin 1 => ((0 : Fin 1), act o.1 ω.1.2)) = (fun o => (0, o.1)) ∧
        (act ω.1.1 ω.1.2, ω.2) = (0, 0)) := by
    decide +kernel
  apply hc
  have := congrArg (fun x => x * (weights.N : ℝ) * weights.N) this
  simp only [show S.μ.w = weights.w from rfl, weights.mass_eq_cnt] at this
  have hN : (weights.N : ℝ) ≠ 0 := by exact_mod_cast weights.N_pos.ne'
  field_simp at this
  exact_mod_cast this

end DDnotEff

/-! ### `CorrDyn`: every field of the structure, without `I ⊥ E ∣ B` -/

namespace CorrDyn

/-- Worlds `(d, e)`, weighted `3 : 1` towards `d = e`.
Source: none: infrastructure (mandate T7(a)(ii))
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Ω : Type := Fin 2 × Fin 2

/-- The correlated weights.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def weights : IntWeights Ω where
  wt ω := if ω.1 = ω.2 then 3 else 1
  pos ω := by revert ω; decide
  N := 8
  sum_eq := by decide +kernel

/-- **`CorrDyn` as an abstract decision structure**: `D_I = d`, `D_E = e`, everything else
constant; every factorization field holds (the fields are support-level), and `U = 𝟙[d = e]`.
Source: mandate T7(a)(ii)
Kind: N+
Fidelity: n/a
Hyps: none -/
noncomputable def S : AbstractDS Ω (Fin 1) (Fin 1) (Fin 1) (Fin 1) (Fin 2) (Fin 2) (Fin 1)
    (Fin 1) (Fin 1) where
  μ := weights.dist
  pos := weights.w_pos
  oI _ := 0
  oE _ := 0
  aI _ := 0
  aE _ := 0
  dI ω := ω.1
  dE ω := ω.2
  dB _ := 0
  oH _ := 0
  oC _ := 0
  polS _ := fun _ => (0, 0)
  U := natDiv (fun ω => if ω.1 = ω.2 then 1 else 0) 1
  U_mem := natDiv_mem _ (by norm_num) (fun ω => by split_ifs <;> omega)
  oI_I := by decide +kernel
  oE_E := by decide +kernel
  aI_B := by decide +kernel
  aE_B := by decide +kernel
  oH_oI := by decide +kernel
  oC_oI := by decide +kernel
  IB_common := commonInfo_of_step (by decide +kernel) (by decide +kernel) (by decide +kernel)
  BE_common := commonInfo_of_chain (by decide +kernel) (by decide +kernel)
    (fun ω₁ ω₂ => (ω₁.1, ω₂.2)) (by decide +kernel)
  I_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  E_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  B_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  IB_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _
  IB_det := by decide +kernel
  O_fac := (factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _).symm
  A_fac := factorsAs_of_subsingleton_range _ _ fun _ _ => Subsingleton.elim _ _

/-- **`I ⊥ E ∣ B` fails on `CorrDyn`**: `B` is constant, and `D_I`, `D_E` are correlated in
law (`3 : 1`) though independent in support — the factorization fields do not give it.
Source: [[udt-tiling-working-notes-2025-06-30]] lines 260–267; mandate T7(a)(ii)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem not_ieIndepB : ¬ IEIndepB S := fun h => by
  have := h (0, 0) ((0, 0), 0) (0, 0)
  have hc : weights.cnt (event fun ω : Ω => S.I ω = (0, 0) ∧ S.B ω = ((0, 0), 0) ∧ S.E ω = (0, 0)) *
      weights.cnt (event fun ω : Ω => S.B ω = ((0, 0), 0)) ≠
    weights.cnt (event fun ω : Ω => S.I ω = (0, 0) ∧ S.B ω = ((0, 0), 0)) *
      weights.cnt (event fun ω : Ω => S.B ω = ((0, 0), 0) ∧ S.E ω = (0, 0)) := by
    decide +kernel
  apply hc
  have := congrArg (fun x => x * (weights.N : ℝ) * weights.N) this
  simp only [show S.μ.w = weights.w from rfl, weights.mass_eq_cnt] at this
  have hN : (weights.N : ℝ) ≠ 0 := by exact_mod_cast weights.N_pos.ne'
  field_simp at this
  exact_mod_cast this

end CorrDyn

end Cleanroom.Udt.UdtCtExamples
