import Cleanroom.Udt.UdtCommTrust.Determination
import Cleanroom.Udt.UdtPolicyCalc.LocalGlobal
import Cleanroom.Udt.UdtPolicyCalc.TransparentNewcomb

/-!
# `Cleanroom.Udt.UdtCondenseDd.Squeeze`: the "representation theorem" squeeze and the archived axiom system (T10)

Work package `udt-condense-dd`, target T10 (udt-rep-038, 039, 2-033).

* **T10(a), the "representation theorem"** ([[agency-as-condensation]] lines 235–239,
  [[condensation-connection-attempt]] lines 140–153: agency conditions 1–4 + rationality ⟹
  `Π(o) = argmax_a E[U | Π(o) = a]`). Restated honestly over `udt-comm-trust`:
  `udt_formula_of_optimal` is *literally* `udt-policy-calc`'s `isLocalOptimum_of_isOptimal` — global
  optimality of the policy utility gives local optimality — with decision-determination as an
  **unused** hypothesis (the `S` row: "conditions 1–3 do not occur in the proof"; determination,
  recoverability and unity are not even statable over the structure and are not defined here —
  their absence *is* the finding). `udt_formula_condExp` is the `C` row: DD enters only through
  `condExp_DIB_eq_policyUtility` when the conclusion is written as conditional expectations given
  `D_{I,B}`.
* **T10(b), policy-compatibility** ([[formal-theorem-attempt]] lines 42–48): clause 2 (the
  observation marginal does not depend on the policy) excludes every problem in which the
  observation law depends on the policy — transparent Newcomb in particular
  (`transparentNewcomb_not_policyCompatible`, with `udt-policy-calc`'s `Transparent.obs`/`coinW`).
  The axiom system's domain excludes its motivating cases; its proof "bridges two measures"
  (`E_{P_π}[U]` vs `E_P[U | π(o) = a]`) without a lemma (findings).
* **T10(c), `policy-as-latent`'s "characterization"** (`archive/policy-as-latent.md` line 30, 69,
  84: "Π is characterized by `H(A | Π, B) = 0`"): every refinement of the action satisfies it
  (`refinement_satisfies_determination`), so the condition characterizes nothing. `L`.
-/

namespace Cleanroom.Udt.UdtCondenseDd

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

noncomputable section

set_option linter.unusedSectionVars false

/-! ### T10(a): the squeeze, and its honest form -/

section Representation

variable {Ω OI OE AI AE DI DE DB OH OC : Type}
variable [Fintype Ω] [DecidableEq Ω] [Fintype OE] [DecidableEq OE] [Fintype AE] [DecidableEq AE]
  [Fintype DE] [DecidableEq DE] [Fintype DI] [DecidableEq DI] [Fintype DB] [DecidableEq DB]
variable (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC)

/-- **The corpus's "representation theorem", restated honestly (T10(a), the `S` row)**: a globally
optimal external policy (for the policy utility `E[U | Π̈ = ·]`) is a local optimum — the UDT
formula's shape. The hypothesis `h : S.DecisionDetermined` is **unused**: the proof is
`udt-policy-calc`'s `isLocalOptimum_of_isOptimal` applied. Of [[condensation-connection-attempt]]'s
conditions 1–3 (its own numbering: 1 determination, 2 recoverability, 3 decision-determination),
decision-determination does work in the conditional-expectation form of the conclusion — once, to
turn `E[U | D_{I,B} = ·]` into a policy utility (`udt_formula_condExp`); determination holds by
construction of `Π̈` in `udt-comm-trust` (`polE_apply_of_DIB_eq`); recoverability across
situations has no counterpart in the single-situation structure. In this `S` form, with the
conclusion already stated over policy utilities, none of the three is used: the content is
`IsOptimal → IsLocalOptimum`, global ⟹ local optimality. (Repair round 1: the first docstring read
"conditions 1–3" under [[agency-as-condensation]]'s numbering, where unity is condition 3 and DD is
condition 4, and called the note's sentence "the content is in conditions 1–3" (line 153) false;
under the note's own numbering the sentence is right about DD.)
Source: [[agency-as-condensation]] lines 228–239; [[condensation-connection-attempt]] lines 140–153; [[unified-formal-framework]] Layer 5; [[formal-theorem-attempt]] Axioms 1′–3′ (udt-rep-038; findings §6.7)
Kind: S
Fidelity: exact (the conclusion's shape; the unused DD hypothesis kept for the record)
Hyps: (a) `hopt`; `h` unused -/
theorem udt_formula_of_optimal (_h : S.DecisionDetermined) {π : OE → AE}
    (hopt : IsOptimal S.policyUtility π) : IsLocalOptimum S.policyUtility π :=
  isLocalOptimum_of_isOptimal hopt

/-- **The `C` row: where DD actually enters.** For a world `ω` whose external policy is globally
optimal, the conditional expected utility given the dynamics of *any* world `ω'` is at most that
given the dynamics of `ω`: `E[U | D_{I,B} = D_{I,B}(ω')] ≤ E[U | D_{I,B} = D_{I,B}(ω)]`. DD is used
exactly once, to rewrite both conditional expectations as policy utilities
(`condExp_DIB_eq_policyUtility_polE`); the comparison itself is global optimality. Repair round 1:
the first version quantified over realized one-observation modifications `Π̈(ω') = Π̈(ω)[s ↦ a]`;
the r1 adversarial audit (§3.4, probe `CondExpDecorative.lean`) showed that hypothesis is inert
under global optimality, so the theorem is now stated for every `ω'` and the modification form is
the corollary `udt_formula_condExp_modify`.
Source: [[condensation-connection-attempt]] lines 123–130 ("Bridging the Gap", steps 2–6) (udt-rep-038)
Kind: C
Fidelity: stronger: every `ω'`, not only realized one-observation modifications (the note's local form is the corollary)
Hyps: (a) `h`, (a) `hopt`; `udt-comm-trust` §3 (c) by reference -/
theorem udt_formula_condExp (h : S.DecisionDetermined) {ω : Ω}
    (hopt : IsOptimal S.policyUtility (S.polE ω)) (ω' : Ω) :
    condExpJunk S.μ.w S.U (S.evDIB (S.DIB ω')) (-1) ≤
      condExpJunk S.μ.w S.U (S.evDIB (S.DIB ω)) (-1) := by
  rw [S.condExp_DIB_eq_policyUtility_polE h ω', S.condExp_DIB_eq_policyUtility_polE h ω]
  exact hopt _

/-- **The note's local form, as a corollary**: for a realized one-observation modification
`Π̈(ω') = Π̈(ω)[s ↦ a]`, the same inequality. The modification hypothesis (with `s`, `a`) is not
used by the proof — `udt_formula_condExp` holds for every `ω'` — and is kept only so that the
statement reads as the note's `Π(o) = argmax_a E[U | Π(o) = a]` display does. Quantified over
*realized* modifications only: an unrealized `Π̈[s ↦ a]` has no `D_{I,B}`-atom to condition on
(the junk `−1`).
Source: [[condensation-connection-attempt]] lines 123–130 (udt-rep-038)
Kind: L
Fidelity: exact (conditional-expectation form, realized modifications; the modification hypothesis is cosmetic)
Hyps: (a) `h`, (a) `hopt`; the modification hypothesis is inert -/
theorem udt_formula_condExp_modify (h : S.DecisionDetermined) {ω : Ω}
    (hopt : IsOptimal S.policyUtility (S.polE ω)) (s : OE) (a : AE) {ω' : Ω}
    (_hω' : S.polE ω' = Function.update (S.polE ω) s a) :
    condExpJunk S.μ.w S.U (S.evDIB (S.DIB ω')) (-1) ≤
      condExpJunk S.μ.w S.U (S.evDIB (S.DIB ω)) (-1) :=
  udt_formula_condExp S h hopt ω'

end Representation

/-! ### T10(b): policy-compatibility excludes prediction-dependent observations -/

section PolicyCompatible

variable {O A : Type} [Fintype O] [DecidableEq O] [Fintype A] [DecidableEq A]

/-- **The archive's policy-compatibility** ([[formal-theorem-attempt]] Definition, lines 42–48): for
each policy `π` a distribution `P_π` on `O × A` with (1) `P_π(o, a) > 0 ↔ π(o) = a` and (2) the
observation marginal of `P_π` equal to a fixed `D₀` for every `π`.
Source: [[formal-theorem-attempt]] lines 42–48 (udt-rep-039)
Kind: D
Fidelity: exact
Hyps: n/a -/
def PolicyCompatible (P : (O → A) → FinDist (O × A)) (D₀ : FinDist O) : Prop :=
  ∀ π : O → A, (∀ o a, 0 < (P π).w (o, a) ↔ π o = a) ∧
    ∀ o, mass (P π).w (event fun x : O × A => x.1 = o) = D₀.w o

/-- **Clause 2 alone forces the observation marginal to be policy-independent.**
Source: [[formal-theorem-attempt]] line 48 ("observations don't depend on the policy") (udt-rep-039)
Kind: L
Fidelity: exact
Hyps: none -/
theorem PolicyCompatible.marginal_eq {P : (O → A) → FinDist (O × A)} {D₀ : FinDist O}
    (h : PolicyCompatible P D₀) (π π' : O → A) (o : O) :
    mass (P π).w (event fun x : O × A => x.1 = o) = mass (P π').w (event fun x : O × A => x.1 = o) := by
  rw [(h π).2 o, (h π').2 o]

/-- **Policy-compatibility excludes every problem whose observation law depends on the policy**: if
the problem's own observation marginal under `π` is `Dof π` and `Dof` takes two values at some
observation, no `P` reproducing those marginals is policy-compatible.
Source: [[formal-theorem-attempt]] lines 42–48 (udt-rep-039; findings §6.8)
Kind: L
Fidelity: exact
Hyps: (a) -/
theorem not_policyCompatible_of_dependent (Dof : (O → A) → FinDist O) {π π' : O → A} {o : O}
    (hne : (Dof π).w o ≠ (Dof π').w o) :
    ¬ ∃ (P : (O → A) → FinDist (O × A)) (D₀ : FinDist O), PolicyCompatible P D₀ ∧
      ∀ π o, mass (P π).w (event fun x : O × A => x.1 = o) = (Dof π).w o := by
  rintro ⟨P, D₀, hPC, hmarg⟩
  apply hne
  rw [← hmarg π o, ← hmarg π' o]
  exact hPC.marginal_eq π π' o

end PolicyCompatible

/-! #### Transparent Newcomb's observation marginals -/

namespace TransparentMarginal

open Cleanroom.Udt.UdtPolicyCalc.Transparent

/-- **The observation marginal of transparent Newcomb under policy `π`**: the coin-weighted mass of
`{c : obs π c = o}`, with `udt-policy-calc`'s `Transparent.obs` and `Transparent.coinW`.
Source: [[gap1-reframing-predictor-access]] §8 (udt-rep-034, 039)
Kind: D
Fidelity: exact
Hyps: n/a -/
def obsMass (ε : ℝ) (π : TPolicy) (o : TObs) : ℝ :=
  ∑ c : Bool, coinW ε c * (if obs π c = o then 1 else 0)

/-- Supporting lemma: the marginal as a `FinDist` (for `0 ≤ ε ≤ 1`).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def obsDist (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (π : TPolicy) : FinDist TObs where
  w := obsMass ε π
  nonneg o := by
    unfold obsMass
    refine Finset.sum_nonneg fun c _ => mul_nonneg ?_ (by split_ifs <;> norm_num)
    cases c <;> simp [coinW] <;> linarith
  sum_one := by
    unfold obsMass
    rw [Finset.sum_comm]
    have : ∀ c : Bool, ∑ o : TObs, coinW ε c * (if obs π c = o then 1 else 0) = coinW ε c := by
      intro c
      rw [← Finset.mul_sum, Finset.sum_ite_eq, if_pos (Finset.mem_univ _), mul_one]
    simp_rw [this]
    exact coinW_sum ε

/-- **The one-boxer-on-full policy sees the full box with probability `1 − ε`.**
Source: [[gap1-reframing-predictor-access]] §8 ("An agent verdicted a one-boxer faces `o_full` at rate `1 − ε`")
Kind: L
Fidelity: exact
Hyps: none -/
theorem obsMass_oneTwo_full (ε : ℝ) : obsMass ε (Transparent.mk .one .two) TObs.full = 1 - ε := by
  simp [obsMass, coinW, obs, prediction, Transparent.mk, Transparent.flip]

/-- **The two-boxer policy sees the full box with probability `ε`.**
Source: [[gap1-reframing-predictor-access]] §8 ("An agent verdicted a two-boxer faces `o_full` at rate `ε`")
Kind: L
Fidelity: exact
Hyps: none -/
theorem obsMass_twoTwo_full (ε : ℝ) : obsMass ε (Transparent.mk .two .two) TObs.full = ε := by
  simp [obsMass, coinW, obs, prediction, Transparent.mk, Transparent.flip]

/-- **Transparent Newcomb is not policy-compatible (T10(b), refutation)**: for `ε ≠ 1/2`, no
`P : TPolicy → FinDist (TObs × BoxAct)` reproducing the problem's observation marginals satisfies
the archive's Definition — the marginal is `1 − ε` under `(1box, 2box)` and `ε` under
`(2box, 2box)`. Clause 1 is not even needed. The axiom system's domain excludes its motivating case.
Source: [[formal-theorem-attempt]] lines 42–48 (udt-rep-039; findings §6.8); [[gap1-reframing-predictor-access]] §8
Kind: P
Fidelity: exact
Hyps: (a) `hε`, (a) `h0`, `h1` -/
theorem transparentNewcomb_not_policyCompatible {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (hε : ε ≠ 1 / 2) :
    ¬ ∃ (P : TPolicy → FinDist (TObs × BoxAct)) (D₀ : FinDist TObs), PolicyCompatible P D₀ ∧
      ∀ π o, mass (P π).w (event fun x : TObs × BoxAct => x.1 = o) = (obsDist ε h0 h1 π).w o := by
  refine not_policyCompatible_of_dependent (obsDist ε h0 h1) (π := Transparent.mk .one .two)
    (π' := Transparent.mk .two .two) (o := TObs.full) ?_
  show obsMass ε (Transparent.mk .one .two) TObs.full ≠ obsMass ε (Transparent.mk .two .two) TObs.full
  rw [obsMass_oneTwo_full, obsMass_twoTwo_full]
  intro h
  apply hε
  linarith

end TransparentMarginal

/-! ### T10(c): the one-condition "characterization" characterizes nothing -/

section Refinement

variable {Ω : Type}

/-- **Every refinement of the action satisfies `H(A | Π, B) = 0`**: for any `A`, `B` and any `J`,
`A` is a function of `((A, J), B)` — so the condition "`Π` is characterized by `H(A | Π, B) = 0`"
(`policy-as-latent`) is satisfied by `Π := (A, J)` for every `J`, in particular by `A` itself, and
characterizes nothing. Stated on the support (function-of everywhere); the a.e. form is the same
statement by T7(a).
Source: `archive/policy-as-latent.md` lines 30, 69, 84 (udt-rep-2-033(a); findings §6.10)
Kind: L
Fidelity: exact
Hyps: none -/
theorem refinement_satisfies_determination {V W J : Type} (A : Ω → V) (B : Ω → W) (Jv : Ω → J) :
    IsSubvariable (fun ω => ((A ω, Jv ω), B ω)) A :=
  fun _ _ h => (Prod.mk.inj (Prod.mk.inj h).1).1

end Refinement

end

end Cleanroom.Udt.UdtCondenseDd
