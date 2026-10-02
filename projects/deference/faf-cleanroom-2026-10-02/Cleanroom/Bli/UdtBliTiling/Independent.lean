import Cleanroom.Bli.UdtBliTiling.Defs
import Cleanroom.Bli.UdtBliCore.WitnessCorr
import Cleanroom.Bli.UdtBliCore.WitnessGap
import Cleanroom.Bli.UdtBliCore.Mugging
import Cleanroom.Bli.UdtBliSist.ModelB

/-!
# `udt-bli-tiling` · Independent: one-step tiling under independent points and local utility
(T1, load-bearing 1)

**Scope: independent points, local utility, one level.** Over a `FiniteBLIPrior` with
`NDHOME ∧ NDPOLICY ∧ ReflectivePolicy ∧ LocalUtility ∧ IndependentPoints`, every one-step policy
is prior-optimal and has no strict preference for precommitment (`oneStep_tiles_of_independent`);
the point form at one table (`noStrictPrecommitAt_of_oneStepChoice`). Every step is derived from
`udt-bli-core`:
`IndependentPoints ∧ ReflectivePolicy ⟹ IndependentPointsGivenState`
(`indepGivenState_of_indep_reflectivePolicy`) `⟹ NoCrossBranch` with `LocalUtility`
(`noCrossBranch_of_localUtility_indepGivenState`) `⟹ IsPriorOptimal`
(`priorOptimal_of_oneStepPolicy`), and then `noStrictPrecommit_of_priorOptimal`. bli-soto-b-045's
outline maps onto this chain: "by fairness its actions look better" is the separable value
(`exAnteValue_eq_sepValue`, from `ReflectivePolicy ∧ LocalUtility`); "by no-coordination-problems
they look better in individual cases" is the one-point update of the separable value
(`sepValue_update`, which needs nothing more); "UDT picks the individually best action" is
`IsOneStepChoice = IsUpdatefulChoice` (`oneStep_iff_updateful`, from `NoCrossBranch`, which is
where `IndependentPoints` enters).

**Not a squeeze** (mandate T1 traps): the hypotheses are structural predicates about `μ` that
never mention `exAnteValue` or optimality, and each is checked false on a prior where it is
needed (`hypotheses_fail_somewhere`): `IndependentPoints` on `gapPrior` (where tiling fails,
`GapWitness.lean`), `LocalUtility` and `NoCrossBranch` on `muggingPrior` (where tiling holds
anyway, `MuggingTiles.lean`), `ReflectivePolicy` on `udt-bli-sist`'s Model B.

**Witness** N+: `corrPriorFull` with the non-constant one-step policy `ab` (`corrFull_tiles`).
N−: `gapPrior` (`GapWitness.lean`).

Sources: [[bli-program]] §3.9 U9(2); [[bli-program-desiderata]] U6; bli-soto-a-024;
bli-soto-b-045. The name says what is proved; nothing here is called "UDT tiles".
-/

namespace Cleanroom.Bli.UdtBliTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A] [Fintype A]
variable {P : FiniteBLIPrior 𝒮 m 𝒟 A}

/-- **One-step tiling under independent points and local utility (one level).** Under
`NDHOME ∧ NDPOLICY ∧ ReflectivePolicy ∧ LocalUtility ∧ IndependentPoints`, every one-step policy
`π` is prior-optimal and has no strict preference for precommitment:
`𝔼_μ[U | pp = π[T ↦ b]] ≤ 𝔼_μ[U | pp = π]` for every table `T` and action `b`.
Scope: independent policy points, local (additive cross-term) utilities, one level of tables.
The hypotheses are the structural predicates only; each fails on some prior
(`hypotheses_fail_somewhere`), and `IndependentPoints` fails exactly where tiling fails
(`GapWitness.lean`).
Source: [[bli-program]] §3.9 U9(2) ("one-step tiling holds under `PolicyFair ∧
IndependentPoints`" — here (F) is automatic on the bare prior, `policyFair_trivialLayer`, and
(I) is `IndependentPoints ∧ LocalUtility`); [[bli-program-desiderata]] U6 (the Theorem-2 shape
over a BLI prior); bli-soto-a-024 (Desideratum 2, one-level finite form); bli-soto-b-045 (the
outline; see the module docstring for the step-by-lemma map)
Kind: C (`indepGivenState_of_indep_reflectivePolicy`,
`noCrossBranch_of_localUtility_indepGivenState`, `priorOptimal_of_oneStepPolicy`,
`noStrictPrecommit_of_priorOptimal`)
Fidelity: weaker: one level and finite — bli-soto-a-024's "`k` forced actions" and "late enough
`i`" are not here (the rounds are `SingleCoin.lean`'s; the inductor is nobody's yet)
Hyps: (a) all five structural predicates are hypotheses of the statement (none is assumed to
hold of any prior; each is derived on the witnesses); does not use faith -/
theorem oneStep_tiles_of_independent [Nonempty A] (hhome : P.NDHOME) (hpol : P.NDPOLICY)
    (hR : P.ReflectivePolicy) (hL : P.LocalUtility) (hI : P.IndependentPoints) (π : Policy 𝒟 A)
    (h1 : P.IsOneStepPolicy π) : P.IsPriorOptimal π ∧ NoStrictPrecommit P π := by
  have hN : P.NoCrossBranch :=
    P.noCrossBranch_of_localUtility_indepGivenState hL
      (P.indepGivenState_of_indep_reflectivePolicy hI hR)
  have hopt := P.priorOptimal_of_oneStepPolicy hhome hpol hN hR hL π h1
  exact ⟨hopt, noStrictPrecommit_of_priorOptimal hpol hopt⟩

/-- **The point form**: at a single table `T` where `π T` is a one-step choice, the same package
gives no strict preference for precommitment at `T` — the one-point precommitment `π[T ↦ b]`
changes the separable value by `μ(state = T) · (homeEU T b − homeEU T (π T)) ≤ 0`.
Source: [[bli-program]] §3.9 U9(2); mandate T1 ("also the point form")
Kind: C (`oneStep_iff_updateful`, `exAnteValue_eq_sepValue`, `sepValue_update`)
Fidelity: exact (one level)
Hyps: (a) the five structural predicates; does not use faith -/
theorem noStrictPrecommitAt_of_oneStepChoice [Nonempty A] (hhome : P.NDHOME) (hpol : P.NDPOLICY)
    (hR : P.ReflectivePolicy) (hL : P.LocalUtility) (hI : P.IndependentPoints) (π : Policy 𝒟 A)
    (T : ↥𝒟) (h1 : P.IsOneStepChoice T (π T)) : NoStrictPrecommitAt P π T := by
  have hN : P.NoCrossBranch :=
    P.noCrossBranch_of_localUtility_indepGivenState hL
      (P.indepGivenState_of_indep_reflectivePolicy hI hR)
  have hT : 0 < P.stateMass T := FiniteBLIPrior.NDHOME.stateMass_pos P hhome T
  have hu : P.IsUpdatefulChoice T (π T) :=
    (P.oneStep_iff_updateful (FiniteBLIPrior.NDHOME.ndpol P hhome) (P.reflective_of_reflectivePolicy hR) hN T hT (π T)).mp h1
  refine ⟨hpol π, fun b _ => ?_⟩
  rw [P.exAnteValue_eq_sepValue hR hL _ (hpol _), P.exAnteValue_eq_sepValue hR hL _ (hpol _),
    sepValue_update]
  have : P.stateMass T * (P.homeEU T b - P.homeEU T (π T)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hT.le (by linarith [hu b])
  linarith

/-! ## The N+ witness: the full-support independent prior with the non-constant policy `ab` -/

/-- **N+ for `oneStep_tiles_of_independent`**: on `corrPriorFull` (independent uniform points,
home-only utilities `(1,0)/(0,2)`), the one-step policy is the non-constant `ab`, it is
prior-optimal with value `3/2`, and it has no strict preference for precommitment. The full
hypothesis package is inhabited (`CorrFull.structure_all`), the conclusion is not a
constant-policy triviality (`const_ne_abPol`).
Source: mandate T1 (witness); [[bli-program]] §3.9 U9(2)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem corrFull_tiles :
    corrPriorFull.IsOneStepPolicy abPol ∧ corrPriorFull.IsPriorOptimal abPol ∧
      NoStrictPrecommit corrPriorFull abPol ∧ corrPriorFull.exAnteValue abPol = 3 / 2 ∧
      ∀ c : Bool, (fun _ : ↥twoTables => c) ≠ abPol := by
  obtain ⟨_, _, hRp, hL, hI, _, hhome, hpol⟩ := CorrFull.structure_all
  obtain ⟨h1, _, hv⟩ := CorrFull.oneStep_ab
  obtain ⟨hopt, htile⟩ := oneStep_tiles_of_independent hhome hpol hRp hL hI abPol h1
  exact ⟨h1, hopt, htile, hv, const_ne_abPol⟩

/-! ## The guard: each hypothesis fails somewhere -/

/-- **Each structural hypothesis of T1 is checked false on some prior** (mandate T1 traps; the
guard of [[bli-program]] §7 item 9 against "fairness restating the conclusion"):
`IndependentPoints` on the full-support correlated prior (where tiling fails,
`GapWitness.lean`), `LocalUtility` and the derived `NoCrossBranch` on the mugging prior (where
tiling holds anyway, `MuggingTiles.lean` — the package is sufficient, not necessary), and
`ReflectivePolicy` on `udt-bli-sist`'s Model B (through `reflective_of_reflectivePolicy`).
Source: mandate T1; [[bli-program]] §7 item 9
Kind: N−
Fidelity: n/a
Hyps: (a) none -/
theorem hypotheses_fail_somewhere (r : Bool → ℚ) :
    ¬ gapPrior.IndependentPoints ∧ ¬ (muggingPrior r).LocalUtility ∧
      ¬ (muggingPrior r).NoCrossBranch ∧ ¬ UdtBliSist.ModelB.modelB.ReflectivePolicy :=
  ⟨Gap.not_independentPoints, Mugging.not_localUtility r, Mugging.not_noCrossBranch r,
    fun h => UdtBliSist.ModelB.not_reflective_B (UdtBliSist.ModelB.modelB.reflective_of_reflectivePolicy h)⟩

end Cleanroom.Bli.UdtBliTiling
