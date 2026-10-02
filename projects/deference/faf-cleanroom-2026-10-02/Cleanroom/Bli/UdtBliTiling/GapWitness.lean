import Cleanroom.Bli.UdtBliTiling.Defs
import Cleanroom.Bli.UdtBliCore.WitnessGap

/-!
# `udt-bli-tiling` · GapWitness: the failure of one-step tiling without independence
(T2, load-bearing 2)

On `udt-bli-core`'s full-support correlated prior `gapPrior` — two tables of mass `1/2`,
policy points correlated across tables (`aa, bb ↦ 2/5`, `ab, ba ↦ 1/10`), home-only utilities
`T1: a ↦ 1, b ↦ 0`, `T2: a ↦ 0, b ↦ 2` — the one-step policy is `bb` (`gap_full_support`), and
its one-point precommitment `bb[T1 ↦ a] = ab` is strictly better: `3/2 > 1`. So
`¬ NoStrictPrecommitAt gapPrior bb T1` (`gap_not_noStrictPrecommitAt`), with every policy of
positive mass — no junk enters (core finding F-4: the program's own witness `corrPrior` is
null-mass on `ab`, and its `V(a,b) = 1.5` is a `sepValue`, not an `exAnteValue`).

The hypothesis audit (`gap_hypothesis_audit`): `gapPrior` satisfies `NDHOME`, `NDPOLICY`,
`ReflectivePolicy`, `LocalUtility` and fails `IndependentPoints` — **exactly** the independence
clause of T1's package is missing. This is the N− of `Independent.lean` and the refutation of the
unqualified sentence "one-step UDT tiles" ([[bli-program]] §3.9 U9(3) in the full-support reading
of core's F-4).

Sources: [[bli-program]] §3.9 U9(3) and §7 item 9; core finding F-4; mandate T2. Not called
"Soto's impossibility": the name carries the hypothesis class.
-/

namespace Cleanroom.Bli.UdtBliTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliCore.Gap Finset

namespace GapTiling

/-- The one-point precommitment of `bb` at `T1` to `a` is `ab`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma update_bb_T1 : Function.update (fun _ : ↥twoTables => false) T1 true = abPol := by
  funext T
  rcases eq_T1_or_T2 T with rfl | rfl
  · rw [Function.update_self, abPol_T1]
  · rw [Function.update_of_ne T2_ne_T1, abPol_T2]

/-- **`gapPrior` satisfies `NDHOME`**: every home cell has positive mass (the base masses are
`1/5` and `1/20`).
Source: mandate T2 (the hypothesis audit)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem ndhome : gapPrior.NDHOME := by
  intro T a
  rcases eq_T1_or_T2 T with rfl | rfl <;> cases a <;>
  · unfold FiniteBLIPrior.jointMass gapPrior
    rw [handPrior_massOf]
    simp only [handPrior]
    norm_num [massOf, gapMass, Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_bool,
      T1_ne_T2, T2_ne_T1, mAsk_ne_mRec, Ne.symm mAsk_ne_mRec, tnPP]

/-- **The tiling failure without independence**: on `gapPrior`, the one-step policy `bb` strictly
prefers the one-point precommitment `bb[T1 ↦ a] = ab`:
`𝔼_μ[U | pp = bb[T1 ↦ a]] = 3/2 > 1 = 𝔼_μ[U | pp = bb]`, both policies of positive mass. Hence
`¬ NoStrictPrecommitAt gapPrior bb T1`, and `bb` is not prior-optimal while `ab` is.
Source: [[bli-program]] §3.9 U9(3) ("`V(a,b) = 1.5 > 1 = V(b,b)`: the prior strictly prefers
precommitting `a` at `T₁`" — read with full support after core's F-4: the program's witness has
`ab` null, so its `1.5` is a `sepValue`); [[bli-program]] §7 item 9; mandate T2
Kind: N− (for `oneStep_tiles_of_independent`) / refutation of the unqualified sentence
"one-step UDT tiles over a BLI prior"
Fidelity: exact (about `𝔼[U | pp = π]` of positive policies; no junk)
Hyps: (a) none -/
theorem gap_not_noStrictPrecommitAt :
    gapPrior.IsOneStepPolicy (fun _ => false) ∧
      ¬ NoStrictPrecommitAt gapPrior (fun _ => false) T1 ∧
      gapPrior.exAnteValue (Function.update (fun _ => false) T1 true) = 3 / 2 ∧
      gapPrior.exAnteValue (fun _ => false) = 1 ∧
      ¬ gapPrior.IsPriorOptimal (fun _ => false) ∧ gapPrior.IsPriorOptimal abPol := by
  obtain ⟨h1, _, hab, hnbb, vab, vbb⟩ := gap_full_support
  refine ⟨h1, ?_, by rw [update_bb_T1]; exact vab, vbb, hnbb, hab⟩
  apply not_noStrictPrecommitAt_of_lt (b := true) (ndpolicy _)
  rw [update_bb_T1, vab, vbb]; norm_num

/-- **The hypothesis audit**: `gapPrior` has `NDHOME`, `NDPOLICY`, `ReflectivePolicy`,
`LocalUtility`, and not `IndependentPoints` — exactly T1's independence clause is missing where
tiling fails. (It also fails `NoCrossBranch`, the derived predicate.)
Source: mandate T2 ("so exactly T1's independence clause is missing"); [[bli-program]] §7 item 9
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem gap_hypothesis_audit :
    gapPrior.NDHOME ∧ gapPrior.NDPOLICY ∧ gapPrior.ReflectivePolicy ∧ gapPrior.LocalUtility ∧
      ¬ gapPrior.IndependentPoints ∧ ¬ gapPrior.NoCrossBranch :=
  ⟨ndhome, ndpolicy, reflectivePolicy, localUtility, not_independentPoints, not_noCrossBranch⟩

end GapTiling

end Cleanroom.Bli.UdtBliTiling
