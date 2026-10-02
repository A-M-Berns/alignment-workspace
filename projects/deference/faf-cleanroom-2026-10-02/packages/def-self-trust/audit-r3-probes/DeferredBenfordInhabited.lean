import Cleanroom.Deference.DefSelfTrust.Pseudorandom

/-!
# Audit probe (def-self-trust, round 3, adversarial): the OPEN conjecture's explicit hypotheses are consistent

`truthStar_deferred_benford` (OPEN, `Pseudorandom.lean`) carries the hypotheses `ha : Injective a`,
`hg : ∀ j, j < g j`, `hp : 0 ≤ p ≤ 1`, `hcodes : MachineSentenceCodes (atomFamily a)`,
`hfg : ∀ n, f n < g n` for a deferral `f` (which FAF forces to satisfy `n < f n`), plus the
`IsLogicalInductor` instance binder (li-pseudorandom's OPEN T7). An OPEN statement whose
explicit hypotheses were jointly unsatisfiable would be a vacuous conjecture. This file checks
they are not: `a := id`, `g := (· + 2)`, `f := succDeferral` satisfy every explicit hypothesis.
The instance binder is not discharged here (T7). Not imported by the library.
-/

namespace Cleanroom.AuditProbe.DefSelfTrust.DeferredBenfordInhabited

open LogicalInduction Cleanroom.Li.LiPseudorandom Cleanroom.Deference.DefSelfTrust

/-- The explicit hypothesis package of `truthStar_deferred_benford` is inhabited: an injective
placement, a delay with `j < g j`, codes for the atom family, and a deferral strictly before
the decision day. -/
theorem deferredBenford_explicit_hyps_inhabited :
    ∃ (a g : ℕ → ℕ) (f : DeferralFunction), Function.Injective a ∧ (∀ j, j < g j) ∧
      MachineSentenceCodes (atomFamily a) ∧ (∀ n, f n < g n) :=
  ⟨id, fun j => j + 2, succDeferral, Function.injective_id, fun j => by show j < j + 2; omega,
    machineSentenceCodes_atomFamily_id, fun n => by show n + 1 < n + 2; omega⟩

end Cleanroom.AuditProbe.DefSelfTrust.DeferredBenfordInhabited
