import Cleanroom.Li.LiCoupledPair.A.JointInductor
import Cleanroom.Li.LiCoupledPair.A.SealedInductor

/-!
# `li-coupled-pair` · A/Open: the two OPEN rows of record (T4.3, T5.2)

The unconditional existence of the two-way pair and of the sealed-sibling system over
`paperDP 𝗜𝚺₁` — stated precisely, left `sorry`, listed in `li-coupled-pair-A-open.txt`. Reason, both:
FAF proves uniform computability of its bounded LIA evaluator in the stage table only as the
`private` `liaPrefixFromStagesAtFuel_prim` (`Construction/LIACompiler.lean:3665`); every consumer
in the run cites these names (plan §0.4 rule 1).

* `twoWayPair_exists` (T5.2): its conditional form is **proved** —
  `twoWayPair_exists_of_uniform : UniformLIAEvaluator → twoWayPair_exists`'s statement — through
  `paperTwoWayPair_of_uniform`, so the API fix (`uniform_of_primrec` on the private lemma)
  discharges it in one line.
* `sealedSystem_exists` (T4.3): its conditional form is **proved** too —
  `sealedSystem_exists_of_uniform` through `paperSealedSystem_of_uniform` (`A/SealedInductor.lean`,
  continuation 1) — so the same API fix discharges it in one line. The schedule clauses are those of
  the witness: same-day publication, horizon `succDeferral`, settlement `payoutSchedule` (the first
  attempt's statement said next-day publication with a `succDeferral`-shaped horizon, which no
  `SealedSpec` can satisfy: `e_lt_F` would need `n + 1 < n + 1`; see the report).
-/

namespace Cleanroom.Li.LiCoupledPair.A

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
open Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair

/-- **T5.2's statement, under the hypothesis (proved):** there is a two-way pair over
`paperDP 𝗜𝚺₁` on both sides with `quotedA = witnessQuoted` (the tag-0 atoms `⟨0, ⟨j, n⟩⟩`),
next-day publication, `XH = cleanX`, `f = succDeferral`, settlement `payoutSchedule` and payout
after the lookahead — `paperTwoWayPair_of_uniform`, every field pinned (repair round 1, audit r1
fidelity N2: the statement now pins exactly the witness's data, so no degenerate discharge with,
e.g., `quotedA j n := ⊤` could satisfy it).
Source: mandate T5.2/T5.3
Kind: C
Fidelity: variant: plain trader class
Hyps: (b) `UniformLIAEvaluator` -/
theorem twoWayPair_exists_of_uniform (hU : UniformLIAEvaluator) :
    ∃ p : TwoWayPair, p.DPA0 = paperDP 𝗜𝚺₁ ∧ p.DPH0 = paperDP 𝗜𝚺₁ ∧ p.quotedA = witnessQuoted ∧
      p.e = (fun _ => PublicationSchedule.succ) ∧ p.XH = cleanX ∧ p.f = succDeferral ∧
      p.σ = (fun _ => payoutSchedule) ∧ ∀ j n, p.f.f n < (p.σ j).e n :=
  ⟨paperTwoWayPair_of_uniform hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ n => payout_after_deferral n⟩

/-- **OPEN (T5.2): the two-way pair exists unconditionally** over `paperDP 𝗜𝚺₁`, with the witness's
data pinned (`quotedA = witnessQuoted`, next-day publication, `XH = cleanX`, `f = succDeferral`,
settlement `payoutSchedule`, payout after the lookahead). Open because the only missing input is
`UniformLIAEvaluator` (`twoWayPair_exists_of_uniform`), which FAF proves as a private lemma. Every
two-way row in the run cites this name.
Source: [[route-sparse-schedule]] §10 hypothesis 7 (vq-wiki-067); [[route-negative-introspective]] §4.4 (vq-wiki-2-017 (b)); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037)
Kind: OPEN
Fidelity: variant: plain trader class
Hyps: n/a (open) -/
theorem twoWayPair_exists :
    ∃ p : TwoWayPair, p.DPA0 = paperDP 𝗜𝚺₁ ∧ p.DPH0 = paperDP 𝗜𝚺₁ ∧ p.quotedA = witnessQuoted ∧
      p.e = (fun _ => PublicationSchedule.succ) ∧ p.XH = cleanX ∧ p.f = succDeferral ∧
      p.σ = (fun _ => payoutSchedule) ∧ ∀ j n, p.f.f n < (p.σ j).e n := by
  sorry

/-- **T4.3's statement, under the hypothesis (proved):** there is a sealed-sibling system over
`paperDP 𝗜𝚺₁` (both bases) with same-day publication, horizon `succDeferral`, settlement
`payoutSchedule`, `quoted = witnessQuoted` and `contract = witnessQuoted 0` —
`paperSealedSystem_of_uniform`, every field pinned (repair round 1, audit r1 fidelity N2), and
the siblings pinned to FAF's LIA on each frozen process, so that `Y_eq` reads
`Y n = sib n (F n) (contract n)` — the corpus's `Y_n := H^{[n]}_{F(n)}(P^{(n)})` with `H^{[n]}`
*the* sibling (repair round 2, audit r2 adversarial N1).
Source: mandate T4.3
Kind: C
Fidelity: variant: exact rational contract; plain trader class; `A` quotes the base propositions, not the contract (see `paperSealedSpec`)
Hyps: (b) `UniformLIAEvaluator` -/
theorem sealedSystem_exists_of_uniform (hU : UniformLIAEvaluator) :
    ∃ S : SealedSiblingSystem, S.base = paperDP 𝗜𝚺₁ ∧ S.DPA0 = paperDP 𝗜𝚺₁ ∧
      S.e = (fun _ => PublicationSchedule.sameDay) ∧ S.F = succDeferral ∧ S.σ = payoutSchedule ∧
      S.quoted = witnessQuoted ∧ S.contract = witnessQuoted 0 ∧
      S.sib = fun N => liaHistory (siblingProcess S.base S.a S.e N) :=
  ⟨paperSealedSystem_of_uniform hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **OPEN (T4.3): the sealed-sibling system exists unconditionally** over `paperDP 𝗜𝚺₁` (both
bases), with same-day publication, horizon `succDeferral`, settlement `payoutSchedule`, and the
witness's `quoted = witnessQuoted`, `contract = witnessQuoted 0` pinned, and the siblings pinned
to FAF's LIA on each frozen process (repair round 2). Open because the only missing input is
`UniformLIAEvaluator` (`sealedSystem_exists_of_uniform`), which FAF proves as a private lemma.
Source: [[frozen-deliberation-deference-v6]] §4 (anson-017); [[deference-in-logical-induction-v6]] §5.2 (root-deference-037)
Kind: OPEN
Fidelity: variant: exact rational contract; plain trader class; `A` quotes the base propositions, not the contract (see `paperSealedSpec`)
Hyps: n/a (open) -/
theorem sealedSystem_exists :
    ∃ S : SealedSiblingSystem, S.base = paperDP 𝗜𝚺₁ ∧ S.DPA0 = paperDP 𝗜𝚺₁ ∧
      S.e = (fun _ => PublicationSchedule.sameDay) ∧ S.F = succDeferral ∧ S.σ = payoutSchedule ∧
      S.quoted = witnessQuoted ∧ S.contract = witnessQuoted 0 ∧
      S.sib = fun N => liaHistory (siblingProcess S.base S.a S.e N) := by
  sorry

end Cleanroom.Li.LiCoupledPair.A
