# Report

## Result

Verdict **GATE-NOT-UTILITY**.  The six answers the dispatch's §21 asks for:

1. **What Normative Induction needs from decision theory.**  One hypothesis of the
   existing `adequate_set_route`: the realized response distribution's mass off the
   adequate set is affine in the public defect (`hcouple`).  `DECISION_THEORY_BILL.md`
   reads it off the canonical `Evaluation` / `PracticalUptake` types and splits it into
   region soundness (semantics), Lipschitz continuity (decision theory), inquiry and
   competence.
2. **The weakest object that supplies it.**  A soft gate on adequacy prices: ramp
   weight times task preference, normalized, inquiring when nothing is confidently
   adequate.  `GatedChoice.softGate_practicalCert` (Lean) gives `PracticalCert` with
   `M = D·|Q|·pmax/(pmin·δ)`, `ε = εad`, given a region that encodes inadequacy and
   marks some adequate response with margin.  A hard gate has no Lipschitz constant
   (`hardGate_discontinuous`, Lean).
3. **Task competence with non-compensable constraints.**  Yes, conditionally: a BRIA over
   the gated decision-problem sequence keeps its own guarantee among adequate
   responses, and the gate is invariant to forbidden responses' task value
   (`gate_invariant`).  No compensatory scalar can be (`scalar_bribery`).  The
   composition fails when admissible actions change future admissibility — a domain
   restriction, not a learner property, is the repair (`test_5`).
4. **The same architecture for constitutional constraints.**  As a type, yes: branch
   vetoes are adequate sets, and the branch index must be anchored (`test_9`); the gate
   must cover successor installation (`test_7`), two levels suffice (`collapse`).
5. **Reflective stability.**  A design stipulation plus containment: gate preservation
   is an induction over admissible transitions once the gate's alphabet includes
   self-rewriting, and alphabet completeness is PR89's `Mediates`.
6. **Where a new theorem is necessary.**  Margin realization at the realized market
   (the completeness half of the semantic bill), gated no-regret under endogenous
   admissibility, and continuity through the switch into inquiry.

## Dependencies

Takes as hypotheses `2026-09-08-canonicalization` (the `Evaluation` interface and
`adequate_set_route`), `2026-09-05-practical-certificate`,
`2026-09-06-corrigibility-architecture` (anchoring, lanes, `Mediates`) and
`2026-09-06-incentive-nonpreemption` (`Φ_C`).  `Oesterheld, Demski and Conitzer`, "A
Theory of Bounded Inductive Rationality", TARK 2023 (EPTCS 379, pp. 421–440), is used
for BRIA's definitions and its Section 6 guarantee; nothing from it is re-proved or
asserted.

## Deviations and prompt corrections

- The dispatch's `(D1)`/`(D2)` factorization is not new to the repository: it is
  `adequate_set_route`'s `hcouple` and its two loss hypotheses.  The round says so and
  builds on it rather than introducing a `d^dec` symbol.
- No repository material on BRIA or decision markets exists beyond passing mentions in
  the frozen note dumps; the BRIA setting was taken from the paper directly and its
  guarantee is cited, not reproduced.
- The dispatch's §7 laws for a "decision theory of reasons" are recorded as inherited
  from the legitimacy properties rather than as a new theory; the round declines to
  present the correspondence as more than the gate's input type.
- Lean was written for the soft-gate coupling, its composition with the adequate-set
  route, the hard-gate discontinuity, scalar bribery and gate invariance.  The
  reflective and branch models stay in exact Python: their content is a definitional
  domain condition plus a countermodel.
- No wiki or specification surface beyond `DECISIONS.md`, `PRIORITIES.md`,
  `PROVENANCE.md` and `state/` was touched.

## What this does not establish

- That any realized market satisfies `Region` and `Margin`; both are external at finite
  time and the second is a completeness condition no sound-only compiler gives.
- That the constant `κ` is tight; it grows with the menu and with `1/δ`.
- Anything about infinite menus, about the transition into and out of inquiry, or about
  mixed-type violations under the typed repairs of `CORRIGIBILITY_CONNECTION.md` §4.
- Any bound on the precondition half of `Φ_C` (trigger integrity, capture, boundary
  escape); the architecture round's scope warning stands.

## Outstanding maintainer actions

1. Whether `GatedChoice.softGate_practicalCert` should be registered; `PRIORITIES.md`
   item 85 files the margin-realization problem it consumes.
2. Whether the repository should carry the BRIA paper on `wiki/Sources.md`; the round
   did not edit the wiki.

## Attribution

- Prompt author: maintainer, relayed verbatim.
- Executor: Claude Fable 5.1 (Anthropic).
- Date: 2026-09-06.
