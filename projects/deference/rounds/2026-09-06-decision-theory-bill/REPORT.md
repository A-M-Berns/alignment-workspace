# Report

Two passes on one round: the exploratory pass (verdict `GATE-NOT-UTILITY`) and the
pressure pass dispatched against it, which supersedes it.  Verdict after pressure:
**STATIC-CHOICE-CLOSED-DYNAMIC-ADMISSIBILITY-OPEN.**

## Result

The six answers the exploratory dispatch's §21 asks for, as corrected:

1. **What Normative Induction needs.**  The coupling hypothesis of `adequate_set_route`.
   Its abstract form is `adapter_coupling` (Lean): sound at a region point and
   `ℓ¹`-Lipschitz in the scores ⇒ mass off the adequate set affine in the defect;
   `adapter_practicalCert` composes it to `PracticalCert`.
2. **The weakest object.**  A sound Lipschitz adapter.  The soft gate is one realization
   with the sharp constant `(Σ_{q∉A} pref)/(W δ)` (`softGate_massOff_le_sharp`), of which
   the first pass's `|Q| pmax/(pmin δ)` is a corollary.  The hard gate is sound and has no
   Lipschitz constant (`hardGate_discontinuous`).  Inquiry is a wrapper
   (`gateWithInquiry`), silent under margin, with nothing proved about its branch.
3. **Competence with non-compensable constraints.**  What is proved is narrower than
   the first pass said: a finite additive penalty cannot uniformly make a constraint
   non-compensable under unbounded stakes (`scalar_bribery`), and a within-domain argmax
   never consults the forbidden value (`gate_invariant`).  Non-compensability must appear
   in the ordering itself; domain restriction is one realization, not the only one.
4. **Same architecture for corrigibility.**  As a type, yes, with the Branch Persistence
   Lemma in adequate-set form and the index anchored in the prestate charter.  Failures
   classify by locus (index, domain, level, provenance, mediation); the first three are
   typed exclusions, the last two preconditions.
5. **Reflective stability.**  A representation (`collapse`) plus strict-prestate
   authorization, plus the domain condition; not a theorem about preferences, and the
   "preserving successor dominates" reading is the domain condition restated.
6. **Where a new theorem is necessary.**  Margin realization on either route with the
   amplification `Γ` uniformly bounded; the averaged calibration bridge for empirical
   adequacy, which is open; and gated bounded rationality with endogenous admissibility,
   where `test_dynamic` shows comparator restriction without dynamic evaluation is
   vacuous.

## What the pressure pass changed

| first-pass claim | finding | correction |
|---|---|---|
| `softGate_practicalCert` discharges soundness, continuity and inquiry | the Lean is on the regime `total > 0`; no `⊥` | inquiry is `gateWithInquiry`, a wrapper; theorems hold on its gate regime |
| a constraint is non-compensable iff it restricts the domain | not proved; lexicographic and veto orders realize it too | the weaker claim, exactly `scalar_bribery` + `gate_invariant` |
| `κ = |Q| pmax/(pmin δ)` as an implementation detail | it is charged through amplification; `W = W(δ)` | §5 of the bill: the exact condition is the amplification/modulus condition, `δ* ∈ argmax W(δ)δ`; sharp constant in Lean |
| margin supplied by provability induction | that is a property of `b`, `MarginMass` is a property of `u` | two routes in Lean: `MarginMass` (route A, on `u`) and `MarginDisplayed` (route B, on `b`) |
| unbiasedness from feedback gives the coupling in the mean | no such theorem | the empirical averaged bridge is **OPEN**; the static theorem is pointwise and applies to certified adequacy |
| "two levels suffice", "no regress" | representational | stated as a representation plus authorization; no reflective theorem |
| trigger/capture/containment "not decision theory" | overdrawn | "not discharged by this gate interface"; preconditions |
| gated BRIA "fails" with endogenous admissibility | the failure is myopia, and typing restores safety | three ways distinguished (typing, dynamic evaluation, comparator restriction); restriction alone vacuous, exact fixture |
| branch deletion scored at a worst value | scalar | adequate-set form: the destroying act is inadequate |
| continuity through conflict needed | not required by Progress | margin-gated transport, or `Adequate(⊥)` compiled |

## Dependencies

Takes as hypotheses `2026-09-08-canonicalization`, `2026-09-05-practical-certificate`,
`2026-09-06-corrigibility-architecture` and `2026-09-06-incentive-nonpreemption`.
`Oesterheld, Demski and Conitzer`, "A Theory of Bounded Inductive Rationality", TARK 2023
(EPTCS 379, pp. 421–440), for BRIA's definitions and its Section 6 guarantee, cited not
re-proved; `lic_provind_true` of the pinned Logical Induction dependency as evidence of route B's
shape, cited by declaration and not composed.

## Deviations and prompt corrections

- The `(D1)`/`(D2)` factorization is `adequate_set_route`'s, not new.
- No repository material on BRIA or decision markets beyond passing mentions; the paper
  was read directly.
- The dispatch's abstract adapter lemma is formalized (`adapter_coupling`); the soft
  gate's own `ℓ¹`-Lipschitz constant is not, and the soft-gate theorems are proved
  directly.  Recorded as a minor open item rather than an artificial adapter.
- The pressure dispatch's inquiry option 1 (a total `softGateWithInquiry` with its
  coupling theorem) is done as far as the definition and the regime lemma; the coupling
  on the inquiry branch is not a theorem and is not claimed.
- Lean for speculative dynamic machinery was not written.
- The wiki `Sources` page gains the bounded-inductive-rationality paper, as dispatched;
  no other wiki surface was touched.

## What this does not establish

- That any realized market satisfies `Region`, `MarginMass` or `MarginDisplayed`; route B's
  asymptotics carry no rate, finite time is external, and the empirical averaged bridge
  is open.
- The soft gate's `ℓ¹`-Lipschitz constant; a converse to `adapter_coupling`.
- Anything about the inquiry branch beyond its definition; anything about infinite
  menus; commutation of typed exclusions for mixed-locus failures.
- Any dynamic competence theorem; any bound on provenance or mediation failures.

## Outstanding maintainer actions

1. Whether `adapter_practicalCert` or `softGate_practicalCert` should be registered;
   item 85 (refined to the deductive/empirical split and the rate condition) files what
   they consume.
2. Whether the inquiry semantics should be the wrapper or the compiled `Adequate(⊥)`;
   the round records both and prefers the second.

## Attribution

- Prompt author: maintainer, relayed verbatim (two dispatches).
- Executor: Claude Fable 5.1 (Anthropic).
- Dates: 2026-09-06 (exploratory pass), 2026-09-07 (pressure pass and maintainer integration pass).
