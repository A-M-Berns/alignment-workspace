# Report — procedural legitimacy sufficiency prosecution

**Attribution.** Prompt author: GPT-5.6 Sol (OpenAI). Executor: Claude Opus 5
(Anthropic). Dispatched 2026-08-12; executed 2026-08-13, which is why the round
directories carry the later date.

**Verdict: four-condition sufficiency is REFUTED**, with six all-four
counterexamples and a record-equivalence argument showing that no fifth conjunct
of the same type closes them. Classification per §VII: **(4)**, the target was
underspecified, with a piece of **(1)**, one condition was too weak — and
explicitly **not (3)**, a missing fifth property.

By §XIV this is **partial success**: the decomposition survives and is useful, a
whole-architecture counterexample survives with it, and the round isolates which
of the three diagnoses applies.

---

## What was built

`projects/leverage/rounds/2026-08-13-procedural-legitimacy/` — the independent
target, provenance ancestry, the branching-safe answerability forest, the four
conditions, twelve attacks, six independence witnesses. 37 tests.

`projects/leverage/notes/LEGITIMACY_ARCHITECTURE.md` — substantially revised, and
now answers §XVII's fourteen questions.

## What was proved or mechanically checked

- **No authority amplification.** A provenance-valid ground's scope is contained
  in what its roots were granted — induction along the basis DAG, exhaustive over
  all `4^3` scope chains of length three. Defeats attack A. Necessity shown: the
  same chain without the amplifying link is admitted.
- **Cycles and self-filed roots are refused**, decidably.
- **The previous round's fate label is not branching-safe.** Over all `343`
  length-three histories, `36` have leaves of more than one status and `20` have a
  terminal branch the label omits together with its witness.
- **Branching conservation.** Every leaf is live, suspended with a route, or
  terminal with backing; exhaustive over `343` sequences, refusing `254` when the
  backing fields are stripped.
- **Forest composition**, `F_{0->T} = F_{s->T} . F_{0->s}`, over all `2401`
  segment pairs.

## What failed under prosecution

Six trajectories satisfy all four conditions and fail the target, in three
families — the reasoner's inquiry machinery drifting from what arises (attacks C,
E); its bearing relation from what bears (G); its adequacy relation from what
settles (H, I, L). Each uses authority the reasoner genuinely holds, over a
coordinate the grant genuinely covers, by a derivation that is genuinely
well-founded.

The obstruction is structural, not a weak clause: one trajectory and two
environments differing only in whether the adequacy relation is faithful give any
trajectory-predicate one value and the target two.

**The obvious fifth condition fails instructively.** Prospectivity refuses the
retroactive attack *and* the positive control, because adding a new way to settle
a demand is the same operation whether the new way is better or worse. Disclosure
— a revision reaching a live liability must name it — admits the control and
refuses the retroactive attack, so it is strictly better, and it still admits the
prospective attack. It is recommended as a recording requirement, not a
prohibition, and is not offered as a sufficiency conjunct.

## What the four conditions do buy

Attacks A, B, D and F are defeated. Provenance stops laundering by chain and by
cycle while leaving derivation, proof, conceptual innovation and genuine
defeaters unobstructed. The prospective read of entitlement stops de-entitling a
question already raised — and reading entitlement at service time instead lets
the same trajectory through, which is shown, so the clause is load-bearing rather
than decorative. Flooding is self-defeating once service obligations carry
deadlines. The positive control passes.

## Deviations

1. **No Lean.** The execution environment has no toolchain, so §XV.11–12 could not
   be run: `python3 tests/run.py` is green, `lake build` was not run. The two
   short inductions are filed as port targets. This is the second round to pay
   this, and friction item F7 already records it.
2. **§XIII.13 adversarial review in a separate context was not performed.** The
   round is its own adversary — the attack suite is the prosecution — and no
   independent context reviewed it.
3. **The round directory carries 2026-08-13, not the dispatch's 2026-08-12.** Two
   round directories under one date would be ambiguous, and the dispatch date is
   recorded here.
4. **The four-condition architecture is reported as three plus two rules.**
   §IX invites a cleaner factorization; inquiry adequacy decomposes into
   generation, entitlement and service, generation and entitlement are state
   coordinates governed by the other conditions, and service obligations are
   liabilities that answerability already conserves.
5. **Attack J is reported as a type mismatch rather than a counterexample.** Both
   arms of the cost pair are licensed and both satisfy the target; "chosen because
   it closes the books" is a fact about a policy's counterfactuals, and no
   predicate of a trajectory expresses it.
6. **The environment is a modelling device.** §II asks for an independent target;
   the only way to get one was to posit a structure the reasoner does not control.
   The round does not claim such a structure exists or is knowable, and says so
   where the target is stated.

## What this does not establish

- Nothing is kernel-checked; nothing is registered in `CLAIMS.md`.
- Sufficiency is refuted, not disproved in general: six finite counterexamples
  and one measurability argument, in one small model class.
- The reasoner-relative reading is *not* shown sufficient. The counterexamples
  evaporate on it by construction, which is a reason to think it might be
  provable, and no proof is offered.
- The scope-bound question — union or intersection — is displayed as a real fork
  and left open.
- The arrival process is declared, so an advisor controlling what *arises* is
  outside the model, as it was before.
- That this round's boundary and the previous round's are one theorem rather than
  two instances of one shape is stated as a resemblance and is unexamined.
- No corrigibility composition was attempted.

## Filings

Items 40–44 filed in `PRIORITIES.md` under this round's dispatched scope, with
this prompt as the authorization.

## New names introduced, all provisional

`procedural legitimacy`, `provenance validity`, `authority scope`, `inquiry
generation`, `inquiry entitlement`, `service window`, `descent forest`,
`prospectivity`, `disclosure`, `substantive drift`, `reasoner-relative` and
`environment-relative` readings.

## Outstanding maintainer actions

1. **Rule on the two readings of the target.** The round found the dispatch's
   prose target ambiguous between a reasoner-relative and an environment-relative
   reading, and the sufficiency verdict differs between them. *Doing it* is
   reading `rounds/2026-08-13-procedural-legitimacy/L_STAR.md` §"Two readings" and
   saying which the programme means. *Waiting* leaves every future sufficiency
   claim ambiguous in the same way.
2. **Rule on disclosure versus prospectivity.** The round recommends disclosure
   as a recording requirement and rejects prospectivity as a prohibition, on the
   evidence that prospectivity refuses the positive control. *Doing it* is one
   decision over the table in `THEOREM_MAP.md` §5. *Waiting* costs nothing; the
   attacks are recorded either way.

Both are appended to `DECISIONS.md`'s *Awaiting the author*.
