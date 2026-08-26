# Report — legitimate evolution and cross-process recognition

**Verdict: LEGITIMATE-EVOLUTION-CONSUMABLE.**

Both halves of the addendum's upgraded standard are met and checked. There is an
implementation-neutral succession frame with six axioms; a register of offices
and appointments satisfies all of them, imports the interface module and nothing
else of this repository's, and refuses a laundered warrant. Reflective Integrity
with the Carroll challenge operator satisfies the same six, five of them
unconditionally and one — issuance stability — exactly where the record's
schemas are pre-state-blind. Both realizations run the same theorems.

The verdict is not unqualified, and the three reservations are in the round's
`README.md` and `THEOREM_MAP.md`: recognition transport is an axiom plus two
theorems and not a theorem; the counterfactual half of a certificate does not
compress in our realization; and the interface constrains the form of a
legitimacy calculus, not its coverage.

Deliverables are at
`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/`.

---

## Deviations from the prompt

**The prompt says PR58 is merged; `main` carries the Carroll round without a
pull-request number in its message.** `44d1821` — "The Carroll round: reproduce
the paper, prosecute the criterion, close it" — is `main`'s head and is the
round the prompt names, so the round is based on it. The number is not verifiable
from the tree and is not asserted anywhere in the deliverables.

**`≺_L` is not a binary relation on standings, and `≼_L` is not its
reflexive-transitive closure.** §§4-5 propose both. A supersession may consume
several authorities at once, so a *chain* through the clean one of a pair does
not carry the pair, and a process could present a flattering path. The relation
shipped is a derivability judgment `G |- y` over finite trees, requiring **all**
of an exercise's sources. `warrant.merge_register` is the register that decides
it; our own architecture cannot, because `G6` refuses a supersession with an
absent target.

**The theorem family of §18 is reorganized rather than filled in.** `T5
Answerability Preservation` split into three results and moved out of the central
statement, for the reason §13 asked the round to look for. `T6 Recognition
Transport` is reported as an axiom plus verifier soundness plus composition, per
§8's own instruction not to disguise a bridge principle. `T7` is a document, not
a theorem.

**`LegitCert(x0, x)` is over a base *set*, not a single `x0`.** Forced by the
all-of-sources decision above.

**The round ships two reference models and 32 tests, against §20's "not a request
to produce a large Python fixture suite."** The second realization is the only
evidence that the interface is about legitimacy rather than about a ledger, and
it cannot be prose: the claim is that a system with no normative record satisfies
the axioms and refuses the laundering, and that is a thing one runs.

**The addendum arrived after the record-side model was written.** The chain
machinery it contained was folded into the realization module and the file
deleted rather than left as a second, redundant statement of the relation.

---

## The final questions

**1. What is the exact type of immediate legitimate succession?** Not a relation
on two standings. In the abstract interface it is a *certified exercise*:

```text
Certified_q(t)  :=  q |= lic(t)  and  q |= t          t : T,  q : Q
```

with `src, tgt : T -> Pfin(A)` and `lic : T -> A`. The edge it induces is
`src(t) -> tgt(t)`, many-to-many and challenge-relative. The realization maps `T`
to `NormEvent`, `A` to `StandingId` and `q |= ·` to survival under the excised
replay.

**2. What is the exact type of legitimate evolution?**

```text
G |-_q y  :  Pfin(A) x Q x A -> Prop     the least set containing G and closed
                                          under certified exercises all of whose
                                          sources are already in it
G |- y    :=  forall q in Q. G |-_q y
```

A derivability judgment over finite trees, not a reflexive-transitive closure of
a binary relation, and quantified over challenges rather than composed across
them — because the challenge operator is neither monotone nor composable.

**3. What non-tautological global theorem follows from the local conditions?**
Two, and they are different in kind.

*T2, lineage existence.* Under precedence and no-ex-nihilo, every authority has a
finite well-founded provenance whose minimal elements lie in the base, **with no
legitimacy clause taking part**. This is what keeps the theory off Failure A:
*having* a lineage is earned from the local rules, *having a certified one* is
the extra content, and the two come apart on `C10`, where the manufactured
protocol is in force, reaches the seed, and is not derivable.

*T3, no self-ratifying authority.* Step-local obligations — stability of one
licence and one exercise — give a global conclusion: no authority anywhere in a
certified provenance, at any depth, was issued by an exercise the challenge
challenges. That is §6's "global path property from step-local obligations",
which was the strongest of the six shapes the prompt offered.

**4. What prevents self-ratifying authority?** Three axioms and not one. *Origin
necessity* (an authority survives a challenge only if its issuer does) is the
half that does the work; *issuance stability* is its converse and carries the
induction; *challenge bite* is what makes the counterfactual be about something.
Splitting the first two is this round's sharpest structural finding: in the
realization origin necessity holds from the identifier scheme alone and issuance
stability needs pre-state-blindness, so they are different hypotheses that the
Carroll round stated as one argument.

**5. Can legitimate authority survive genuine normative content change?** Yes,
and by the type rather than by a witness: the frame has no content field, so no
clause of `|-` can read what an authority says. The witnesses are that the
realization inherits it — relabelling every value specification in a record
leaves the derivable set fixed — and `C11`, `C14` and `C33`, which are revision,
divergent-provenance and later-independent-adoption respectively.

**6. What does answerability add that authority succession alone does not?**
Two constructors and one fact, and **not** a clause of succession. A delegation
has `src(t) = tgt(t)` and issues nothing, so on the authority graph it is a
self-loop and only the account layer distinguishes it from a no-op. A disposal
has `tgt(t) = {}`, so the authority graph has no edge at all and only the ended
account records it. And *visible discontinuity* is the only clause of the whole
interface that can fail with the authority side clean.

The countermodel that settled it is `delegated_custody(answered=False)`: a clean
spine, a derivable authority, and a base account outstanding forever. So
answerability is not constitutive of the *authority* — and putting it in `|-`
would refuse a case in which nothing about the authority is wrong. It is
constitutive of the process being an answerable one, which is a different
question, and it belongs on the recognizing process's side of the interface.

**7. What is the minimum certificate another process needs?** A base, a target,
a finite derivation, the challenges it was taken against, and the stability
judgments each step relies on. The derivation is canonical under unique issuance
— there is only one, so a flattering lineage cannot be presented — and finite in
the size of the target's provenance. If the recipient also wants answerability it
must be given the *branching*, not the chain: `split_with_due_branch` is a record
where the derivation is clean and the base is discontinuous.

**8. What assumption lets recognition transport?** That the recognizing process
treats certified succession from a base it accepts as preserving its recognition.
Two theorems narrow what that commits to: verifier soundness, and the fact that
`|-_q` is a least fixed point, so one commitment covers arbitrarily long
evolution rather than needing one per step.

**9. Does that assumption amount to a substantive philosophical axiom?** Yes.

> **(R)** `A` regards inheritance of authority through a certified succession
> from a base it accepts as preserving its recognition.

It is stated as an axiom in `CROSS_PROCESS_INTERFACE.md` §1 and is not derived.
What the mathematics contributes is that (R) is a commitment to L0-L4 being the
right conditions and to nothing else — in particular not to any claim about what
the future authority says.

**10. Can the current cross-process trust/deference theorem consume this
interface?** Not as it stands, and the obstacle is one field on the consumer's
side. `GradeTrust EX W eta` at `DelegationBridge.lean:52` types `W` as
`C -> P -> Q` with **no index** — no time, no process, no standing — so the
premise has nowhere to attach. The required change is `W : A -> C -> P -> Q` plus
the hypothesis that the grade is a function of the authority in force. Neither
revises a registered statement, since `delegation_bridge` is proved for every `W`.

The deference line diagnosed this hole itself. `FUTURE_AGENT_SPEC.md`'s status
block concludes that its construction collapsed because "the authorisation
relation has to be in the type", and four questions later that "value drift is
deliberately excluded". This round has produced an object of that type.

**11. What would the corrigibility theorem approximately say?**

```text
Recognizes_A(G)  and  B |= LegitimacyInterface  and  G |-_B x
GradeTrust EX W_x eta,  W_x a function of the authority in force
EffectiveAuthority: the principal's corrective capability survives every
                    advisor policy in scope
--------------------------------------------------------------
A has no strictly dominant preemption on the protected domain
```

Statable, and not provable: the third hypothesis has no formal object.
`ReachableCorrectiveControl`'s registered refutations
(`advisor_has_a_universal_veto`, `canCorrectFuture_measures_advisor_cooperation`)
say its capability predicate is satisfied by the advisor's leave rather than
against its opposition. Legitimacy does not supply that and this round does not
try; standing and effective causal access were separated by the
relational-scorekeeping bridge and shown independent in both directions.

**12. Which parts remain Carroll-specific?** In the abstract interface, none —
that is the addendum's result. In the realization, three: the challenge is an
influence episode's ancestry class computed in the settlement-reference graph;
stability is survival under the excised replay; and the challenged set is read
off the reason ledger. All three are realizations of `Q`, `|=` and `Chal`, and a
later consolidation replaces them by supplying different ones rather than by
changing a theorem. `prospective_license` is the one thing not lifted, and it
should stay unlifted: it is act-relative and reads content.

**13. Which primitive normative seams remain?** Three, unchanged in number.
*Base recognition* — L0, now an explicit axiom rather than a fact inside a
definition; legitimacy is definable only relative to a base, and this round makes
that visible instead of removing it. *Challenge coverage* — `Chal` and `Q` are
only as wide as the record's provenance links, which is the Carroll round's `C25`
hypothesis. *Content seams* — `covers`, a protocol's `condition` and the fact
vocabulary, which belong to `prospective_license` and never enter `|-`.

**14. What is the strongest counterexample?** Provenance incompleteness, and the
abstraction makes it worse rather than better. An external process satisfying
L0-L4 with a challenge set naming almost nothing is certified by the interface,
because the axioms are conditions on the *form* of a legitimacy calculus and not
on its coverage. That is the largest remaining hole and no axiom here addresses
it.

**15. Refine the counterfactual, or consolidate?** Neither first. The round's own
answer is that the next thing is a **Lean port of the abstract layer**, which is
finite, first-order, has no dependency on either reference model, and would make
the frame the first thing in this line with a statement of record. Refining the
counterfactual semantics is now a question about one realization's `|=` rather
than about legitimacy, which is a smaller and better-posed question than it was
before the addendum; and consolidation should follow the port rather than precede
it, because the port is what would say which vocabulary survives.

---

## The addendum's questions

**16. The minimal implementation-independent interface.** Eight pieces of data —
authorities, exercises, `src`, `tgt`, `lic`, a well-founded `rank`, a challenge
set with `Chal`, and a stability relation — and six axioms: base stability,
precedence, no ex nihilo authority, unique issuance, issuance stability, origin
necessity, challenge bite. Plus an optional account layer of two axioms.

**17. Which notions are genuinely semantic?** *Precedence*, *no ex nihilo
authority* and *unique issuance* are ordinary well-foundedness and origin
conditions, intelligible for any granting practice. *Base stability*, *issuance
stability*, *origin necessity* and *challenge bite* are conditions relating a
counterfactual to a grant structure, and each has a reading that constrains an
institution. None is a renamed Reflective Integrity concept: the evidence is that
the warrant register satisfies all seven, and that two of them behave differently
there — issuance stability is free in a monotone dependency model and is a real
hypothesis in a replay model.

The account layer is closer to a rename. Carriage and trichotomy are Reflective
Integrity §§15-19 abstracted, and the round did not find an independent
institutional reading that adds anything to them.

**18. Can an external process satisfy the interface without a ledger like ours?**
Yes, and it is checked rather than argued. `src/warrant.py` is a register of
offices and appointments; `test_frame.py` parses its imports and asserts that
`frame` is the only one of ours.

**19. The realization map.** In `LEGITIMATE_EVOLUTION.md` §7, with an
axiom-by-axiom table saying which Reflective Integrity statement discharges each:
Fresh Allocation for no-ex-nihilo and unique issuance, `G4`/`G6` for precedence,
the identifier scheme for origin necessity, the `G2` cascade for challenge bite,
§§15.2 and 17 for carriage, §19 for trichotomy. `L0` is a theorem there because
excision cannot reach the seed.

**20. Which conclusions are abstract and which only realization?** Everything in
`T1`-`T4` and `T6` is abstract. What belongs only to the realization is the
*cost*: that stability is a replay, that the operator is neither monotone nor
composable, and therefore that the counterfactual half of a certificate does not
compress. That last is the single most consequential thing the abstraction
clarified — it was previously readable as a defect of legitimacy and it is a
property of one implementation.

**21. Can the deference theorem quantify over arbitrary implementations?** Yes.
`B |= LegitimacyInterface and G |-_B x` are conditions on the frame, and
`CertifiedDelegation` in `CONSUMER_TEST.md` §2 is written that way.

**22. The irreducible recognition axiom.** (R), above. One axiom, and it is a
commitment to the seven conditions rather than to any content.

**23. Does recognition remain content-independent?** Yes, by the type at the
abstract level and by a checked relabelling at the realization level.

**24. Does the abstraction reject Carroll-style laundering without Carroll-specific
objects?** Yes. `warrant.laundered_register` has an inspector citing a warrant
granted on the very finding under challenge; nothing in it is a normative record,
and `G |-_q` excludes both the warrant and what it issued. `merge_register` does
the same for laundering through a merge — and it is the register that decided the
all-of-sources rule, which our own architecture could not.

---

## What this round does not establish

No Lean and no registered claim. Every theorem is a paper derivation exercised on
finite records, and the realization theorem is an argument from Reflective
Integrity's own statements — which are themselves unregistered.

The axioms are conditions this round wrote and most of the countermodels are ones
it wrote too. Two are not, and they are the only evidence the exercise was
adversarial: the Carroll round's `C28`, which killed the unconditional form of
the realization theorem and forced issuance stability to become a hypothesis; and
Reflective Integrity's `G6`, which made the all-of-sources decision undecidable
inside our architecture and forced a second realization to settle it.

Recognition transport is not proved and is not claimed to be. The desired answer
set for the addendum's §H negative test is four *yes/yes/no/no*; the round gets
three, and the third is qualified rather than met, because in our realization `A`
must hold `B`'s record, challenge it interactively, or accept an attestation.

The account layer's abstraction is weaker than the spine's. It is Reflective
Integrity's answerability structure with the names changed, and the round found
no second reading that tested it.

Nothing here says how a process comes to be *entitled* to the stability
judgments, as against a theorem consuming them.

---

## Outstanding maintainer actions

1. **Rule on whether the deference kernel's grade acquires an index.** Append the
   entry now in `DECISIONS.md`'s *Awaiting the author* — the change is
   `W : C -> P -> Q` to `W : A -> C -> P -> Q` in
   `lean/Workspace/Deference/Contrib/DelegationBridge.lean`, plus a stated
   hypothesis that the grade is a function of the authority in force. It touches
   a specification-layer Lean file in a line the wiki records as paused, and it
   is the whole of what stands between this interface and a consumption.
   *Turns on:* whether the deference line is being restarted, and what a paper
   needs. The round has no evidence either way and does not adopt it.

2. **No other item is reserved.** The two forks the round did face it adopted, as
   dated `DECISIONS.md` entries marked agent-decided and reversible: that
   answerability continuity is not a conjunct of legitimate succession, and that
   derivability requires all of an exercise's sources.

---

## Attribution

| | |
|---|---|
| prompt author | a maintainer, with a model-assisted draft; the addendum was sent mid-round |
| executor | Claude Opus 5 (Anthropic) |
| dates | 2026-08-25 |
