# Answerable Revision under revisable warrants

Status: **specification, reference models and a prosecution record;
unregistered.** All names provisional under `AGENTS.md` §6. No Lean, no
registered claim.

Frozen Legitimate Evolution is untouched. `replay.py` and `answer.py` are
imported unchanged and a test asserts by AST parse that only `Duties`, `Ob`,
`Frame`, `Edit`, `Occ`, `BASE`, `incurred` and `outstanding` are read.

## A. Verdict

```text
ANSWERABLE-REVISION-SURVIVES
```

Secondary:

```text
THE-CONTENT-IS-PROMOTION-PERMANENCE, not the closure theorem
PRE-PROMOTION-SEALING-OUT-OF-SCOPE
```

Standards may change; reasons incurred under them remain answerable. The
reflective case works with no meta-hierarchy. The honest qualification is that
**most of the theorem is inherited** and the new content sits in one premise.

## B. The theorem

At the strict pre-state of `t`, let `W` be standing, `E` admissible under `W`,
and `Promote(W, E) = rho`.

> **Answerable Revision.** Under `P1` and frozen `A1`, for every later `s`:
> `rho` is incurred at `s`, and is either outstanding at `s` or was resolved by
> an accepted resolution in `(t, s]` — however `P`, `Lambda` and `W` change in
> between.

*Proof.* Promotion puts `rho` in `opens_t`, so frozen
`Incurred_{t+1} = Incurred_t u opens_t` incurs it and `Incurred` never shrinks.
Frozen `A1` lets it leave the outstanding set only through an accepted `Resolve`.
A warrant revision is not a resolution and appears in neither fold. ∎

**The proof is three lines because it is nearly all inherited, and saying so is
part of the result.** What is *not* inherited is `P1`.

### P1, promotion permanence

> What was promoted at `t` is a function of the state at `t`.

A process that re-derives its own past under present standards violates this, and
**frozen Legitimate Evolution would not notice**: its premises govern how claims
*leave* the outstanding set, and this attack works by preventing them from
arriving. `AR4` is that process; `test_and_the_theorem_alone_does_not_catch_it`
asserts that the closure theorem, `A1` and Grounded Replay are all clean on it
while the reason simply never exists.

So the round's actual content is one premise and one corollary:

> **No retroactive erasure.** A reason that occurred legitimately is incurred at
> the end, whatever the warrant now says.

## C. The promotion interface

```text
Warrant      wid, target, admits(E), promotes(E)
Evidence     eid, about, form, strength
Reason       payload, under, at          identity records where it came from
History      standing(t), promoted_at(t), resolutions
```

Four things the round refuses to collapse:

```text
a true counterfactual comparison   epistemic validity
admissible evidence                what a standing warrant will look at
a revision reason                  what promotion produces
a Due obligation                   what a supplied Due semantics may then say
```

**The reference realization collapses the last step, deliberately, and the round
did not say so.** `warrant.duties` wires every promoted reason straight into
frozen `opens`, which *is* incurrence. So the fixtures adopt

```text
promotion  ->  answerability incurrence
```

as one **canonical constitution**, not as a claim about every normative system.
The generic theory does not identify a revision reason with a Due obligation, and
the two statements it actually supports are:

> **Historical Reason Persistence.** A promotion that occurred at `t` is a
> permanent historical event. That is `P1`, and it needs no Due semantics at all.

> **Answerable Revision.** *If* the supplied normative semantics makes a promoted
> reason incur an answerability claim, then frozen Legitimate Evolution prevents
> later warrant, evaluator or policy revision from silently erasing it.

Everything below is stated under the canonical instance. A constitution that
promotes reasons without incurring claims gets the first statement and not the
second, and this round exhibits no such constitution.

`Reason` identity is `(payload, under, at)`. The warrant and the position are
part of it because the claim is historical: this reason was promoted *under that
warrant, at that time*. A later warrant cannot make it a different reason and
cannot make it not have happened.

**Transition order.** `standing(t)` reads installs strictly before `t`. So a
revision is evaluated by the warrant it replaces, never by itself.

## D. The revisable warrant

`W_t -> W_{t+1}` is ordinary legitimate revision and nothing here fixes an
eternal meta-warrant. The fixed substrate is only:

```text
how current warrant standing is identified
how a standing warrant is read at the strict pre-state
how a promotion occurrence is recorded  (write-once: P1)
how later reasons remain historically incurred  (frozen Incurred)
```

Substantive warrant content — which baselines, which comparative forms, which
targets — is revisable throughout. The round takes no view on which
admissibility rule is correct, and `AR2` installs a genuinely narrower successor
that would not have promoted the evidence it inherits.

## E. Historical validity is not current endorsement

Two predicates, deliberately distinct:

```text
occurred_legitimately(rho)   was it promoted under a then-standing warrant
currently_endorsed(rho)      would the warrant standing now promote it
```

They diverge in `AR2`, `AR3` and `AR10`, and divergence is **not** a violation.
It is the state the round exists to make expressible:

> *This really was a reason we incurred under our then-legitimate standards, and
> we now reject its force for reasons S.*

That is revision. What is forbidden is:

> *Because our standards changed, there never was an answerability relation.*

That is laundering, and it is `AR4`.

## F. Countermodel table

```text
AR   what it does                          result          who owns it
1    policy revision after promotion        outstanding     caught
2    warrant revision after promotion       outstanding     caught; diverges
3    evaluator revision after promotion     outstanding     caught; diverges
4    retroactive invalidation               P1 fires        the round's premise
5    legitimate defeat, Resolve accepts     answered        caught
6    trivial defeat                         answered        structural only
7    supersession by a better repair        answered        no new machinery
8    same-step self-authorisation           nothing promotes strict pre-state
9    preemptive self-sealing                nothing promotes OUT OF SCOPE
10   criticism of a warrant                 outstanding     caught; reflective
```

Every hypothesis and the countermodel forcing it:

```text
P1                     AR4.  Without it the theorem is vacuous rather than false.
strict pre-state       AR8.  The installed warrant *would* have promoted the
                             evidence; the refusal is the reading, not the case.
frozen A1              inherited; the improvement round already prosecuted it.
```

## G. The reflective case, without a hierarchy

`AR10`: a standing warrant admits comparisons **about warrant protocols**.
Evidence criticises `W` itself, promotes `rho_W`, and `W` is then replaced. The
reason survives.

No `W^0, W^1, W^2, ...` is introduced. `Warrant.target` is an ordinary
identifier that may name a warrant, and a test asserts the module contains no
`meta`, `level`, `hierarchy`, `rank` or `order` identifier. **The ambitious
architecture does not require an immutable meta-warrant**, which was the failure
mode the dispatch asked to watch for.

## H. The improvement round, recovered

The merged round is one warrant:

```text
admits    evidence of the incumbent-versus-repair form about the diagnosed target
promotes  when accumulated advantage crosses a threshold
```

Its withdrawal challenge is then an ordinary Answerable Revision instance, and
its boundary is recovered by the same route: `pr60_undemonstrated` withdraws
below the threshold, nothing promotes, and nothing is answerable — which is that
round's CM2 one level up.

**The specialization is one-directional and that is worth stating.** This round
begins at promotion, so it inherits nothing about what happens while the repair
is still live. Repair regret governs that, and `warrant.py` names no regret
quantity at all. The two rounds compose by sitting on either side of the
promotion event, not by one containing the other.

What the improvement round contributes and this one does not replace: the
evidence/uptake-regret separation, the repair-regret kernel, and No Free Evasion
for a demonstrated repair's withdrawal.

## I. Responsive Revision — not claimed

The quantitative follow-up would say that while an outstanding reason supports a
live repair, low repair regret prevents indefinitely leaving it unused. It would
import the improvement round's Theorems A and B and require a service premise
this round does not have. **Not claimed and not built.** Answerable Revision does
not depend on it.

## J. Boundaries

**Pre-promotion self-sealing (AR9).** The warrant narrows itself before the
criticism can be promoted. Nothing promotes, so nothing is answerable, and the
narrowing is legitimate under every premise here and in frozen LE. Answerable
Revision begins *at* promotion and cannot reach behind it.

This is structurally the same boundary the improvement round found one level
down — a repair retired before it was demonstrated. The same shape appearing at
two levels is some evidence it is the real boundary of this family rather than an
artefact.

The frontier it names:

> **Reflective openness.** A cognitively significant component cannot permanently
> immunize itself from relevant criticism merely by controlling whether that
> criticism is represented, serviced, evaluated or promoted.

That will need inquiry, service, exploration or anti-manipulation, and none of it
is smuggled in here.

**Also outside:** evaluator manipulation; whether a defeat is substantively good
(`AR6` is answered and may be worthless); long-horizon and policy effects; delay.

## K. Export property

> A process is **answerably revising** when reasons legitimately generated under
> its operative standards remain matters it must incorporate or explicitly answer
> — even as those operative standards, and the standards for what counts as a
> reason, themselves change.

It does not say the process must keep its standards, must agree with its past, or
must adopt what a past reason recommended. It says a change of standards is not a
way of never having owed anything.

Conceptually usable for an institution or a deliberative body without claiming
either satisfies RI. Not connected to deference here.

## L. Freeze / do not freeze

```text
FREEZE
  promotion permanence (P1) as the round's own premise, distinct from A1
  historical validity and current endorsement as separate predicates
  strict pre-state reading of warrant standing
  Reason identity carrying the warrant and the position
  the reflective case needs no meta-warrant
  Answerable Revision begins at promotion

DO NOT FREEZE
  the Warrant tuple. It is the smallest that carried AR1-AR10, not a derived
    minimum, and only one promotion rule has been exercised per fixture
  the promotion rule interface; every fixture promotes deterministically
  whether promotion should be a ReasonOcc in RI -- not settled, not attempted
  the specialization of the improvement round; it is one-directional
  anything about Responsive Revision
```

## M. What no claim above asserts

- No claim that the process must adopt what a promoted reason recommends.
- No claim that a defeat is correct. `AR6` accepts a bare refusal.
- No claim about criticism that never reaches promotion. `AR9` is legitimate here.
- No claim that the round is deep. The closure theorem is three lines of
  inheritance; the content is `P1` and the two-predicate distinction.
- No claim that RI realizes any of this. Promotion is not mapped to a `ReasonOcc`
  and no RI event kind was added or proposed.
