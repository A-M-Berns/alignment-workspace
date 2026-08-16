# Source map

Three registers, kept apart throughout. **SOURCE** is what *Making It Explicit*
says, cited by chapter, section and page of the Harvard University Press
paperback edition (first paperback printing, 1998), with the content quoted
inline rather than cited by remembered label. **ANALOGUE** is what this round
implemented. **INFERENCE** is this round's own conjecture about why the analogue
might matter, and carries no authority from the source.

Page numbers were read from the copy's own running heads. Where a passage
straddles a page break the range is given.

No claim below is that the source proves a mathematical result here. Where the
source does not support a move, the row says so.

---

## 1. Commitment and entitlement are two statuses, neither defined from the other

**SOURCE.** Ch. 3 §II.2, pp. 159–161. Commitment and entitlement "correspond to
the traditional deontic primitives of obligation and permission", and the text
declines to define either by negating the other, because doing so "requires
taking a formal notion of negation for granted". The relation is used in the
other direction, to get "a material notion of negation, or better,
incompatibility": *two claims are incompatible when commitment to one precludes
entitlement to the other* (p. 160).

**ANALOGUE.** `Practice.committive`, `Practice.permissive` and
`Practice.incompatible` are three independent fields. `State.blocked` implements
the incompatibility clause literally: a content is blocked for an agent when the
scorekeeper attributes that agent a commitment to something paired with it.
Neither status is derived from the other.

**INFERENCE.** The independence is what lets an undercutter defeat entitlement
while leaving commitment standing, which is the gap the applicability attack
runs through. A single-sorted "permitted response" state — which is what the
learning line's constraint statics currently carry — cannot express it.

---

## 2. Scorekeeping is perspectival, and attribution is the fundamental attitude

**SOURCE.** Ch. 3 §II.5, p. 166: practitioners "keep score on deontic statuses by
attributing those statuses to others and undertaking them themselves", and "of
these, attributing is fundamental". Ch. 8 §VI.3, p. 596: "Acknowledging a
commitment can be identified with attributing it to oneself."

**ANALOGUE.** `State.commitments(scorekeeper, target)` is indexed by both agents.
Self-score is the diagonal, not a separate mechanism.

**INFERENCE.** None needed; this is a direct transcription.

---

## 3. Consequential commitment is computed with the *scorekeeper's* auxiliary premises

**SOURCE.** Ch. 8 §VI.3, pp. 596–597. "What one is really committed to by an
acknowledgment … is to be assessed by conjoining it with truths — that is,
statements of fact. But what plays this role for a scorekeeper is the set of
sentences by the assertion of which the scorekeeper is prepared to acknowledge,
and so undertake, doxastic commitment." And: "the consequences of a particular
acknowledgment are assessed differently from different perspectives — that is, by
different attributors … But how this line is drawn in particular varies from
scorekeeper to scorekeeper."

**ANALOGUE.** The one equation the round turns on:

```
commitments_i(j) = closure of Ack_j under I_i
```

The target supplies the acknowledgments; the scorekeeper supplies the rules.

**INFERENCE.** This is the round's central conjecture and the source does **not**
state it as a repair to anything. The inference is that this equation is exactly
the missing object in the procedural-legitimacy obstruction: there, the reasoner
held its own copy of a relation the environment also held, and no predicate of
the reasoner's trajectory could compare copy against original. Here there is no
original — there is a second participant's copy, which the reasoner has no move
to write, and which is itself contestable by the same grammar. Whether that is a
repair or a relocation of the problem is prosecuted in `PROSECUTION.md`, not
settled by the citation.

---

## 4. Acknowledged and consequential commitments diverge

**SOURCE.** Ch. 3 §IV.6, p. 194. "These consequential commitments may not be
acknowledged; we do not always acknowledge commitment to all the consequences of
the commitments we do acknowledge. They are commitments nonetheless."

**ANALOGUE.** `State.unacknowledged_consequences`, and the first component of the
public loss.

---

## 5. Disavowal does not succeed while the basis stands

**SOURCE.** Ch. 3 §IV.5, pp. 192–193. "B's disavowal of p can be successful
(according to A) only if B is also prepared to disavow q. Indeed, disavowing p is
indirectly disavowing q. But if B persists in asserting q, that commitment is
incompatible with the disavowal, and the disavowal of p cannot accordingly
reinstate entitlement…"

**ANALOGUE.** `Move("disavow", …)` removes an acknowledgment and nothing else;
`commitments` is recomputed by closure. T1 is a consequence, not a clause.

**INFERENCE.** The source is about a scorekeeper's assessment of a disavowal. The
inference this round adds is that the same structure blocks *self-exculpation by
rule revision*, which the source does not discuss: revising `I_H` moves the
diagonal and leaves `commitments_C(H)` fixed. That is T2, and it is this round's
extension rather than the source's claim.

---

## 6. Challenge is generated by entitled incompatibility, and challenges are not privileged

**SOURCE.** Ch. 3 §III.4, pp. 177–178. Entitlement has "a default and challenge
structure"; a challenge takes effect when "the challenger is entitled to the
challenge"; "the simplest way to implement such a feature … is to require that
the performances that have the significance of challenging entitlements to
assertional commitments themselves be assertions. One then can challenge an
assertion only by making an assertion incompatible with it … Then challenges have
no privileged status: their entitlement is on the table along with that of what
they challenge." And p. 193: "There is no reason in principle that conflicts of
this sort need to be resolvable."

**ANALOGUE.** `State.challenge_is_entitled` derives force from the challenger's
entitlement to a materially incompatible ground. `Challenge` is a bookkeeping
record with no force of its own. T3's unresolved two-way conflict is the last
sentence.

**DEVIATION.** The source lets a challenge's own entitlement be challenged in
turn. The implementation reads the challenger's entitlement at default level and
does not iterate, which is a declared stratification adopted to keep the fixed
point monotone and terminating. It is recorded in `MODEL.md` under what was not
shown.

---

## 7. Objectivity is a structural feature of every perspective, not a privileged one

**SOURCE.** Ch. 8 §VI.3, pp. 593–597. The criterion of adequacy is that an
account "make sense of a distinction between how [concepts] are applied in fact,
by anyone or everyone, and how they ought to be applied". Understanding
objectivity as intersubjectivity is rejected because it loses "the capacity to
make sense of the distinction between correct and incorrect claims … on the part
of the whole community": "even if all of us agree and always will agree … the
possibility remains that we are all wrong". The resolution: "the distinction
between claims or applications of concepts that are objectively correct and those
that are merely taken to be correct is a structural feature of each scorekeeping
perspective", and "objectivity is a structural aspect of the social-perspectival
form of conceptual contents".

**ANALOGUE.** No oracle field exists. T3 and T4 are witnessed inside the model:
every agent scores every agent, so each is challengeable; and a unanimous
position is convicted by the consequential closure meeting an incompatibility
that all of them endorse.

**INFERENCE.** The source is arguing about conceptual content. The inference is
that this is the exact structure the four kill criteria K1–K4 demand — a
correctness distinction with no self-oracle, critic-oracle, community-oracle or
environment-oracle. The finite witnesses show the distinction is expressible;
they do not show the source's larger thesis.

---

## 8. Practical authority is a different structure from testimonial authority

**SOURCE.** Ch. 4 §IV.3, pp. 238–243. "There is nothing corresponding to the
authority of testimony in the practical case"; the responsibility to vindicate a
practical commitment is "exclusively a justificatory responsibility". "What I
take-true I thereby, ceteris paribus, authorize you to take-true … What I (seek
to) make-true, however, I do not thereby in general authorize you also to (seek
to) make-true", because "you and I may have quite different ends, subscribe to
different values, occupy different social roles, be subject to different norms".

An interpersonal practical authority can be added "as a superstructure", and it
has three disanalogies. It is **scoped**: "the licensing is restricted as to
subject matter and the interlocutors involved, to those situations in which a
prior superior/subordinate authority relation has been established" (p. 241). It
is **asymmetric**: assertion "is an egalitarian practice in a sense in which
commanding and giving permission is not", since asserters are "authorized to
authorize others in the same sense in which they are authorized", whereas "only
in very special cases does the practical license one is given authorize the
further issuance of such licenses" (pp. 241–242). And the asymmetry is
load-bearing: "if subordinates have the same authority as their superiors …
the entitlement of a superior to issue a command would be subject to challenge by
commands issued by subordinates … and the hypothesized asymmetry … would
disappear" (p. 243).

**ANALOGUE.** Three implemented consequences, one per disanalogy.

| source point | implementation | test |
|---|---|---|
| no testimonial analogue in the practical case | `deferrals` and `testimony_permitted` transmit entitlement; no move transmits a grant | C1 |
| scoped to subject matter and to agents | `Grant(holder, subject)`, read by `may_perform` | C2 |
| no reassertion licence | holding a subject does not license granting it; granting needs the reserved subject `authority:<holder>` | C2 |

**INFERENCE.** The source separates the two authority structures; it does not
claim the separation bears on machine corrigibility. The inference is that this
separation is the missing authorization object the deference line named, and that
C1's negative — epistemic authority reaching no practical jurisdiction under any
advisor run — is the formal shadow of "what I take-true I authorize you to
take-true; what I make-true I do not".

---

## 9. Normative vocabulary makes explicit what was implicit in practice

**SOURCE.** Ch. 4 §V.3, p. 248, titled "Normative Vocabulary Makes Explicit
Material Proprieties of Practical Reasoning"; and Ch. 2 §IV, "Material Inference,
Conceptual Content, and Expression", p. 94, where a claim can make explicit an
inferential propriety that was implicit in what practitioners do.

**ANALOGUE.** `a_rho`: a content asserting that the pattern `rho` applies. It is
an object of commitment, entitlement, challenge and defeat, and it sits in
`rho`'s premise set as an ordinary content.

**INFERENCE, and the round's own constraint.** The source is not committed to any
claim about rule regress in a formal system. This round's constraint — that
asserting `a_rho` must **not** install `rho` — is imposed by the round, and it is
what keeps the applicability object from generating a tower of rules licensing
rules. The test that an agent whose practice lacks `rho` draws nothing from
`a_rho` is where that constraint is checked.

---

## 10. What the source was not used for

- No claim here that the source's account of conceptual content is correct.
- No claim that the source addresses machine learning, corrigibility, regret,
  or delegated authority. It does not.
- The source's expressive-completeness material (Ch. 9) was read and **not**
  used: nothing in this round turns on a practice becoming able to score its own
  scorekeeping, and a row asserting otherwise would be decoration.
- The reliability material (Ch. 4 §§II–III) was read and used only for the shape
  of noninferential entitlement in T4's observation witness. The round does not
  model reliability, reference-class gerrymandering, or observational authority,
  and `s` is an ordinary content entitled by acknowledgment rather than a modelled
  perceptual input.
