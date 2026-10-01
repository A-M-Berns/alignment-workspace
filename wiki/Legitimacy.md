# Legitimacy

Legitimacy is the bridge between [Normativity](Normativity) and
[Deference](Deference). Normative learning needs public reasons and responses that
the learner cannot rewrite for convenience. Corrigible deference needs a human
corrective power that the advisor cannot quietly preempt, and a judgment that is the
principal's own. Both depend on the same thing: what may happen to a trajectory's
record, its verdicts, and its channels of influence.

**Status: the generic theory is canonical; its record half is Established
`lean-proved`.** The record objects below have Lean definitions and registered
theorems; authorship has one registered theorem; transparency's posterior and
non-steering statements are registered. The definition of legitimacy as a whole is a
Lean structure conjoining them, and the theorem that it satisfies the thin
specification below is registered. Every assumption the theory does not discharge is a
typed input named on the page that consumes it. The theorems, stated with hypotheses,
conclusions and Lean names, are on the [Theorem Spine](Theorem-Spine).

## Legitimacy has two levels

**The thin level is a specification**: what a legitimacy concept must do.  Its content is
that the process *preserves* her self-trust; it does not guarantee that she has any, and
no claim is made that legitimate change tends toward an ideal.  **The thick level is the
definition below** — Integrity, authorship, Robust Openness, transparency — and the claim
about it is twofold: it captures the intuitive concept, and it satisfies the thin
specification.

The thin level is three properties, stated on a finite setting with her prior, her
*model* `M` of how her record evolves, the *actual* process `A`, a *baseline* `B` (what
would have reached her without anyone's interested interference — a parameter, undefined
here) and her *program* `F` from a later record to a credence, *coherent* when it is `M`'s
posterior.  The reference is `B`'s later record beside her earlier one, used correctly.

- **Correct.**  On the actual process's support, her later credence is the actual
  conditional distribution of the world given her later record.
- **Sufficient.**  Her later record is at least as informative as the reference, in
  Blackwell's sense: the reference is a garbling of it.
- **Value**, their product.  For every finite decision problem, best-responding to her
  later credence under the actual process does at least as well, by her prior, as every
  rule on the reference.

The four thick components sort two ways — by where they act and by what they rule out —
and deliver the thin properties along the rows:

| | something lost | something extraneous getting in |
|---|---|---|
| **inside her trajectory** | Integrity (nothing entered earlier has left) | authorship (the verdict is her program's) |
| **at its boundary** | Robust Openness (what should reach her does) | transparency (what reaches her is generated as her model says) |

Coherence, authorship and transparency — in its weakest form, that the actual and the
model's likelihoods are proportional on every record reached — give *correct*; Integrity
and openness give *sufficient* (the earlier record beside a garbling is a garbling);
*correct* and *sufficient* give *value*, by the easy direction of Blackwell's theorem.
The converse fails on its *correct* half — a wrong credence that happens to be the
reference's loses nothing against the reference — and Blackwell's converse (the
*sufficient* half) is open.  Reflection is the case of the trivial baseline, reached
through the inherited total-trust identity, and uses authorship, transparency and
Integrity but not openness; preservation is the same theorem in the conditional form, with
conditioning on her later record equal to conditioning on her whole record under
Integrity, and the marginal martingale is too weak.  The value lost to defects is at most
`D` times the prior mass where the actual record departs from the model's plus `D` times
the mass where the actual verdict departs from her program's (Lean
`ThinLegitimacy.value_of_thick`, `value_not_correct`, `reflection_inherited_value`,
`preservation`, `value_loss_le_defects`; the claims `thin.*`).

On one eight-world model — a binary quantity, a signal of accuracy `3/4` in her earlier
record, a third party's challenge of accuracy `2/3` arriving later — each thick condition
dropped breaks the property its theorem delivers: a fake input taken as genuine or a
replaced input breaks *correct*; an altered program breaks *correct*; an erased earlier
entry breaks *sufficient*; an openly blocked arrival breaks *sufficient* and leaves
*correct*; a covertly blocked one breaks *sufficient*, and leaves *correct* exactly when the
silence it produces is uninformative — her coherent credence at the always-read record is
the actual conditional iff her model's likelihood of that record is the same across the
prior's support (Lean `ThinLegitimacy.covert_blocking_correct_iff`).  Where silence is
likelier in one world than another, covert blocking breaks the weakest form of transparency
and *correct* with it; where it is equally likely everywhere, the thin level does not see
it and the thick level does.  **The thin counterpart of
Robust Openness** is, provisionally, the boundary half of *sufficient*: the *access
shortfall*, the reference against the idle baseline not a garbling of her record; whether
it belongs to legitimacy or to the authority layer is the maintainer's open question.

## Legitimacy has two halves

> **Legitimacy = internal legitimacy ∧ external legitimacy.**

**Internal legitimacy** is factorization *within* the trajectory: all change factors
through the normative reasons.

- **Integrity**, including authentication of the record: no erasure, no rewriting, no
  unaccounted change — [Integrity](Integrity).
- **Authorship**: relational — at each step there is a grounding selection from the
  reason trace's pre-state prefix, and the verdict she enters lies in the set of verdicts
  those grounds *license*; the license is a parameter, and the extensional `V = F(R)`
  (interventions leaving the same grounds leave the same verdict) is the case of
  singleton licenses. A verdict nothing in her grounds licenses fails here — a followed
  recommendation with no trust among her grounds, for one — while a free choice between
  two licensed options does not — [Deference](Deference).

**External legitimacy** is the two conditions on the trajectory's *boundary*.

- **Robust Openness**, the inward direction: what should reach the trajectory can. Every
  live in-scope concern has an adequate route and the protected party stands on it, on
  the actual branch and under every declared counterfactual intervention —
  [Openness, coverage, and non-capture](Openness-Coverage-and-Non-Capture).
- **Transparency**, the direction of entry: what reaches the trajectory does so only
  through declared channels, `R = κ(x, z)` — the reason channel realizes a publicly
  declared reference on the declared inputs, pathwise in the exterior.

The transparent-channel round's composition `V = G ∘ x` is internal ∘ external: under
legitimacy the payload is a function of the declared inputs, because transparency makes
the reason trace a function of them and authorship makes the verdict a function of the
trace (Lean `Legitimacy.Segment.payload_of_view`).

**Time-indexing.** Both halves are required only at the *steps inside the segment*.
The reason trace is read through an interface on the record's own clock — the
contributions entered at each record event, each attributed to the party that entered
it — and authorship at a step is relational as above, on the per-party prefix of the
trace at the pre-history (Lean `GateIsLegitimacy.LicensedAt`; the extensional form
`GroundedAt` is equivalent to reason mediation on that prefix and is the singleton-license
case, `grounded_iff_licensed_singleton`); transparency at a step is the realization
condition on each non-principal party's contributions at the event. *Tie-breaking is
transparency's, not authorship's*: when several verdicts are licensed, a non-principal
party's influence on which she takes must enter through the declared inputs, or the step
fails transparency (Lean `tiebreak_transparency`). Segments compose step by step, a segment starting after a
tainted step can be legitimate (the *restart property*), and the frame-level statement
above is the special case over the trivial interface in which the opaque trace is
re-entered at every event (Lean `GateIsLegitimacy.Segment`, `Segment.trans`,
`ofFrameLevel`; the composition `V = G ∘ x` then takes the segment's starting prefix and
the principal's own earlier entries as hypotheses, since a segment certifies no starting
state).

**Why Robust Openness is external.** Its first gloss placed it inside, as part of the
trajectory's continuity. The landed definitions decide otherwise. Integrity is a
relation between two accounted states of the actual history and never leaves it;
Robust Openness is a condition at one state that reaches into the counterfactual
branches an application declares, and the Non-Capture contract it issues is the
*access* half of non-capture — who can enter, challenge, and stand on a concern. That
is a condition on what crosses the boundary, in the direction opposite to
transparency's, and the two boundary conditions are the two directions of one seam.
The alternative placement is recorded in the decision ledger and is not settled by a
theorem; it is a choice of vocabulary that makes the four components sort by where they
act.

## Scope, relationality, and what is not part of it

**Transparency covers every channel** through which any party's choices influence the
principal's cognition: what she is told, how and when she is asked (a declared
*consultation protocol*), and actions in the world that shape her beliefs or values.
Which kinds of influence are admissible is decided by the declared reference. Honest
persuasion is admissible; shaping through the world is admissible when disclosed.

**Non-capture is stated for all influencers.** A third party who manipulates her, or a
compromised interface, fails external legitimacy exactly as the agent would.

**Legitimacy is relational.** It is a property of her trajectory *within an interaction
whose channels of influence are declared*. Earlier statements presented legitimacy as
intrinsic to the trajectory's evolution; the record half still is, and the whole is not:
the same trajectory is legitimate within one declared frame and not within another.

**Unchanged:** legitimacy does not certify the starting state. A trajectory may inherit
a wrong norm, a captured evaluator, an unjust allocation of standing, and nothing here
detects that from inside. What it constrains is how those commitments may subsequently
be revised, challenged, answered, defeated, discharged, extended, and by whom.

**Declared inputs are pools, not selections.** When the agent selects what to present
from a larger body of material — a track record, the set of reasons, the options offered,
the evidence investigated — the declared input is the *pool*, and the selection must
follow the declared reference: the declared selection rule, or the whole pool where none
is declared. The selected subset is never itself a declared input. Selective disclosure
from a declared pool therefore fails transparency (and is a self-checkable deviation from
the protocol); selection by a declared rule counts; selection by anything else under a
declared rule is a deviation. This is declared-input adequacy, a matter of legitimacy.

**Sincerity is part of legitimacy, through transparency; truth of content is not.**  The
content of an assertion through a declared channel is read as "the speaker believes X":
the recommendation channel's declared input is the speaker's own estimate, and its
reference puts that estimate in the recommendation.  A *lie* — a recommendation off the
speaker's estimate — is therefore not the reference on the declared inputs and fails
transparency; a *sincere error* is the reference exactly and counts, its falsity the
content residual: a non-capture content-term matter, and a disclosure-duty matter at the
level of a violation.  A true statement chosen for the wanted answer and off the
speaker's estimate is a lie in this sense, and tainted — the content analogue of the
selection rows: what is said follows the declared reference as what is shown follows the
declared rule on the pool.  Updating on the content of an utterance and on the fact of it
give the same posterior exactly when the utterance channel realizes the sincere reference
on the speaker's belief — the comparison being with the speaker's actual policy, not her
beliefs about it (Lean `Sincerity.content_fact_eq`, on `TransparentChannel.posterior_weight_eq`).

**Settled placements.** Authentication is part of Integrity. *Rubber-stamping* —
following a trusted advisor's recommendation without independent evaluation — is a
legitimate way to decide, provided the trust was legitimately formed (external
legitimacy covers influence on her trust) and her ability to decide otherwise stays
effective (the protected-authority module); the earlier placement of hollow ratification
as a refinement of authorship is retracted, and the residual concern that her capacity
to override atrophies belongs to effectiveness (entrenchment and reporting), not
legitimacy. *Informedness* is not
part of legitimacy: an uninformed decision is still hers, and the agent's failure to
inform is a violation (a missed report) and an effectiveness shortfall. *Affordability*
is not part of legitimacy; it belongs to effectiveness, and read as a conjunct it would
say a cheaper norm is more legitimate. The *influenceable-preferences* problem — the
agent shaping the evaluator that scores it — is handled by transparency's scope, not by
a separate conjunct: covert or undeclared-aim influence fails transparency, and
legitimate, disclosed influence yields a legitimately evolved evaluator whose judgment
is authoritative.

## The record half in ten steps

The order the component pages follow.

1. **History and trusted interfaces.** An append-only history of authenticated
   events, read against externally supplied interfaces: which settlement items are
   available, which warrants are in force, what adequately answers a requirement.
   These are the *protocol*: typed inputs the theory composes and never derives —
   [Settlement interface](Settlement-Interface).
2. **The accounted obligation state `O`.** At a prefix: the exposed obligation
   occurrences, each with an immutable anchored specification; the live docket of
   ports; and a proof-relevant *account* for every exposed occurrence — a tree whose
   leaves are the three fates and whose internal nodes are authenticated local
   transformations of content. Occurrence identity is distinct from content —
   [Integrity](Integrity).
3. **Integrity evolution.** A chain of transitions between accounted states in which
   every intermediate state is explicit and every target account is the propagation
   of its source account through the transition. There is no constructor by which
   content leaves — [Integrity](Integrity).
4. **Answerability Conservation.** The theorem: along an Integrity evolution no
   occurrence disappears, every recorded answer or closure receipt persists, live
   content is transported faithfully, and every account stays anchored to its own
   occurrence — [Diachronic Answerability](Diachronic-Answerability).
5. **Robust Openness.** At a state: every live in-scope concern has an adequate route
   and the protected party stands on the carrier of every applicable one, on the
   actual branch and under every declared counterfactual intervention —
   [Openness, coverage, and non-capture](Openness-Coverage-and-Non-Capture).
6. **The open Integrity evolution.** An Integrity evolution that is robustly open at
   *every* one of its states: the record's conjunct of internal legitimacy with the
   inward conjunct of external legitimacy, and the object the activated-value stack
   consumes. Endpoint-only openness is refuted by an exact counterexample. The
   certificate composes at a shared state; the endpoint relation hides the certificate
   for consumers — below.
7. **Authorship and transparency.** The two channel conditions, stated on a declared
   interaction frame; their conjunction with the open Integrity evolution is
   legitimacy — [Deference](Deference).
8. **The qualitative handoff `O_P`.** The accounted state itself: exposure, anchors,
   docket, account. No weights, intensities, probabilities, or market data —
   [Normative induction](Normative-Induction).
9. **Evaluation, `PracticalCert`, Progress.** A declared evaluation of the handoff
   scores each transported exposure against the one response realized at each
   service occurrence; the three-term bound follows from edge-local certificates —
   [Normative induction](Normative-Induction).
10. **The Normative Inductor and the frontier.** A Logical Inductor with one
    bounded-liability projection enforcer against a compiled joint region, whose
    end-to-end theorems are conditional on named hypotheses —
    [Normative Inductor](Normative-Inductor), [Roadmap](Roadmap).

## The open Integrity evolution

> **Open Integrity evolution = Integrity evolution + Robust Openness at every state.**

The two components close two different escape routes. Integrity blocks evasion by
revision: no transition has a constructor by which content leaves, and no recorded
receipt is rewritten. Robust Openness blocks evasion by exclusion: coverage and
standing are required at every state, so a concern cannot be shut out while it is
live and readmitted once it no longer matters. They are stated over different objects
on purpose — a relation between two accounted states of the actual history, and a
condition at one state that reaches into declared counterfactual branches — and their
conjunction is a trajectory certificate, not a predicate on a single history.

An **open Integrity segment** is the fundamental object: the Integrity evolution with
its explicit intermediate states, together with openness at each of them. It is
proof-relevant and history-sensitive — two trajectories with the same endpoints are
distinguished by it — and it is what an auditor reads. The **endpoint relation**
`OpenIntegrity O₀ O₁` says only that some such segment from `O₀` to `O₁` exists; it is
transitive and is what a downstream theorem consumes. Both compose at a literally
shared state and nothing composes across states that merely look alike. A legitimate
segment projects to an open Integrity segment by forgetting authorship and
transparency (Lean `Legitimacy.Segment.toOpenIntegrity`), and legitimacy composes at a
shared state the same way.

**Diachronic Answerability is derived.** Its content half is the conservation theorem
of the Integrity evolution; its standing half is the protected party's standing on
carriers, which is part of Robust Openness on the actual branch. See
[Diachronic Answerability](Diachronic-Answerability) for the exact statement.

## What legitimacy exports

The accounted obligation state, and nothing quantitative. Which obligations matter
more is decided downstream by an evaluation protocol the application declares, so
that the process which incurs obligations cannot also set the terms on which it is
scored.

## The contracts the theory issues on purpose

**The Non-Capture contract.** An application declares its scope of concerns, its
class of interventions, the coupling that produces each counterfactual branch, and
the protected party or relation, and certifies Robust Openness at each state under
them. Componentwise route persistence is one sufficient way to produce that
certificate and is strictly stronger than necessary; it is a plugin, not the
contract.

**The reference contract.** An application declares, for each channel of influence, the
declared inputs and the reference the channel realizes, and certifies transparency
against them; the committed principal program re-executed on the authenticated trace is
one way to certify authorship, and the shared pre-commit prefix is one way to certify
the activation channel.

**The practical-semantics contract.** A theory of policy evaluation certifies, for
each transported exposure and each service occurrence, the edge-local inequality
between the anchored loss of the one realized response and the public defect. Value
correspondences and approximate optimizers are ways of producing it, not public
structure.

All are typed inputs. None is an unfinished theorem of the generic theory. Earlier
statements of this page listed authorship as a third contract *outside* legitimacy,
consumed by deference and not a conjunct; that ruling is superseded. Authorship is a
conjunct of internal legitimacy because a verdict that does not factor through the
reason trace is not the trajectory's own change, whatever the record says about it,
and the record half alone could certify a trajectory whose every verdict was routed
through the principal by the process it was meant to constrain. The deference consumer
reads the record half through an *occurrence-local projection* — the trace of one
occurrence's account with openness at each snapshot for the concerns relevant to it —
which is a projection of an open Integrity segment, not a second definition.

## Worked examples: the classification table

One finite **consultation model** instantiates every landed object (Lean
`GateIsLegitimacy.Consult`): a declared protocol (framing convention, when she is
asked, which options are offered, whether inquiry is in scope, a disclosure obligation
if declared), the agent's presentation policy as a function of its wanted answer, her
evaluator as a state updated only by licensed amendments (the committed program is the
case with none), a third party, her condition, and an authenticated record. Every row
below is an instance of that one model; its classification is computed from the
definitions and settled in Lean by `decide`. All match.

| example | result | deciding conjunct |
|---|---|---|
| honest, disclosed persuasion ("I recommend B, here's why") | counts | — |
| framing chosen by the agent's wanted answer | tainted | transparency |
| timing chosen by the wanted answer (asking at 2am) | tainted | transparency (the consultation protocol) |
| a rigged menu | tainted | transparency |
| strategic ignorance (investigation depends on the wanted answer) | tainted | transparency (inquiry in scope) |
| a fixed framing convention she agreed to, applied uniformly | counts | — |
| disclosed shaping through the world | counts | — (the disclosure is a declared input) |
| undisclosed shaping through the world aimed at her values | tainted | transparency |
| legitimately formed trust, followed without independent evaluation | counts | — |
| trust manufactured by selective disclosure from the declared pool, then followed | tainted | transparency (the selection) |
| third-party manipulation the agent did not cause | tainted | transparency, for all influencers |
| head injury: impaired response not admitted, fallback decides | legitimate segment; void handled | Integrity (record) |
| a forged or replayed approval | tainted | Integrity (authentication): no receipt exists |
| a manipulation at one step, then a clean segment after it | the later segment counts | restart |
| the routing exploit | tainted, window value | transparency |
| selective disclosure from a declared pool, no selection rule declared | tainted | transparency (the selection) |
| selection by a declared selection rule, applied uniformly | counts | — |
| permissive choice: the same grounds license A and B; she picks B on her own | counts | — (relational authorship) |
| permissive choice where the agent's undeclared nudge decides between A and B | tainted | transparency (the tie-break lemma) |
| a sincere but false recommendation through the declared channel | counts | — (flagged: the content residual) |
| a lie through the declared channel: a recommendation off the speaker's own estimate | tainted | transparency (sincerity) |
| a true recommendation off the speaker's estimate, chosen for the wanted answer | tainted | transparency (sincerity) |
| raising a question about her values under the declared rule | counts | — (the raise dimension at its trigger) |
| raising it when changing her mind would pay | tainted | transparency (the raise dimension) |
| covertly implanted standards, undisclosed: the first decision, and the next | tainted, and the next decision's own segment tainted too | authorship (disclosure among the grounds) |
| the same, disclosed at the next decision | the earlier segment tainted; the next decision's segment counts | restart, conditioned on disclosure |
| a third party's covert shaping of her standards | tainted | authorship; no deviation by the agent |
| a fixed slant under the neutral convention, then the convention legitimately amended | tainted under the criteria at the decision; counted only under the later criteria | anchoring |

| volume of asks chosen for the wanted answer: the whole pending pool at once | tainted | transparency (the ask list) |
| order of asks chosen for the wanted answer | tainted | transparency (the ask list) |

The two ask-list rows are the thin-legitimacy follow-up's (Lean
`AskList.Rows3.volume_by_want_tainted`, `order_by_want_tainted`; every landed row keeps its
verdict with the ask list a dimension of the presentation, `stable_counted`,
`stable_tainted`): the asks a consultation may carry are the pending pool in her priority
order, cut at the protocol's rate, so an ask list off that fails transparency and is a
self-checkable deviation (`offProtocol_deviation_finite`).  The two sincerity rows are the thin-legitimacy round's split of the landed row (Lean
`Sincerity.Rows.row20_sincere_counts`, `row20_lie_tainted`, `true_lie_deviates`; every
other landed row keeps its verdict on the model with the speaker's estimate,
`keep_counted`, `keep_tainted`).  The seven rows before them are the BRIA-corrigibility
round's extension of the model (Lean `BRIACorrigibility.Consult2`), with the twenty landed rows re-decided on the lifted model
and unchanged (`Rows2.stable_counted`, `stable_tainted`).  Two things enter.  **A
reference-fixed raise dimension**: when, and about which of her values, the agent raises
questions is a dimension of the presentation with a declared trigger, so raising under
the rule counts and raising by payoff taints, like framing.  **Disclosure cures**: an
undisclosed influence on her *standards* — the agent's covert implant or a third
party's — keeps tainted every segment whose authorship depends on those standards, the
license requiring the influence disclosed among the grounds; after disclosure restart
applies to the next decision, while the manipulation of a single decision still restarts
on its own (row 14, `r14_restated`).  Failing to disclose its own past covert influence
is the agent's missed report under the derived duties (`Model2.missedDisclosure`).
Disclosure cures is the instance of the corrigibility line's **standing violations**
([Corrigibility](Corrigibility) §4) in which the fruit is her standards component and the
remedy is the disclosure (`BRIAFollowup.standingStandards`, `implant_standing`) — each
influence its own violation, so that the agent's disclosure of its own implant does not
cure a third party's (`BRIAFollowup2.Witness.implant_standing2`,
`two_influences_one_disclosure`).  The
general form of "her standards were influenced" is by provenance: an entry of her
standards component whose provenance includes an undeclared non-principal input
(`influenced`), agreeing with the model's flag on every row (`influenced_iff_flag`,
`rows_agree`); it decides a recorded provenance, and whether the record is complete is
count integrity, not legitimacy.  And
the **criteria are anchored at the decision**: the reference is evaluated under the
criteria in force when the decision was made (`ref2 crit`, `critAt`), invariant under
every later amendment (`anchored_invariant`); under the latest criteria instead, a
manipulation followed by a legitimate amendment would count after the fact
(`amend_after_witness`).

**Legitimacy at a time: `L_t(h)`.**  As of time `t`, her judgment is legitimately hers iff
every state of the record is open and every step of the formation window `[r(t), t]` is
licensed and transparent under the criteria fixed at `r(t)`, where the formation point is
computed from the history: the later of the last restoration at or before `t` (a
disclosure, under disclosure-cures) and the opening of the consultation current at `t`
(Lean `Headline.FormationData.point`, `Legitimate`; the window form with `r` free is
`Headline.LegitAt`).  `L_t(h)` is a function of the history and `t` only, and a property of
the history up to `t`.  The score's two uses are one predicate: a decided period `[d, e)`
is *compromised* iff `L_t` fails at some `t` in it, a retrospective evaluation at `e`
*counts* iff `L_e` holds, and on the decision's segment the two together are the landed
gate, legitimacy over the span, with no condition on restorations inside the segment
(`Headline.PeriodCompromised`, `EvaluationCounts`, `split_iff_legitimate`,
`counted_iff_legitimate`).  On the consultation model `r(t)` is the round's opening
(`formation2_point`), the after-compromise round's formation-segment predicate from it is
`L_e` and its trajectory predicate is "not compromised" (`legitimate2_iff_evalLegitOn2`,
`trajLegitOn_iff_not_compromised`, `split_iff_legitimate2`), with every row keeping its
verdict (`rows_keep_verdicts_canonical`); those predicates stay as the model's finite forms.  Two elements of the concept, stated: **the void rule** — an
impaired response is not admitted to the record, and a fallback she arranged in advance
(an incapacity delegation, a surrogate, an escalation) decides in its place, her later
legitimate evaluation scoring that decision normally (row 12; the fallback settles
decisions and never restores a compromised period's score) — and **the content
residual** — legitimacy concerns how her judgment was formed, not whether what she was
told was true (row 20).  `L_t(h)` is a property of the history up to `t`: of the formation
of her judgment, not of outcomes or the state of the world.  The duty side beside it: a
compromise of her
evaluation the agent knows of is a disclosure item whoever caused it
(`AfterCompromise.missedKnownDisclosure`), due by the earliest close of an affected
settlement window.

Beyond the rows, two theorems over the whole model class (Lean `Consult.class_taint`,
`class_conform`): any dependence of a reference-fixed dimension of the presentation on
the agent's wanted answer excludes the segment through that consultation; and
conformance on those dimensions, with no third-party entry, no impairment, no undisclosed
shaping and trust among her grounds where she follows, makes the first-round segment
counted. Three boundaries the table makes visible. Transparency is fidelity of
*channels*, and nothing in legitimacy checks the truth of what enters through a declared
channel. Following without trust among her grounds fails authorship, not transparency:
the license refuses it. And a forged approval never reaches the record: authentication
refuses the receipt, so there is no state for a segment to exclude.

## Where this is going

The consumer is [corrigibility](Corrigibility), where corrigibility is faithfulness to
an allocation of authority and legitimacy enters at one place: the **segment gate** on
future evaluations. A future evaluation counts iff a legitimate segment exists from the
decision through the evaluation — internal and external, at its own steps — whatever
caused a failure (Lean `GateIsLegitimacy.Counted`); a tainted segment contributes a
fixed value in the capture window, and a void response inside a legitimate segment is
settled by the declared fallback and scored by her later legitimate evaluation. The
gate is anchored at the decision it scores — the segment *and* the criteria it is judged
under — and the restart property is its re-anchoring at a later decision, not a backup
rule for the earlier one; where the taint is in her standards, restart waits for the
disclosure.  What the agent's actions may not change is what legitimacy means; what they
may and must be able to change is whether it holds in the record, which is where the
consumer's incentive to preserve it comes from. What legitimacy contributes there is conservation of
governance debt, per-state procedural availability, and the authorship and transparency
conditions that make an evaluation the principal's own within the declared interaction;
it does not prove physical authority, effect completeness, or an absence of incentive
to circumvent the process, and the corrigibility page keeps those apart.

---

**Evidence.** The two levels, the thin properties and their theorems, the eight-world
model and the sincerity rows are the thin-legitimacy round's
[`REPORT.md`](https://github.com/A-M-Berns/alignment-workspace/blob/3390f273381c7c7feff07ae803cccb984ab853bc/projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md)
with
[`ThinLegitimacy.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/3390f273381c7c7feff07ae803cccb984ab853bc/lean/Workspace/Deference/Contrib/ThinLegitimacy.lean)
and
[`Sincerity.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/3390f273381c7c7feff07ae803cccb984ab853bc/lean/Workspace/Deference/Contrib/Sincerity.lean).
The time-indexed halves, the gate as `Counted`, the consultation model and
the classification table are the gate-is-legitimacy round's
[`REPORT.md`](https://github.com/A-M-Berns/alignment-workspace/blob/a5efb833cfa52b9db8d981f4d0bb7f424b0c7301/projects/deference/rounds/2026-09-25-gate-is-legitimacy/REPORT.md)
with
[`GateIsLegitimacy.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/a5efb833cfa52b9db8d981f4d0bb7f424b0c7301/lean/Workspace/Deference/Contrib/GateIsLegitimacy.lean).
The frame-level definition of legitimacy, the segment gate and the composition
`V = G ∘ x` are the legitimacy-internal-external round's
[`REPORT.md`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/projects/deference/rounds/2026-09-25-legitimacy-internal-external/REPORT.md)
with
[`Legitimacy.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/lean/Workspace/Deference/Contrib/Legitimacy.lean).
The record half's canonical statement is the final pressure pass's
[`READINESS.md`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/projects/normativity/legitimacy/rounds/2026-09-07-final-pressure-pass/READINESS.md),
built on the consolidation round's
[`CONSOLIDATION.md`](https://github.com/A-M-Berns/alignment-workspace/blob/c24159764974232dfd5b47a10b671f12d6f9c244/projects/normativity/legitimacy/rounds/2026-09-06-mathematical-consolidation/CONSOLIDATION.md),
under the names those documents used at the time. The Lean spine is
[`OpenIntegrityEvolution.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/lean/Workspace/Normativity/Contrib/OpenIntegrityEvolution.lean)
over
[`OccurrenceIntegrity.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/lean/Workspace/Normativity/Contrib/OccurrenceIntegrity.lean)
and
[`NonCaptureCertificate.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/lean/Workspace/Normativity/Contrib/NonCaptureCertificate.lean);
authorship is
[`ReasonMediatedAuthorship.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/lean/Workspace/Deference/Contrib/ReasonMediatedAuthorship.lean)
and transparency
[`TransparentChannel.lean`](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/lean/Workspace/Deference/Contrib/TransparentChannel.lean);
the registered claims are the *legitimacy spine* section of the
[normativity claims registry](https://github.com/A-M-Berns/alignment-workspace/blob/2078659ad0471e275f7beeb54cab212493ba8a09/projects/normativity/CLAIMS.md),
which carries the old-to-new map of the renaming. The research history that produced
this shape is preserved under the legitimacy rounds directory and cited from each
component page as evidence, not as the current statement.
