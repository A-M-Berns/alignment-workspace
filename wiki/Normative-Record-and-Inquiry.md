# Normative Record and Inquiry

Normative learning needs a left side. Before a learner can answer a demand,
something must determine why the demand arose, how evidence enters the practice,
what authorizes a normative response, and what keeps an unanswered question from
vanishing. The working architecture is afoundational: it permits one primitive
induction into a normative practice and then requires every later exercise of
normative authority to remain genealogically answerable to that practice.

```text
one-time initialization
  afoundational seed S₀ ──pre-licensed induction──▶ normative record R₀

recurrent learning loop
  (Rₙ, Lₙ) ──inquiry──▶ world ──receipts──▶ Lₙ₊₁
      └────────────────reasoned uptake────────────▶ Rₙ₊₁

normative realization
  Rₙ ──authorization──▶ Oₙ ──credal interpretation──▶ Cₙ
     ──price realization──▶ Kₙ ──traderization──▶ Eₙ
```

The left side develops the practice and its questions. The right side gives
some current demands operative form. An enforcement mechanism cannot legitimate
its input, and an impeccable record does not compile itself into a credal
constraint.

> **Status: open / unregistered research.** A finite prosecution supports a
> repaired interface and counterexamples. No new claim is registered or
> Lean-checked. “Proved” below means a conditional paper derivation in that
> round, not Established workspace state.

## An afoundational start

The seed `S₀` is a small induction into a practice: enough initial authority to
begin making and assessing normative moves. It is pre-licensed because there is
no earlier state inside the model from which its license could come. This is the
model's one explicit expenditure of primitive normativity.

The seed is not a set of eternal truths. Its contents can be criticized,
reinterpreted, revised, or retired through the practice it begins. The intended
invariant is not that `S₀` entails every later norm. It is:

```text
every later exercise of normative authority has an accountable ancestry
through earlier authority-bearing acts, ending at an occurrence in S₀.
```

Later empirical experience may supply nearly all the grounds for a current
judgment. Seed ancestry says why the judgment belongs to this continuing
practice; it does not say the seed substantively entails or justifies it.

`S₀` is an initialization interface, not an explanation of normative
bootstrapping. A future theory might instead factor the start as
`I₀ --Uptake--> R₀`, where `I₀` is an ordinary empirical, social, or practical
induction history and `Uptake` spends only a minimal primitive participation
license. The present architecture does not determine whether this factorization
works or what normative structure the uptake operation must contain.

The fixed checker sits at an important boundary. Ideally it enforces only the
grammar of pre-state authority, version binding, scope, and accountable
disposition. Any substantive norm hardcoded into that checker is another
primitive normative expenditure, even if it is not drawn as a root.

## A thin world and two records

The interactive world supplies actions, utterances, measurements, testimony,
query responses, and consequences. It does not label them “really due” or
“truly authoritative.” Those labels would install an external normative oracle
inside the positive model.

`Lₙ` is the permanent empirical and logical transcript. It records what was
received or done and when. An interpretation of an observation—what it
indicates, whether it defeats a warrant, what it calls for—is a revisable
judgment in `Rₙ`.

`Rₙ` is the append-only history of normative acts: commitments, rules,
undertaken reasons, due tokens, accounts, and reviews. The current standing
state is a derived view:

```text
Vₙ = View(Rₙ, Lₙ).
```

The closest analogy is a self-amending court with an immutable transcript.

- `S₀` is its initial charter and induction, not a declaration of moral truth.
- `L` is the court reporter's permanent interaction transcript.
- `R` contains changing rules, cases, commitments, reasons, and accounts.
- `May` rules state what normative acts the court is empowered to make.
- `Must` rules state what cases or tasks it incurs when triggers occur.
- A due token records that a case was incurred while a rule stood.
- Amendment changes future operation; an incurred case needs a recorded account.
- Service leaves evidence under the specification governing the case.

## The proof-relevant narrow waist

Many normative objects can share one identity-bearing account form:

```text
Commitment
  Hold(judgment)
  Do(task)
```

Interpretations, rule activation, warrant applicability, standing, and
authorization can be `Hold` contents. Consideration, investigation, review,
response, and substantive performance can be `Do` contents. Once an inquiry is
docketed as `Do(investigate …)`, the existing answerability machinery supplies
stable identity, split and merge, delegation, suspension, explicit release,
basis-loss review, successor obligations, and typed terminal dispositions.

This is only a partial unification under the tested representation. There, a
**due token** is the historical receipt that a standing rule fired. A
**coverage debt** records that the token has not yet become an identity-bearing
commitment or received an explicit terminal account.
Equal content does not identify occurrences. Two identical investigations may
share evidence or one physical action, but both old identities require their own
adequacy and account edges.

The finite implementation therefore uses an event family larger than
`Root`/`Undertake`/`Account`:

```text
Observe(receipt, time)                         in L

Seed(commitment, induction receipt)            in R
Undertake(act, grounds, license, account, certificate)
Accrue(due token, rule version, receipt, service specification)
Account(inputs, disposition, successors, certificate)
BasisLost(historical use, epoch, review occurrence)
```

That operational distinction is not a representation-theoretic minimality
result. The current three constructors do not expose all information used by
the checker, but the round does not prove that accrual, review, or due tokens
cannot be compiled faithfully into a differently typed smaller calculus.

## The reason state beneath the record

This page's `R` is the record: the append-only history of normative acts. A
research round now prosecutes a separate object beneath it — the practice's
*current reason structure*, provisionally the **reason state**. Its candidate
form: particular reason applications are identity-bearing hyperedges whose
sources cite both revisable claims and transcript receipts; schema membership
and staged applicability are themselves ordinary contents (`Inst(e,σ)`,
`App(σ,c@n)`), so undercutting a reason is an ordinary reason against its
applicability, and reorganizing schemas is reason-guided revision rather than
external clustering. The substrate stores no belief statuses and runs no
update rule: it answers which reasons are enabled under a candidate stance and
what depends on what, while adjudication — what to retain, adopt, suspend, or
investigate when live reasons conflict — belongs to the normative learner.
Two demands survived prosecution: contents need a constitutive contradiction
floor, and applicability must be staged, with persistence across stages earned
by defeasible schemas rather than granted by the substrate.

The dispatch proposes writing the reason state `𝓡_n` against the record
`N_{≤n}`; this page keeps `R` for the record until the naming is ruled on.
Evidence: [the reason-representation round](https://github.com/A-M-Berns/alignment-workspace/tree/11b4d47f4e97130b78f644964652e6db4169f42c/projects/normativity/legitimacy/rounds/2026-08-23-reason-representation).

A successor round derives the boundary above the substrate: a normative
transition carries a certificate citing its grounds — particular reason
occurrences — its license — a prior, scoped authority act — and its lineage —
the commitments it answers — as separate sorts, all checked strictly against
the pre-state. Three principles carry the discipline: strict pre-state
citation, constitutive immutability, and answerability continuation. Under
them, a transition cannot mint its own reasons or authority, its claimed
historical basis cannot be rewritten, and losing a relied-on basis is
detected at the frozen citation even when a substitute reason stands —
refusals that fall out of the principles rather than from dedicated
anti-laundering rules. What a valid certificate establishes is that the act
was licensed within the current accountable practice, not that the practice
is apt. Evidence:
[the transition-certificates round](https://github.com/A-M-Berns/alignment-workspace/tree/3f042ea60ce03a9c64dca5c6307bf77fcf613259/projects/normativity/legitimacy/rounds/2026-08-23-transition-certificates).

## Grounds, license, and account lineage

| Relation | What it answers | Typical inputs |
|---|---|---|
| grounds | Why this content? | empirical receipts and earlier judgments |
| normative license | What entitled this kind of move? | standing authority in the pre-state |
| account lineage | Which old commitment is being answered? | input-scoped occurrence identities |

Empirical receipts may ground a normative move. They do not create normative
authority by themselves. A measurement can explain why a practice revises a
rule; some already standing authority must license revision of that kind.

License edges point strictly backward. This blocks self-installing authority and
same-transition mutual licensing. In a finite accepted record, the decreasing
time index makes every maximal license path terminate at a seed. That “no new
roots” derivation concerns continuity of authority, not normative truth.

Account edges preserve another history: which inherited commitments were
performed, closed, suspended, split, merged, or transformed. Authorization is
not automatically adequate disposition; the pinned lifecycle version and
input-scoped evidence still matter.

## `May`, `Must`, and event-time accrual

`May` and `Must` are rule modes, not a complete logic. A `May` rule licenses a
typed normative act. A `Must` rule emits a typed due token when its finite
trigger fires. Every rule is itself a versioned `Hold` commitment whose
authority comes from the practice. This avoids defining coverage as closure
under every semantic implication of an open-ended theory.

A due token records the generating rule version, triggering receipt, accrual
time, required task, and service-specification version. Later repeal does not
rewrite it.

“When the trigger occurs” needs explicit ordering:

```text
append receipt → evaluate triggers under the fixed pre-state rule view
               → append due tokens and coverage debts
               → admit amendments → derive the next view
```

A receipt followed by repeal in one transaction therefore incurs the case;
repeal governs later receipts. A revision effective before the receipt changes
the rule view first. Delayed recognition normally accrues when the practice
receives evidence. A rule may reason about an earlier world-time field, but that
retroactive reach is itself substantive and versioned.

New evidence may show that the original interpretation was mistaken. The token
then receives review, cancellation, migration, or another typed account. It does
not disappear. Even an authorized retroactive amendment changes current
treatment through accountable dispositions rather than erasing the transcript.

## Coverage is three questions

**Docket coverage** asks whether every generated token becomes a commitment or
remains represented by a visible coverage debt. Atomic debt creation makes this
safety-like. A docketing deadline requires a processor bound; eventual docketing
requires fairness and serviceability.

**Service coverage** asks whether live inquiry liabilities are eventually
serviced or receive another authorized disposition. This is liveness. It cannot
be unconditional for a bounded reasoner: if two tasks arrive per step and only
one can be processed, backlog grows forever.

**Service certification** asks what justifies closure. Each liability pins a
versioned specification `σℓ`. Partial progress may be represented by
`fℓ(history) ∈ [0,1]`, but even `fℓ=1` does not silently close the liability. A
terminal account needs a certificate against the pinned `σℓ`. Revising `σℓ`
requires a licensed, lineage-linked migration.

Basis loss uses the existing review mechanism. A commitment validly undertaken
under an old basis remains historical. Recognized undercutting emits a `Review`
task concerning current consequences and descendants. A different proof can
make review easy to close; it does not alter the originally undertaken basis.

## Bounded scheduling is downstream

The normative record determines what inquiry is owed. A scheduler decides how a
bounded reasoner allocates actions across the docket. A finite snapshot may
include actions, pinned specifications, progress functions, delay or urgency,
context costs, and certified progress.

| Mathematical class | Exact fit | What is not inherited |
|---|---|---|
| Set Cover with Delay | Dynamic deterministic arrivals; an action serves all pending tokens in its fixed subset; action and accumulated-delay costs are preserved. | Finite terminal delay permits permanent nonservice. The model supplies no certification or normative adequacy. |
| Submodular ranking / MLSC | Fixed docket; one normalized monotone submodular progress function per liability; unit-cost ordering for ranking, or metric path for MLSC; sum of cover times is preserved. | Complementary investigations need not be submodular. Mutable dockets, stateful repetition, and nonmetric costs need another model. |
| Adaptive submodular coverage | Fixed item set and realization space, known prior, immutable objective, and adaptive monotonicity/submodularity. Coverage requires success for every realization consistent with observations. | It is a diminishing-returns tractability condition, not legitimacy. Conditional synergy and realization-changing actions fall outside it. |
| Interactive submodular set cover | Finite hypothesis class, known valid responses, adversarial response consistent with a fixed target, and pointwise-submodular objectives. | The class may be misspecified; the base model assumes noiseless consistency and fixed service semantics. |

The Set Cover with Delay bridge exposes a liveness trap. Divergent delay for one
ignored task plus a global competitive ratio does not guarantee service when
background optimum cost grows. A policy can pay background cost `T`, accrue
focal delay `T`, and remain two-competitive against a comparator costing `T+1`.
Eventual service follows with a stronger condition: the competitive inequality
plus a comparator whose total cost stays uniformly bounded, or an equivalent
marginal guarantee.

Golovin–Krause's self-certification motivates the proof-relevant boundary:
actual target achievement is not enough for stopping if observations do not
certify achievement across every still-consistent realization. This architecture
borrows that distinction without adopting a Bayesian prior or adaptive
submodularity as constitutive of legitimate inquiry.

Guillory–Bilmes is useful where worst-case compatible responses are preferable
to a prior. It still describes a scheduler class, not the authority by which a
service objective enters the record.

## External evaluation and counterfactual legitimacy

An external evaluator may state which demands deserved confrontation from a
meta-theoretic perspective. It remains useful for counterexamples and measuring
divergence. It is not the preferred positive model, where inherited `Must` rules
generate the docket. The evaluator and internal practice can disagree.

Actual-run legitimacy and counterfactual legitimacy remain separate:

```text
legitimacy ≈ process integrity on the actual run
           + counterfactual non-capture and corrective control
```

A process can follow every internal rule, docket every generated obligation,
and maintain flawless accounts while another agent strategically shapes how the
rules evolve. Genealogy makes that evolution inspectable; it does not show that
it was unmanipulated. Non-capture remains a hyperproperty over coupled runs.

## Hand-off to the normative compiler

The current view of `Rₙ` should tell an operative compiler which liabilities
stand, which are applicable, which are authorized to exert a kind of force, and
which have credal-bearing content. That is the input boundary to `R → O`.

The compiler remains open. Joint semantics must be formed before lossy credal
or price projection, and safety semantics alone does not guarantee a nonempty
closed convex credal set. Once a valid operative object and credal presentation
exist, the current `O → C → K → E` machinery handles interpretation, price
realization, and traderized force under its own feasibility and funding
hypotheses. It does not validate the record.

## Open questions

- Can the seed be factored into an ordinary induction history plus a minimal
  primitive uptake or participation license, and what normative structure must
  that uptake operation contain?
- Is there a semantics-preserving smaller event calculus for accrual, review,
  and due-token history, or an obstruction to one?
- Which checker clauses are grammar, and which spend substantive normativity?
- What finite trigger language avoids hidden logical omniscience?
- When should delayed evidence use current rules versus world-time rules?
- Which overload and fairness assumptions are appropriate for service coverage?
- How are service specifications compiled into evidence predicates?
- Which inquiry domains are submodular, and how should complementarity be scheduled?
- Can mutable objectives become auditable fixed scheduler instances with migration?
- Which current commitments compile through the open `R → O` interface?
- How should actual-run integrity compose with counterfactual non-capture?

## Evidence and sources

- [Afoundational inquiry round and status map](https://github.com/A-M-Berns/alignment-workspace/tree/226de9c690f7879cfb17ab07f13277773757de22/projects/normativity/legitimacy/rounds/2026-08-23-afoundational-inquiry)
- [Internal-answerability kernel](https://github.com/A-M-Berns/alignment-workspace/blob/e5de4b9c03730961154eec555153a59ec3e7462a/projects/normativity/legitimacy/rounds/2026-08-21-internal-answerability/MEMO.md)
- [Role-parametric answerability wrapper](https://github.com/A-M-Berns/alignment-workspace/blob/e5de4b9c03730961154eec555153a59ec3e7462a/projects/normativity/legitimacy/rounds/2026-08-22-role-parametric-answerability/MEMO.md)
- [Set Cover with Delay](https://doi.org/10.4230/LIPIcs.ESA.2020.8)
- [Adaptive Submodularity](https://arxiv.org/abs/1003.3967)
- [Minimum Latency Submodular Cover](https://doi.org/10.1145/2987751)
- [Interactive Submodular Set Cover](https://arxiv.org/abs/1002.3345)

The literature supplies scheduler definitions and guarantees only under the
hypotheses described above. Authority, record, and certification are this
program's proposed interfaces around those tools.
