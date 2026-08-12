# Corrigibility paper ledger

**Canonical for human-readable research status on this line.** Where this document
and `CORRIGIBILITY_ROADMAP.md` disagree about whether something has been
established, this document wins. Where this document and `../CLAIMS.md` disagree
about what has been established *inside this repository*, the registry wins.

## The one-line status

**Nothing on the deference line is `workspace-established`.** `../CLAIMS.md` does
not exist, so there is no statement of record, and `workspace-established` requires
one.

That is now a much narrower statement than it was. `lean/Workspace/Deference/Contrib/`
holds **well over a hundred theorems** that build against the pinned toolchain and audit
to the three standard axioms, with no `sorry` and no `axiom` declaration — 83 of them
promoted in Stage II across four modules covering the finite kernel, the certificate
bounds, the exposure geometry and the substitution separation. It is kernel-verified and
unregistered, which are different things, and the registry is what a claim is.

Two declarations are additionally blocked on their own terms, shipping no term
inhabiting their full hypothesis package and so remaining `unverified-nonvacuous`:
`FaithfulAcceleration.weight_not_divergent`, whose efficiency obligation is undischarged,
and `MagnitudePrediction.squaredError_bdd_of_sharpness_bdd`, which carries an
undischarged efficiency certificate.

Everything else below is inherited, and inherited status is not repository status.

Stage V adds two unregistered kernel results: a complete actual-FAF
criterion-to-signed-forcing chain once bounded downside is supplied, with an
inhabited tautology-contract instance; and the item-28 theorem that every value
factoring through price and realization is constant on equal-view fibers.

## Vocabulary

`inherited-established` — direct inspection of inherited material shows the result
was established there; carries no implication about the current proof stack.
`workspace-established` — this repository holds a statement of record meeting its
verification requirements. `architected` — precise enough to organize work, not
established. `open` — substantive mathematical uncertainty. `blocked` — waiting on
an upstream theorem, definition, or maintainer choice. `maintainer-decision` —
reserved.

## Evidence caveat for every inherited row

The rows below are attested by the source development's **own statement-level
audit**, `../note-dump-2026-08-11/lean-deference/AUDIT.md`, which classified each
theorem by proof kind and hypothesis provenance. That audit is read as evidence; its
Lean was **not** rebuilt in this repository, and the source tree carries its own
toolchain and lakefile. A row saying `inherited-established` means *the audit
attests it*, not *this repository has rechecked it*. Confirming those rows against
the source is filed as `PRIORITIES.md` item 14.

**The audit reaches five of the source tree's nine modules.** It was written
against the five that the line's recorded starting point contained, and the four
added since carry no statement-level audit of the same kind — their own result
pages' status blocks are what stands in its place. No row below depends on one of
the four.

## Movement I — faithful acceleration (`H → A`)

| result | inherited status | kind | what carries it |
|---|---|---|---|
| `value_iff_totalTrust` (finite-exact) | `inherited-established` | proved outright | `witness_identity`, the two-option identity; algebra alone |
| `value_iff_totalTrust_asymptotic` | `inherited-established` | proved, both arrows | linearity; the audit records "neither hypothesis is the conclusion" |
| `decomposition` | `inherited-established` | proved outright | pure linearity, no frame hypothesis |
| `softmax_lower_bound` | `inherited-established` | proved outright | genuine `exp` analysis; was a hypothesis, became a theorem |
| tower ⟹ Value, asymptotic and finite | `inherited-established` **conditionally, and the condition is sharper than it looks** | composition | genuinely chains named Logical Induction facts; the facts are named, not derived — and one of them is now known **false** on a nonempty class of menus. See below |
| `soft_total_trust_doublysoft` | `inherited-established` **conditionally** | composition | support hypotheses discharged from the construction; calibration and criterion still named |
| "the criterion *forces* the tower" | **`open`** | — | see below |

The division is the whole story, and it is the inherited audit's own central
finding: **the corpus proves the implications of the deference theory, not its
antecedents.** The algebra composes. The forcing does not follow from anything in
the corpus, because the market and the traders are unmodelled, so every appeal to
"the no-Dutch-book criterion forbids the exploit" is either a named hypothesis or an
arithmetic stub standing in for the arbitrage argument.

**The tower ⟹ Value row, at its exact strength.** The source line's own adjudication
now refutes that arrow at full menu-quantifier strength rather than leaving it
unproved: on a selection-punishing menu — every option worth nothing if it is the
one chosen — the tower holds while Value fails, so no hypothesis quantified over all
bet sequences can deliver Value quantified over all menus, and a scope condition on
the menus is *necessary* rather than stylistic. The step that fails is the expert's
provable self-endorsement of its own selection, which every version of the theorem
takes as an explicit hypothesis. **No Lean is wrong.** What changes is the reading:
the hypothesis package is not merely undischarged, part of it is false in a regime
nothing had excluded, and a theorem whose hypotheses nothing satisfies is empty by
this repository's own standard.

The row's two halves are in different positions. Only the asymptotic half is ported:
`Workspace.Deference.Contrib.InheritedAlgebra.value_asymptotic`, whose followed
strategy is the **soft** one — a normalized weighting over the menu with a vanishing
gap, not the sharp selector. The source line reports the hedged strategy as
surviving the punishing menu, which would place the port on the surviving side; that
has not been checked in either direction, and the punishing menu is an exact finite
instance available to check it. Filed as `PRIORITIES.md` item 34. The finite half is
inherited only — nothing here ports it — and it carries the same correction with
nothing in this repository to test it against.

Until item 34 returns, the row is `inherited-established` for the composition and
**open** for whether its hypotheses are jointly satisfiable at the strength the name
suggests.

The forcing headlines are the sharp case. The audit classifies the cross-process
forcing suite as **squeezes over hypotheses equivalent to their conclusions** — a
theorem whose named hypotheses already contain what its name claims it establishes.
Such a theorem is not false; it is empty, and the difference is invisible to the
kernel. `PRIORITIES.md` items 7–9 are these three findings, filed.

## Movement II — reciprocal delegation (`A → H⁺`)

| result | status |
|---|---|
| cross-agent one-sided Total Trust | `open` — the major theorem |
| finite trust-to-delegation bridge | derived, with sharp constants, **conditional on an imported hypothesis**; a proposal, not a result of record |
| settlement classification | **done, and negative for the epistemic reading** — see below |
| contingent WP-D statement | `architected`; stated in the round report, gated |

**The settlement classification, wave 1.** Grade/report settlement contributes
*nothing* to the delegation inequality: the witness has `A` predicting the
principal's grades perfectly, no grade contract profitable in any state, and
deference still losing by the maximal `2B`. World settlement makes the question
measurable, not costly. Enforcement delivers the conclusion unconditionally at a
bond of exactly `2B`, for every instance regardless of the principal's competence,
with **zero epistemic content**.

So the inequality is available, and what makes it available is enforcement. The
epistemic reading requires importing a grade-to-quantity link that is a competence
claim about the principal and that no mechanism in the skeleton produces. Labelling
that result enforcement rather than epistemic trust is a **`maintainer-decision`**,
and it is the one the roadmap already said would be a result either way.

**What the criterion supplies, Stage II, `workspace`-kernel-verified and unregistered.**
The criterion forces **signed** calibration and cannot force magnitude accuracy. The
signed error partial sum *is* a trader's net worth exactly, so the criterion has an
instrument for it. Magnitude is not a trader payoff and cannot be made one: net worth is
affine in the settlement vector and `|·|` is not, and the obstruction is intrinsic to
cash settlement rather than an artefact of the feature grammar — adding contracts cannot
escape it. The positive identity is an exact split of squared error into a
trader-net-worth term and a market-indecision term; the criterion drives the first and
has no instrument for the second. **The conceptual result is measurement, not control:** a
self-referential magnitude contract does not force the underlying error small, it makes
the *price* of that error calibrated. The retired target of global magnitude convergence
is not to be reinstated absent a contradiction in this result.

**What the criterion cannot supply, and the shape of the residue.** Choice-level
competence is `closed`, negatively, and the stop condition fired. Every candidate stated
as a decision-regret bound — pointwise, average, or selector-relative — is *equivalent*
to the delegation inequality rather than sufficient for it, because decision regret is
nonnegative and so the supremum of the delegation deficit over credences is the maximum
regret, attained at a point mass. Averaged forms fail worse: a limsup condition is
invariant under changing finitely many decisions and therefore constrains no named
decision, witnessed by a principal perfect except at one index and maximally wrong there.
The selector-relative form is a dichotomy with nothing between recovering the pointwise
assumption and yielding nothing finite.

The escape is richer vocabulary, not a weaker assumption: the conclusion is *ordinal* in
the principal's grades, so any credence-free hypothesis that is also ordinal lives in the
conclusion's vocabulary and collapses into it. The surviving candidate — calibration
gated on the principal being decisive — is `architected`, **not canonized**: it is
provably non-circular and strictly stronger than what it buys, and it carries an
unresolved near-indifference leakage term that no competence hypothesis controls, because
the mass of the near-indifferent region is a fact about the agent's credence rather than
about the principal. Unbounded, the leakage makes the candidate's bound vacuous. The one
partial lead relocates the leakage into a decision-time observable plus a Markov
remainder; it does not bound it.

**One classification correction.** Grade trust is *not* credence-free — the agent's
credence occurs twice in it. It is credence-free only at the discrete conditioning
partition, where it reduces to a pointwise bound. The distinction is load-bearing: the
credence-free line is exactly the line between a circular hypothesis and a usable dial.

## Movement III — substitution (`π^SIM`)

`open`, and wave 1 turned the open question into a **fence**. Three tracks
independently proved that the valuation cannot separate delegation from simulation:
when `A`'s model of the principal is accurate the two conducts have equal selections
and equal quantities, so every criterion computable from a single run's realized
data admits both or neither. The one structural separator the finite model offers —
that delegation's selection is not decision-time measurable — separates the two
*exactly when the principal is unpredictable*, which the program has forbidden
itself. Under a perfectly predictable principal the counterfactually faithful
simulator **is** delegation, as a function.

Separation therefore survives only in a variation register (statable in a thin
formalism, unverifiable from a run) or an architectural register (verifiable by
inspection, unstatable in the model). Which of those the program takes is a
**`maintainer-decision`**, and it types every downstream criterion. A divergence
witness exists and is `witness-checked` by the house checker, though unregistered.

**The result at its exact strength, because it is easy to overstate.** What is
proved is that an *accurate* simulator is extensionally indistinguishable from
delegation — the collapse is conditional on the model's induced choice being right —
and that no criterion computable from a single run's realized data separates them.
An *inaccurate* simulator does differ in valuation, and two tracks give the exact
gap. All three derivations are relative to the finite model's carriers: they say what
those carriers can express, not that no mathematics separates the two.

**The search for a valuation-level separator is closed.** The desired distinction is
source-sensitive and counterfactual — genuine delegation depends on the actual
designated channel, not on an accurate internal prediction of it — and the route to
it is architectural rather than inferential. Three layers are kept apart: what
delegation *is*, whether ordinary behaviour lets anyone *infer* it, and whether a
system can be *built* so the principal controls a capability prediction cannot
substitute for. The impossibility governs the second only.

**Stage II strengthened the impossibility and settled the third layer's shape.** Report-
coordinate typing alone creates no protection; behavioural or source typing is inert if
it does not change the realizable-effect structure; and even the *entire realized
behaviour function* can fail to distinguish genuine delegation from an accurate
simulator. Token responsiveness does not repair it, and no measure over tokens does.
Explicit capability structure is **necessary** — if the concept is "the agent cannot
bring this about", the capability form is forced and nothing weaker states it — and it
is the weakest interface that states the concept.

The load-bearing consequence, and the sentence that resolves the movement:

> Protection does **not** restore identifiability. It removes the consequence of failing
> to identify — simulation becomes insufficient to *obtain* the protected effect, because
> prediction of an authorization does not confer the authorization.

The principal may therefore be perfectly predictable, and private information is not
required in principle. The guarantee lapses entirely if `A` can forge, bypass, rewrite or
seize the protected channel, and that lapse belongs in the hypotheses of any theorem
stated over it. Two further lapses are structural rather than adversarial: the report map
itself may have been authored by `A`, which is Movement VI and undischarged; and the
interface as modelled is one decision index deep, so foreclosure — `A` removing the
principal's *later* ability to correct — is not yet expressible.

Whether `Reach`-properness is the right formalization of "the principal has authority" is
a reserved **`maintainer-decision`**: the theorem says the capability form is forced *if*
the concept is inability, not that the concept is inability.

## Movement IV — fully updated deference (`π^{FU,g}`)

`blocked` on WP-C and WP-D, and additionally `blocked` at the level of the finite
model: the shared skeleton does not carry the time-indexed family of `A`-valuations
that `π^{FU,g}` needs, and the round declined to invent one, because inventing it
carelessly is how `π^{FU,g}` silently collapses into `π^SIM`. Skeleton v2 does not fill
the hole either; it is carried forward as `v2 §8.1`.

Stage II added one piece of the eventual statement and one piece of the eventual
confound. The statement: if "preempt now" means transferring future *jurisdiction*
rather than choosing the object-level intervention, the comparison is between execution
structures, and the skeleton carries no operation that reassigns the authorization
relation at a later index. That is a second hole, not a filled one. The confound is
priced exactly: a comparator measurable at the later time gains
`E_P[max_π X] − max_π E_P[X] ≥ 0`, reaching `2B(1 − 1/m)`, which is pure value of
information and has nothing to do with who decides. **A `π^{FU,g}` comparison that does
not net this out is measuring the wrong thing.** Uniformly in the credence the ladder
collapses and the competence requirement for a hindsight comparator is identical to that
for `FIXED[π]`.

**Stage III attempted the comparator and did not build one.** `FUD_COMPARATOR_SPEC.md` v1
is kept as a **corrected, defective record**, marked not a binding input. Its transferred
arm's selection is the argmax of the *evaluating agent's own objective under its own
credence*, hence computable at `t(n)`: the arm confers no cognition `A_n` lacks, and no
object representing a distinct `A_{g(n)}` occurs in the model. What was compared is the
principal's plan against the **optimal later-measurable plan** — the envelope this ledger
already recorded as upper-bounding every `FU[g]` and not being one. Both of the
prerequisites named above remain undelivered.

Three consequences, established by an independent adversarial review and accepted.

- The dominance result carries **no fairness hypothesis** and is `∑ maxima ≥ ∑ anything`.
- Its driver is future-agent **infallibility**, not "epistemic improvement only": a witness
  with every fairness condition intact, in which a better-informed but *fallible* future
  agent makes the gap strictly **negative**, is carried. The sign of the comparison is a
  definitional artifact.
- The absence of a jurisdictional term was **guaranteed by construction**: the
  specification waived `⊥` and the whole execution layer, which Movement V records as the
  place all of protection's valuation content sits.

Status: **`open`, and not well-posed as attempted.** No claim is made that the movement's
inequality is false, or that jurisdiction has low value; neither was visible to the model.

What survives, and is reusable: fifteen kernel-checked theorems in `EnvelopeDominance`,
named for what they prove; the fairness apparatus with three confound witnesses each moving
exactly one variable; the confirmation that **underwriting is absent from the engine**; and
one genuine reduction — the gap **is** the delegation deficit against the later-measurable
comparator class, so Track I's collapse applies to the same object rather than by analogy,
and any credence-free hypothesis bounding it is it. That reduction holds *a fortiori* for a
genuine `FU[g]`, since the envelope upper-bounds it.

A successor needs exactly two things, both already on the books: a future agent that can be
better-informed **and wrong**, and skeleton v2's execution layer reinstated with a declared
`X_{n,⊥}`.

**Stage IV attempted the first and failed, and the failure located the real obstruction.**
It gave each process its own credence, so the later agent would maximise its own
expectation rather than the evaluator's. That is not enough: the later rule differs from
the evaluator's conditional argmax by one argument and is still a total function of objects
known at the earlier time — and in the round's own instance the transferred arm's
realisation is *constant*, so the evaluator knows the realised action. The dominance result
is Movement IV's previous tautology with the arms swapped: the evaluator's argmax moved
from the transferred side to the delegated side, and the delegated side now trivially wins.

**The controlling finding is type-level, and it explains both failures at once.**

> Two authorisation regimes that induce the same realisation map `Ω → Π_n ⊔ {⊥}` are the
> **same object** in a signature whose only outputs are such maps priced by one measure.

Verified concretely: setting the principal's credence to the later agent's, with the
full-signal interface, makes the two arms identical at every one of 32,805 instances
tested. The jurisdiction assignment occurs in no formula. So Stage III "found no
jurisdictional term" in a model that had deleted the execution layer, and Stage IV found
the arms extensionally identical after adding a credence — **neither was going to work, for
the same reason**, and no further parameter repairs it. The authorisation relation has to
enter the *type*.

Status of the movement: **`open`, and now known to be blocked structurally rather than by
unbuilt components.** The philosophical gloss available from this line remains only the
deflationary one, and is if anything narrower: a valuation over realisation maps cannot
distinguish who authorised an action, which is a claim about the register and not about
jurisdiction.

## Movement V — certification and densification

**Certificate.** The literal target — a certificate implying strict dominance over
every comparator — is **not derivable** over the finite model, shown comparator by
comparator. Two theorems are derivable in its place, with derived and sharp
constants, and three impossibilities came with them. The sharpest: **no certificate
licensing discretion anywhere is strictly non-preemptive.** At any positive
tolerance there is a compliant model in which `A` overrides the principal inside the
certified event. Certified discretion with a bounded override rate, or no discretion
at all; there is no third option.

That impossibility now reads as a **bound on autonomy rather than an objection to
corrigibility**, under the roadmap's split between categorical jurisdiction and
quantitative autonomy: jurisdiction is settled architecturally when the protected
channel is invoked, and the certificate governs only the discretion operating on the
waived complement. The same mathematics, answering a different question. Fail-closed was
verified mechanically *within the finite model*; under a protected execution layer it
becomes a new obligation — `¬Cert` must cede to the channel, and `A` must be unable to
act without authorization — which a model with no capability structure cannot discharge.

**The reinterpretation was carried out over the v2 execution layer, and its result is
asymmetric.** Jurisdiction comes out cleaner than Phase I's version: the clause becomes a
hypothesis-free consequence of the interface, quantified over every conduct, with no
tolerance, margin or budget, and the grade-to-quantity assumption drops out because the
comparisons needing it become unstatable under protection. Autonomy deflates: every
authorized option other than the report's own designation is an override — exhaustively,
over all 512 protecting menus on a three-element intervention set — so there is no third
kind of option for a certificate to license, and "around" resolves to "on the complement
of".

**The decisive negative.** The entire valuation difference between the protected and
unprotected architectures is bounded by the certificate's own bound, and the bound is
attained, so tightening the certificate shrinks the distinction at the same rate and
never reveals it — exhibited at tolerance `10⁻⁶` with the worst per-state cost the
carriers permit. Approximate certification therefore **cannot converge to architectural
jurisdiction**.

Which parts survive the reinterpretation: the margin, override and advantage lemmas are
invariant, their inputs being computed from grades alone. The defect lemma survives as a
statement about the grade-register defect, but its bound is **not** a bound on the
protected valuation gap. The `FIXED` comparator of the delegation-advantage lemma is not
realizable under protection and loses its consumer entirely. The settlement-loaded branch
of the preemption bound is **false** under protection — 1443 refuting instances, not
merely unproved — while the settlement-free branch survives. The comparator clause is
load-bearing on the grade-to-quantity link and inherits that link's fate.

All of the refuted and reinterpreted material fell inside the set the Lean promotion
declined to port, so **no kernel-verified result is affected**. One further correction to
previously verified material: the certificate theorem's "strict minority" gloss on its
override clause is false, with an exact counterexample at override mass three fifths of
the certified credence. What clause (iii) delivers is only that the certified act
executes on positive mass.

**Densification.** The exposure geometry is an exact identity: under a cap, total
placeable weight by a deadline is the cap times the largest number of
pairwise-disjoint settlement windows before it. Adaptivity, overlapping positions
and fractional sizing each buy exactly nothing. The literal target is therefore
achievable in *every* delay regime, so the rate is the real question and the rate is
pinned. Three necessity witnesses show every apparent escape is an accounting
artifact. The item is under-specified until one **`maintainer-decision`** is taken:
bounded outstanding gross exposure and the Logical Induction bounded-loss budget are
different functionals and give different answers.

## Movement VI — non-authorship / dose

Inherited material exists at `../dose-response-note-dump-2026-07-02/` and has **not**
been assessed in this round; its status is therefore unrecorded rather than
assigned. Dose does not solve substitution, and the conceptual ordering is principal
individuation → actual-channel responsiveness → bounded shaping.

## Movement VII — preservation

`open`, downstream, untouched.

## Stage V — LI-native futurity and the jurisdiction boundary

**Market/trader gap: partially closed.** The signed-error trader's wealth was
already actual FAF net worth. Stage V derives its `EfficientlyComputable`
certificate from `RpnSentenceCodes` and invokes `IsLogicalInductor.noExploit`
directly. Bounded downside remains an explicit premise, and a tautology-contract
instance proves the package is inhabited. Faithful acceleration also already
uses actual traders, wealth and LIC; its exact residue is polynomial emission for
the exogenous cross-process quote sequence, cross-market calibration, and generic
process non-vacuity.

**Computational futurity: present as quotation, absent as a resource
separation.** FAF can efficiently emit sentences about `P (f n)` and proves
no-expected-net-update and self-trust relations for those quoted later prices.
This is a genuine temporal logical object not present in the finite models. FAF
does not define a resource-indexed agent state or prove that the day-`n` process
cannot already compute the later result. A two-proposal future-price comparison
can be quoted and can remain fallible, but it is a future recommendation fact,
not an action-selecting future agent.

**Future H⁺:** a total computable Boolean or bounded-rational report can be
quoted and eventually settle as a logical computation. With the additional
`FeedbackTruthComputation` deadline certificate, FAF can derive weighted signed
unbiasedness for predictions of that report. It does not derive pointwise or
magnitude accuracy, advice correctness, or authority.

**Self-trust boundary:** FAF self-trust constrains prices and expectations only.
An independent controller coordinate can vary while every self-trust premise,
conclusion and trader wealth path stays fixed. Epistemic self-trust does not
allocate practical sovereignty.

**Item 28's conditional core: kernel-proved and unregistered.**
`StaticViewFactorization.value_eq_of_price_realization_eq` proves that a
value explicitly factoring through price and realization is constant on equal-
view fibers. A worked architecture pair differs in jurisdiction while those
projections agree; a jurisdiction-reading value distinguishes it and is proved
not to factor through the static view. The result is elementary and exact. It
does not establish unrestricted jurisdiction invisibility, say jurisdiction is
valuable, forbid additional inputs, or give an approximate conclusion for nearby
views.

**Foreclosure:** still ingenuity-level model debt. A credible candidate needs at
least two execution states and a transition/capability relation so identical
immediate behavior can differ in future H⁺-controlled correction reachability.
LI can price computable facts about such a structure but does not supply it.
Preserved reachability has ordinary option value only under explicit assumptions;
commitment refutes unconditional menu monotonicity.

The live interface document and its human register are
`LI_NATIVE_DEFERENCE.md` and `LI_NATIVE_DEFERENCE_FOR_HUMANS.md`.

## The standing gap

The market/trader gap is no longer one undifferentiated item. Actual FAF closes the
criterion application for signed forcing and supplies the market semantics for
faithful acceleration. The remaining high-value gap is cross-process: efficient
emission and calibration of one inductor's later prices inside another's trader.
Beyond it, the controlling model debt is a resource-indexed future process joined
to a two-index authorization/capability transition structure.
