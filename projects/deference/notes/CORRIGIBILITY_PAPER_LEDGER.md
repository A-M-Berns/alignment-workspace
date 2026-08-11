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
holds **155 theorems across 10 files** that build against the pinned toolchain and audit
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

## Vocabulary

`inherited-established` — direct inspection of inherited material shows the result
was established there; carries no implication about the current proof stack.
`workspace-established` — this repository holds a statement of record meeting its
verification requirements. `architected` — precise enough to organize work, not
established. `open` — substantive mathematical uncertainty. `blocked` — waiting on
an upstream theorem, definition, or maintainer choice. `maintainer-decision` —
reserved.

## Evidence caveat for every inherited row

The rows below are attested by the inherited development's **own statement-level
audit**, `../note-dump-2026-06-27/lean/AUDIT.md`, which classified each theorem by
proof kind and hypothesis provenance. That audit is read as evidence; its Lean was
**not** rebuilt in this round, and the inherited tree carries its own toolchain and
lakefile rather than this repository's. A row saying `inherited-established` means
*the audit attests it*, not *this repository has rechecked it*. Confirming those
rows against the source is filed as `PRIORITIES.md` item 14.

## Movement I — faithful acceleration (`H → A`)

| result | inherited status | kind | what carries it |
|---|---|---|---|
| `value_iff_totalTrust` (finite-exact) | `inherited-established` | proved outright | `witness_identity`, the two-option identity; algebra alone |
| `value_iff_totalTrust_asymptotic` | `inherited-established` | proved, both arrows | linearity; the audit records "neither hypothesis is the conclusion" |
| `decomposition` | `inherited-established` | proved outright | pure linearity, no frame hypothesis |
| `softmax_lower_bound` | `inherited-established` | proved outright | genuine `exp` analysis; was a hypothesis, became a theorem |
| tower ⟹ Value, asymptotic and finite | `inherited-established` **conditionally** | composition | genuinely chains named Logical Induction facts; the facts are named, not derived |
| `soft_total_trust_doublysoft` | `inherited-established` **conditionally** | composition | support hypotheses discharged from the construction; calibration and criterion still named |
| "the criterion *forces* the tower" | **`open`** | — | see below |

The division is the whole story, and it is the inherited audit's own central
finding: **the corpus proves the implications of the deference theory, not its
antecedents.** The algebra composes. The forcing does not follow from anything in
the corpus, because the market and the traders are unmodelled, so every appeal to
"the no-Dutch-book criterion forbids the exploit" is either a named hypothesis or an
arithmetic stub standing in for the arbitrage argument.

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

## The standing gap

One item explains most of the rest. Modelling the market and the traders converts
"criterion ⇒ forcing inequality" from a named hypothesis into a theorem, and it is
the same gap the leverage line and the pinned dependency sit on the other side of.
It is `PRIORITIES.md` item 7 and the most valuable single item in that file.
