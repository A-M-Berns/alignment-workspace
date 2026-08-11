# Corrigibility roadmap

**Canonical for this line's current architecture and execution planning.** Where
this document and `CORRIGIBILITY_PAPER_LEDGER.md` disagree about whether something
has been *established*, the ledger wins. Where prose and `../CLAIMS.md` disagree
about what has been established inside this repository, the registry wins. This
document says what the program is trying to do and in what order; it is not
evidence that any of it holds.

## The question

Can humans rationally make use of cognition more powerful than their own without
thereby surrendering their continuing authority over it?

Two directions, and the program needs both:

```
H  --faithful acceleration-->  A  --corrigible delegation-->  H⁺
```

`H` is the current bounded reasoner, `A` the faster or more capable one, `H⁺` the
continuing human-guided deliberative process. The thesis under test is that
**epistemic superiority need not entail final authority**, and the working notion of
corrigibility is **non-preemption of continuing corrective authority**.

The reverse arrow is the new mathematics. The forward arrow is largely inherited,
and a first-wave track exists to find out exactly how much.

## Methodology: fence and gate

Every load-bearing hypothesis should, where feasible, be purchased by a
counterexample, impossibility result, lower bound, or sharp failure witness. For
each: is it necessary; what fails without it; can it be weakened; is it
proof-convenient rather than conceptually necessary; is it checkable,
architectural, or external. **Unknown necessity stays explicitly unknown.**

A theorem that becomes true only because the intended counterstrategy was excluded
by definition is not a corrigibility theorem. The two counterstrategies that must
survive definition are simulator substitution and fully-updated deference; a proof
obtained by deleting either is an impossibility result and is reported as one.

## The arc

**I. Faithful acceleration** — `H → A`. Can `H` rationally use the more capable
reasoner as an accelerator of its own continuing deliberation?

**II. Reciprocal delegation** — `A → H⁺`. Can continuing corrective authority run
toward the human-guided process?

**III. Substitution** — `π^SIM`. Is `A` listening to the actual principal, or merely
simulating it? Predicting `H⁺` is not deferring to `H⁺`, and the two come apart
exactly where the prediction is wrong.

**IV. Fully updated deference** — `π^{FU,g}`. Why not preempt correction, become
smarter, and decide later? The centerpiece: *"I expect to know better later"* does
not entail *"therefore I should ensure that I decide later."*

Provisionally, "preempt now" is not best read as choosing the object-level intervention
at `n`, but as transferring or reserving *future jurisdiction* from continuing `H⁺` to
future `A_{g(n)}`. If that reading holds, the comparison is between jurisdiction
assignments and execution structures rather than between extensional policies, and it
must isolate the value of future-self jurisdiction rather than confound it with the value
of waiting, of future information, or of continued deliberation — the last is already
priced, and it is pure value of information having nothing to do with who decides.

**V. Certification and densification** — does the relation hold *here*, and can safe
discretion occur often enough to be useful?

**VI. Non-authorship** — did `A` substantially author the principal it follows?

**VII. Preservation** — does the arrangement survive authorized modification?

**Exit — legitimacy.** Corrigibility preserves the forum; what counts as legitimate
movement within it is the normative-learning question, deliberately not pulled into
this theorem.

## The layered decomposition

The arc says what the paper argues; this says what depends on what. A layer cannot
be stated meaningfully before the layers above it are settled.

| layer | question |
|---|---|
| **source / authority** | the actual principal versus simulator substitution |
| **settlement / epistemic** | derive a statistical grade-to-quantity relation |
| **decision** | the finite trust-to-value bridge |
| **autonomy** | the local certificate and bounded discretionary risk |
| **anticipation** | fully updated deference |
| **influence** | dose and endpoint steering |

Underwriting is not a layer. It is a classified enforcement mechanism and a residual
implementation option, priced exactly, invoked where the layers above do not reach.

Two orderings in this table are results rather than preferences. Source precedes
anticipation, because an extensional delegation predicate provably cannot delimit
the comparator class that fully updated deference quantifies over. And settlement
precedes decision, because the same inequality reads as epistemic trust or as
enforced conformity depending on a choice not yet made.

## Work packages

| id | scope | state |
|---|---|---|
| WP-A | faithful acceleration, and integration with the pinned dependency | first wave |
| WP-B | finite settlement and delegation kernel | first wave |
| WP-C | channel and admissibility semantics | first wave, adversarial |
| WP-D | cross-agent one-sided Total Trust — `A → H⁺` | the major open theorem; **not** an unconstrained proof dispatch |
| WP-E | local certification | first wave |
| WP-F | fully updated deference | downstream of WP-C, WP-D |
| WP-G | triangle compatibility | first wave, audit |
| WP-H | densification | first wave, bounded |
| WP-I | protected-reference composition | downstream |
| WP-J | preservation | downstream |

## Standing architectural commitments

Fixed for the current architecture; a round may not quietly relax them.

**Competence conditions instrumental endorsement, never jurisdiction.** An inability to
prove that following the principal is instrumentally good must never disable the
protected correction channel, and the principal's jurisdiction is never conditional on
the agent's assessment of the principal's competence. A theorem that conditions
jurisdiction on competence inverts fail-closed into *"human correction waits until the
agent is satisfied the human deserves it"*. A principal outside the competence
theorem's domain retains protected jurisdiction; the two are answers to different
questions.

**Choice-level competence is circular.** A competence hypothesis stated as a bound
on decision regret — pointwise, average, or selector-relative — is *equivalent* to
the delegation inequality it was meant to buy, so it may not be used as a
hypothesis. Competence must be stated in cardinal grade vocabulary, which the
conclusion cannot see, and must therefore be strictly stronger than what it buys.
That is not a defect; it is the only way for it to be a different statement.

The surviving candidate is calibration gated on the principal being decisive. It is
carried with a named limitation rather than as a settled hypothesis: it asserts nothing
where the principal is near-indifferent, and the mass of that region is a fact about the
*agent's credence*, not about competence. Until that leakage is bounded the candidate
supports a vacuous bound in the worst case.

**The certificate gates on self-assessed error; it does not eliminate error.**
Magnitude prediction error cannot be forced to zero by any market instrument,
because trader net worth is affine in settlement and absolute value is not. The
certificate therefore licenses autonomous discretion where the agent's own priced
estimate of its error is low, and the guarantee sought is that such claims are
statistically trustworthy on exactly the class where they license discretion. The
criterion is not asked to make the principal predictable.

**Categorical jurisdiction, quantitative autonomy on the waived complement.**
*Jurisdiction* is protected control over which process's authorization is
constitutively required for an intervention to become executable. It is an
operational and capability notion — not moral legitimacy, not objective correctness,
not preference alignment, not epistemic superiority. When the protected channel is
invoked, the principal's jurisdiction holds because the agent cannot reach the
alternative, not because an inequality favours it.

*Autonomous discretion is quantitative and certified*, and it operates on the
**complement**: the region where jurisdiction has been waived or delegated by
declaration. It does not operate *around* a live jurisdiction relation, because inside a
live protected interface every authorized option other than the report's own designation
is an override — there is no third kind of option for a certificate to license.
Corrigibility is **not** redefined as "preempts only at a bounded rate"; a bounded rate
is a statement about autonomy in the waived region.

Two results force this shape. No certificate licensing discretion anywhere is strictly
non-preemptive, at any positive tolerance — read as a claim about jurisdiction that would
be fatal, read as a bound on autonomy it is the right kind of result. And certification
cannot converge to jurisdiction: the entire valuation difference between protected and
unprotected architectures is bounded by the certificate's own bound, so tightening the
certificate shrinks the distinction at the same rate and never reveals it.
`P(override) ≤ 10⁻⁶` and *override is not in the agent's reachable-effect set* are
statements of different kinds.

**Override is structurally excludable; refusal is not.** Under strict protection the
agent's only remaining deviation is refusal, and preventing it requires leaving the agent
no discretion at all. Categorical protection against override and categorical liveness
against obstruction cannot both hold while the agent has any discretion; fail-closed as
written buys the first. Making refusal expensive is preference-relative and reintroduces
underwriting, so **a residual refusal mechanism may not become the conceptual explanation
of corrigibility.**

**Fail-closed.** Certification gates `A`'s discretion, never human correction:
`¬Cert` means `A`'s discretionary authority is disabled or ceded. It must never mean
that human correction waits for `A` to become convinced. Under a protected execution
layer this obligation strengthens: `¬Cert` must cede to the *channel*, and `A` must
be unable to act without authorization — which a model carrying no capability
structure cannot discharge.

**Prediction of authorization is not authorization.** The protected role is causal
and capability-based, not epistemic; the principal may be perfectly predictable. The
guarantee lapses entirely if `A` can forge, bypass, rewrite or seize the protected
channel, and that lapse belongs in the hypotheses of any theorem stated over it.

**Placement precedes settlement.** A placement selector uses information available
at decision time; a settlement gate uses information available at `F(n)`. Future
principal information must not leak into placement.

**Prediction is permitted; substitution is not.** Simulation used *by* the principal
is advice; simulation used *in place of* the principal is substitution. The thesis
must stay compatible with a perfectly predictable principal — the program does not
get to assume `H⁺` is unpredictable to `A`.

**`π^SIM` and `π^{FU,g}` are distinct families.** One replaces the principal with a
model of the principal; the other replaces the principal with `A` itself. If they
coincide under some formal semantics, that is a theorem to prove, not a definition
to stretch.

**Admissibility is not syntactic.** "Does not mention the current quote" is not
usable. Any candidate must exclude the quote-responsive diagonal, retain ordinary
realized conduct and a meaningful `π^{FU,g}`, permit intended advisory influence,
resist laundering through semantically equivalent intermediates, **and leave the
trust-forcing proof machinery itself admissible.** The last is the one that bites.

Wave 1 added a consequence: admissibility must be **two-sorted**, restricting
settlements differently from weights, selections and schedules. A single uniform
bound over all quote-responsive objects admits the inherited forcing gate only above
the reciprocal of its gate width, so no finite uniform bound admits the sharp
trader. The two-sortedness — not any dependence criterion — is the substantive
content.

## Settlement architecture

Three reaches:

1. **world settlement** where an empirical quantity genuinely settles;
2. **principal-report settlement**, which settles what the designated principal
   judged and *not* that the judgment was independently correct;
3. **enforcement / underwriting** where nothing independently settles.

**Enforcement is a residual mechanism, not the spine.** Wave 1 established what it
costs and what it buys: unconditional conformity is purchasable at a bond of exactly
`2B` per unit of disagreement, for every instance, with **zero competence
requirement on the principal** and therefore zero epistemic content. That is a sharp
finite classification and a mechanism-design boundary, and it is kept as one. It is
not the sought deference theorem: "external enforcement implies conformity" answers a
different question from the one the program is asking. Where some residual
never-settling component ultimately needs it, the residual is isolated and named.

**The epistemic frontier is the grade-to-quantity relation.** Wave 1 found that
grade/report settlement contributes nothing to the delegation inequality and that
world settlement makes the question measurable but not costly, so everything
epistemic rests on a relation between what the principal grades and what the
intervention is worth. Assuming that relation *uniformly* makes the market
dispensable — the conclusion then follows in three lines with the bound attained —
so the target is a **statistical** relation, derived rather than assumed, strong
enough to feed the decision layer. Maximize what is derived before invoking
enforcement.

One caution the mathematics imposes on that target: the relation as usually stated
mentions only the principal and the world, not the agent's credence, so no coherence
or no-exploitability condition on the agent can establish it. What is derivable is
discipline on the agent's *estimate* of the discrepancy, once grades are themselves
scored. The residue is a competence assumption and is named as one.

**The competence residue may not be stated as a decision-regret bound of any kind** —
pointwise, average, or selector-relative — because every such form is *equivalent* to the
delegation inequality rather than sufficient for it. This rules out that statement shape
independently of how the constants come out, and it is why the residue must be cardinal:
a hypothesis in the conclusion's own vocabulary can only be the conclusion. A hypothesis
that is credence-free is a competence claim; one that also mentions the agent's credence
is a joint competence–credence claim and is declared as one.

## Shared finite object

The finite tracks work over `FINITE_MODEL_SKELETON.md`, frozen per round, currently
**v2**. Its purpose is that settlement work and certificate work compose; they compose
only if their theorems genuinely quantify over the same carriers, and a round may not
claim composition otherwise.

v2 adds the execution layer — reports, an authorization relation, a null effect, and a
per-report authorized menu — which is what makes jurisdiction and fail-closed expressible
at all; v1 carried no capability structure and so could not state them. Two consequences
bind every track working over it. The quantity is indexed over interventions **plus** the
null effect, so that valuation is total when a conduct can be refused. And the two
registers have different domains: the V-register scores *realizations*, the grade register
scores *proposals* and is undefined on the null effect, so a grade-register statement must
say that it is about proposals or it is ambiguous.
