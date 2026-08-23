I’d make the follow-up explicitly try to close the reason-state interface enough to hand it to the transition/Licensed layer, rather than doing another open-ended representation pass.

Follow-up research round: close the reason-state narrow waist and derive the reason-accounted transition interface

Work in the live A-M-Berns/alignment-workspace repository. Start from PR #48, “Legitimacy: prosecute the reason-state narrow waist”, and read its prompt, MEMO.md, implementation, tests, and relevant prior legitimacy rounds directly. Do not rely on this dispatch’s summary when the artifacts say something more precise. Base this round on the PR #48 head unless repository rules require another arrangement; do not silently merge or promote PR #48.

The previous round substantially supported a narrow reason-state substrate:

> V ::= \mathsf{Atom}
> \mid \mathsf{Neg}(V)
> \mid \mathsf{App}(\sigma,c,n)
> \mid \mathsf{Inst}(e,\sigma)
> \mid \mathsf{Incomp}(S)
>

with identity-bearing append-only reason occurrences

> e=(id,\;s(e)\subseteq_{\mathrm{fin}}V\sqcup L,\;t(e)\in V),
>

bare schema and case identities, a separate stance B, a monotone transcript L, and a total stateless query interface centered on Enabled, Reasons, Dependents, Explain, and LostBasis.

The round also proposed:

* a constitutive involutive negation floor;
* richer substantive incompatibility as revisable content;
* staged applicability App(σ,c,n);
* applicability-in-source;
* persistence of applicability by ordinary defeasible reasons rather than automatic substrate behavior;
* Inst as revisable schema organization that does not retroactively rewrite occurrence sources;
* JTMS/ATMS functionality as policy + caching above the substrate rather than the substrate itself.

Treat all of that as provisional and attackable, not as established doctrine.

Primary goal

Determine whether this representation is now sufficiently precise to support the next narrow waist:

> \boxed{
> \text{reason state}
> +
> \text{normative record}
> +
> \text{stance}
> \longrightarrow
> \text{reason-accounted normative transitions}
> }
>

In particular, try to derive the smallest useful interface for a transition or Licensed certificate that can say:

this revision / undertaking / response was licensed by these particular reasons, under these applicability judgments and this prior authority, and remains answerable to that basis if it later loses standing.

Do not begin by inventing a full normative learner or a general stance-update policy. The question is whether we can specify the certificate/postulates on individual transitions before specifying how the learner chooses among all allowed transitions.

⸻

Part I — repair or refute PR #48’s remaining representation defects

Before building anything downstream, prosecute at least the following.

1. Genuine n-ary incompatibility

PR #48 intends Incomp(S) to represent arbitrary finite substantive conflict, including cases where

> \{a,b,c\}
>

is jointly impossible while every pair is compatible.

Inspect whether the current implementation actually has that semantics. In particular, attack any definition that turns

> \mathsf{Incomp}(\{a,b,c\})
>

into pairwise incompatibility.

Develop the correct primitive/derived interface. Possible shape:

> \mathsf{Conflict}_B(S)
>

over finite sets of contents, with binary rebuttal only a derived special case if appropriate.

Test at least:

* pairwise contradiction;
* genuinely ternary conflict with all pairs compatible;
* overlapping conflict sets;
* a learned incompatibility later defeated;
* a stance containing all members of an adopted conflict remaining representable but criticizable, rather than being rejected by the substrate.

If this forces a change to the representation, make it. If it reveals that Incomp is the wrong abstraction, say so rather than patching around it.

2. Semantics of staged case views

PR #48 distinguishes

> \mathsf{App}(\sigma,c,n)
> \quad\text{from}\quad
> \mathsf{App}(\sigma,c,n+1),
>

which is necessary to distinguish changed-world from corrected-belief histories.

But determine whether c@n currently has actual semantics or whether the stage argument is merely an identity tag.

Give the smallest explicit semantics required. Candidate:

> \operatorname{View}(c,n;N_{\le n},L_{\le n}),
>

where the case identity is persistent but the stage view is determined by the record/transcript prefix.

Questions to prosecute:

* What information belongs in a case view?
* Is App applicability to the entire case view, or merely to a case identity under a stage-indexed evidential situation?
* Can two record histories induce the same c@n view?
* Must applicability depend on world-time, receipt-time, or record-time? The previous round chose record-time; attack that choice.
* Does delayed evidence produce pathological retroactive applicability?
* Can the semantics remain external to the reason state, or must App carry more structure?

Avoid turning Case into a giant state bundle unless examples force it.

3. Constitutive negation really is constitutive

Audit the reference model’s claim that

> \neg\neg x=x.
>

If direct construction permits syntactically distinct Neg(Neg(x)), repair the model with normalization, a smart constructor, quotienting, or another minimal mechanism.

More importantly, prosecute whether a fixed contradiction floor is genuinely the minimum unavoidable constitutive logic. Try alternatives. The floor should contain only what must be fixed for the reflective language itself to be intelligible.

4. Applicability-in-source

The previous round admitted this is currently a convention rather than type-enforced structure.

Determine whether:

1. it should remain an explicit well-formedness condition,
2. it can be derived from another invariant,
3. the types should enforce it, or
4. the convention is actually too strong.

Give adversarial examples involving:

* ordinary warrant application;
* an occurrence with multiple applicable schemas;
* nested undercutting;
* reclassification after reliance;
* persistence schemas;
* an occurrence whose applicability judgment itself has lost basis.

If the convention survives, implement a checker and tests for it.

⸻

Part II — derive the transition-certificate narrow waist

Once the representation survives Part I, derive—do not merely stipulate—the smallest transition certificate the current consumers require.

The central candidate is something like:

> \mathsf{Cert}(m):
> \quad
> \text{transition }m
> \text{ cites a finite set of reason occurrences}
>

together with enough information to establish that those occurrences were available/applicable/licensed in the pre-state and to reopen the transition if its relied-on basis later disappears.

Work from the existing:

* internal-answerability round;
* role-parametric answerability round;
* afoundational normative-record/inquiry round;
* PR #48 reason-state round;
* Due / Licensed / Performance response-learning interface;
* current wiki architecture.

Do not duplicate machinery already established in the record layer.

Prosecute the following candidate requirements

A. Finite cited basis

A normative transition cites particular occurrence identities, not merely conclusions or schemas.

Attack whether this is necessary. Use the equal-content/different-occurrence case.

B. Pre-state validity

A certificate may cite only occurrences enabled under the relevant pre-transition stance/transcript:

> \forall e\in Basis(m),\quad
> \mathsf{Enabled}_{B_n,L_n}(e).
>

Determine exactly which time/index is appropriate and whether anything must be frozen beyond enabledness.

C. Applicability provenance

For a cited reason occurrence, the certificate should expose the App claims actually present among its constitutive sources rather than reconstructing applicability later.

Test whether that is enough for future basis-loss review.

D. License versus grounds

Preserve the existing distinction

> \boxed{
> grounds\neq normative\ license\neq account\ lineage.
> }
>

A reason occurrence may explain why this content without entitling the process to perform this kind of normative act.

Determine the minimum additional citation needed for normative license. In particular:

* Does a certificate cite a record-side authority occurrence?
* a May rule?
* a license genealogy endpoint?
* some typed scope object?

Do not hide authorization inside generic reason support.

E. Target/scope typing

Ask whether Licensed can remain

> Licensed:S\to D\to A\to Prop
>

with a certificate underneath it, or whether the reason representation forces a richer typed target/scope interface.

Try belief revision, practical undertaking, schema reclassification, rule amendment, and inquiry launch as distinct transition kinds.

F. Basis loss

If a transition relied on occurrence e and e later becomes disabled, the record should detect this even if an alternative reason for the same conclusion now exists.

This should compose with the existing account/review machinery, not replace it.

Test:

* same conclusion, different basis;
* original basis undercut, substitute basis available;
* schema reclassified after the transition;
* applicability persisted at n+1 but the transition relied on applicability at n;
* an incompatibility claim underlying the transition is later defeated.

G. Non-laundering

Try hard to construct transitions that certify themselves.

At minimum attack:

* transition creates the reason that licenses itself;
* transition creates the authority that licenses itself;
* two simultaneous transitions mutually license one another;
* reclassification of an occurrence changes the claimed historical basis;
* a new interpretation of a receipt retroactively turns an old transition into a licensed one;
* a new persistence judgment launders a past applicability failure.

Check whether strict pre-state citation plus immutable occurrence sources and the existing authority-genealogy rule already exclude these, or whether another axiom is required.

⸻

Part III — ask whether a small postulate set emerges

Do not assume the following names are correct, but specifically test whether the transition discipline compresses to a small set of independent postulates such as:

1. Basis — every relevant normative transition cites finite particular reasons.
2. Prior license — the transition’s type/scope was authorized in the pre-state by genealogy terminating in the admitted seed.
3. Conservation / lineage — if the transition disposes of or transforms an existing commitment/liability, its account edges preserve the old occurrence identities.
4. Defeat sensitivity — loss of a relied-on basis creates review/answerability rather than silently rewriting history.
5. No self-grounding — neither reasons nor licenses created by the transition may justify that same transition.

Try to collapse or refute these. I am more interested in finding three genuine principles than retaining five labels.

For every surviving postulate:

* give a minimal failure witness without it;
* say which downstream theorem/interface consumes it;
* say whether it belongs to the reason state, normative record, certificate checker, or learner policy.

In particular, look for a clean theorem-shaped statement of the form:

> \text{well-formed reason-accounted certificate}
> +
> \text{record invariants}
> \Longrightarrow
> \text{internal answerability properties}.
>

It is fine if the result is only a finite formal kernel or an interface theorem rather than the full philosophical property.

⸻

Part IV — test whether Licensed can now become substantive

The previous reason-state round says its main downstream payoff should be Licensed.

Try to turn that into an actual object.

Preferred outcome:

> Licensed(S,d,a)
>

is witnessed by a certificate whose:

* cited reasons are identifiable;
* applicability is explicit and defeasible;
* normative authority/scope is prior and independently genealogized;
* lineage to what is being answered is explicit where relevant;
* later basis loss is mechanically detectable;
* certificate cannot be manufactured by the very transition it licenses.

Then run this against the response-learning kernel’s existing R1–R7 / Due / Licensed expectations.

Do not claim substantive normative truth. A certificate establishes something like:

this response is licensed within the current accountable normative practice.

It need not establish that the practice is morally correct.

If Licensed still cannot be made nontrivial without smuggling substantive normative judgment into a checker, identify the exact blocker. That negative result would be important.

⸻

Scope discipline

Keep these out unless a concrete counterexample forces them in:

* probabilities and credences;
* market prices;
* traderization/liability;
* utility securities;
* general corrigibility/deference;
* a complete stance-update algorithm;
* a general priority calculus;
* philosophical moral realism;
* a general theory of empirical induction.

Generalization from examples remains the host inductor’s job. Do not reinsert a generic Generalize operation into the normative seed.

Likewise, do not make the reason state itself decide what to believe. If an operation chooses a stance, resolves conflicts, weighs priorities, or adopts every supported conclusion, name it as a policy layer.

⸻

Required adversarial fixtures

In addition to examples inherited from PR #48, include finite tests for:

1. genuine three-way incompatibility with pairwise compatibility;
2. corrected belief versus changed situation across staged case views;
3. delayed receipt about an old case;
4. transition supported by two extensionally identical but historically distinct reasons;
5. transition whose relied-on reason is later undercut while an alternative remains;
6. transition attempting to mint its own license;
7. same-transition mutual licensing;
8. schema split after a certified transition;
9. cross-cutting schema organization;
10. license inherited through a diamond-shaped authority genealogy;
11. authority genealogy valid but substantive grounds absent;
12. excellent substantive grounds but no authority to perform that transition;
13. practical n-ary conflict;
14. applicability persistence justified in one case and unjustified in another;
15. a certificate that would pass if grounds/license/lineage were conflated and must fail under the repaired interface.

Add further kill tests where useful.

⸻

Deliverables

Produce a focused research round under the appropriate projects/normativity/legitimacy/rounds/ path containing:

* MEMO.md with the prosecution, repairs, verdict, and exact proposed interface;
* executable exact finite fixtures/tests;
* a small reference implementation if useful;
* a compact mapping to the prior reason-state and answerability interfaces;
* PROVENANCE.md and normal workspace round artifacts;
* wiki edits only if the result genuinely changes the conceptual architecture and repository governance permits it.

The memo should contain explicit sections:

1. What survived from PR #48
2. What failed and why
3. Final reason-state interface
4. Final transition-certificate interface
5. Which postulates are independent
6. Licensed verdict
7. What remains policy rather than substrate
8. What remains genuinely open

End with a concrete recommendation for the next research pass.

Open a PR when complete. Do not register or promote claims unless repository rules and maintainer authorization explicitly permit it. Mark finite-test-supported versus derived versus proved claims accurately.

Success criterion

A successful round does not need to produce a full normative learner.

It succeeds if, after prosecution, we can draw a reasonably stable boundary:

> \boxed{
> \text{reason substrate}
> \to
> \text{reason-accounted transition certificate}
> \to
> \text{normative record/accountability}
> }
>

and say exactly what is still missing before the transition system can be called reflectively legitimate.

A particularly good outcome would be discovering that a small set of certificate invariants simultaneously explains the existing conservation, prior-authorization, non-laundering, and basis-loss-review conditions rather than treating them as unrelated rules.

If that compression fails, demonstrate why with minimal counterexamples rather than adding machinery until it works.

---

*Sent mid-round, before the pull request was opened:*

Use this as a **late-stage addendum**, not a replacement for the existing prompt. I’d make it explicitly ask for a closure decision rather than another representation brainstorm.

> ## ADDENDUM — try to close the reason-representation narrow waist
>
> Do not restart or rewrite the primary pass. Complete its existing investigations, then add a final **narrow-waist closure phase** before the PR is finalized.
>
> The purpose of this addendum is to answer a stricter question than “does the current representation handle the examples?”:
>
> [
> \boxed{
> \text{Is the reason-state interface now stable enough that future work should occur above it?}
> }
> ]
>
> Treat “closed” as a research-engineering status, not a mathematical uniqueness claim. We do **not** need to prove that no alternative representation exists or that this ontology is formally minimal. We do need enough evidence that new primitives should henceforth require a concrete failure of the interface.
>
> ---
>
> # 1. State an explicit closure criterion
>
> Before drawing a verdict, formulate the criterion you are using.
>
> A candidate:
>
> > The reason-representation narrow waist is provisionally closed iff:
> >
> > 1. the known adversarial microhistories are representable without hidden stance policy;
> > 2. the currently known downstream consumers can obtain what they need through the public interface;
> > 3. the remaining open questions concern semantics, policy, authorization, learning, or implementation rather than missing representational kinds;
> > 4. attempts to remove any surviving primitive produce a concrete loss of expressive capacity or a collapse of an important distinction;
> > 5. attempts to add plausible new primitives can instead be represented using existing contents, occurrences, record facts, or derived queries.
>
> Improve this criterion if prosecution suggests a better one.
>
> The closure verdict should be one of:
>
> ```text
> CLOSED-PROVISIONALLY
> NOT-CLOSED — specific missing primitive/interface
> INDETERMINATE — specific unresolved kill test
> ```
>
> Do not use “closed” merely because all current tests pass.
>
> ---
>
> # 2. Prosecute the ontology by subtraction
>
> For every surviving primitive/type distinction, try to remove it.
>
> At minimum attack:
>
> ### Identity-bearing reason occurrences
>
> Can reasons instead be identified extensionally by `(sources,target)`?
>
> Kill this with historical reliance, repeated independent occurrences, different cases, or another minimal example—or conclude identity is unnecessary.
>
> ### Hyperedges rather than ordinary edges
>
> Can conjunction of sources be compiled into ordinary intermediate claim vertices without loss?
>
> Ask whether doing so invents reason occurrences/commitments the learner never actually had, changes historical basis identity, or otherwise makes the compilation semantically nonconservative.
>
> Be precise about whether “multi-hypergraph” is essential ontology or merely convenient presentation.
>
> ### Separate receipt and claim sources
>
> Try seriously to collapse
>
> [
> V\sqcup L
> ]
>
> into one source sort.
>
> Determine whether this inevitably makes transcript facts defeasible, introduces an “indefeasible claim” subtype equivalent to the receipt sort, or actually yields a cleaner representation.
>
> ### `App`
>
> Try to eliminate explicit applicability as content.
>
> Alternatives to prosecute:
>
> * applicability encoded into the occurrence identity;
> * applicability encoded into source claims without a dedicated constructor;
> * attack/undercut relation instead;
> * case-indexed schemas;
> * negative dependencies/default absence.
>
> Ask whether any alternative preserves nested undercutting and reflective criticism without moving normative policy into structure.
>
> ### `Inst`
>
> Try to eliminate schema-membership claims.
>
> Can schema organization be recovered from provenance or occurrence metadata? If so, can the learner still reason that its old classification was mistaken without rewriting history?
>
> ### Staged applicability
>
> Try to remove the stage index or replace it with some other object.
>
> The representation must distinguish:
>
> [
> \text{“I was wrong that it applied then”}
> ]
>
> from
>
> [
> \text{“it applied then and no longer applies now.”}
> ]
>
> Determine the minimum structure necessary for that distinction.
>
> ### Constitutive contradiction floor
>
> Try to make all incompatibility revisable.
>
> Does that make `p` and `¬p`, or `App` and `¬App`, jointly acceptable except by a further learned norm? If yes, state exactly why a minimal logical floor is representational rather than substantive normativity.
>
> ### `Incomp`
>
> Try to eliminate the dedicated constructor in favor of ordinary atoms, typed feasibility predicates, or another mechanism.
>
> Distinguish:
>
> [
> \text{logical contradiction}
> ]
>
> from
>
> [
> \text{learned finite substantive incompatibility}.
> ]
>
> If `Incomp` survives, ensure genuinely n-ary conflict is represented without inducing false pairwise conflict.
>
> ---
>
> # 3. Prosecute the ontology by addition
>
> Construct a list of plausible primitives that someone might reasonably think are missing:
>
> ```text
> Undercuts
> Rebuts
> Priority
> Reliability
> EvidentialRelevance
> Hold
> Do
> May
> Must
> Supported
> Live
> Defeated
> Assumption
> Context
> Environment
> CaseView
> SameCase
> SchemaSuccessor
> ReasonStrength
> ```
>
> For each, classify it as exactly one of:
>
> ```text
> EXISTING CONTENT
> EXISTING RECORD FACT
> DERIVED QUERY
> LEARNER POLICY
> DOWNSTREAM NORMATIVE SEMANTICS
> GENUINELY MISSING PRIMITIVE
> ```
>
> Give a one- or two-sentence reason.
>
> The point is to test whether the interface has acquired a genuine **negative boundary**:
>
> [
> \boxed{
> \text{we know not only what belongs inside, but what belongs outside}.
> }
> ]
>
> Any item classified `GENUINELY MISSING PRIMITIVE` blocks closure.
>
> ---
>
> # 4. Consumer-completeness test
>
> This is the most important part of the addendum.
>
> Treat the reason state as an abstract module. Downstream code may use only its public types/queries plus the normative record and transcript. It may **not inspect representation internals** or invent hidden semantic fields.
>
> Test the known consumers one by one:
>
> ### Normative learner
>
> Can it determine:
>
> * what reasons currently bear on a content;
> * what reasons oppose or conflict with a candidate stance;
> * what would cease to bear under a hypothetical stance change;
> * what organizational/applicability judgments are themselves open to reasons?
>
> without the substrate deciding what to adopt?
>
> ### Historical answerability
>
> Can the record:
>
> * cite the exact occurrence actually relied upon;
> * recover its constitutive sources later;
> * detect loss of that basis;
> * distinguish alternative current support from original historical reliance?
>
> ### `Licensed`
>
> Can a transition certificate cite:
>
> * particular reason occurrences;
> * their applicability dependencies;
> * relevant case/stage;
> * the pre-state in which they were enabled;
>
> while keeping normative authorization/genealogy record-side?
>
> This current pass is already developing `Licensed`; explicitly note whether it **forces any new reason-representation primitive**. If it does, closure fails until that is resolved.
>
> ### Inquiry
>
> Can inquiry generation distinguish:
>
> * a receipt merely occurring during work on a case;
> * a reason taking that receipt to bear on an issue;
> * unresolved conflict or basis loss worth docketing?
>
> ### Operative compiler
>
> Without solving `R → O`, can a future compiler at least recover all representation-level information it plausibly needs:
>
> * endorsed content;
> * current bearing;
> * exact cited bases;
> * applicability;
> * schema organization;
> * case/stage;
> * historical reliance?
>
> If any consumer needs a representational fact that cannot be expressed or queried, identify the missing fact exactly.
>
> End this section with a table:
>
> | Consumer | Needs | Supplied by | Needs new primitive? |
> | -------- | ----- | ----------- | -------------------- |
>
> Closure requires every currently known consumer to answer “no” in the last column.
>
> ---
>
> # 5. Representation vs policy audit
>
> For every proposed checker or invariant in the round, ask:
>
> [
> \boxed{
> \text{Does this make a structure well-formed, or does it decide how a reasoner ought to respond?}
> }
> ]
>
> In particular prosecute:
>
> * stance consistency;
> * closure under supported conclusions;
> * conflict resolution;
> * priority;
> * persistence of applicability;
> * treatment of undercutters;
> * whether review must occur;
> * which reason is stronger;
> * which schema should organize a case.
>
> The narrow waist should remain total on **criticizable states** whenever possible.
>
> A stance being irrational, conflicted, unresponsive, or normatively bad should usually not make it unrepresentable.
>
> If some proposed representational invariant rules out exactly the bad behavior later legitimacy theory is supposed to criticize, presume it is in the wrong layer and prosecute it hard.
>
> ---
>
> # 6. Test the “multi-hypergraph + stance” characterization
>
> Determine whether the following is now an accurate mathematical compression:
>
> [
> H=(V,E,s,t)
> ]
>
> is an append-only identity-bearing directed multi-hypergraph, with
>
> [
> s:E\to\mathcal P_{\mathrm{fin}}(V\sqcup L),
> \qquad
> t:E\to V,
> ]
>
> and
>
> [
> B\subseteq V
> ]
>
> is a separate stance/marking.
>
> The currently enabled slice is
>
> [
> E_{B,L}
> =======
>
> {e:s_V(e)\subseteq B,;s_L(e)\subseteq L}.
> ]
>
> Ask:
>
> * Is “multi” genuinely required?
> * Is “hyper” genuinely required?
> * Is the stance accurately modeled as a marking/subset of claim vertices?
> * Are schemas/cases best modeled as external identity sorts referenced by reflective claim constructors?
> * Is anything important lost by describing the substrate this way?
>
> Give an explicit verdict. If the language is merely mnemonic and the actual type is importantly different, say so.
>
> ---
>
> # 7. Attempt a representation-completeness counterexample search
>
> Do not attempt an impossible general theorem over all future normative reasoning. Instead search systematically for **classes of microhistory not already represented**.
>
> At minimum generate examples involving:
>
> * testimony about testimony;
> * reasons about the reliability of a reason source;
> * several independently sufficient bases;
> * jointly necessary sources;
> * circular support;
> * self-undercutting;
> * mutual undercutting;
> * reasons about incompatibility;
> * reasons that a schema was previously misapplied;
> * reasons that two cases should be merged;
> * reasons that a previous merge was mistaken;
> * delayed evidence about an old case;
> * evidence relevant to several cases differently;
> * practical resource conflicts;
> * permissions versus positive reasons to act;
> * reasons to investigate rather than conclude;
> * a reason whose importance/priority changes;
> * a reason that another reason is unreliable but not inapplicable;
> * conflict between normative practices or scorekeepers.
>
> For each ask only:
>
> > Can the representational content and dependency structure be expressed?
>
> Do not require the substrate to decide the correct response.
>
> If these all fit by composition of existing primitives, record that as evidence for closure.
>
> ---
>
> # 8. Distinguish three kinds of remaining open problem
>
> At the end, classify every unresolved issue into:
>
> ### Representation-open
>
> We still do not know how to express some necessary reason fact/dependency.
>
> ### Semantics-open
>
> The representation is adequate, but some constructor needs a fuller interpretation—e.g. exact semantics of `c@n`.
>
> ### Policy/theory-open
>
> The representation exposes the situation, but we do not know the legitimate response—e.g. conflict resolution, priority, review, `Licensed`, learning.
>
> This distinction matters for closure.
>
> A narrow waist can be called provisionally closed with substantial **semantics-open** and **policy-open** work remaining.
>
> It cannot be closed with a known **representation-open** blocker.
>
> ---
>
> # 9. Freeze recommendation
>
> If the verdict is `CLOSED-PROVISIONALLY`, propose an explicit freeze rule:
>
> > Future work treats the reason-state public interface as fixed. A new primitive or breaking change requires a minimal counterexample showing that some required reason structure cannot be represented through the existing interface without importing learner policy or rewriting historical provenance.
>
> List:
>
> 1. the frozen public types;
> 2. the frozen public queries;
> 3. semantic conventions that remain provisional;
> 4. downstream objects explicitly excluded from the freeze.
>
> In particular, do **not** freeze implementation choices or caching strategies.
>
> If the verdict is not closed, give the **smallest next round** capable of deciding the blocker. Do not propose another broad representation survey.
>
> ---
>
> # Required final section in `MEMO.md`
>
> Add:
>
> ## Narrow-waist closure verdict
>
> containing:
>
> ```text
> Verdict:
>
> Core representation:
>
> Why each primitive survives:
>
> Negative boundary — what is deliberately outside:
>
> Consumer-completeness result:
>
> Remaining representation-open blockers:
>
> Remaining semantics-open questions:
>
> Remaining policy/theory-open questions:
>
> Freeze recommendation:
>
> Minimal evidence that would reopen the interface:
> ```
>
> The goal is to leave the next researcher knowing whether they should continue designing the reason representation or **stop touching it and work on revision/legitimacy above it**.
>
> The preferred result is not “the representation is elegant.” It is:
>
> [
> \boxed{
> \text{we have tried both removing and adding structure, tested its consumers, and now know where the abstraction boundary is.}
> }
> ]
>
> If that conclusion is not warranted, say exactly why.
