You are running a focused mathematical research round in `A-M-Berns/alignment-workspace` on the **Legitimate Evolution theorem and its cross-process recognition interface**.

This round begins **after the Carroll legitimacy round has closed and PR58 has been merged**. Work from current `main`. Inspect the live repository rather than relying on this prompt when there is any discrepancy.

## Core research question

We now have a candidate mathematical object involving:

```text
typed append-only history
Reflective Integrity replay
reason occurrences / reason multihypergraph
normative standing
authority
answerability/custody succession
prospective license
counterfactual record replay / excision
```

Carroll suggested that this may be more than an “internal integrity” component of legitimacy. The working hypothesis is:

> **Legitimacy is a modal property of an answerable normative history: legitimate authority may change substantially over time, but its changes must inherit authority through admissible, answerable, non-self-ratifying succession.**

The goal of this round is to determine whether that hypothesis can be compressed into a **Legitimate Evolution theorem whose output is strong enough to be consumed by the existing cross-process trust / deference / corrigibility program.**

This is the primary success criterion.

Do **not** optimize for philosophical elegance in isolation. Ask repeatedly:

> What exact mathematical fact would a different process need in order to defer to a future normative process whose conclusions it does not already endorse?

---

# 1. Read the actual mathematical substrate

Before proposing a theorem, inspect at minimum:

* the current Reflective Integrity core;
* the end-to-end legitimacy vertical slice;
* the inquiry return-loop round;
* the merged Carroll legitimacy round;
* the previous counterfactual legitimacy/interface rounds;
* relevant deference/trust/corrigibility material in the workspace;
* the current liability/traderization interface where it matters to downstream corrigibility.

Search broadly enough to recover the actual current vocabulary and open seams.

In particular establish the live definitions of:

```text
Standing
PAuth / PProto / PValue / other current payloads
NormEvent
schemaRef
ReasonOcc
AnsRoot / custody episode
succession
prospective_license
legitimate_succession
counterfactual replay / excision
provenance ancestry
current standing
```

Also inspect the existing deference target carefully enough to know what kind of premise it actually needs.

Do not silently design against an obsolete version of that work.

---

# 2. Start from the downstream consumer

The most important downstream use is roughly:

```text
current process A
    recognizes some present authority of process B

B changes through learning/reflection/delegation/value revision

legitimacy theory certifies B's later authority as a legitimate continuation

trust/deference theory lets A defer to B's later judgment

corrigibility theory shows A lacks incentive to preempt/disable/replace B
```

The legitimacy layer must therefore support **cross-process recognition of authority despite genuine content change**.

A theorem that merely says:

```text
every current standing has a valid internal history
```

is insufficient.

The target interface is closer to:

```text
Recognizes_A(x0)
and LegitimateEvolution_B(x0, x)
--------------------------------
Recognizes_A(x)
```

where `x0` and `x` may have substantially different normative content.

The round should determine whether `Recognizes` needs to be a primitive relation, a theorem-level assumption, a certificate-checking relation, or something else.

---

# 3. Distinguish the jobs of the theorem

Do not collapse these:

```text
internal RI admissibility
legitimate succession
answerability succession
prospective action license
current standing
cross-process recognition
epistemic trust
decision-theoretic deference
corrigibility
```

A desired modular decomposition is:

```text
LEGITIMACY:
    "this later authority is an entitled continuation of authority already recognized"

TRUST:
    "A appropriately anticipates / trusts what B will conclude"

DEFERENCE:
    "A treats B's conclusion as action-guiding"

CORRIGIBILITY:
    "A does not benefit from preventing the authoritative future choice"
```

Test whether this decomposition is actually mathematically coherent.

If legitimacy needs to absorb some part of trust or vice versa, say exactly why.

---

# 4. Try to formulate a legitimate-succession relation

Search for the smallest useful relation, provisionally something like:

```text
x ≺_L y
```

meaning that standing/authority `y` is a **legitimate immediate successor** of `x`.

Determine its actual type.

It may need to relate:

```text
StandingId × StandingId
NormEvent × StandingId
authority episodes
standing states
histories / prefixes
```

rather than merely two contents.

Candidate ingredients include:

* actual RI admissibility of the normative event;
* an appropriate predecessor/authority relation;
* answerability continuity;
* survival under the relevant challenged-history replay;
* independence of authority and applicability grounds from the challenged influence;
* faithful provenance assumptions.

Do not simply import the Carroll criterion wholesale. Derive what the succession relation needs from the intended theorem.

In particular distinguish:

```text
generic possession of authority
```

from

```text
this particular exercise of authority
```

since Carroll showed the former can survive manipulation while the latter does not.

---

# 5. Then define legitimate evolution

Investigate whether the right global object is the reflexive-transitive closure:

```text
x ≼_L y
```

of immediate legitimate succession, perhaps indexed by a history interval.

The ideal interpretation is:

> `y` is reachable from `x` through a finite chain of legitimately inherited normative authority.

Determine what has to be preserved along the chain:

* authority domain?
* principal?
* custody/answerability?
* protocol?
* nothing except an explicitly authorized transformation relation?

Do not force literal identity preservation if that would block delegation or genuine normative change.

---

# 6. Aim at an actual Legitimate Evolution theorem

Try to make a theorem with approximately this semantic content:

> Given a base of recognized legitimate authority, an RI-admissible history with faithful provenance and appropriately legitimate/answerable succession cannot generate current normative authority except through a finite legitimate lineage from that base; in particular, no current authority can acquire its legitimacy solely from the influence/exercise whose legitimacy it is used to establish.

Candidate theorem skeleton:

```text
LegitimateEvolution

assumptions:
  base legitimacy / recognized seed
  RI-good history
  provenance adequacy for challenged episodes
  every relevant authority-changing transition satisfies LegitSucc
  answerability continuity / appropriate custody succession
  prospective licenses satisfy anti-self-ratification

conclusion:
  every current legitimate authority-bearing standing x has
  a finite certificate

      x0 ≺_L x1 ≺_L ... ≺_L xn = x

  from some legitimate base x0.
```

Press whether this is actually substantive or merely true by recursive definition.

A bad result is:

```text
define Legitimate(x) := reachable by legitimate transitions
therefore every Legitimate(x) is reachable by legitimate transitions
```

The theorem must earn something.

Possibilities include:

* deriving lineage existence from local transition conditions;
* proving absence of self-ratifying cycles;
* proving preservation of an invariant;
* proving a global path property from step-local obligations;
* proving transport of recognition;
* proving a decomposition theorem between current standing and provenance.

Find the strongest non-tautological version the architecture supports.

---

# 7. Make anti-self-ratification theorem-shaped

Carroll suggests the central modal invariant is something like:

> An exercise cannot obtain the sole authority by which it is licensed from normative structure that exists only because of that exercise's challenged ancestry.

Try to formulate a global result rather than merely a fixture-level criterion.

Candidate shapes:

```text
NoBootstrap:

if x is used as the legitimating basis for intervention I,
then x (and the relevant applicability grounds) survive Challenge_I(H)
```

or:

```text
no legitimate lineage contains an edge whose sole legitimating basis
exists only downstream of the challenged influence represented by that edge.
```

Determine whether a well-founded grounding/dependence relation can express this more cleanly than repeated prose.

But do not introduce a new causal ontology unless it genuinely compresses the existing replay semantics.

---

# 8. Cross-process Recognition Transport is the key consumer theorem

Try hard to obtain a theorem/corollary of the form:

```text
RecognitionTransport

Recognizes_A(x0)
AcceptsLegitimacyRules_A(N)
x0 ≼_L x
--------------------------------
Recognizes_A(x)
```

The crucial requirement is:

```text
Recognizes_A(x) must NOT require Endorses_A(content(x)).
```

Otherwise it is not useful for deference.

Explicitly construct a witness in which:

```text
content(x0) != content(x)
```

perhaps radically,

while recognition transports.

Ideally the theorem should make clear what A has to recognize:

* the base authority;
* the legitimacy calculus;
* a certificate/verifier;
* relevant provenance/authentication assumptions.

If `RecognitionTransport` is not a mathematical theorem without adding a substantive axiom such as:

```text
A accepts legitimate succession as recognition-preserving
```

say so. Then isolate that assumption sharply.

Do not disguise a philosophical bridge principle as a derived theorem.

---

# 9. Design a consumer-facing legitimacy certificate

A downstream process should not have to replay the entire philosophical development.

Ask whether legitimate evolution should export a finite structured certificate, provisionally:

```text
LegitCert(x0, x)
```

containing enough information to verify:

* base authority;
* succession lineage;
* cited normative events;
* authority bases;
* answerability continuity;
* counterfactual survival / independence claims;
* provenance challenge used for each relevant edge.

Determine the minimal certificate interface.

A good interface might support:

```text
verifyLegit : History × LegitCert(x0,x) -> Bool/Prop
```

with a soundness theorem:

```text
verifyLegit(H,c)
-> x0 ≼_L x.
```

Do not overbuild an implementation. The point is to understand what information the downstream trust/deference layer must receive.

---

# 10. Explicitly test the theorem against the deference consumer

Locate the current cross-process trust/deference target and attempt to restate it using the legitimacy output.

The desired decomposition is approximately:

```text
Recognized legitimate authority
      +
epistemic trust / prediction
      +
decision-theoretic bridge
      =
deference / corrigibility consequence
```

Try to write an actual prospective theorem shape, e.g.:

```text
CorrigibleDeference

Recognizes_A(B_t, D)
LegitimateEvolution_B(t,t')
Trust_A(B_t' on D')
DecisionBridge(...)
--------------------------------
A has vanishing / bounded incentive to preempt, disable or replace
B_t' on the protected choice domain.
```

This need not be proved in this round.

But the round should determine **exactly which legitimacy fact appears as a hypothesis** of such a theorem.

If the current legitimacy proposal does not supply enough, identify the missing field/relation.

This is the round's most important negative test.

---

# 11. Test genuine reflective change

The legitimacy theorem fails the downstream use if it only preserves authority by preserving content.

Build/prove witnesses for:

### Non-lock-in

```text
x ≼_L y
and content(x) != content(y)
```

### Delegation

Authority legitimately moves to another principal/process.

### Revision

Earlier value/standing is legitimately superseded.

### Later independent adoption

An illegitimate influence produces value `v`, but later legitimate reflection independently installs the same `v`; the later standing is legitimate while the earlier intervention remains unlicensed.

### No temporal dictatorship

Initial/current/final position alone never determines legitimate authority.

These should be theorem-level desiderata or explicit model witnesses, not philosophical assurances.

---

# 12. Test bad transitions break recognition

We also need:

```text
causal succession != legitimate succession.
```

Build the sharpest examples showing:

```text
Recognizes_A(x)
and x -> y
```

does not imply:

```text
Recognizes_A(y).
```

Candidate breakers:

* manufactured authority;
* manipulated grounds;
* proxy laundering;
* provenance-incomplete influence;
* unanswerable transfer;
* illicit succession despite same endpoint.

The theorem should be permissive about genuine change but brittle to illegitimate change.

---

# 13. Work out answerability's exact role

Do not assume answerability belongs in Legitimate Evolution merely because it is central to the broader project.

Determine what theorem would fail without it.

Possible role:

> legitimate succession does not merely transfer discretion; it transfers an outstanding normative relation whose successor remains accountable for how inherited authority is revised or disposed.

Ask whether the theorem needs:

```text
authority succession
```

and

```text
answerability succession
```

as separate relations.

If yes, state what each contributes.

Look for a countermodel:

```text
all authority-transition conditions hold
but answerability continuity fails
```

and determine whether cross-process recognition should still transport.

This is important. We need to know whether answerability is constitutive of legitimacy or merely a useful audit mechanism.

---

# 14. Clarify the role of liability

Inspect the current liability/traderization theory and decide whether Legitimate Evolution itself should mention liability.

Candidate possibilities:

1. **No** — legitimacy identifies entitled authority; liability belongs to realization/corrigibility.
2. **Yes, weakly** — legitimate authority requires that inherited normative burden remains bounded/accounted for.
3. **Yes, centrally** — answerability/liability conservation is part of legitimate succession.

Do not choose based on conceptual symmetry.

Ask which version the downstream theorem actually consumes.

If a later process can inherit arbitrary unbounded normative liabilities and still count as legitimate, is that a problem for recognition/deference?

Record the answer explicitly.

---

# 15. Keep counterfactual semantics theorem-directed

Do not launch a general theory of counterfactual replay.

Ask only which properties of the challenge operator are required for:

```text
LegitSucc
LegitimateEvolution
NoBootstrap
RecognitionTransport
```

Current Carroll excision is a **record counterfactual**, not a world counterfactual.

Leave it that way unless a target theorem actually fails without world-counterfactual information.

In particular, do not demand:

```text
monotonicity
composition
SCM semantics
```

merely because they would be mathematically pleasant.

---

# 16. Separate primitive assumptions from derived structure

The round must explicitly classify every hypothesis as one of:

```text
architectural definition
theorem assumption
substantive normative assumption
provenance/authentication assumption
downstream recognition axiom
derived theorem
open seam
```

Especially audit:

```text
base legitimacy
covers
protocol conditions
fact semantics
provenance completeness
recognition of the base
acceptance of legitimacy rules by A
```

Do not hide the true substantive normative input inside a structural definition.

One possible outcome is that legitimacy is only definable **relative to a base recognition relation**. That is acceptable if made explicit.

---

# 17. Look for a minimal axiomatic spine

By the end, try to compress the theorem to the smallest hypotheses that actually do work.

Candidate local ingredients might be:

```text
A1 actual-history integrity
A2 legitimate authority inheritance
A3 answerability continuity
A4 challenge independence / no self-ratification
A5 provenance adequacy
```

But this list is provisional.

For every hypothesis you keep, provide:

```text
hypothesis
what conclusion uses it
smallest counterexample without it
```

If two assumptions do the same work, merge them.

If an assumption never enters a desired theorem, remove it from the core theorem.

---

# 18. Desired theorem family

Aim to leave theorem statements resembling the following, but change them when the mathematics demands it:

```text
T1 Immediate Succession Soundness

T2 Legitimate Evolution / Lineage Existence

T3 No Self-Ratifying Authority

T4 Non-Lock-In / Genuine Revision Witness

T5 Answerability Preservation

T6 Recognition Transport

T7 Consumer Interface for Cross-Process Deference
```

For each give:

* exact types;
* hypotheses;
* conclusion;
* whether currently proved, plausibly provable, test-supported, or only conjectured;
* proof idea;
* dependency on Carroll-specific machinery;
* downstream consumer.

Do not inflate the theorem list if several collapse into one clean result.

---

# 19. Most important failure conditions

The round should report failure rather than paper over any of these:

### Failure A — legitimacy is tautological

The proposed Legitimate Evolution theorem is merely a restatement of a recursively defined `Legitimate`.

### Failure B — recognition requires content agreement

If `A` can transport recognition only when it already endorses the future content, the theorem does not serve deference.

### Failure C — future authority is temporal dictatorship in disguise

If later standing wins because it is later, reject the theorem.

### Failure D — manipulation can inherit recognized authority

If Carroll-style laundering preserves the recognition chain, reject the theorem.

### Failure E — cross-process handoff is undefined

If the theorem only concerns one process's internal standings and gives no principled relation another process could consume, the round has not succeeded.

### Failure F — answerability is ceremonial

If answerability is included but no theorem uses it, say so and remove it from the central statement.

### Failure G — legitimacy absorbs competence

Do not require truth, optimality, convergence, epistemic adequacy, or agreement unless a theorem genuinely needs them.

---

# 20. Deliverables

Create an isolated round directory with at minimum:

```text
README.md
LEGITIMATE_EVOLUTION.md
CROSS_PROCESS_INTERFACE.md
THEOREM_MAP.md
COUNTERMODELS.md
CONSUMER_TEST.md
```

Optional executable reference models/tests are welcome if they sharpen distinctions, but this is a mathematical theorem-design round, not a request to produce a large Python fixture suite.

`LEGITIMATE_EVOLUTION.md` should contain the clean mathematical theory.

`CROSS_PROCESS_INTERFACE.md` should state exactly what process A receives and what it is entitled to infer about process B.

`CONSUMER_TEST.md` should take the actual current trust/deference/corrigibility target and attempt to plug the proposed legitimacy theorem into it.

`COUNTERMODELS.md` should prosecute every major hypothesis.

`THEOREM_MAP.md` should be brutally honest about theorem status.

---

# 21. Verdicts

End with exactly one of:

```text
LEGITIMATE-EVOLUTION-CONSUMABLE
```

if there is a coherent theorem/interface under which cross-process trust/deference/corrigibility can genuinely consume legitimacy without content agreement;

```text
LEGITIMATE-EVOLUTION-INTERNAL-ONLY
```

if the architecture yields a meaningful internal legitimacy theory but no principled cross-process recognition transport;

```text
LEGITIMATE-EVOLUTION-NOT-YET-WELL-POSED
```

if essential types/relations are still missing.

Do not use the first verdict merely because a suggestive story exists.

---

# Final report

End by answering these questions directly:

1. What is the exact type of immediate legitimate succession?
2. What is the exact type of legitimate evolution?
3. What non-tautological global theorem follows from the local conditions?
4. What prevents self-ratifying authority?
5. Can legitimate authority survive genuine normative content change?
6. What does answerability add that authority succession alone does not?
7. What is the minimum certificate another process needs?
8. What assumption lets recognition transport from (A)'s accepted base authority to (B)'s later authority?
9. Does that assumption amount to a substantive philosophical axiom, and if so what exactly is it?
10. Can the current cross-process trust/deference theorem consume this interface?
11. What would the resulting corrigibility theorem approximately say?
12. Which parts remain Carroll-specific and should disappear in later consolidation?
13. Which primitive normative seams remain (`covers`, conditions, base authority, etc.)?
14. What is the strongest counterexample to the proposed theorem?
15. Should the next round refine the counterfactual semantics, or is the theory ready for aggressive canonical consolidation?

The central standard is:

> **A future process must be able to reach a normative conclusion the present process does not endorse, while the present process nevertheless has a mathematically intelligible reason to continue recognizing the future process's authority — and that recognition must break under illicit manipulation rather than blindly tracking causal succession.**

If the proposed theorem accomplishes that, the round has found the legitimacy interface we need.

---

---

# ADDENDUM — THE HEADLINE THEOREM MUST BE IMPLEMENTATION-INDEPENDENT

*Sent while the round was running, before any prose had been written.*

A further requirement has become central while this round is running.

**Do not make the headline Legitimate Evolution theorem a theorem specifically about Reflective Integrity, `NormEvent`, `ReasonOcc`, `PAuth`, `AnsRoot`, Carroll `excise`, or any other internal architectural representation.**

Those objects may be essential for proving that *our architecture instantiates the theorem's hypotheses*. They should not, if avoidable, appear in the statement that an external process must satisfy in order for the cross-process deference work to consume the result.

The desired architecture is now:

```text
ABSTRACT LEGITIMACY INTERFACE
         |
         |  implementation-independent theorem
         v
LEGITIMATE EVOLUTION / RECOGNITION TRANSPORT

---------------- realization boundary ----------------

RI + reason history + standing replay
+ answerability + counterfactual replay
         |
         |  realization theorem
         v
satisfies ABSTRACT LEGITIMACY INTERFACE
```

This separation is a major success criterion of the round.

---

### A. Ask what an external object would have to expose

Imagine that the future human-guided process (B) **does not run our implementation at all**.

It may be:

* another agent architecture;
* an institution;
* a mathematical deliberation process;
* a proof-producing reasoner;
* a black-box process accompanied by auditable certificates;
* a future alignment formalism developed independently of this repository.

We still want to be able to prove that its later authority is a legitimate continuation of authority currently recognized by (A).

Therefore ask:

> What is the weakest externally meaningful interface (B) could satisfy which is sufficient for Legitimate Evolution and Recognition Transport?

Do not answer by requiring (B) to implement our ledgers.

---

### B. Search for the abstract mathematical structure first

A candidate shape might contain objects such as:

```text
Authority        -- whatever may legitimately govern some domain
Transition       -- a proposed change/exercise of authority
Challenge        -- the intervention/capture whose dependence is being tested
Certificate      -- evidence that a transition satisfies the interface
Carries          -- answerability/accountability continuity, if needed
Covers           -- domain of authority, or an abstraction of it
```

and relations provisionally like:

```text
CurrentAuth_t(x)

Succ(x, c, y)
    c certifies an immediate authority succession from x to y

Grounded(c, X)
    the transition's legitimating basis comes from X

Stable(c, q)
    the relevant legitimating basis remains valid under challenge q

Carries(x, y, λ)
    y inherits the relevant outstanding accountability structure from x
```

These names are provisional. Find cleaner mathematics if possible.

The key requirement is that these notions have **semantic interpretations outside our architecture**.

For example:

* our `NormEvent` may *witness* an abstract succession transition;
* our Carroll replay may *witness* abstract challenge stability;
* our `AnsRoot` lineage may *witness* abstract answerability continuity.

They should not automatically be the abstract notions themselves.

---

### C. Avoid two opposite abstraction failures

#### Too concrete

Bad headline theorem:

```text
If every NormEvent has an active PAuth schemaRef,
every AnsRoot succeeds correctly,
and excise(H,E) preserves ...
then ...
```

That is a theorem about our software architecture. It may be a useful **realization theorem**, but it is not yet the cross-process legitimacy theorem we want.

#### Too abstract

Equally bad:

```text
Assume every transition is legitimate.
Then legitimate authority is preserved.
```

or:

```text
Assume recognition-preserving succession.
Then recognition is preserved.
```

These simply rename the conclusion.

The abstract premises must be independently intelligible and must constrain external objects in ways that can be falsified.

A good test is:

> Could a system satisfy each premise without using any of our internal representations, while still being possible to construct a counterexample system that violates that premise?

---

### D. Try for an abstract local-to-global theorem

A particularly attractive shape is:

Let (G) be a set of base authorities already recognized by an external process.

Suppose an evolving process exposes a finite local succession relation

[
X \xRightarrow[c]{} y
]

where (X) is a finite collection of prior authorities and (c) is a certificate satisfying a small abstract legitimacy interface.

Define a derivability relation

[
G \vdash y
]

by finite trees / DAGs of such certified local successions.

Then aim for a theorem whose nontrivial content is something like:

> Local satisfaction of the legitimacy interface along an execution implies that every currently authoritative object has a finite derivation from the recognized base, with no authority edge bootstrapped solely from the challenged exercise that it legitimates.

Importantly, the theorem should be able to apply whether the certificates were produced by:

```text
RI replay
a proof assistant
an institutional audit procedure
another agent architecture
another formal legitimacy model
```

---

### E. Separate the abstract theorem from the realization theorem

Try to produce **two theorem families**.

#### 1. Abstract Legitimate Evolution

Stated without our internal architecture.

It should derive some combination of:

```text
finite legitimate lineage
no ex nihilo authority
no self-ratifying authority
genuine content-changing revision is possible
delegation is possible
recognition can be transported along certified succession
```

#### 2. RI Realization

Then prove or argue:

```text
Reflective Integrity
+ standing replay
+ reason provenance
+ answerability succession
+ Carroll-style challenged replay

instantiate the abstract hypotheses.
```

This second theorem is where internal objects are welcome.

Ideally there should be a clear interpretation map such as:

```text
abstract Authority          <- relevant RI standing/episode
abstract Succession         <- certified NormEvent transition
abstract Challenge          <- challenged influence ancestry
abstract Stability          <- survival under replay
abstract Accountability     <- answerability succession
abstract Certificate        <- finite RI/provenance witness
```

Do not force these exact correspondences if a better abstraction appears.

---

### F. Recognition Transport must quantify over external implementations

The downstream theorem we ultimately want should look more like:

[
\operatorname{Recognizes}_A(G)
\land
B\models\mathsf{LegitimacyInterface}
\land
G\vdash_B y
\Longrightarrow
\operatorname{Recognizes}_A(y),
]

not:

[
A\text{ recognizes }B\text{ because }B\text{ has our specific ledger fields}.
]

The recognition result must still permit:

[
content(g)\neq content(y).
]

An implementation-independent theorem is especially valuable here because the intended deference target (H^+) should **not have to literally implement our normative architecture** to qualify as legitimately evolving.

We may instead prove separately that some model of (H^+) satisfies the abstract legitimacy interface.

---

### G. Treat “recognition preserves certified succession” carefully

There is a danger that Recognition Transport becomes tautological if we simply assume:

```text
A recognizes every legitimate successor.
```

Try to isolate the smallest genuine bridge principle.

For example, the external process (A) might:

1. recognize a base authority (G);
2. recognize a public verifier (V);
3. accept a rule of the form:

[
V(c,x,y)=\mathrm{true}
\Rightarrow
\text{authority recognized at }x\text{ is inherited by }y.
]

If such a bridge is irreducibly substantive, call it a **recognition axiom** and say so.

The mathematics should then tell us as much as possible about what (V) must verify, rather than burying the whole legitimacy judgment inside (V).

A useful decomposition may be:

```text
mathematical theorem:
    certificate satisfies externally stated structural properties

substantive bridge:
    A regards those properties as recognition-preserving

conclusion:
    recognition transports without content endorsement
```

This is acceptable. Do not claim that mathematics derives the substantive bridge from nothing.

---

### H. Consumer test: pretend RI does not exist

Add a strong negative test to `CONSUMER_TEST.md`:

> Restate the proposed cross-process deference/corrigibility theorem while treating the future process (B) as an arbitrary external object satisfying only the abstract legitimacy interface.

Ask:

```text
Can the consumer theorem still be stated?
Can the legitimacy premise still be checked/proved in principle?
Does A need to know B's internal representation?
Does A need to endorse B's future normative content?
```

Desired answers:

```text
yes
yes
no
no
```

If the theorem becomes meaningless when the words `NormEvent`, `AnsRoot`, or `ReasonOcc` are removed, the abstraction has not succeeded.

---

### I. This may alter what “nice mathematical shape” means

Prefer a theorem whose statement has the form:

[
\boxed{
\text{Any process satisfying axioms }L_1,\ldots,L_k
\text{ supports legitimate evolution and recognition transport.}
}
]

followed by:

[
\boxed{
\text{Our event-sourced architecture satisfies }L_1,\ldots,L_k.
}
]

This is substantially better than one large theorem whose hypotheses expose every internal implementation choice.

If possible, identify a **minimal abstract axiomatic spine**. Candidate concepts include:

```text
grounded succession
challenge independence
answerability continuity
no ex nihilo authority
```

but these are suggestions rather than required names.

For each abstract axiom provide:

* a semantic English reading;
* its exact mathematical type;
* a system satisfying it without RI, if one can be easily exhibited;
* an RI realization;
* a counterexample showing why the global theorem fails without it;
* the downstream theorem clause that consumes it.

---

### J. New success criterion

Upgrade the standard for:

```text
LEGITIMATE-EVOLUTION-CONSUMABLE
```

It now requires both:

1. an implementation-neutral legitimacy theorem / interface that an external process could satisfy without implementing RI;
2. a realization argument showing our architecture is one implementation of that interface.

A particularly strong success would be:

> The headline theorem and Recognition Transport corollary can be understood and applied by a mathematician who never learns the internal RI vocabulary; RI then appears in a separate representation/realization theorem.

If this cannot be achieved without making the abstract theorem vacuous, report that. Understanding why implementation independence fails would itself be an important result.

---

### K. Add these questions to the final report

In addition to the existing final questions, answer:

16. What is the minimal implementation-independent legitimacy interface?
17. Which of its notions are genuinely semantic and which are merely renamed RI concepts?
18. Can an external process satisfy the interface without possessing a ledger isomorphic to ours?
19. What is the realization map from RI into the abstract interface?
20. Which conclusions belong to the abstract theorem and which only to the RI realization?
21. Can the cross-process deference theorem quantify over arbitrary implementations satisfying the interface?
22. What is the irreducible recognition axiom, if any?
23. Does recognition transport remain content-independent?
24. Is the abstraction strong enough to reject Carroll-style laundering without mentioning Carroll-specific objects?

The new guiding test is:

[
\boxed{
\text{Our architecture should witness legitimacy, not define the only way legitimacy can exist.}
}
]

The downstream goal is to be able to say:

> **Whatever future process (B) is internally, if it satisfies this externally stated legitimacy interface, then authority presently recognized by (A) can be transported through (B)'s genuine reflective change in exactly the sense needed by the trust/deference/corrigibility theorem.**

Press hard on whether that sentence can actually be made mathematical.

---

---

# REPAIR PASS — HOSTILE TO THE ABSTRACT THEOREM ITSELF

*Dispatched after the first pass shipped and was reviewed.*

You are doing a **pressing and repair pass on the legitimate-evolution theorem round** in `A-M-Berns/alignment-workspace`.

Work from the live branch:

```text
round/2026-08-25-legitimate-evolution
```

At dispatch time it was one commit ahead of `main` and had verdict:

```text
LEGITIMATE-EVOLUTION-CONSUMABLE
```

Do not trust that verdict.

The previous pass successfully produced an implementation-independent succession frame, a Reflective Integrity realization, a second warrant/appointment realization, and a deference consumer test. But review has identified several potentially central defects and missing consumer requirements.

**This pass is about prosecuting and repairing the abstract mathematics before any Lean port or canonical consolidation.**

Do not port to Lean in this pass.

Do not broaden Reflective Integrity.

Do not preserve current notation merely because it already exists.

The intended successful endpoint is:

```text
a repaired, two-consumer, implementation-independent legitimacy theorem spine
```

strong enough to justify a later Lean formalization.

---

# 1. Read the live round and its consumers first

Read at minimum:

```text
projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/
  README.md
  LEGITIMATE_EVOLUTION.md
  CROSS_PROCESS_INTERFACE.md
  CONSUMER_TEST.md
  COUNTERMODELS.md
  THEOREM_MAP.md
  src/frame.py
  src/ri_frame.py
  src/warrant.py
  src/cases.py
  tests/test_frame.py
```

Also inspect the live relevant source material for:

```text
Reflective Integrity
Carroll challenge/excision
DelegationBridge.lean
FUTURE_AGENT_SPEC.md
ReachableCorrectiveControl.lean
traderized enforcement
bounded-lifetime liability / answerability accounting
ForceRequest
liability allowance / grant channel
```

Use the live repository rather than the prompt wherever they differ.

---

# 2. First attack: the license itself is currently not required to be legitimately derived

The present derivability rule is approximately:

```text
G |-_q y
```

if either `y ∈ G`, or there exists an exercise `t` such that:

```text
src(t) ⊆ Derivable_q
y ∈ tgt(t)
q |= lic(t)
q |= t
```

The likely defect is:

```text
lic(t)
```

need only be **stable**, not itself **legitimately derivable from G**.

Prosecute this explicitly.

Construct the smallest abstract countermodel of the following shape:

```text
g ∈ G

challenged exercise r:
    consumes legitimate structure
    issues z
    r does not survive q
    z therefore does not survive / is not derivable

later exercise s:
    somehow issues m from or through z
    m is stable under q
    m is NOT legitimately derivable from G

exercise t:
    src(t) is legitimate
    lic(t) = m
    t survives q
    t issues y
```

Test whether the current definition derives:

```text
G |-_q y
```

despite `m` not being legitimately grounded in `G`.

Also test the current proof of T3:

> every authority in the provenance of a certified authority is free of challenged issuance.

`provenance` currently follows both:

```text
src
lic
```

while `derivable` may recurse only through `src`.

If so, identify the exact invalid proof step.

The suspected repair is:

```text
src(t) ∪ {lic(t)} ⊆ Derivable_q
```

rather than merely:

```text
src(t) ⊆ Derivable_q
and q |= lic(t)
```

But do not force that repair if a cleaner distinction appears.

**Required outcome:** either prove the current rule is sound, or ship the smallest counterexample and repair the derivability judgment.

Re-run every theorem after the repair.

---

# 3. Distinguish stability from legitimate grounding

This pass must make the following distinction explicit:

```text
q |= x
```

means roughly:

> `x` survives the challenge.

It must not silently mean:

> `x` has legitimate authority relative to G.

Test and document:

```text
Stable_q(x)  does NOT imply  G |-_q x.
```

We actively need stable-but-illegitimate objects as negative cases.

If the repaired derivability relation correctly refuses exercises licensed by such objects, preserve that as a theorem/countermodel.

This is central to cross-process recognition:

> A recognizer should not inherit authority merely because the authority survived the counterfactual.

---

# 4. Second attack: unique issuance is claimed optional but is used by the implementation

The current theory says:

```text
L2' unique issuance
```

buys only **canonicity**.

But inspect:

```text
minted_by
provenance
L3'
T2
T3
```

`minted_by` currently appears to raise when there is more than one issuer.

Prosecute the claim:

```text
T2 lineage existence requires only L1 + L2
```

independently of L2'.

The mathematically desired separation is likely:

### Without unique issuance

```text
every authority has at least one finite well-founded lineage to G
```

perhaps with a choice of issuer at branching origin points.

### With unique issuance

```text
the provenance DAG is canonical / determined by the target
```

Do not allow the reference implementation to smuggle uniqueness into the existential theorem.

Repair the code and statements so that:

```text
L2' really is optional
```

if the mathematics permits it.

If T3 genuinely requires unique issuance, say so and explain why rather than retaining the current claim.

Add a multiple-issuer realization/countermodel that decides the issue.

---

# 5. Third attack: `NormEvent` identity may be too coarse for abstract exercise identity

The current RI realization needs:

```text
pre-state-blindness
```

to establish L3:

```text
q |= t  ->  y ∈ tgt(t) -> q |= y.
```

The Carroll C28 witness is:

```text
the same event id survives replay
but its schema sees a different strict pre-state
and therefore produces a different payload.
```

Do not immediately conclude that Reflective Integrity must globally restrict practical schemas to pre-state-blind ones.

Prosecute the **realization map itself**.

Ask whether the abstract notion:

```text
exercise : T
```

should correspond to:

```text
NormEvent id
```

or instead something semantically richer, for example:

```text
(NormEvent, frozen effect)
(NormEvent, Digest)
authority-changing act token
event-with-output
```

or another object.

The semantic intuition to test is:

> If the same event id is replayed but produces a different authority-changing effect, did the same legitimacy-relevant exercise really survive?

Try a stability semantics where:

```text
q |= t
```

means the **same exercise/effect** survives, rather than merely the event id being admitted.

Then ask:

1. Does L3 become unconditional?
2. Does C28 remain correctly diagnosed?
3. Does L3' still hold?
4. Does the new exercise identity break other realizations?
5. Does it make the abstract notion more semantically intelligible for external systems?

Compare at least:

```text
event-id exercise identity
effect-sensitive exercise identity
```

Do not choose the latter merely to remove a hypothesis. Choose the abstraction with the best external semantics.

The goal is to learn whether:

```text
pre-state-blindness is genuinely a legitimacy requirement
```

or merely:

```text
a consequence of an overly coarse RI realization map.
```

---

# 6. Fourth attack: provenance/challenge coverage must become a first-class input interface

The current frame has:

```text
Q
Chal : Q -> Pfin(T)
q |= u
```

but a process with a nearly empty challenge set can satisfy all structural axioms.

The current round itself calls this the largest hole.

Do not leave it as a prose caveat.

Introduce/propose the narrowest abstract **provenance adequacy / challenge coverage interface** required by the legitimacy theorem.

Candidate shape:

```text
Depends(q,t)
```

meaning:

> exercise `t` is in the relevant dependence cone of influence/challenge `q`.

with a law such as:

```text
Depends(q,t) -> t ∈ Chal(q)
```

or perhaps:

```text
TrueInfluence(q,t) -> represented_dependency(q,t)
```

if two levels are required.

Avoid pretending to solve world causation.

It is acceptable to state legitimacy **relative to a supplied threat/dependence class**:

```text
Coverage_Ξ(Chal)
```

for some externally specified `Ξ`.

The critical requirement is:

```text
Q = ∅
```

or:

```text
Chal(q) = ∅ for every q
```

must not automatically certify a system against a nonempty threat model.

Separate:

```text
form of challenge reasoning
```

from:

```text
adequacy of challenge coverage.
```

Add a theorem/countermodel showing exactly what global legitimacy guarantee depends on coverage.

---

# 7. Fifth attack: `src` may conflate historical targets with legitimacy parents

Current certified derivability requires:

```text
all of src(t)
```

to be legitimately derivable.

The warrant merge countermodel was used to choose "all-of-src" over "one-of-src."

Press whether the type itself is doing two jobs.

Distinguish conceptually:

```text
affected(t) / consumed(t)
```

— the positions the exercise acts on, supersedes, revokes, merges, etc.

from:

```text
grounds(t) / legitimacyParents(t)
```

— the prior authorities from which the successor's entitlement is inherited.

and separately:

```text
lic(t)
```

— the warrant under which the exercise is performed.

These may coincide in some systems and differ in others.

Important test:

> A legitimate authority cleans up, revokes, or supersedes an illegitimate standing. Must the successor become illegitimate merely because the illegitimate standing was among the objects acted on?

Build the smallest external register deciding this.

Do not preserve `src` as the legitimacy-parent relation merely because Reflective Integrity's `Supersede X` exposes a target set.

If the correct interface needs:

```text
affected : T -> Pfin(A)
parents  : T -> Pfin(A)
lic      : T -> A
```

split them.

If all-of-`src` remains correct, give the semantic argument and countermodel showing why.

---

# 8. Reconstruct the abstract theorem only after those repairs

After §§2–7, rewrite the minimal abstract frame from scratch.

Do not patch the old theorem statement incrementally if the ontology has changed.

The desired shape is still something like:

```text
lifecycle/evolution interface
prior-authority / grounding interface
provenance + challenge interface
optional accountability interface
base recognition / threat model
```

implying a global legitimacy structure.

Try to minimize the spine.

For every remaining axiom state:

```text
exact mathematical type
semantic English reading
theorem that uses it
smallest countermodel without it
RI realization
warrant/institution realization
```

Explicitly mark:

```text
architectural structure
structural assumption
substantive normative axiom
provenance/threat-model assumption
consumer-side recognition axiom
derived theorem
```

---

# 9. The conclusion should now be a time-indexed legitimacy interface, not merely `G |- y`

The current theorem is primarily about authority provenance.

The downstream traderization consumer needs more:

> Which norms are legitimately in force throughout which intervals?

Add a genuine lifecycle/frontier component.

Introduce the smallest sensible abstraction of:

```text
Live_t(x)
```

or:

```text
Frontier_t ⊆ A
```

where this is an externally supplied lifecycle view, not Reflective Integrity's `Std_t`.

Aim to derive/provide a **legitimate live frontier**:

```text
F^leg_t
```

satisfying at least:

### Groundedness

```text
x ∈ F^leg_t  ->  G |- x
```

under the relevant challenges/threat model.

### Legitimate entry

```text
x enters F^leg
->
x enters through certified legitimate succession
```

except for base elements.

### Persistence

```text
x ∈ F^leg_s
and no legitimate disposing/superseding transition on [s,t]
->
x ∈ F^leg_t
```

### Legitimate exit

An authority/norm leaves the legitimate frontier only through the lifecycle interface's legitimate disposition semantics.

### Revisability

Successors may differ arbitrarily in content.

### No bootstrap

Every legitimacy-grounding dependency of a frontier element is clean against the relevant challenge class.

Do not make persistence mean:

```text
once legitimate, always legitimate.
```

The target is:

```text
persistent until legitimately changed.
```

---

# 10. Keep authority and norm projections separate

The legitimacy output should be rich enough to expose two consumer views:

```text
AuthorityView_t
NormView_t
```

They may be projections of one live legitimate frontier.

The abstract legitimacy theorem should not know anything about Logical Induction or prices.

The norm projection needs only enough structure that a downstream interpreter can map:

```text
norm n at time t  ->  constraint K^n_t
```

The authority projection needs only enough structure that an external recognizer can say:

```text
this later authority is a legitimate descendant of a base I recognize.
```

---

# 11. Re-run the deference consumer test on the repaired interface

Return to:

```text
DelegationBridge.lean
FUTURE_AGENT_SPEC.md
```

and restate the consumer theorem against the repaired interface.

Preserve the useful discovery that the existing grade:

```text
W : C -> P -> Q
```

carries no authority/process index.

Prosecute the proposed repair:

```text
W : Authority -> C -> P -> Q
```

or whatever the repaired interface demands.

The core question remains:

> Does legitimacy make the future grade/judgment a proposition selected by legitimately inherited authority rather than by the advisor/manipulator?

The deference consumer must still work when:

```text
content(future authority) != content(base authority)
```

and must break on laundering.

Do not require the consumer to know:

```text
NormEvent
ReasonOcc
AnsRoot
```

or any RI implementation type.

---

# 12. Add a second full consumer test: traderization / bounded-lifetime liability

This is new and important.

Inspect the live traderized-enforcement and answerability/liability work.

The consumer question is:

> Can the same legitimacy interface identify exactly which norms are entitled to continued enforcement, so that bounded-lifetime-liability theorems can guarantee enforcement throughout their legitimate lifetime?

Write a prospective theorem shape like:

```text
PersistentLegitimateEnforcement

L : LegitimacyInterface
n ∈ LegitimatelyLive_t over its legitimate lifetime
interpret(n,t) = K^n_t
appropriate feasibility / geometry hypotheses
bounded-lifetime-liability hypotheses
--------------------------------------------------------
the enforcement mechanism satisfies K^leg_t
throughout the legitimate lifetime
```

where:

```text
K^leg_t = intersection of K^n_t over legitimately live norms n.
```

The exact theorem may use approximate enforcement:

```text
dist(P_t, K^leg_t) <= eps_t
```

if that matches the actual traderization result.

Do not invent liability mathematics the repository does not have.

Instead identify:

1. what the legitimacy interface must export;
2. what the current liability theory already supplies;
3. what exact additional bounded-lifetime-liability theorem remains open.

The key target is:

```text
indefinitely enforceable while legitimately live
```

not:

```text
once legitimate, enforced forever.
```

If a norm is legitimately superseded, the enforcement target must move.

---

# 13. Press the interaction between legitimate succession and liability succession

The current round concluded that answerability is not constitutive of authority recognition.

Do not reverse that without evidence.

But the traderization consumer may need more than authority recognition.

Investigate whether there should be:

```text
Legitimacy
```

plus a separate:

```text
Serviceable / Accountable / LiabilityContinuity
```

interface.

Candidate picture:

```text
legitimate authority
    = entitled

answerability continuity
    = accountable

bounded lifetime liability
    = sustainably enforceable
```

Determine which conclusions require which.

In particular:

```text
can a legitimately live norm carry an unbounded enforcement burden?
```

If yes, legitimacy should still call it legitimate while traderization refuses to promise enforcement.

That modularity would be useful.

---

# 14. Target theorem family after repair

Try to end with a small family resembling:

```text
T1  Finite / well-founded provenance

T2  Legitimate Grounding
    every legitimate-live authority has a certified derivation from G

T3  Global No-Bootstrap
    no legitimacy dependency at any depth is generated by the challenged
    influence under the stated coverage hypothesis

T4  Content Independence / Genuine Revision

T5  Legitimate Frontier Persistence
    legitimate objects persist until legitimate disposition

T6  Recognition Consumer Corollary
    under explicit recognition axiom R

T7  Norm-Lifecycle Consumer Interface
    sufficient input for persistent traderized enforcement

T8  Optional Answerability / Continuity theorem
```

The exact numbering and factorization may differ.

Do not retain a theorem merely to preserve the old map.

---

# 15. Required countermodels

By the end there must be explicit models for at least:

1. **Stable but illegitimate license.**
   A stable authority not derivable from `G` attempts to license a successor.

2. **Multiple issuance.**
   Decide whether existence and canonicity really separate.

3. **C28 under two exercise identities.**
   Event-id versus effect-sensitive survival.

4. **Challenge undercoverage.**
   A structurally perfect frame with inadequate `Chal`.

5. **Legitimate cleanup of illegitimate standing.**
   Decide whether all affected predecessors must be legitimacy parents.

6. **Content-changing legitimate succession.**

7. **Legitimate norm persistence and legitimate supersession.**

8. **Legitimate but financially unenforceable norm.**
   Demonstrate the distinction between legitimacy and bounded-liability serviceability if the current theory permits it.

---

# 16. Failure conditions

Use a negative verdict if any of these survive:

### A. Stable authority can substitute for legitimately grounded authority

If an exercise can inherit recognition from a stable-but-illegitimate `lic`, the spine is broken.

### B. T3 proof still assumes every provenance ancestor is derivable when the rule does not ensure this

Do not patch prose around this.

### C. L2' remains secretly required by "L1+L2" theorems

Fix the theorem or fix the implementation.

### D. The RI realization imposes pre-state-blindness only because exercise identity is too coarse

Decide this before treating pre-state-blindness as a canonical assumption.

### E. Empty challenge coverage still yields full legitimacy against a nonempty threat model

Coverage must be explicit somewhere.

### F. The abstract theory cannot tell what remains legitimately live through time

Then it is insufficient for the traderization consumer.

### G. The theorem only works for deference or only for enforcement

The goal is one legitimacy output with two projections.

### H. `src` is used as legitimacy ancestry merely because of the RI representation

Separate historical affectedness from legitimating inheritance if the countermodels demand it.

---

# 17. Deliverables

Update the existing round rather than creating a completely unrelated theory directory.

At minimum revise:

```text
LEGITIMATE_EVOLUTION.md
CROSS_PROCESS_INTERFACE.md
CONSUMER_TEST.md
COUNTERMODELS.md
THEOREM_MAP.md
README.md
src/frame.py
src/ri_frame.py
src/warrant.py
tests/test_frame.py
```

Add:

```text
TRADERIZATION_CONSUMER.md
```

or an equivalently clear consumer document.

If the interface changes substantially, prefer rewriting the abstract layer cleanly to preserving backwards compatibility with provisional names.

---

# 18. Do not port to Lean yet

The previous round recommended a Lean port next.

**Do not do that in this pass.**

The abstract theorem currently has at least one suspected proof defect and several unsettled type boundaries.

The output of this pass should answer:

```text
Is there now a stable enough abstract theorem to formalize?
```

not formalize it.

---

# 19. Verdicts

End with exactly one of:

```text
LEGITIMATE-EVOLUTION-TWO-CONSUMER-READY
```

if:

* the license-grounding defect is repaired;
* the no-bootstrap theorem is actually valid;
* existential versus canonical lineage is clean;
* challenge coverage is an explicit hypothesis/interface;
* exercise identity has been prosecuted;
* the theorem exports a legitimate-live lifecycle/frontier;
* both deference and traderization can consume the result without RI internals.

```text
LEGITIMATE-EVOLUTION-REPAIRABLE-BUT-NOT-STABLE
```

if the abstraction remains promising but one of those points is unresolved.

```text
LEGITIMATE-EVOLUTION-SPINE-FAILS
```

if the current local-to-global idea cannot survive the attacks without becoming tautological or architecture-specific.

---

# 20. Final report

Answer directly:

1. Was the stable-but-illegitimate-license counterexample valid?
2. What is the repaired exact definition of certified derivability?
3. Are licenses recursively required to be legitimately grounded?
4. What is the exact role of `src` after prosecution: affected objects, legitimacy parents, or both?
5. Does T3 now actually follow from its stated hypotheses?
6. Does lineage existence require unique issuance?
7. What exactly does unique issuance buy?
8. What is the right abstract identity of an exercise?
9. Does the RI realization still require pre-state-blind schemas?
10. What is the explicit provenance/challenge coverage hypothesis?
11. Against what threat/dependence class is the legitimacy theorem relative?
12. What is the time-indexed legitimate frontier/lifecycle object?
13. What theorem gives "persistent until legitimately changed"?
14. What does the deference consumer receive?
15. What does the traderization consumer receive?
16. Which additional bounded-lifetime-liability theorem would yield persistent enforcement?
17. Is answerability part of legitimacy, or a separate consumer-visible refinement?
18. Can a norm be legitimate but unenforceable because of unbounded liability?
19. Can both consumers quantify over external implementations without RI vocabulary?
20. Is the abstract theory now stable enough for a Lean port?

The central standard for this pass is:

> **A legitimately evolving process must propagate authority only from legitimately grounded authority, must remain robust to the relevant challenged influences under an explicit coverage assumption, must permit genuine content change, and must expose a time-indexed "legitimately live" object that one consumer can recognize and another can enforce.**

And the architectural standard is:

> **Reflective Integrity should be one realization of these hypotheses; deference and traderization should consume only their conclusions.**

Do not preserve the previous verdict if the mathematics does not earn it.

---

---

# COMPRESSION PASS — HOSTILE TO THE ABSTRACT THEOREM ITSELF

*Dispatched after the repair pass shipped and was reviewed.*

You are doing a **theorem-compression prosecution pass** on the live legitimacy branch:

```text
round/2026-08-25-legitimate-evolution
```

The current branch has already repaired several real defects:

* licences must themselves be recursively derivable, not merely challenge-stable;
* `affected` is separated from legitimacy `parents`;
* unique issuance is optional;
* no-bootstrap is stated over a derivation rather than route-blind provenance;
* challenge coverage is now an explicit typed hypothesis;
* a lifecycle/frontier and two consumer projections were added;
* traderization is now a second consumer;
* the current verdict is `LEGITIMATE-EVOLUTION-TWO-CONSUMER-READY`.

Do **not** trust that verdict as final.

This pass asks whether the current succession/challenge theorem can be compressed into a stronger and more semantically correct theorem about **legitimate replay, no laundering, and hidden-state noninterference**.

Do not Lean-port in this pass. Do not preserve the current L0-L8 spine merely because it now passes its tests. Do not preserve `F^leg = live ∩ Derivable` if a better semantic object is required.

The target is the **shortest implementation-independent theorem whose local hypotheses genuinely imply the global legitimacy properties needed by both deference and persistent enforcement**.

# 1. Read the repaired round first

Read the round's seven documents and five modules. Also inspect the current live material for Carroll legitimacy/excision, Reflective Integrity Core, the inquiry return loop, the answerability scout, `DelegationBridge.lean`, `ReachableCorrectiveControl.lean` and traderized enforcement. Use live repository contents over this prompt where they differ.

# 2. First attack: `F^leg = live ∩ Derivable` may not mean "persistent until legitimately changed"

Prosecute: `n` is legitimately live; an attacker performs an illegitimate exercise `r`; `r` revokes or supersedes `n` in the raw lifecycle; `n` therefore leaves raw `live[s]`. Does `n` now leave `F^leg` merely because `F^leg = raw_live ∩ derivable`, even though no **legitimate** transition disposed it?

If yes, the current theorem establishes only *persistent until something in the raw process changes it*, which is too weak for the traderization consumer.

**Required countermodel:** a legitimately live norm subjected to an illegitimate raw revocation. Determine the expected enforcement target before and after the attack.

# 3. Prosecute a derived legitimate replay instead

Try replacing `F^leg = raw_live ∩ Derivable` with a separately reconstructed legitimate state:

```text
L_0 = G
L_{s+1} = apply(L_s, e_s)  if Valid(L_s, e_s, c_s)
          L_s              otherwise
```

Prosecute whether this yields: illegitimate creation is a no-op; illegitimate revocation is a no-op; legitimate revision changes legitimate state; legitimate delegation changes legitimate authority state; legitimate self-revocation is allowed if authorized by the strict pre-state. The raw process may diverge arbitrarily.

Do not assume this construction is correct merely because it fixes the lifecycle problem. Ask whether it makes the headline theorem tautological. If it does, identify which genuinely global consequences still require proof.

# 4. Separate historical time from audit time

A historical edit may have appeared legitimate when performed, while later inquiry discovers forged provenance, hidden influence, invalid consent, omitted dependency or fraudulent authority.

Introduce/prosecute a two-index object `L^alpha_s` where `s` is historical/event time and `alpha` is the current audit/provenance context. For fixed `alpha`, replay the historical edit sequence. The current legitimacy state at `t` is `L^{alpha_t}_t`.

Prosecute whether this cleanly separates the historical authorization rule from current evidence about whether that rule was actually satisfied. Changing `alpha` may revise the legitimacy assessment of old edits without retroactively changing which normative rule was historically applicable.

Add a fixture where later audit information invalidates an earlier authority-changing edit and all descendants whose legitimacy depended on it.

# 5. Replace "challenge survival" with "authorization of the actual edit" if possible

Canonical case: Alice legitimately has authority to revise policy after hearing Bob; Bob gives an argument; Alice changes policy because of it; remove Bob's argument and the edit no longer occurs. This should **not** by itself make the edit illegitimate.

Test whether legitimacy should require that the edit survives the challenge, or instead that prior legitimate authority permitted this exact edit given this certified input. Candidate local judgment `Permit_L(B, I, e)`. It may be content-sensitive and jurisdiction-sensitive, and must allow `content(successor) != content(predecessor)` without allowing arbitrary scope expansion.

Decide whether challenge replay belongs in the abstract legitimacy theorem or in one realization of provenance/exercise validity. Do not preserve L3/L3' unless the theorem genuinely needs them after this reformulation.

# 6. Add an explicit distinction between legitimate authority and permitted exercise

Construct: authority `a` is legitimately grounded; `a` has jurisdiction only over domain `D`; exercise `t` uses `a` to perform edit `e` outside `D`. Does the current abstract frame reject it? If not, the theorem establishes authority provenance but not legitimacy of the particular exercise.

Introduce the narrowest abstract authorization relation necessary to block this. It must express jurisdiction, scope, consent conditions, amendment rules, procedural conditions and domain restrictions without importing Reflective Integrity.

**Required countermodel:** legitimate authority used outside its jurisdiction.

# 7. Distinguish input validity from exercise validity

A legitimacy certificate may need `c = (B, I, X)` — prior legitimate authority basis, authorization-relevant informational input, and evidence that this was an admissible/authentic exercise. Prosecute `InputOK` and `ExerciseOK` as separate concepts, deciding cases like legitimate argument, forged message, coercion, tampered decision procedure, fake consent, valid election, manipulated election.

Do not hardcode normative answers. The live rules may permit arbitrary influence, in which case the theorem should accept it. The structural theorem should only require that whatever the rules treat as relevant to authentic exercise is represented through the interface.

# 8. Dependency factorization must become precise

The central remaining risk is that "provenance completeness" just means "assume hidden influence does not matter." Turn this into a falsifiable mathematical interface.

Let the legitimacy-relevant view of a historical edit be `V_s = (L_s, B_s, I_s, X_s, e_s)`. Require: `V_s(H) = V_s(H') -> Valid(H, e_s) = Valid(H', e_s)`, and where valid, `apply_H(L_s,e_s) = apply_H'(L_s,e_s)`.

This should generalize the earlier pre-state-blindness issue: schemas may read pre-state, but every legitimacy-relevant read must factor through the declared interface. Build a negative fixture where a hidden variable changes either whether the edit is admitted or what normative effect is produced, while all declared inputs remain fixed.

# 9. Threat-relative provenance adequacy should remain explicit

Preserve the good repair that legitimacy is relative to a threat model `Xi`. But reconsider whether the current `ThreatModel.depends` / `Coverage via Chal` remains the best abstraction if challenge replay moves below the headline theorem. A more abstract interface may be `ProvOK_{alpha,Xi}(I, X)` with a semantic adequacy law. It is acceptable for Carroll replay to realize this interface; it is not acceptable for the headline theorem to silently assume every relevant dependency is already recorded.

# 10. Prosecute the distinction between soundness and completeness

If `Verify(c,e) -> Valid(e)` but not conversely, the legitimate replay is a sound under-approximation. That may be enough for some recognition tasks and wrong for enforcement: a legitimate revocation is missed, the old norm remains in the derived replay, and enforcement wrongly continues.

Explicitly separate verifier soundness, verifier completeness and the semantic legitimacy relation. Add a fixture where sound-but-incomplete verification leaves an obsolete norm in force.

# 11. Prosecute occurrence identity versus content identity

A rejected edit may introduce content `x`; later an independent legitimate edit may introduce the same content. We want illicit occurrence != later legitimate occurrence even when the contents are equal. Build: bad edit introduces policy P; descendants use the bad occurrence; later clean authority independently adopts P. Required: first lineage rejected, later clean occurrence legitimate. Do not poison content globally.

# 12. Target a real No-Laundering theorem

> If an authority-changing edit is rejected under audit context `alpha` and threat model `Xi`, then the authority occurrence it creates cannot become a valid legitimacy ground merely through downstream use.

Test whether this follows from strict-prestate grounding, legitimate replay and occurrence identity, rather than from challenge-stability axioms. This should be a global theorem, not a definition.

# 13. Target finite grounding as a certificate theorem

For every legitimate authority occurrence derive a finite certificate tree whose leaves lie in `G`, whose internal nodes are `alpha`-valid historical edits, and whose children are the prior authority grounds of the edit, with historical time strictly decreasing. No unique issuance required; multiple valid derivations allowed. Compare this to the current `derivation` object and decide whether the latter survives.

# 14. Target hidden-state noninterference

Define the complete legitimacy-relevant view up to `t` and try to prove that two raw histories with the same view have the same legitimate state. Interpretation: hidden implementation state cannot change what is legitimately in force except by changing something that crosses a declared legitimacy interface. Authorized influence is allowed. The theorem should not require invariant outputs under legitimate persuasion. Add both positive and negative tests.

# 15. Persistence theorem must be stated correctly

Under a fixed audit context: `x in L^alpha_s` and no `alpha`-valid edit disposes `x` during `(s,t]` implies `x in L^alpha_t`. Separately, `alpha -> alpha'` may remove `x`. Do not conflate normative revision with revised legitimacy assessment.

# 16. Revisit authority and norm as separate sorts/views

Ensure the abstract interface can distinguish authority-bearing outputs from force-bearing/substantive normative outputs without consumer knowledge leaking into the theorem. Deference consumes `AuthorityView`; traderization consumes `NormView`.

# 17. Re-run both consumers against the compressed theorem

Deference: does the consumer now receive enough to establish that a future authority occurrence is in the valid closure of a base authority it recognizes, while allowing radically changed content, and rejecting raw future authority generated by an invalid edit? Preserve the finding that recognition transport is still an explicit consumer axiom.

Traderization: define the enforcement target from `Norm(L^alpha_t)`, not raw standing. Test that illegitimate revocation leaves the norm in the target, legitimate revocation removes it, and later audit invalidation revises it. Retain the modular separation of legitimacy, accountability and serviceability; do not pull liability into the headline theorem.

# 18. Re-evaluate the current challenge spine

For each of L0-L4, `q |= x`, `Chal`, issuance stability, origin necessity and challenge bite, classify: still essential; realization-specific; replaced; optional strengthening; obsolete. Decide whether pre-state-blindness remains a global legitimacy assumption or whether its genuine content is captured by authorization/effect factorization. The branch's effect-identity prosecution showed changing exercise identity alone does not remove the problem; do not ignore that, and do not treat it as proof that challenge survival is the correct abstraction.

# 19. Compression target

Candidate local hypotheses: mediated explicit mutation; strict-prestate grounded authorization; permit/jurisdiction soundness for the exact edit; declared dependency/effect factorization; threat-relative provenance/exercise adequacy. Then prove a global package: finite grounding to the recognized base; no self-ratification; no laundering of rejected authority; hidden-state noninterference; persistence until valid disposition; unrestricted permitted substantive revision — relative to base `G`, authorization semantics `Pi`, threat model `Xi` and audit context `alpha`. The theorem should not claim to derive substantive moral correctness of `G` or `Pi`.

# 20. Required countermodels

Illegitimate revocation of a legitimate norm; legitimate authority with unauthorized jurisdiction; legitimate persuasion; hidden authorization dependency; hidden effect dependency; later audit discovery; rejected-authority laundering; independent readoption of identical content; sound but incomplete checker; two raw histories with the same declared legitimacy view.

# 21. What counts as real mathematical content

Do not count "only Valid edits affect the legitimate replay" as the headline theorem if that is true merely by definition. The theorem should earn finite grounding, no laundering and noninterference by induction/factorization from local hypotheses. The proof should contain a recognizable global step. If all global conclusions are definitional unfoldings, the compression has gone too far.

# 22. Keep the realization boundary sharp

The headline theorem must not mention `NormEvent`, `ReasonOcc`, `Settlement`, `AnsRoot`, Reflective Integrity, Carroll DR-MDP, Logical Induction, `PForce` or replay internals. Then separately ask whether Reflective Integrity realizes the hypotheses, and whether the warrant/register model can realize them without RI. If the non-RI realization becomes difficult after adding `Permit`, `ProvOK` and audit context, build a minimal independent office/constitution model rather than weakening the theorem to preserve the old fixture.

# 23. Do not Lean-port

Even if the current branch says a Lean port is recommended: **DO NOT LEAN-PORT THIS PASS.** A Lean port of the wrong abstraction would freeze provisional ontology.

# 24. Deliverables

Update the current round. At minimum revise `README.md`, `LEGITIMATE_EVOLUTION.md`, `CROSS_PROCESS_INTERFACE.md`, `CONSUMER_TEST.md`, `TRADERIZATION_CONSUMER.md`, `COUNTERMODELS.md`, `THEOREM_MAP.md`, `src/frame.py`, `src/ri_frame.py`, `src/warrant.py`, `tests/test_frame.py`. Add a dedicated document if useful, but prefer one compressed canonical theorem document over proliferating prose. Preserve old rejected rules/countermodels where they remain informative.

# 25. Verdicts

`LEGITIMACY-THEOREM-COMPRESSED` if: the raw lifecycle has been replaced or shown sufficient; the illicit-revocation case is handled correctly; legitimate authority is distinguished from authorization of the exact exercise; legitimate influence does not need outcome survival; audit time and historical time are handled coherently; dependency/effect factorization is precise and falsifiable; no-laundering is proved; finite grounding is proved; hidden-state noninterference is proved; both consumers work against the same abstract output.

`LEGITIMACY-THEOREM-PROMISING-BUT-NOT-COMPRESSED` if the new direction is better but one ingredient remains unresolved.

`CURRENT-SUCCESSION-SPINE-REMAINS-BEST` only if the alternate formulation is actually weaker, false, or collapses into tautology.

`LEGITIMACY-ABSTRACTION-FAILS` if no nontrivial implementation-independent theorem survives without smuggling the desired conclusion into `Valid`.

# 26. Final report

Answer directly: 1. Does `F^leg = raw_live ∩ Derivable` fail under illegitimate revocation? 2. What replaces it? 3. One legitimate replay or an audit-indexed family? 4. What is the exact local `Valid` judgment? 5. Does a grounded licence suffice, or is `Permit` required? 6. What belongs in `InputOK` versus `ExerciseOK`? 7. Does the abstract theorem still need challenge survival? 8. What becomes of L3/L3'? 9. What is the dependency-factorization law? 10. What is the effect-factorization law? 11. What is the threat-relative provenance adequacy hypothesis? 12. Is `Valid` semantic, verifier-relative, or both? 13. Do consumers require verifier completeness? 14. What is the finite grounding theorem? 15. What is the no-laundering theorem? 16. What is the hidden-state noninterference theorem? 17. What is the persistence theorem at fixed audit context? 18. How does later audit information retract previously accepted legitimacy? 19. How is later clean readoption distinguished from laundering? 20. What does deference consume? 21. What does traderization consume? 22. Which current branch axioms survived unchanged? 23. Which became realization-specific? 24. Is pre-state-blindness still genuinely required? 25. Is the resulting theorem materially non-definitional? 26. Is the theorem short enough to be the compression target for the whole legitimacy line? 27. Is it stable enough for a later Lean port?

# 27. Central standard

> **Given a recognized base, explicit locally authorized normative edits, complete declared authorization dependencies, and provenance adequate to a stated threat model, every currently legitimate authority has a finite authorization lineage to the base; rejected authority cannot acquire legitimacy merely through downstream use; hidden implementation differences cannot change the legitimate state without crossing the declared legitimacy interface; and legitimate normative state persists until a valid edit changes it, while genuine content-changing learning remains allowed.**

> **Reflective Integrity should realize the hypotheses. Deference and traderization should consume only the conclusions.**

> **The theorem must say more than "the valid replay contains only valid edits." Its global content should be finite grounding, no laundering, and noninterference.**

Treat the current branch as a strong provisional result, not as something to defend.

---

---

# PROSECUTION AND COMPRESSION PASS — BEFORE MECHANIZATION

*Dispatched after the compression pass shipped and was reviewed.*

You are doing one more mathematical prosecution/compression pass on
`round/2026-08-25-legitimate-evolution`. Current verdict:
`LEGITIMACY-THEOREM-COMPRESSED`. Do **not** trust that verdict. Do **not**
Lean-port anything in this pass.

The previous pass appears to have found the correct dynamic object and correctly
replaced the old `raw_live ∩ Derivable` frontier. The purpose of this pass is
different:

> **Strip the theorem down to its exact mathematical kernel, prosecute every
> remaining premise, and separate the structural replay theorem from the
> substantive local legitimacy semantics and from implementation-factorization
> claims.**

The target is not another richer architecture. The target is a theorem small
enough that every type, premise and conclusion is obviously doing necessary work.

# 1. Start by trying to refute the current G1

Construct an edit with `grounds = {}`, issuing a fresh authority, disposing
nothing, with `Valid` true, `Permit` true, `ProvOK` true, `Xi = {}`. Current H3
says `Valid(L,e) -> grounds(e) ⊆ Auth(L)`, which holds vacuously. Does current G1
nevertheless claim a finite grounding tree whose leaves lie in `G`? If yes, G1 is
false as stated. Do not paper this over by changing the certificate checker.
Identify the exact missing premise — candidates being
`Valid(L,e) and apply(L,e) != L -> grounds(e) != {}` or the stronger
`Valid(L,e) -> grounds(e) != {}` — and decide which is mathematically right.
Interpret the choice: if something may enter or leave legitimate normative state
without any prior authority premise, it is a new root, and roots that are intended
belong in `G`. Add the minimal countermodel and repair.

# 2. Prosecute occurrence identity harder

`Occ = (at, index, sort)` and freshness is claimed to follow from the type. Are
historical times guaranteed unique per edit? What happens if two edits share `at`?
Is `at` identity or merely order? Does `Process.at(s)` silently assume at most one
edit per time? If freshness depends on unique historical times, that is an
unstated structural premise. Prefer, if necessary, an `EditId` with `time` separate
and `Occ = (issuer, slot)`. Do not add complexity unless the current
representation actually has the hole. State exactly which property the theorems
consume: **unique birth of an occurrence**, not unique issuance of a content.

# 3. Attack the current soundness/completeness result

Prosecute with a missed authority revocation: `a ∈ Auth(G)`, a semantically valid
`e0` revoking `a`, a sound-but-incomplete verifier rejecting `e0`. Compare the
semantic replay with the verifier replay. Does the recognizer now positively
recognize an authority no longer semantically legitimate? Then let a later `e1`
use `a` as a ground: because the checker replay retains `a`, `e1` may be valid
relative to the checker state and invalid relative to the semantic one. Test
whether the current `verifier_sound` still calls this checker sound. Determine the
correct mathematical relation between semantic replay and checker replay — full
equivalence, or a projection-specific simulation. Find the weakest condition
actually sufficient for current `AuthorityView`, current `NormView`, and positive
issuance certificates. This is a mathematical question, not a product-design
choice.

# 4. Distinguish three different certification questions

Construct `g --e1--> a`, `e2` validly revokes `a`, `a --e3--> b`. The apparent
grounding tree `g -> a -> b` contains no representation of `e2`, yet whether `e3`
was valid depends on `a ∈ Auth(L_3)`, which depends on `e2`. Distinguish origin /
grounding, historical-liveness, and current-state certificates. Ask exactly what
G1 proves and do not let "finite grounding tree" silently imply the latter two.
Determine whether an independently checkable current-authority certificate
requires replaying the prefix, a state commitment plus proof, proof of absence of
valid disposal, a richer authorization-proof object, or something else. The
theorem must stop claiming more than G1 gives.

# 5. Reconsider whether `Valid` should remain an arbitrary parameter

If `Valid` means semantic legitimacy relative to the supplied semantics, why is it
permitted to arbitrarily reject an edit that is properly grounded, permitted and
provenance-adequate? Try defining semantic validity rather than constraining it,
and distinguish semantic `Valid`, computable `Verify` and raw-process admission.
Decide whether H3/H4/H6 should disappear as theorem hypotheses and become clauses
of the definition. If there is a good reason to keep `Valid` primitive, exhibit a
case which requires the extra freedom.

# 6. Separate descriptive provenance from normative permission

Provenance should answer descriptive questions — did Bob provide this argument,
was this signature forged, was Alice coerced, which inputs entered this exercise,
was the designated investigation run. `Permit` should decide what those facts mean
normatively — persuasion is allowed, forgery does not count as exercise, coercion
does or does not invalidate, this jurisdiction may act on this subject, this vote
threshold suffices. Re-run persuasion, forged input, coerced exercise and the
laundering campaign. The persuasion case is especially important: Bob's argument
should appear in provenance while still being normatively permitted.

# 7. Make the remaining coverage problem exact

Do not solve coverage. State the irreducible question as sharply as possible: for
a threat class `Xi`, does the provenance view expose every `Xi`-relevant
dependency of the authorization judgment? Try to state an adequacy property which
is not circular, not "assume all relevant influences are visible" in prose, not
equivalent to "refuse every influence", compatible with permitted persuasion, and
falsifiable by the existing fixtures. If no satisfactory abstract condition
exists, say so and leave coverage as an explicit epistemic/causal assumption. Do
not contaminate Grounded Replay with it.

# 8. Freeze the effect inside the edit

If legitimacy authorizes the exact normative edit, consider making `delta =
(dispose, issue)` part of the proposal, so `apply` is deterministic by
construction. A raw implementation performing another effect has not executed the
same edit; it has violated a realization-level conformance relation. Ask whether
the hidden-effect countermodel belongs at the legitimacy theorem or at the
raw-history to abstract-edit realization boundary. Prefer the latter if the maths
permits.

# 9. Move H5 to the correct level if possible

Decompose: raw history → extraction → edit trace → deterministic semantic replay →
`L`. At the abstract level, same base plus same abstract trace gives the same
replay, which is fold congruence. At the realization level, same declared raw view
gives the same extracted trace, which is the substantive factorization theorem.
Determine whether hidden-state noninterference should therefore be a composition
of the two. If so, H5 is not a legitimacy premise.

# 10. Delete or repair G6

Arbitrary content relabelling should be able to change `Permit` and therefore
legitimacy — a fiscal warrant may permit setting a tax rate while refusing to
disable a safety system. Also inspect whether the executable check genuinely
replays a relabelled process or merely builds a relabelled dictionary while
replaying the unchanged one. If the claim is vacuous or false, withdraw it, and
replace it with a no-content-conservativity statement that is not a separate
theorem if it follows from the structural proof never inspecting content.

# 11. Reconsider the authority/norm partition

Ask whether the theorem requires a partition. Could one item be both
authorization-bearing and substantively normative? Grounded Replay seems to need
only `Auth`, while the enforcement consumer needs `Norm`; they need not be
exhaustive or disjoint unless a theorem uses that. Prefer predicates if the
partition buys nothing. Do not change RI merely for elegance.

# 12. Strip the structural theorem down aggressively

Isolate a theorem mentioning none of `Permit`, `ProvOK`, `Xi`, raw histories,
challenge replay, reason occurrences, settlements, answerability, deference or
traderization. Structural premises should be only what the induction consumes.
Candidate minimum: unique birth; accepted nontrivial edits have a non-empty ground
set; `Valid(L,e) -> grounds(e) ⊆ Auth(L)`; plus whatever ordering fact ensures
grounds strictly precede issued outputs. Determine the exact minimum. Do not
retain six hypotheses for symmetry.

# 13. State the strongest exact Grounded Replay theorem

State it in mathematical form, not prose, with the corollaries — no
self-ratification, no laundering of rejected occurrence identities, persistence
until accepted disposal — derived separately. Check whether these are genuinely
consequences of the same premises or require different structural assumptions.

# 14. Ask whether live-state membership is what G1 should range over

An occurrence can be legitimately issued and later legitimately disposed; its
legitimacy history does not vanish. Consider `Admitted` = `G` union the issues of
accepted edits, with `L ⊆ Admitted`, and lifecycle separate. Prosecute both
formulations and use the one the consumers actually need.

# 15. Press the distinction between lineage and currentness

`Grounded`, `Admitted` and `Live` should not be silently identified. Determine
their exact relationships and build counterexamples for the reverse implications.
In particular: a grounding tree may establish `Grounded(o)` but cannot by itself
establish `Live_t(o)`. Make this explicit if true.

# 16. Re-run the two consumers after the distinction

Deference: decide whether the bridge needs `Grounded(o)` or `Live_t(o)`. If it
needs current legitimate authority, a grounding tree alone is insufficient and
checker completeness matters. Traderization clearly consumes `Norm(L_t)`, so it
requires currentness; re-test unauthorized repeal, valid repeal, missed valid
repeal and audit-invalidated repeal.

# 17. Keep the reasons multihypergraph below the structural theorem

Do not put `ReasonOcc` into Grounded Replay. A reason derivation is evidence for
the local judgment, not a parent in the authorization grounding tree unless a
normative rule separately makes it one. Preserve: epistemic provenance is not
normative authority provenance.

# 18. Do not repair RI jurisdiction yet

Leave the bare-`PAuth` gap as a realization failure. Do not widen `PAuth` merely to
make a hypothesis green. First determine the clean abstract `Permit` interface.

# 19. Required countermodels

Nullary authority creation; two edits at one historical time; missed valid
authority revocation; stale authority used downstream; grounding tree omitting an
intervening revocation; content-sensitive jurisdiction; permitted persuasion;
forged input; coerced exercise; hidden raw dependency; hidden effect; legitimate
readoption of identical content.

# 20. What may survive

A structural core (Grounded Replay, finite grounding, no self-ratification, no
laundering, persistence); local semantics (`Valid` defined from prior authority,
non-empty basis, complete provenance description, `Permit`); realization
(extraction factorization giving hidden-state noninterference); computation
(`Verify` versus semantic `Valid`, with separate soundness/completeness/simulation
questions).

# 21. Do not oversell mathematical depth

If Grounded Replay is a short induction, say so. The contribution may be
identifying the correct derived state, the exact closure invariant, why previous
natural objects fail, the separation of global grounded evolution from local
substantive legitimacy, and the right interfaces for two consumers. Do not inflate
a two-line persistence lemma into a central theorem.

# 22. Deliverables

Update the current round. Delete obsolete claims and tests rather than keeping them
alive for continuity. Preserve withdrawn formulations in the prosecution record
where historically useful. **Do not write Lean.**

# 23. Final theorem statement

End with a section literally titled `MINIMAL MATHEMATICAL STATEMENT` containing
exact types, exact definitions, the minimal premises, the exact theorem, exact
corollaries, one counterexample per premise, which claims are definitional versus
inductive, and which objects are structural versus semantic versus
realization-level. It should fit on roughly one page.

# 24. Final questions

1. Is current G1 false because empty ground sets are allowed? 2. What is the
minimal repair? 3. Is historical time being used incorrectly as edit identity? 4.
What exact freshness property is required? 5. Does sound verifier
under-approximation preserve current `AuthorityView`? 6. Does it preserve current
`NormView`? 7. What is the weakest checker relation sufficient for each? 8. What
exactly does a grounding tree certify? 9. What does it fail to certify? 10. Is a
current-state certificate necessarily history-sensitive? 11. Should semantic
`Valid` be defined rather than primitive? 12. What is the exact definition if so?
13. Which work is descriptive provenance doing? 14. Which work is `Permit` doing?
15. What exactly remains open in threat/provenance completeness? 16. Should the
edit contain its frozen effect? 17. If yes, what becomes of hidden-effect
factorization? 18. Is H5 a legitimacy hypothesis or a realization theorem? 19. Is
G6 false/vacuous and should it be deleted? 20. Must `Auth` and `Norm` be a
partition? 21. What are the minimal structural premises? 22. Should G1 range over
current live state or all historically admitted occurrences? 23. What is the exact
relation between grounded, admitted and live? 24. Which does deference consume?
25. Which does traderization consume? 26. What remains of H1-H6? 27. What remains
of G1-G6? 28. Is the theorem now stable enough for a future Lean port?

# 25. Verdicts

`GROUNDED-REPLAY-KERNEL-STABLE` if the structural theorem reduces to a small exact
induction with all premises prosecuted and the semantic/realization layers cleanly
separated. `COMPRESSION-STILL-LEAKY` if the replay object is right but
types/premises/certificates still conflate distinct notions.
`REPLAY-SPINE-FAILS` if a serious counterexample breaks the reconstructed-state
approach itself. No Lean in any case.

The standard for this pass:

> **At the end I should be able to write the core theorem on a whiteboard in under
> a minute, and every symbol on the board should have a mathematically unavoidable
> role.**

The main thing to resist is adding concepts. Prefer deleting assumptions,
splitting claims that are mathematically different, and moving
implementation-specific facts below the realization boundary.

---

---

# PROPER EXERCISE — A NARROW THEOREM-DISCOVERY ROUND

*Dispatched after the prosecution pass shipped and was reviewed.*

Treat **Grounded Replay as frozen infrastructure** unless you discover an actual
contradiction in it. Do not enrich it. Do not re-open succession calculus,
challenge survival, raw-live filtering, or the grounding-tree/currentness
distinction unless Proper Exercise genuinely forces a change.

Grounded Replay establishes, roughly: legitimate state is reconstructed by
replaying valid edits from a base; accepted issuance is grounded in already-live
prior standing; admitted standing has finite ancestry to the base; rejected issued
identities cannot be laundered into legitimate standing; live standing persists
until a valid edit disposes it.

It does **not** establish that a grounded authority was entitled to perform the
particular act it performed. The canonical counterexample is a fiscal authority,
grounded, with impeccable provenance, legislating on safety.

> **Find the smallest mathematical theory of Proper Exercise that distinguishes
> possessing legitimate authority from being entitled to perform this exact edit,
> and determine whether it yields a nontrivial no-privilege-escalation theorem.**

Do not write Lean. Do not attempt the full legitimacy theorem package. Do not
solve Reason Disposition, Liability Continuity, provenance adequacy or deference
except where they are necessary as consumers or tests.

# 1. Start from the failure, not from an ontology

Construct the smallest examples separating grounded authority from proper
exercise: (A) fiscal authority on fiscal policy, should pass; (B) the same on
safety, should fail; (C) safety authority delegating narrower safety power,
probably pass; (D) safety authority delegating fiscal power, should fail absent a
higher rule; (E) ordinary authority expanding its own jurisdiction, should fail;
(F) constitutional authority expanding another office's, may pass; (G)
constitutional authority changing the constitution itself, may pass if amendment
authority exists.

Do not begin by inventing fields like `scope`, `domain`, `capability`, `role` or
`jurisdiction`. Let the counterexamples tell you which structure is necessary.

# 2. Ask what `Permit` must contain

`Permit(L, e, r)` is a valid semantic interface but not yet a theory. Determine
whether it admits a useful internal factorization — authority to a class of
permitted edits; authority plus jurisdiction to a permitted transformation; or a
proof-relevant judgment. The target must reject fiscal-to-safety overreach and
still allow delegation, amendment, constitutional change, open-ended substantive
revision, multiple authorities jointly authorizing, and different authorization
proofs for the same edit.

# 3. Separate three questions

Is the authority live; what class of acts is it empowered to perform; were the
procedural and contextual conditions satisfied. Grounded Replay handles the first.
Provenance supplies descriptive facts relevant to the third but should not make
the normative decision. Give exact types without collapsing them.

# 4. Prosecute the naive capability-set model

`J(a) subset Edit`, with exercise proper if `e` is in the combination over the
basis. Attack it: is `Edit` too intensional or too concrete; should permissions
range over edit descriptions; how are context-dependent conditions represented;
how are joint authorities; is authority conjunctive, disjunctive, thresholded,
role-sensitive; can it be conditional on state; can the same authority permit
different acts depending on declared evidence; can a permission be revised.

# 5. Press especially on authority that changes authority

How can legitimate authority scope change without allowing arbitrary privilege
escalation? Naive monotonicity `J(a') subset J(a)` for delegation is likely too
strong. Distinguish object-level permissions from permissions to transform
permissions only if counterexamples require it; investigate whether higher-order
authority can be represented uniformly as permission over edits whose content
happens to modify authorization structure. Prefer a single uniform calculus.

# 6. Target a No Unauthorized Privilege Escalation theorem

Aim beyond "Permit was checked". Intended: any authority in force may have
broader, narrower or different scope than its ancestors, but every change in that
scope must itself occur through an edit that prior live authority was empowered to
perform. This should imply that no office bootstraps new powers merely by
exercising the powers it has, while allowing a constitutionally empowered
amendment authority to widen another office.

# 7. Ask whether Grounded Replay needs extension or only decoration

Ideally the kernel is unchanged and Proper Exercise attaches a proof object to
each accepted edge. Prefer this over modifying the replay kernel. If the kernel
genuinely needs more structure, exhibit the exact counterexample.

# 8. Keep reasons and provenance local

Hereditary authority support `B`, plus local reason/provenance evidence `r`, plus
the exact edit. The grounding recursion follows `B` and does not recurse through
`r`. Test: Bob persuades Alice, Alice uses valid authority to revise, removing the
argument would remove the revision, and the exercise should still be proper if
persuasion is permitted. Do not reintroduce challenge survival.

# 9. Do not let provenance decide normativity

Provenance says what happened; Proper Exercise says what those facts authorize.
Both "coercion invalidates" and "coercion does not invalidate" must be
representable. Same for forged signature, vote threshold, consent, declared
reason, delegated actor, procedural defect. Provenance adequacy remains an
explicit epistemic assumption; do not derive it.

# 10. Press on proof relevance

Should `ProperExercise(L,e)` be a proposition, or is the important object a proof
with accessible support? Multiple proofs may exist for one edit, which matters for
joint authority, redundant authority, alternative amendment paths and ex post
rationalization. Prosecute: an edit performed under invalid basis B_bad, where a
valid B_good could have authorized the same edit. Should it thereby count as
proper? Probably not automatically. Determine whether Proper Exercise must certify
the actual exercise route rather than existentially quantifying.

# 11. Build an ex-post-rationalization counterexample

Alice performs `e` claiming `a_bad`, which does not authorize it, while `b_good`
independently could have and was not invoked. Compare `exists B. Permit(B,e)`
against the actual exercise carrying a valid witness. Decide which notion
legitimacy requires; this should inform whether grounds belong to `Edit` or to a
witness.

# 12. Press on delegation

Narrower, equal, broader, incomparable. Which are always permissible, never, or
permissible only with delegation/amendment authority. Avoid assuming a subset
relation unless it survives. Try for a compositional theorem: proper delegation
plus proper use by the delegate gives proper downstream exercise.

# 13. Press on joint and threshold authority

Two-of-three, unanimity, co-signature, ordinary authority plus emergency
condition. Support plus a predicate may already handle all of these; if so, do not
add an authority algebra. Determine what structural theorem, if any, is provable
without inspecting `Permit`.

# 14. Press on negative conditions

No veto active; no conflict of interest; no superseding rule live; emergency
absent or present. Separate hereditary authority premises from local contextual
conditions. A negative fact must not become an ancestor in the authority tree
merely because `Permit` consulted it.

# 15. Ask what theorem remains if `Permit` is opaque

Be ruthless. If the only theorem is "valid edits satisfy Permit", nothing
mathematical has been gained. We need internal structure yielding a theorem, or a
proof-relevant interface whose composition yields one, or a no-privilege-escalation
invariant, or a recognition/composition property unavailable to an arbitrary
predicate. If none exists, say clearly that Proper Exercise is semantic input, not
a theorem module. That is an acceptable result. Do not manufacture fake theorem
content.

# 16. Try three candidate abstraction levels

Level A opaque `Permit`; Level B capability/jurisdiction; Level C a proof system
with rules for direct exercise, delegation, amendment, joint authority and
procedural side conditions. Compare on expressive adequacy, theorem strength, RI
realization cost, and risk of smuggling moral theory into the calculus. Prefer the
weakest level that earns a real theorem.

# 17. Try to characterize privilege escalation exactly

Define a formal bad event — an authority capability becoming available downstream
although no proper authority-transforming edit in its lineage licensed it, or a
downstream exercise permitted by newly created authority where no ancestor had
permission to create authority permitting it. Then prove or refute that proper
authority-transforming transitions imply no unauthorized privilege escalation.

# 18. Constitutional self-amendment is a mandatory test

Amendment rule R replaces itself with R'. The validity is judged under the strict
prestate rule R; R' governs later edits only; R' must not retroactively authorize
its own creation. If the abstraction cannot represent this without a special case
it is probably wrong.

# 19. Also test constitutional replacement

R authorizes replacement of the entire constitutional structure, with radically
different authority classes. The theorem should still say the replacement was
proper because the prior constitution authorized that transformation. Do not
impose conservativity that rules this out.

# 20. Interaction with Grounded Replay

Aim for a strengthened lineage result where every internal edge carries a Proper
Exercise witness. Name it only if useful; do not rename Grounded Replay. Then ask
whether the combination yields No Unauthorized Privilege Escalation.

# 21-22. Do not solve Reason Disposition or Liability Continuity

Reasons are local evidence only; due reasons, defeat, response obligations and
inquiry liveness are the next module. Custody, answerability roots, charges and
grants are out of scope except as counterexamples showing Proper Exercise does not
imply answerability.

# 23. RI is a consumer, not the definition

Report which Proper Exercise hypotheses RI can realize now, exactly which it
cannot, and the minimal data it would need. If the clean theorem implies `PAuth`
needs a jurisdiction field, say so; if a `PProto`-style external rule suffices, say
so. Do not modify RI solely to make tests pass.

# 24. Required countermodels

Fiscal used for fiscal; fiscal used for safety; self-expanding authority without
amendment permission; constitution-authorized expansion; narrower delegation;
broader delegation without meta-authority; broader delegation with explicit
authority-transforming permission; two-of-three joint authority; a negative side
condition such as no-veto; ex-post rationalization by an unused valid route;
permitted persuasion; forged exercise; self-amendment under the strict prestate
rule; attempted self-amendment justified only by the new rule; total
constitutional replacement explicitly authorized by the prior rule.

# 25. Desired theorem package

A definition of Proper Exercise; an Exercise Preservation / Proper Lineage
theorem; a No Unauthorized Privilege Escalation theorem; a No Jurisdictional
Self-Ratification corollary. If only the definition survives, report that there is
no independent mathematical theorem here.

# 26. Final compression

End with a section titled `MINIMAL PROPER-EXERCISE KERNEL`, roughly one page,
containing exact types, the exact local judgment, which premises are hereditary,
which inputs are merely local evidence, whether grounds live on the edit or the
witness, the exact theorems, one countermodel per premise, whether
authority-transforming edits need special structure, whether privilege escalation
has a clean mathematical definition, and what RI is missing. If it requires a large
authority ontology, treat that as evidence the abstraction has not compressed.

# 27. Questions that must be answered

1. Is `Permit` inherently opaque, or is there a useful minimal internal structure?
2. Is authority best represented as a capability over edits? 3. Is jurisdiction a
property, a relation, or a theorem of a proof system? 4. Do grounds belong to the
edit or the witness? 5. Is Proper Exercise existential over routes or tied to the
actual route? 6. How is ex-post rationalization prevented? 7. How are
joint/threshold authorities represented? 8. How are negative side conditions
represented without making them hereditary ancestors? 9. Can
authority-transforming edits be represented uniformly? 10. Can legitimate scope
widen? 11. What licenses widening? 12. What is the exact definition of
unauthorized privilege escalation? 13. Can a no-privilege-escalation theorem be
proved? 14. Does constitutional self-amendment work under strict-prestate
semantics? 15. Does total authorized replacement work? 16. Does Proper Exercise
require any change to Grounded Replay? 17. What stronger lineage witness results?
18. What does RI need to add? 19. Is this genuinely a theorem module, or mostly
substantive semantic input? 20. What is the smallest object worth formalizing
later?

# 28. Verdict

`PROPER-EXERCISE-KERNEL-STABLE` if a small falsifiable mathematical structure
earns a genuine theorem such as no unauthorized privilege escalation.
`PROPER-EXERCISE-SEMANTIC-ONLY` if the honest result is that propriety resides in
an opaque `Permit` semantics and no nontrivial generic theorem follows.
`PROPER-EXERCISE-ABSTRACTION-LEAKY` if the current abstraction still conflates
authority, local evidence, procedure or scope. Do not write Lean regardless.

The standard:

> **Grounded Replay already tells us that authority has legitimate ancestry. The
> new mathematics must tell us something nontrivial about what inherited authority
> is allowed to do, without freezing substantive normative content or pretending to
> derive a moral theory.**

Prefer one strong theorem with a small interface over a taxonomy of authority
concepts.

---

# Sixth dispatch — 2026-08-26, the Legitimate Evolution round

Verbatim as received.

Use this as the next pass:

> You are continuing the legitimacy project on branch:
>
> ```text
> round/2026-08-25-legitimate-evolution
> ```
>
> Treat the latest results as the starting point:
>
> ```text
> GROUNDED-REPLAY-KERNEL-STABLE
> PROPER-EXERCISE-SEMANTIC-ONLY
> ```
>
> Grounded Replay is frozen unless you find an actual contradiction.
>
> Do not write Lean.
>
> Do not reopen the search for a generic Proper Exercise theorem. The previous round established that substantive propriety lives in the local permission semantics:
>
> ```text
> Permit(L,e,ProvView(e))
> ```
>
> Jurisdiction, delegation, amendment, widening, quorum, vetoes, constitutional replacement, etc. are semantic choices. The only generic structural facts worth retaining are strict-prestate evaluation / no self-ratification and Grounded Replay itself.
>
> The goal of this pass is:
>
> > **Find the smallest local-to-global theorem that deserves the name Legitimate Evolution.**
>
> In particular, prosecute whether the non-entitlement half of legitimacy compresses into a small **answerability-transition kernel**, analogous to Grounded Replay.
>
> The target architecture to attack is:
>
> ```text
> local normative semantics
>     Permit
>     Due
>     Disposes
>     [possibly Transfer / Succession semantics]
>           |
>           v
> Grounded Replay          Answerability Continuity
>           \               /
>            \             /
>             LEGITIMATE EVOLUTION
> ```
>
> Do not assume this architecture is correct. Try to break or compress it.
>
> ---
>
> # 1. Start with the local-to-global standard
>
> Legitimate Evolution should not be defined as a conjunction of desired global properties.
>
> The desired theorem shape is:
>
> ```text
> small local transition conditions
>             +
> small substantive semantic judgments
>             |
>             v
> global invariants over arbitrarily long histories
> ```
>
> Grounded Replay is the model:
>
> ```text
> accepted local edits satisfy two structural premises
> ->
> every admitted occurrence has finite ancestry to G
> ```
>
> Find the analogous theorem for unresolved normative obligations.
>
> The final theorem should earn something globally that is not merely a restatement of its premises.
>
> ---
>
> # 2. Freeze the entitlement side
>
> Assume the current entitlement side:
>
> ```text
> Valid(L,e)
>   := grounded in live prior authority
>      and nonempty authority for effectful edits
>      and ProvComplete(e)
>      and Permit(L,e,ProvView(e))
> ```
>
> with Grounded Replay giving:
>
> ```text
> finite ancestry
> no self-ratification
> no rejected-occurrence laundering
> persistence until accepted disposal
> ```
>
> Do not add jurisdiction/capability structure to the structural kernel.
>
> Proper Exercise is represented by `Permit`.
>
> What Legitimate Evolution still lacks is a theorem saying what happens to **normative burdens that have become outstanding**.
>
> ---
>
> # 3. Separate three semantic questions
>
> Begin with candidate semantic judgments:
>
> ```text
> Due(L,r,q)
> ```
>
> meaning:
>
> > under the adopted normative semantics, reason occurrence `r` places issue/standing `q` under an obligation of treatment.
>
> ```text
> Disposes(L,x,q)
> ```
>
> meaning:
>
> > response/edit/event `x` counts as a legitimate disposition of the outstanding issue `q`.
>
> Possibly:
>
> ```text
> Transfers(L,x,q,q')
> ```
>
> meaning:
>
> > `x` legitimately moves responsibility for `q` to successor `q'`.
>
> Do not assume these exact types.
>
> Ask whether `Due` and `Disposes` are semantic in exactly the same sense that `Permit` turned out to be semantic.
>
> In particular, do **not** try to derive:
>
> ```text
> which reasons really matter
> ```
>
> or:
>
> ```text
> what the morally correct answer is.
> ```
>
> The theorem should be relative to supplied semantics.
>
> ---
>
> # 4. Search for the smallest answerability object
>
> Do not begin from the existing `AnsRoot` architecture.
>
> Start abstractly.
>
> You need enough state to represent:
>
> ```text
> an obligation is opened
> it remains outstanding
> it is legitimately disposed
> it is transferred
> possibly split
> possibly merged
> ```
>
> Try the smallest possible object first.
>
> Candidate:
>
> ```text
> Obligation occurrence q
> status_t(q) ∈ {open, closed}
> successor relation
> ```
>
> but attack this.
>
> Ask:
>
> * Does a transfer close the old occurrence and open a successor?
> * Does the global theorem need occurrence identity?
> * Is unique birth needed?
> * Is succession tree-shaped, DAG-shaped, or arbitrary?
> * Can one obligation split into two?
> * Can two merge into one?
> * Does merge create laundering?
> * Is a persistent identity with changing custodian simpler than explicit successors?
>
> Prefer the smallest representation that survives the countermodels.
>
> ---
>
> # 5. Target a qualitative continuity theorem
>
> The first hoped-for theorem is approximately:
>
> ```text
> if q becomes outstanding,
> then at every later time either
>
>     q has a legitimate disposition,
>
> or
>
>     there exists a currently live successor chain carrying what remains owed.
> ```
>
> In symbolic shape:
>
> ```text
> Open_s(q)
> ->
> Disposed_{s:t}(q)
>    or
> exists q'. Carries_{s:t}(q,q') and Open_t(q')
> ```
>
> Do not accept this formulation uncritically.
>
> Find the exact relation.
>
> The intended global consequence is:
>
> ```text
> no silent obligation loss.
> ```
>
> This should cover more than persistence of a docket bit.
>
> ---
>
> # 6. Distinguish the semantic and structural halves
>
> A local semantic rule can say:
>
> ```text
> x counts as a disposition of q
> ```
>
> or:
>
> ```text
> x validly transfers q to q'
> ```
>
> The structural theorem should say:
>
> > if transitions may remove an outstanding obligation only through one of these declared operations, arbitrarily long replay preserves either a live carrier or a valid disposition history.
>
> Do not smuggle “correct response to reasons” into the structural theorem.
>
> The analogue to Proper Exercise may be:
>
> ```text
> which responses count as dispositions is semantic;
> that obligations cannot disappear except by those dispositions is structural.
> ```
>
> Test this analogy explicitly.
>
> ---
>
> # 7. Prosecute whether Reason Disposition is a separate theorem module
>
> Previously the proposed package contained:
>
> ```text
> Reason Disposition
> Liability Continuity
> ```
>
> Determine whether this was a false decomposition.
>
> Candidate compression:
>
> ```text
> Due                 semantic
> Disposes            semantic
> obligation replay   structural
> ```
>
> producing:
>
> ```text
> no silent issue loss
> ```
>
> If so, withdraw `Reason Disposition` as an independent theorem module.
>
> Conversely, if something genuinely additional is required to connect reason occurrences to answerability episodes, exhibit the countermodel.
>
> ---
>
> # 8. The central question: qualitative continuity versus quantitative liability
>
> The existing quantitative idea is:
>
> ```text
> c_t + Phi_{t+1} <= Phi_t + eta_t
> ```
>
> hence:
>
> ```text
> sum_{t<T} c_t + Phi_T
> <=
> Phi_0 + sum_{t<T} eta_t.
> ```
>
> Do not assume this belongs inside Legitimate Evolution.
>
> Prosecute two hypotheses:
>
> ```text
> H-A:
> qualitative answerability continuity is sufficient for legitimacy;
> the quantitative bound is a downstream strengthening.
> ```
>
> ```text
> H-B:
> qualitative continuity is too weak;
> without a quantitative invariant obligations can be diluted through succession,
> so liability continuity is constitutive of Legitimate Evolution.
> ```
>
> Build countermodels that distinguish them.
>
> ---
>
> # 9. Required dilution countermodels
>
> At minimum test:
>
> ```text
> A. q remains literally open forever but nobody is required to do anything
> ```
>
> ```text
> B. q transfers q -> q1 -> q2 -> ... and each transfer halves its burden
> ```
>
> ```text
> C. q splits into n successors each carrying 1/n^2 of the original burden
> ```
>
> ```text
> D. two obligations merge into one whose burden is less than either parent
> ```
>
> ```text
> E. q is transferred to a successor that has no capacity / no actual duty
> ```
>
> ```text
> F. q is explicitly disposed by an answer the local semantics recognizes,
> even though an external observer thinks the answer is terrible
> ```
>
> F should probably remain **legitimate evolution**.
>
> The question is whether A-E are already excluded by semantic `Disposes/Transfers`, or whether a quantitative invariant is necessary.
>
> ---
>
> # 10. Distinguish identity from quantity
>
> Be precise about what the liability potential measures.
>
> Possibilities:
>
> ```text
> burden
> required future effort
> enforcement exposure
> unresolved normative debt
> expected repair cost
> capacity reserved for discharge
> ```
>
> Do not use `Phi` until its semantic role is clear.
>
> If no quantity can be given an interpretation generic enough for legitimacy, conclude:
>
> ```text
> quantitative liability is consumer-specific and not constitutive of Legitimate Evolution.
> ```
>
> That is an acceptable result.
>
> ---
>
> # 11. Split and merge are mandatory tests
>
> Any answerability calculus that works only for one-to-one succession may be too weak.
>
> Test:
>
> ```text
> q -> {q1,q2}
> ```
>
> and:
>
> ```text
> {q1,q2} -> q'
> ```
>
> Ask what must be conserved.
>
> Is there:
>
> ```text
> exact conservation
> subadditivity
> superadditivity
> monotone potential
> resource accounting
> ```
>
> or merely a semantic condition that the successor set “carries” the old obligation?
>
> Do not manufacture a numerical invariant merely because split/merge suggests one.
>
> ---
>
> # 12. Custody is not answerability unless the theorem needs it
>
> Current RI uses `AnsRoot` and custody-like structure.
>
> Do not assume that abstract Legitimate Evolution needs a custodian.
>
> Ask:
>
> ```text
> Is "who is responsible?" necessary to state the global theorem?
> ```
>
> Perhaps the minimal object is only:
>
> ```text
> outstanding issue occurrence
> successor relation
> disposition relation
> ```
>
> and custody is realization-level metadata.
>
> Conversely, if delegation without a responsible bearer creates a real laundering counterexample, then custody may belong in the abstract kernel.
>
> Let countermodels decide.
>
> ---
>
> # 13. Keep learning out
>
> Legitimate Evolution must allow:
>
> ```text
> a process that repeatedly makes the same stupid choice,
> faithfully records every outstanding issue,
> and never improves.
> ```
>
> It must also allow:
>
> ```text
> a process that never receives the relevant evidence.
> ```
>
> Those failures belong to:
>
> ```text
> Coverage
> Regret
> Legitimate Learning
> ```
>
> not Legitimate Evolution.
>
> Required negative test:
>
> ```text
> high-regret but procedurally impeccable process
> ->
> Legitimate Evolution = yes
> Legitimate Learning = no
> ```
>
> Do not introduce fairness, service, exploration, or asymptotic improvement into this pass.
>
> ---
>
> # 14. Keep coverage out
>
> Do not require:
>
> ```text
> every relevant real-world reason becomes Due.
> ```
>
> That is learning coverage.
>
> Legitimate Evolution should say only:
>
> ```text
> once the process's supplied semantics recognizes an issue as Due,
> it cannot lose it except through an accepted disposition/succession mechanism.
> ```
>
> Separate:
>
> ```text
> ProvComplete
> ```
>
> from:
>
> ```text
> learning coverage.
> ```
>
> Provenance adequacy concerns whether a local legitimacy judgment sees the relevant history.
>
> Learning coverage concerns whether recurrent failures are exposed to the learning process often enough.
>
> ---
>
> # 15. Keep substantive correctness out
>
> Legitimate Evolution must allow radical normative change.
>
> Required positive cases:
>
> ```text
> constitution replaces itself under a permitted amendment
> ```
>
> ```text
> process rejects a reason after a disposition recognized by its own semantics
> ```
>
> ```text
> Bob permissibly persuades Alice and the final norm changes
> ```
>
> ```text
> current values radically differ from initial values
> ```
>
> There must be no theorem of the form:
>
> ```text
> distance(content_t, content_0) <= epsilon.
> ```
>
> If your abstraction implies content conservativity, reject it.
>
> ---
>
> # 16. Formulate Legitimate Evolution as a global theorem
>
> Try to reach something approximately like:
>
> ```text
> THEOREM — Legitimate Evolution
>
> Given:
>   an accepted base G;
>   a semantic validity relation built from Permit and provenance;
>   semantic Due / Disposes / succession judgments;
>   Grounded Replay's local premises;
>   local answerability-transition premises;
>
> then for every finite time t:
>
>   (E) every live standing has a finite chain of
>       strict-prestate accepted exercises to G;
>
>   (A) every issue previously recognized as due has
>       either a legitimate disposition or a currently
>       outstanding successor trace;
>
>   (L?) any further quantity required for non-dilution
>        satisfies its global conservation/bound.
> ```
>
> The theorem should support arbitrary substantive content change.
>
> Do not force `(L?)` to survive.
>
> ---
>
> # 17. The theorem needs a nontrivial composition payoff
>
> Avoid:
>
> ```text
> GroundedReplay
> and AnswerabilityContinuity
> ->
> GroundedReplay and AnswerabilityContinuity.
> ```
>
> Find the strongest useful global statement earned by their interaction.
>
> Candidate:
>
> > Across any finite sequence of locally legitimate revisions, the process cannot acquire live normative standing without accepted ancestry, and cannot cease to bear an outstanding normative claim except through an accepted disposition or succession route.
>
> Perhaps the entitlement and answerability results are merely parallel rather than interactive.
>
> If there is no deeper interaction theorem, say so.
>
> It may be that:
>
> ```text
> Legitimate Evolution
> ```
>
> is best understood as one semantic property packaged from two independently proved closure theorems.
>
> That is acceptable if true.
>
> Do not invent interaction.
>
> ---
>
> # 18. Test the package against both downstream consumers
>
> ### Traderization
>
> Traderization needs:
>
> ```text
> current Norm(L_t)
> ```
>
> and should receive:
>
> ```text
> these norms are currently live on a Legitimate Evolution trajectory.
> ```
>
> It does **not** need coverage or regret.
>
> Ask whether qualitative answerability continuity contributes anything necessary to entitlement to enforcement, or instead constrains how the norm process may revise while enforcement continues.
>
> Keep traderization's financial/enforcement liability distinct from any normative answerability potential unless a theorem genuinely identifies them.
>
> ### Deference
>
> Deference needs:
>
> ```text
> current Auth(L_t)
> ```
>
> and ultimately:
>
> ```text
> Legitimate Learning
> ```
>
> But Legitimate Evolution should already justify:
>
> ```text
> this radically changed current state remains a legitimate successor.
> ```
>
> Do not solve current-state certification in this pass.
>
> Treat semantic currentness and efficient certification as separate.
>
> ---
>
> # 19. Consumer separation tests
>
> Ensure Legitimate Evolution judges these correctly:
>
> ```text
> legitimate but financially unenforceable norm
>     -> legitimate evolution YES
> ```
>
> ```text
> legitimate but high-regret reasoner
>     -> legitimate evolution YES
> ```
>
> ```text
> legitimate but unobservant process
>     -> legitimate evolution YES
> ```
>
> ```text
> unauthorized norm issuance
>     -> NO
> ```
>
> ```text
> validly issued norm, later invalidly revoked
>     -> remains live
> ```
>
> ```text
> outstanding issue deleted by record mutation
>     -> NO
> ```
>
> ```text
> outstanding issue transferred according to accepted semantics
>     -> YES
> ```
>
> ```text
> obligation diluted to nothing through formally named successors
>     -> determine whether semantics alone or a quantitative invariant must reject this.
> ```
>
> ---
>
> # 20. Revisit RI only after the abstract kernel stabilizes
>
> Once the abstract answerability theorem is clear, map it to:
>
> ```text
> ReasonOcc
> AnsRoot
> NormEvent
> Response
> ```
>
> Ask:
>
> * Does `AnsRoot` contain too much?
> * Does it contain too little?
> * Can `Due` be realized from existing RI data?
> * Can a `Response` realize disposition?
> * Can transfer/succession be realized?
> * Does RI already prevent silent issue loss?
> * If a quantitative invariant is needed, where would its data live?
>
> Do not add new event kinds.
>
> Do not modify RI just to fit a provisional theorem.
>
> Record the exact realization gaps.
>
> ---
>
> # 21. Provenance adequacy remains an assumption
>
> Do not spend this pass trying to solve `ProvComplete`.
>
> It remains:
>
> ```text
> an epistemic assumption at the extraction boundary.
> ```
>
> Use it where local `Permit`, `Due`, or `Disposes` need descriptive facts.
>
> If answerability introduces a **new and genuinely distinct** adequacy condition, identify it explicitly rather than silently folding it into `ProvComplete`.
>
> ---
>
> # 22. Required countermodels
>
> Build and execute at least:
>
> ```text
> 1. due issue silently deleted
> 2. due issue legitimately answered
> 3. due issue legitimately rejected/defeated
> 4. due issue transferred once
> 5. transfer chain
> 6. transfer to nowhere
> 7. split obligation
> 8. merge obligations
> 9. nominal persistence with burden diluted to zero
> 10. high-regret but procedurally legitimate process
> 11. no-coverage but procedurally legitimate process
> 12. radical constitutional change with clean answerability
> 13. unauthorized standing with perfect answerability
> 14. perfect entitlement history with laundered obligation
> 15. current standing validly revoked while its grounding tree remains
> ```
>
> Cases 13 and 14 are especially important: they establish independence of entitlement continuity and answerability continuity.
>
> ---
>
> # 23. Try to compress the package
>
> Explicitly compare:
>
> ```text
> Candidate A:
> Grounded Replay
> + Proper Exercise
> + Reason Disposition
> + Liability Continuity
> ```
>
> against:
>
> ```text
> Candidate B:
> local semantics (Permit, Due, Disposes)
> + Grounded Replay
> + Answerability Continuity
> ```
>
> against:
>
> ```text
> Candidate C:
> local semantics
> + one unified replay theorem over both standing and obligations
> ```
>
> Candidate A is the old picture.
>
> Proper Exercise already gives evidence against A.
>
> Determine whether B is the natural endpoint or whether C produces real compression rather than merely putting unrelated state components in one tuple.
>
> Prefer B over fake unification.
>
> ---
>
> # 24. Ask whether entitlement and answerability are dual
>
> Investigate, but do not romanticize, the apparent symmetry:
>
> ```text
> entitlement:
>     standing cannot appear without ancestry
> ```
>
> ```text
> answerability:
>     obligation cannot disappear without disposition/succession
> ```
>
> Is there a useful abstract notion of:
>
> ```text
> controlled creation
> controlled destruction
> ```
>
> from which both are instances?
>
> If yes and it actually proves something reusable, report it.
>
> If it is merely a verbal duality, leave the theorems separate.
>
> ---
>
> # 25. Decide what “Legitimate Evolution” is a theorem about
>
> At the end answer explicitly:
>
> ```text
> Is Legitimate Evolution:
>
> A. one derived theorem;
> B. a named conjunction of two independent local-to-global theorems;
> C. a semantic definition plus corollaries;
> D. something else?
> ```
>
> Do not assume A is better.
>
> The goal is conceptual truth and compression, not a grand theorem title.
>
> ---
>
> # 26. Desired final mathematical package
>
> The ideal outcome, if earned, is approximately:
>
> ```text
> LOCAL SEMANTICS
>   Permit(L,e,r)
>   Due(L,r,q)
>   Disposes(L,x,q)
>   [Transfer ...]
> ```
>
> ```text
> THEOREM 1 — Grounded Replay
>   local accepted issuance
>   ->
>   finite entitlement ancestry
> ```
>
> ```text
> THEOREM 2 — Answerability Continuity
>   local obligation lifecycle
>   ->
>   no silent obligation loss over arbitrary finite history
> ```
>
> ```text
> [THEOREM 3 — Liability Bound]
>   only if a genuinely legitimacy-relevant quantitative invariant is necessary
> ```
>
> ```text
> COROLLARY / THEOREM — Legitimate Evolution
>   arbitrary substantive normative evolution preserves
>   entitlement integrity and outstanding normative claims.
> ```
>
> Then downstream:
>
> ```text
> Legitimate Evolution
> + Coverage
> + Low Regret
> ->
> Legitimate Learning
> ```
>
> Do not work on the regret theorem in this pass.
>
> ---
>
> # 27. Final section
>
> End with:
>
> ```text
> MINIMAL LEGITIMATE-EVOLUTION PACKAGE
> ```
>
> It must fit on roughly one page.
>
> Include:
>
> * exact semantic parameters;
> * exact structural state;
> * exact local transition rules;
> * exact global theorem(s);
> * which pieces are semantic rather than mathematical;
> * whether Reason Disposition survives as a separate module;
> * whether quantitative liability is constitutive or downstream;
> * one countermodel per indispensable structural premise;
> * independence test between entitlement and answerability;
> * exact RI realization gaps;
> * what Traderization consumes;
> * what Deference consumes;
> * what is deliberately postponed to Legitimate Learning.
>
> If the package cannot be written on a whiteboard in a few minutes, continue compressing.
>
> ---
>
> # 28. Verdict
>
> End with exactly one:
>
> ```text
> LEGITIMATE-EVOLUTION-KERNEL-STABLE
> ```
>
> if a small local-to-global package survives and the remaining substantive choices are cleanly semantic parameters.
>
> ```text
> ANSWERABILITY-KERNEL-STABLE-BUT-COMPOSITION-TRIVIAL
> ```
>
> if the answerability theorem stabilizes but “Legitimate Evolution” is honestly just a useful name for two independent closure results.
>
> ```text
> LEGITIMATE-EVOLUTION-DECOMPOSITION-LEAKY
> ```
>
> if entitlement, reason disposition, liability, coverage, or learning are still being conflated.
>
> ```text
> ANSWERABILITY-SPINE-FAILS
> ```
>
> if no small local-to-global continuity theorem survives the countermodels.
>
> Do not write Lean regardless of verdict.
>
> ---
>
> The research standard for this pass is:
>
> > **A legitimate process may change its substantive normative content arbitrarily. What it may not do is acquire entitlement except through locally permitted prior entitlement, or cease to owe what its own semantics has made outstanding except through a locally legitimate disposition or succession. Find the smallest local conditions from which those global facts follow.**
>
> The key uncertainty is whether that second clause is a simple qualitative replay theorem, or whether genuine legitimacy requires the quantitative liability structure as well. Do not resolve that by intuition; make the countermodels decide.

This is the pass where I’d want the architecture to either compress to something almost embarrassingly small, or fail clearly enough that we know exactly what extra structure is doing real work.

---

# Seventh dispatch — 2026-08-26, the smallest correct package

Verbatim as received.

Use this as the next agent pass.

> Continue on:
>
> ```text
> round/2026-08-25-legitimate-evolution
> ```
>
> Current head:
>
> ```text
> b9f01d4
> ```
>
> Current verdict:
>
> ```text
> LEGITIMATE-EVOLUTION-KERNEL-STABLE
> ```
>
> Treat that verdict as provisional.
>
> Do **not** write Lean.
>
> The purpose of this pass is not to add more architecture. It is to answer one narrow question:
>
> > **Is the current pair — Grounded Replay + Answerability Continuity — actually the smallest correct local-to-global theorem package for Legitimate Evolution, or is the answerability side still one semantic seam too weak?**
>
> The standard is:
>
> > Legitimate Evolution should say that arbitrary substantive normative change cannot manufacture entitlement, ignore something the process's own represented reasons make due, or erase what has become owed except through locally legitimate evolution.
>
> ---
>
> # 1. Freeze Grounded Replay
>
> Do not modify Grounded Replay unless this pass finds an actual contradiction.
>
> Assume:
>
> ```text
> S1 prior live grounding
> S2 no ex-nihilo effectful edit
> ```
>
> and the current theorem/corollaries.
>
> The entitlement side is not the target.
>
> ---
>
> # 2. First attack: transfer then discharge
>
> The current Answerability Continuity statement appears false.
>
> Build exactly:
>
> ```text
> O_0 = {q0}
>
> t=0:
>     transfer q0 -> q1
>
> t=1:
>     discharge q1
> ```
>
> Require A1 and A2 to hold.
>
> Then check the current theorem for:
>
> ```text
> q0, s=0, t=2
> ```
>
> Current conclusion says q0 is either:
>
> ```text
> discharged in [0,2)
> ```
>
> or:
>
> ```text
> connected by transfers to something outstanding at 2.
> ```
>
> Neither appears true.
>
> Do not patch the implementation first. Decide the **correct mathematical conclusion**.
>
> Candidate:
>
> ```text
> every obligation outstanding at s has, at time t,
> a finite forward resolution derivation whose leaves are either:
>
>     currently outstanding at t
>
> or
>
>     validly discharged before t.
> ```
>
> Transfers expand a node into its successor obligations.
>
> Test whether this handles:
>
> ```text
> direct discharge
> one transfer
> transfer chain
> transfer -> discharge
> split
> split -> partial discharge
> split -> all discharge
> merge
> merge -> discharge
> indefinite persistence
> ```
>
> Find the smallest exact statement.
>
> ---
>
> # 3. Decide whether the correct witness is a chain, tree, DAG, or something simpler
>
> Do not assume “resolution tree.”
>
> Splits suggest branching.
>
> Merges suggest DAG structure.
>
> But the theorem for one root obligation may be representable by an unfolded finite tree even when global succession is a DAG.
>
> Compare:
>
> ```text
> transfer chain
> resolution tree
> finite derivation
> reachability relation plus leaf classification
> ```
>
> Prefer the mathematically smallest object that handles every lifecycle correctly.
>
> The proof should remain a simple induction on trace position if possible.
>
> ---
>
> # 4. Attack A2 directly
>
> Current A2:
>
> ```text
> opened obligations are fresh / nobody has opened them before
> ```
>
> The current proof says freshness makes transfer chains finite.
>
> But the trace is already finite and every transfer step happens at a later edit.
>
> Try to prove the corrected Answerability Continuity theorem from **A1 alone**.
>
> Then explicitly build:
>
> ```text
> drop A2
> satisfy A1
> violate freshness
> ```
>
> and ask whether the theorem actually fails.
>
> Do not retain A2 merely because it makes the answerability theorem look symmetric with Grounded Replay.
>
> Verdict must distinguish:
>
> ```text
> A2 necessary
> A2 only representation hygiene
> A2 definitional under occurrence identity
> A2 entirely unnecessary
> ```
>
> If A2 is not necessary, remove it from the theorem package.
>
> ---
>
> # 5. The central conceptual attack: stipulated obligations versus due obligations
>
> Current Answerability Continuity starts from:
>
> ```text
> q is already outstanding.
> ```
>
> That may be too weak for Legitimate Evolution.
>
> Build the following countermodel:
>
> ```text
> reason occurrence r is represented
> local semantic judgment says Due(L,r,q)
> no q is ever opened
> no outstanding obligation is ever silently deleted
> Grounded Replay is perfect
> ```
>
> The current package likely passes this.
>
> Decide whether it should count as Legitimate Evolution.
>
> My intended answer is probably:
>
> ```text
> NO
> ```
>
> because this is not a coverage failure:
>
> ```text
> r is already represented.
> ```
>
> Nor is it a regret failure.
>
> The process's own local semantics says the represented reason makes something due, and the process simply fails to enter that obligation into its answerability dynamics.
>
> Prosecute this hard.
>
> ---
>
> # 6. Distinguish coverage from Due-realization
>
> Keep these separate:
>
> ```text
> COVERAGE:
>     does the relevant failure/reason ever become represented?
>
> DUE:
>     given a represented reason, does the local normative semantics say it
>     requires treatment?
>
> MINTING:
>     if Due says yes, does the answerability state actually reflect that?
> ```
>
> Legitimate Evolution should **not** require coverage.
>
> It may require:
>
> ```text
> Due -> opened-or-immediately-resolved
> ```
>
> once the reason is represented.
>
> Test:
>
> ```text
> relevant reason never observed
> ```
>
> should remain:
>
> ```text
> Legitimate Evolution YES
> Legitimate Learning potentially NO
> ```
>
> while:
>
> ```text
> reason represented
> Due says it requires treatment
> answerability state ignores it
> ```
>
> should probably be:
>
> ```text
> Legitimate Evolution NO
> ```
>
> If you disagree, provide the exact conceptual reason and consumer test.
>
> ---
>
> # 7. Search for the minimal local minting law
>
> Candidate:
>
> ```text
> Due(X_t,r,q)
> ->
> q is opened by the accepted event at t
> or q is legitimately resolved in that same event
> ```
>
> But do not assume this exact form.
>
> Questions:
>
> * Is `q` determined by `Due`, or does `Due` merely say some obligation must open?
> * Can one reason create multiple obligations?
> * Can several reasons jointly create one obligation?
> * Can a reason become due without a new event?
> * Is “immediate resolution” meaningful, or should opening and resolution occur at distinct trace positions?
> * Does the theorem need occurrence identity at the minting site?
>
> Find the smallest rule needed to prevent:
>
> ```text
> recognized-due-but-never-entered
> ```
>
> without introducing coverage or progress.
>
> ---
>
> # 8. Reconsider the local semantic interface
>
> Current documents list:
>
> ```text
> Auth
> Permit
> Due
> Disposes
> Transfers
> ```
>
> Press whether this is the right factoring.
>
> Candidate compressed interface:
>
> ```text
> Permit
> Due
> Resolve
> ```
>
> where `Resolve` may return:
>
> ```text
> done
> carry(successor set)
> ```
>
> Or perhaps the truly minimal object is:
>
> ```text
> LegitStep(X_t,e_t,X_{t+1})
> ```
>
> with named projections used only by consumers.
>
> Compare:
>
> ```text
> A. Permit + Due + Disposes + Transfers
> B. Permit + Due + Resolve
> C. one joint LegitStep relation
> ```
>
> Do not choose the formally smallest encoding if it destroys the distinctions needed by downstream theorems.
>
> In particular:
>
> * Grounded Replay wants the authority/Permit side;
> * Legitimate Learning will likely need access to Due;
> * Answerability Continuity needs the resolution/succession side.
>
> Find the smallest **semantically informative** factorization.
>
> ---
>
> # 9. Should both folds still share one `Valid` bit?
>
> Current coupling:
>
> ```text
> the same Valid gates normative replay and obligation replay
> ```
>
> giving:
>
> ```text
> unentitled act discharges nothing.
> ```
>
> Keep this test, but ask whether `Valid` is now too coarse.
>
> Could there be an event where:
>
> ```text
> normative effect invalid
> but a reason becomes Due anyway?
> ```
>
> For example, an unauthorized act may still generate a complaint.
>
> Or:
>
> ```text
> normative edit rejected
> but descriptive evidence arrives
> and opens an obligation.
> ```
>
> If so, “same Valid gates both entire folds” may be too strong.
>
> This is important.
>
> Distinguish:
>
> ```text
> entitlement to alter normative standing
> entitlement to discharge/transfer an existing obligation
> occurrence of a fact/reason that opens a new obligation
> ```
>
> We definitely want:
>
> ```text
> an unentitled act cannot discharge an obligation.
> ```
>
> But do we really want:
>
> ```text
> a rejected normative edit cannot cause a new obligation to become due?
> ```
>
> Construct examples.
>
> This may force a more precise joint transition semantics than a shared scalar `Valid`.
>
> ---
>
> # 10. Mandatory unauthorized-act / complaint test
>
> Build:
>
> ```text
> Alice performs unauthorized action e
> e is rejected as normative standing change
> the action itself is represented in provenance
> that fact gives rise to a complaint q
> ```
>
> Desired behavior may be:
>
> ```text
> normative effect: no-op
> answerability effect: q opens
> ```
>
> If the current shared-Valid architecture makes this impossible, decide whether that is a genuine flaw.
>
> This test is central.
>
> It separates:
>
> ```text
> normative legitimacy of an act
> ```
>
> from:
>
> ```text
> the process becoming answerable for the fact that the act occurred.
> ```
>
> Do not assume a rejected event is metaphysically nonexistent.
>
> Remember:
>
> ```text
> replay legitimacy state != raw history.
> ```
>
> ---
>
> # 11. This may change the coupling theorem
>
> If openings can arise from represented raw/rejected events while discharges require normative entitlement, the right coupling may be asymmetric:
>
> ```text
> OPEN:
>     can be triggered by represented reasons/facts even when no normative edit is accepted
>
> DISCHARGE / TRANSFER:
>     must be licensed by the legitimate prestate
> ```
>
> Investigate whether this is the correct architecture.
>
> Candidate:
>
> ```text
> raw/represented history
>      |
>      +--> Due --> opens obligations
>      |
>      +--> proposed normative edit
>              |
>              Permit
>              |
>              accepted effect / discharge / transfer
> ```
>
> If this is right, the current “same Valid gates both folds” should be weakened.
>
> ---
>
> # 12. Preserve strict-prestate semantics
>
> Whatever local judgment survives, require that:
>
> ```text
> an edit cannot use authority it creates to justify itself
> ```
>
> and:
>
> ```text
> a purported resolution cannot use a successor obligation it creates
> retroactively as evidence that the predecessor was already handled.
> ```
>
> Test self-ratifying resolution analogues.
>
> ---
>
> # 13. Reassess quantitative liability carefully
>
> Retain the important result:
>
> ```text
> qualitative answerability continuity
> does not imply quantitative burden conservation.
> ```
>
> Do **not** overstate this as:
>
> ```text
> quantitative liability is definitely not constitutive of any legitimacy semantics.
> ```
>
> The structural theorem is content-blind.
>
> A `Resolve/Transfer` semantics may refuse a nominal successor that does not genuinely carry the old obligation.
>
> State the result narrowly:
>
> ```text
> quantitative burden conservation is not a generic structural consequence
> of answerability continuity.
> ```
>
> Then ask whether any quantitative law belongs:
>
> ```text
> a. inside semantic Resolve/Transfers,
> b. downstream for traderization,
> c. nowhere generically.
> ```
>
> Do not decide by intuition.
>
> ---
>
> # 14. Fix or withdraw the current quantitative helper
>
> Inspect:
>
> ```text
> thm_no_dilution_gives_monotone_potential
> ```
>
> Current code appears to:
>
> * check per-parent dilution rather than total dilution;
> * ignore that entirely new obligations may increase potential.
>
> Either repair the theorem with exact sufficient hypotheses or withdraw it.
>
> Do not leave a false/underspecified quantitative theorem adjacent to the stable qualitative kernel.
>
> Preserve the result:
>
> ```text
> total accounting, not per-parent accounting, is required for merges.
> ```
>
> ---
>
> # 15. Revisit the supposed entitlement/answerability duality
>
> Current slogan:
>
> ```text
> entitlement controls creation
> answerability controls destruction
> ```
>
> Press this after adding Due.
>
> The more accurate picture may be:
>
> ```text
> entitlement:
>     controlled creation of normative standing
>
> answerability:
>     required creation + controlled resolution of normative obligations
> ```
>
> That is less symmetric but possibly more correct.
>
> Do not preserve a pretty duality if `Due -> mint` breaks it.
>
> ---
>
> # 16. Target the actual Legitimate Evolution theorem
>
> Try to end with something close to:
>
> ```text
> THEOREM / PACKAGE — Legitimate Evolution
>
> Given:
>
>   an accepted normative base G;
>   represented descriptive history;
>   substantive local semantics Permit, Due, Resolve;
>   strict-prestate evaluation;
>   Grounded Replay's structural premises;
>   a local Due-realization law;
>   a local controlled-resolution law;
>
> then for every finite t:
>
>   E. every live normative standing has finite accepted
>      strict-prestate ancestry to G;
>
>   A. every represented reason that the local semantics made Due
>      has a finite resolution derivation whose current frontier
>      consists only of obligations still outstanding at t or
>      obligations validly discharged before t.
> ```
>
> Then derive:
>
> ```text
> no manufactured entitlement
> no recognized-due-but-ignored obligation
> no silent obligation loss
> no unentitled discharge
> ```
>
> This should permit:
>
> ```text
> radical normative change
> permitted persuasion
> constitutional replacement
> high regret
> no coverage
> obligations remaining open forever
> ```
>
> ---
>
> # 17. Keep Legitimate Learning out
>
> Do not prove progress.
>
> Do not prove coverage.
>
> Do not prove low regret.
>
> Required boundary:
>
> ```text
> Legitimate Evolution
> + Coverage
> + Low Regret
> ->
> Legitimate Learning
> ```
>
> remains downstream.
>
> The only reason to mention this is to test whether `Due` belongs upstream of coverage.
>
> ---
>
> # 18. Consumer tests
>
> ### Deference
>
> Ask whether the strengthened theorem now supports the intended statement:
>
> ```text
> future process is not merely genealogically descended,
> but any represented reason it itself recognizes as demanding treatment
> remains in its normative answerability dynamics.
> ```
>
> No current-state certification work in this pass.
>
> ### Traderization
>
> Traderization still consumes:
>
> ```text
> current legitimate Norm(L_t)
> ```
>
> It should not need Coverage or Regret.
>
> Ask whether outstanding obligations affect:
>
> ```text
> which norm edits/discharges are legitimate
> ```
>
> versus:
>
> ```text
> financial serviceability of enforcement.
> ```
>
> Keep those distinct.
>
> ---
>
> # 19. RI realization check
>
> This time actually inspect the RI code before claiming priority 71.
>
> Determine:
>
> ```text
> Does ReasonOcc ever directly or indirectly mint an AnsRoot?
> ```
>
> ```text
> What exactly triggers MINT?
> ```
>
> ```text
> Can a represented reason be Due without a NormEvent effect already deciding to mint?
> ```
>
> ```text
> Is Due currently derivable, representable, or merely a semantic parameter?
> ```
>
> If RI cannot realize:
>
> ```text
> represented reason -> Due -> outstanding obligation
> ```
>
> identify the smallest missing seam.
>
> Do not add a new event kind.
>
> ---
>
> # 20. Required new countermodels
>
> At minimum:
>
> ```text
> 1. transfer -> discharge
> 2. split -> discharge one branch, leave one open
> 3. split -> discharge both branches
> 4. merge -> discharge successor
> 5. violate A2 while satisfying A1
> 6. represented reason is Due but no obligation opens
> 7. relevant reason never represented
> 8. unauthorized normative act generates a legitimate complaint
> 9. unauthorized act attempts to discharge an existing complaint
> 10. rejected normative edit whose descriptive consequences still create Due
> 11. self-ratifying resolution attempt
> 12. radical constitutional replacement with obligations correctly carried
> ```
>
> Cases 6-10 are the conceptual heart of the pass.
>
> ---
>
> # 21. Re-evaluate the number of semantic primitives
>
> At the end, compare:
>
> ```text
> Auth + Permit + Due + Disposes + Transfers
> ```
>
> ```text
> Permit + Due + Resolve
> ```
>
> ```text
> one joint LegitStep plus exposed Due projection
> ```
>
> Report:
>
> ```text
> smallest formally sufficient interface
> ```
>
> and:
>
> ```text
> smallest semantically useful interface
> ```
>
> These may differ.
>
> Prefer the second for the theorem statement.
>
> ---
>
> # 22. Decide what Legitimate Evolution actually is
>
> End by answering:
>
> ```text
> Is Legitimate Evolution:
>
> A. Grounded Replay + corrected Answerability Continuity;
>
> B. those two plus Due-realization;
>
> C. one joint local-to-global theorem;
>
> D. a named package of independent closure theorems plus one or two coupling laws;
>
> E. something else?
> ```
>
> Do not optimize for making it “one theorem.”
>
> Optimize for the smallest correct statement that deserves the intended philosophical use.
>
> ---
>
> # 23. Final compression
>
> End with:
>
> ```text
> MINIMAL LEGITIMATE-EVOLUTION STATEMENT
> ```
>
> It must fit on one page and include:
>
> * exact state carried;
> * exact local semantic inputs;
> * exact structural premises;
> * exact theorem conclusion;
> * exact role of Due;
> * whether A2 survives;
> * exact corrected answerability witness object;
> * exact coupling between normative and answerability evolution;
> * what is semantic versus structural;
> * what is explicitly deferred to Coverage / Regret / Traderization;
> * exact RI realization gap.
>
> Then give a 4-6 line whiteboard version.
>
> ---
>
> # 24. Verdict
>
> End with exactly one:
>
> ```text
> LEGITIMATE-EVOLUTION-FROZEN
> ```
>
> if the package survives these attacks and there is no remaining structural ambiguity.
>
> ```text
> LEGITIMATE-EVOLUTION-NEEDS-DUE-BRIDGE
> ```
>
> if Grounded Replay and obligation continuity are right but the represented-reason → outstanding-obligation seam remains unresolved.
>
> ```text
> ANSWERABILITY-THEOREM-NEEDS-REPAIR
> ```
>
> if the transfer/discharge issue or A2 issue prevents freezing the current kernel.
>
> ```text
> SHARED-VALID-COUPLING-FAILS
> ```
>
> if unauthorized acts creating obligations show that one acceptance bit cannot correctly gate both channels.
>
> ```text
> LEGITIMATE-EVOLUTION-DECOMPOSITION-LEAKY
> ```
>
> if the boundary between legitimacy, coverage and learning is still not clean.
>
> Do not write Lean regardless of verdict.
>
> ---
>
> The research standard for this pass is:
>
> > **A legitimate process is not merely one that preserves obligations someone handed it. Once a represented reason is, by the process's own accepted semantics, something it owes an answer to, that fact must enter the answerability dynamics; thereafter it may disappear only through a legitimate resolution path. At the same time, unauthorized normative acts must not gain the power to erase obligations, even though their occurrence may itself generate new obligations. Find the smallest local-to-global theorem that captures exactly this.**

The unauthorized-act-generates-complaint case is the one I’d pay particular attention to. It may expose that the current “same `Valid` gates both folds” coupling is too crude even though the corollary it was introduced to secure is exactly right.

---

# Eighth dispatch — 2026-08-26, the Due bridge

Verbatim as received.

Use this for the next hostile pass:

> Continue on:
>
> ```text
> round/2026-08-25-legitimate-evolution
> ```
>
> Treat the current result as:
>
> ```text
> LEGITIMATE-EVOLUTION-NEEDS-DUE-BRIDGE
> ```
>
> Do **not** write Lean.
>
> Do **not** reopen Grounded Replay unless you find an actual contradiction.
>
> Do **not** reopen quantitative liability except to preserve the already-earned conclusion:
>
> ```text
> qualitative answerability continuity does not imply quantitative burden conservation
> ```
>
> and:
>
> ```text
> total accounting, not per-parent accounting, is required for any later quantitative law.
> ```
>
> The purpose of this pass is narrower:
>
> > **Find the smallest correct local semantics and one-step transition laws for the Due bridge and answerability resolution, so that Legitimate Evolution can finally be frozen as a local-to-global theorem package.**
>
> The current candidate picture is:
>
> ```text
> local semantics:
>     Permit
>     Due
>     Resolve
>
> local structural laws:
>     grounded permitted standing change
>     newly-due -> outstanding
>     outstanding removal only by legitimate discharge/carry
>
> global theorems:
>     Grounded Replay
>     Answerability Continuity
> ```
>
> Attack this. Do not preserve it for aesthetic reasons.
>
> ---
>
> # 1. Start from the corrected answerability theorem
>
> The old chain theorem is withdrawn.
>
> The corrected intended conclusion is:
>
> > Every obligation outstanding at time `s`, at every later finite `t`, has a finite forward resolution derivation rooted at that obligation whose leaves are all either:
> >
> > * currently outstanding at `t`; or
> > * validly discharged before `t`.
>
> Transfers expand a node to the obligations that carry it.
>
> Splits create multiple children.
>
> Merges may create a DAG globally but may be unfolded into a finite derivation tree for an individual root.
>
> Verify this exact theorem against:
>
> ```text
> direct discharge
> transfer
> transfer chain
> transfer -> discharge
> split
> split -> discharge one branch, leave one open
> split -> discharge all branches
> merge
> merge -> discharge successor
> indefinite persistence
> ```
>
> Be explicit that **every frontier branch must be accounted for**.
>
> No existential “one surviving descendant is enough.”
>
> ---
>
> # 2. Remove A2 unless it earns its place
>
> Current evidence says freshness of obligation identity is not needed for the theorem.
>
> Use:
>
> ```text
> q0 -> q1 -> q0
> ```
>
> or any stronger freshness violation while preserving controlled resolution.
>
> Determine exactly:
>
> ```text
> A2 is:
>     necessary theorem premise
>     representation hygiene
>     definitional under occurrence identity
>     irrelevant
> ```
>
> My current expectation is:
>
> ```text
> representation hygiene / definitional, not a theorem premise.
> ```
>
> Do not keep a premise merely to mirror Grounded Replay.
>
> ---
>
> # 3. Tighten the one-step controlled-resolution law
>
> Current transfer rules may still be too restrictive if they require successors to be newly opened by the same edit.
>
> Test:
>
> ```text
> O_t = {q1, q2}
> ```
>
> followed by:
>
> ```text
> Resolve(q1) = carry({q2})
> ```
>
> where `q2` was already outstanding.
>
> This should probably be legitimate consolidation.
>
> Candidate minimal law:
>
> ```text
> if q leaves O_t at step t,
> then either:
>
>   Resolve_t(q) = done
>
> or
>
>   Resolve_t(q) = carry(S)
>   with S nonempty and S subset O_{t+1}.
> ```
>
> Do not require `S` to be fresh unless a countermodel proves it necessary.
>
> Test split, merge, preexisting-successor transfer, and shared successors.
>
> ---
>
> # 4. Decide exactly what `Resolve` means
>
> Compare:
>
> ```text
> Resolve(L, history, e, q) = done
> ```
>
> and:
>
> ```text
> Resolve(L, history, e, q) = carry(S)
> ```
>
> against separate:
>
> ```text
> Disposes
> Transfers
> ```
>
> Ask whether one `Resolve` judgment is enough for:
>
> ```text
> answer
> defeat
> withdrawal
> delegation
> referral
> split
> merge
> transfer into existing episode
> ```
>
> Prefer one `Resolve` unless separate primitives are needed by a downstream theorem.
>
> ---
>
> # 5. The central attack: what exactly is `Due`?
>
> Do not use a timeless predicate casually.
>
> The naive statement:
>
> ```text
> Due(L_t, r, q) -> q in O_{t+1}
> ```
>
> risks reopening already-resolved obligations forever if `r` remains represented.
>
> Build:
>
> ```text
> r is represented at t=0
> Due(r,q)
> q opens
> q is legitimately discharged at t=5
> r remains in the reason ledger forever
> ```
>
> Ask whether the current Due semantics forces `q` to reopen.
>
> If yes, reject that semantics.
>
> ---
>
> # 6. Compare three candidate Due interfaces
>
> Test at least:
>
> ```text
> A. persistent predicate
>    Due_t(r,q)
> ```
>
> ```text
> B. event-like judgment
>    NewDue_t(r,q)
> ```
>
> ```text
> C. transition generator
>    Due(X_t, new represented material at t) = finite set of new obligation payloads
> ```
>
> Find the smallest interface that:
>
> * does not reopen resolved obligations;
> * can represent old reasons becoming newly due after context changes;
> * can represent several reasons jointly generating one obligation;
> * can represent one reason generating several obligations;
> * does not smuggle Coverage into legitimacy.
>
> Do not assume `ReasonOcc arrival == Due event`.
>
> ---
>
> # 7. Old reason becoming newly due is mandatory
>
> Build:
>
> ```text
> r exists in the reason ledger from t=0
> at t=0 it is not Due
> normative/context state changes at t=5
> at t=5 the same old r now makes q newly due
> ```
>
> A design that only mints obligations when a `ReasonOcc` is first created is too weak if this case is legitimate.
>
> Determine whether Due should be evaluated over:
>
> ```text
> represented reason ledger + strict prestate
> ```
>
> and produce **newly activated due claims** relative to prior answerability history.
>
> ---
>
> # 8. Several reasons jointly creating one obligation
>
> Test:
>
> ```text
> r1 alone: not due
> r2 alone: not due
> {r1,r2} together: q becomes due
> ```
>
> Do not force one obligation to have exactly one reason parent unless necessary.
>
> This may suggest:
>
> ```text
> Due(X_t, support_set, q)
> ```
>
> or a derived activation condition over the whole represented reason state.
>
> Keep the interface as small as possible.
>
> ---
>
> # 9. One reason creating several obligations
>
> Test:
>
> ```text
> r -> {q1,q2}
> ```
>
> e.g. one represented failure creates:
>
> ```text
> obligation to repair
> obligation to explain
> ```
>
> The Due bridge must handle this without special machinery.
>
> ---
>
> # 10. Distinguish Due from Coverage
>
> Required cases:
>
> ```text
> relevant reason never represented
> ```
>
> should remain:
>
> ```text
> Legitimate Evolution YES
> ```
>
> while:
>
> ```text
> reason represented
> local Due semantics activates q
> q never enters answerability
> ```
>
> should be:
>
> ```text
> Legitimate Evolution NO
> ```
>
> State the distinction formally.
>
> Coverage concerns:
>
> ```text
> whether relevant world failures/reasons become represented
> ```
>
> Due concerns:
>
> ```text
> what the process's semantics says follows normatively from represented material.
> ```
>
> Do not mix them.
>
> ---
>
> # 11. Do not gate Due-openings by normative `Permit`
>
> Preserve the key countermodel:
>
> ```text
> unauthorized act occurs
> normative standing change is rejected
> fact of the act is represented
> that fact makes complaint q due
> ```
>
> Desired:
>
> ```text
> normative effect: rejected
> answerability opening: accepted
> ```
>
> This should remain representable.
>
> Thus do not use:
>
> ```text
> one Valid bit gates all effects.
> ```
>
> ---
>
> # 12. Find the exact asymmetric local gates
>
> Current guess:
>
> ```text
> normative standing effect:
>     gated by Permit
>
> obligation opening:
>     generated by Due
>
> obligation discharge/carry:
>     gated by Resolve
> ```
>
> Test whether these three are genuinely independent.
>
> Required examples:
>
> ```text
> unauthorized action creates complaint
> unauthorized attempted discharge fails
> ordinary Response discharges without changing normative standing
> normative amendment changes standing without opening or resolving anything
> represented evidence opens an obligation without any NormEvent
> ```
>
> If one joint `LegitStep` relation can represent these cleanly without losing useful factorization, report that.
>
> Otherwise retain three semantic projections.
>
> ---
>
> # 13. `Resolve` must read legitimate strict prestate
>
> We still need:
>
> ```text
> an actor cannot use authority it just created to resolve an obligation
> ```
>
> and:
>
> ```text
> an unentitled actor cannot erase an obligation.
> ```
>
> Require resolution semantics to be evaluated against the legitimate prestate:
>
> ```text
> Resolve(L_t, O_t, represented history, event, q)
> ```
>
> Test:
>
> ```text
> self-authorize then discharge in same step
> ```
>
> It should fail unless the old prestate already permits the resolution.
>
> ---
>
> # 14. Same-step Due and Resolve
>
> Test:
>
> ```text
> an event reveals a problem and simultaneously provides a complete legitimate answer
> ```
>
> Is it necessary for `q` to appear in an intermediate outstanding set?
>
> Compare:
>
> ```text
> Due -> open q -> resolve q in same step
> ```
>
> versus:
>
> ```text
> Due claim gets an immediate resolution witness and never appears in O_{t+1}
> ```
>
> Choose the cleaner semantics.
>
> The global theorem must still have a resolution derivation for that due claim.
>
> Do not let “same-step resolution” become a loophole for silently ignoring Due.
>
> ---
>
> # 15. Decide whether answerability identity is semantic or structural
>
> If a due claim is immediately resolved, it may still need a proof-relevant identity so the global theorem can say:
>
> ```text
> this due claim was handled.
> ```
>
> Ask whether the minimal object should be:
>
> ```text
> Claim occurrence
> ```
>
> minted by Due even when not live after the step.
>
> This may parallel `Admitted` versus `Live` on the entitlement side.
>
> Do not add identity unless the theorem actually needs it.
>
> ---
>
> # 16. Try an `Admitted obligation` / `Outstanding obligation` distinction
>
> Grounded Replay benefited from distinguishing:
>
> ```text
> Admitted
> Live
> ```
>
> There may be an exact answerability analogue:
>
> ```text
> Incurred_t
> Outstanding_t
> ```
>
> where:
>
> ```text
> Incurred
> ```
>
> records every obligation ever generated by Due,
>
> and:
>
> ```text
> Outstanding
> ```
>
> is those not yet legitimately resolved.
>
> This would make the global theorem naturally quantify over:
>
> ```text
> every incurred obligation
> ```
>
> rather than over whatever happens to be outstanding at some chosen start time.
>
> Test whether this substantially cleans up same-step resolution and Due-realization.
>
> ---
>
> # 17. Candidate local-to-global theorem
>
> Try to derive:
>
> ```text
> For every due-generated obligation occurrence q incurred by time t,
> there is a finite resolution derivation rooted at q whose leaves
> are all either:
>
>     validly discharged occurrences
>
> or
>
>     obligations currently outstanding at t.
> ```
>
> This is likely the answerability theorem Legitimate Evolution actually wants.
>
> Compare this with the older:
>
> ```text
> every q outstanding at s ...
> ```
>
> Decide which is more primitive and useful.
>
> ---
>
> # 18. Reassess the package after Due is added
>
> Candidate:
>
> ```text
> LOCAL SEMANTICS
>     Permit
>     Due
>     Resolve
>
> STRUCTURAL LAWS
>     S1/S2
>     D1 every newly-due claim is incurred
>     A1 every outstanding removal has a Resolve witness
>
> GLOBAL
>     Grounded Replay
>     Answerability Resolution
> ```
>
> Ask whether `D1` and `A1` are the only answerability-side premises.
>
> If yes, produce one countermodel for dropping each.
>
> Required:
>
> ```text
> drop D1:
> represented due claim is ignored
> ```
>
> ```text
> drop A1:
> incurred/open claim disappears silently
> ```
>
> These should fail for genuinely different reasons.
>
> ---
>
> # 19. Ask if D1 can be definitional
>
> Be suspicious.
>
> If the type of the model defines:
>
> ```text
> incurred := all Due outputs
> ```
>
> then:
>
> ```text
> Due -> incurred
> ```
>
> is no longer a premise; it becomes true by construction.
>
> That may be correct, or it may repeat the earlier mistake where A1 became unfalsifiable.
>
> Try to build:
>
> ```text
> semantics says q is newly due
> implementation fails to record q
> ```
>
> If the model cannot represent this failure, D1 is hidden in the type.
>
> Decide whether Legitimate Evolution should treat Due-realization as:
>
> ```text
> semantic definition
> ```
>
> or:
>
> ```text
> conformance premise at the realization boundary.
> ```
>
> This distinction matters.
>
> ---
>
> # 20. Inspect RI now, carefully
>
> Actually inspect the current RI implementation/spec.
>
> Determine:
>
> ```text
> what creates AnsRoot?
> what `MINT` means exactly?
> whether ReasonOcc can affect root creation
> whether old reasons are re-evaluated after normative/context changes
> what RI's existing `due()` predicate means
> whether Response can settle a root without NormEvent
> whether continuity_ok already works over incurred/history rather than only live roots
> ```
>
> Do not infer from names.
>
> Quote exact types/transition rules in the round notes.
>
> ---
>
> # 21. Do not immediately add a reason-keyed MINT
>
> The tempting repair is:
>
> ```text
> ReasonOcc -> Due -> AnsRoot
> ```
>
> but old-reason-becomes-newly-due may refute “mint on reason arrival.”
>
> Compare:
>
> ```text
> reason-keyed minting
> ```
>
> ```text
> due-activation step over the whole represented reason state
> ```
>
> ```text
> answerability projection derived after each replay step
> ```
>
> Pick the smallest RI seam that can realize the abstract theorem.
>
> Do not add a fifth event kind.
>
> ---
>
> # 22. Re-check the philosophical boundary
>
> Required legitimate cases:
>
> ```text
> radical value change
> constitutional replacement
> permitted persuasion
> high regret
> failure never observed
> obligation left open forever
> legitimate reassessment that reduces burden
> ```
>
> Required illegitimate cases:
>
> ```text
> ex-nihilo entitlement
> represented Due claim ignored
> silent obligation deletion
> unauthorized discharge
> transfer to empty frontier
> one split branch silently lost
> ```
>
> If the theorem does not separate these automatically, keep working.
>
> ---
>
> # 23. Keep quantitative liability downstream
>
> Do not put a weight in the generic theorem.
>
> Preserve:
>
> ```text
> a successor may legitimately change substantive burden
> ```
>
> because `Resolve` decides whether it genuinely carries the predecessor.
>
> Any later quantitative law should be:
>
> ```text
> an extra semantic restriction / consumer theorem
> ```
>
> not part of the structural Legitimate Evolution kernel.
>
> ---
>
> # 24. Final theorem target
>
> Aim for something approximately:
>
> ```text
> LEGITIMATE EVOLUTION
>
> Given local semantics Permit, Due, Resolve and a finite represented history:
>
>   1. standing effects obey Grounded Replay's local premises;
>
>   2. every newly activated Due claim is incurred;
>
>   3. an outstanding claim can cease to be outstanding only through
>      a locally legitimate Resolve judgment whose carried frontier is nonempty
>      and lies in the next outstanding state;
>
> then for every finite t:
>
>   E. every live standing has finite legitimate ancestry to the accepted base;
>
>   A. every incurred answerability claim has a finite resolution derivation
>      whose leaves are all validly discharged or currently outstanding.
> ```
>
> Semantic consequence:
>
> ```text
> the process can change substantive normative content arbitrarily,
> but cannot manufacture entitlement, ignore a claim its represented reasons
> newly make due, or erase such a claim without a legitimate resolution history.
> ```
>
> Do not force this exact statement if the countermodels improve it.
>
> ---
>
> # 25. Decide the theorem/package status
>
> Explicitly answer:
>
> ```text
> Is Legitimate Evolution now:
>
> A. one theorem;
> B. two local-to-global theorems plus a Due-realization premise;
> C. a named package of Grounded Replay + Answerability Resolution;
> D. a semantic transition definition with two global corollaries;
> E. something else?
> ```
>
> Again, do not optimize for grandeur.
>
> ---
>
> # 26. Final compression
>
> End with:
>
> ```text
> MINIMAL LEGITIMATE-EVOLUTION KERNEL
> ```
>
> It must fit on one page.
>
> Include:
>
> * state;
> * semantic primitives;
> * exact Due notion;
> * exact local premises;
> * exact resolution witness object;
> * exact theorem conclusions;
> * one countermodel per non-definitional premise;
> * whether D1 is structural or realization-level;
> * exact asymmetric gating;
> * exact RI realization;
> * what remains outside: Coverage, Regret, quantitative liability, certification.
>
> Then give:
>
> ```text
> WHITEBOARD VERSION
> ```
>
> in no more than six lines.
>
> ---
>
> # 27. Verdict
>
> End with exactly one:
>
> ```text
> LEGITIMATE-EVOLUTION-FROZEN
> ```
>
> if the Due bridge and resolution law survive the hostile cases and the RI realization seam is clear.
>
> ```text
> DUE-SEMANTICS-UNSTABLE
> ```
>
> if persistent/newly-due/joint-reason cases prevent a clean semantic interface.
>
> ```text
> DUE-REALIZATION-GAP
> ```
>
> if the abstract theorem stabilizes but RI cannot yet realize it.
>
> ```text
> ANSWERABILITY-RESOLUTION-UNSTABLE
> ```
>
> if the corrected frontier/transfer semantics still fails.
>
> ```text
> LEGITIMATE-EVOLUTION-DECOMPOSITION-LEAKY
> ```
>
> if the theorem again starts importing Coverage, progress, regret, or substantive correctness.
>
> Do not write Lean regardless of verdict.
>
> ---
>
> The research standard is:
>
> > **Do not let “Due” mean “this reason remains eternally unresolved,” and do not let the answerability theorem merely preserve a docket someone handed it. Identify the exact moment a represented reason creates a new normative claim, ensure that claim enters the process, and then prove that arbitrary future evolution cannot lose any branch of what became owed except through a legitimate resolution.**

This is the pass where I’d especially want the agent to attack whether `D1` is actually a theorem premise or a realization/conformance condition. That feels like the same class of mistake the earlier rounds repeatedly caught: a morally important sentence can live at a very different layer from the mathematical induction.
