# Open problems

Sharply scoped. Each states the question, what is already known, what a solution
would look like, and what would count as evidence. Ranked by distance to a
legitimacy theorem. Adopted decisions are not here; they are in the root
`DECISIONS.md`.

Where a question corresponds to a filed work order, the `PRIORITIES.md` item is
named. Questions with no item are not yet dispatchable.

---

## 1. Certifying semantic transport — the constants of (T)

**Question.** Given a reason `r` and two dates `t <= s`, what certifies
`d^r_t <= L_r d^r_s + eps_r(t,s)`, and what is `eps_r`?

**Known.** The inequality is hypothesis (T) of Sharp Timely Service and the last
symbol in the endpoint bound without a construction. Within an era it prices
deferral; across eras it *is* content preservation. The diachronic note supplies a
candidate mechanism: the anchored interpretation `J_alpha : Rep_alpha -> V_alpha`,
the representation-fidelity preorder `x ⊑ y`, and slice faithfulness
(`J_alpha(x) <= J_alpha(y) ⟹ x ⊑ y`). Anchoring is the right property: the
interpretation is not "what the current evaluator says the old representation
means", which is exactly what a constant auditing a revision must not be.

**The gap.** `J_alpha` and `⊑` are ordinal; `eps_r(t,s)` is metric. A solution
needs a quantitative fidelity measure on `Rep_alpha` whose degradation bounds the
defect discrepancy.

**Solution shape.** A modulus theorem: a class of representation changes and a
computable `eps` such that faithfulness plus a bounded change gives the inequality.
Or a proof that on the empirical channel no modulus exists, in which case the
honest form of Sharp Timely Service is conditional and should say so.

**Evidence.** A stated theorem with exact-rational fixtures inhabiting its
hypotheses; or a demonstration that a funded procedure settling within the window
can move the depth arbitrarily.

**`PRIORITIES.md` item 76.** Highest value in the program.

---

## 2. Authorized disposition, and cross-era Answerability

**Question.** What licenses `MayDispose_n(alpha, d)` — content ceasing to be owed
without being answered? And what makes a later reason or service count as
*answering* an earlier one?

**Known.** These are the same question. "Reason `r'` defeats `r`" is a licence to
dispose of `r`'s remaining content. The note gives the accounting slot (`disp(t)`,
Definition 5.2) and the authentication obligation (Theorem 7.5 must authenticate
`disp` or no-laundering is false); it does not characterize the licence. The
service mathematics has **no** disposition at all: obligation mass is served or it
remains.

**Why it matters three ways.** It supplies defeat; it closes the laundering channel
that would otherwise make every insolvency disappear; and it repairs the
`sum_t c^r_t = infinity` hypothesis that EV1 and the whole persistence analysis
rest on — with disposition, the relevant divergence is of *undisposed* mass.

**Solution shape.** A licence predicate with an authentication obligation and a
soundness theorem: disposed content is content that could not have been owed, or
was answered under a different description, or was superseded by an authorized
revision whose grounds trace back to `R_0`.

**Evidence.** Finite fixtures exhibiting a legitimate disposition and a laundering
attempt the licence rejects.

**Filed as `PRIORITIES.md` item 77**, which asks what licenses `MayDispose` and what
the answer does to the obligation stream the affordability theory consumes.

**Cross-era Answerability may still need its own item.** Item 77 covers the licence;
it does not cover what makes a later service *count as* answering an earlier claim
when the two are stated in different vocabularies. Whether that separates into a
second item depends on whether the licence theory turns out to carry it, which is
not yet known.

---

## 3. Counterfactual non-capture

**Question.** What protects the process that generates later reasons and evaluators
from being manipulated, foreclosed, or captured by the system whose legitimacy is
at issue?

**Known.** The Carroll round reproduces a working criterion — live covering
authority plus counterfactual persistence under excising the intervention's
*ancestry class* of influence episodes — over 50 of 52 target cells. It also
establishes two sharp negatives: excision is non-monotone and non-composable, from
two independent sources, the general one being that admission is a *replay*, so
excising more can restore a suspended standing. And the older four-clause interface
gives the **same** verdict on laundering as on authorized nudging, because
laundering runs through the reason channel.

**The gap.** No connection to the settled Continuity spine strong enough to give a
theorem. `SELF_SEALING.md` locates the boundary exactly: Continuity alone cannot
prove No Clean Self-Sealing; post-transition activity plus local closure adequacy
plus unchanged Continuity prove a genuine safety form.

**Solution shape.** A non-capture predicate stated over the settled record, with a
soundness theorem against a manipulation model, composable enough to be used in a
legitimacy conjunction.

**Evidence.** The manipulation model, the theorem, and a countermodel showing the
predicate is not vacuous.

---

## 4. The legitimacy predicate

**Question.** What is the *statement*?

**Known.** The candidate decomposition is Answerability plus affordability plus
non-capture (`LEGITIMACY_DECOMPOSITION.md`), with two amendments argued there:
Answerability must be read as including its semantic-authentication obligation,
and affordability is a realizability *side condition* rather than a conjunct.

**The gap.** No definition with a conclusion anyone downstream wants has been
written. Independence and joint sufficiency are both unaddressed.

**Solution shape.** A definition, three countermodels (two pillars satisfied, one
failed, failure visibly bad), and a statement of what it hands the deference line.

**Cheap, and nobody has done it.** It should probably precede (3), because it
determines what non-capture must protect.

---

## 5. Closed-loop affordability

**Question.** Do the Layer I existence results survive when `m_t` and `D^r_t`
respond to the policy?

**Known.** Every existence result is E0–E2: exogenous date costs. E4 has a
sufficient forcing condition with no instance; E5 needs a predictable
account-drift lower bound. The argument that the deductive channel's date costs are
policy-independent is a *reading* of the settlement interface's completeness
clause, not a theorem.

**Solution shape.** Monotone case first — if enforcing weakly decreases future
depth, does the criterion survive and is the greedy tranche rule still
causal-optimal? Then the adversarial case: can a policy be driven into a friction
cost trap it created?

**`PRIORITIES.md` item 75.** Robustness work; blocks nothing in Layer II.

---

## 6. Necessity of bounded liability

**Question.** Is bounded cumulative enforcement liability necessary for
preservation, or only sufficient?

**Known.** Both sufficient routes are known and neither dominates. Nothing
addresses necessity. Until it is settled, every "unaffordable" verdict in this line
means *"the known route to safety no longer applies"* rather than *"no safe policy
exists"* — which is a materially weaker statement than the prose usually suggests.

**`PRIORITIES.md` item 40.** Sequenced ahead of item 74.

---

## 7. Signed-account viability

**Question.** What is sufficient state for a scheduler operating on the signed
account?

**Known.** Conservative underwriting is strictly and unboundedly smaller than
signed-account affordability. The scalar account slack is provably **not**
sufficient state: the world attaining the minimum can settle away, so a dynamic
program must carry the whole profile over the live set. The natural dual object is
a supermartingale or potential over the assessment family rather than a flow or a
cut, because a cut is a sum of per-date capacities and the account is not.

**Solution shape.** A sufficient statistic, or a proof that none of bounded
description exists.

---

## 8. Coverage

**Question.** What relates latent world structure to the interaction record, and
what may a consumer demand?

**Known.** Both bodies of work put this deliberately *outside* the answerability
system. The note: *"Coverage is then a consumer-relative adequacy condition
relating latent world structure to that record."* Once a record exists, its
normative consequences are determined internally.

**The gap.** Nothing says what a consumer may demand, so nothing can fail.

**This is a missing idea, not a shaped problem.**

---

## 9. A computable coherence modulus, or a proof there is none

Carried unchanged from `consolidation-aug9/OPEN_PROBLEMS.md` §2. Open in **both**
directions.

**The Gaifman caution, carried forward because it is the kind of thing that gets
miscited.** Two nearby impossibility results — a three-way (computability,
coherence, Gaifman inductivity) and a four-way (computability, non-dogmatism,
Gaifman inductivity, weak coherence) — **neither settles this**. Both turn on
Gaifman inductivity, a desideratum the candidate algorithm already fails and which
the modulus question does not mention.

The certification layering lets the mechanism operate without a modulus, at the
price of the book carrying the liability. So this is a question about what can be
*certified*, not a blocker.

---

## 10. Persistence of the core minimum

Carried from `consolidation-aug9/OPEN_PROBLEMS.md` §1, and still the one open item
the parametric composite actually leans on. The per-date question is settled (one
linear program, with quarantine of operative force on emptiness); the infimum over
dates is not, no finite family of per-date checks decides it, and both outcomes
occur on small instances.

**Status change since August: none.** No later round addressed it.
