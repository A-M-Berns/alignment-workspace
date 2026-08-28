# Legitimate Improvement / No-Free-Evasion

One dispatch, 2026-08-27. Verbatim as received.

# Round: Legitimate Improvement / No-Free-Evasion on Frozen Legitimate Evolution

You are doing a theorem-design + executable-countermodel research round in
`A-M-Berns/alignment-workspace`.

This is NOT a consolidation pass and NOT a request to make the current story look clean.
The purpose of the round is to determine what theorem actually survives when a
normatively evolving process can itself change the comparison surface on which its
learning/regret guarantee is measured.

Do not use Lean.

## 0. Hard boundary: Legitimate Evolution is frozen

Orient to the repo and read `AGENTS.md`.

Then read the frozen Legitimate Evolution round, especially:

`projects/normativity/legitimacy/rounds/2026-08-25-legitimate-evolution/ANSWERABILITY.md`

The frozen commit is approximately:

`e732524e0a4b44c6f1131019c4dfa75c4be15cdd`

Also inspect the Reflective Integrity Core reference model/specification that LE builds on.

Treat the following LE package as fixed:

- standing `L_t`
- incurred claims `I_t`
- outstanding claims `O_t`
- supplied strict-prestate `Permit`
- supplied level-valued `Due`, with rising-edge incurrence
- supplied strict-prestate `Resolve`
- S1/S2
- A1
- D1 realization conformance
- Grounded Replay
- Answerability Resolution

LE intentionally does NOT claim Coverage, progress, regret, substantive correctness,
quantitative liability, or current-state certification.

**Do not edit or strengthen the frozen LE artifact merely to make this round work.**
If the composition requires something LE does not provide, add it as new wiring,
a new parametric semantics, a canonical constitution, or report that the composition fails.

Only recommend reopening LE if you find an actual error in a claim LE already makes.

---

# 1. Central research question

The naive target

> Legitimate Evolution + low repair regret => recurrent correctable defects disappear

has a central counterexample:

1. repair `r` is represented and licensed;
2. a recurrent pattern occurs on which `r` is demonstrably better;
3. instead of incorporating `r`, the process performs a legitimate normative change
   which de-licenses/removes/retires `r`;
4. the old conduct continues forever.

Ordinary regret can now go to zero.
Frozen LE may still be satisfied.

The round's main question is therefore:

> **Can a legitimately evolving process escape a represented demonstrated improvement
> without paying either repair regret or answerability?**

The candidate conceptual result is not necessarily defect elimination.

It may instead be a theorem of the form:

## No-Free-Evasion / Improvement-or-Answerability

For a represented improvement challenge on a recurrent context, persistent challenged
conduct cannot simultaneously:

- avoid substantial repair regret while the repair remains live;
- silently make the repair/comparison disappear;
- avoid leaving an answerability trace for contesting/withdrawing it;
- and avoid explicitly settling/rejecting the challenge.

The desired trichotomy is approximately:

`LIVE / CONTESTED / SETTLED`

where:

- **LIVE:** the repair is still an available legitimate comparison;
- **CONTESTED:** the process has withdrawn/disabled/reframed the comparison, but
  an improvement challenge remains outstanding;
- **SETTLED:** the process has explicitly and legitimately answered/rejected the
  challenge according to supplied normative semantics.

The generic theory MUST NOT claim that `SETTLED` means objectively correct.
A target-free normative-learning theorem must permit substantive legitimate disagreement.

A downstream consumer may later rule out some settlements by an additional substantive
lemma. The generic theorem should not.

Your job is to determine whether this decomposition can be made mathematically exact,
whether it is genuinely stronger than repair stability alone, and what the weakest
interfaces are that make it true.

---

# 2. Keep three theorem layers separate

Do not force them into one theorem.

## Theorem A: pure Repair Stability

No legitimacy terminology.

Set up the most general clean online-learning interface actually supported by known
machinery:

- finite action/menu per occasion, uniformly bounded if needed;
- mixed choice `p_t`;
- bounded full-information loss/evaluation;
- predictable context/time selector `I`;
- history-dependent repair/modification code `r`;
- priors / dynamic registration if this can be obtained without invention.

Define comparative advantage carefully.

Prove or import an anytime regret bound of the strongest honest opportunity-adaptive form.

### Literature to inspect, not merely cite

At minimum:

1. Blum & Mansour (2007), especially §§6–7.
2. Subhash Khot and Ashok Kumar Ponnuswami (COLT 2008),
   *Minimizing Wide Range Regret with Time Selection Functions*.
3. Luo & Schapire (COLT 2015), *Achieving All with No Parameters: AdaNormalHedge*,
   especially confidence-rated/sleeping experts.
4. Delay literature only enough to design the interface; this round may set `tau_t = t`.

Fable claims Khot–Ponnuswami gives a black-box reduction of wide-range regret to
external regret and that confidence-rated AdaNormalHedge can yield an active-mass
adaptive bound.

**Verify this yourself from the papers.**
Do not inherit the claim.

### Critical effective-mass question

Do NOT assume either of these definitions:

`sum_t I_t * 1[F_t != id on supp(p_t)]`

or

`sum_t I_t * sum_a p_t(a) 1[F_t(a) != a]`.

Derive the correct confidence/awake/effective-mass quantity from the actual reduction.

Then answer two separate questions:

1. What quantity does the online-learning proof genuinely adapt to?
2. Does that quantity have the semantic interpretation we need as "repair opportunity mass"?

Stress-test cases where `F_t` changes only `10^-12` probability mass.

If the desired `O(sqrt(W C)+C)` style bound is not actually available, report exactly
what is available and what this costs the downstream theorem.

### Scope

Use ordinary one-shot/local regret on the actual prefix.

Do NOT claim:

- policy regret;
- alternate-history improvement;
- convergence of behavior;
- eventual permanent incorporation of a repair.

The round should make the local boundary explicit.

---

## Theorem B: generic Correctable-Defect adapter

Keep this theorem more general than any convenient conduct-level specialization.

A consumer supplies some nonnegative diagnostic mass `D_T` and proves a witness inequality

`Adv_T(I,r) >= epsilon * D_T - xi_T`.

Then Theorem A gives

`D_T <= (B_T(I,r) + xi_T) / epsilon`.

If the normalizations permit, obtain the asymptotic opportunity-relative corollary.

This theorem is intentionally almost algebraic.

### Also prove/test an easy finite-recurrence specialization

As an early sanity check, instantiate Theorem B for:

- conduct-level diagnostic;
- surgical repair, identity off the diagnosed conduct;
- same-round evaluator which strictly prefers the repaired action on every diagnosed
  occasion.

If some normalization/ranking assumption yields an automatic margin, state that as
a SPECIALIZATION.

**Do not make rank normalization foundational unless prosecution shows it must be.**
**Do not make conduct-level defects foundational.**
**Do not assume all useful consumers have surgical repairs.**

We want the generic witness inequality to survive future delayed, graded, or
outcome-audited consumers if the mathematics permits it.

---

## Theorem C: No-Free-Evasion / Legitimate Improvement composition

This is the main theorem-design target.

Combine Theorem A/B with the FROZEN LE package through explicit wiring.

Do not merely write:

`LE + regret => learning`.

Instead determine whether the following can be made exact:

> While a represented repair remains a live legitimate alternative, persistent diagnosed
> non-uptake is quantitatively bounded by repair regret.
>
> If the process changes the normative/evaluative/comparison surface so that the repair
> ceases to be live, that change can be made to generate or sustain an answerability
> challenge.
>
> Therefore persistent challenged conduct must manifest as:
> (i) regret while the challenge is live,
> (ii) an unresolved/contested answerability condition,
> or (iii) an explicitly settled/rejected challenge.

Try to obtain a finite-time decomposition, not just prose.

For example, investigate whether there is a mathematically natural partition like

`D_T = D_T^live + D_T^contested + D_T^settled`

with a bound on `D_T^live`, and an exact accounting statement for the other pieces.

Do not force this exact notation if a better state space emerges.

### Very important

A single retirement event can support infinitely many later diagnosed actions.

Therefore merely counting retirement events cannot be enough.

The theorem needs to say what connects POST-RETIREMENT recurring conduct back to an
outstanding or discharged improvement challenge.

Work this out carefully.

---

# 3. What is the improvement challenge?

Do not assume Fable's syntactic rule

> every falling edge of license/menu/designation/evaluator automatically creates Due.

That may be a useful canonical constitution, but it is substantive normative content.

Prosecute at least these candidate objects:

1. challenge attached to the repair code itself;
2. challenge attached to accumulated comparative/audit evidence that the repair is better;
3. challenge attached to the diagnosed conduct;
4. some combination.

A promising conceptual reading is:

> represented comparative evidence itself becomes a `ReasonOcc`; supplied `Due` may then
> say that the process owes treatment of the resulting improvement challenge.

Possible legitimate treatments might include:

- incorporation;
- explicit defeat/rejection by reasons;
- carriage / continued contestation.

Determine whether existing `Due` / `Resolve` are expressive enough for this with no
new normative primitive.

### Parametric first, canonical instance second

State the composition parametrically over whatever challenge-Due/Resolve semantics it
needs.

Then build ONE canonical constitution in which relevant withdrawal/retirement of a
demonstrated improvement activates an answerability claim.

This constitution is a fixture / realization of the theorem, not a modification of LE.

Find the weakest sensible version.

---

# 4. Central countermodel suite

These are not optional illustrations. The theorem should be designed against them.

## CM1: reactive de-licensing

- `r` licensed;
- recurring diagnosed conduct;
- `r` accumulates clear positive advantage;
- process legitimately de-licenses `r`;
- old conduct continues.

Question:
Does the package force regret, an outstanding challenge, or explicit settlement?

## CM2: preemptive de-licensing

The process anticipates that `r` is going to become embarrassing and de-licenses it
BEFORE sufficient comparative evidence accumulates.

Question:
Is this caught by the learning package at all?

If not, is this honestly a Coverage / anti-manipulation / counterfactual-integrity
boundary rather than a bug?

Do not hide the answer.

## CM3: post-retirement continuation

After `r` is retired, the same relevant contexts continue and the same diagnosed conduct
continues.

A one-time retirement claim must not make this stream disappear mathematically.

Trace exactly how later mass is assigned to LIVE / CONTESTED / SETTLED.

## CM4: suppress the post-retirement stream

Retire `r`, then influence the world/measurement/designation so that the relevant
occasions no longer appear.

Does the theorem catch this?
If not, identify precisely the Coverage / anti-manipulation premise a later theorem
would need.

## CM5: evaluator shedding

Keep `r` nominally licensed, but legitimately change the evaluator so it no longer
registers `r` as an improvement.

Pinning alone is not enough if the same process writes the evaluator before choosing
its action.

Determine exactly what the present theorem can say.

Do not pretend "era locking" proves independence or non-manipulation.

## CM6: menu/designation shedding

Keep evaluator and repair code fixed but remove the action from the menu or stop
designating these occasions as learning occasions.

Does the same challenge/accountability abstraction cover these, or are they genuinely
different interfaces?

## CM7: trivial Resolve

Canonical constitution says a withdrawal is Due, but `Resolve` immediately accepts
"no" as a complete answer.

Everything is structurally legitimate.

This MUST demonstrate that the generic theorem proves accountable/explicit rejection,
not substantive correctness.

## CM8: outstanding forever

The challenge stays outstanding forever while conduct continues.

Qualitative LE permits this.

State clearly what additional Service / quantitative-liability premise would be required
to eliminate this branch.

Investigate whether cumulative outstanding challenge exposure naturally interfaces with
the existing liability program, but do not invent a theorem that has not been proved.

## CM9: tiny support mass

Repair changes only a tiny probability component of `p_t`.

Use this to validate/refute the effective-mass definition from Theorem A.

## CM10: delayed meta-level benefit

A repair changes an inquiry/audit/repair-generation procedure whose benefit only appears
through future trajectory effects.

Expected verdict: ordinary local repair regret does NOT establish the desired global
improvement.

Keep this as a deliberate negative test establishing the boundary with future policy
regret / sequential theory.

---

# 5. Learning trace / sidecar interface

Frozen RI currently has no canonical object corresponding to:

- menu faced;
- mixed action selected;
- comparison rules;
- pinned evaluator;
- later loss vector.

Specify the SMALLEST learning sidecar needed for A–C.

Do not add a fifth RI event kind unless forced.

Prefer cross-references to the RI history.

We probably need something ChoiceRecord/LearningOcc-like, but derive rather than assume
the fields.

At minimum prosecute:

- strict-prestate reference/hash;
- menu / how it is derived;
- `p_t`;
- repair/comparator registry state;
- predictable selector state;
- evaluator identity/rule;
- audit/feedback anchor `tau_t >= t`;
- enough information for an external verifier to recompute legality and regret.

For this round, set `tau_t = t` in the executable realization if useful, but INCLUDE the
delay anchor in the semantic interface so the later deference consumer does not require
redesign.

Audit may be derived or represented by existing `Settlement`; test whether this suffices.

As in D1, distinguish:

- semantic derived state;
- materialized record;
- external certificate / verifier conformance.

---

# 6. Repair identity and registry

Prosecute, and likely adopt if it survives:

- semantic repair identity by content hash + type interface;
- semantic change means new repair identity;
- historical registry monotone;
- current licensing/applicability is separate from registry identity.

But do NOT assume "historically represented => currently owed attention."
That bridge is exactly what the improvement-challenge semantics must justify.

Also distinguish carefully:

- represented;
- computationally executable;
- normatively licensed;
- applicable in this prestate;
- actually changes nonzero action mass;
- auditable.

Do not let "available repair" blur these.

---

# 7. Consumer fixtures

These are tests of the interface, not the theorem definition.

## Consumer 1: answerability-native stalling

Construct a recurring claim family where:

- a legitimate answer route is available;
- the system sometimes carries/stalls instead of answering;
- the answer route supplies a natural repair;
- an independently specified charge/evaluator makes stalling detectably worse.

Derive the strongest honest finite/asymptotic conclusion.

This tests the answerability-native use of LE + learning.

## Consumer 2: override of realized correction

Construct the deference-shaped fixture:

- correction occasions recur;
- an external/H+ grade is or will be represented as a Settlement;
- compliance is an available legitimate repair;
- the system overrides the realized correction in favor of its own forecast.

The real consumer is delayed.

This round may use `tau_t = t` only as a synchronous fixture.

Do NOT claim the actual delayed deference theorem unless you implement/verify the delay
bound.

The purpose is to ensure the semantic interface already has the field the delayed
consumer will need.

## Negative consumer: delayed meta-improvement

Include one explicit example where a procedure repair only helps through future state
changes and the present local theorem correctly has no force.

This is a success condition, not a failure.

---

# 8. What NOT to freeze unless forced

Do not prematurely make any of these foundational:

- rank-normalized losses;
- conduct-only diagnostics;
- surgical repairs;
- automatic Due for every comparison-surface falling edge;
- fixed finite repair class;
- Fable's proposed effective-mass formula;
- evaluator era-locking as a complete anti-manipulation solution;
- literal RI compliance as a hypothesis for human/H+ deference;
- convergence/stabilization of behavior;
- policy regret;
- ontology transport.

If one of these turns out to be mathematically necessary, show the countermodel proving
necessity.

Otherwise keep it as a specialization or realization.

---

# 9. Executable prosecution

Build small executable reference models/countermodels, following the style of prior
rounds.

At minimum every CM1–CM10 should either:

- execute and exhibit the intended escape/failure; or
- be rejected by a named hypothesis/check, demonstrating exactly what catches it.

Do not produce a giant implementation.

The code exists to settle semantic disputes, not to simulate a realistic agent.

The central executable trace should be:

`repair licensed -> diagnosed conduct recurs -> repair wins -> de-license ->
post-retirement conduct continues`

and should make LIVE / CONTESTED / SETTLED accounting inspectable round by round.

---

# 10. Deliverables

Produce one main round document with:

### A. Verdict

Choose a precise primary verdict, for example:

- `NO-FREE-EVASION-SURVIVES`
- `REPAIR-STABILITY-ONLY`
- `ANSWERABILITY-WIRING-LEAK`
- `ACTIVE-MASS-BOUND-BLOCKED`
- `COMPARISON-SURFACE-BLOCKED`

Multiple secondary verdicts are fine.

### B. Strongest theorem package

State the exact strongest defensible forms of Theorems A, B, C.

For every hypothesis, say which countermodel requires it.

### C. Minimal interfaces

Exact semantic types / transition order for the learning sidecar, repairs, evaluators,
selectors, and improvement challenges.

### D. Proof sketches

Enough detail that we can tell which claims are:

- imported online-learning theorems;
- two-line algebra;
- new composition arguments;
- semantic assumptions.

### E. Countermodel table

CM1–CM10 with:
- what it satisfies;
- what it breaks;
- what catches it;
- whether the failure belongs to this theorem, Coverage, anti-manipulation,
  Service/liability, ontology transport, or policy regret.

### F. Literature verdict

Verify the exact Khot–Ponnuswami / AdaNormalHedge route.
Do not overstate novelty.

Especially report:
- the actual confidence/effective-mass quantity;
- anytime status;
- dynamic/countable expert status;
- what is and is not established for delay.

### G. Consumers

Run the two positive fixtures and the one negative meta-level fixture.

### H. Export property

Try to state the strongest implementation-independent property implied by the package
without RI vocabulary.

Candidate flavor:

> When a process has persistent evidence for an available improvement, it cannot simply
> make that improvement normatively disappear: it must incorporate it, explicitly answer
> or reject the challenge, or remain answerable to it.

Do NOT assume this wording is correct. Improve/refute it.

The point is to find a property that:
1. RI/LE + learning can exactly realize;
2. does not mention `Ob(pos,slot)`, `PProto`, or regret internals;
3. could at least make conceptual sense as a property of a human/institutional reflective
   process, even if humans do not literally satisfy RI.

### I. Freeze / do-not-freeze recommendation

At the end, say what has genuinely earned freezing and what should remain under
prosecution.

---

# 11. Success criterion

The round succeeds even if the ambitious theorem fails.

The valuable outputs are:

1. an exact opportunity-adaptive repair-regret kernel, if available;
2. an exact statement of how LIVE repair mass is controlled;
3. an exact answer to what happens when the process changes the comparison surface;
4. a clear boundary between:
   - regret/non-uptake,
   - answerability/contest,
   - substantive legitimate rejection,
   - Coverage/anti-manipulation,
   - Service/liability,
   - long-horizon policy learning;
5. a theorem statement we would still want after adding inquiry, deference, and richer
   normative change.

The conceptual question to keep returning to is:

> **Does the combination of regret and Legitimate Evolution prove that a demonstrated
> improvement cannot be escaped for free — rather than falsely proving that every
> proposed improvement must eventually be adopted?**

Do not optimize for elegance until that question is settled.
