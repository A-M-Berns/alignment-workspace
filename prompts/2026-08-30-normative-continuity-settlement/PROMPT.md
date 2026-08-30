# Prompt — 2026-08-30 normative-continuity-settlement

Verbatim as sent. Prompt author: the maintainer (drafted with GPT-5.6 Sol, OpenAI).
Executor: Claude Fable 5 (Anthropic). The maintainer's framing preceding the quoted
prompt: "merge this pr, then do this task on a new pr I'd make the next pass explicitly a
**mathematical closure pass**: no new architecture, no prose polishing, no broad
provenance work. Its job is to remove the remaining modeling degrees of freedom and make
the paper model and Lean model line up exactly enough that we can say 'Normative
Continuity is settled.' Use this:"

---

We are doing the **final mathematical settlement pass for Normative Continuity**.

PR #67 has already completed the concordance and Lean formalization of the current theorem spine. Treat that work as the starting point, especially:

* `projects/normativity/legitimacy/rounds/2026-08-29-normative-continuity-concordance/CONCORDANCE.md`
* `THEOREM_MAP.md`
* `NORMATIVE_CONTINUITY.tex`
* `PROOF_PASS.md`
* `lean/Workspace/Normativity/Contrib/NormativeContinuity.lean`
* the relevant entries in `DECISIONS.md`

Current status:

* checkpoint: `AGENT-CONSOLIDATED`;
* concordance: `CONCORDANT WITH LOCAL REPAIRS`;
* formalization: `FORMALIZATION SURVIVES`;
* Persistent-Wait, Persistent Opportunity, No Structural Abandonment, Grounded Replay, the standing bridge, and the critical regression fixtures are Lean-verified under their stated abstract hypotheses;
* CI on PR #67 is green.

This pass is **not** another synthesis round. Do not invent a richer theory, rename everything, or reopen philosophical scope. The question is:

> **What exact mathematical specification should we now regard as the settled Normative Continuity theory?**

If the answer survives, we want to leave this pass able to mark the mathematics itself as settled and move on to Progress.

---

# 1. Resolve the one genuinely open modeling decision: successor freshness

The current synthesis requires

$$
q\xRightarrow[n]{}S
\quad\Longrightarrow\quad
S\subseteq B_n,
$$

so every successor is freshly opened in the resolution batch.

Frozen Legitimate Evolution instead allowed successors to be preexisting/shared. PR #67 correctly identified this as a real design reversal, not a theorem contradiction.

Prosecute this decision from first principles.

Compare at least three possibilities:

### A. Fresh-successor model

$$
S\subseteq B_n.
$$

Advantages currently claimed:

* successor edges are intrinsically prospective;
* ancestry cannot be retroactive;
* acyclicity follows from birth time;
* an issue becoming a continuation of a matter has an unambiguous transition position;
* Persistent-Wait uses this cleanly.

### B. Existing-successor model with static ancestry

Permit

$$
S\subseteq B_n\cup O_n
$$

with some explicit acyclicity condition.

Pressure-test whether this is actually coherent. In particular:

* if \(q'\) existed before \(q\) resolves into it, does a static relation \(q\to q'\) make \(q'\) appear retroactively to have carried \(q\)'s matter?
* can `Live_n(m)` and matter inheritance still be defined extensionally from static ancestry without time-indexing the edge?
* does an acyclicity premise alone solve this, or only graph cycles?

### C. Existing-successor model with time-stamped successor edges

Something like

$$
q\xrightarrow[n]{}q'.
$$

Determine how much machinery is required to define time-relative ancestry and matter inheritance correctly.

Then answer:

> Is there any actual expressivity we currently need from preexisting successors that cannot instead be represented by prerequisite/reference edges?

Give a firm recommendation. Do not default to frozen LE merely because it is older.

My current hypothesis to test is:

> For Normative Continuity, succession represents **diachronic continuation of an entitlement**, not mere relation to an existing issue. Therefore fresh successors are the right primitive; already-existing issues should be related by prerequisites/references. Generalization to time-stamped consolidation can be deferred until a real consumer needs it.

Either vindicate that or break it.

If fresh successors win, record the choice as a deliberate supersession of LE A5/A11 with the mathematical reason, not merely "because the proof uses it."

---

# 2. Settle the other LE → NC departures

PR #67 found several undeclared changes. Decide whether each should remain in the settled theory.

## Same-batch opening and resolution

Current NC:

$$
O_{n+1}=(O_n\setminus R_n)\cup B_n,
$$

so a fresh issue cannot also disappear in its opening batch.

LE allowed same-batch opening and resolution.

Determine whether NC should deliberately forbid it. Check:

* strict-prefix evaluation of `Resolve`;
* definition of current state \(s_n(q)\);
* whether allowing same-batch resolution requires a separate semantics for birth-state resolution;
* whether permitting it opens any genuine silent-materialization loophole.

Give a firm choice.

## Due timing

Current NC evaluates

$$
\Due_n=\Due(H_n,L_n)
$$

from the strict prefix, so a record in \(e_n\) can first affect `Due` at \(n+1\).

LE allowed descriptive material from the current event while pinning normative standing to the pre-state.

Determine whether the settled NC model should be uniformly strict-prefix. Check for any lost expressivity beyond a one-position shift.

Give a firm choice.

## Resolution gating

LE used `Permit` in resolution validity; NC treats

$$
\Resolve_n(q;g,S)
$$

under \(q\)'s anchored protocol as the relevant local semantic judgment.

Decide whether `Resolve` should be:

1. sufficient on its own, with any global permission checks optionally read inside its semantics; or
2. conjunctively gated by `Permit`.

Prefer the weaker primitive interface unless the second gate does independent structural work.

## Scope of standing grounds

LE S1 constrained grounds of every accepted standing edit; NC currently only needs authorized/nonempty grounds when the edit actually changes \(L_n\).

Determine the clean settled requirement. Do not preserve a distinction with no semantic content merely for provenance fidelity.

---

# 3. Close the paper-model ↔ Lean-model gap for matters

This is the main remaining formalization debt.

The paper constructs matters from roots and later designations. Lean currently abstracts to

$$
M:\mathbb N\to\operatorname{Finset}(Q)
$$

with:

* `matters_mono`;
* `matters_prior`.

Prove in Lean that the **actual paper construction of \(M_n\)** satisfies exactly the abstract properties consumed by the theorem spine.

This should include:

* roots becoming matters at the intended position;
* explicit designation becoming effective only prospectively;
* no retroactive matterhood;
* monotonicity;
* prior birth;
* split/merge behavior;
* the definition of `Live_n(m)` matching the paper.

If the construction needs one more property than the abstract theorem currently states, identify it rather than silently strengthening the structure.

Once proved, either:

* keep the theorem generic over abstract \(M\) and add a realization lemma from the concrete matter construction; or
* explain why directly using the concrete construction is mathematically cleaner.

I expect the former.

---

# 4. Audit exact structural satisfiability

We now know the theorem implications are correct. Check that the **whole settled specification is jointly satisfiable**, rather than only theorem-by-theorem.

In particular:

### Standing

Verify there are traces satisfying:

* strict-prefix standing change;
* authorized grounding;
* fresh standing occurrences if retained;
* standing gain and loss;
* open issues continuing under a protocol that later loses standing.

### Due + opening

Verify `Due` + standing-at-opening + due realization are jointly satisfiable without needing a hidden totality assumption beyond the explicit due/standing compatibility condition.

### Attention

Verify the matter-grain budget

$$
0\le a_n(m)\le o_n(m),\qquad
\sum_{m\in M_n}a_n(m)\le1
$$

together with non-starvation for all matters.

The positive-share construction should be stated with the exact time-indexed matter-birth convention and overlapping matters. Check there is no hidden problem from infinitely many total matters appearing over time.

### Prerequisites

Check:

* one-shot prerequisite occurrences;
* co-opened route roots;
* withdrawal;
* semantically identical reintroduction as a fresh occurrence;
* route extinction after introduction;
* reach-gated additions.

We should be able to point to at least one nontrivial trace satisfying the complete structural theory.

---

# 5. Recheck the theorem statements against the final choices

After resolving §§1–4, rerun the Lean theorem spine using the **settled model**.

The desired dependency facts remain:

$$
\text{Persistent-Wait}
\quad\text{uses only}\quad
4,5,7,8,9,10,12+\text{finite/history bookkeeping},
$$

$$
\text{Persistent Opportunity}
=
\text{Persistent-Wait}+\text{Wait Responsiveness},
$$

$$
\text{No Structural Abandonment}
=
\text{Persistent Opportunity}+\text{Non-Starvation},
$$

with Grounded Replay mathematically independent except for the standing-at-opening bridge.

If any final modeling choice changes those dependencies, report exactly why.

Re-run the important fixtures, especially:

* rotating prerequisite countermodel;
* co-opened route-root counterexample to unqualified route extinction;
* waiting-cycle-as-work;
* split/merge/designation;
* a protocol losing standing while an issue anchored to it remains live.

---

# 6. Settle the exact status of Wait Responsiveness

Do **not** try to derive it from Coverage in this pass.

But make sure its mathematical form is exactly what the theorem needs:

$$
\left(
\exists N_0\ \forall n\ge N_0,\;
d\in\NoRoute_n(m)
\right)
\Longrightarrow
\exists k\ge N_0,\;\Met_k(d).
$$

Check whether the equivalent "no fixed prerequisite remains a no-route wait forever" form is cleaner as the primitive assumption.

Explicitly distinguish:

* what the continuity theorem assumes;
* possible future sufficient conditions from Coverage/inquiry/hygiene.

No `External(d)` classification should return unless mathematics actually requires it.

---

# 7. Grounded Replay: settle the exact theorem we want

The current NC theorem says:

$$
\lambda\in L_n
\Longrightarrow
\lambda\text{ has a finite authorization ancestry to }G.
$$

Frozen LE proved the stronger historical statement for every admitted occurrence, whether or not still standing.

Decide whether the settled NC document should:

* state only the current-standing form because that is exactly what its consumer needs;
* state the stronger admitted-occurrence theorem as the canonical Grounded Replay theorem and derive the live form as a corollary.

My prior is that the second is cleaner if it does not complicate the model: Grounded Replay is fundamentally a historical theorem, and "ancestry, not permanence" is more naturally expressed over admitted occurrences.

Test this.

---

# 8. Requirement minimization versus theory membership

Produce a final table with two separate notions:

| condition | part of settled Normative Continuity? | used by which theorem? |
| --------- | ------------------------------------- | ---------------------- |

Do not delete a structural continuity principle merely because Persistent-Wait does not use it.

But also do not let the document say "Theorem X follows from the structural requirements" when X only uses a proper subset.

The final theory should clearly distinguish:

$$
\boxed{\text{definition of legitimate/normatively continuous evolution}}
$$

from

$$
\boxed{\text{minimal hypotheses of each derived theorem}.}
$$

---

# 9. Mathematical red-team

Before declaring victory, do one final small-countermodel search targeted specifically at the **settled choices**, not at old versions.

Try to produce traces exploiting:

* successor sharing;
* merge/split;
* matter designation timing;
* standing repeal;
* Due timing;
* co-batch events;
* prerequisite churn;
* route-root churn;
* `Met` transitions;
* attention shared across overlapping matters;
* empty or degenerate histories.

Search for either:

1. a violation of one of the headline theorems while satisfying its stated hypotheses; or
2. an internally contradictory set of structural requirements.

If you find either, stop and report it.

---

# 10. Allowed edits

Unlike the concordance pass, this pass **may create the post-concordance revision** of the theory.

Do not mutate the byte-exact `AGENT-CONSOLIDATED` checkpoint.

Instead:

* preserve it historically;
* make a new revision containing the settled decisions and applicable errata E1–E9;
* remove stale notation such as the unused `\Ext`;
* update provenance to say exactly what changed from the checkpoint and why;
* update Lean only where required by the settled mathematics.

Keep exposition changes strictly local. This is a mathematical settlement pass, not a rewriting pass.

---

# 11. Final verdict

End with exactly one of:

### `NORMATIVE-CONTINUITY-MATH-SETTLED`

Use this only if:

* all open modeling decisions above have explicit resolutions;
* the concrete paper matter construction is connected to the Lean abstraction;
* the whole specification has a satisfiability witness;
* the headline theorem spine still passes Lean;
* the regression fixtures pass;
* there is no unresolved countermodel;
* Wait Responsiveness and Non-Starvation are clearly identified as assumptions rather than secretly "proved."

### `SETTLEMENT BLOCKED — LOCAL MATHEMATICAL ISSUE`

Use if there is a specific repairable issue.

### `SETTLEMENT BLOCKED — STRUCTURAL DEFECT`

Use if the theory needs architectural revision.

If the first verdict holds, record a status checkpoint in the workspace:

**`NORMATIVE-CONTINUITY-MATH-SETTLED`**

with the gloss:

> The structural mathematical specification, its principal modeling choices, theorem dependencies, satisfiability, and Lean theorem spine have been settled. This does not assert Coverage, Progress, substantive normative correctness, Proper Exercise, or realization by a concrete reasoner.

Do not call the entire legitimacy project settled.

---

# Governing question

At every disputed point ask:

> **Does this structure preserve exactly the continuity relation we mean, or is it merely convenient for the proof?**

We are done when the answer to that question is clear for every load-bearing piece.

The target conceptual content remains:

$$
\boxed{\textbf{Authority must have a history. Obligations must have a future.}}
$$

The purpose of this pass is to determine the exact mathematics that sentence has earned.

---

If this comes back `NORMATIVE-CONTINUITY-MATH-SETTLED`, I would actually honor that status and stop touching this layer while we work on Progress. The next reason to reopen it should be a downstream consumer exposing a concrete missing capability, not another round of aesthetic unease.
