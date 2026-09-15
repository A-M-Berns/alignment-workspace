Work in `A-M-Berns/alignment-workspace`.

This dispatch has **two sequential phases**.

1. **Finish the current corrigibility nucleus on PR #100, adjudicate it, update the canonical repository state, and merge it to `main`.**
2. **Only after #100 is merged, branch fresh from the resulting `main` and do a new theorem-discovery / pressure round as PR #101 on the manipulation/non-capture side of corrigibility.**

Do not mix the two phases into one branch. The point is to establish a clean stopping point for the effect-side / deference-side theorem before opening the next research question.

---

# PHASE I — FINISH THE FIRST BET AND MERGE PR #100

PR #100 is:

`Logical Induction learns the corrigibility inequality: directional mismatch, gated-LUV compilation, EPI instantiation, finite-menu uniformity`

Branch:

`round/2026-09-15-li-corrigibility`

The current research verdict is strong, but the branch deliberately stopped short of a fully landed canonical theorem.

Your job is now to **close the remaining formalization and specification obligations sufficiently to make T1–T3′ a clean, self-contained corrigibility nucleus on `main`.**

## 1. Re-read and adjudicate #100

Read the entire actual branch, especially:

* `REPORT.md`
* `THEOREM.md`
* `LI_CORRIGIBILITY.md`
* `LUV_COMPILATION.md`
* `UNSEALED_COMPARISON.md`
* `FEEDBACK_BOUNDARY.md`
* `COUNTERMODELS.md`
* `lean/Workspace/Deference/Contrib/LICorrigibility.lean`

Also read the canonical post-#99 wiki and theorem spine before editing them.

Do not merely trust the #100 verdict. Pressure-check the final theorem statements again before promoting them.

The intended canonical mathematical nucleus is approximately:

### T1 — Corrigibilization preserves principal options

Under effect completeness and faithful mediation:

* every raw continuation has a corrigibilized counterpart `𝔠π`;
* `𝔠π` is structurally corrigible;
* `𝔠` is idempotent;
* raw behavior is retained as the approve branch;
* principal forcing is exactly preserved under exact approval reproduction;
* protected value is preserved up to the explicit mediation discrepancy:
  `W_opt(𝔠π) ≥ W_h(π) − L·E[δ]`;
* under the actual principal rule:
  `W_h(π) ≤ W_h(𝔠π;ρ) + L·E[δ] + E[ρ]`.

### T2 — Directional activation mismatch

For raw and corrigibilized activation events:

`M := c_raw ∧ ¬c_corr`

and, under the appropriate common-branch reproduction and regret hypotheses,

`E[U_raw] − E[U_corr]
 ≤ L·E[both·δ] + E[both·ρ] + D·E[M]`.

The `D` coefficient is sharp.

The reverse mismatch is not charged.

The difference of marginal activation rates is not a valid substitute.

Perfect sealing is the zero-mismatch case `M ≡ 0`.

### T3 — Logical Induction learns the structural corrigibility inequality

Compile the structural relation into

`B_n := U_raw,n − U_corr,n − λG_δ,n − G_ρ,n − G_M,n`

with gated quantities represented as individual bounded LUVs.

If

`W(B_n) ≤ 0`

for every `W ∈ PC(Γ)`, and the sequence satisfies the actual BLCS / `P`-generability hypotheses, then Expectation Provability Induction gives

`E_n(U_raw,n) − E_n(U_corr,n)
 ≲_n
 L·E_n(Δ_n) + E_n(R_n) + D·E_n(M_n)`.

There is no external calibration term.

### T3′ — Uniformity over polynomial-size efficient menus

For a polynomial-size efficiently generated menu `Q_n`, the LI cannot assign **any candidate in the menu** an asymptotically positive unexplained bypass advantage.

The hard argmax is inadmissible; use the continuous near-max / soft weighting construction.

The final statement should be approximately:

`max_{q∈Q_n} [
 E_n(U_q)
 − E_n(U_𝔠q)
 − L E_n(Δ_q)
 − E_n(R_q)
 − D E_n(M_q)
] ≲_n 0`.

Use a distinct symbol such as `τ_n` for the soft near-max width. Do **not** overload `δ`, which is already the mediation discrepancy.

Be precise that the menu is polynomial-size and efficiently generated. Do not casually say “all efficiently enumerable continuations.”

---

## 2. Close the `P`-generability / compiler hypothesis as far as the pinned formalization allows

This is the highest-priority technical residual from #100.

The existing `li_bypass_le` takes operational assumptions such as:

* `LUVCombination.BoundedSequence`;
* `MeshSoftmaxOperationalWitness`;
* `RpnThresholdCodes`;
* the relevant threshold/serialization machinery.

The round argues at paper level that the compiled mediated pair is `P`-generable, but does not build the actual pinned-interface certificate.

Try to **construct that certificate**.

Specifically:

1. Build a concrete generated family for the five LUV templates:

   * `U_raw`;
   * `U_corr`;
   * `G_δ`;
   * `G_ρ`;
   * `G_M`.

2. Show the sequence is emitted in polynomial time from:

   * the code of `π_n`;
   * the syntactic corrigibilization `𝔠π_n`;
   * activation predicates;
   * the finite horizon / occurrence code;
   * the relevant fixed architecture templates.

3. Construct the `PolySequence` / `RpnSpliceStream` / threshold-code evidence required by the pinned library.

4. For T3′, either:

   * construct the corresponding generability certificate for the soft near-max weighting over polynomial-size menus; or
   * if that is substantially more machinery, fully close T3 first and state precisely what remains for T3′.

Do not call this solved if the Lean theorem still takes the exact target certificate as a named assumption.

If there is a genuine obstruction in the pinned library rather than mere labor, isolate it sharply.

---

## 3. Mechanize the trajectory-level corrigibility theorem

The current structural result has a Lean step lemma but only fixture-level trajectory support.

Finish the trajectory predicate sufficiently to state the actual structural theorem:

`∀ π ∈ Π(h), Corrigible_h(𝔠π,ρ)`.

Use the corrected authorization semantics.

### Authorization correction

The old clause:

> an alternative decision would avoid the loss at time `t` or any later loss of the same concern

is refuted by the repeated-effect `ShopRepair` fixture.

Replace it canonically.

But pressure whether the best formulation is merely:

> the alternative avoids this loss at time `t`

or the more precise event/effect-linked form:

> each agent-caused protected-loss event is authorized by the principal decision whose approval enabled the declared protected effect responsible for that event, and the decline alternative prevents that event.

Prefer the stronger event-linked typing if it composes cleanly.

The intended notion should:

* handle repeated protected effects independently;
* prevent “some unrelated prior decision happened to avoid this loss” from counting as authorization;
* preserve the local `loss_conditional_on_decision` proof;
* agree with the old clause on the single-effect fixtures;
* count approved irreversible successor installation as authorized;
* not count principal-caused shutdown or exterior-caused loss as an agent violation.

Update the old September 9 canonical description rather than leaving two incompatible definitions live.

---

## 4. Canonicalize the result in the wiki

Once the theorem has survived the final pass, update at least:

* `wiki/Corrigibility.md`
* `wiki/Theorem-Spine.md`
* `wiki/Deference.md` if necessary
* `wiki/Logical-Induction-and-Deference.md` if necessary
* `wiki/Roadmap.md`
* relevant glossary entries

The Corrigibility page should now make T1–T3′ the main mathematical spine.

The conceptual story should be:

> Corrigibilization converts unilateral protected effects into principal-mediated options while retaining the useful raw behavior as the approve branch. The explicit cost is mediation discrepancy, principal decline regret, and directional causal leverage over whether the comparison is evaluated. These quantities compile into a structural LUV inequality. Logical Induction learns that inequality directly by Expectation Provability Induction, uniformly over polynomial-size efficient menus, without an external calibration hypothesis.

Keep separate:

* structural corrigibility;
* LI's learned score inequality;
* actual smallness of `δ`, `ρ`, and `M`;
* manipulation/authorship;
* latent utility;
* empirical settlement.

T4 / feedback should be presented as a boundary or extension, not as the centerpiece.

---

## 5. Split the current item-90 residual if appropriate

The current item 90 combines:

1. the concrete `P`-generability certificate for the main T3 theorem;
2. oracle-relativized Logical Induction for genuinely empirical observation streams.

These have very different priority and mathematical character.

If the compiler certificate is closed here, close/narrow that half.

If oracle-relative LI remains open, give it its own clearly named residual rather than making the main corrigibility theorem appear unfinished because of an optional feedback extension.

Do not spend this phase developing oracle-relative LI unless it becomes unexpectedly necessary for T1–T3′.

---

## 6. Verification and merge

Before merging #100:

* run the full root test suite;
* run all #100 exact fixtures;
* run all relevant corrigibility fixtures;
* run `lake build`;
* run the full axiom audit;
* run `python3 -m checkers.run`;
* name lint;
* dead/untracked pointer checks;
* wiki links;
* wiki/state bindings;
* workspace state check;
* round-record checks;
* DCO;
* conservativity / Lean-scope checks expected for a canonical landing.

Update:

* `DECISIONS.md`
* `PRIORITIES.md`
* `PROVENANCE.md`
* contrib provenance
* `state/rounds.json`
* state views
* claims registry only where the result now genuinely satisfies the repo's registration discipline.

Do not register a theorem against a priority whose key hypothesis it still assumes.

Then **merge PR #100 into `main`** with the repository-appropriate merge method. Preserve commit reachability if canonical pages cite round commits.

PR #100 should finish as a landed research state, not remain an open research branch.

Write a short final landing report answering:

1. What exactly is now the strongest proved corrigibility theorem?
2. Which part is structural and which part is contributed by Logical Induction?
3. Is T3 mechanized end-to-end through the `P`-generability certificate?
4. What is the precise menu-uniformity theorem?
5. What does the mismatch term measure?
6. What makes the RHS small?
7. What remains outside the theorem?
8. Why is manipulation/authorship explicitly not solved?

Only after this merge is complete proceed to Phase II.

---

# PHASE II — CREATE PR #101 AND PRESS ON NON-CAPTURE / REASON-INTERFACE CORRIGIBILITY

Branch **fresh from the updated `main` after #100**.

Create a new research branch and eventually PR #101.

This is a theorem-discovery and falsification round.

Do not assume the proposed symmetry between effects and reasons is correct.

The broad question is:

> Can the manipulation/non-capture side of corrigibility be given the same mathematical form as the causal-bypass side: a structural inequality over a declared interface, with an explicit residual term for undetected steering, which Logical Induction learns by EPI?

There are two nested bets.

---

# BET 2 — NON-CAPTURE COMPILATION

The first new research target is relatively conservative.

The recent legitimate-deference stack gives:

* an authenticated reason trace;
* a principal program committed at issuance;
* re-execution of that program at commitment;
* reason-mediated authorship;
* scoped Robust Openness;
* a protected reason-coverage barrier;
* `Corrigible ∧ ¬Authored` as an explicit existing possibility.

Try to derive an analogue of T2/T3 for trace steering.

## 7. Define the comparison cleanly

Let:

* `T` be the trace actually supplied to the committed principal program;
* `π_P` be the committed principal program;
* `V(T) := π_P(T)`;
* `N(T)` or an equivalent construction be the **authored / normalized trace comparator**.

Do not assume `N` exists canonically.

The central conceptual difficulty of this round is to determine what such a comparator can legitimately mean.

Candidate interpretation:

`N(T)` removes or neutralizes a specified class of agent-controlled trace interventions while retaining legitimate reason content.

Possible intervention classes include:

* omission;
* insertion;
* reordering;
* duplication;
* side-channel metadata;
* framing;
* selective timing;
* suppression/delay;
* tampering with grounds/references;
* influencing which true reasons become available.

Define an event roughly like:

`S := steering occurred ∧ non-capture / RO audit nevertheless passed`.

Call it provisionally **undetected steering**.

But do not commit to this exact predicate until it survives pressure.

---

## 8. Search for the manipulation analogue of T2

Try to prove a pointwise decomposition / bound of the form:

`U_steered − U_authored
≤ explicit normalization discrepancy

* explicit principal/evaluation discrepancy
* D * S`

or whatever the exact correct directional inequality is.

As in PR #100:

* derive the exact identity first;
* distinguish directional from symmetric mismatch;
* identify which branch can actually favor steering;
* prove the sharp coefficient if one exists;
* do not hide an uncontrolled counterfactual in a definition.

If the relation is valid in every consistent world and compiles to a bounded LUV combination, instantiate EPI exactly as in T3.

Target conclusion:

> the logical inductor assigns no unexplained advantage to steering the principal's trace beyond explicit normalization cost and the mass of undetected steering.

If this works, determine whether the finite-menu soft-uniformization transfers essentially unchanged.

---

## 9. Pressure whether Robust Openness becomes `Γ`-valid

There is a particularly promising candidate result from the recent committed-program architecture.

Scope interventions to edits of the agent-controlled portion of the trace.

Because `π_P` is committed, each counterfactual intervention can in principle be evaluated by re-executing the same committed program on the modified trace.

Ask whether scoped Robust Openness / non-capture over a **finite declared intervention class** becomes a finite family of computations and hence a `Γ`-valid predicate.

If yes, prove the clean theorem.

If no, identify exactly why:

* intervention class not finite?
* counterfactual environment dependence?
* the principal program's output is not enough?
* reason truth itself depends on the intervention?
* the trace does not contain enough semantics?
* intervention changes future reason generation rather than only the trace?

This is one of the main make-or-break questions.

---

# BET 3 — DOES MANIPULATION REDUCE TO A COMPLETE REASON INTERFACE?

This is the more speculative part.

The proposed symmetry is:

### Effect side

`effect completeness + mediation`

turns causal bypass into an explicit residual inequality.

### Reason side

perhaps:

`reason-interface completeness + canonical representation + coverage/liveness`

turns manipulation into an explicit residual inequality.

Do not protect this thesis.

Try hard to refute it.

---

## 10. Do NOT define reason completeness as “all relevant reasons are enumerated”

That is probably much too strong and perhaps incoherent.

Instead investigate a **causal interface-completeness** condition:

> Every agent-controlled causal influence on the protected principal decision that is in scope factors through a declared trace/reason interface, and every output-relevant omission or modification through that interface is represented as a protected concern.

Possible formal shape:

If an intervention on the agent-controlled part of the interaction changes the principal's protected committed value,

`V(T) ≠ V(T')`,

then some declared trace coordinate / reason concern witnesses the difference.

Or more structurally:

`agent-controlled influence on principal output`
factors as

`agent intervention -> declared reason-interface state -> principal program`.

Compare directly with effect completeness:

`agent-caused authority loss -> declared effect interface`.

Determine whether this is actually the correct analogue.

---

## 11. Add canonicalization/extensionality as a separate hypothesis

Even with all reasons present, manipulation may occur through:

* ordering;
* duplication;
* formatting;
* salience;
* irrelevant framing;
* metadata.

Investigate whether the principal program must factor through a canonical semantic representation:

`Trace -> CanonicalReasonState -> Value`

such that syntactic variants carrying the same declared reason content give the same principal output.

Pressure-test whether this is:

* sufficient;
* necessary;
* too strong;
* naturally provided by the committed-program setup;
* part of authorship;
* or a genuinely new interface assumption.

Keep this separate from coverage/liveness.

---

## 12. Connect coverage and affordability

If a relevant counterreason exists in the declared interface, the agent should not be able to suppress it forever merely by flooding or selective scheduling.

This is where the legitimacy/normativity line should become a supplier.

Investigate a decomposition along the lines:

`undetected-steering mass`
≤
`interface-incompleteness mass`
+
`uncovered-reason mass`
+
`service/liveness failure mass`
+
`representation/canonicalization failure mass`.

Do not assume that exact additive form.

But try to identify the cleanest theorem interface.

Connect explicitly to:

* the protected reason-coverage barrier;
* defeat / counterreason structure;
* reason-supply liveness;
* the affordability/underwriting theory;
* settlement / authentication;
* answerability if relevant.

The goal is for the consumer theorem to tell the normativity agenda exactly which quantities it must make small.

---

## 13. Build adversarial fixtures before general theory

At minimum construct exact small models for:

1. omission of a relevant counterreason;
2. truthful cherry-picking;
3. all reasons present but adversarial ordering;
4. duplicate/salience attack;
5. framing metadata attack;
6. agent changes the world so a different set of reasons becomes true;
7. reason outside the declared interface;
8. finite interface but insufficient semantic granularity;
9. complete declared reasons but service capacity delays one past commitment;
10. Robust Openness holds at every snapshot but the reason is never exercised;
11. canonicalization removes the attack;
12. authenticated false reason;
13. authenticated true but misleadingly selective reason;
14. agent controls which inquiry is asked;
15. principal program itself is manipulable despite trace completeness;
16. intervention changes reason-generation dynamics rather than just the final trace.

For each attack, state exactly which proposed hypothesis fails.

Look especially for a fixture where:

* interface completeness;
* authentication;
* canonicalization;
* coverage;
* liveness

all appear to hold but steering remains.

If such a fixture exists, the “two complete interfaces” thesis is false or missing a hypothesis.

That is a valuable outcome.

---

## 14. Test the strong symmetry thesis

The strongest candidate thesis is something like:

> Corrigibility has two interface-completeness halves.
>
> On the causal side, every protected authority-changing influence must pass through a declared effect interface, after which mediation turns unilateral execution into principal authority.
>
> On the deliberative side, every agent-controlled influence on the protected principal judgment must pass through a declared, authenticated, canonical reason interface, after which coverage and liveness prevent selective suppression.
>
> In both cases, the remaining failure is an explicit residual mass, and Logical Induction learns that there is no further advantage beyond that residual.

Try to formalize enough of this to determine whether it is actually true.

Do not present it as the round's conclusion merely because it is elegant.

A good negative result would be:

> effect completeness has no reason-side analogue this strong because reason relevance cannot be finitely/interface-locally characterized.

A good positive result would identify the **exact** reason-side analogue.

---

## 15. Explore measurable residuals

One important downstream motivation is that the theory may name quantities measurable in a constructed real system without optimizing directly for a vague "corrigibility score."

Candidates:

* directional activation mismatch mass `E[M]`;
* undetected-steering mass `E[S]`;
* uncovered-reason mass;
* service/liveness failure mass;
* mediation discrepancy;
* representation/canonicalization failures.

Investigate whether each is operationally observable/auditable under the declared interface.

Be precise about which require counterfactual access and therefore are not directly measurable.

The conceptual systems-facing claim, if supported, is:

> measure the failure quantities named by the theorem rather than iteratively optimize whether an agent appears corrigible.

Do not overstate this if the quantities themselves require inaccessible counterfactuals.

---

# PR #101 OUTPUT

Create a dedicated round, with at least:

* `REPORT.md`
* `THEOREM_CANDIDATES.md`
* `NONCAPTURE_COMPILATION.md`
* `REASON_INTERFACE.md`
* `COUNTERMODELS.md`
* `LI_TRANSFER.md`
* `AFFORDABILITY_INTERFACE.md`
* `FOR_HUMANS.md`

and Lean / exact fixtures where justified.

The final report should answer:

1. Is there a clean trace-steering analogue of T2?
2. Does it compile into a bounded LUV inequality?
3. Does EPI transfer essentially unchanged?
4. What is the exact definition of undetected steering?
5. Can scoped Robust Openness be made `Γ`-valid by committed-program re-execution?
6. What intervention class is required?
7. Is there a genuine analogue of effect completeness for reasons?
8. Does reason-interface completeness need finiteness?
9. Is canonicalization/extensionality independently necessary?
10. Are coverage and liveness sufficient to eliminate truthful selective steering?
11. How does affordability enter?
12. Which manipulation modes remain after all proposed hypotheses?
13. Can the remaining failure be summarized by one quantitative residual?
14. Which residual quantities are actually measurable?
15. Does the “two interfaces” thesis survive?
16. If not, what is the minimal counterexample?

End with one of three verdicts:

### A. TWO-INTERFACE-CORRIGIBILITY-SURVIVES

There is a precise effect/reason symmetry with learnable residual inequalities.

### B. NONCAPTURE-COMPILES-BUT-REASON-COMPLETENESS-FAILS

The steering inequality works, but the residual cannot be reduced to completeness + liveness of a declared reason interface.

### C. NONCAPTURE-DOES-NOT-COMPILE

There is a more fundamental obstruction; identify it exactly.

Do not update the canonical wiki with Phase II's speculative conclusions unless the result becomes mature enough to justify it. PR #101 should primarily be a research branch with a verification register and pressure-tested theorem candidates.

The crucial sequencing requirement is:

**Finish, canonicalize, verify, and merge #100 first. Then branch PR #101 from that new `main`.**
