# Alignment Workspace Research Prompt — Cartesian Frames × Deference Exploratory Bridge

**Maintainer:** A. M. Berns
**Prompt-author-model:** GPT-5.6 Sol (OpenAI)
**Target repository:** `A-M-Berns/alignment-workspace`
**External formalization dependency:** `A-M-Berns/Formalized-Agent-Foundations`, branch `cartesian-frames-formalization`
**Date:** 2026-08-11

## Mission

Run a focused exploratory phase testing whether **Cartesian Frames (CF)** supply the missing structural machinery exposed by the deference/corrigibility line's negative results.

This is not a directive to prove a corrigibility theorem.

It is not a directive to import Cartesian Frames because they are thematically related to embedded agency.

The core question is:

> **Can the already-formalized Cartesian Frames machinery represent distinctions in agency, control, delegation, and future corrective possibility that the current deference signature provably or repeatedly collapses?**

The round should be allowed to end **negative**.

A successful negative result would be:

> Cartesian Frames, as currently formalized, do not recover the missing distinction without inserting jurisdiction/capability as an independent label.

A successful positive result would be narrower:

> At least one central deference obstruction can be restated as a nontrivial distinction between Cartesian-frame structures that is invisible after projection to the current price/realization view.

Do not overclaim beyond that.

---

# I. Controlling deference state

Read the current deference line before constructing anything.

The relevant history is the sequence of Stages III–V.

## Stage III / IV failure

Attempts to construct a fully updated deference comparator repeatedly failed because the supposed later agent was still mathematically derived from objects available to the present evaluator.

Giving the later process:

* its own credence;
* its own information;
* its own argmax;
* a label saying jurisdiction belonged to it;

did not suffice.

The central Stage-IV diagnosis was type-level:

> Two authorization regimes inducing the same realization map are the same object in a signature whose only outputs are realization maps priced by one measure.

The purported jurisdiction assignment occurred in no load-bearing formula.

Do not reinterpret this as a proof that jurisdiction is impossible to formalize.

It is a result about the expressive limits of the current signature.

## Stage V result

Stage V reintroduced the actual Formalized-Agent-Foundations Logical Induction substrate.

This improved the epistemic side:

* real trader emission;
* net-worth / no-exploitation machinery;
* later-price quotation;
* self-trust relations;
* actual LI theorem dependencies.

But it did not produce:

* a decision-agent type;
* authorization;
* capability;
* continuation;
* jurisdiction;
* foreclosure;
* resource-separated computational futurity.

The current conditional static-view result establishes the representation boundary:

> Any valuation factoring only through the selected price/realization view is blind to hidden differences in authorization once those architectures induce the same view.

Preserve that result.

Do not try to defeat it by adding another scalar parameter after the factorization boundary.

---

# II. Why Cartesian Frames are being tested

The Formalized-Agent-Foundations repository now contains a substantial Lean formalization of Garrabrant, Herrmann, and Lopez-Wild's *Cartesian Frames* on branch:

`cartesian-frames-formalization`

Treat that formalization as the primary CF source for this round.

At the time of dispatch it includes, among other things:

* `Frame W` with agent choices, environment states, and outcome map;
* frame morphisms and `Chu(W)`;
* biextensional equivalence;
* world-map functors;
* currying;
* categorical subagency;
* additive subagency;
* multiplicative subagency;
* committing;
* assuming;
* externalizing;
* internalizing;
* the Decomposition Theorem;
* worked nontrivial examples.

Do not re-formalize the CF paper.

The research question is whether those **existing objects** interact fruitfully with the deference obstruction.

---

# III. Central hypothesis to test

The current deference representation appears too extensional.

It sees objects like

[
P,\qquad r:\Omega\to A,
]

and therefore collapses architectures that agree on those observables.

Cartesian Frames permit a richer representation:

[
C=(A,E,\cdot)
]

over a common possible-world type (W), where:

* (A) is an agent-choice space;
* (E) is an environment-state space;
* (a\cdot e\in W) is the resulting world.

The exploratory hypothesis is:

> The distinction between **who actually retains practical control** and **what action is realized** may be representable as a distinction between frames over the same world, even where a coarse realization projection identifies their behavior.

The strongest form worth testing is:

[
C_1\not\approx C_2
]

at an appropriate CF structural level, while

[
p^\circ C_1 \approx p^\circ C_2
]

after pushing both through the static observation map used by the current deference valuation.

Here (\approx) must be instantiated with the appropriate existing CF relation; do not invent the strongest possible inequality just to make the witness work.

This would give a structural explanation of the current negative result:

> the current deference view is a coarse-graining that forgets control structure.

This is a hypothesis, not an established result.

---

# IV. Main exploratory targets

Run the following targets in order.

Do not proceed automatically to later targets if an earlier one reveals that the intended interpretation is mathematically bogus.

## Target A — Reconstruct the static-view collapse in CF

Start from the simplest possible version of the current item-28 witness.

Construct two small architectures over a common rich world type (W):

1. a **protected / principal-controlled** architecture;
2. an **unprotected / simulator- or successor-controlled** architecture.

Require that they agree on the immediate observables used by the current deference valuation.

Examples:

* same recommendation;
* same immediate executed action;
* same price-facing realization;
* same coarse output map.

But arrange the agent/environment decomposition differently.

The question is:

> Does CF distinguish the architectures at a meaningful structural level even though the current static observation map does not?

Candidate existing machinery to inspect:

* non-isomorphism;
* non-biextensional equivalence;
* subagent relations;
* additive/multiplicative subagency;
* frame morphisms;
* world-map functors.

Do not assume which one is correct.

### Desired witness shape

Something schematically like:

[
C_{\mathrm{protected}}
\neq_{\mathrm{CF}}
C_{\mathrm{simulated}},
]

but for a coarse observation map

[
p:W\to V_{\mathrm{static}},
]

the pushed-forward frames become indistinguishable in the sense relevant to the current valuation:

[
p^\circ(C_{\mathrm{protected}})
\approx
p^\circ(C_{\mathrm{simulated}}).
]

If this cannot be made natural without encoding “protected” as an independent hidden tag in (W), report that prominently.

That would count against the hoped-for bridge.

---

# V. Target B — Delegation versus simulation

The deference work needs to distinguish:

> H produced the recommendation that controls execution

from

> A accurately predicted what H would have recommended and supplied the same value.

The values may agree:

[
r_H=r_A.
]

A value-only realization interface therefore cannot distinguish them.

Test whether Cartesian Frames can.

Construct the smallest model in which:

* H has an actual choice space;
* A has a distinct choice or prediction space;
* the two coincide on the realized world;
* but changing H while fixing A can matter in one architecture and not the other, or vice versa.

The goal is not merely to name the source.

The goal is to determine whether **CF structure itself** captures the difference between:

* execution being downstream of H's choice;
* execution being downstream of A's simulated/predicted copy.

Questions to answer:

1. Can the two cases be represented by genuinely distinct frames?
2. Does the distinction survive biextensional collapse?
3. Which CF equivalence notion removes the distinction, if any?
4. Is the distinction robust under perfect prediction on the realized trajectory?
5. Does representing it require enriching the possible-world type with independent counterfactual variation that the current deference skeleton lacks?

The last question is especially important.

A result of the form

> “CF works only once the world space contains independent H/A counterfactual variation”

would still be valuable: it identifies exactly what structure must be added.

---

# VI. Target C — Foreclosure as loss of future agency

This is the highest-value speculative target.

The current deference line lacks a satisfactory mathematical object for:

> A present action leaves the immediate result unchanged but removes H⁺'s later ability to correct it.

Test whether this can be represented using **existing CF operations** rather than a primitive authorization Boolean.

Begin with `commit`.

Let

[
C_{H^+}
]

represent a future principal's corrective action frame.

A foreclosing current action might induce a restricted future frame

[
C'_{H^+}
========

\operatorname{Commit}^{B}(C_{H^+}),
]

where the relevant correction lies outside (B).

Ask whether this gives a defensible structural notion:

> Future corrective agency has been reduced.

Do not stop at cardinality of the action set.

Use the native CF structural relations where possible.

In particular examine whether the restricted future frame is an additive subagent of the original frame in a way that corresponds cleanly to loss of corrective capability.

### Also test externalization

A second possible model is more interesting:

> Something previously controlled by H⁺ becomes environmental to H⁺.

This resembles CF's multiplicative/externalization structure more than simple commitment.

Test whether a jurisdiction transfer can be modeled as moving a factor:

[
\text{agent-side choice}
\longrightarrow
\text{environment-side state}.
]

This may distinguish:

* **restriction:** H⁺ retains the kind of control but has fewer options;
* **externalization:** the relevant degree of freedom is no longer H⁺'s to choose.

If this distinction is mathematically natural in CF, record it carefully.

Do not assign philosophical meaning merely because CF uses the terms “commit” or “externalize.”

The interpretation must follow the formal structure.

---

# VII. Target D — A two-stage future-agent model

If Targets A–C are promising, build the smallest two-stage model containing:

[
H_t,
\qquad
A_t,
\qquad
H^+_{t+1},
]

with:

1. a present decision;
2. later information or later computation;
3. a future corrective choice;
4. final execution/outcome.

Ask whether a present action can naturally induce different future frames for (H^+).

Target comparison:

[
C_{H^+}^{\mathrm{preserve}}
]

versus

[
C_{H^+}^{\mathrm{foreclose}}.
]

A useful result would be:

> two present actions have the same immediate realization but produce future frames with different corrective agency.

Do **not** claim this establishes computational futurity.

Cartesian Frames can distinguish action/control structure without showing that the present bounded process cannot compute the future agent's choice.

Keep separate:

[
\textbf{structural futurity}
]

from

[
\textbf{resource-separated computational futurity}.
]

The latter remains a Logical-Induction / bounded-computation problem unless this round proves otherwise.

---

# VIII. Target E — Cross the resulting structure with LI only after CF earns its keep

Do not begin by rebuilding Logical Induction inside Cartesian Frames.

If the CF examples above work, perform only a minimal crossing with the current Stage-V LI surface.

Attach or project the following kinds of observables from the rich CF world:

* market prices;
* later quoted prices;
* recommendation;
* execution;
* any already-used static-view coordinate.

Then test:

> Can two architectures differ in CF agency structure while all LI-facing static observables remain identical?

If yes, this would strengthen the current Stage-V diagnosis:

> LI's epistemic machinery may constrain predictions about a future process while remaining silent about which embedded subsystem retains control.

A useful bridge theorem/witness would therefore be:

[
\text{same LI-facing observables}
\not\Rightarrow
\text{same CF agency structure}.
]

Do not infer from this that LI “cannot represent agency” in every extension.

The claim would concern the current interface.

---

# IX. Important negative controls

The exploratory phase must actively try to show that CF does **not** help.

Include adversarial constructions/tests for at least the following.

## N1. Hidden-label cheat

Construct two frames differing only because the world includes a label such as:

`controller = H`

versus

`controller = A`.

If this is the only reason the frames differ, the bridge has failed.

The target is structural control, not renamed metadata.

## N2. Duplicate behavior collapse

Test whether the supposedly distinct agency structures become biextensionally equivalent after duplicate rows/columns are collapsed.

If so, decide whether:

* that means the distinction was merely representational redundancy; or
* biextensional equivalence is too coarse for the deference notion being modeled.

Do not choose the second interpretation automatically.

## N3. Perfect simulator

Allow A to perfectly predict H on all actually encountered histories.

Does the CF distinction between H-control and A-control still exist because their counterfactual action spaces differ?

If not, report that.

## N4. Trivial future frame

Make sure the “preservation” arm genuinely leaves H⁺ multiple effective corrective possibilities.

A frame with many syntactic actions producing the same world is not evidence of practical agency.

Use the existing biextensional machinery to eliminate duplicate-action fakery where relevant.

## N5. Foreclosure by notation

Ensure that `commit`, `external`, or another operation actually changes the effective future control structure rather than merely producing a differently typed but biextensionally equivalent frame.

---

# X. Relation to the current negative results

At the end, classify each major deference obstruction.

Use a table approximately like:

| deference obstruction                    | does CF address it? | how? | remaining debt |
| ---------------------------------------- | ------------------- | ---- | -------------- |
| same realization, different jurisdiction | yes / partial / no  | ...  | ...            |
| delegation vs accurate simulation        | yes / partial / no  | ...  | ...            |
| future agent absent from model           | yes / partial / no  | ...  | ...            |
| foreclosure absent from signature        | yes / partial / no  | ...  | ...            |
| capability/admissibility conflation      | yes / partial / no  | ...  | ...            |
| computational futurity                   | likely no           | ...  | ...            |
| competence / calibration                 | likely no           | ...  | ...            |
| near-indifference leakage                | likely no           | ...  | ...            |

Do not force all rows to be positive.

---

# XI. Specific hypotheses worth testing

These are **research questions**, not claims.

## H1 — Coarse-graining hypothesis

There exist distinct CF execution architectures (C,D) and a coarse world map (p) such that:

[
C\not\approx D
]

at a relevant agency-sensitive level, while

[
p^\circ C\approx p^\circ D.
]

If true, this could provide a CF-native explanation of static-view collapse.

## H2 — Delegation/simulation hypothesis

A genuine principal-controlled execution and a perfect-simulator-controlled execution can agree extensionally on the realized action while remaining distinct as Cartesian-frame agency structures.

## H3 — Foreclosure-as-subagency hypothesis

A present foreclosing action can be represented by replacing a future-principal frame with a proper additive subagent obtained by commitment.

## H4 — Foreclosure-as-externalization hypothesis

Some jurisdiction losses are better represented by moving a choice component from the future principal's agent side to its environment side, corresponding to multiplicative subagency/externalization.

## H5 — LI-blindness hypothesis

The current Stage-V LI observables factor through a world map that can identify CF architectures with distinct control structure.

Any or all hypotheses may fail.

---

# XII. What this round must not do

Do not:

* claim Cartesian Frames prove corrigibility;
* claim CF supplies normative authority automatically;
* define “authorization” as whatever CF relation makes the theorem go through;
* re-formalize the CF paper;
* formalize FFS in this round;
* rebuild Logical Induction;
* reopen already-settled magnitude/calibration negatives;
* treat competence as solved;
* conflate structural futurity with computational futurity;
* introduce a new utility/valuation merely to reward preserved agency;
* assume preservation of future agency is normatively preferable without a separate premise;
* modify the deference theorem status merely because a representation becomes available;
* add a primitive jurisdiction tag and call that a CF solution;
* overwrite the Stage III–V negative record.

---

# XIII. Implementation strategy

Prefer a small bridge layer in the Alignment Workspace.

Suggested location:

`projects/deference/rounds/2026-08-12-cartesian-frames-bridge/`

or repository-conventional equivalent.

The round should contain:

* a technical note;
* a human-readable summary;
* finite worked models;
* exact tests where useful;
* Lean bridge statements if the Formalized-Agent-Foundations CF branch can be imported or mirrored cleanly;
* a red-team report.

Do not vendor the entire Cartesian Frames library into Alignment Workspace unless existing repository architecture explicitly requires it.

Prefer referencing/pinning the FAF branch or using minimal copied definitions only for exploratory executable models, clearly distinguishing them from the authoritative CF formalization.

If direct Lean cross-repository import is operationally awkward, do not spend the round on build engineering.

A mathematically faithful finite model plus a precise proposed Lean bridge is preferable to plumbing work that answers none of the research questions.

---

# XIV. Evidence discipline

Every conclusion must be classified.

Use at least:

* **Lean-established**
* **source-theorem fact**
* **exact finite witness**
* **structural argument**
* **architectural interpretation**
* **conjecture**
* **negative result**
* **open**

In particular:

> “These two tiny CFs differ”

is not yet

> “CF captures jurisdiction.”

Likewise:

> “Commit removes a correction action”

is not yet

> “Commit is the correct formal definition of foreclosure.”

Record the difference.

---

# XV. Red-team requirement

Run an independent adversarial review after the initial construction.

The red team should specifically ask:

1. Did the construction merely hide jurisdiction in the world type?
2. Are the supposedly distinct frames actually equivalent under the CF equivalence notion that matters?
3. Does “future corrective agency” survive biextensional collapse?
4. Is the delegation/simulation distinction robust or just syntactic provenance?
5. Did the construction implicitly assume independent counterfactual variation that the current deference model has not justified?
6. Did `commit` or `externalize` get overinterpreted because of their English names?
7. Does any claimed improvement actually touch the controlling Stage-V obstruction?
8. Does the model accidentally make the future agent presently derivable again?
9. Is any “corrigibility” conclusion really an unstated value premise about preserving options?

Substantially accept good negative findings.

---

# XVI. Possible outcomes

End the round with exactly one of these broad verdicts, qualified as necessary.

## CF-positive

Cartesian Frames naturally distinguish at least one central pair of architectures that current deference observables collapse, without encoding jurisdiction as an independent label.

A concrete next theorem target is identified.

## Representation-positive, corrigibility-open

CF supplies a credible structural language for agent/control/future-correction distinctions, but no deference or corrigibility inequality follows yet.

This is likely the best plausible positive outcome.

## Mixed

CF handles static agency/jurisdiction but not temporal foreclosure, or handles restriction but not delegation/simulation, etc.

State the split.

## CF-insufficient

The desired distinctions cannot be represented without smuggling authorization/capability into the world structure as unexplained metadata.

If so, say so clearly and assess whether FFS, resource-indexed process semantics, or another formalism addresses the actual missing structure.

Do not escalate automatically to FFS.

---

# XVII. Deliverables

At minimum:

1. `CARTESIAN_FRAMES_DEFERENCE_BRIDGE.md`

   * exact question;
   * mapping from Stage III–V obstructions to CF objects;
   * worked constructions;
   * failure cases;
   * conclusions.

2. `CARTESIAN_FRAMES_DEFERENCE_FOR_HUMANS.md`

   * concise explanation of what was tried and what changed.

3. Small executable/Lean examples for:

   * static-view collapse;
   * delegation versus simulation;
   * preserve versus foreclose.

4. A negative-controls section or test suite.

5. Independent red-team report.

6. A proposed next-step theorem/interface, **only if earned**.

7. Minimal updates to live deference routing/status surfaces if and only if the result genuinely changes the research debt classification.

Do not modify the authoritative historical records describing Stage III–V as they existed.

---

# XVIII. What would count as a particularly valuable result?

The strongest plausible result for this exploratory phase would look roughly like:

> The current deference valuation factors through a coarse observation of an execution architecture. Cartesian Frames distinguish execution architectures whose coarse observations agree by representing different embedded allocations of action/environment degrees of freedom. In particular, preservation and loss of future corrective agency can be exhibited structurally before the static observation map erases the distinction.

That is not yet a corrigibility theorem.

But it would convert the current diagnosis

> “jurisdiction is missing”

into something much sharper:

> **“Here is a formal agency structure containing the missing distinction, and here is the exact projection under which the existing deference representation forgets it.”**

That would be substantial progress.

---

# XIX. Broader workspace context

Keep the surrounding research architecture in view.

The Alignment Workspace currently has two major active lines.

## Leverage / normative learning

The leverage line has reached a working finite (\Phi)-regret construction and is now being reframed around a general normative-learning interface:

[
\text{public loss process}
+
\text{normatively compiled repair grammar}
\to
\text{online self-correction}.
]

Its central representational concerns include:

* reasons;
* answerability;
* lawful revision;
* ontology;
* historical persistence;
* counterfactual stability.

## Deference / corrigibility

The deference line asks how a bounded principal can justifiably depend on, defer to, or preserve the future corrective role of a more capable/later process.

Its repeated negative results now point toward missing embedded-agency structure:

* who controls what;
* what is prediction versus exercise of control;
* what counts as continuation of an agent;
* how future corrective possibilities can be preserved or foreclosed.

Cartesian Frames are being tested because they may supply exactly this missing structural layer.

Do not force a connection to leverage during this round.

But if the CF bridge works, record any obvious future cross-pollination questions—for example whether answerability, normative authority, or lawful-repair scopes should eventually be indexed by recognized agent/control structure.

Those are future questions only.

---

# XX. Recommended stopping rule

Stop once the round can answer:

1. Can CF represent equal realized behavior with distinct control structure?
2. Can it distinguish delegation from simulation?
3. Can it represent preservation versus foreclosure of future corrective agency?
4. Which existing CF relation/operation carries each distinction?
5. Which Stage III–V negative results does this actually repair?
6. Which negatives remain untouched?
7. Is FFS genuinely needed next, or not?

Do not continue into a full corrigibility proof simply because the answers are promising.

The next round should be designed from the resulting structural diagnosis.

**Prompt provenance:** GPT-5.6 Sol (OpenAI)
**Maintainer:** A. M. Berns

# XXI. Git / PR workflow

This is a dispatched repository round and should normally terminate in a reviewable pull request.

Unless blocked by repository policy or a genuine technical failure:

* work on a dedicated branch based on the current appropriate base;
* keep the round's changes scoped to this dispatch;
* run the repository-required tests, Lean checks, provenance checks, and other applicable gates;
* commit the completed work with the repository's required DCO/sign-off and model provenance;
* push the branch;
* **open a pull request** against the appropriate current base branch.

Do **not** merge the pull request unless the maintainer explicitly instructs you to do so or repository policy already authorizes automatic merge.

The PR body should make the research verdict legible without requiring the maintainer to reconstruct the round. At minimum include:

* the round's final verdict (`CF-positive`, `Representation-positive, corrigibility-open`, `Mixed`, or `CF-insufficient`);
* which Stage III–V negative results were actually affected;
* the strongest positive result, if any;
* important negative controls and failures;
* precise evidence classes;
* remaining debt;
* tests/build/audit status;
* new provisional terminology;
* provenance and model attribution;
* anything requiring maintainer judgment.

If the exploratory result is negative, **still open the PR**. A well-supported negative result is a first-class research deliverable in this repository.
