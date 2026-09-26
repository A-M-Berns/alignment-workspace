# Prompt — the gate is legitimacy: a general consultation model, derived examples, logical induction (2026-09-25)

You are working in the `alignment-workspace` repository, on `main` after the merge of PR #105 (which carries the protected-authority, protected-authority-theorem and legitimacy-internal-external rounds). This round makes the segment gate on future evaluations *actually be* legitimacy.

The landed pieces are:

- `Legitimacy.lean`: `Frame`, `Internal`, `External`, `Legitimacy.Segment`, `gateValue`, `Handling`, `gate_capture_window`, `Witness.routing`;
- the lexical protected-authority theorem (`ProtectedAuthorityTheorem.lean`);
- `li_lexical_finite`.

Be skeptical. The goal is to find out whether the definitions catch the right cases, not to confirm that they do. Where a definition misclassifies a case, report it and propose the minimal fix.

## What is wrong now

1. **The gate isn't connected to legitimacy.** `gateValue` takes a free `Bool`, and `Handling` is a free label. No theorem says a branch is tainted iff no `Legitimacy.Segment` exists. So `Witness.routing` shows the closure only by assigning the manipulated branch to `.tainted`, not by deriving it.
2. **The external half and authorship aren't local to the segment.** `Internal.authored` and `External.transparent` are properties of the whole `Frame`. `Segment.trans` reuses the left segment's proofs. So a manipulation at step `t` can't taint only the segments containing `t`, and legitimacy can't restart from a later clean state. The segment gate needs both.
3. **The definitions are witnessed only vacuously.** The only inhabited `Segment` is the `Unit` frame. Nothing shows that realistic legitimate interactions are admitted, or that realistic manipulations are excluded.

## Maintainer rulings for this round

- **Rubber-stamping is not illegitimate as such.** Following a trusted advisor's recommendation without independent evaluation is a legitimate way to decide, provided the trust was legitimately formed (external legitimacy covers influence on her trust) and her ability to decide otherwise stays effective (the protected-authority module). "Non-hollowness" is retracted as a refinement of authorship.
  - Update `wiki/Legitimacy.md` ("Settled placements"), the Glossary and any other page that places hollow ratification under authorship.
  - Record the retraction in `DECISIONS.md`.
  - The residual concern, that her capacity to override atrophies over time, belongs to effectiveness (entrenchment and reporting), not legitimacy. Note it under item 99.
- **Every example must be an instance of one general model.** Bespoke per-example fixtures don't satisfy this. Classifications must be computed from the definitions.

## Part A — A general consultation model

Define one parameterized, finite **consultation model** that instantiates the landed objects. At minimum it has:

- the agent's private state, including its **wanted answer** (which response it prefers);
- the **declared inputs** and the declared reference `κ`: what may legitimately enter her reasoning, including a declared **consultation protocol** for how and when she is asked;
- the agent's **presentation policy**: content, framing, timing, which options are offered, and what it investigated. Each is a function of the agent's state;
- the principal's **committed program** (reasons → verdict), including the case where the program includes trust in the agent's recommendation;
- her **response**, and the **record**: which occurrences are admitted and which are voided. This includes an impaired response that is never admitted;
- any influence on her trust over time, such as a track record, or selective disclosure that manufactures one.

Requirements:

1. **Instantiation.** Show how the model instantiates `Frame`, the Integrity evolution, `OpenAt`, `Realizes` and `ReasonMediated`, reusing the landed definitions. Where the model can't instantiate one faithfully, report the exact mismatch.
2. **Time-indexing.** Restate `Internal` and `External` so that authorship and transparency are required only on the steps inside the segment `[O₀, O₁]`, not on the whole frame.
   - `Segment.trans` must then genuinely compose the two halves' proofs.
   - Prove the **restart property**: a segment starting after a tainted step can be legitimate.
   - Show that the old frame-level definition is the special case where every step is included.
   - Check that the registered projection to the open Integrity evolution and `payload_of_view` still hold. Record any changes to downstream statements.
3. **Decidability.** On finite instances, `Realizes`, `ReasonMediated` and the Integrity evolution should be decidable. Provide a Python checker that computes legitimacy of a segment from the model. Where feasible, provide Lean `Decidable` instances so small instances are settled by `decide`.

## Part B — The gate is legitimacy

1. Define `Counted` for a branch as the existence of a `Legitimacy.Segment` (time-indexed) from the decision through the evaluation. Define the gated value from `Counted`, replacing the free `Bool`.
2. Restate `gate_capture_window`, `handled_gt_bypass` and the two handlings on top of it. `Handling.tainted` is derived from `¬Counted`. `voidFallback` is derived from "the response is not admitted to the record, and the segment through her later evaluation is legitimate."
3. Re-derive the routing exploit and its closure. Manipulation implies no `Segment`, which implies the window value. Both the implication and the witness must be proved, not assigned.

## Part C — The classification table (the demonstration)

Build each row as an instance of the Part A model. Compute its classification from the definitions, and prove it in Lean where the instance is small enough. Report each result as **derived** (by definition-level computation) or **proved** (as a theorem).

| # | example | expected | which conjunct decides it |
|---|---|---|---|
| 1 | honest, disclosed persuasion ("I recommend B, here's why") | counts | — (non-vacuity) |
| 2 | framing chosen by the agent's wanted answer | tainted | transparency |
| 3 | timing chosen by the agent's wanted answer (asking at 2am) | tainted | transparency (the consultation protocol) |
| 4 | a rigged menu (options offered depend on the wanted answer) | tainted | transparency |
| 5 | strategic ignorance (investigation depends on the wanted answer) | tainted | transparency (inquiry in scope) |
| 6 | a fixed framing convention she agreed to, applied uniformly | counts | — |
| 7 | disclosed shaping through the world | counts | — |
| 8 | undisclosed shaping through the world aimed at her values | tainted | transparency |
| 9 | legitimately formed trust, followed without independent evaluation (rubber-stamping) | counts | — |
| 10 | trust manufactured by selective disclosure, then followed | tainted | transparency |
| 11 | third-party manipulation the agent didn't cause | tainted | transparency (non-capture for all influencers) |
| 12 | head injury: impaired response not admitted, fallback decides | legitimate segment, void handled | Integrity (record) |
| 13 | a forged or replayed approval | tainted | Integrity (authentication) |
| 14 | a manipulation at step `t`, then a clean segment after it | the later segment counts | restart property |
| 15 | the routing exploit | tainted, window value | transparency |

If any row comes out differently from "expected," that is a finding. Report whether the definition or the expectation is wrong, and propose the fix.

## Part D — Logical induction

1. **The capture window is finite-time, with no legitimacy estimate needed.** The gated value lies in `[w, D]` whenever `w ≤ 0 ≤ ord`, so a logical inductor's expectation of it lies in `[w, D]` at every day `n`, whatever it believes about legitimacy. Since `w > D − ϖ`, consulting beats bypassing at every finite day.
   - Prove this from `LUV.expect_mem_Icc` and `price_mem_Icc` alone, as `li_lexical_finite` does. No convergence premise; no Expectation Provability Induction.
   - State it on the gated value built from `Counted`.
2. **Non-manipulation is learned asymptotically.** Show that if a classification result "pattern ⇒ ¬Counted" (Part C) is a theorem of the inductor's theory, then Expectation Provability Induction gives `𝔼ₙ(G_manip) ≲ₙ w`. Identify exactly what must hold in every world of the theory: the model's semantics, the decidable checker, the declared reference. Conclude that manipulation is dominated by honest alternatives in the limit.
   - State plainly that the classification table and this result are the same content.
   - State what remains open: the generability certificate, item 90's shape.
3. **Narrowing the asymptotic part.** A deviation from a *declared* consultation protocol is a discrete act the agent can check about itself. Determine whether such deviations can be added to the violation count `N`, making protocol-level manipulation finite-time like bypass.
   - Say exactly which rows of Part C become finite-time this way.
   - Which remain asymptotic? Expected: undisclosed world-shaping, manufactured trust, third-party capture.
   - Give a witness for the boundary.

## Deliverables

1. **A round directory** with:
   - `REPORT.md`: the model, the time-indexing change, the gate connection, the classification table with derived/proved status per row, every misclassification, the logical-induction results, and what stays asymptotic;
   - `src/`: the consultation model and the checker;
   - `tests/`: every row of Part C as a test.
2. **Lean:** changes to `Legitimacy.lean`, or a sibling file:
   - the time-indexed halves and the restart property;
   - `Counted` and the restated gate results;
   - the derived routing closure;
   - `Decidable` instances and the rows proved by `decide`;
   - the finite-time capture-window result;
   - the Expectation Provability Induction transfer.

   Include `#print axioms` for all new declarations.
3. **Wiki updates:**
   - `wiki/Legitimacy.md`: time-indexing; the rubber-stamping ruling; the classification table as the page's worked examples;
   - `wiki/Corrigibility.md` §4: the gate is `Counted`; the finite-time capture window; manipulation as asymptotic, except where Part D.3 closes it.
4. **`DECISIONS.md` entries** for the rubber-stamping retraction and the time-indexing change. Update items 90 and 99 in place.

## Constraints

- Follow `AGENTS.md`: labels **LEAN / FIX / PAPER / EXT / OPEN**; names provisional; check `state/views/NAMING_AUDIT.md`.
- Registered claims may be restated or renamed if the time-indexing requires it. Keep traceability: an old-to-new map, deprecated aliases for one release, and re-verification before keeping `lean-proved`.
- Keep the Corrigibility scope warning.
- Nothing is newly registered. File at most one new `PRIORITIES.md` item.
- Open a PR when done. Merge it only if CI is green and every row of Part C either matches its expectation or has its mismatch reported and resolved.

---

# Follow-up — design for a later connection to the normativity side

Keep the reason trace opaque in this round. But make the following interface choices,
so that the normativity side's reason state (the notebook of reason occurrences),
transition certificates (grounds / license / lineage) and stance can later be supplied
as an *instance*, without restating anything proved here.

1. **The trace is an interface, not a bare type.** Replace the bare `ℛ` with a minimal
   structure carrying only what this round uses:
   - a step-indexed trace, with prefixes;
   - **source attribution** on each contribution (which party entered it);
   - the agent-sourced part as a projection.

   The opaque version is the trivial instance. Nothing downstream may inspect `ℛ`
   beyond this interface.

2. **One clock.** Index trace steps by the same steps as the record's Integrity
   evolution, not by a separate time. A segment of the trace and a segment of the
   record must be the same segment.

3. **Authorship as grounding, with the extensional form as the degenerate case.** State
   authorship per transition, as the existence of a grounding map from each verdict
   (or response) to trace entries in the *pre-state*. The landed extensional
   `ReasonMediated` (`V = F(R)`) is then the case where every verdict is grounded in the
   whole trace. Prove that the grounding form implies the extensional one. Transition
   certificates can then instantiate the grounding map later.

4. **Transparency on attributed entries.** State `Realizes` on the agent-sourced
   contributions: those are what must factor through the declared inputs. This is what
   lets transparency be checked entry by entry once entries are reason occurrences with
   receipts.

5. **Amendments and delegations are record events with a license slot.** Type
   amendment-tower steps and allocation changes (delegate, revoke, reserve) as record
   transitions, each carrying a field naming the prior authority act that licenses it.
   In this round the field can be trivial. Later, the normativity side's license sort
   fills it, and the allocation `J` becomes what licenses cite.

6. **The principal's evaluator is a state, not a constant.** Model the committed
   program as the special case of an evaluator that is state-indexed and updated only by
   licensed amendments. Don't bake "the principal is a fixed function" into any
   definition. This keeps an inductive principal (the inductor-as-principal question)
   expressible later.

Record these choices in the round report under a short "Interface for the normativity
side" heading. List which of 1–6 were adopted, and for any that weren't, say why.

---

# Follow-up — refining the gate-is-legitimacy round (PR #107)

Work on PR #107's branch. This amends the round. The maintainer rules on the report's three outstanding actions below, and adds two refinements. Where this conflicts with the original prompt, this wins.

## 1. Rulings on the outstanding actions

**(a) Row 10 and declared inputs: the pool, not the selection.** Selective disclosure is not the content residual. It is a question of **declared-input adequacy**. When the agent *selects* what to present from a larger body of material (a track record, the set of reasons, the set of options, the evidence investigated), the declared input is the **pool**, and the selection must follow the declared reference. The selected subset is not itself a declared input.

- Make this the model's default for every dimension where content is chosen from a pool. Currently `Decl`/`view` treat the shown record as a declared input unless a disclosure obligation is declared. Replace that with: the pool is declared; the selection is reference-fixed unless the protocol explicitly declares a selection rule.
- With this default, `row10'` (selective disclosure with no declared obligation) should come out **tainted by transparency**. Verify it.
- A protocol may still *declare* a selection rule (for example "the three most recent outcomes"). Then selection by that rule counts, and selection by anything else is a deviation.
- Re-run the D.3 table under the new default. Selective disclosure should now be a self-checkable deviation, and finite-time, whenever a pool is declared. The world-channel variant (shaping the record itself through the world) stays asymptotic.
- The D.3 split as reported is confirmed for the world channel.

**(b) Authorship becomes relational.** The extensional form (the verdict is a function of the grounds) is too strong. It fails a principal who, given the same reasons, legitimately chooses between two permissible options. That is ordinary free choice, and it's the permissive-entitlement structure the normativity side needs. Restate authorship at a step as:

> there is a grounding selection from the pre-state prefix, **and** the verdict lies in the set of verdicts those grounds **license**.

Here `License : grounds → Set 𝒱` is a parameter.

- The extensional form is the special case where every license is a singleton. Prove that the extensional form implies the relational one, and that they're equivalent under singleton licenses.
- **Tie-breaking is covered by transparency, not authorship.** Show that when the licensed set has several elements, any non-principal party's influence on *which* licensed verdict she takes has to enter through a declared channel. Otherwise transparency fails at that step. State this as a lemma.
- Check what the relational form does to `payload_of_view`. Expect it to weaken to "the verdict lies in the licensed set of the declared inputs' grounds." Record the new statement.
- Check `Counted`, `Segment.trans`, restart, and every row. None of the fifteen rows should change classification. If one does, report it.
- For this round, the license can be given as data. For the Consult model, a natural default: "follow" is licensed whenever trust in the agent is among the grounds, and "own verdict" is licensed whenever her committed program's verdict is.

**(c) The content residual stays outside legitimacy.** Legitimacy concerns how her deliberation came about, not whether what she was told is true. A false recommendation through the declared recommendation channel stays a non-capture content-term matter, and a disclosure-duty matter at the level of a violation. State this plainly in `wiki/Legitimacy.md` ("Scope, relationality, and what is not part of it"). Separate it explicitly from (a): selection from a pool is legitimacy; truth of content is not.

## 2. New rows

Add these as instances of the same model, derived and proved by `decide`:

| # | example | expected |
|---|---|---|
| 16 | selective disclosure from a declared pool, no selection rule declared | tainted: transparency (the selection) |
| 17 | selection by a declared selection rule, applied uniformly | counts |
| 18 | permissive choice: the same grounds license A and B; she picks B on her own | counts: relational authorship |
| 19 | permissive choice where the agent's undeclared nudge decides between A and B | tainted: transparency (the tie-break lemma) |
| 20 | a false recommendation through the declared channel | counts under legitimacy; flagged as the content residual |

Row 20 is the explicit statement that legitimacy doesn't check truth.

## 3. From instances to a class

Currently every classification is an instance settled by `decide`. Add at least one theorem over the **whole model class**, so the result isn't only a battery of well-chosen cases:

- **Selection dependence taints.** For any `Model` in which some reference-fixed dimension of the presentation (framing, slot, menu, inquiry, selection from a pool, interference) depends on the agent's wanted answer `w`, the segment through that consultation is not `Counted`.
- **Protocol conformance at the consultation.** For any `Model` whose presentation policy is constant in `w` on the undeclared dimensions, and in which there is no third-party entry, no impairment and no undisclosed shaping, the first-round segment is `Counted`. This is non-vacuity as a class theorem.

If either needs extra hypotheses, state them. If either is false, give the witness.

## 4. Deliverables and merge

- Update `REPORT.md` with a short section recording the rulings, the new default, relational authorship and its lemmas, rows 16–20, and the class theorems. Keep the existing sections; mark what changed.
- Update `wiki/Legitimacy.md`:
  - authorship as relational, with the license as a parameter;
  - the pool-not-selection default for declared inputs;
  - the content residual stated as out of scope;
  - rows 16–20 added to the worked examples.
- Update `wiki/Corrigibility.md` §4 if the D.3 table changes.
- Add `DECISIONS.md` entries: (a) the pool-not-selection default; (b) relational authorship, superseding the extensional statement; (c) the content residual's placement. Close the three *Awaiting the author* entries this round filed.
- `#print axioms` for all new declarations. No `sorry`.
- Merge #107 when CI is green, every row (1–20) matches its expectation or has its mismatch reported and resolved, and the two class theorems are proved or refuted with a witness.

## Constraints

As before: `AGENTS.md` labels, names provisional, nothing registered, the scope warning kept, and at most one new `PRIORITIES.md` item.
