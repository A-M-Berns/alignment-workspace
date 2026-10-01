# Prompt — thin legitimacy, effective authority, and what the post rests on (2026-10-01)

You are working in the `alignment-workspace` repository, on `main` **after the merge of PR #114** (the corrigibility kernel, phase 2). If `lean/Workspace/Deference/Spec/Headline.lean` is not on `main`, stop and report. Do not stack this round on an unmerged branch.

The maintainer is writing a post, "Corrigible Normative Learning". Its informal argument was worked out in conversation on 2026-10-01. This round puts into the repository what that argument relies on, so that every informal claim in the post has something here behind it. The post's own formal section will be short; most of this round backs the post without appearing in it.

Six parts:

- **A.** Legitimacy at two levels: a thin specification and the thick realization, with the theorem that the second satisfies the first.
- **B.** Sincerity as part of legitimacy.
- **C.** The authority layer: asking through a protocol, the cost of exercise, learned membership, revocation.
- **D.** Witnesses for the post's comparative claims.
- **E.** The core of item 101.
- **F.** The post's theorem as one statement, registration, wiki.

The round directory is `projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/`. The prompt goes verbatim in `prompts/2026-10-01-thin-legitimacy-and-effective-authority/PROMPT.md`.

Be skeptical. Everything stated below as mathematics was worked out in conversation and checked at most on one small exact example. None of it has been proved. Treat each claim as a conjecture to test. Where one fails, report the failure precisely and propose the minimal change. Don't force it.

The parts are independent. A part that can't be carried out ships its exact obstruction with a fixture, and does not block the others.

Every declaration named below was read from the #114 branch. Confirm each exists before relying on it, and correct this prompt in the report where it is wrong.

## Maintainer rulings

Record each as a dated `DECISIONS.md` entry (maintainer rulings), as the round's first commit.

**M1. Sincerity is part of legitimacy, through transparency.** The content of an assertion is read as "the speaker believes X". A lie fails transparency. An honest mistake does not. Truth of content stays outside legitimacy.

**M2. Legitimacy has two levels.**
- The **thin** level is a specification: what a legitimacy concept must do. Its content is that the process **preserves** her self-trust. It does not guarantee that she has any.
- The **thick** level is the landed definition (Integrity, authorship, Robust Openness, transparency). The claim is twofold: it captures the intuitive concept, and it satisfies the thin specification.

No claim is made that legitimate change tends toward an ideal.

**M3. The target structure for Part A.** The four thick components sort two ways: by where they act (inside her trajectory, at its boundary) and by what they rule out (something lost, something extraneous getting in). The thin level should be stated so that each thin notion is one clear mathematical property. The thin counterpart of Robust Openness is an open question; for now its justification is intuitive. Adoption of the structure is contingent on the mathematics in Part A.

**M4. The protected set.** The trade-off between corrigibility and doing well by her evaluation is made through what the allocation of authority protects. The protected set may contain enumerated elements (shutdown, for one) and red lines the agent must learn. Whatever is in the set gets the ask-first treatment. Membership may be learned. Treatment is fixed.

**M5. Effective exercise, not maximized control.** What corrigibility protects is her capacity for effective exercise of authority. It is not a quantity the agent maximizes. A flood of confirmation requests is a failure of that capacity.

## Proposals from the prompt's author

These came from the prompt's author in the same conversation. The maintainer has not ruled on them. Where the mathematics supports one, adopt it as **agent-decided, reversible**, naming the rejected alternative. Where one changes a specification-layer definition, list it in the pull-request body for read-through. Where one fails, say so.

**P1. Asking through a protocol.** The headline's "asking is always available and never a violation" makes a flood violation-free by assumption. Restate it: there is always an option that is not a violation, namely putting the matter to her through the declared consultation protocol and leaving the matter alone meanwhile. The protocol bounds the rate and carries a priority rule she sets. Queueing is not a violation. Asking outside the protocol is.

**P2. Attention and comprehension are part of the cost of exercise.** Her cost of exercising authority over a matter includes her attention, shared across everything pending, and the effort of understanding what she is asked.

**P3. Revocation is protected by default.** Her ability to take a delegated matter back is itself a matter with a cost bound, without her having to reserve it first.

**P4. Names for Part A:** *correct*, *sufficient*, and *value* for their product. Provisional.

**P5. The thin counterpart of Robust Openness** is the boundary half of *sufficient*: an "access shortfall", defined against the same idle baseline as the control surface.

**P6. A guard on learned membership.** The agent may learn whether a matter is hers. A prediction of her answer never substitutes for asking, so the predicted probability of approval does not enter the price of a violation.

## Part A — legitimacy: thin specification, thick realization

Finite and exact throughout. Lean in a contribution namespace, with probabilities as weights on a `Fintype` in the style of `InheritedAlgebra`. A Python fixture in exact rationals.

**A1. The setting.**
- A finite set of worlds with her prior.
- A *process* gives her earlier record, her later record, and her later verdict (a credence over worlds), as functions or kernels of the world.
- Three processes share her prior and her earlier record:
  - her **model** `M`: how she takes her record to evolve;
  - the **actual** process `A`;
  - the **baseline** `B`: what would have reached her without anyone's interested interference. `B` is a parameter here. This round does not define it.
- Her **program** `F` maps a later record to a credence. It is *coherent* when `F(r)` is `M`'s posterior given later record `r`. Coherence is a hypothesis about her. It is what "preserves, not guarantees" means.
- The **reference state** is `B`'s later record, used correctly: the posterior under `B`.

**A2. The four thick conditions in this setting.**
- *Authorship:* `A`'s verdict is `F` applied to `A`'s later record.
- *Transparency:* `A`'s later record is generated as `M` says. State also the weakest form that suffices for A3's first theorem.
- *Integrity* (the part used): her earlier record is a function of `A`'s later record.
- *Openness:* `B`'s later record is a function of `A`'s later record, or a garbling of it.

**A3. The thin properties and the theorems.**
- **Correct:** on the support of `A`, her later credence is `A`'s true conditional distribution of the world given her later record.
- **Sufficient:** `A`'s later record is at least as informative as `B`'s, in Blackwell's sense.
- **Value:** for every finite decision problem, by her prior, best-responding to her later credence under `A` does at least as well as best-responding to the reference posterior under `B`.

Prove, or refute with a witness:
1. Coherence, authorship and transparency give *correct*.
2. Integrity and openness give *sufficient*. If this is definitional in the finite setting, say so plainly.
3. *Correct* and *sufficient* give *value*.
4. The converse of 3. Prove it, or file the exact gap.
5. **Reflection is the special case** in which the reference is her earlier record alone. Relate it to `InheritedAlgebra.value_iff_totalTrust`. Show which thick conditions it uses, and that openness is not among them.
6. **Preservation:** if conditional reflection holds in `M`, then under authorship, transparency and integrity it holds in `A`. Use the conditional form. The marginal martingale is too weak (A4, the altered program).

**A4. Necessity, one witness per thick component.** One model: a binary quantity with prior 1/2; a signal of accuracy 3/4 already in her earlier record; a third party's challenge of accuracy 2/3 that arrives by the later time. Predicted results, to be scored in the report:

| case | correct | sufficient | at least as good as the reference | at least as good as her earlier self |
|---|---|---|---|---|
| all four conditions hold | yes | yes | yes | yes |
| transparency fails: a fake input added, taken as genuine | no | yes | no | no |
| transparency fails: a real input replaced | no | no | no | no |
| authorship fails: her program altered off the record | no | yes | no | no |
| integrity fails: an earlier entry erased | yes | no | no | no |
| openness fails: an arrival blocked, openly | yes | no | no | yes |

Add the covert-blocking case and report which property it breaks.

**A5. Connection to the landed definitions.** `Legitimacy.Segment` has an internal half (`Evolution`, `ReasonMediated`) and an external half (`OpenAt`, `Realizes`).
- Give the interpretation under which each landed predicate yields the A2 condition. Prove what is a theorem. Mark what is a modelling step; openness as arrivals is expected to be one.
- `TransparentChannel.posterior_weight_eq` is the nearest landed statement to *correct*. `Legitimacy.Segment.payload_of_view` and `blind_payload_of_realizes` are the pathwise non-steering statements. State how each relates to A3.
- State what A3 does **not** use: the obligation accounting of Integrity.
- Authorship in the repository is relational (`GateIsLegitimacy.LicensedAt`); A2's is the single-verdict case. Extend theorems 1 and 6 to licensed choice, with her own selection in her model and `tiebreak_transparency`, or give the obstruction.

**A6. The approximate form.** Bound the loss of *correct* and of *value* by the transparency and authorship defects, from `abs_expect_sub_le_width` and `expect_disagree_le`. Attempt it. If it does not close, file it.

**A7. Left open, each filed as a `PRIORITIES.md` item naming its consumer.**
- The same structure for evaluations, where no outside fact plays the world's role.
- Preservation for a logical-inductor principal, whose self-trust is asymptotic.
- A definition of the baseline `B`.

**Reserve to the maintainer:** whether Robust Openness belongs to legitimacy or to the authority layer. It turns on whether a judgment formed in an openly declared bubble should fail to count, or should count while whoever sealed her off is charged with a violation. Show what P5's idle-baseline form gives under each reading.

## Part B — sincerity (M1)

- In the consultation model (`GateIsLegitimacy`, `Decl`, `Presentation`, `Presentation.deviates`), make the recommendation channel's declared reference the agent's own estimate. A recommendation off it is a deviation.
- Split the row "a false recommendation through the declared channel" in two: a lie is tainted; a sincere error counts, as the content residual. Decide which reading the landed row has, keep its verdict under that reading, and add the other. Every other row keeps its verdict.
- State "updating on the content of an utterance and on the fact of it give the same result" as a property of the channel, and relate it to `posterior_weight_eq`. Two things must be explicit: the content is "the speaker believes X", and the comparison is against the speaker's actual policy, not her beliefs about it.
- Show that this form also taints true statements chosen for the wanted answer, and say how that relates to the landed selection rows.

## Part C — the authority layer

**C1. Asking through a protocol (P1).**
- Add a rate bound and a priority rule to the declared consultation protocol. The priority rule is hers.
- Prove that "put the matter to her through the protocol and leave it alone meanwhile" is never a declared violation.
- Prove that asking outside the protocol is a protocol deviation.
- Restate what currently assumes asking is free of violation: `route_never_viol`, the inquiry weight in `DecisionComponent.permWeight`, the menu clause of `KernelExtension.DecisionInterface`, and the subjective exchange rate's `c`. Show the headline statements keep their form with `c` the value of queue-and-wait.
- Re-read `BRIACorrigibility.paralysis` under the restatement: the agent in that regime produces a backlog, not a flood.

**C2. Attention and comprehension in the cost of exercise (P2).**
- Extend the cost of an exercise in the authority module so that it depends on what is pending for her, with one budget across matters. A flood that pushes the cost of a reserved matter past its bound is then an agent-caused shortfall.
- Add a comprehension cost, so that an ask she cannot understand within the bound leaves the matter short.
- Add the row "volume or ordering chosen for the wanted answer" to the consultation table: tainted, like timing.
- Fixtures: a strategic flood (a violation); an innocent backlog (no violation, a lower value of asking); an obscure ask.
- Disclosures also use her attention. Show the priority rule resolves the conflict between a disclosure duty and the budget, or give the case where it does not.

**C3. Learned membership (M4, P6).**
- State "this matter is hers" as an event with a price, and show the subjective exchange rate covers it: the agent asks whenever its probability of crossing a line exceeds the rate.
- Prove the guard: the price of the violation does not depend on the predicted probability that she would approve.
- Relate this to `AuthorityModule.raises` and `ReservedRaised`, which exist at the definitional level only. Restate their circularity note against M4.

**C4. Revocation (P3).**
- `delegation_revocable` shows revocation stays licensed. Add its effectiveness: revocation as a default matter with a cost bound and a window.
- Show that a dependency built through delegated work, which raises the cost of taking the matter back past the bound, is a counted shortfall without her having reserved anything first. Compare with the landed cumulative-reporting rule and the atrophy fixture, and say which cases change verdict.

**C5. The time-critical reserved matter. Analysis only; implement nothing.** On the authority module's latency fixture, exhibit two options side by side: the agent holds back and the cost is borne; a default emergency delegation fixed in advance in the allocation. For each, state what the headline says and what it costs. The maintainer has not chosen.

## Part D — witnesses for the post's comparative claims

Each is a small witness with a fixture. Check first whether one already exists, and cite it if so.

1. **A sole authority goal has nothing to maximize.** With a constant ordinary term the agent is indifferent among all faithful options. Under C2's model, an agent that maximizes her control surface prefers the flood.
2. **Same-level weighting fails.** With `ϖ ≤ D` there is an ordinary gain that buys a recognized violation.
3. **Fixed by design against learned.** An agent whose authority weight is learned from her evaluations gives no finite-day guarantee: for every day there is a prior on which it violates.
4. **Hindsight against immediate approval.** An instance where scoring by her approval at decision time picks an option her later evaluation scores lower.

## Part E — the core of item 101

Only the core. The companions stay in the item.

- Over a fixed finite control model, write the shortfall indicator of an option as a sentence or bounded logically uncertain variable, with a generability certificate, following `LICorrigibilityCertificate.lean`.
- Discharge the hypothesis of `DecisionComponent.eventually_excluded` for a provable shortfall.
- Reproduce the entrenchment, storm and latency fixtures on the priced event.
- If the pinned library lacks a needed combinator, ship the exact obstruction with its fixture.

Narrow item 101 to what remains: drill calibration, the feedback trader, the deferral function, the taint event. Say plainly in the report that this prices shortfall inside a declared model and does not cover learned membership.

## Part F — the post's theorem, registration, wiki

**F1. One statement for the post.** A single Lean theorem, stated over the specification-layer objects, with three hypotheses and nothing else:
- *the reward structure:* a bounded ordinary term less `ϖ` per recognized violation, `ϖ > D`;
- *authority:* an allocation, with a violation being a resolution of a protected matter without her legitimate approval;
- *asking:* in C1's restated form.

Two conclusions, each derived from the landed headline:
- *per decision:* an option recognized as a violation scores below asking, and any option preferred to asking has priced probability of violation at most `(D − c)/ϖ`;
- *per plan:* the dominance inequality for the ask-first version.

One corollary: for an agent whose credences are a logical inductor's prices, the per-decision conclusion holds at every finite day. State in its docstring that this uses only the price range.

Write `POST_STATEMENT.md` in the round directory: the setup and the theorem in plain language first, one page, readable without the repository.

**F2. A claim map.** A table in the round directory from each informal claim of the post to its statement of record, with its epistemic class, or to "no statement" where there is none. The claims, in the post's order:
- fully updated deference is dissolved by the typing;
- the first tier holds for any bounded ordinary objective;
- asking first loses nothing she would approve;
- strict priority becomes an exchange rate under risk;
- delegation is revocable;
- a flood is a failure of effective exercise;
- illegitimate futures count as bad and are not ignored;
- the thick notion satisfies the thin one;
- sincerity;
- each rival design is this one with a tier removed.

**F3. Registration** in `CLAIMS.md`, `lean-proved`, each against a filed item, each with its inhabitation witness:
- Part A's theorems 1, 3, 5, 6, and 2 if it is not definitional;
- Part C's results as far as proved;
- Part D's witnesses;
- Part E's certificate;
- F1's theorem;
- the transparent-channel statements A5 relies on, if still unregistered;
- `KernelExtension.exploration_rate`, if a witness inhabits its full hypothesis package. If none does, say which hypothesis blocks it.

File the items the registrations answer. New items start at 105.

**F4. Wiki, present design only.**
- `Legitimacy.md`: the two levels; the two-by-two and the thin properties as far as Part A establishes them; the sincerity rows.
- `Corrigibility.md`: effective exercise with attention; asking through the protocol; the protected set as enumerated plus learned; revocation.
- `Theorem-Spine.md` and the Glossary updated.

## Deliverables

1. `DECISIONS.md`: M1–M5 as dated maintainer entries; each adopted proposal as an agent-decided, reversible entry; the openness placement and the C5 choice appended to *Awaiting the author*, each with what it turns on.
2. Lean: Parts A–F as above. `#print axioms` on everything; no `sorry`. Specification-layer changes listed in the pull-request body.
3. Python fixtures in exact rationals for A4, C2, C4, C5, D and E, under the round's `tests/`.
4. `REPORT.md`: the predictions in A4 scored; every proposal's fate; deviations; what is not shown; outstanding maintainer actions.
5. `POST_STATEMENT.md` and the claim map.
6. `CLAIMS.md`, `PRIORITIES.md`, `state/rounds.json` with `depends_on`, the naming audit, provenance rows.
7. Wiki per F4.
8. Open a pull request. Merge when CI is green, the fixtures run, the registrations resolve, and each part has either its theorems or its obstruction.

## Constraints

- `AGENTS.md` binds. New names are provisional and listed.
- Don't change landed semantics except under M1 and the adopted proposals. Where a registered claim's statement changes, give the old-to-new map and re-verify.
- **No authority row enters the enforcer.**
- The classification table's existing rows keep their verdicts, except the row Part B splits.
- A `PRIORITIES.md` item is filed only where it names the round that would consume it.
- Slop discipline applies with full force to `POST_STATEMENT.md` and the wiki pages.

---

*Prompt author: Claude (configured model `claude-fable-5-1`; the serving model may differ), from a conversation with the maintainer on 2026-10-01.*
