# Normativity/Legitimacy cluster — interrogation findings

All paths relative to the worktree root
`/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-02-epistemic-assessments/`.

## 0. The named hypothesis: settlement ↔ logical induction

**Verdict: GROUNDED, in a sharper form than stated — and the generalization runs
the other way at one layer.** Two senses of "settlement" live in the materials,
and the LI connection is exact at one of them and an open bridge at the other.

**At the force/market layer the connection is a theorem, not an analogy.**
`projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md` §A: the object LI
actually consumes is the evolving plausible-world family `PC(D_t)`; the
generalization replaces it with an *assessment process* `L_t`, and this is a
**proper** generalization (`allTrueLive_not_deductive`) with deduction an **exact
specialization** (`exploits_ofDeductiveProcess`), all `lean-proved` and registered
(Theorem 1 there). Theorem 5 ("deduction revisited") is the hypothesis's content
made precise: the region `K_t^D = conv(PC(D_t)|_{Φ_t})` — the prices forced by the
sentences deduction has settled — is enforced at **exactly zero risk capital**, so
the *original* LIC survives untouched and finite-time approximate coherence is
free. Proposition 6 and
`projects/normativity/notes/TRADERIZED_FORCE_INTERFACE.md` ("What a source must
do…"): **settlement and coherence rows are liability-free, always, because their
right-hand sides are minima over the assessed worlds**; substantive endorsement
rows are what cost risk capital. So: LI's decided/settled sentences are the
zero-liability case of the settled-region machinery, and the settled-region
machinery (pins + seed rows forcing intervals, `forcedRegion` in
`wiki/Seed-Theory.md`; rebuttal-by-settlement contraposition, `settleForm`) is the
proper generalization of price-forcing on a decided fragment. The maintainer's
belief is supported at this layer with Lean declarations behind it.

**At the record layer the connection is an interface plus an open bridge.** The
`wiki/Settlement-Interface.md` object (six conditions, closure receipts,
externally supplied items) connects to the market only through the realization's
three settlement functions — "certified reports translated into sentences the
assessment process settles; settlement items as citable grounds for a disposal;
and closure receipts that terminally discharge" (`wiki/Settlement-Interface.md`
§Three uses; `wiki/Normative-Inductor.md`). The arrow from the record to a credal
constraint or price region *with its liability certificate* is `PRIORITIES.md`
item 39, explicitly "deliberately absent" from the force interface
(`TRADERIZED_FORCE_INTERFACE.md`, last paragraph) and still **[open]**, narrowed
2026-10-21/22 (`PRIORITIES.md:425`: the geometric half registered as
`seed.forced-interval-spec`/`-bounds`, rowwise conformance as
`inductor.conformance`, the answer "weak" standing). And the record's interface
deliberately *refuses* the identification LI makes: in LI a decided sentence is
available, true, and usable all at once; the interface separates availability,
the closure judgment, and authority ("Availability does not establish the closure
judgment, and the judgment does not establish the item's truth",
`wiki/Settlement-Interface.md`), the separation forced by the integrity-adversary
attacks (`projects/normativity/legitimacy/rounds/2026-09-05-integrity-adversary/ATTACKS.md`).

So "direct generalization of LI's decided sentences" is right about the
settled-*region* machinery (seed/force layer) and wrong if read as a claim about
the record's settlement interface, whose relation to LI is mediated and whose
bridge (item 39) is the program's named open problem.

### Proposed links (hypothesis)

1. MISSING LINK: `logical-induction -> seed-theory`, rel `["substrate","contrast"]`,
   undirected: no — directed from logical-induction.
   Why-line: *"a settled fragment generalizes deduction's decided sentences:
   settlement pins are liability-free rows and deduction is the exact
   zero-risk-capital specialization, with the generalization proper"*.
   Evidence: `projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md` (§A,
   Theorems 1, 5, Prop 6), `projects/normativity/notes/TRADERIZED_FORCE_INTERFACE.md`
   ("settlement and coherence rows are liability-free"), `wiki/Seed-Theory.md`
   (§Rebuttal by settlement).

2. MISSING LINK: `settlement-interface -> normative-inductor`, rel `["part"]`.
   Why-line: *"one history, three settlement functions: sentences the assessment
   process settles, citable grounds for disposal, and closure receipts no
   participant can manufacture"*.
   Evidence: `wiki/Settlement-Interface.md` §Three uses of settlement in the
   realization; `wiki/Normative-Inductor.md`.

3. WIKI EDIT (load-bearing): `wiki/Settlement-Interface.md`, at the end of
   §"Three uses of settlement in the realization", insert:
   > On the price side, what a settled sentence forces is liability-free: a
   > settlement pin's right-hand side is a minimum over the assessed worlds, so
   > enforcing it consumes no risk capital — deduction, where every plausible
   > world satisfies every pin, is the exact zero-risk-capital case
   > ([Seed Theory](Seed-Theory); the traderized-enforcement round's handoff).
   The page currently gives a reader no route from the record's settlement to the
   market's, though both ends exist in the materials.
   Evidence: paths as in item 1.

4. SHALLOW: current why-line on `logical-induction -> normative-inductor` —
   *"the market, the traders, the market maker and the criterion are inherited"* —
   understates a kernel-proved fact: the inheritance passes through a **proper
   generalization** (assessment processes replacing `PC(D_t)`).
   Proposed replacement why-line: *"inherited through the assessment-process
   generalization: deduction is an exact specialization and the generalization is
   proper, both kernel-proved"*.
   Evidence: `projects/normativity/notes/GENERALIZED_LI_PAPER_HANDOFF.md`
   (Theorem 1, companion corollaries `exploits_ofDeductiveProcess`,
   `allTrueLive_not_deductive`).

## 1. Other missing links

5. MISSING LINK: `seed-theory -> enforcement-compiler`, rel `["uses"]`.
   Why-line: *"the seed's live rows compile through the same rational-row compiler
   the force layer consumes; `toForceRow` is the bridge"*.
   Evidence: `wiki/Seed-Theory.md` §The statics ("compile — through the
   rational-row compiler the force layer already consumes") and §Where the seed
   sits.

6. MISSING LINK: `farkas-duality -> seed-theory`, rel `["uses"]`.
   Why-line: *"an empty forced region is certified by a Farkas certificate whose
   positively weighted rows already suffice"*.
   Evidence: `wiki/Seed-Theory.md` §Certificates (`SureLoss`, `sureLoss_of_cert`,
   `FarkasCert.support_sound`). The existing farkas link reaches only
   `enforcement-compiler`.

7. MISSING LINK: `robust-openness -> diachronic-answerability`, rel `["uses"]`.
   Why-line: *"the other conjunct: openness is required at every state along the
   segment, and endpoint-only openness is provably insufficient"*.
   Evidence: `wiki/Theorem-Spine.md` Theorem 3.3 (`open-integrity.answerable`:
   "decomposes exactly as conservation from Integrity plus access and standing
   from Robust Openness") and Witness 3.4
   (`openness.endpoint-only-insufficient`). The current graph derives diachronic
   answerability from `integrity` alone, which misstates the theorem's shape.

8. MISSING LINK: `serviceability -> answerability`, rel `["shapes"]`.
   Why-line: *"answerability's substantive content lives in deadlines: eventual
   answering is provably no stronger than persistence, and only timeliness makes
   reasons compete for a finite budget"*.
   Evidence: `wiki/Why-Normativity.md` §Why the mathematics has to be there;
   `wiki/Theorem-Spine.md` Theorem 8.5 citing
   `projects/normativity/legitimacy/rounds/2026-08-31-normative-affordability/EVENTUAL_VS_UNIFORM_SERVICE.md`
   (persistent affordable schedule exists iff an affordable discharging plan
   exists; uniform timeliness strictly stronger);
   `wiki/Liability-and-Affordability.md` ("Persistence does not create
   competition between reasons… Timeliness does").

## 2. Shallow or wrong blurbs

9. SHALLOW/WRONG: `legitimacy-line` blurb — *"Its two halves are the record
   (Integrity: every debt tracked) and the licence (warrants: every verdict
   backed)."* The canonical definition has **four** thick components in a 2×2 —
   internal = Integrity ∧ authorship, external = Robust Openness ∧ transparency —
   and a thin specification (correct / sufficient / value: the process preserves
   her self-trust) that the thick definition provably satisfies
   (`ThinLegitimacy.value_of_thick`). "Record and licence" drops both boundary
   conditions, which are half the definition.
   Evidence: `wiki/Legitimacy.md` §Legitimacy has two levels, §Legitimacy has two
   halves; `wiki/Theorem-Spine.md` Definition 3.5.
   PROPOSED BLURB: "What makes a correction count: standing, not compliance. Four
   conditions in a two-by-two — inside the trajectory nothing entered is lost
   (Integrity) and the verdict is her program's (authorship); at its boundary
   what should reach her can (Robust Openness) and what does arrives through
   declared channels (transparency) — proved to preserve her self-trust in the
   Blackwell sense."

10. SHALLOW/WRONG: `imprecise-probability` blurb — *"The states the enforcement
    mechanism works on are exactly such convex sets."* The mechanism works on
    **price-space regions**, which are lossy projections of credal sets: "A region
    is not a semantics. If the source has a semantic credal constraint, `K_t` is
    its projection" (`projects/normativity/notes/TRADERIZED_FORCE_INTERFACE.md`),
    and "two credal sets can share a projection and differ in live worlds, and two
    can share live worlds and differ in the quantitative constraints"
    (`GENERALIZED_LI_PAPER_HANDOFF.md` §A). "Exactly" asserts the identification
    the materials go out of their way to refuse.
    PROPOSED BLURB: "Belief as a set of probability distributions rather than one.
    The credal state is the semantic object; what enforcement works on is its
    lossy projection to a price-space region, and the two lossy images — live
    worlds and price region — recover neither the credal set nor each other."

11. SHALLOW/WRONG: `progress` blurb — *"A statistic for whether the practice
    improves: repeated failures must lose weight."* "Repeated failures lose
    weight" is the **normative-response-learning** claim (its blurb already says
    so); Progress is different and narrower: the obligation-weighted statistic —
    transport-weighted anchored loss plus residual charged at the worst loss —
    whose vanishing says what was *owed* came to bear on what was *done*, ruling
    out behavioral inertness. The page is emphatic that the name went to the
    obligation-weighted form and that the service-weighted form does not imply it
    (two-surface fair-rotation countermodel: service-weighted 0, obligation-
    weighted → ½).
    Evidence: `wiki/Progress.md` (§The word does real work, §Two forms),
    `wiki/Normative-Induction.md` §The statistic.
    PROPOSED BLURB: "The statistic that rules out behavioral inertness: the
    transport-weighted loss on what was owed, with unserved mass charged at the
    worst loss. Its finite three-term bound is established; servicing only the
    dates where nothing was wrong provably cannot fake it."

12. SHALLOW/WRONG: `normative-induction` blurb — *"…a finite bound on how much
    accounted obligation can leak."* Nothing leaks in the Progress bound's
    conclusion — **Integrity** is the no-leak law ("satisfied, disposed, or still
    outstanding — nothing vanishes", its own blurb). The quantitative thread bounds
    *normative error*: evaluation-weighted practical loss plus residual, three
    terms for three failures (uptake/amplification, decision or semantic error,
    unserved mass).
    Evidence: `wiki/Normative-Induction.md` §The statistic, §The bound;
    `wiki/Theorem-Spine.md` §5.
    PROPOSED BLURB: "The quantitative thread: given the obligations a legitimate
    process has incurred, does what it owes come to bear on what it does, at a
    rate, against an evaluation committed before the responses it scores? The
    finite three-term bound on normative error is established."

13. SHALLOW: `enforcement-compiler` blurb — *"compile it into a projection of the
    market's belief state onto the region the obligation allows."* Two
    inaccuracies. The mechanism is an **added trader** — a position bought against
    the violation, entering the aggregate the market maker prices against; the
    market maker is untouched, *which is why every theorem about the underlying
    inductor survives* — the load-bearing fact the blurb omits. And the
    projection enforcer is now one of **two** realizations of one interface (the
    rowwise warrant enforcer is the registered one, `inductor.warrant-inductor`).
    Also missing: simultaneously serviced constraints are conjoined into **one
    joint region**, because individually feasible constraints can have an empty
    conjunction.
    Evidence: `wiki/Actionability-and-Normative-Force.md` §What it means for a
    reason to have force, §Several reasons at once; `wiki/Normative-Inductor.md`
    §The interface.
    PROPOSED BLURB: "How an obligation becomes a price movement: compile it into a
    trader that buys against its violation, added to the aggregate the market
    maker prices against — the maker is untouched, which is why every theorem
    about the underlying inductor survives. Constraints serviced together are
    conjoined into one joint region, failure conserves every cited obligation,
    and the core results are kernel-checked."

14. SHALLOW: `liability-affordability` blurb — *"the liability theory built on
    them is open work"* hides the sharp results the page states: the account is
    **signed and cumulative** (worst-case-per-date underwriting is strictly,
    unboundedly conservative); aggregate safety does not give per-reason safety
    (the +1/−1 two-book counterexample); and the affordability criterion is exact
    — enforcing a reason forever on any finite budget is possible iff the unit
    cost dips arbitrarily close to zero infinitely often, with persistence
    creating no competition between reasons while timeliness does.
    Evidence: `wiki/Liability-and-Affordability.md`;
    `wiki/Theorem-Spine.md` Theorem 8.5 (sharp persistence), 8.7 (accounting).
    PROPOSED BLURB: "Who pays for enforcement: the signed, cumulative account a
    norm's force draws on. Sustaining a reason forever on any finite budget is
    possible exactly when a unit of enforcement gets arbitrarily cheap infinitely
    often — persistence never makes reasons compete, deadlines do. Whether bounded
    liability is necessary, not just sufficient, for preservation is open."

15. SHALLOW (minor): `normative-inductor` blurb — *"its main theorems hold under
    stated hypotheses"* is out of date in emphasis: since 2026-10-23 the
    consolidated warrant realization is **registered**
    (`inductor.warrant-inductor`) with two witness runs discharging computability
    and liability (`inductor.witness`, `inductor.rebuttal-run`); and "what the
    record obliges" skips entitlement — the compiler receives only constraints the
    accounted state *entitles*, and licences introduce no constraint.
    Evidence: `wiki/Normative-Inductor.md` (Status 2026-10-23; §Entitlement, not
    licence).
    PROPOSED BLURB: "The central machine: a logical-induction market with one
    added trader enforcing what the accounted record entitles — never what a
    licence announces. The rowwise warrant realization is registered with two
    end-to-end runs; the projection realization's joint package stays
    conditional."

## 3. Not established

- Whether any primary material states the record→region bridge (item 39) will
  close in the settled-region vocabulary — the narrowings registered the
  geometric half, but "the normative record canonically generates the intended
  `C_t` or `L_t`" remains explicitly unclaimed
  (`GENERALIZED_LI_PAPER_HANDOFF.md` Prop 6 "What must not be claimed").
- Whether the Hoffman-constant gap between the two enforcer guarantees (item
  125) is the intended eventual unification or a permanent fork; the Inductor
  page says only "neither is retired".
- Whether the maintainer intends "settlement" on the record side and on the
  price side to merge into one concept node; the materials keep them apart
  deliberately (availability ≠ judgment ≠ truth), and a single merged node would
  erase the distinction the integrity-adversary round paid for.
- Whether `answerability-score` connects to the force layer at all; no material
  read ties the score to prices, and I propose nothing there.
