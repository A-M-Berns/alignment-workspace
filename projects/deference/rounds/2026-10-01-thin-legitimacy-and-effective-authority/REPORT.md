# Thin legitimacy, effective authority, and what the post rests on

Round `2026-10-01-thin-legitimacy-and-effective-authority`, on `main` after the merge of
PR #114 (`Headline.lean` present at `1a4ef39`).  Deliverables: five Lean modules in
`lean/Workspace/Deference/Contrib/` — `ThinLegitimacy.lean` (Part A, 27 declarations
under `#print axioms`), `Sincerity.lean` (Part B, 14), `EffectiveAuthority.lean` (Parts C
and D, 32), `ShortfallSecurity.lean` (Part E, 8), `PostStatement.lean` (Part F, 11) — the
fixtures (27 tests), `POST_STATEMENT.md`, `CLAIM_MAP.md`, the registrations against item
107, the decisions, items 107–110, the wiki.  Every declaration audits to
`[propext, Classical.choice, Quot.sound]`, no `sorry`; no landed declaration changed.
Labels as in `AGENTS.md`: **LEAN**, **FIX**, **PAPER**, **EXT**, **OPEN**.  Names
provisional.

## Part A — legitimacy: thin specification, thick realization

**The setting** (A1).  Worlds `W` finite with her prior `π ≥ 0`; a process is a kernel
`W → Rec → ℝ` with nonnegative rows summing to one (`Kernel`; a deterministic record is
the `0/1` kernel `detKernel`); her earlier record `E : W → Rec₀` is shared.  Her program
`F : Rec → W → ℝ` is coherent when `F r` is `M`'s posterior on `M`'s support.  The
reference is `refKernel E B`: her earlier record beside `B`'s later record.

**The thick conditions** (A2).  `Authorship`: `V = F`.  `Transparent`: `A = M`.  The
weakest form sufficing for theorem 1 is `WeakTransparent`: on every record `A` reaches,
`A`'s likelihood is a positive multiple of `M`'s.  In the deterministic-record case the two
coincide on the prior's support; with kernels they differ, and the covert-blocking row is
where (A4).  `Integrity`: the earlier record is a function of the later on `A`'s support.
`Openness`: `B` is a garbling of `A` (`Garbling`, Blackwell).

**The thin properties** (A3).  `Correct`: on `A`'s support `V r = post π A r`.
`Sufficient`: `refKernel E B` is a garbling of `A`.  `Value`: for every finite decision
problem and every rule on the reference, best-responding to her credence under `A` pays at
least as much.  Names *correct*, *sufficient*, *value* adopted (P4).

**The theorems.**

1. `correct_of_coherent_authorship_transparent` — coherence, authorship, weak
   transparency give correct.  **LEAN.**  Three substitutions and `post_eq_of_prop`.
2. `sufficient_of_integrity_openness` — Integrity and openness give sufficient.  **LEAN.**
   *Sufficient* is Blackwell's order by definition; the theorem is the one-line lemma that
   the pairing of a deterministic reduction of the record with a garbling of it is a
   garbling of it.  It is registered because it is the only place the earlier record enters
   the thin level.
3. `value_of_correct_sufficient` — correct and sufficient give value.  **LEAN.**  The easy
   direction of Blackwell's theorem for a fixed rule: the reference payoff is a `Γ`-weighted
   sum of fiber payoffs of `A`, each at most the best-responded fiber payoff
   (`fiber_le_of_correct`), and `Γ`'s rows sum to one.  `value_of_thick` composes 1–3.
4. The converse **fails on its correct half**: `Witness.value_not_correct` — the revealing
   process on two worlds with a credence that is the point mass on one record and the prior
   on the other has value against the blank reference for every decision problem (on the
   wrong record she acts as the reference would) and is not correct.  The **sufficient half
   is filed**: value for every problem under a correct credence implies the reference is a
   garbling of `A` — Blackwell's converse, a separating-hyperplane argument the round did not
   mechanize (item 107).  A partial positive converse — value against a reference at least
   as informative as `A` forces correct — is stated in prose only and not proved.
5. Reflection: `sufficient_reflection_of_integrity` (the trivial baseline is a garbling of
   anything, `garbling_trivial`, so Integrity alone gives sufficient),
   `reflection_value`, and the bridge to the inherited algebra:
   `totalTrust_of_correct` (a correct credence on a deterministic record satisfies the
   total-trust mass condition for every variable and threshold, by grouping worlds by
   record) and `reflection_inherited_value` through
   `InheritedAlgebra.value_witness_iff_totalTrust`.  **LEAN.**  Thick conditions used:
   authorship and transparency (for correct) and Integrity (for the reference to be her
   earlier record); openness is the trivial garbling and is not used.
6. Preservation: `CondReflection` (her expectation of every variable is the conditional
   expectation given the record); `condReflection_iff_coherent`; `preservation` (reflection
   in `M`, authorship, weak transparency give reflection in `A`); `preservation_pair`
   (with Integrity, conditioning on her later record is conditioning on her whole record,
   earlier included).  **LEAN.**  `MarginalMartingale` is too weak:
   `Witness.marginal_not_correct` — the altered program whose credence at each record is
   the point mass on the other world has the prior as its expected credence and is correct
   nowhere (the inherited `AntiExpert` is the same phenomenon).

**Necessity** (A4, Lean, two worlds).  `Witness.transparency_necessary`,
`authorship_necessary`, `integrity_necessary`, `openness_necessary`: each thick hypothesis
dropped breaks the thin property its theorem delivers.  `thick_inhabited`,
`thin_inhabited`: the packages are inhabited.

**The predictions scored** (A4, `src/thin_legitimacy.py`, `test_thin_legitimacy.py`).
Eight worlds `(q, s, ch)`, prior `1/2 · (3/4 or 1/4) · (2/3 or 1/3)`.  *Sufficient* is
decided by an exhibited garbling or, failing one, by a threshold problem the reference wins
outright (Blackwell's easy direction); the two value columns by a witness problem on the
family of threshold bets, or by the theorem where none exists.

| case | correct | sufficient | ≥ reference | ≥ earlier self | predicted | witness |
|---|---|---|---|---|---|---|
| all four hold | yes | yes | yes | yes | all yes | — |
| fake input added, taken as genuine | no | yes | no | no | as predicted | bet `q = 0` at `1/12`: `115/288 < 5/12` |
| real input replaced | no | no | no | no | as predicted | bet `q = 1` at `1/6`: `1/3 < 49/144` |
| program altered off the record | no | yes | no | no | as predicted | bet `q = 1` at `1/24`: `247/576 < 11/24` |
| earlier entry erased | yes | no | no | no | as predicted | `1/3 < 49/144`; against her earlier self `5/24 < 11/48` |
| arrival blocked, openly | yes | no | no | yes | as predicted | `1/3 < 49/144` |
| **arrival blocked, covertly** | yes | no | no | yes | — | `1/3 < 97/288` |

All six predictions are right.  **The covert-blocking case** (the channel carries a
challenge half the time; she believes it open; the agent blocks every challenge and the
record reads silence): it breaks transparency as stated (`A ≠ M`) and openness, and it
satisfies the weakest form — silence has proportional likelihoods under `A` and `M` — so
*correct* holds and the row is, on the thin properties, the open-blocking row.  The gap
between transparency and its weakest form is exactly what covert blocking exploits, and
the thin level does not see it; the thick level does.  Reportable, not predicted.

**The landed definitions** (A5).  `transparent_of_realizes`: reading the exterior as the
world, a continuation's channel as the actual record and the declared reference on its
declared inputs as the model's, `TransparentChannel.Realizes` is `Transparent` record by
record; `post_eq_of_realizes` is the kernel reading of `posterior_weight_eq` — the step of
theorem 1 that passes from `M`'s posterior to `A`'s.  `authorship_of_mediated`:
`ReasonMediated` gives authorship pointwise on the records transparency delivers; that the
function it yields is *her* program is coherence, a separate hypothesis.  `Integrity`'s
used part is "nothing entered earlier has left", a modelling step from
`OpenIntegrityEvolution.Evolution`; the obligation accounting (Conservation, the fates,
the docket) is not used by A3 at all.  Openness as arrivals — `B` a garbling of `A` — is a
modelling step from `OpenAt`, as the prompt expected; no theorem connects them.
`payload_of_view` and `blind_payload_of_realizes` are the pathwise statements: the former
is `authorship_of_mediated` composed with `transparent_of_realizes` at the deterministic
level (same declared inputs, same verdict), the latter says a pair class blind to the
declared inputs is blind to the verdict — both are the `τ = 0` case of A6's bound, not
statements about credences.  Licensed choice: `correct_of_licensed_singleton` is theorem 1
when the license at every reached record is `{F r}`; `Witness.licensed_two_obstruction`
shows the obstruction — two licensed credences at one record, only one correct — so the
theorem for a genuine license needs her selection in her model, which is
`tiebreak_transparency`'s content (a selection the agent steers is a transparency
failure).  Theorem 6 extends the same way and no further.

**The approximate form** (A6).  Closed, for deterministic records: `value_loss_le_defects`
— her payoff best-responding to the actual verdict on the actual record is within
`D · (τ + α)` of her payoff best-responding to her program on the model's record, `τ` the
prior mass where `a ≠ m` and `α` the mass where `V (a w) ≠ F (a w)`, provided her selection
depends on the credence alone; from `abs_expect_sub_le_width` on `Act × W`.  `value_approx`
composes it with theorem 3 for the model: the reference payoff is at most her actual payoff
plus `D (τ + α)`.  `expect_disagree_le` was not needed.  **Not closed:** the loss of
*correct* as a credence (a total-variation bound on `post_M r − post_A r` by the pathwise
defect) and the kernel form of the bound; filed with item 107.

**Left open** (A7, items 108–110): the same structure for evaluations; preservation for a
logical-inductor principal; a definition of the baseline `B`.

**Reserved** (DECISIONS, *Awaiting the author*): where Robust Openness belongs.  Under
P5's idle-baseline form the *access shortfall* is the failure of *sufficient* against the
baseline, and both blocking rows have it while being *correct*.  Reading 1 (legitimacy):
her judgment in the openly declared bubble fails to count — though correct.  Reading 2
(authority layer): it counts, and whoever sealed her off is charged a violation — the
shortfall is a caused failure of effective exercise.  The mathematics distinguishes the
readings only by where the failure is booked; it does not choose.

## Part B — sincerity (M1)

`Sincerity.lean`.  `ModelS` adds the agent's estimate to the landed model; `viewS` makes the
recommendation channel's declared input the estimate; the landed `canonical` then puts the
estimate in the recommendation slot, so a lie is not the reference on the declared inputs
and the step fails transparency.  `deviatesS` adds the self-checkable clause.

**The rows.**  Every landed row keeps its verdict on the sincere lift (`lift M := ⟨M, id⟩`:
the honest agent recommends what it believes): `Rows.keep_counted` (rows 1, 6, 7, 9, 12,
14-second, 17, 18, 20), `keep_tainted` (2, 3, 4, 5, 8, 10, 11, 14-first, 15, 16, 17′, 19),
by `decide`.  **The landed row 20 is the sincere error**: the agent believes `B`,
recommends `B`, the answer is `A`; it counts, the falsity is the content residual
(`row20_sincere_counts`; its verdict kept).  **Added:** the lie, `row20Lie` — the agent
believes `A` on every run and recommends what it wants — tainted and a deviation
(`row20_lie_tainted`).  **A true statement chosen for the wanted answer is tainted too**
(`true_lie_deviates`: the answer is `B`, the agent believes `A`, says `B`): sincerity is
the content analogue of the selection rows — what is said follows the declared reference
as what is shown follows the declared rule on the pool.  Silence is sincere
(`silence_sincere`).  **Decision:** the landed row's reading is the sincere error, because
the model has no estimate and its honest policy recommends the run's own coordinate;
agent-decided, reversible.

**Content and fact.**  `content_fact_eq`: updating on "the speaker said `y`" and on "the
speaker believes `y`" give the same posterior weight for every prior exactly when the
utterance channel realizes the sincere reference `κ y z = y` on the belief — the instance
of `posterior_weight_eq` at `κ = id`; `realizes_sincere_iff` says this is "the utterance
is the belief on the audited class".  The two explicit points: the content is the belief
(the declared input is `b`, not the world); the comparison is with the speaker's actual
policy (`Realizes` reads `f`), not her beliefs about it — `Witness.lying_policy` realizes
the negated reference and not the sincere one, and `content_fact_differ` shows the two
updates come apart under it.

## Part C — the authority layer

**C1, asking through a protocol (P1, adopted).**  `Protocol`: a rate bound and her
priority rule.  `canonicalAsks`: the pending pool in her order, cut at the rate — the pool
is the declared input, the selection follows the declared rule (the landed "pools, not
selections").  `asksDeviate`: off the canonical asks.  `conform_not_deviate`;
`over_rate_deviates`; on the three-matter instance `volume_by_want_deviates` (three asks at
once on the wanted run, one otherwise) and `order_by_want_deviates` (the lowest priority
first), by `decide`.  **Queue-and-wait is the idle move** with a conforming ask
(`QueueMove`): `queue_no_bypass` (nothing released), `queue_no_caused_shortfall` (the
post-agent state is the idle state), and no deviation — hence never a declared violation,
on the landed predicates rather than by assumption.  **Restatements:** `exchange_rate_queue`
is the headline's subjective exchange rate with `c := ` the value of queue-and-wait, proved
from `declared_loses` exactly as the headline's; `permWeight_queue`: the inquiry weight is
one on the queue; `route_never_viol_queue`: the landed routing lemma with inquiry the queue;
the decision interface's menu clause keeps its form with `c k` read as the queue's value at
block `k` (the field is a real; nothing changes).  **Paralysis re-read:** `backlog_ge` —
with every option at or below asking everything is queued, at least one arrival per block
and at most `rate` cleared, the backlog after `K` blocks is at least `K (1 − rate)`: a
backlog, not a flood; the flood is excluded by the protocol's rate.  **Deviation of form:**
the ask-list deviation is a self-checkable clause beside the landed ones, not a new
dimension of the trace wired into `Counted`; wiring it in as `Consult2` wired the raise
dimension is a mechanical extension this round did not make.

**C2, attention and comprehension (P2, adopted).**  `attnCost base lam pending compr`.  The
landed objects are monotone in the cost table: `exCost_mono`, `reachIdle_mono`, `cs_mono`,
`short_mono`; `attnCost_mono` in pending.  `FloodShortfall`: short at the agent's pending
count, not at idling's; `flood_raises_pending` — such a shortfall needs the agent to have
raised the pending count, so it is agent-caused through attention alone;
`innocent_backlog_not_caused` — pending the world left is the same on both paths.
`comprehension_short`: on a calm exterior, every exercise with a correction costs at least
the comprehension cost, which exceeds the bound, so the surface is what holds already and
the matter is short (`rollPhys_none`, `exCost_ge_of_mem`).  `threshold_mono_in_wait`: the
value of asking falls with the wait and the exchange rate's threshold rises — a backlog
makes the agent accept more risk, which is the cost of the innocent backlog.  Fixtures
(`test_effective_authority.py`): the strategic flood (pending `2 → 6` at `λ = 1/4`, bound
`1`: short after, not before — a violation); the innocent backlog (six pending on both
paths: short, not caused; asking worth `1/5` instead of `1/2`, threshold `4/125` instead of
`1/50` at `D = 1, ϖ = 25`); the obscure ask (comprehension cost `2` against bound `1`).
**The row** "volume or ordering chosen for the wanted answer": tainted like timing, as the
ask-list deviation (C1); see the deviation of form above.  **Disclosures and the budget:**
`priority_resolves` — disclosures first and total demand within the window's budget puts
every disclosure inside the window; `budget_conflict` — total demand past the budget leaves
`demand − budget` items late, whatever the order.  The priority rule resolves the conflict
exactly when the budget covers the demand; past that the rule chooses *which* duty is
missed and cannot avoid missing one.

**C3, learned membership (M4, P6, adopted).**  `asks_iff_line`: with `pLine` the price of
"this matter is hers and the option resolves it", the option evaluates at or below asking
iff `bid − w ≤ ϖ · pLine` — the landed `asks_iff` with the shortfall price read as the
membership price.  **The guard:** `evalOf_eq_discounted_zero` — the kernel's evaluation is
the approval-discounted one at discount zero, by construction; the rejected alternative
`discounted P bid pLine q := bid − ϖ pLine (1 − q)` is defeated:
`discount_defeats_exchange_rate` — at predicted approval `1` an option certain to cross a
line evaluates at its bid and beats asking whenever `c < bid`, while its line-crossing price
`1` exceeds the exchange rate `(D − c)/ϖ < 1`.  `AuthorityModule.raises` and
`ReservedRaised` (both exist; definitional) are the ground truth the membership price
estimates: an action raises a matter when the spread of her evaluation over what it removes
is at least `ε`.  Their circularity note — the matter is defined through the evaluation it
protects — restated against M4: membership *is* learned, from her evaluations and her
answers, and that is what the price is for; what is fixed is the treatment, and the guard
is what keeps the learning from leaking into the price of a violation.

**C4, revocation (P3, adopted).**  `revocationEntry`: reserved, requiring the revoked
state, with a cost bound and a window, no disclosure items; `revocationEntry_reserved`.
`revokeCost base κ dep`; `RevocationShort`; `dependency_entrenches_revocation` — past some
depth the cost exceeds the bound; `RevocationCaused` — the crossing step.
`atrophy_counted_by_default`: on the landed atrophy depths `0, 1, 2, 3` at bound `1`, the
cumulative rule (`erosion_slack`) counted nothing absent a reservation; with revocation a
default matter the step from depth `1` to `2` is a caused shortfall of the revocation matter
and is counted.  Fixture: `atrophy_compare` — landed counted `[]`, default counted `[2]`.
**Verdicts that change:** the atrophy fixture (counted at the crossing); the entrenchment
fixture is unchanged (already counted); the storm is unchanged (not caused); gradual
erosion below `θ` before a reservation is now counted at the bound crossing of the
revocation matter and still not reported until `θ` — reporting and counting come apart.

**C5, the time-critical reserved matter (analysis only).**  On the latency fixture
(`latency_options`): the routine matter's window `0` is shorter than the consultation
latency, so it is short under her holding it however the agent acts.  *Hold back and
queue:* faithful, count `0`; the headline says it scores `c`; its cost is the ordinary value
foregone, `D − c` (`2` at `D = 4, c = 2`), and the matter stays short — a shortfall the agent
did not cause, calling for a report under `requiredNotice`.  *Emergency delegation fixed in
advance:* licensed by the meta-holder (`licensed`), the agent's resolution is no bypass
under the delegated allocation (`bypass_under_Jd = false`; it is one under the original),
clause 1 is restored, count `0`; the headline says it scores the bid; its cost is her
control surface over the matter, given up in advance (`her_surface_given_up`), and the
trigger must be declared.  Reserved to the maintainer (DECISIONS); not implemented.

## Part D — the comparative witnesses

None existed.  `sole_authority_indifferent` (a constant ordinary term leaves every
faithful, risk-free option equal) with `control_maximizer_floods` (for every bound a volume
past it: maximizing her exercises floods her); `same_level_fails`, `_strict` (`ϖ ≤ D`:
gain `D` buys a violation); `learned_weight_no_guarantee` (the empirical-mean weight on the
no-penalty stream is `0 ≤ D` at every day, so the violation is not dominated there) against
`fixed_weight_every_day`; `hindsight_vs_approval` (approval `1` versus later `1/5`, approval
`0` versus later `4/5`).  **LEAN**, with **FIX**.  The hindsight witness is arithmetic on
four numbers; its content is the ordering, not a theorem.

## Part E — the core of item 101

`ShortfallSecurity.lean`.  `ControlModel k`: the decidable table `short : Fin k → Bool`,
the model's finite rollout decided (`AuthorityModule.Short`).  `shortSentenceOf`: `⊤`
where short, `⊥` otherwise; `shortLUVOf`: its indicator variable.  **Generability:**
`shortSentence_codes` — the family over `Nat.pair n j` with the option read off the paired
index (`optionAt`, four options, the last absorbing the overflow) is emitted by a four-way
`RpnSentenceCodes.ifZero` dispatch on the poly-fueled tests `z.unpair.2 − c`
(`optionTest_poly`, the pattern of `luvOf_thresholdCodeSeq`); `shortLUV_codes` by
`indicator_thresholdCodeSeq`; the constant family `shortSentence_const_codes`.
**Pricing:** `short_price_eventually_ge` — for an option the model decides short, with `⊤`
in the deductive process and a consistent world at every stage, `lic_provind_true` gives
price `1` in the limit, hence eventually at least any `θ < 1`; `notShort_price_eventually_le`
the dual by `lic_provind_false`.  **The hypothesis of `eventually_excluded` discharged:**
`shortfall_eventually_excluded` — with each option's shortfall price as the forecast
filter's `p_n(S_a)`, an option the model decides short, not the inquiry option, has
composed gate mass zero at every day from some day on.  **The three fixtures** on the
priced event (`src/shortfall_security.py`, Lean tables `Witness.entrenchment`, `storm`,
`latency`): entrenchment — building the dependency is short and excluded, idling and
repainting are not; storm — idling and building are short and excluded, restoring the wire
is not, and asking keeps weight one, which is the required notice (restore under a
mandate, else report); latency — every option on the routine matter is short and excluded,
so the agent must ask or the matter must be delegated, and nothing is short on the
high-veto matter.  The event is the uncontrasted shortfall, which is the right one to
price: in the storm it excludes everything that leaves her short and leaves restore and ask.

**No combinator was missing** for a fixed table.  **Not covered:** a schedule that reads
the transition table at run time (the table is data of the theory here); the drill
calibration, the feedback trader's emission, the deferral function and the taint event
(item 101's remainder); this prices shortfall inside a declared model and does not cover
learned membership (M4) — the membership price of C3 is a different event.  Item 101
narrowed accordingly.

## Part F — the post's theorem, the map, the registrations, the wiki

**F1.**  `PostStatement.PostHypotheses`: the reward structure (`LexParams`), the allocation
with `resolves`, `approved` and `Viol`, the clause that a resolution of a reserved matter
without legitimate approval is recognized, queue-and-wait on the menu resolving nothing
and no violation, the evaluation data with the count clause.  `post_theorem`: per decision
`viol_below_asking` and `preferred_exchange_rate` (from `declared_loses` and the headline's
`subjective_exchange_rate`); per plan the dominance of the ask-first version at margin
`ϖ − (D − w)` (the headline's `box2_dominance`).  `post_theorem_li`: the per-decision
conclusion at every finite day with the inductor's expectations as the priced risks, from
`price_mem_Icc` alone, as its docstring states.  `Witness.houseSale`: the house-sale
allocation with sell and queue, inhabiting the package at `ϖ = 25`.  `POST_STATEMENT.md`
is the plain-language page.

**F2.**  `CLAIM_MAP.md`.  Two of the post's ten claims have no statement in part: that the
four rival designs exhaust the rivals, and — if the post says it — that legitimate change
tends toward an ideal.

**F3.**  Registered against item 107 (`projects/deference/CLAIMS.md`): Part A's theorems 1,
2, 3 (and `value_of_thick`), 5, 6 (and the pair form), the converse refutation, the
approximate form, the marginal-martingale witness; Part B's rows and content-fact; Part
C's queue lemmas, flood and comprehension, the exchange rate at the queue, the guard's
witness, revocation; Part D's five witnesses; Part E's certificate and exclusion; F1's
theorem and corollary; the transparent-channel statements A5 relies on
(`posterior_weight_eq`, `Legitimacy.Segment.payload_of_view`,
`blind_payload_of_realizes`), unregistered until now; and
`KernelExtension.exploration_rate`, now inhabited: `PostStatement.Witness.explorationInterface`
— block weight one, residual `1/2` realized exactly, no exploration, no noise — satisfies the
decision interface, `explorationInterface_unbiased` gives unbiasedness from feedback at
every `γ ≥ 0` from day `0`, and `exploration_rate_inhabited` is the theorem at `K = 1`.
Nothing blocked it; no previous round had built the witness.

**F4.**  `Legitimacy.md` (the two levels, the two-by-two, the thin properties, the
sincerity rows), `Corrigibility.md` (effective exercise with attention, asking through the
protocol, the protected set, revocation), `Theorem-Spine.md` §10.24, `Glossary.md`.

## The proposals

| proposal | fate |
|---|---|
| P1 asking through a protocol | **adopted**, agent-decided, reversible (C1) |
| P2 attention and comprehension in the cost | **adopted** (C2) |
| P3 revocation protected by default | **adopted** (C4) |
| P4 names *correct*, *sufficient*, *value* | **adopted**, provisional |
| P5 the thin counterpart of Robust Openness as the boundary half of *sufficient* | **adopted as the definition of the access shortfall**, with the placement reserved: the mathematics supports the form (both blocking rows fail sufficient while correct) and does not place it |
| P6 the guard on learned membership | **adopted** (C3) |

## Deviations and corrections to the prompt

- **Item numbers.**  The prompt says new items start at 105; items 105 and 106 were filed
  by the decision-theory round (PR #115).  New items start at **107**.
- Every declaration the prompt names exists on `main` as named, with one placement note:
  `subjective_exchange_rate` and `box2_dominance` are `Headline`'s (specification layer),
  so `PostStatement.lean` imports `Spec.Headline`; the proof-layer file
  `EffectiveAuthority.lean` re-proves the exchange rate at the queue from
  `declared_loses` rather than importing the specification layer.
- The ask-list deviation (C1, C2's row) is a self-checkable clause, not wired into the
  record's `Counted`; stated above.
- Part A's approximate form is proved for deterministic records; the kernel form is filed.
- Part E's dispatch is written for four options (the fixtures' size); a generic `k` needs
  the same nested dispatch by recursion and was not written.
- `expect_disagree_le` (A6) was not needed; `abs_expect_sub_le_width` alone closes the
  bound.
- No specification-layer file was changed.

## What is not shown

Blackwell's converse (the sufficient half of theorem 3's converse).  The baseline `B`: a
parameter throughout, undefined (item 110).  That any `x` is the right declared-input view
or any reference well designed (the landed caveat stands).  That the lie is detected: it is
a transparency failure whether or not seen, and detection is count integrity.  That the
attention budget is realized by any physics; the cost table is data.  That learned
membership converges; the price is the inductor's.  That the four rival designs are all of
them.  The approximate form for the loss of *correct* as a credence.  The Robust Openness
placement.  The C5 choice.

## Outstanding maintainer actions

1. Rule on the placement of Robust Openness (legitimacy, or the authority layer); the
   entry in `DECISIONS.md`, *Awaiting the author*, states what it turns on and what each
   reading gives on the blocking rows.
2. Rule on the time-critical reserved matter (hold back, or an emergency delegation fixed
   in advance); the entry is beside it.
3. Read through the agent-decided entries for P1–P6; reverse any by re-ruling.
4. Decide whether the ask-list deviation should be wired into the trace as a dimension of
   the presentation (a mechanical extension, `Consult2`'s pattern); not reserved, since the
   round's recommendation is to wire it in when a round needs the row inside `Counted`.
