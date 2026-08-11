# Triangle compatibility — Track F report

Dispatch: `PROMPT.md` beside this file, verbatim. Authorizing item: `PRIORITIES.md` 19
(WP-G). Snapshot: `alignment-workspace` at `990a822`, branch
`round/2026-08-11-deference-corrigibility`.

**Attribution.** Prompt-author-model: GPT-5.6 Sol (OpenAI). Executor-model: Claude
Opus 5 (Anthropic), model id `claude-opus-5`. Date: 2026-08-11. Review status:
`ci-only`. No Lean was built; no file outside this directory was touched.

Path key, used in the Evidence column:

| key | path |
|---|---|
| `RM` | `projects/deference/notes/CORRIGIBILITY_ROADMAP.md` |
| `SK` | `projects/deference/notes/FINITE_MODEL_SKELETON.md` |
| `LG` | `projects/deference/notes/CORRIGIBILITY_PAPER_LEDGER.md` |
| `DQ` | `projects/deference/notes/DISPATCH_QUEUE.md` |
| `ADD` | `prompts/2026-08-11-deference-corrigibility/PROMPT-integration-addendum.md` |
| `FA` | `projects/deference/note-dump-2026-06-27/notes/faithful-acceleration.md` |
| `PT` | `projects/deference/note-dump-2026-06-27/notes/pointwise-tower-and-faithful-acceleration.md` |
| `SC` | `projects/deference/note-dump-2026-06-27/notes/faithful-acceleration-scope.md` |
| `NT` | `projects/deference/note-dump-2026-06-27/anson-notes/no-timely-pointwise-tower.md` |
| `FD` | `projects/deference/note-dump-2026-06-27/anson-notes/frozen-deliberation-deference-v6.md` |
| `SUM` | `projects/deference/note-dump-2026-06-27/anson-notes/trust-between-inductors-summary-v2.md` |
| `AUD` | `projects/deference/note-dump-2026-06-27/lean/AUDIT.md` |
| `LEAN` | `projects/deference/note-dump-2026-06-27/lean/` |

---

## 0. The classification discipline, stated before the table

The table is only worth reading if the reader knows what stopped a row from being
promoted. Two rules were applied mechanically.

**A row is `conditionally compatible` only when the `A → H⁺` cell has fixed content
and the condition is a choice among options already enumerated in a fixed
document** — which of the roadmap's three settlement reaches, which skeleton
instantiation. If closing the row would require a commitment that appears nowhere
fixed, the row is `unresolved` and the would-be commitment is reported in §13 as a
proposal, never as a condition. Without this rule every row could be made
`conditionally compatible` by naming its own missing premise as its condition,
which is the failure mode the item exists to prevent.

**A row is `compatible` only when both cells have fixed content that positively
agrees.** "No conflict found" between a requirement and an *absent* commitment is
`unresolved`, not `compatible`.

One structural fact explains most of the outcome, and it is the audit's real
finding: **the fixed `A → H⁺` architecture is an ordering-and-measurability
architecture with no cost model, no market, and no trader class** (`SK` §8.3:
trader legality and the market are "absent entirely … must not be read as" closed).
**Every load-bearing `H → A` requirement that is not a pure ordering condition is a
cost condition, a market condition, or a settlement-semantics condition.**
Compatibility is therefore decidable exactly on the ordering fragment and on nothing
else. That is not a gap in this audit; it is the shape of the work.

---

## 1. Exact result — the matrix

| # | Interface | `H → A` requirement | `A → H⁺` fixed content | Status | Evidence |
|---|---|---|---|---|---|
| 1 | Timing — event ordering | emission `e(n)` < horizon `F(n)` < settlement `σ(n)`; the trade weight is formed at day `n` from day-`n` observables and cashed out at `f(n)` | `t(n) < F(n)` (`SK` §1); "placement precedes settlement … future principal information must not leak into placement" | **compatible** | `FD` §3 "Schedules"; `FA` §5; `SK` §1; `RM` standing commitments |
| 2 | Timing — resource schedule | `e ≥ R` (emission dominates coupled cost); `σ(n) ≥ c·R_H(F(n))` for the timely form of T1; `F` superpolynomial, canonically `2ⁿ`; `𝒞_A` affords `R_H(F(n))` (A4) | none — the skeleton carries no cost function, no per-stage cost, no `R` | **unresolved** | `FD` §3–§4 (A4, A5), `SUM` §4 "Schedules and computational assumptions"; `SK` §8.3 |
| 3 | Advisory access — principal reads the advisor | required and load-bearing: a ledger settling `A`'s published quote as an ordinary decided fact, `𝒞_A`-hard to generate and `𝒞_H`-cheap to read; "the theorem fails with either [channel] alone" | **no carrier.** `SK` §4 conducts are interventions; there is no published-advice object anywhere in the skeleton. The only fixed content is that admissibility must "permit intended advisory influence" | **unresolved** (skeleton deficiency, §7) | `FA` §3 "Mutual observability"; `FD` §3 (A2), §4; `SK` §4; `RM` "Admissibility is not syntactic" |
| 4 | Advisory access — advisor reads the realized principal | required: `A` records `H`'s realized prices, so ingredient (II) has feedback by the deferral and nothing is forward-simulated | `SK` §5 instantiations 1 and 2 make a principal-side quantity `F(n)`-measurable; instantiation 3 settles nothing epistemic. The choice is a `maintainer-decision` | **conditionally compatible** — condition in §2 | `FA` §4 (II), §8 obligation 1; `SK` §5; `RM` "Settlement architecture — candidate, not endorsed"; `LG` Movement II |
| 5 | Information flow — measurability and non-leakage | placement uses only decision-time observables (`a_n`, `H`'s own day-`n` price); the target is realized only at `f(n)` | `SK` §3: `v̂⁺` is `t(n)`-measurable, `v⁺` is `F(n)`-measurable — "the skeleton's whole account of the asymmetry"; `RM` no-leakage | **compatible** (with the provisionality note in §3) | `FA` §5; `SK` §3; `RM`; `ADD` §1 |
| 6 | Information flow — no forward self-simulation | `𝒞_A` must **not** be required to contain `R_A ∘ F`; the calibration ingredient is checked after the fact precisely so the regress never arises | none. The nearest object is the `FU[g]` hole, which by construction needs "a time-indexed family of `A`-valuations" | **unresolved** (risk flagged, §5) | `NT` §4 (2b); `FA` §4 first bullet; `SK` §4, §8.1 |
| 7 | Settlement — which reach settles what | two incompatible inherited routes: the frozen route needs principal-report settlement at `σ(n)` against a held-out deliberation; the faithful-acceleration route needs **no** hard settlement anywhere (obligation 3 — never settle a contract against a discontinuous function of `a_n`) | three reaches enumerated and explicitly **not endorsed**; "the choice is a maintainer decision" | **unresolved** | `FD` §5; `FA` §8 obligation 3; `SC` §5, §8; `RM` "Settlement architecture"; `LG` Movement II |
| 8 | Reference-process identity | the inherited corpus carries **three** distinct reference objects with different reach: the autonomous `H` (never reads `A`), the sealed family `H^[n]` (frozen prefix), and the coupled `H⁺` (reads `A`) | the roadmap names two vertices, `H` and `H⁺`, and identifies neither with an inherited object; protected-reference composition (WP-I) is downstream and unscheduled | **unresolved** — see §4 | `SUM` §4 "The honest cost"; `FD` §3, §5; `FA` §3; `NT` §0; `RM` "The question", WP-I |
| 9 | Seals / blindness | **derived, not assumed**: the settlement target must hold out `A`'s current and future output, else 2a or 2b applies. The price is a *family* of one inductor per index, which is exactly why off-`G` soundness is unforceable | none. The skeleton attaches no seal to `v⁺`, and permits `v⁺` to be `t(n)`-measurable (the perfectly-predictable-principal case the program may not rule out) | **unresolved** | `FD` §5 "Why the current quote is held out", Target-Soundness; `SUM` §2.2 dichotomy; `SK` §3 |
| 10 | Influence | forced faithfulness cannot distinguish predicting an independent principal from predicting a steered one, off the checkable fragment; the trace shows the same vanishing error either way | "prediction is permitted; substitution is not"; `π^SIM` and `π^{FU,g}` are distinct families; conducts are "identified by [their] rule and evaluated through [their] quantity" | **unresolved** — standing constraint in §6 | `FD` "The manipulation question, stated exactly"; T7; `PT` §6; `SK` §4; `RM` standing commitments; `LG` Movement III |
| 11 | Trader populations | `𝒞_H ⊆ 𝒞_A`, each closed under polynomial overhead and c.e., canonically `P ⊆ EXP`; A4 power, satisfiable **only because** the target is blind to `A`; and the forcing weight must itself be a legal trader — which the inherited Lean does not model | **explicitly absent** | `FD` §3 (the concrete satisfying choice), §4 (A4); `AUD` §3.1; `SK` §8.3 |
| 12 | Admissibility | a restriction on the **contract family**: the theorem holds off the quote-referencing family, characterized *semantically* (the target hard-settles as a discontinuous, anti-inductive function of `a_n`), not syntactically | a restriction on **conducts and traders**, with six stated requirements; "none is installed here"; under active attack as item 20 | **unresolved** — carrier mismatch, §7 | `SC` §3, §6, §7; `PT` §4.1; `RM` "Admissibility is not syntactic"; `SK` §8.2 |
| 13 | Update timing / patience | the weighting must be *patient* — deferred until the feedback is in; the trader thins to a sparse schedule on which the windows `[n, f(n)]` are disjoint, which is what bounds risk | `SK` §6 declines to fix an update rule ("avoids committing to an update rule the round has not decided"); §8.6 states results per decision index with no cross-decision structure | **unresolved** — see §5 | `FA` §4, §5 proof; `SK` §6, §8.6; `DQ` (WP-D "needs … an explicit patience regime"); `PRIORITIES.md` 18 |
| 14 | Certification failure direction | settlement-powered forcing is co-extensive with settlement and goes **silent** when settlement is withdrawn; `A` cannot pin `H`'s credence on an unresolvable question | fail-closed is fixed and may not be traded away: `¬Cert` disables or cedes `A`'s discretion and never means human correction waits for `A` | **compatible** | `FD` T7 and its v4 gloss, T5; `SUM` §5 "The central safety property"; `FA` §7; `RM`; `PRIORITIES.md` 16 |
| 15 | Forcing mechanism | the relation is made a theorem by an exploiting trader in a market with settlement; the exploit itself is *not* formalized anywhere in the inherited Lean | none — WP-D is "the major open theorem" and explicitly not an unconstrained proof dispatch; no market exists in the skeleton | **unresolved** — obstruction in §6 | `AUD` §1, §3.1; `RM` WP-D; `DQ` "Not dispatchable in this wave"; `LG` "The standing gap" |

**Counts: `compatible` 3 · `conditionally compatible` 1 · `incompatible` 0 ·
`unresolved` 11 · total 15.**

`unresolved` dominates, and that is the honest state of the work. Two further
qualifications on the three `compatible` rows, so the count is not read as stronger
than it is: rows 1 and 5 are two aspects of **one** underlying agreement (the
decide-early / verify-late asymmetry), so the three compatible rows rest on two
independent facts, not three. And row 14 is compatibility of a *failure direction*,
not of a positive requirement.

Against the decomposition the dispatch offered: when-influence is rows 1, 2, 5, 13;
what-influence is rows 3, 4, 9, 12; destination faithfulness is rows 7, 8, 10, 14;
rows 6, 11, 15 are the mechanism questions that sit under all three.

## 2. The one condition (row 4)

**Condition.** The settlement instantiation must be `SK` §5.1 (grade/report), or a
declared `F(n)`-measurable subset of §5.2 (world/outcome), so that a realized
principal-side quantity becomes available at `F(n)` and can serve as the feedback
the calibration ingredient consumes. Under §5.3 (underwriting/enforcement) the
condition fails: nothing epistemic settles, so the `H → A` calibration channel has
no counterpart on the reverse arrow, and the reverse relation — whatever it then is
— is not the same kind of object.

This is precisely the maintainer decision `RM` and `LG` reserve. It is listed in §12.

## 3. Provisionality of row 5's reverse cell

`ADD` §1 instructs the integration phase to treat the skeleton's timing account —
actual delegation `F(n)`-measurable, simulator acting at `t(n)` — as "a provisional
modeling choice, not yet … the final conceptual account of prediction vs
substitution," and asks whether timing alone is doing the conceptual work. Row 5
therefore records consistency with a modeling choice the maintainer has already
flagged as unsettled, not with a settled account. Row 1's reverse cell is more
robust, because placement-precedes-settlement is a standing commitment in `RM`
rather than a skeleton detail.

`ADD` was explicitly not fed back into the active tracks and was not used as an
instruction here; it is cited only as fixed content of the snapshot bearing on what
counts as fixed.

## 4. Reference-process identity — the naming defect (row 8)

The inherited corpus does not use `H` and `H⁺` consistently, and the roadmap's two
vertices do not map onto the inherited objects without a decision.

- `FD` §3 names three inductors: `A`; `H⁺`, "the advised reasoner", founded over the
  weaker reasoner's world plus the full quote ledger; and the family `{H^[n]}`, the
  frozen-deliberation settlement target, which keeps quotes `a_{<n}` and freezes.
- `SUM` §4 makes the *live* target the **autonomous** `H`, "where `H` never reads
  `A`", and states the resulting cost plainly: "the *predicted* reasoner (`H`,
  unadvised) and the *advised* reasoner (`H⁺`, the realistic one) are different
  objects, so the headline is about a counterfactual."
- `FA` §3 and `PT` §1 use `H` for the **coupled** reasoner that does read `A`, whose
  lookahead credence `Y_n = E^H_{f(n)}(X)` is the calibration target.

So the inherited forward-arrow results are not all about the same `H`, and the
strongest of them (`FD` T3, T4) are stated for `H⁺` — the object the roadmap places
at the *destination* of the reverse arrow. Which inherited object the roadmap's `H`
is, and which its `H⁺` is, is unrecorded. Every downstream composition claim depends
on that answer, and the three objects have provably different reach: pointwise per
day on `G` only (sealed family), averaged over the admissible domain (coupled),
counterfactual-but-pointwise (autonomous).

## 5. Two transported risks, marked as inference

Neither is established. Both are stated so they can be attacked.

**`FU[g]` may inherit 2b.** The skeleton's `FU[g]` hole needs "a time-indexed family
of `A`-valuations" (`SK` §4, §8.1). 2b is the theorem that a trader required to
price the coupled system forward to the horizon would need `𝒞_A ∋ R_A ∘ F`, "a
contradiction, since the market would have to sit strictly above its own trader
class" (`NT` §4). Whether filling the hole puts `A`'s own later valuations inside
something that must be *priced at decision time* is not fixed, so the regress may or
may not appear. Class: conjecture.

**Sparse scheduling versus densification.** The inherited trader buys bounded risk
by thinning to a schedule with disjoint windows `[n, f(n)]` (`FA` §5 proof). Item 18
asks whether exposure weights can keep outstanding delayed exposure bounded while
the harvest against persistent defect diverges — the same geometry, from the other
side. The two are plainly the same quantity; whether the inherited thinning is
compatible with any useful density is exactly item 18's open question. Class: an
observed coincidence of quantities, not a result. Note also that the disjointness
condition appears **only in the prose proof**: `LEAN/FaithfulAcceleration.lean`'s
`FaithfulAccel.soft_total_trust_doublysoft` sums over every index in range, and
bounded risk enters as the named hypothesis `hbdd`, consistent with `AUD` §3.1.

## 6. The one cross-arrow obstruction the audit found (row 15)

Stated as a conditional, because the reverse arrow has no fixed forcing mechanism.

> **If** the `A → H⁺` relation is to be forced by a trader argument in a market
> whose reference quantity is the actual principal's later report, **then** that
> quantity is responsive to `A`'s own conduct — the principal sees what `A` did
> before correcting it — which is the coupled-target configuration 2a and 2b
> jointly kill on the forward arrow. The inherited repair is to seal the target
> against `A`'s current output (`FD` §5, derived from the two impossibilities). But
> a corrective authority sealed from what it is correcting is not corrective
> authority, so the forward arrow's repair is unavailable on the reverse arrow in
> the form it took there.

This is the sharpest thing the two arrows say to each other, and it is why row 15 is
not a bookkeeping row. It is **not** an incompatibility finding: the reverse relation
may be established by something other than a market argument, and nothing fixed says
it is a market argument. It is a named target for a counterexample or a proof.

The escape route the inherited work already exhibits is worth recording alongside
it: `FD` keeps *all past* quotes in the target and drops only the current one — "the
maximal design respecting blindness" — so a seal against the current index is not a
seal against the advisor's history. Whether that suffices for a reverse-arrow
correction quantity is open.

**A standing constraint the inherited work does impose on Movement III (row 10).**
Any criterion separating prediction from substitution that is purely *extensional*
over the observable trace is already refuted by inherited material: `FD`'s
manipulation section establishes that "the trace shows the same vanishing prediction
error whether the AI is faithfully predicting an independent human or predicting a
human it has steered," and `SUM` §6 records the companion "one cannot certify *why*
the advisor is right from its behavioral trace." The fixed `A → H⁺` side is already
built to survive this — `SK` §4 identifies a conduct by its **rule** and only
evaluates it through its quantity — so this is a consistency, not a conflict. It is
recorded because it forecloses a whole family of candidate criteria in advance for
item 17.

## 7. Two carrier defects in the shared vocabulary

**The skeleton has no advice object (row 3).** Its conducts are interventions
chosen by `A`; nothing in it corresponds to the quote ledger, which on the forward
arrow is what makes advice `𝒞_H`-readable and is one of the two channels without
which the theorem fails. Reported as a deficiency per `DQ`; the minimal patch shape
would be a per-index published quantity emitted by `A` at `t(n)` and available to
the principal thereafter. Not proposed as a definition, and no name is offered.

**"Admissibility" names two different restrictions (row 12).** On the forward arrow
it restricts the **contract family** — which questions the theorem covers. On the
reverse arrow it restricts **conducts and traders** — which comparator policies the
delegation inequality must beat. Item 20's red team and the inherited admissible
domain are therefore not attacking the same object, and a result from one does not
transfer to the other without an argument nobody has written.

Within that caveat, the inherited work supplies two things item 20 asked for. The
separating axis it locates is **semantic, not syntactic**, which is what `RM`
requires: the price-level liar `χ ↔ (P^H(χ) < ½)` is benign because the target is
continuous and independent of `a_n`, while `g_n ↔ (a_n ≤ ½)` is fatal because the
target hard-settles to `𝟙[a_n ≤ ½]`, a discontinuous anti-inductive function of
`a_n` (`SC` §3). Mentioning the quote is *not* the separator, because the forcing
machinery mentions it too. And the strongest explicit disagreement-exploitation
template the architecture currently supports is constructed and kernel-checked:
`FaithfulAccel.dsWeight` = `softInd δ (a − t) · softInd δ (t − ε − p)`, with
`FaithfulAccel.dsWeight_continuous` proving the joint continuity a hard indicator
violates, consumed by `FaithfulAccel.soft_total_trust_doublysoft`. That weight is
quote-responsive and continuous, so any candidate admissibility family must admit
it while excluding `g_n` — the test `RM` calls "the one that bites", with a concrete
object to run it against.

## 8. Evidence class

No claim in this report is above `test-supported`, and most are documentary.

- The `H → A` column is `inherited-established` in `LG`'s sense where `LG` says so,
  and read here from the notes and `AUD`. **No Lean was rebuilt in this round**, per
  the dispatch's prohibition; the inherited tree carries its own toolchain, and
  `PRIORITIES.md` 14 owns the confirmation.
- The `A → H⁺` column is a documentary reading of `RM`, `SK`, `LG`, `DQ` and `ADD`.
  It records what those documents fix, not what is true.
- The classifications are the author's judgment under the §0 discipline. They are
  **not** claims registered anywhere and nothing here belongs in `CLAIMS.md`.
- §5 and §6 are explicitly inference: conjecture and a conditional obstruction.

Reading `AUD` as evidence carries `LG`'s standing caveat: it attests, it does not
recheck. Where this report cites a Lean declaration name it was read directly from
`LEAN/FaithfulAcceleration.lean` at this snapshot, not from `AUD`.

## 9. Files, declarations, checks

Read: `AGENTS.md`; `PRIORITIES.md` items 14–20; `RM`; `LG`; `DQ`; `SK`; `ADD`; `AUD`;
`FA`; `PT`; `SC`; `NT`; `FD`; `SUM`; `projects/deference/note-dump-2026-06-27/ORIGIN.md`;
`projects/deference/note-dump-2026-06-27/anson-notes/INDEX.md`; targeted reads in
`LEAN/FaithfulAcceleration.lean` and `LEAN/TowerAndAcceleration.lean`; one grep of
`anson-notes/trust-between-inductors-chats/05_2026-06-06_quote-resolution-audit.md`.

Declarations cited, all verified present in `LEAN/FaithfulAcceleration.lean` at this
snapshot: `FaithfulAccel.softInd`, `FaithfulAccel.dsWeight`,
`FaithfulAccel.dsWeight_continuous`, `FaithfulAccel.dsWeight_pos_imp_fst`,
`FaithfulAccel.dsWeight_pos_imp_snd`, `FaithfulAccel.soft_total_trust`,
`FaithfulAccel.soft_total_trust_doublysoft`. From
`LEAN/TowerAndAcceleration.lean`: `TowerAccel.two_faces_distinct`,
`TowerAccel.witness_gap`, `TowerAccel.witness_tracking_fails`.

Checks run: none. No `lake build` (prohibited this wave), no Python runner, no
gate. This deliverable is a matrix and its evidence, and it is `ci-only` in the
strong sense that no CI job bears on it.

## 10. What was not established

- **No compatibility of the triangle was established.** Three rows agree on
  ordering and one failure direction; eleven have no reverse-arrow content to
  compare against.
- **No row was shown incompatible.** Zero `incompatible` is not a clean bill of
  health — it is a consequence of the reverse arrow being mostly unfixed. An
  interface with no fixed content cannot be contradicted.
- The `H → A` requirements are read from notes, not rechecked. `SC` establishes that
  two inherited notes flatly disagreed about the theorem's scope and that `FA`
  over-claims; `SC`'s recommended edits to `FA` §4, §5 and §6 **have not been made**
  in the consolidated tree, so `FA` still reads "over all sentences" while `SC` and
  `PT` say "admissible domain". This report uses the corrected claim.
- The forcing itself is not established anywhere, on either arrow: `AUD` §3.1 and
  `LG` "The standing gap" record that "criterion ⇒ the forcing inequality" is nowhere
  in the corpus, and `SK` §8.3 records that the skeleton does not close it. Every row
  in this matrix sits above that gap.
- Whether the inherited forward-arrow results compose with anything on the reverse
  arrow is not established and could not be, because row 8 is unresolved: the
  objects have not been identified.
- The two chat-derived items in the corpus that bear on influence — the
  usefulness-forces-an-uninspectable-channel result and the density refinement — are
  self-rated in the source at roughly 70–75% with the construction named as the main
  risk, and they are chat material rather than a note. Nothing in the matrix rests
  on them.

## 11. Assumptions added, deviations, provisional names

**Assumptions added: none.** The §0 classification discipline is a reporting
convention, not a mathematical assumption; it is stated so a reader can recompute
every classification from the two cells.

**Deviations.**

1. The dispatch names the parent snapshot as `ec7d6cc`; the branch head this track
   ran against is `990a822` ("Freeze the wave-1 snapshot and record the seven track
   dispatches"), which is also the snapshot `ADD` names. The difference is one
   commit that adds the round's prompt directories. No inherited or specification
   content differs.
2. `DQ` records Track F as not binding to the skeleton. The skeleton was nonetheless
   used as evidence of fixed `A → H⁺` content, because for rows 1, 3, 4, 5, 6, 9, 13
   it is the *only* fixed content that exists. It is treated as a frozen round
   specification with its own declared holes, never as a canonical model — which is
   what `SK` §§8, 10 ask for.
3. The dispatch lists ten interfaces; the matrix has fifteen rows. Timing, advisory
   access and information flow were each split in two, because in each case the two
   halves receive different classifications and merging them would hide a
   `compatible` inside an `unresolved` or the reverse. Two rows were added:
   certification failure direction (14), which is the only other place the fixed
   reverse-arrow content meets an inherited fact, and forcing mechanism (15), which
   carries §6.
4. The round's `REPORT.md` was produced as report text by the executing agent rather
   than written to disk by it; the harness running this track blocked the file write.
   Content is unaffected.

**Provisional names: none introduced.** The report uses the skeleton's own §9
provisional vocabulary and the inherited notes' existing names unchanged. The patch
shape suggested in §7 is deliberately left unnamed.

## 12. Maintainer decisions surfaced

1. **The settlement interpretation** (already reserved in `RM` and `LG`; row 4's
   condition and row 7 both turn on it).
2. **Which inherited object is the roadmap's `H`, and which its `H⁺`** — three
   candidates, provably different reach (§4). Not previously recorded as a decision.
3. **Whether "admissibility" continues to name two different restrictions** (§7), or
   whether one of the two gets a different word before item 20 reports.
4. **Whether the skeleton acquires an advice carrier** (§7), given that the forward
   arrow's theorem fails without one.

## 13. Next recommended theorem or experiment

In value order.

1. **Decide row 8 first.** It is a naming decision, not mathematics, and it is
   upstream of every composition claim in the round. Nothing else on this list is
   worth doing before it.
2. **Attack §6's conditional obstruction directly**, as a targeted counterexample
   rather than a proof attempt: exhibit the smallest reverse-arrow configuration in
   which the correction quantity is responsive to `A`'s own conduct, and determine
   whether the 2a diagonal is constructible in it. `DQ` permits targeted
   counterexamples in this wave. If the diagonal is constructible, the reverse arrow
   cannot be forced by a market argument against an unsealed correction quantity,
   and that is a result.
3. **Run `FaithfulAccel.dsWeight` against every candidate admissibility family** item
   20 produces — the concrete instance of `RM`'s requirement that the forcing
   machinery stay admissible (§7).
4. **State the `H → A` requirement list once, canonically**, in the vocabulary of
   whatever carrier survives. This audit had to reconstruct it from five notes that
   disagree about scope and about which `H` they mean, and the reconstruction is the
   most fragile input to the matrix.

---

## Outstanding maintainer actions

1. **Decide the settlement interpretation** — which of `RM`'s three reaches, or which
   hybrid, governs. Row 4's condition and row 7 are both blocked on it, and `LG`
   already carries it as a `maintainer-decision`. Exact form: an entry in
   `DECISIONS.md` naming the reach or the hybrid, and an edit to `RM`'s "Settlement
   architecture" section replacing "candidate, not endorsed."
2. **Identify the roadmap's `H` and `H⁺` with inherited objects** — the autonomous
   `H` of `SUM` §4, the sealed family `{H^[n]}` of `FD` §3, or the coupled `H⁺` of
   `FD` §3 / `FA` §3. Exact form: a sentence in `RM` "The question" fixing each
   vertex, and a `DECISIONS.md` entry. Until this is done no cross-track composition
   claim in this round is well-formed.
3. **Decide whether the skeleton gains an advice carrier before skeleton v2.** If it
   does, `SK` §10 requires a new version number and every track that consumed v1 is
   rerun or explicitly reconciled — including this one, whose rows 3, 4 and 13 would
   change.
4. **Decide whether "admissibility" keeps naming both the contract-family
   restriction and the conduct/trader restriction.** Exact form: either a note in
   `RM`'s standing commitments stating the two senses, or a rename of one of them
   before item 20 reports and fixes the ambiguity in a second document.
5. **Carry `SC`'s three unmade corrections to `FA` §4, §5 and §6, or record that the
   consolidated tree keeps the over-claim.** `SC` is in the same consolidated tree
   and contradicts `FA` on the theorem's scope; a reader who opens `FA` alone gets
   the wrong claim. Per `AGENTS.md` standard 1 this is an edit to an
   `agent-consolidated` tree, so it needs a stated reason in the commit and a
   `DECISIONS.md` entry — which is why it is a maintainer action and not something
   this round did.
6. **Write this report to `prompts/2026-08-11-deference-triangle/REPORT.md`.** The
   executing agent's harness blocked the file write; the content above is the
   deliverable verbatim. *(Discharged by the orchestrator, 2026-08-11.)*
