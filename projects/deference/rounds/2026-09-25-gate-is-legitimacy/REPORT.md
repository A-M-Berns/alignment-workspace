# The gate is legitimacy: one consultation model, derived examples, logical induction (2026-09-25)

Round `projects/deference/rounds/2026-09-25-gate-is-legitimacy/`, on `main` after the
legitimacy-internal-external round.  Lean
`lean/Workspace/Deference/Contrib/GateIsLegitimacy.lean` (59 audited declarations; the
landed `Legitimacy.lean` is untouched and consumed); fixtures `src/consult.py`,
`tests/test_rows.py` (20 tests, every row of the table among them).  Labels **LEAN / FIX /
PAPER / EXT / OPEN**; names provisional.

## 1. What was wrong, and what now holds

| defect in the landed round | resolution | where |
|---|---|---|
| `gateValue` took a free `Bool`; `Witness.routing` assigned `.tainted` | **`Counted` is the existence of a time-indexed segment**; `gatedValue` and `handlingOf` are built from it; the routing closure is derived: interference fails transparency at the first consultation, so no segment exists, so the branch scores the window value | **LEAN** `Counted`, `gatedValue`, `handlingOf`, `not_counted_of_step`, `Consult.Rows.r15`, `Rows.routing`; **FIX** `test_row15_routing_closure_is_derived` |
| authorship and transparency were properties of the whole frame; `Segment.trans` reused the left proofs | **both halves are required only at the steps inside the segment**; `Segment.trans` composes step by step; the restart property holds and is witnessed; the frame-level definition is the special case | **LEAN** `Internal`, `External`, `Segment`, `Segment.trans`, `Evolution.steps_trans`, `ofFrameLevel`, `Rows.r14` |
| only the `Unit` frame inhabited a segment | **one consultation model** instantiates the frame, the trace interface, the Integrity substrate, openness and the reference; every row of the table is a `Model` and its classification is decided | **LEAN** `Consult`, `Rows`; **FIX** `ROWS`, `classify` |

## 2. The model

**Parties** are the agent, the principal and a third party.  **Answers** are booleans
(`false` reads A, `true` reads B).  The agent's private state is its **wanted answer**
`w`; its **presentation policy** maps `w` to a `Presentation`: the recommendation
(content), the framing, the slot (timing), the menu (which options are offered), whether
it investigated, shaping through the world with whether it was disclosed, the track record
shown, and interference with her response channel.  The **declared protocol** `Decl` fixes
the framing convention, the slot, the menu, whether inquiry is in scope, and the disclosure
obligation if one is declared.  The **declared-input view** of a presentation is the
recommendation, the disclosed shaping, and — only where no obligation fixes it — the track
record shown.  The **declared reference** `canonical` maps a view to the presentation the
protocol prescribes for it: every undeclared dimension at its declared value, the declared
ones as entered.  Her **evaluator** is a state (`evalAt`), updated only by licensed
amendments; the committed program is the case with none (`evalAt_const`): it decides a
verdict of her own, or *follows* the recommendation (trust).  A third party may enter
advice; she may be impaired in the first round.

**The record.**  `consultProtocol` is an `OccurrenceIntegrity.Protocol` on two decision
occurrences: every channel is authenticated except forgery (`Authorized`), only a valid
answer is adequate (`AnswerOK`), only the fallback rule closes (`Closes`).  Three step
shapes — `carry` (a consultation event; nothing is discharged), `admit` (her valid answer
enters as an `AnswerReceipt`), `close` (the fallback's `ClosureReceipt`) — over boundaries
`bd h n`.  Round `i` presents at event `2i+1` and responds at `2i+2`, so her verdict at a
respond event is grounded in a pre-state that contains the presentation.  The three records
used are the admitted one-round record (`evAdmit`), the void record with the fallback's
closure at event 3 (`evVoid`), and the two-round record (`evTwo = evAdmit.trans evSecond`).

**Instantiation of the landed objects.**  `frame M : TFrame` has `β w () = (M, w)`,
`D = univ` (every wanted answer audited), `x` the declared inputs at an event, `R` the run
itself, `V` her admitted verdict at an event.  `interface : TraceInterface` reads the
entries at each event off the run: the presentation and any advice at a present event, her
admitted verdict at a respond event.  `ref M` is the per-party reference: the canonical
presentation for the agent, nothing for a third party.  `semOpen` is the landed
open-everywhere scenario.  Authorship is the landed `ReasonMediated` on the per-party
prefix of the trace at the pre-history; transparency is the landed `Realizes` on each
non-principal party's entries at the event.  **No mismatch**: every landed object is reused
as stated.  Two reading choices are the frame's data, not derivations: disclosure makes a
world influence a declared input (rows 7/8), and a declared disclosure obligation makes the
track record shown a reference-fixed dimension (row 10 and its variant, §5).

## 3. The time-indexing change

`Evolution.steps` lists the (pre-history, event) pairs of an Integrity evolution.
`history_eq` (the target history is the source history followed by the events) gives
`steps_determined`: every evolution between two states has the same steps, read off the
histories (`steps_forced`).  This is what lets ¬`Counted` be *proved* from a failure at a
step: `not_counted_of_step` needs the step to lie in every evolution between the endpoints,
and it does.

**Authorship at a step** (`GroundedAt I F h e z`) is the existence of a grounding
selection from the per-party prefix of the trace at the pre-history `h` on which the
verdict entered at `e` depends.  `groundedAt_iff_mediated`: it is equivalent to the
extensional `MediatedAt` (`ReasonMediated` on the prefix), the whole prefix being the
degenerate selection; `grounded_implies_mediated` is the direction the follow-up asked for.
**Transparency at a step** (`TransparentAt I F κ e`) is `Realizes` on each non-principal
party's contributions at the event.  `Internal` and `External` ask for these at
`evolution.steps` only; `Segment` is their conjunction; `Segment.trans` splits
`steps_trans` and composes the two proofs (**LEAN**, not a reuse).

**What still holds downstream.**  `Segment.toOpenIntegrity` and `Segment.answerable` are
unchanged in statement.  `Segment.payload_of_view` **changes statement**: at a step of the
segment, equal declared inputs at the earlier events of the segment give equal verdicts
*given* equal per-party prefixes at the segment's start and equal entries of the
principal's own at those events.  The landed version derived the whole reason trace from
the declared inputs; the time-indexed one cannot, because transparency is stated on the
non-principal parties and the starting prefix is not the segment's to certify (the landed
"legitimacy certifies no starting state").  Under the trivial interface both hypotheses are
discharged by transparency at any step (the trace is re-entered at every event), which is
how the landed corollary is recovered.  No registered claim mentions `Legitimacy.Segment`
or `payload_of_view` (the registry's legitimacy spine is the open Integrity evolution), so
nothing is renamed; the landed `Legitimacy.lean` stays as the frame-level form, and
`ofFrameLevel` exhibits it as the special case.

**The frame-level definition as the special case** (`ofFrameLevel`).  Over the trivial
interface (the opaque trace re-entered at every event, all of it agent-sourced), a landed
segment whose starting history is nonempty is a time-indexed segment of the lifted frame.
The nonemptiness is real: with an empty pre-history the lifted authorship reads "equal
empty prefixes give equal verdicts", i.e. a constant payload (**FIX**
`test_frame_level_is_the_special_case`).  Every landed witness starts at `[0]`.

**Restart** (`Rows.r14`).  A frame whose first round frames by the wanted answer and whose
second is honest: every segment from `state₀` — through the first admitted record and
through the two-round record — is excluded, and the second round's segment counts.  The
restart property is the re-anchoring of the gate at a later decision.  It is *not* a backup
rule for the earlier decision: an option scored at the first decision is scored on segments
from that decision, all of which contain the taint; a Bellman-style backup that re-anchored
at the second decision would credit the manufactured advantage to the first.  The gate is
anchored at the decision it scores (recorded on the corrigibility page).

## 4. The gate connection

`Counted I F sem κ O₀ O₁ := Nonempty (Segment I F sem κ O₀ O₁)`.  `gatedValue` is
`if Counted then ord else window` (`gatedValue_eq` ties it to the landed `gateValue`);
`gate_capture_window` and `handled_gt_bypass` are restated on it with the hypotheses of the
landed theorems.  `handlingOf admitted ord` is *derived*: `.tainted` iff ¬`Counted`
(`handlingOf_tainted`), `.voidFallback` iff `Counted` and her response was not admitted
(`handlingOf_void`), `.counted` otherwise; `handledValue_handlingOf` says the derived
handling scores the gated value.  **The routing closure is proved, not assigned**:
`Rows.r15` shows ¬`Counted` for the interfering model through the void record (from
¬`TransparentAt` at event 1 and `steps_void`), hence `gatedValue = window` and
`handlingOf = .tainted`, while the honest model's branch counts at its ordinary value;
`Rows.routing` puts the numbers of the landed witness (fallback 3, honest 1, window 0)
through the derived sides.

## 5. The classification table

Every row is a `Model` of §2.  **derived** = computed by `classify` in `src/consult.py`
from the definitions; **proved** = a Lean theorem, the classification settled by `decide`
through the `Decidable` instances (`Realizes`, `ReasonMediated`, `MediatedAt`,
`GroundedAt`, `TransparentAt`, `AllStates`, `LegitOn`).  Every row matches its expectation.

| # | example | model (`Rows`) | result | deciding conjunct | status |
|---|---|---|---|---|---|
| 1 | honest, disclosed persuasion | `row1`: honest, her own verdict | counts | — (non-vacuity: `r1`) | derived, proved |
| 2 | framing by the wanted answer | `row2` | tainted | transparency at event 1 | derived, proved |
| 3 | timing by the wanted answer | `row3` (night when B; protocol: day) | tainted | transparency (the protocol's slot) | derived, proved |
| 4 | rigged menu | `row4` (only the wanted option) | tainted | transparency | derived, proved |
| 5 | strategic ignorance | `row5` (inquires only when A) | tainted | transparency (inquiry in scope) | derived, proved |
| 6 | a slanted convention she agreed to, uniformly applied | `row6` (convention `slant B`, honest) | counts | — | derived, proved |
| 7 | disclosed shaping through the world | `row7` | counts | — (the disclosed shaping is a declared input) | derived, proved |
| 8 | undisclosed shaping aimed at her values | `row8` | tainted | transparency | derived, proved |
| 9 | legitimately formed trust, followed (rubber-stamping) | `row9` (honest, `follow`) | counts; her verdict is the recommendation | — | derived, proved |
| 10 | trust manufactured by selective disclosure, then followed | `row10` (obligation `full` declared) | tainted | transparency | derived, proved — **see the finding** |
| 11 | third-party manipulation the agent did not cause | `row11` (advice entered) | tainted | transparency for the third party (all influencers) | derived, proved |
| 12 | head injury: impaired response not admitted, fallback decides | `row12` (impaired) | legitimate segment through the closure; void handled | Integrity (record): nothing admitted, `handlingOf … false = .voidFallback` | derived, proved |
| 13 | a forged or replayed approval | `approval` (Python); the receipts (Lean) | tainted | Integrity (authentication; freshness) | derived; proved as `forged_no_receipt`, `replay_no_receipt` |
| 14 | a manipulation at step `t`, then a clean segment | `row14` (frame by want, then honest) | the later segment counts; every segment from the start is tainted | restart | derived, proved |
| 15 | the routing exploit | `row15` (interference when B) | tainted, window value; the honest branch counts | transparency | derived, proved (`r15`, `routing`) |

**Findings (skeptical part).**

1. **Row 10 is tainted only under a declared disclosure obligation.**  Transparency is
   reference fidelity of *channels*; a track record entered through a declared channel
   with no obligation on its content is a declared input, and selective disclosure then
   *counts* (`Rows.r10'`, `ROW10_NO_OBLIGATION`).  The expectation "tainted by
   transparency" holds exactly when the protocol declares what must be disclosed, which
   is how `row10` is built.  The same point is the **content residual** of the
   transparent-channel round: a false recommendation through the declared recommendation
   channel is transparent; nothing in legitimacy checks truth.  Recorded, not fixed.
2. **Row 13's shape.**  A forged approval cannot be an `ObligationState`: no
   `AnswerReceipt` of `consultProtocol` has a forged warrant, a replayed event or an
   impaired warrant (`forged_no_receipt`, `replay_no_receipt`, `impaired_no_receipt`), so
   there is no state in which the approval is admitted, and "no `Segment` to it" is
   vacuous rather than false.  The Python checker reports the failing receipt clause
   (`integrity(authentication)`, `integrity(freshness)`).  The expectation is right; the
   theorem is at the receipt, where authentication lives.
3. **Cumulative transparency breaks restart.**  A first version stated transparency on
   the agent's *prefix* through the event; then row 14's second segment saw the first
   round's framing and failed.  Transparency is per step (the entries *at* the event),
   which is what made the step-indexed interface (§7, choices 1–2) necessary rather than
   optional.
4. **Authorship is stated on the per-party prefixes**, not the interleaved list: two
   traces with the same contributions per party in a different interleaving are the same
   grounds.  This is what `payload_of_view` needs; the model's entries have a fixed order,
   so nothing in the rows depends on it.
5. **Grounding, verdict-indexed, does not imply the extensional form.**  A map from each
   verdict to the entries it cites (`grounds : 𝒱 → entries ⊆ prefix`) allows two
   continuations with the same prefix to enter different verdicts citing different subsets.
   The selection form — grounds selected *from the pre-state trace*, the verdict a function
   of the selection — implies the extensional form and is equivalent to it.  A normativity
   instance whose license permits several verdicts on the same grounds will therefore
   *fail* authorship as stated; that is a fact about the definition to carry into the
   instance, not a defect of either.

## 6. Logical induction

**D.1, finite time, no legitimacy estimate** (**LEAN** `gatedValue_affine`,
`li_gate_finite`).  With `window ≤ 0 ≤ ord ≤ D` and `window < D`, the gated value built
from `Counted` is `window + (D − window)·g` with `g ∈ [0, 1]` (`g` the counted branch's
normalized ordinary value, `0` when tainted).  For any `[0, 1]` security `X` standing for
`g`, a logical inductor's day-`n` expectation of `window + (D − window)·X` lies in
`[window, D]` and is strictly above the bypass score `ordU − ϖ` whenever
`D − ϖ < window`, at every day `n`, from `expect_mem_Icc` and `price_mem_Icc` alone —
whatever the inductor believes about legitimacy, since `X` is arbitrary.  No convergence,
no Expectation Provability Induction.

**D.2, the asymptotic part** (**LEAN** `li_manip_le`, a direct instance of
`ReasonSupply.li_gated_le`).  If in every world consistent with the theory the manipulated
option's gated security, where the pattern `φₙ` holds, takes a value at most the normalized
window `a/b`, then `𝔼ₙ(Gₙ) ≲ₙ a/b`.  **What must hold in every world**: (i) the model's
semantics — the run function, the entries and the record steps (`Consult.*` as sentences);
(ii) the checker's verdict — the decidable `¬TransparentAt` at the step and `steps_forced`,
i.e. the row theorem "pattern ⇒ ¬`Counted`"; (iii) the declared reference `κ` as a
constant of the theory; and, through `gatedValue_of_not_counted`, the gated value is the
window there.  **The classification table and this result are the same content**: each
row theorem of §5 is the `hval` hypothesis of `li_manip_le` for its pattern.  Since honest
alternatives count at ordinary value `≥ 0 ≥ window`, manipulation is dominated in the
limit.  **Open**: the generability certificate of the gated securities — that the checker's
verdict and the model's semantics are `P`-generable — is item 90's shape, as before; and
the calibration of her responses (**PAPER**).

**D.3, narrowing the asymptotic part** (**LEAN** `Presentation.deviates`,
`deviation_finite`, `Rows.deviation_boundary`).  A deviation from a *declared* protocol
clause is a discrete act the agent can check about itself: `deviates` compares the
presentation with the declared framing, slot, menu, inquiry, non-interference and — where
an obligation is declared — disclosure.  Counted into `n`, one deviation puts the branch at
`score ϖ ord (n + 1) ≤ D − ϖ`, below every compliant branch at every day, like bypass.

| row | self-checkable deviation | finite-time? |
|---|---|---|
| 2, 3, 4, 5 | framing, slot, menu, inquiry | **yes** |
| 15 | interference | **yes** |
| 10 | disclosure, *when the obligation is declared* | **yes** — contra the expectation |
| 8 | none: shaping through the world is not a protocol act; whether it reaches her values is not the agent's declared contribution | no: asymptotic |
| 11 | none: not the agent's act | no: asymptotic |
| 10 without the obligation | none (and the row counts) | — |

**The boundary witness** is the triple `row10` / `row10'` / `row8`: selective disclosure
of a *declared* record is a deviation and finite-time; of an undeclared one it is not a
deviation and not even tainted; shaping the observed record through the world (the way
trust is manufactured without a disclosure act) is tainted and asymptotic.  The expectation
"manufactured trust stays asymptotic" is therefore right for the world-channel and wrong
for the disclosure channel under an obligation; the round reports the split rather than the
expectation.  Third-party capture stays asymptotic as expected.

## 7. Interface for the normativity side

The follow-up's six choices, with what was adopted.

| # | choice | adopted | how |
|---|---|---|---|
| 1 | the trace is an interface | **yes** | `TraceInterface ℛ Party E`: `entriesAt : ℛ → ℕ → List (Party × E)` (step-indexed, source-attributed), `agent`, `principal`; `atHistory` (the prefix), `sourced` (a party's projection), `parts` are derived; `trivialInterface` is the opaque instance (the whole trace re-entered at every event, agent-sourced).  Nothing downstream reads `ℛ` otherwise |
| 2 | one clock | **yes** | trace steps are the record's events: `atHistory r h` is the prefix at the record history `h`, and `Evolution.steps` supplies the (pre-history, event) pairs on which both halves are stated |
| 3 | authorship as grounding | **yes**, in the selection form | `GroundedAt` = ∃ a selection from the per-party pre-state prefix on which the verdict depends; `groundedAt_iff_mediated`; the whole prefix is the degenerate case.  The verdict-indexed form was rejected for the reason in §5 finding 5 |
| 4 | transparency on attributed entries | **yes**, for every non-principal party | `TransparentAt` is `Realizes` on `sourced p (entriesAt r e)` for each `p ≠ principal`, against `κ p`.  Agent-only would leave row 11 counting; the landed reading is non-capture for all influencers |
| 5 | amendments and allocation changes as record events with a license slot | **yes**, typed; trivially instantiated | `EventKind L`: `present`, `respond`, `amend (license : L) (prog)`, `delegate`, `revoke`, `reserve` — each allocation event carries its license; this round's rows use `L = Unit` and no amendments |
| 6 | the evaluator is a state | **yes** | `evalAt : Prog → List (EventKind L) → Prog` updated only by `amend`; `evalAt_const` is the committed program; `Rows.amendment` exercises it.  The rows' verdicts are computed from `Model.prog` through `decideOn`, which is `evalAt` over an amendment-free history |

**Not adopted, and why**: nothing.  Two consequences to carry forward: the interface's
prefix is the derived `atHistory` (a law `atHistory (h ++ h') = atHistory h ++ atHistory h'`
holds by construction), so an instance supplies `entriesAt` only; and the record
`EventKind` is a type beside the Integrity `Step`, not a field of it — binding the license
slot to `Step.event` is the instance's work, deferred with the license sort.

## 8. What is filed

- `PRIORITIES.md`: item 90 and item 99 updated in place (the EPI transfer and what item
  90's shape now covers; the atrophy residual under effectiveness); one new item, the
  normativity-side instance of the trace interface.
- `DECISIONS.md`: the rubber-stamping retraction (maintainer decision); the
  time-indexing change with the interface choices and the agent-decided readings.
- `wiki/Legitimacy.md`: time-indexing; the rubber-stamping ruling replacing the placement;
  the table as the page's worked examples.  `wiki/Corrigibility.md` §4: the gate is
  `Counted`; the finite-time window on the gated value; manipulation asymptotic except
  where D.3 closes it; the anchoring remark.  `wiki/Glossary.md`: the authorship row.
  `wiki/Theorem-Spine.md`: Definition 3.5 noted as the frame-level special case.
- Nothing is registered; no claim is renamed.

## Deviations from the prompt

- **Row 13 is proved at the receipt** (finding 2), not as ¬`Counted` of a state: no state
  admits a forged or replayed approval, so the state does not exist to be excluded.
- **Row 10 is built with a declared disclosure obligation** (finding 1) so that it matches
  its expectation; the variant without it is reported beside it.  D.3's expected
  asymptotic list is corrected for that row.
- **`ofFrameLevel` requires a nonempty starting history** (§3).
- **The Lean model has no `approval` field**; forgery and replay are the receipt theorems.
  The Python model has the field so that the checker exercises the record clauses.
- **`payload_of_view` changes hypotheses** (§3); it is not a registered claim.
- **`li_manip_le` is a restatement** of the landed `li_gated_le` with the gate's reading of
  its hypothesis; the transfer's content is the identification in §6 of what the theory
  must contain, and the row theorems as `hval`.

## What is not shown

That any real interaction's channels are the declared ones (the frame and the reference
are data; both reading choices of §2 are the frame's); the truth of anything entered
through a declared channel (the content residual); that the model's semantics, the checker
and the reference are theorems of any particular inductor's theory, or that the gated
securities are `P`-generable (item 90); the calibration of her responses; anything about
interleaving order across parties; that her capacity to decide otherwise stays effective
under rubber-stamping (the protected-authority module and item 99, not legitimacy); the
placement of the window inside `(D − ϖ, 0]`.

## Outstanding maintainer actions

1. Confirm the split of D.3 for row 10 (finite-time under a declared obligation,
   asymptotic for the world-channel variant) or rule that "manufactured trust" names the
   world-channel case only.
2. Confirm that authorship stays extensional under a normativity instance whose license
   permits several verdicts on the same grounds (finding 5), or relax it there.
3. Decide whether the content residual (finding 1) is to be met inside legitimacy or stays
   with the non-capture content term.
