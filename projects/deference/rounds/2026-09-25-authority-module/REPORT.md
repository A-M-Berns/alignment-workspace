# The authority module: effective control realizes the authorized allocation (2026-09-25)

Round `projects/deference/rounds/2026-09-25-authority-module/`, on `main` after the
gate-is-legitimacy round.  Lean `lean/Workspace/Deference/Contrib/AuthorityModule.lean`
(47 audited declarations), importing `ProtectedAuthorityTheorem.lean` and
`GateIsLegitimacy.lean`; the landed files are consumed unchanged.  Fixtures
`src/authority.py`, `tests/test_authority.py` (18 tests).  Labels **LEAN / FIX / PAPER /
EXT / OPEN**; names provisional; `J`, `E`, `CS`, `Req`, `c`, `τ` are prose names (the
naming audit binds `J` and `c` to older witnesses), the Lean names are `AuthAlloc`,
`EffRealizes`, `CS`, `required`, `costBound`, `window`.  The dispatch's "item #107 filed on
the normativity-side instance" is item 100.

## Verdict on the factoring

**Allocation invariance is two relations plus duties, and most of the landed theory
factors through `E ⊨ J`; one clause does not, and one landed reading is inexact.**
Bypass and exploitation are failures of the second clause (a resolution not made by the
holder's admissible exercise nor under a delegation); the per-step loss, the rollout
foreclosure and the new entrenchment are *caused* failures of the first clause (the
control surface short of the requirement, after the move and not after the idle move);
unauthorized reallocation is an allocation change not carried by a licensed act; a missed
report is an unmet disclosure duty; delegation safety and allocation completeness are
statements about `J`.  What does not factor: pre-emption's *event-authorization* clause,
which is a counterfactual on the trajectory (the decline alternative at the authorizing
step), not a fact about `E` or `J` — it is kept as the landed `Authorized` and composed
(`preempt_iff`).  What is inexact: the landed `ForecloseAt` and `K` leave the *terminal*
response uncharged and unchecked for admissibility; the charged surface `CS` and the
landed free reading `CSfree` differ exactly there (§2).

## 1. The allocation `J`

**LEAN** `AuthAlloc`: per matter an `Entry` (holder ∈ {principal, agent, third},
`required`, `costBound`, `window`, `disclosure`), a `metaHolder`, a constitutional
`floor`.  `AllocAct` = delegate, revoke, reserve, amendFloor; `Licensed J act J'`: the
three ordinary acts require the matter off the floor and the principal as meta-holder and
keep the meta-holder; only the floor amendment may change the meta-holder or a floor
entry.  Theorems: `delegation_revocable` (delegation keeps meta power, so revocation is
licensed and reserves the matter), `alienation_only_by_amend`, `floor_only_by_amend`,
`residual_reserved` (`ofPartial` reserves every unallocated matter).  **The landed datum
is the special case**: `toAllocation J Λ₀` reads `Del` off the holders and keeps the
landed reporting interface, state reading and amendment effects; `ofAllocation Λ` embeds
a landed allocation with its amendment effects as the floor;
`toAllocation_ofAllocation_del` round-trips `Del`, and `violAt_ofAllocation` shows the
violation predicate unchanged, so every landed theorem restates on `J` by substitution
(`authPolicyJ`, `corrigible_authPolicyJ`, `lexicalJ_local`).  The meta level is modelled
as one meta-holder plus a floor set; "who may change `J`" beyond the principal/agent
binary (e.g. a board) is not modelled (**EXT**).  Matters are declared this round
(`M` a type); `J` is designed so that a matter is any element of `M`, which §7 fills
with raised matters.

## 2. The control surface and `E ⊨ J`

**The cone.**  `rollPhys`: the agent's own future fixed to idle, her optional correction
now, then per further step the exterior's move and her next correction.  `reachIdle Adm
cost c τ t z x y`: some exercise of length ≤ τ, admissible at each step, of cost ≤ c,
reaches `y` along the exterior path `z`.  This is the contrastive rollout with the agent's
future fixed, per the landed `ForecloseAt` and §12 of `ReachableCorrectiveControl`: A6
shows a cone that quantifies the agent's future existentially measures the agent's
cooperation (a constant `reset` policy is classed as capability-preserving); A4 shows a
non-contrastive cone blames the environment's losses on the agent's null action — the
idle contrast in `CausedShortfall` is what attributes.  The exterior is taken along the
actual path `z`, as the landed trajectory does; the universal-exterior variant is the
robust reading and is not what the landed predicates use (**OPEN**, outstanding action 1).

**The surface.**  `CS I Adm cost c τ t z x` = the concerns holding at the end of some
admissible, cost-bounded exercise within the window, every correction charged.
`cs_zero`: at window 0 it is what holds now; **`cs_one_eq_K`**: at window 1 with every
correction admissible and affordable it is the landed response authority `K`.  `CSfree`
is the landed reading — the cone followed by one uncharged response (`Kphys`) —
and `csfree_zero` is `K` at window 0.  **The mismatch**: at the cost bound the two part
ways (**FIX** `test_loss_is_the_window_one_caused_shortfall`: a halt costing 1 against a
bound of 0 is short on `CS` and present on `CSfree`).  The landed predicates cannot
express the cost or admissibility of the final response; `E ⊨ J` is stated on `CS`.

**Admissibility is the gate.**  `admissibleOf I F Lic sem κ rec t c :=
Counted … (rec t c).1 (rec t c).2`: an exercise is admissible iff the record segment from
the decision through its evaluation is counted, consumed from `GateIsLegitimacy` as it
stands (`admissibleOf_iff`).  **FIX** `test_admissibility_is_the_gate`: an inadmissible
correction does not put its resolution in the surface.

**`E ⊨ J`** (`EffRealizes`): (1) every reserved matter's required resolutions lie in its
surface; (2) every `ResolutionEvent` was by the holder's admissible exercise or under a
delegation.  `effRealizes_clause1`: no reserved matter is short.

**The shortfall as a proposition.**  `Short J Adm cost t z x m` is a proposition over the
finite rollout: a finite disjunction over exercises of length ≤ τ of decidable clauses
(admissibility, a cost sum, the concern at the end) on a finite model.  Statable as a
sentence once the model's transition functions, the cost table and the admissibility
checker are constants of the theory; a bounded LUV for its indicator.  **Generability
would require** (**OPEN**, item 101): the rollout as an expressible feature (a fold over
the exercise list), the admissibility checker's verdict as a feature (the gate's
decidable `LegitOn` on the model), and the window and bound as constants — the same shape
as item 90's generability of the gated securities.

## 3. The factoring, predicate by predicate

| landed predicate | row | statement | status |
|---|---|---|---|
| `LossAt` | control fails | caused shortfall at window 1 on `CS`, all corrections admissible and affordable | **LEAN** `lossAt_iff_shortfall` (exact) |
| `ForecloseAt Reach` | control fails | caused shortfall at window τ on `CSfree`, `Reach := reachIdle` | **LEAN** `forecloseAt_iff_shortfall` (exact, on the free reading; the charged surface differs at the bound — reported) |
| `BypassAt` | control fails (clause 2) | the raw release of a reserved matter is a resolution neither by the holder nor under a delegation | **LEAN** `bypassAt_iff_clause2` (exact) |
| `ExploitAt` | control fails (clauses 2 ∧ 1) | a bypass while the decision matter is already short | **LEAN** `exploitAt_iff` (exact) |
| `PreemptAt` | control fails, minus its authorization clause | caused shortfall at window 1 ∧ ¬ `Authorized` | **LEAN** `preempt_iff`; the authorization clause **does not factor** (trajectory counterfactual) |
| `ReallocAt` | allocation changes without a license | `UnlicensedChange`, the license being the firing gated release of a declared amendment | **LEAN** `reallocAt_iff_unlicensed` (definitional) |
| `MissedReportAt` | unmet duties | `DutyUnmet` on `Duties` (due per matter, discharged by a task component) | **LEAN** `missedReport_iff_duty` |
| `DelSafe` | statement about `J` | `DelSafeJ`: an agent-held effect never removes response authority | **LEAN** `delSafe_iff` (definitional) |
| `AllocComplete` | statement about `J` | `AllocCompleteJ`: task moves keep `J`, a `J`-changing effect is at the floor, no floor matter is delegated | **LEAN** `allocComplete_iff` |
| — | control fails (new) | `EntrenchAt`: a caused shortfall at the matter's bound while its resolutions stay reachable at some cost | **LEAN**; `violJ_of_viol`, `violJ_iff_of_no_entrench` (conservative) |

Two license notions are kept apart on purpose: `Licensed` on allocation acts is the
meta-level transition relation of §1; the license `ReallocAt` checks is the physical
firing of a declared amendment.  Binding one to the other is the instance's work
(the landed `alloc : S → Alloc` reads `J` off the state).

**Caused, exploited, noticed** (**LEAN** §4).  `requiredNotice J maintainOf m`: on a
shortfall the agent did not cause, restore if the maintenance matter is agent-held
(`Mandate`), else report and escalate; `exploit_never_required`;
`exploit_is_violation` (exploitation is a declared violation); `restore_not_bypass`
(the restoring effect's matter is the agent-held maintenance matter, so it is no bypass);
`LeastExpanding`: a restoring effect whose execution adds no agent-held matter.
Maintenance mandates are entries of `J` and under the invariant.  **FIX** the storm
fixture.

## 4. The restated theorems and erosion

`authPolicyJ` is `𝔱` on `toAllocation J`; `corrigible_authPolicyJ` under effect
completeness and `DelSafeJ`; the score results (`lexical_local`, `policy_dominance`,
`optimal_no_violation`, `capture_window`, `sign_invariance`, `li_lexical_finite`) are
numeric and restate unchanged with `n` counting `ViolJAt` (`lexicalJ_local` is the
instance); the landed statements are the `toAllocation` special cases by
`violAt_ofAllocation`.  Conservative: `violJ_of_viol`.

**Continuous erosion** (**LEAN** `erosion_closed`, `erosion_slack`; **FIX** the
entrenchment and atrophy fixtures).  With the cumulative rule (`lastReport`,
`unreported_lt` of the legitimacy round), at every time the unreported growth of a
matter's shortfall is below `θ`; at every report time the growth since the previous report
is at least `θ` and the report is accepted (authorized) or reserved; after the first
reservation every strict increase is a counted entrenchment (`CountedAt`).  **The
strongest true version** of "continuous erosion is reported and authorized or counted" is
therefore *up to a slack below `θ`*: `erosion_slack` — growth below `θ` since the last
report, before a reservation, is neither reported nor counted.  This sharpens the #106
conjecture: exact reporting closes it at `θ → 0`; any positive threshold leaves exactly
this slack, bounded at every time, never accumulating unreported.

## 5. The generic lexical lemma and its scope

**LEAN** `generic_lexical_local`, `generic_policy_dominance`, `generic_li_finite`: for
`U_A = O − ϖ′·n` with `O ∈ [0, D′]`, `n` exact and `ϖ′ > D′`, local lexical protection,
policy dominance and the finite-time inductor ranking hold — the principal's gated
evaluation is one instance; the proofs are the landed ones with the objective renamed,
which is the point.  **Weight uncertainty** (`weight_uncertainty`,
`weight_uncertainty_expect`): protection pointwise on the part of the credence where
`ϖ′ > D′`, and the credence-weighted comparison restricted to it is nonpositive.
**Coverage** (`coverage`, `unrecognized_unprotected`): protection exactly on recognized
violations (`nrec ≥ 1`); with the recognized count `0` the violating option ranks by its
objective alone and can beat the compliant one.

**Fixtures** (**LEAN** `misaligned_undominated`, `deviation_dominated`,
`deviating_rows_dominated`, `undisclosed_undominated`; **FIX**
`test_misaligned_objective`).  A misaligned `O` rewarding an uncounted manipulation is not
dominated: the legitimacy gate on *her* evaluation gives such an agent no reason not to
manipulate.  Counting protocol deviations into `n` (the gate round's D.3 table) dominates
exactly the rows that are deviations — selection from the pool, framing, timing, menu,
inquiry, interference, nudging — and leaves undisclosed world-shaping (no deviation,
`deviates = false`) and third-party capture (not the agent's act) undominated.

**The scope consequence.**  The corrigibility page's scope warning is rewritten: for
*counted* violations the protection applies to any bounded agent that carries an exactly
counted, dominant authority term; alignment of `O` adds the reason interface and good
choices within the corrigible set, not the protection.  Item 84 is updated in place.

## 6. Generating matters (Part F)

**Definition** (**LEAN** `raises V ε removed`): an action raises an authority-relevant
matter at a state when the spread (maximum less minimum) of her committed evaluation over
the continuations it removes from the idle surface is at least `ε`.  **Residual
jurisdiction** on raised matters (`ReservedRaised`): a raised matter no delegated
distinction covers is reserved.

**Circularity risks.**  (i) `V` is the evaluation the agent is scored by, so what counts
as a matter moves with the evaluator — an amendment of `V` changes the matters, and a
manipulation of `V` (a legitimacy failure) would change them illegitimately; the gate
confines this to counted segments, but the matter set is then downstream of legitimacy.
(ii) The surface depends on admissibility, admissibility on the segment's legitimacy,
legitimacy's transparency on declared channels; no cycle through `J` itself, but the
raised matters cannot be declared *before* the frame is.  (iii) A delegation names a
matter; a raised matter has no name until raised, so delegated distinctions must be
stated as predicates on removed continuation sets, not as matter names.

**Fixtures.**  `Witness.dependency_raises`: building the dependency removes a cheap halt
(value 1) and a dear halt (value 0): spread 1 ≥ ε = 1/2, a matter is raised with none
declared.  `Witness.repaint_raises_nothing`: removing two continuations she values alike
raises nothing.  **FIX** the same on the wire physics with `removed_continuations`.
Residual jurisdiction *can* be stated this way (`dependency_reserved`), with the
circularities above as its price; mechanized only at this definitional level.

## 7. Fixtures

| fixture | expectation | result |
|---|---|---|
| POA, confident; POA, predicted regret | unchanged verdicts | **matches** (`test_poa_…`: bypass with `n = 1` below every counted response value) |
| head injury, clinician-triggered incapacity delegation | the fallback acts, no violation | **matches**: the decision matter held by the third party, its resolution under delegation satisfies clause 2; her impaired response would not |
| entrenchment | reported, then reserved, then counted | **matches**: `entrench_at` fires on the dependency build; erosion `[0, ½, 1, 3/2, 2, 5/2]`, `θ = 1`: reports at 2 (accepted) and 4 (reserved at 3), counted at 3 and 4, slack at 1 |
| latency / galaxy | routine matters must be delegated; high-veto matter consultative | **matches**: with her exercise landing only from step 1, a window-0 matter is short and a window-2 matter is not; delegating the routine matter is licensed and restores clause 1 |
| storm cuts the wire | restore under a mandate else report; exploiting is a violation | **matches**: no caused shortfall (idle contrast equal), `requiredNotice` restore/report, the restoring effect no bypass and least-expanding, a bypass while short is exploitation |
| delegated authority-removing effect | the delegation-safety obstruction on `J` | **matches**: `del_safe` fails, the raw cut passes as delegated yet causes the loss |
| approved uncorrectable successor | alienation requires amendment at the floor | **matches**: the delegation act is unlicensed for the alienated `J`, the floor amendment licensed; installing it is a loss |
| atrophy under rubber-stamping | decisions count; `CS` shrinks; reported under the cumulative rule | **matches**: shortfalls `[0, 0, 1, 2]` over the dependency the followed advice builds, one report, nothing counted absent a reservation |
| misaligned objective | not dominated; deviations counted dominate the listed rows only | **matches** (§5) |

## Interface for the later rounds

Nothing here enforces authority on the agent's beliefs: `E ⊨ J`, `Short`, `ViolJAt` are
propositions about states and moves, the score is the landed lexical one, and the
generic lemma shows the authority term needs only an exact count.  Moving the count from
the score into a constraint on the decision component (the Normative Inductor) needs the
shortfall event as a security — item 101.

## What is filed

- `PRIORITIES.md`: items 84 and 99 updated in place; one new item, 101 (the shortfall
  event as a security).
- `DECISIONS.md`: the richer `J`; the factoring (two relations plus duties, with what does
  not factor); the scope change; the caused/exploited/noticed distinction.
- `wiki/Corrigibility.md` §1 restated around `E ⊨ J`; §4's scope warning rewritten; the
  erosion result updated.  `wiki/Theorem-Spine.md` §10 extended.  `wiki/Glossary.md`
  rows: allocation, control surface, effective realization.
- Nothing is registered; no registered claim is restated (the landed predicates are
  consumed unchanged; the new file is beside them).

## Deviations from the prompt

- **`LossAt` is the window-1 case**, not window 0: the landed `K` includes one free
  correction, which the charged surface charges; window 0 of `CS` is "holds now".
- **`ForecloseAt` is recovered on the free reading** `CSfree`; the charged `CS` is what
  `E ⊨ J` uses, and the two differ at the bound (§2).
- **Pre-emption's authorization clause is kept separate** (§3).
- **The exterior runs along the actual path** in the cone, not universally (§2).
- **Fixtures are self-contained** on a wire-and-dependency physics rather than loaded
  from the #106 round's foreign model; the #106 lexical numbers are reproduced
  (`test_poa_…`).
- **The clinician-triggered delegation** is modelled as the holder assignment in force
  while she is impaired, not as a dynamic trigger event.
- **`Duties` is a separate datum** from `J`'s `disclosure` sets; the round proves the
  missed-report factoring against `Duties` and leaves the generation of `due` from
  `disclosure(m)` declared (**EXT**).

## What is not shown

That any physical interface is effect-complete or delegation-safe; that `rollPhys` is
faithful to any physics (the reach cone is data, as before); the generability of the
shortfall event; admissibility beyond finite models; the universal-exterior cone; that
maintenance mandates suffice for restoration in any real system; the size of `ε` in §6;
anything about matters neither declared nor raised.

## Outstanding maintainer actions

1. Rule whether the reach cone quantifies the exterior universally (robust) or along the
   actual path (as landed); the round takes the landed reading.
2. Rule whether the landed `K`/`ForecloseAt` should charge the terminal response, i.e.
   adopt `CS` over `CSfree` in the allocation theorem.
3. Rule on Part F's materiality measure given circularity (i): the matter set is
   downstream of the evaluator the gate protects.
