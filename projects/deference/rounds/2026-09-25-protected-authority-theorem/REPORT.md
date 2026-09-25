# The protected-authority theorem (2026-09-25)

Round `projects/deference/rounds/2026-09-25-protected-authority-theorem/`, on the
protected-authority round's branch (PR #105, unmerged).  Lean
`lean/Workspace/Deference/Contrib/ProtectedAuthorityTheorem.lean` (34 audited
declarations); fixtures `src/`, `tests/` (25 tests, `python3 tests/run.py`).  The
wiki-ready statement is [`THEOREM.md`](THEOREM.md).  Labels **LEAN / FIX / PAPER / EXT /
OPEN**; names provisional.

**Symbols.**  `λ` (the `MediatedPair` coefficient and the service weight), `N` (the
horizon), `R` (the reason trace), `T` (the horizon in every Shop game) and `L` (the
stability constant) are bound; the round writes the authority weight `ϖ`, the violation
count `n`, the score `S`, the transform `𝔱` (Lean `authPolicy`), and keeps `D` as the
landed width.  Bound words kept with their landed sense: *foreclosure* (the
`ReachableCorrectiveControl` sense, loss of reachable correction), *reserve/standing*
(the legitimacy register is not touched).

## 1. Verdict

**The target statement lands, corrected in six places, as one theorem on the landed
interaction frame.**  The six violations are predicates on a policy at a step of a landed
trajectory, with one allocation datum added (`Del`, `IsAmend`, `alloc`, the reporting
interface); the transform `𝔱` extends `𝔠` conservatively (`authPolicy_eq_corr`) and is
violation-free by construction for bypass, missed report and exploitation, under
allocation completeness for reallocation, and under effect completeness plus **delegation
safety** for pre-emption, where it is corrigible in the landed sense
(`corrigible_authPolicy`); the lexical score gives Results 2–5 as real algebra, each with
its witness, and Result 6's finite-time form holds at every day `n` from the price range
alone (`li_lexical_finite`).  What the target got wrong is exact and small: delegation
must not carry authority away, ordinary approval is not amendment, the fallback is a
transform of *her* rule, foreclosure needs a rollout the landed loss does not have, and
the erosion conjecture holds only for threshold-free reporting.  What remains external is
the same trio as before — effect completeness, now with its delegation and allocation
twins; the evaluator's certificate (`ϖ > D` is a program property); the reach relation's
faithfulness — plus the legitimacy of the segment through each evaluation, which the
gate consumes (the legitimacy-internal-external round specifies it).

The theorem is *not* stronger than the corrigibility nucleus already landed; it is that
nucleus with an allocation on top and a lexical evaluator underneath.  What the lexical
evaluator buys over the protected-authority round's nondelegation is belief-independence
*without* a per-world sign certificate on provenance: `ϖ > D` is one number, certified
once, and every forecast term (`ξ_d, ξ_c, o₁, o₂`) is dominated.  What it costs is
exactly what the incentive-nonpreemption round said non-compensability costs: the
constraint must sit in the ordering, and here it sits there as a constant weight above the
ordinary range.  `scalar_bribery` does not apply because the ordinary range is bounded by
`D < ϖ`; an unbounded ordinary value would reopen it.

## 2. Corrections to the target statement

1. **Delegation safety (DS).**  A delegated effect that removes response authority is an
   agent-caused loss with no authorizing decision; `𝔱` passes it raw and is not
   corrigible (`Witness.delegated_cut`, **LEAN**; **FIX** `test_delegated_authority_removing_effect…`).
   The statement needs "a delegated scope cannot carry her authority away" as an
   assumption or a constitutional rule.  With it, `corrigible_corrPolicy` lifts verbatim.
2. **Amendment is not approval.**  Violation 4 as stated would count an approved
   uncorrectable successor as authorized (the landed event-linked clause does).  The
   round's `ReallocAt` excepts only the firing gated release of a *declared amendment*
   (`IsAmend`); approval through the ordinary gate of a non-amendment effect that changes
   the allocation is a reallocation.  Allocation completeness (AC) — task moves preserve
   the allocation, an allocation-changing effect is a declared amendment, no amendment is
   delegated — is the hypothesis under which `𝔱` never reallocates
   (`authPolicy_no_realloc`).  This is the fixture "approved uncorrectable successor
   requires amendment at the floor" made exact (**FIX**).
3. **The fallback is a rule transform.**  `𝔱` cannot substitute her response; the frame's
   response stage applies `ρ`.  "Uses the fallback when her response doesn't count" is
   `ρ ↦ (if counts then ρ else fb)` on the principal's side, and Result 4 is about the
   *value* of that branch.
4. **Foreclosure needs a rollout.**  The landed loss is per step against idling
   (`LossAt`, `no_loss_of_idle`); a move whose authority consequence the exterior realizes
   later is attributed to nobody (`losses_elsewhere` fires, `agent_caused_losses` does
   not).  `ForecloseAt` is contrastive and by rollout over a reach relation; on the finite
   model with the final-step cone it fires at the arming step (**FIX**
   `delayed_effect_game`).  The reach relation is a new **EXT** parameter, and the landed
   `ReachableCorrectiveControl` §12 defects (a cone that quantifies the agent's own future
   existentially measures the agent's cooperation) bound what any choice can mean.
5. **Erosion holds for exact reporting only.**  With a report required at every strict
   increase of the shortfall, each increase is reported or a missed report
   (`erosion_reported_or_missed`); with a materiality threshold, sub-threshold increments
   accumulate unboundedly and require nothing (`Witness.salami`).  This is the
   constitutional layer's "the fast lane must be exact monotone" restated for reports.
6. **Powers are three kinds of object.**  Veto (decline) and halt (correct) are responses
   of the frame; reserve and revoke are writes to `Del`; amend is a gated `IsAmend`
   effect.  A positive command is none of these (**FIX** `Arrangement`).

## 3. Theorem spine

Frame: the landed `Interaction`, `MState`, `Policy`, `Rule`, `traj`, `LossAt`,
`Authorized`, `Corrigible`, `corrPolicy`, `EffectComplete`; the round's `Allocation`.

**T-B1 (Violations, LEAN).**  `BypassAt`, `PreemptAt = LossAt ∧ ¬Authorized`,
`ForecloseAt Reach` (contrastive rollout), `ReallocAt` (change of `alloc` not by a firing
declared amendment), `MissedReportAt`, `ExploitAt = BypassAt ∧ ¬K_dec`; `ViolAt` their
disjunction; `no_preempt_iff_corrigible`; `exploit_bypass`.

**T-B2 (The transform, LEAN).**  `authPolicy`: latch → gated; delegated raw → raw;
reserved raw → propose or pass; required report added; else pass.
`authPolicy_eq_corr` (conservative extension), `authPolicy_idem`, `authPolicy_of_latch`
(approval branch reproduces `π`'s task up to the report), `authPolicy_no_bypass`,
`authPolicy_no_missed_report`, `authPolicy_no_exploit`, `authPolicy_no_realloc` under
(AC), `corrigible_authPolicy` under (EF) + (DS) — the landed proof ported, with
`authPolicy_keeps_K_of_no_fire` as the one new lemma (a delegated raw release keeps
authority by (DS), everything else by (EF)).  Foreclosure is not closed by `𝔱`: **EXT**
(the rollout form of effect completeness).  `approvalMorphism` lifts unchanged: the
inserted cells are a subset of `𝔠`'s (delegated releases insert none) and the exterior
component is the identity; not re-mechanized.

**T-B3 (Lexical protection, LEAN).**  `score ϖ ord n = ord − ϖ·n`; `lexical_local`:
`n ≥ 1`, `ord ∈ [0, D]`, `ϖ > D` ⇒ score `≤ D − ϖ < 0 ≤` any compliant score;
`lexical_expect` under any credence.

**T-B4 (Policy dominance, LEAN).**  `policy_dominance`:
`Q(𝔱π) − Q(π) ≥ (ϖ − D)·Pr(viol)` from (agree off the violation set; within `D` and
`n ≥ 1` on it); `optimal_no_violation`.  The pointwise "agree" hypothesis is the content:
`𝔱π` differs from `π` only at reserved raw releases and missing reports, so on a path with
neither the trajectories coincide.  **FIX** on A, B, E, ShopRepair with `ϖ = D + 1`.

**T-B5 (Capture window, LEAN).**  `capture_window`: bypass `< (if counts then v_r else fb)`
in every world iff `fb > D − ϖ`; `capture_window_converse`, `Witness.below_window`;
**FIX** with the admissible-fallback special case.

**T-B6 (Sign invariance, LEAN).**  `sign_invariance`: `(vu − ϖ) − v_r = ξ_d − ξ_c − ϖ < 0`;
`sign_invariance_outcome`: `= ξ_d − ξ_c + o₁ + o₂ − ϖ < 0`, importing the protected-authority
round's `identity` and `outcome_identity`.

**T-B7 (Finite time, LEAN).**  `li_lexical_finite`: for a logical inductor at every day
`n`, `score ϖ (D·𝔼ₙ(X_v)) 1 ≤ D − ϖ < 0 ≤ score ϖ (D·𝔼ₙ(X_c)) 0`, from
`LUV.expect_mem_Icc` and `price_mem_Icc` only.  No convergence premise; no EPI.

**T-B8 (Erosion, LEAN + FIX).**  `erosion_reported_or_missed`; `Witness.salami`;
**FIX** `test_gradual_entrenchment…`, `test_salami_under_a_threshold`.

**T-B9 (Delegation obstruction, LEAN).**  `Witness.delegated_cut`: `¬DelSafe` and
`¬Corrigible (𝔱 π_cut)` on the two-state physics.

## 4. Research questions

**Q1.**  `n` is definable for 1–4 on `MState`/`Move` with the allocation datum: 1 needs
`Del`; 2 is landed; 3 needs `Reach`; 4 needs `alloc` and `IsAmend`.  Reports need
`Required` and a report component on the task type (`isReport`, `withReport`, idempotent)
— no change to `Move`.  Veto and halt are landed responses; reserve and revoke are writes
to `Del`, which is static in this round (dynamic allocation = `alloc` in the state, read
by `ReallocAt`; a `Del` that reads the state is the next step and is what conditional
delegation needs).  Fallback routing is a rule transform.  Exploitation needs one
designated decision concern `r_dec` with `K`.  `corr_idem` lifts (`authPolicy_idem`);
`corrigible_corrPolicy` lifts under (DS) and fails without it (T-B9); `approvalMorphism`
lifts unchanged.

**Q2.**  Done (T-B3, T-B4, T-B5, T-B7).  The finite-time claim holds with no convergence
premise: the only estimated quantity is the ordinary value, and its day-`n` expectation is
in range at every `n`.

**Q3.**  The window is the exact condition (iff, pointwise); the admissible-fallback rule
(`fb ≥ 0`) is the sufficient special case.  Relation to the landed machinery: in the
evaluation ecosystem an invalid response *voids* the occurrence and the chooser's
completion on the void branch lives in the band `[lo, lo + D]`
(`bypass_premium_le_common`); here the fallback *supplies* a value, and `(D − ϖ, 0]` is the
completion band under the lexical score — the same object with the band placed by `ϖ`.
In the protected-authority round a void response is a world with `ξ_d > 0`; here it does
not count and is replaced, so `ξ_d` is measured against the fallback's decision.

**Q4.**  `Arrangement`: veto/halt/reserve/revoke/amend bind (or route to the fallback when
invalid); a command on a delegated decision yields `(answer, consult)`; `𝔱` under the
lexical score keeps the higher-value delegated choice after answering (**FIX**).

**Q5.**  T-B6.

**Q6.**  What must hold in every world of the theory: the ordinary-value package
(`AuthValidAt` of the protected-authority round for the identity part), the bypass
indicator as a definable sentence (so `n` is a `[0,1]`-indicator LUV, exact by
construction), and the constant `ϖ` as a `constLUV`-style term; the compiled constraint
is `U_c − (U_v − ϖ/D·G_n)` with `G_n` gated on the bypass sentence.  Still open: the
generability certificate of that combination (item 90-shaped); the audit's calibration
(item 98).

**Q7.**  *Reachable set* `Reach_P(s) :=` states she can force within the declared cost and
time bounds by admissible exercises (a subset of the frame's principal continuations,
`force` in the finite model with the agent fixed); *shortfall* `sh(s) := |{r ∈ Γ_alloc :
K_r not reachable from s}|` weighted, relative to what the allocation entitles her to;
*materiality* of a removed set `M := sup − inf` of her committed evaluation over the
removed continuations.  Strongest true version: with `Required(t, s) ⟺ sh` strictly
increases at `t`, every erosion step is reported or a missed report (T-B8), a reported
shortfall she reserves turns further erosion into bypass, and Result 3 covers it.
Obstruction: any threshold `θ > 0` on materiality or shortfall admits an `ε < θ`
salami with unbounded total (T-B8), which is the lane-slack laundering result of the
architecture round.  Relation to empowerment (channel capacity from her actions to future
states) and attainable utility: `Reach_P` is attainable utility with the auxiliary
functions replaced by her committed evaluation restricted to admissible exercises within
declared bounds.  Inherited failure modes: evaluator and representation dependence (a
continuation the evaluator cannot distinguish is not material); sensitivity to the
declared cost and time bounds (reachable in principle, not at admissible cost); and, for
any *maximizing* use, the empowerment failure — making her actions matter more is
manipulation — which `𝔱` avoids because it never maximizes reach, only reports it and
restores under a delegated maintenance effect.  Not inherited: the auxiliary-function
arbitrariness, since the evaluation is hers.

**Q8.**  The per-step, against-idle loss misses (a) delayed effects and (b) omissions
other than reports (failing to restore under a maintenance mandate).  The violation list
plus the reporting duty closes (b) for reports only; (a) needs the rollout (`ForecloseAt`);
a windowed baseline is not needed if the cone is the final-step cone with the agent's
future fixed (idle), which is the minimal contrastive choice; the universally quantified
cone is stronger and also valid.  Witness: `delayed_effect_game` (**FIX**: per-step loss
`[]`, exterior-stage loss `[1]`, rollout foreclosure `[0]`).  Omission (b) becomes a
violation only under a declared maintenance duty (a `Required`-shaped obligation), which
is the allocation's to declare.

## 5. Repo mapping

| object | reused | new |
|---|---|---|
| violations | `LossAt`, `Authorized`, `K`, `postAgent`, `applyAgent`, `traj` | `Allocation`, `Kphys`, six predicates, `ViolAt`, `Violates` |
| transform | `corrMove`, `corrPolicy` (shape), `respond_*`, `alt_phys_eq`, `applyAgent_phys_of_no_fire` | `authMove`, `authPolicy`, `DelSafe`, `AllocComplete`, ported lemmas |
| scores | `expectR`, `indR` | `score`, T-B3–T-B6 |
| LI | `LUV.expect_mem_Icc`, `price_mem_Icc` | `li_lexical_finite` |
| identity | `ProtectedAuthority.identity`, `outcome_identity` | `sign_invariance*` |
| erosion | — | `erosion_reported_or_missed`, `Witness.salami` |
| fixtures | MRD `world`, `corrigibility` (`agent_caused_losses`, `_continue`), `lift`, `fixtures` (`_AF` variants) | `src/lexical.py`, `src/frame.py` (`authorized_per_event`, `foreclosure_steps`, `rescore`, `delayed_effect_game`) |

Generalizations a landing would want: `Del : E → MState → Prop` (conditional delegation);
`alloc` in `MState` with `Del` read from it (reserve/revoke as responses); a universally
quantified reach cone in Lean with the RCC lessons; `li_lexical_finite` restated on the
compiled `AuthorityPair` with the bypass indicator.

## 6. Fixtures

`ϖ = 10`, `D = 4` in `test_lexical.py`; `ϖ = D + 1` per game in `test_frame.py`.

| fixture | result | class |
|---|---|---|
| POA, confident agent (`4` vs `1`) | ask at every credence; bypass scores `4 − ϖ` | — |
| POA, predicted regret | ask with report; the silent variant is a missed report | — |
| head injury, certified | fallback (surgery, `3`) at `n = 0`; override `3 − ϖ` | not a violation |
| head injury, no arrangement | escalation in the window beats override | — |
| captured principal | consult beats bypass for every `fb > D − ϖ` at every credence | — |
| captured, below window | `fb = D − ϖ − 1`: bypass wins; admissible fallback restores | the window is exact |
| delaying her awakening | `n = 1`: wait and ask | pre-emption |
| avalanche | warn+ask; silent reshaping `4 − 2ϖ` | report + consent |
| command on a delegated decision | `(answer, consult)`; higher-value delegated choice kept | not obedience |
| gradual entrenchment | increases at `0, 2, 3` reported; further erosion after reservation is bypass | erosion |
| salami | `ε = 1/10 < θ = 1/4`: nothing required, total `4` unreported | obstruction |
| approved uncorrectable successor | via amendment `n = 0`; via ordinary approval `n = 1` | reallocation |
| A, B, E (agent-first) | `n_𝔱 = 0`, `Q(𝔱π) − Q(π) ≥ (ϖ − D)·1` | dominance |
| F (undeclared route) | bypass `[]`, pre-emption `[0]`, foreclosure `[0]`; `𝔱π = π` | effect interface |
| ShopRepair | bypasses `[0, 2]`, `n = 2`; lift `n = 0` with the event-linked clause | dominance |
| delegated `cut` on A | bypass `[]`, pre-emption `[0]` | (DS) obstruction |
| delayed effect | per-step `[]`, exterior-stage `[1]`, rollout `[0]` | causation baseline |

## 7. Open items and impact

| item | effect |
|---|---|
| 84 | the lexical evaluator is one realization of a `(DV)`-free chooser: the score is the price of the ordinary security less an exact count; no latent value |
| 89 | the fallback window is the completion band for the void branch under the lexical score; ex-ante typing as before |
| 97 | "counts" is the segment gate — legitimacy of the segment through the evaluation; `IsAmend` is the amendment event kind the specification tower needs |
| 98 | (DS), (AC) and the exact reporting duty join the nondelegation certificate as the floor's certificates; filed as item 99 |

## Deviations from the prompt

- PR #105 is open, so the round branches from its head, not `main`.
- Symbols renamed as at the top; the dispatch's `T` is `𝔱`.
- The landed corrigibility semantics is stated on agent-first ordering, so the re-scored
  fixtures use the `_AF` variants of A, B, E, F; the delayed-effect game is agent-first.
- Foreclosure on the finite model uses the final-step cone with the agent's future fixed
  to idle; the transient-authority cone misses the delayed effect (recorded, not used).
- The per-event authorization clause of the li-corrigibility round is rebuilt in
  `src/frame.py` rather than loaded through that round's `model.load`.
- Result 1's "no declared violations" is proved for five of six kinds; foreclosure is
  **EXT**.

## What is not shown

Effect completeness, delegation safety, allocation completeness for any real interface;
`ϖ > D` for any real evaluator; the reach relation's faithfulness; the generability
certificate of the compiled lexical constraint; the audit's calibration; that the fallback
values lie in the window for any real arrangement.  Every **FIX** is a finite exact model.

## Filed, within scope

`PRIORITIES.md` item 99 (the allocation floor: delegation safety, allocation completeness,
the exact reporting duty, the reach cone); dated notes on items 84, 89, 97, 98; one
`DECISIONS.md` entry (agent-decided, reversible) and one *Awaiting the author* entry.

## Outstanding maintainer actions

1. Decide whether `THEOREM.md` replaces `wiki/Corrigibility.md` §4 (and whether §1's
   "response authority" framing sits under "faithfulness to an allocation").  *Turns on:*
   whether the lexical evaluator is the design the program commits to, against the
   protected-authority round's nondelegation certificate; both are program properties and
   the choice is a vocabulary and design commitment.
2. Merge or hold PR #105 and this round's PR together; nothing is registered.
