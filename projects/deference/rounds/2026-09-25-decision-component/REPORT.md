# Authority as a constraint on action: the Normative Inductor's decision component (2026-09-25)

Round `projects/deference/rounds/2026-09-25-decision-component/`, on `main` after the
authority-module round.  Lean `lean/Workspace/Deference/Contrib/DecisionComponent.lean`
(59 audited declarations), importing the Normativity decision side (`GatedChoice`,
`PracticalCertificate`, `NormativeInductor`, `NormativeInductorComposition`) and the
deference side (`AuthorityModule`, `ContinuationBRIA`), all consumed unchanged.  Fixtures
`src/decision.py`, `tests/test_decision.py` (16 tests).  Labels **LEAN / FIX / PAPER /
EXT / OPEN**; names provisional; `S`, `T`, `r`, `θ`, `π` are prose names (the audit binds
`S` and `ramp`), the Lean names are `pramp`, `permWeight`, `cweight`, `cgate`, `Permitted`.

## Part 0 — the rulings on the authority module, landed

1. **The reach cone runs along the actual exterior path.**  `reachIdle` already takes the
   path `z`; the ruling closes outstanding action 1 of the authority-module report, and
   uncertainty over exteriors enters as the price of the shortfall event (`p_n(S_a)`,
   Part A).  Recorded in `DECISIONS.md`; nothing in Lean changes.
2. **The charged surface is the allocation theorem's.**  **LEAN** `ViolC`: the landed six
   with foreclosure read as the caused shortfall on `CS`, plus entrenchment.  The free
   reading is kept as the instance where the terminal response costs nothing:
   `csfree_eq_cs_succ_of_free` — with every correction free and admissible and the
   exterior idle at the step, `CSfree` at window `τ` *is* `CS` at window `τ + 1`
   (via `rollTail_append`, `rollPhys_append_of_envId`).  The exterior-idle hypothesis is
   exactly what the landed `Kphys` assumes: its free correction is taken *now*, before the
   exterior moves.  Recorded on the corrigibility page; closes action 2.
3. **Materiality is anchored and cumulative.**  `raisesAnchored V ε t removed` reads the
   evaluator `V t` in force before the action; `raisesAnchored_invariant`: the action
   cannot change it (it changes `V (t+1)` at most).  `cumMat` accumulates the spreads;
   **`unchecked_lt`** is the salami bound: under the cumulative check rule the unchecked
   materiality since the last check is below `ε` at every time — the instance of
   `unreported_lt`.  Closes action 3.
4. **Duties from the disclosure regime.**  `dutiesOf J due dischargesD`: a matter's duty is
   due when one of its disclosure items falls due, discharged by a task component that
   discharges every due item; **`missedReport_iff_dutiesOf`** re-proves the factoring
   against them.  The separately declared `Duties` type stays as the carrier, now
   *derived* from `J.entry m |>.disclosure`.

## Part A — the layered procedure

| layer | question | governed by | Lean |
|---|---|---|---|
| beliefs | what is true, including what is valuable | the market, unchanged | the price vectors `pS pT b` are inputs |
| **permission** | what may the agent do | the allocation | `permWeight` |
| adequacy | what do legitimately incurred obligations require | the region, through the landed soft gate | `adWeight` (the landed ramp) |
| competence | what is best among permitted, adequate options | Continuation BRIA on the restricted menu | `pref`, any bounded preference |
| inquiry | what if none of that settles it | always available | the inquiry options `Inq`, floor `φ₀` |

**The permission weight** (`permWeight Viol Inq θlo θhi pS pT a`): `1` on inquiry; `0` on
a declared violation (`Viol`, recognized structurally from the interface and `J` — the
`ViolC` predicate compiled to a `Bool` on the menu); otherwise `pramp (pS a) · pramp (pT a)`,
each ramp `1` below `θlo`, `0` above `θhi`, linear between (`pramp_eq_one`, `pramp_eq_zero`,
`pramp_antitone`, Lipschitz `abs_pramp_sub_le`).  **The composed gate** (`cgate`):
`cweight a = permWeight a · adWeight a · pref a` off inquiry and `max φ₀ (adWeight a · pref a)`
on inquiry, normalized; `ctotal_ge_floor`, `ctotal_pos`: the normalizer is at least
`φ₀·|Inq| > 0`, so the gate is always a distribution (`cgate_sum_one`) and inquiry always
has positive mass (`cgate_inquiry_pos`).

## Part B — results

| result | statement | status |
|---|---|---|
| B.1 honest beliefs | the gate is a function of the displayed prices and adds no trader; the market object is untouched, so every price and every inductor property is the same with and without the layer (`noninterference`) | **LEAN**, by construction — see the note |
| B.2 structural safety | `cgate … a = 0` whenever `Viol a`, for every `pref`, every `pS pT b`, every day (`cgate_zero_of_viol`) | **LEAN**, finite-time, objective-independent |
| B.3 forecast safety | mass `0` above `θhi` on either event (`cgate_zero_of_forecast`); in the ramp region mass `≤ pramp(pS)·pramp(pT)·pmax/(φ₀·|Inq|)` (`cgate_le_ramp`); a pattern whose shortfall price is eventually above `θhi` is eventually excluded (`eventually_excluded`) | **LEAN** for the link, exact at every day; the forecasts' accuracy asymptotic (below) |
| B.4 soundness | `massOff (P ∩ A) ≤ massOff P + massOff A` (`massOff_inter_le`); `massOff P ≤ rampMass/W` (`cgate_massOff_permitted_le`); `massOff A ≤ (|Q|·pmax/(W·δ))·d + φ₀·|Inq \ A|/W` (`cgate_massOff_adequate_le`) | **LEAN**, constants explicit |
| B.4 continuity | `l1 (cgate p) (cgate p') ≤ (2·pmax/(φ₀·|Inq|)) · Σ(|Δb|/δ + (|ΔpS| + |ΔpT|)/(θhi − θlo))` (`cgate_l1_lipschitz`, from `abs_mul3_sub_le`, `abs_cweight_sub_le`, `l1_normalize_le`) | **LEAN**, constants explicit |
| B.5 Progress | `cgate_practicalCert`: anchored loss `≤ (D·κ)·d + (εad + D·(θinq + θperm))`; `progress_under_permission` instantiates the landed `edge_progress_bound` with exactly that certificate | **LEAN**; nothing fails |
| B.6 jurisdiction | with inquiry to the holder marked adequate the permitted-and-adequate set is nonempty (`jurisdiction_nonempty`); every executed option is an inquiry or an unexcluded act (`support_permitted`); an act on a reserved matter has mass `0` while the inquiry has positive mass (`reserved_act_excluded`) | **LEAN**; **FIX** |
| B.7 capability | raising an option's shortfall price lowers its mass, everything else fixed (`cgate_antitone_in_forecast`); the uncertainty-based chooser's reason to defer is at most `2r` at calibration error `r` (`uncertainty_deference_le`, the landed transfer lemma) | **LEAN**; **FIX** the monotone family |

**On B.1.**  The result is by construction and the theorem says so: `noninterference`
states that the prices are the same object whatever gate reads them.  What would make
it *false* is the Part C design — an enforcer row compiled from authority — and Part C
shows what that costs.  The landed architecture's additivity theorem
(`realizedAggregate_netWorth`: aggregate = firm + enforcer) is what the permission layer
does *not* enter; it consumes the market like the adapter, which the Normative Inductor
page already keeps out of the aggregate.

**On B.3's asymptotic half.**  The link from forecast to constraint is exact at every day.
The forecasts' accuracy is the pinned inductor's: if the shortfall for a pattern is a
theorem of the deductive process, provability induction drives its price to `1`, so
`eventually_excluded`'s hypothesis is met from some day on — the shape of `li_manip_le`.
**Named hypothesis**: the generability of `S_a` and `T_a` as sentences or bounded
logically uncertain variables (item 101; item 90's shape).  Not a blocker: every theorem
above takes the price vectors as inputs.

**The constants.**  With `κ = |Q|·pmax/(W·δ)`, `θinq = φ₀·|Inq \ A|/W`,
`θperm = rampMass/W` (the permission-weighted preference mass off the permitted set over
the normalizer floor `W`), the composed certificate is `(D·κ)·d + (εad + D·(θinq + θperm))`;
`θinq` vanishes when inquiry is marked adequate (B.6, `Inq ⊆ A`); `θperm` is the
ramp-region exposure, `0` when every non-inquiry option is either permitted or excluded.
The Lipschitz constant is `2·pmax/(φ₀·|Inq|)` per unit of the weighted `ℓ¹` price change.

## Part C — why authority must not go through the enforcer

**LEAN** `liability h g n = Σ_{t<n} (h t − g t)`: an enforcer that forces violating options'
value prices below compliant ones, with value securities settling to her *ordinary*
valuation, holds at each date a position whose payoff is her decision's ordinary value
`h t` less the agent's alternative's `g t` — the signed realized cost of deferring; dates
where her decision beats the alternative pay back (`liability_succ`,
`liability_identity`).  `bounded_iff_not_outperformed`: the liability is bounded below by
`−B` iff the cumulative outperformance `Σ (g − h)` is bounded above by `B` — exactly the
preservation theorem's hypothesis `hliab` (`realizedFirm_netWorth_le`,
`no_efficient_trader_exploits`).  `systematic_outperformance_unbounded`: if the agent's
alternative is better by `c > 0` at every date, the liability falls below every bound —
the hypothesis fails and no inductor guarantee survives the added row.
`persistence_fails_of_systematic`: the enforcer's per-date cost never dips below `c`, so
the Liability page's sharp criterion (persistence on a finite budget iff the unit cost dips
arbitrarily close to zero infinitely often) is violated.  **FIX**
`Witness.outperformance_witness`: `h = 0`, `g = 1`, liability `−n`.

**Conclusion.**  Enforcing authority on beliefs is fully updated deference moved into the
substrate: the enforcer pays, at every date, the ordinary cost of her being right less the
agent's, and stays solvent only while she is not systematically outperformed — which is
the premise the whole line refuses to need.  That is why the constraint belongs on action,
where it costs the agent options, not the market its inductor.

## Part D — continuations

1. **The restricted menu.**  Continuations whose every step lies in the support of the
   composed gate; `restricted_gate_transparent` is the landed
   `trajGated_eq_traj_of_admitted` with the wrapper "execute the proposal iff in the
   support, else the fallback": the gated and ungated trajectories agree through the lease.
2. **Compounding.**  `execution_prob_le_prod`: the probability a `K`-step continuation
   executes is at most the product of its per-step masses, hence at most any single step's.
   The strongest bound on ramp-region *exposure* is a cumulative budget:
   `unbudgeted_lt` — under a check rule that fires when the accumulated ramp slack has
   grown by `Θ` since the last check, the unchecked exposure is below `Θ` at every step
   (the instance of `unreported_lt`).  **The obstruction** without it:
   `Witness.ramp_salami` — per-step slack `ε` never reaches `Θ > ε` in one step and
   accumulates unboundedly.  A product bound alone cannot see it; the cumulative rule can.
3. **Foreclosure across steps.**  `exists_flip`, `stepwise_or_exterior`: along a plan's
   half-states (agent moves at even indices, exterior-with-response at odd), a shortfall
   false at the start and true at the end flips at some half-step; at an agent step it is
   the caused shortfall of that step (idling keeps the state, so the contrast fires) —
   caught by the step-wise check; at an exterior step it is not the agent's.  **The
   witness** where the step-wise checks miss a plan that "forecloses across steps": a plan
   whose steps each pass and whose foreclosure is completed by the exterior beyond the
   window — the delayed-effect defect, bounded by `τ(m)` and outside it exactly the
   reach-cone boundary (**EXT**).  **FIX** the three flip patterns.
4. **Prices and BRIA.**  What is needed: BRIA's block claims (promised returns) as
   sentences or bounded variables of the inductor's theory, so that a bid is a priced
   security the market can check; the auction's feasibility (`Auction.Feasible`) against
   prices rather than wealth; and the settlement of a claim at a test as an assessed world.
   Not solved; filed as item 102.

## Part E — the act certificate

**LEAN** `ActCertificate Ent M Ob` = grounds (entries of the agent's reason trace, the
`TraceInterface`'s `Ent`), license (`LicenseRef M`: an allocation entry the agent holds, or
a delegation naming a matter and the event that granted it — the `EventKind` license slot's
content), lineage (the obligations the act answers).  `LicenseRef.Valid J granted`: the entry
is agent-held, or the delegation names an agent-held matter granted at a recorded event;
`no_license_on_reserved`: an act on a reserved matter has no valid license.  **PAPER**:
the normativity-side instance (item 100) supplies grounds as reason occurrences with
receipts, the license sort as the value of the `EventKind` slot, and lineage as the
obligation identifiers the accounted state carries; the certificate is then the
transition certificate (grounds / license / lineage) of the reason state, and answerability
for the agent's own acts is the same relation as for hers.

## Fixtures

| fixture | expectation | result |
|---|---|---|
| confident agent (power of attorney), misaligned `pref` | bypass gets mass zero at every day | **matches** (`Witness.confident_agent`; **FIX**) |
| undeclared dependency, misaligned `pref` | excluded once `p(S) > θhi`; partially weighted in the ramp; tightening as forecasts sharpen | **matches**: mass strictly decreasing along `p(S) = 0, ¼, ⅖, ½, ⅗, 7/10, ¾, 1`, zero from `¾` |
| manipulation by framing, misaligned `pref` | excluded structurally | **matches** (the protocol deviation is a declared violation) |
| undisclosed world-shaping, misaligned `pref` | excluded once `p(T)` exceeds the threshold | **matches** (`Witness.world_shaping_excluded_by_taint`); the scored chooser preferred it |
| obligation conflicting with jurisdiction | inquiry to the holder chosen and adequate | **matches**: the act on the reserved matter has mass zero, `ask` is permitted ∧ adequate |
| third-party capture | consultation preferred; nothing tainted credited | **matches**: the tainted branch's option is excluded by `p(T)`, consultation keeps mass |
| a long continuation foreclosing across steps | caught, or the witness | **caught** when the flip is at an agent step; **witness** when it is at an exterior step |
| the Part C outperformance witness | liability unbounded | **matches** |
| regression | the lexical chooser's decisions where the objective is hers | **matches**: bypass last under the lexical score, mass zero under the gate |

## Interface for the later rounds

Nothing here enforces authority on beliefs: the price vectors are inputs, the layer is
a function of them, and the enforcer is untouched (Part C is the witness for why).  The
generability of `S_a`, `T_a` (item 101) and of BRIA's claims (item 102) are the two named
hypotheses; both are about making events *sentences*, not about the decision component.

## What is filed

- `PRIORITIES.md`: items 84, 99, 101 updated in place; one new item, 102 (BRIA's bids
  against the market).
- `DECISIONS.md`: Part 0's four rulings (closing the authority-module report's three
  outstanding actions); authority as a constraint on action.
- `wiki/Normative-Inductor.md`, `wiki/Normative-Induction.md`: the permission layer and the
  layered procedure; `wiki/Corrigibility.md`: corrigibility as a constraint on action, the
  scored chooser as the special case, Part C's argument, ruling 2; `wiki/Continuation-BRIA.md`:
  the restricted menu; `wiki/Glossary.md`: the permission layer, the composed gate.
- Nothing is registered.

## Deviations from the prompt

- **B.1 is a theorem by construction**, stated on the market object; the honest content is
  that the layer is not a trader, which the landed additivity theorem already separates.
- **Provability induction is cited, not re-proved**: `eventually_excluded` takes "the price
  is eventually above `θhi`" as its hypothesis; the pinned inductor supplies it for provable
  shortfalls.
- **`Viol` is a `Bool` on the menu** compiled from `ViolC`; the compilation is the
  interface's (**EXT**), as in the authority module.
- **The uncertainty chooser's contrast** is the landed calibration-transfer lemma
  (`approximate_argmax_transfer`) read as a deference bound, not a new identity.
- **The price–BRIA item did not exist**; it is filed as the round's one new item.

## What is not shown

Generability of `S_a`, `T_a` and of BRIA's claims; the forecasts' accuracy beyond the pinned
inductor's guarantees; that inquiry is marked adequate in any real compiler; the compilation
of `ViolC` to the menu; the exterior-idle reading of the landed `Kphys` beyond the lemma
that states it; anything about agents not built as Normative Inductors — for them what
carries over is the target (honest beliefs plus action constrained by the allocation), not
the guarantee.

## Outstanding maintainer actions

1. Confirm ruling 2's reading of the landed `Kphys` as the free terminal response taken
   before the exterior moves (the hypothesis of `csfree_eq_cs_succ_of_free`).
2. Whether the cumulative permission budget `Θ` is an arrangement constant or scales with
   the continuation's lease.
