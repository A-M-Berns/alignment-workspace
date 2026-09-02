# Supersession map

**History remains history; canonical documents state the current theory.** No
round record is edited to pretend it never made the move below. This table is how
a reader learns which of two conflicting statements is current without inferring
from dates.

Format: what was asserted, what replaced it, where the replacement lives, and why
the change happened.

---

## 1. Program-level supersessions

| superseded | current | where | why |
|---|---|---|---|
| **Realized corrective force `beta·g(P)` is the service variable** | **Enforcement intensity `a = beta`** | `rounds/2026-08-31-normative-affordability/SERVICE_FORCE_TYPING.md` | The realized position is unschedulable (decided at the fixed point), undefined under perfect compliance, and anti-monotone in conformance — it scores a date as better served because the reasoner did worse |
| **Bounded-deficit Surface Fairness gives obligation-weighted service fidelity** | **It is a condition on total mass and gives nothing about claim weighting**; only Persistent Relevance interface 1 transfers | `…/SERVICE_TRANSFER.md` §3 | A two-surface fair rotation has service-weighted defect exactly zero at every horizon and obligation-weighted defect tending to `1/2` |
| **Contiguity is the service interface primitive** | **A transport plan** (feasibility + stability + service-to-obligation cap) | `…/SERVICE_TRANSFER.md` §4 | Contiguity is not checkable at a finite horizon, not quantitative, and false of bounded-delay service, which is normatively unimpeachable |
| **Transport derives contiguity** | **The two routes are incomparable** | `…/SERVICE_TRANSFER.md` §4 | The transport theorem bounds only the density of the *transported* obligation measure |
| **Per-reason Uptake is free from the LI criterion** | **Uptake is the MarketMaker cumulative cap** | `…/FOLLOWUP_REPORT.md` §B | The enforcement position sits in the price-setting aggregate and is not required to be efficiently computable, so the criterion never quantifies over it |
| **The criterion's preservation theorem is Uptake** | **It is substrate preservation** | `…/FOLLOWUP_REPORT.md` §B | Preservation says the learner survives being made to obey; it says nothing about the norm being taken up |
| **Pointwise self-financing is necessary for persistent affordability** | **It is sufficient and not necessary** | `…/FOLLOWUP_REPORT.md` §C | Sup/sum interchange; an alternating norm is robustly loss-making at every date while the signed account stays in a fixed band |
| **"Self-financing control"** (the name) | **withdrawn, not renamed** | same | The concept it named does not survive |
| **The sustainable authority-rate region, and its convexity by time-sharing** | **The persistence region** | `…/CAUSAL_CAPACITY.md` §1 | Time-sharing convexifies a *renewable* per-date flow; the liability budget is a *consumable* stock. And the object was wrong: the rate region reports `{0}` on friction sequences where the reason is in fact persistently served |
| **The rate region is non-convex wherever non-degenerate** | **narrowed to the finite-horizon cumulative-authority frontier** | `…/CAUSAL_CAPACITY.md` §3 | Under a floored friction every long-run rate is zero (convex); under fast-decaying friction the region is all of `R_+^R` (convex) |
| **Sharp persistence = exclusion depth alone dipping** | **`liminf L_t(1) = 0`**, comparable within a factor 4 to `min(D^2, D sqrt(m))`; depth-only holds exactly under an engine-scale floor | `…/SHARP_PERSISTENCE.md` §3, Lemma S3 | `D_t = 1` with `m_t -> 0` is persistently enforceable with no depth decay at all |
| **The sharp charge leaves the conservative criterion unchanged** | **They differ in both directions** | `…/SHARP_PERSISTENCE.md` §3 | `s_t = 1/t, m_t = t^4`: conservative friction diverges while a constant allocation is sharply affordable forever |
| **The causal scheduler is factor-4 competitive for accumulated authority** | **No positive competitive ratio exists** | `…/ONLINE_EXISTENCE.md` | Two dates cap any rule at `1/4`; an `n`-date cascade drives the ratio to zero. Only the qualitative equivalence survives |
| **A fixed disjoint blocking is the service condition** | **The sliding-window minimum `Cost_H(c) = sum_t c_t min_{s in [t,t+H]} w_s`** | `…/BOUNDED_DELAY_AFFORDABILITY.md` D4 | The two differ by up to the deadline; the disjoint version is an upper bound, not the criterion |
| **D1/D3 hold under star-shapedness** | **D1 needs concavity; D2/D3 additionally need equal obligation masses** | `…/BOUNDED_DELAY_AFFORDABILITY.md` §2 | With existing load the comparison is between increments (split `2` beats atomic `5/2`); a crossed assignment wins `1.6` vs `6` when a saturating date should take the larger claim |
| **Bounded-delay cost interpolates to persistence as `H -> infinity`** | **withdrawn** | `…/BOUNDED_DELAY_AFFORDABILITY.md` §4 | `lim_H Cost_H` can strictly exceed `Cost_infinity` when the gaps between cheap dates diverge |
| **Eventual full service is strictly stronger than persistence** | **They are equivalent as existence questions (EV1)** | `…/EVENTUAL_VS_UNIFORM_SERVICE.md` §2 | The old countermodel priced block-batching and read one plan's cost as the minimum; the diagonal gives each claim its own dip |
| **Positive density of cheap dates implies bounded gaps**; **bounded gaps imply finite timely cost** | **both withdrawn**; only D4 decides | `…/EVENTUAL_VS_UNIFORM_SERVICE.md` §4 | Countermodel E3: gaps of exactly two, friction dipping to zero, cost diverging |
| **`F_r` is a property of the norm, scheduler-independent** | **`F_r` is the misfit profile read against the chosen service measure** | `…/SERVICEABILITY_FRONTIER.md` §3, `…/JOINT_SERVICEABILITY.md` §1 | A scheduler that services a reason on nearly-satisfied dates gets a small residual; one that services it on deep-exclusion dates does not |
| **The transport residual is the raw sum `sum T eps`** | **the obligation-normalized `epsbar_N(T)`** | `…/SERVICE_TRANSFER.md` T3 | The raw sum is extensive and diverges on any infinite obligation stream even when every edge is exact to a fixed tolerance |
| **Every Pareto point is recovered by scalarization** | **true, under fractional splitting** (linear objectives on the transportation polytope); otherwise only the supported frontier | `…/JOINT_SERVICEABILITY.md` JS2 | Repaired rather than withdrawn — the hypothesis was missing, not the conclusion |
| **Every form of overload is liability overload** | **conditional on force feasibility** | `…/OVERLOAD_TARGET.md` §2 | An empty region, an unpriceable row, or an illegal compiled control fails before any account is consulted |
| **Separate reason underwriting is necessary** | **The additive test is sufficient; the true joint cost is subadditive** | `…/MULTIREASON_SERVICEABILITY.md` M1 | The world quantifier supplies an economy of scope, and shared rows another |
| **SS1 holds with no hypothesis on the live sets** | **needs assessment-set nesting `A_N ⊆ A_t`** | `…/SHARP_SERVICEABILITY.md` SS1 | The charge is scored against `A_t`, the residual against `A_N`; a world admitted after `t` was never bounded by `D^r_t` |
| **The square-root branch fails "only when `m_t` is not summable"** | **`(1/A_N) sum (l_t + m_t)^2/m_t -> 0`** | `…/SHARP_SERVICEABILITY.md` §3 | Summability is neither necessary nor sufficient |

## 1a. Supersessions made by this checkpoint itself

Two, both from the September cleanup, and both about how the checkpoint describes
things rather than about the mathematics.

| superseded | current | where | why |
|---|---|---|---|
| **Gale–Hoffman / Horn as *adjacent* prior art to BD1**, with "we take nothing formally" | **A direct mathematical dependency** | `../../notes/PRIOR_ART.md` §6.2 | BD1's sufficiency proof invokes the Gale–Hoffman feasibility condition by name. A document cannot claim independence from a theorem its proof cites. Independent rediscovery is a fact about process and never settles dependency |
| **Affordability as a conjunct of the candidate legitimacy decomposition** | **A realizability side condition** | `LEGITIMACY_DECOMPOSITION.md` §3 | As a conjunct it invites the reading that a cheaper norm is more legitimate, which the round's own slogan — *cheap enforcement is not always conforming enforcement* — forbids. Affordability contributes feasibility, never normativity |

Neither changes a theorem. Both change what the checkpoint is entitled to say.

## 2. Terminology

### 2a. The September 2026 naming audit

A maintainer pass, applied across the checkpoint and the wiki. Historical rounds keep
their original vocabulary and are not rewritten; this table is how a reader maps one
onto the other.

| retired | canonical | why |
|---|---|---|
| **claim stream** | **obligation stream** | *claim* already means a traded proposition in the market, an asserted result, and a normative entitlement. The quantitative burden `c^r_t` needed a word of its own |
| **claim measure** | **obligation measure** | same; `mu^r_N` weights dates by what was owed |
| **claim-weighted** | **obligation-weighted** | and the bare word **Progress** now denotes it |
| **claim mass**, **claim marginal** | **obligation mass**, **obligation marginal** | same |
| **claim-normalized transport error** | **obligation-normalized semantic error** | follows the two renames above, and names the *source* of the error — semantic change, not the transportation algorithm |
| **allocated authority** | **enforcement intensity** | *authority* is normatively loaded elsewhere — practical authority, authority genealogy, authorized disposition, standing authority. `a_t = beta_t` is a mechanical scalar the scheduler fixes before the market clears |
| **allocated service** | *retired* | a second name for the same scalar. Service is the broader Answerability-facing relation; intensity is the resource that supplies it here |
| **local authority capacity** | **local enforcement capacity** | follows the rename; *per-date intensity cap* is acceptable for the scalar inequality alone |
| **transport stability** | **semantic stability** | it is not a property of the transport plan. It says later service still counts as answering what was owed earlier, up to controlled distortion — which across a self-revision is the central problem |
| **service parsimony** | **service-to-obligation cap** | not a virtue and not advice to economize; a bound on over-service, `W_N <= K C_N` |
| **nested assessment** | **assessment-set nesting** | the assumption is `A_N ⊆ A_t`. Its *reason* is settlement monotonicity, and using one phrase for both blurred an assumption into its justification |
| **settlement-misfit landscape** | **misfit profile**, or just the exclusion deficits | florid, and used twice |
| **serviceability frontier** | **critical delay** `H*(B)` plus the **liability–timeliness tradeoff** | the frontier was never a primitive. The scalar is the critical delay; the rest is a monotone relation between budget and achievable timeliness |
| **overload certificate** | **finite-horizon infeasibility certificate** | the fixed-era enforcement layer does not behave like a shared server, and *overload* reimports that model. The certificate may witness capacity failure, liability failure, or both |
| **friction**, used for three objects | **settlement-friction residual** `F_r(a)`; **date cost** `L_t(a)`; **conservative cost coefficient** `q_t = D_t sqrt(m_t)` | the worst collision in the set. `q_t` is a coefficient inside one date-cost instance, not a cost of anything by itself |

**Kept after review**, because connected prose exposed no collision: answerability
slice, anchored interpretation, fixed-set contiguity, coercive Actionability,
persistence region, star-shaped date cost, admissible service trace, critical delay,
deadline insolvency, realized force, service measure, Service Transport, Uptake,
Progress, Sharp Timely Service.

**`Sharp Timely Service` keeps its name, with `sharp` defined wherever it is
introduced.** It names the *sharp robust liability charge* — `L_t(a) = a D_t^2/4` on
the linear branch — and not tightness or exactness in any generic sense. That exact
charge is what lets one budget control the settlement-friction residual's numerator.
`PAPER_CANDIDATES.md` notes that a paper may prefer *Timely Service under Sharp
Liability* if the short name proves opaque outside this repository.

### 2b. Earlier terminology

| retired | canonical | note |
|---|---|---|
| *pin*, *pinned* (of a settlement) | **settlement event**, **settled** | `pin` is reserved for settlement in the vendored interface documents; repository artifacts are **frozen** |
| *pinned* (of a digest or input) | **frozen** | same reservation |
| *the pen / the clock / the purse* | **reports / timing / enforcement** | `consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §0 |
| *self-financing control* | — | withdrawn, not renamed |
| *sustainable authority-rate region* | **persistence region** | the object, not just the name, was wrong |
| *realized corrective force* (as the service variable) | **enforcement intensity** | the term survives for the endogenous position; it is not service |

## 3. Names, after the audit

The September 2026 naming audit settled the prose vocabulary; §2a is the map. The
names in the right-hand column there, together with the *kept* list, are canonical
for current-facing documents.

**Still provisional, and a smaller list than before:** the two inherited from the
diachronic-answerability note — **answerability slice** and **anchored
interpretation** — which are the note author's to settle rather than this
checkpoint's, and which read well after reconciliation.

**Not covered by this audit:** the Lean declaration names. `state/views/NAMING_AUDIT.md`
carries that backlog, which is mechanical, much larger, and a separate sitting.

## 4. Three concepts that should not be revived

1. **Any rate-region or time-sharing picture of authority.** The budget is a
   consumable stock. This has now been got wrong twice from two directions and is
   the program's most reliable trap.
2. **Realized force as a measure of service.** Every quantity built on it inverts
   the sign of successful learning.
3. **Any gap or density condition on cheap dates as a substitute for `D4`.** Three
   separate attempts have failed; the sliding-window sum is the criterion and
   nothing weaker decides it.
