# Current theory

**What this is.** The minimal current theory of the normativity / answerability /
legitimacy program, stated once, with statuses and source paths. It is dry by
intention: definitions, theorem statements, a dependency spine, and what each
result does *not* say. Interpretation lives in the wiki.

**How to use it.** An agent starting a round may treat everything marked current
here as available, subject to its status in `STATUS_LEDGER.md`. Nothing here is a
registered claim: the program's results are paper-derived and exact-rational
tested, and the distinction matters — see *Evidence* below. Terms not listed here
are either superseded (`SUPERSESSION.md`) or were never load-bearing.

**Evidence, in one paragraph.** The repository's class order is
`lean-proved` > `enumeration-verified` > `witness-checked` > `contributor-checked`
> `test-supported` > `conjectured` (`AGENTS.md`). Almost all of the theory below
is **paper-derived prose proof plus exact-rational fixtures**, which is
`test-supported` at best and is *not* citable as proven. The kernel-checked
exceptions are named where they occur. A finite fixture is not a proof of a
statement quantified over infinite horizons; where a document says "pinned by a
fixture", read "an instance was computed exactly", never "the theorem was
verified".

---

## 1. The four layers

The program divides cleanly, and the division is the single most important thing
in this document.

| layer | question | state |
|---|---|---|
| **I — fixed-era normative dynamics** | Within one settled semantics, one evaluator, no ontology revision: when can standing normative claims receive safe, affordable, timely, progress-producing service? | **closed for research sequencing** |
| **II — diachronic legitimacy across revision** | Which reasons survive a self-revision, what makes a successor answerable to a predecessor, how content transports across representational change | **structural core consolidated; semantic transport and authorized disposition open and load-bearing** |
| **III — counterfactual non-capture** | Whether the process producing later reasons and evaluators has itself been manipulated or foreclosed | **open** |
| **IV — corrigibility / deference consumer** | What a legitimacy theorem must hand the deference line | **downstream; interface only** |

**"Closed for research sequencing"** means the current theory regards the question as
sufficiently answered to consume downstream unless an actual contradiction appears.
**It is not an evidence class**, and it is orthogonal to one: Layer I is closed in
this sense while almost all of its mathematics is paper-derived and test-supported
rather than formally verified. Where the two are confused, `STATUS_LEDGER.md`
governs.

**Layer I is what the affordability round closed.** It does *not* answer: which
reasons survive a self-revision; when one reason may defeat or replace another;
how the content of a reason is transported across representational or evaluator
change; what makes a successor answerable to a predecessor; how to prevent
manipulation of the process that generates reasons; counterfactual non-capture;
legitimacy; corrigibility. Every one of those is Layer II, III or IV.

---

## 2. The narrow waist

    world / environment
        --> interaction record            (what actually got written)
        --> settlement                    (what the record makes settled)
        --> normative interpretation      (what the settled record obliges)
        --> controlled learner            (what force the obligation exerts)

Five distinctions the waist keeps apart, and the program should not let collapse:

- **world** — the latent structure. Nothing in the theory quantifies over it
  directly; **coverage** is the (open) consumer-relative adequacy condition
  relating world to record.
- **settlement engine** — supplies three and only three things: **reports** (what
  it writes), **timing** (when), **enforcement** (the weight behind it).
  `consolidation-aug9/THEORY_11_SETTLEMENT_INTERFACE.md` §0.
- **settlement event** — a procedure's report `X(q,t)`. What settles is what the
  procedure returned, never the world-fact behind it. Canonically *not* "pin";
  that word is reserved and the repository's own artifacts are "frozen"
  (`consolidation-aug9/GLOSSARY.md`).
- **endorsement** — one compiled book commitment: a one-sided constraint on the
  credal state. Endorsements are what the docket polytope is built from.
- **normative force** — the compiled trading position that makes a constraint
  operatively bind a bounded reasoner. Force is *not* a semantics and *not* a
  legitimacy certificate.

---

## 3. Layer I, in dependency order

### 3.0 Objects

| symbol | reading |
|---|---|
| `r` | a reason occurrence; owns rows `J_r` |
| `c^r_t >= 0` | the **claim stream**: normative exposure owed to `r` at date `t`; `C^r_N = sum_{t<N} c^r_t` |
| `a^r_t >= 0` | **allocated authority** (service), predictable; `A^r_N = sum_{t<N} a^r_t` |
| `mu^r_N = c/C^r_N` | the **claim measure** — what is owed |
| `nu^{a,r}_N = a/A^r_N` | the **service measure** — what was delivered |
| `d_t in [0,D]` | the **defect**: how badly the reason is answered at `t` |
| `s^{+,r}_t(omega)` | the **exclusion deficit** of the row at live world `omega` |
| `D^r_t = sup_{omega in A_t} s^{+,r}_t(omega)` | the worst live **exclusion depth** |
| `m_t = eps_t + M_t` | the market maker's slack plus the ordinary volume bound |
| `A_t` | the **live assessment set** at `t` — worlds settlement has not excluded |
| `T^r(t,s)` | a **transport plan**: claim mass owed at `t`, served at `s` |

### 3.1 Force — how a constraint binds a bounded reasoner

`projects/normativity/notes/TRADERIZED_FORCE_INTERFACE.md`;
`projects/normativity/rounds/2026-08-16-traderized-enforcement/`.

A price-space region `K_t = { P : <c_j,P> >= r_j }` compiles to a legal trading
strategy

    E_t(P) = sum_j beta_{t,j} g_j(P) c_j ,
    g_j(P) = max(0, r_j - <c_j,P>) ,   beta_{t,j} = (eps_t + C^vol_t)/delta_t^2 ,

added to the aggregate the market maker prices against. It does **not** modify the
market maker, which is why every theorem about the maker survives.

**Conformance guarantee** — `lean-proved`
(`Workspace.Normativity.Contrib.TraderizedEnforcement.weighted_square_le_slack_add_volume`):

    sum_j beta_{t,j} g_j(P_t)^2  <=  eps_t + C^vol_t     hence   g_j(P_t) <= delta_t .

**What force emits is a liability obligation, not a safety certificate.** The
surrounding layer must discharge the enforcement position's cumulative value over
the assessment worlds. A caller reading a conformance certificate as a criterion
guarantee has misread the interface.

**Preservation** — if cumulative liability over the assessment worlds is bounded by
`B`, no efficiently computable trader exploits the modified market and each has
assessed net worth at most `1 + B`. The generalized live-world lift is
`lean-proved` (`AssessmentFirm.trading_firm_dominance`,
`no_efficient_trader_exploits`); the modified market's computability is a
transcription obligation recorded in that round's `PROOF_CLOSURE.md` §VII.

> **Preservation is substrate preservation.** It says the learner survives being
> made to obey. It is *not* Uptake, and it is not a normative result.

### 3.2 Service is allocated authority, not realized force

`rounds/2026-08-31-normative-affordability/SERVICE_FORCE_TYPING.md`.

The service variable is `a = beta`, the enforcement multiplier fixed *before* the
market maker picks a price. It is predictable and freely schedulable. The realized
position `beta·g(P_t)` is decided at the fixed point, is zero exactly when the
reason is perfectly satisfied, and would count a date as *better served* because
the reasoner did worse. Three failures of the realized-force reading:
unschedulable; undefined under perfect compliance; anti-monotone in conformance.

> **Successful learning looks like starvation** if service is read as realized
> force: constant `beta` against geometric defect has divergent allocated service
> and summable realized force.

### 3.3 Actionability — what corrective authority can do

`rounds/2026-08-31-normative-affordability/FIXED_ERA_THEOREM.md` §1 (Theorem F1);
`LI_PROGRESS_FROM_SERVICE.md`.

With `Work_N = sum_{t<N} a_t phi(d_t)` and `phǐ(eps) = inf_{d >= eps} phi(d)`:

1. `Work_N/A_N -> 0` together with `phǐ(eps) > 0` for every `eps > 0` gives
   `E_{nu}[d] -> 0`; and if `phǐ(eps) = 0` for some `eps > 0` there is a
   trajectory with `Work_N/A_N -> 0` and `E_{nu}[d] >= eps`. So the condition is
   necessary as well as sufficient.
2. Without regularity: `E_{nu}[d] <= inf_eps [ eps + D (Work_N/A_N) / phǐ(eps) ]`.
3. With `phi` convex, `phi(0) = 0`, strictly increasing:
   `E_{nu}[d] <= phi^{-1}(Work_N/A_N)`.

> **Convexity is not needed for convergence; it buys the rate.** Projection
> enforcement is `phi(d) = d^2` (rate `sqrt(Work/A)` rather than `(Work/A)^{1/3}`);
> the older linear form is `phi(d) = gamma d`. One theorem, both realizations.

**Joint Actionability** (`JOINT_ACTIONABILITY.md`) **fails** for reason-relative
scoring — an exhibited pair with jointly satisfiable demands has per-reason gain
`-1/8` after aggregation — and **holds** against the common region, with no
convexity and no separability. In the traderized realization it is true and
*unused*, because the compiled position is reactive: there is no aggregation step
at which a per-reason certificate could be invalidated.

**Where Actionability sits.** *Beside* service allocation, not after it.
Answerability says what is owed; Actionability says what a unit of authority
accomplishes. Neither derives from the other. See §4.

### 3.4 Uptake — and where it does not come from

`rounds/2026-08-31-normative-affordability/FOLLOWUP_REPORT.md` §B.

**Uptake is the market maker's cumulative cap, not the LI criterion.** The
enforcement position sits in the price-setting aggregate and is *not* required to
be efficiently computable, so the criterion never quantifies over it. The earlier
claim that per-reason Uptake is free from the criterion is **withdrawn**. What
supplies it is the MarketMaker cap `V^r_N(omega) <= U`, with `U = C + B_F`.

### 3.5 Liability and the account

`rounds/2026-08-30-liability-theory/`;
`rounds/2026-08-30-progress-liability-hard-pass/`;
`rounds/2026-08-31-normative-affordability/REASONWISE_ACCOUNTING.md`,
`CAPACITY_VS_SAFETY.md`, `SIGNED_VS_CONSERVATIVE.md`.

**The account identity.** With `w = beta·g` the position magnitude (not the
multiplier), `V_N(w) = sum_t w_t (d_t - s_t)` where `s` is the **signed** misfit
`r - <c,omega>`. The clipped deficit does *not* satisfy this identity. The maker
cap `V <= U` and the floor `V >= -B` sandwich the service-weighted defect against
the service-weighted misfit.

**Common-Mixture Affordability.** One uniformly covered assessed-world mixture
whose barycenter is admitted by every active projection constraint gives a
tolerance-independent uniform bound `E_N(omega) >= -U(1-theta)/theta`.
Compatibility is retrospective, not merely per-date, and coverage is over payoff
profiles rather than syntactically distinct worlds.

**Reasonwise accounting (Lemma R1).** With per-row liability floors
`sum_j B_j <= B_tot`, every subset of rows gets the uniform ceiling `U + B_tot`.
**Aggregate safety alone does not suffice**: two books with increments `+1` and
`-1` have an identically zero aggregate account and unbounded per-book values.

**Local capacity is not lifetime safety.** A policy inside its per-date capacity at
every date has an account unbounded below when the allowances are not summable.
Spending the *realized* account slack strictly enlarges the viable region,
quadratically.

**Conservative underwriting is strictly and unboundedly smaller than signed-account
affordability.** A satisfied row takes a zero position and costs nothing however
deep its exclusion of the live worlds. The scalar account slack is **not**
sufficient state, because the world attaining the minimum can settle away.

**Two quantifiers, never to be conflated.** Progress uses `inf` over live worlds —
one compatible world suffices. Liability uses `sup` — it needs a covered mixture.

### 3.6 Progress

`rounds/2026-08-30-progress-consolidation/FINAL_SCHEMATIC.md`;
`rounds/2026-08-31-normative-affordability/LI_PROGRESS_FROM_SERVICE.md`,
`FIXED_ERA_THEOREM.md` §2.

**The staging is canonical even though the bare name is not.** Whatever the
maintainer settles "Progress" to mean, the two-stage structure below is how the
checkpoint refers to it, and a document using the bare word without a qualifier is
underspecified:

    service-weighted Progress  --Service Transport-->  claim-weighted Progress
    (the learner-side               (§3.7)              (the Answerability-facing
     mechanism theorem)                                 endpoint; also written
                                                        Sustainable Progress)

**Two forms, and they are genuinely different statements.**

*Service-weighted Progress* — `E_{nu^{a,r}_N}[d] -> 0`. What the learner delivers.
**Theorem F2** (finite horizon), for every `omega` live at `N`:

    E_{nu^{a,r}_N}[d]  <=  || s^+_r(omega) ||_{L^2(nu^{a,r}_N)}  +  sqrt( (U + B_tot) / A^r_N ) ,

with the unconditional fallback `sqrt(S_N/A^r_N)`, `S_N = sum_{t<N} m_t`. The rate
is the inverse square root of allocated service; the residual is the norm's own
weighted mean-square exclusion of the still-live worlds. The liability charge grows
like `sqrt(a)`, which is why divergent service fits a finite lifetime budget.

*Claim-weighted Progress* — `E_{mu^r_N}[d] -> 0`. What Answerability actually asks
for. It does **not** follow from the service-weighted form without a transport
hypothesis (§3.7).

**Which of the two the bare name "Progress" should denote is reserved to the
maintainer** (`DECISIONS.md`, *Awaiting the author*). That reservation is about the
*name*; the staging above is not reserved and is used throughout this checkpoint.

**Surface Fairness is a mass condition and does not deliver claim-weighted
Progress.** A two-surface fair rotation satisfies bounded-deficit `(SF)` with
service-weighted defect exactly zero at every horizon while the claim-weighted
defect tends to one half. Of the four Persistent Relevance interfaces, only
**interface 1** — a registered surface exposed on every service date with
`c_n >= c_* > 0` — transfers; it gives `mu_N <= nu_N/c_*` pointwise and therefore
the quantitative transfer outright. Interfaces 2 and 4 give `(SF)` and nothing
more; the countermodel *is* a two-surface fair rotation.

**Continuity service is the input.** Normative Continuity supplies
`m live forever ==> A_N(m) -> infinity`; Progress consumes it and adds no queue or
successor relation of its own.

### 3.7 Service Transport — relating delivered service to inherited claims

`rounds/2026-08-31-normative-affordability/SERVICE_TRANSFER.md`.

**Contiguity is the exact condition for the array version.** `mu <| nu` — for every
`A_N subseteq [N]`, `nu_N(A_N) -> 0` implies `mu_N(A_N) -> 0` — is necessary and
sufficient (T1, T2). A settlement-relative defect *is* a triangular array, because
the assessment set shrinks as settlement arrives, so necessity bites. For a defect
sequence fixed independently of the horizon the exact condition is the strictly
weaker **fixed-set contiguity**; one-step delay separates them.

**Contiguity is nevertheless the wrong interface primitive** — not checkable at a
finite horizon, not quantitative, and false of bounded-delay service.

**Theorem T3 (Deferred Service Transfer)** is the primitive. Given an adapted
transport plan with the claim marginal, feasibility against `a^r`, stability
`d_t <= L d_s + eps(t,s)` on its support, service parsimony `W_N <= K C_N`, and
residual density `R_N/C_N -> 0`:

    E_{mu_N}[d]  <=  L K E_{nu_N}[d]  +  epsbar_N(T)  +  D R_N/C_N ,
    epsbar_N(T)  =  (1/C_N) sum_{t,s} T_N(t,s) eps(t,s) .

The transport error is **claim-normalized**: a raw sum is extensive and not
comparable to the claim-weighted average it bounds.

**The two routes are incomparable.** Transport does not derive contiguity — what it
bounds is the density of the *transported* claim measure.

### 3.8 Bounded-delay transport, and its exact cost

`BOUNDED_DELAY_TRANSPORT.md`, `BOUNDED_DELAY_AFFORDABILITY.md`.

**BD1 (feasibility).** Against a given service profile a plan exists iff for every
interval, `sum_{[u,v]} c <= sum_{[u,v+H]} a`. Prefixes do **not** suffice, because
service cannot run backwards. **BD2:** first-in-first-out is optimal and complete,
so the plan of T3 is *constructed*, not assumed. Both have strong classical
antecedents — see `../../notes/PRIOR_ART.md` §6.

**D4 (minimum cost, linear branch).** When the profile is chosen,

    Cost_H(c)  =  sum_t c_t · min{ w_s : s in [t, t+H] } ,

a **sliding** window minimum. D1 (no splitting) needs **concavity**, not
star-shapedness; D2/D3 (monotone runs) additionally need **equal claim masses**.

### 3.9 Affordability — whether such service can persist

`SHARP_PERSISTENCE.md`, `PERSISTENT_AFFORDABILITY.md`, `CAUSAL_CAPACITY.md`,
`ONLINE_EXISTENCE.md`, `OVERLOAD_TARGET.md`.

A date's **cost function** `L_t(a)` charges the liability account. Two instances:
conservative `q_t sqrt(a)` with `q_t = D_t sqrt(m_t)`; sharp robust `a D_t^2/4` on
the linear branch `a <= 4m_t/D_t^2`, and `D_t sqrt(a m_t) - m_t` beyond. Both are
increasing, vanish at zero, and are **star-shaped** (`L(a)/a` nonincreasing).

**Theorem S1 (persistence).** For increasing star-shaped `L_t` with `L_t(0) = 0`, a
schedule with `sum a_t = infinity` and `sum L_t(a_t) <= B` exists **iff**

    liminf_t L_t(1) = 0 .

The reference level and the budget are both immaterial.

**Lemma S3.** `(1/4) min(s^2, s sqrt(m)) <= L(1) <= min(s^2, s sqrt(m))`, so there
are **two independent routes to a cheap date**: a shallow exclusion, and an engine
that is easy to move. The criterion reduces to the depth alone exactly under an
engine-scale floor `m_t >= m_0 > 0`.

**Theorem S2 (finite-horizon optimum).**
`max{ sum_{t<N} a_t : charge <= B } = max_{t<N} L_t^{-1}(B)`, attained by spending
the whole budget on one date. An unbounded optimum is necessary but not sufficient
for persistence.

**Persistence is budget-free and does not compete across reasons.** The persistence
region is the full power set of the persistable reasons; there is no Hall-type
condition. **Timely service does compete**, because its minimum cost is a definite
positive number and budgets add — the joint condition is a single sum, sufficient
and not necessary when reasons share rows.

**Online.** A doubling-threshold rule achieves persistence whenever an offline
scheduler can — no online penalty for the *property*. There is **no** positive
competitive ratio for the *amount* of authority accumulated. Under deadlines the
online gap reappears and is unbounded, closing only if the whole window's weights
are predictable at arrival.

**Overload.** Conditional on force feasibility there is no service-capacity
competition between reasons, so overload within that qualification is *liability*
overload; an empty region, an unpriceable row, or an illegal compiled control is a
failure before any account is consulted. The finite-horizon Farkas certificate is
sound and has **no converse**.

**Insolvency.** *Persistence* insolvency is a claim about the infinite future and
needs a proved tail bound; an observed friction floor is not a certificate.
*Deadline* insolvency is finite and authenticated:
`ReqCost = sum_t c_t min{ w_s : s in [max(t,now), t+H] }` (`DEADLINE_INSOLVENCY.md`),
complete exactly when future weights are certified **from below**.

### 3.10 The three service problems

`EVENTUAL_VS_UNIFORM_SERVICE.md`.

    persistence  ==  eventual full service   (  uniform bounded delay

**Theorem EV1.** Under exogenous increasing star-shaped `L_s` vanishing at zero,
finite claims with `sum c_t = infinity`, fungible service and unlimited deferral, a
persistent affordable schedule exists **iff** an affordable plan discharging every
claim exists — both equivalent to `liminf L_s(1) = 0`. Forward by a diagonal that
gives each claim its own cheap date on a geometric tranche of the budget.

**Uniform timeliness is strictly stronger** (countermodel E1), and **no gap
condition substitutes for D4** (countermodel E3: gaps of exactly two, friction
dipping to zero, and divergent timely-service cost).

> **Unlimited deferral makes "eventually answer every persistent claim" no harder
> than maintaining divergent service. The substantive Answerability constraint
> enters only when delay itself matters.**

### 3.11 The endpoint: Sharp Timely Service

`SHARP_TIMELY_SERVICE.md`. **The canonical positive result of Layer I.**

Hypotheses: **(S)** an adapted transport plan with `A^r_N -> infinity`, parsimony
`K_r`, vanishing residual density; **(L)** sharp-linear affordability —
`a^r_t <= 4 m_t/(D^r_t)^2` and `sum (1/4) a^r_t (D^r_t)^2 <= B_r`; **(M)** the
MarketMaker ceiling `U_r = U + B_tot`; **(N)** nested assessment
`A_N subseteq A_t`; **(T)** temporal stability `d^r_t <= L_r d^r_s + eps_r(t,s)` on
the plan's support.

    E_{mu^r_N}[d^r]  <=  L_r K_r ( 2 sqrt(B_r) + sqrt(U_r) ) / sqrt(A^r_N)
                         +  epsbar^r_N(T)
                         +  Dbar_r · R^r_N / C^r_N .

Corollaries: `limsup <= limsup epsbar`; `<= omega_r(H)` under uniform delay `H`;
`-> 0` under exact preservation.

> If Answerability's claims can be transported onto sufficiently timely,
> sharp-linearly affordable enforcement dates, then the same liability budget that
> preserves the learner also drives settlement friction away, leaving only the
> semantic change incurred while the reason waited to be answered.

**What (L) buys.** The liability charge is computed from the supremum over live
worlds of the *same* deficit whose weighted mean square is the settlement-friction
residual, so the residual's numerator is exactly four times the charge and the
residual vanishes. **`F_r` stays in the generic schematic theorem** — the
square-root branch keeps it positive, and (L) is exactly the boundary.

**Hypothesis (N) is load-bearing.** The charge at `t` is scored against `A_t`, the
residual at `N` against `A_N`. Settlement removes continuations and never restores
them; without that, a world admitted after `t` was never bounded by `D^r_t`.

**Corollary.** On the linear branch a norm permanently excluding *every* live world
by a fixed `sigma > 0` cannot be persistently and affordably enforced at all, since
`sigma^2 A_N <= 4B`. Persistent affordable enforcement therefore *entails*
asymptotic compatibility with something still live.

> **Cheap enforcement is not always conforming enforcement.** A norm cheap because
> nobody trades against it (`m_t -> 0`) buys persistence without buying conformance.

---

## 4. The dependency spine, audited

    settlement / interaction semantics
        |
        v
    Answerability generates claims on future normative capacity
        |                        (Layer II object; consumed here as the stream c^r_t
        |                         plus a set of admissible traces)
        +--------------------------+
        |                          |
        v                          v
    Actionability:              traderized force compiles the row;
    what a unit of              LI supplies Uptake under bounded liability
    authority accomplishes         |
        |                          |
        +----------+---------------+
                   v
    allocated authority a^r_t produces service-weighted Progress
                   |
                   v
    Service Transport relates delivered service to inherited claims
                   |
                   v
    affordability / serviceability decides whether that service persists
                   |
                   v
    claim-weighted Sustainable Progress
                   |
                   v
    (L) + timely transport  ==>  Progress up to semantic delay only

**Two corrections to the naive spine.**

1. **Actionability is not downstream of service allocation; it is beside it.**
   Answerability fixes *what is owed* (`c^r_t`); Actionability fixes *what a unit of
   authority accomplishes* (`phi`); the scheduler fixes *how much authority goes
   where* (`a^r_t`). Progress needs all three and derives none from the others.
   Placing Actionability after allocation suggests the scheduler could choose the
   coercivity modulus, which it cannot: `phi` is a property of the response
   geometry and the enforcement compiler, not of the schedule.

2. **The normative demand and the force mechanism are different objects, and the
   spine must show both.** The demand is `(c^r_t, admissible traces)` — exported by
   Answerability, indifferent to how it is met. The mechanism is
   `(K_t, E_t, beta)` — the compiled position and the liability it incurs.
   Affordability is precisely the question of whether the mechanism can meet the
   demand; conflating the two makes that question unaskable, which is the error the
   allocated-service typing corrected.

---

## 4a. The candidate legitimacy decomposition — a research framing

    Legitimacy  ~  Diachronic Answerability, with its semantic authentication
                +  Counterfactual non-capture
                   subject to Affordability as the realizability condition

**This is a research framing, not part of the current theory.** No legitimacy
predicate has been written down anywhere in this repository; the three terms have
not been shown independent; and joint sufficiency for the corrigibility consumer is
unproved. `LEGITIMACY_DECOMPOSITION.md` argues for it and states what would make it
canonical — a definition with a conclusion someone downstream wants — which does not
exist. Cite it as a framing or not at all.

**Affordability is a realizability condition and not a source of legitimacy.** It
says the answering was something the reasoner could have done. Nothing normative
comes from it, and reading it as a conjunct invites the inference that a cheaper norm
is more legitimate — which §3.11's own slogan forbids.

## 5. The Answerability interface

> **Answerability exports admissible claim / service / transfer obligations;
> affordability determines which of those traces the learner can safely realize.**

That sentence is the interface. `ANSWERABILITY_AND_SERVICE.md` states what each
side actually contains, what the mathematics now realizes, and what the conceptual
theory demands that no theorem here supplies — chiefly **disposition**, for which
Layer I has no analogue at all: in the current service theory claim mass is served
or it persists; it never legitimately ceases to be owed.

---

## 6. What Layer I does not construct

The honest boundary of the endpoint theorem.

- **Existence of a plan satisfying (S) and (L) simultaneously.** Timeliness and
  linear-branch affordability are each characterized; their intersection is not.
- **The constants of (T).** No mechanism certifies a temporal modulus. `epsbar` is
  a symbol until one exists. (`PRIORITIES.md` item 76.)
- **(L) in the closed loop.** Every existence result is E0–E2 of
  `CLOSED_LOOP_EXISTENCE.md`: the date costs are exogenous. (Item 75.)
- **Necessity of bounded liability.** (Item 40.)
- **A converse to the overload certificate.** (Item 74.)
- **That `F_r` is ever zero for a norm a practice produces.**
- **Anything across eras.** The residual `eps_r` is a *within-era* deferral
  residual. Cross-era transport needs a semantic bridge nothing in Layer I supplies.
