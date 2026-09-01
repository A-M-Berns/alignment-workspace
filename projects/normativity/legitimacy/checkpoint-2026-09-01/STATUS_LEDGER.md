# Status ledger

One row per major result or interface. **Theorem status and philosophical
confidence are different axes and this table only reports the first.**

## The status vocabulary

The repository's registered epistemic classes (`AGENTS.md`) are, in strength
order, `lean-proved` > `enumeration-verified` > `witness-checked` >
`contributor-checked` > `test-supported` > `conjectured`. Almost nothing in this
program is *registered*, so the table below also uses four non-registry statuses
that describe how a result was obtained:

| status | meaning |
|---|---|
| **lean-proved** | a kernel-checked Lean declaration exists and is named |
| **paper-derived** | a complete prose proof exists in the repository; no Lean; not citable as proven |
| **test-supported** | exact-rational fixtures compute instances; the general statement is *not* thereby verified |
| **established specialization** | a corollary of something above, under stated extra hypotheses |
| **interface assumption** | consumed as a hypothesis; no argument here that it holds |
| **conjectural** | stated, believed, unproved |
| **open** | not answered in either direction |
| **superseded** | was asserted, is not current; see `SUPERSESSION.md` |
| **interpretive** | a reading, not a mathematical result |

Most Layer I rows are **paper-derived + test-supported**. That pairing is the
program's normal state and its natural fate is a Lean port.

---

## Layer I — fixed-era normative dynamics

| # | result / interface | status | source |
|---|---|---|---|
| 1 | **Traderized projection enforcement** — the compiled position is a legal strategy | **lean-proved** | `Workspace.Normativity.Contrib.TraderizedEnforcement`; `projects/normativity/rounds/2026-08-16-traderized-enforcement/PROOF_CLOSURE.md` |
| 2 | **Per-date conformance modulus** `sum beta g^2 <= eps + M` | **lean-proved** | `…TraderizedEnforcement.weighted_square_le_slack_add_volume` |
| 3 | **Preservation / no efficient trader exploits** under bounded liability | **lean-proved**, with one transcription obligation | `AssessmentFirm.trading_firm_dominance`, `no_efficient_trader_exploits`; `PROOF_CLOSURE.md` §VII for the modified market's computability |
| 4 | **Service is allocated authority `a = beta`**, not realized force | **paper-derived**, decisive | `rounds/2026-08-31-normative-affordability/SERVICE_FORCE_TYPING.md` |
| 5 | **Actionability / coercivity (Theorem F1)** — convergence iff `phi` bounded away from zero away from zero | **paper-derived** + **test-supported** | `…/FIXED_ERA_THEOREM.md` §1 |
| 6 | **Joint Actionability** — fails reason-relative, holds against the common region | **paper-derived**, with countermodel | `…/JOINT_ACTIONABILITY.md` |
| 7 | **Uptake = MarketMaker cumulative cap** (not the LI criterion) | **paper-derived**, and a correction of a prior claim | `…/FOLLOWUP_REPORT.md` §B |
| 8 | **Common-Mixture Affordability** | **paper-derived** + **test-supported** | `rounds/2026-08-30-progress-liability-hard-pass/JOINT_MARGIN.md`; `rounds/2026-08-30-liability-theory/LIABILITY_THEORY.md` |
| 9 | **Reasonwise accounting (R1)** — subset ceiling `U + B_tot` from per-row floors | **paper-derived** + **test-supported** | `…/REASONWISE_ACCOUNTING.md` |
| 10 | **Local capacity ≠ lifetime SafeCert** | **paper-derived**, with counterexample | `…/CAPACITY_VS_SAFETY.md` |
| 11 | **Signed vs conservative account: unbounded separation** | **paper-derived** + **test-supported** | `…/SIGNED_VS_CONSERVATIVE.md` |
| 12 | **Service-weighted Progress (F2)** at rate `A_N^{-1/2}` | **paper-derived** | `…/FIXED_ERA_THEOREM.md` §2; `…/LI_PROGRESS_FROM_SERVICE.md` |
| 13 | **Service Transfer T1/T2** — contiguity exactly N&S for triangular arrays | **paper-derived** + **test-supported**. *Prior-art caution:* essentially Le Cam's contiguity equivalence in a new application — see `../../notes/PRIOR_ART.md` §6 | `…/SERVICE_TRANSFER.md` §1 |
| 14 | **Fixed-set contiguity strictly weaker** (one-step-delay separation) | **paper-derived** + **witnessed** | `…/SERVICE_TRANSFER.md` §2 |
| 15 | **Deferred Service Transfer (T3)**, claim-normalized error | **paper-derived** | `…/SERVICE_TRANSFER.md` §4 |
| 16 | **Surface Fairness does not give claim-weighted Progress** | **paper-derived** + **witnessed** | `…/SERVICE_TRANSFER.md` §3 |
| 17 | **Bounded-delay feasibility (BD1), interval condition** | **paper-derived** + **test-supported**. *Prior-art caution:* a Gale–Hoffman / Horn-1974 specialization; likely a rediscovery | `…/BOUNDED_DELAY_TRANSPORT.md` |
| 18 | **FIFO optimal and complete (BD2)** | **paper-derived**. *Prior-art caution:* classical | `…/BOUNDED_DELAY_TRANSPORT.md` §3 |
| 19 | **Exogenous persistence criterion (S1)** `liminf L_t(1) = 0` | **paper-derived** + **test-supported** | `…/SHARP_PERSISTENCE.md` |
| 20 | **Two routes to a cheap date (S3)**; depth-only needs an engine-scale floor | **paper-derived** + **test-supported** | `…/SHARP_PERSISTENCE.md` §3 |
| 21 | **Finite-horizon optimum (S2)** = `max_t L_t^{-1}(B)` | **paper-derived** | `…/SHARP_PERSISTENCE.md` §4 |
| 22 | **Persistence ≡ eventual full service (EV1)** | **paper-derived** + **test-supported** | `…/EVENTUAL_VS_UNIFORM_SERVICE.md` §2 |
| 23 | **Uniform timeliness strictly stronger (E1); gaps insufficient (E3)** | **witnessed** (exact countermodels) | `…/EVENTUAL_VS_UNIFORM_SERVICE.md` §§3–4 |
| 24 | **Linear timely-service criterion (D4)**, sliding window | **paper-derived** + **test-supported** | `…/BOUNDED_DELAY_AFFORDABILITY.md` |
| 25 | **Sharp settlement-friction collapse (SS1)** — `F_r = 0` on the linear branch under nested assessment | **paper-derived** + **test-supported** | `…/SHARP_SERVICEABILITY.md` |
| 26 | **Sharp Timely Service (STS)** — the endpoint | **paper-derived** + **test-supported** | `…/SHARP_TIMELY_SERVICE.md` |
| 27 | **Deadline insolvency certificate (DI1)** | **paper-derived** + **test-supported** | `…/DEADLINE_INSOLVENCY.md` |
| 28 | **Online persistence has no penalty; no competitive ratio for authority** | **paper-derived** + **witnessed** | `…/ONLINE_EXISTENCE.md`, `…/ONLINE_SERVICEABILITY.md` |
| 29 | **Joint frontier convex under fractional splitting** | **paper-derived** | `…/JOINT_SERVICEABILITY.md` JS2 |
| 30 | **Finite-horizon overload certificate**, sound, no converse | **paper-derived**; converse **open** | `…/EXISTENCE_AND_DUALITY.md` §4; `PRIORITIES.md` item 74 |
| 31 | **Temporal-modulus certification (hypothesis T)** | **open** — no mechanism | `…/SHARP_TIMELY_SERVICE.md` §6; `PRIORITIES.md` item 76 |
| 32 | **Closed-loop affordability (E4/E5)** | **open** | `…/CLOSED_LOOP_EXISTENCE.md`; `PRIORITIES.md` item 75 |
| 33 | **Signed-account viability / sufficient state** | **open** — the scalar slack is provably insufficient | `…/SIGNED_VS_CONSERVATIVE.md` |
| 34 | **Necessity of bounded liability** | **open** | `PRIORITIES.md` item 40 |
| 35 | **Simultaneous (S) and (L)** | **open** | `…/SHARP_TIMELY_SERVICE.md` §6 |

## Layer II — diachronic legitimacy across revision

| # | result / interface | status | source |
|---|---|---|---|
| 36 | **Grounded Replay** — every applicable rule has finite recorded provenance in `R_0` | **paper-derived** | `rounds/2026-08-25-legitimate-evolution/`; the note, Thm 2.5 |
| 37 | **Prospective revision / anchored protocol execution** — a later revision cannot retroactively judge an earlier episode | **paper-derived** | the note, Lemma 3.9 and Req. 3.5; `rounds/2026-08-28-answerable-revision/` |
| 38 | **Slice-wise Answerability Conservation** — `c_alpha = Satisfied ∨ Disposed ∨ Remaining` | **paper-derived** + **test-supported** | the note, Thm 6.1. Repository counterpart is in the **unlanded** answerability stack — see the caution below this table |
| 39 | **Remaining content cannot increase; no silent terminal closure** | **paper-derived** | the note, Cor. 6.2 and 6.3 |
| 40 | **Semantic no-laundering** — relabelling alone cannot reduce anchored content | **paper-derived**, *conditional on* semantic authentication and slice faithfulness | the note, Thm 7.5. Repository counterpart **unlanded** |
| 41 | **Semantic authentication `J_alpha`, slice faithfulness** | **interface assumption** — application-supplied | the note, §7, Req. 7.2 and 7.4 |
| 42 | **Persistent-Wait Theorem** — permanent idleness stabilizes on one unrouted blocker | **paper-derived** | the note, Thm 8.12; `rounds/2026-08-28-answerable-challenge-service/` |
| 43 | **Idle non-expansion** | **interface assumption** (a requirement on the reasoner, not a theorem) | the note, Req. 8.10 |
| 44 | **Wait responsiveness, non-starvation** | **interface assumption** | the note, Assumptions 8.13 and 8.16 |
| 45 | **Answerability–Service Dichotomy** — either the matter dies terminally accounted, or attention diverges | **paper-derived** | the note, Thm 9.2 |
| 46 | **Continuity service (CS)**: `m live forever ⟹ A_N(m) → ∞` | **paper-derived**, consumed by Progress | `rounds/2026-08-30-normative-continuity-settlement/`; `progress-consolidation/FINAL_SCHEMATIC.md` |
| 47 | **Cross-era Answerability** — what makes a later service count as answering an earlier claim | **open** | see `OPEN_PROBLEMS.md` §2 |
| 48 | **Content-preserving transfer across representation change**, quantitatively | **open** — the conceptual calculus exists; the metric bridge to `eps(t,s)` does not | `ANSWERABILITY_AND_SERVICE.md` §5 |
| 49 | **Justified defeat / authorized disposition** as a normative (not merely accounting) notion | **open** | the note, Def. 5.2 gives the accounting slot; what licenses it is not characterized. `PRIORITIES.md` item 77 |

> **Caution on Layer II sources.** Rows 36–45 and 49 rest on a maintainer-supplied
> note, *Diachronic Answerability Under Self-Revision* (31 August 2026), which
> declares itself paper-proved and not Lean-verified. Its three repository
> counterpart rounds — answerability carriers, anchored slices, faithful semantic
> preservation — together with the CF-coverage rounds of rows 52–53, are **not on
> `main`**: their pull requests merged into each other on the branch
> `round/2026-08-30-answerability-carriers`, which was never landed. Their exact
> fixtures therefore do not run in this repository's CI, and rows citing them are
> **paper-derived only** until the stack lands. This is recorded, not resolved.

## Layer III — counterfactual non-capture

| # | result / interface | status | source |
|---|---|---|---|
| 50 | **Carroll criterion reproduction** (live covering authority + counterfactual persistence under ancestry excision) | **test-supported**; 50/52 target cells | `rounds/2026-08-25-carroll-legitimacy-test/` |
| 51 | **Excision is non-monotone and non-composable** | **witnessed** | same round; falsification pass |
| 52 | **Coverage** (world-to-record adequacy) | **open** — consumer-relative, deliberately outside the answerability system | the note, §11; the CF-coverage round, **unlanded** |
| 53 | **No Clean Self-Sealing** | **partial** — false from Continuity alone; true under ambient factorization + behavioral locality | the CF-coverage round's `SELF_SEALING.md`, **unlanded** |
| 54 | **Counterfactual non-capture as a pillar of legitimacy** | **conjectural framing** | `LEGITIMACY_DECOMPOSITION.md` |

## Layer IV — corrigibility / deference consumer

| # | result / interface | status | source |
|---|---|---|---|
| 55 | **Epistemic deference ≠ practical authority** | **interpretive**, and load-bearing for scoping | `wiki/Deference.md`, `wiki/What-Deference-Requires.md` |
| 56 | **Legitimacy theorem** | **open** — nothing of this shape exists yet | `ROADMAP.md` |
| 57 | **Corrigibility from legitimacy** | **open** | `wiki/Corrigibility.md` |

---

## The three things this table is most often misread as saying

1. **"Sharp Timely Service is proved."** It is *paper-derived and
   test-supported*, under five hypotheses two of which (T and the simultaneous
   existence of S and L) have no construction. It is the strongest thing Layer I
   has; it is not a verified theorem.
2. **"Lean-proved covers the enforcement story."** Three narrow declarations are
   kernel-checked: the compiler's legality, the per-date modulus, and the
   trading-firm dominance lift. Nothing about Progress, transport, affordability,
   or timeliness is in Lean.
3. **"Layer II is open."** Its *structural* half is as well developed as Layer I —
   conservation, replay, prospective revision, the service dichotomy. What is open
   is the *semantic* half: what content survives, and what makes a later answer
   count as an answer to an earlier claim.
