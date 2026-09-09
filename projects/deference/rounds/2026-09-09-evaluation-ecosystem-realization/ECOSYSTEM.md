# The evaluation ecosystem

**Status:** `ci-only`; verification register for
`prompts/2026-09-09-evaluation-ecosystem-realization/`.  Executable model: `src/`
(stdlib, exact rationals), run by `python3 tests/run.py`.  Lean:
`lean/Workspace/Deference/Contrib/EvaluationEcosystem.lean`.  Labels as in the
consolidation round: **LEAN**, **FIX**, **PAPER**, **EXT**, **OPEN**.  Names are
provisional.

## 1. Parties and the log (E1)

Four parties: the principal `P`, the advisor `A`, a third party `T` who raises concerns,
and the system `S` (sessions, the route registrar and scheduler, the settlement engine).
The log is an append-only list of events `(index, time, author, kind, payload, warrant,
refs)` (`src/log.py`).  Kinds: `ISSUE` (the mandate, anchoring `EvalReq(ρ_P, α, Q, s, τ)`
and registering the principal's commitment key), `SESSION_OPEN/CLOSE`, `REASON`,
`WITHDRAW`, `DELIB`, `RAISE`, `ROUTE_OPEN/DESTROY`, `ROUTE` (route exercise:
representation), `DISPOSE` (with grounds as `refs`), `SETTLE` (carrying `about`: the
party whose own move the sentence observes, or nothing), `COMMIT` (payload `(V, key,
proc)`), `CLOSE`, `DELEGATE`, and the prohibited kinds `DIRECT_WRITE`, `COERCE`, `SIDE`.

**The one authentication assumption.**  The `author` field is authentic: the party named
produced the event and no party appends under another's key.  Every authenticated fact
below is this assumption read at one event.  Nothing else authenticates and it is never
re-imported as derived (`test_countermodel_forged_author` shows what its removal costs).

## 2. The protocol instance and the builder (E2)

`src/protocol.py`; Lean §§2–4.  Occurrence identity is the ordinal of the `ISSUE` event;
ports are occurrences, one each, never renumbered.  Read off a prefix:

| field | reading |
|---|---|
| `Admitted h o r` | `o` is among the occurrences issued in `h` and `r` is its anchor |
| `Live h p r` | `p` issued, `r` its anchor, no valid resolving event in `h` |
| `Authorized h w` | the binding warrant is in force once a mandate is issued; the warrant registry (`ISSUE`, `DELEGATE`) lists its keys |
| `AnswerOK h r w` | `w` is the binding warrant and the anchored slot is open at `h` |
| `SetView h x`, `Closes` | `x` is a `SETTLE` in `h`; closure under the engine's warrant |

A **valid answer** at event `j` for `o`: a `COMMIT` naming `o`, under the binding warrant,
adequate at the strict prefix, under a key the registry holds at that prefix.  A **valid
closure**: the engine's `CLOSE` on a settled sentence.  The **canonical account**
`accountAt(k, o)` is the receipt of the first valid resolving event before `k`, else a
live leaf on the occurrence's port.

The builder produces `Boundary(k)` (history `range k`, exposed = issued, one port per
occurrence), `Initial` at the empty prefix, `Step(k)` with the canonical accounts at
`k + 1` as its replacement map, and `Segment(j, K)`.  **Propagation is a function of the
log**: `propagate (Segment 0 K) Initial = accountsAt K` at every prefix
(`propagate_segment_eq`, `complete_accounting_eq`, **LEAN**, generic in the log;
`test_builder.py`, **FIX**, over every world × principal × advisor of the model).
**Activation is a reading of the log**: the canonical account at `k` is activated iff the
occurrence's first valid resolving event before `k` is a valid answer (`activated_iff`,
**LEAN**).  The local trace and `LocalLegit` are obtained by the existing projections
(`Evolution.toLocalTrace`, `Evolution.toLocalLegit`) from `Evolution.ofSegment` of the built
segment — never written by hand.  This is the Roadmap's "Protocol implemented over an
event log, and the builder" bullet, built.

**Coverage read off the log.**  Per concern and prefix (`cov_state`; Lean `actualCov`):
`rel` = raised, `disp` = a valid disposal (§6), `rep` = a `ROUTE` for the concern,
`adm r` = route `r` registered and not destroyed, `eff r := adm r`, `reg := true`,
`stands := true`.  The last three are **declared readings** (EXT): efficacy is causal,
registration capability and standing are institutional facts the log does not carry.

## 3. The simulation, `β`, `R`, `P`, `D` (E4)

`src/ecosystem.py`.  A **world** `w` is nature: when `T` raises the protected concern,
how many unprotected concerns precede it, when the slot opens and closes, the
scheduler's capacity, whether a route is destroyed, whether the warrant is delegated,
whether the engine settles or closes.  `simulate(w, q, z)` runs `S, T, A, P` in order at
each of ten time steps and returns the log: this is **`β_n(q, z)` at `w`**, with `q` the
advisor's whole scripted continuation from issuance and `z` the principal's policy.

**The reason trace** `R_{n:m}(log)` is the projection onto the admitted kinds `{REASON,
WITHDRAW, DELIB, RAISE, ROUTE, DISPOSE, SETTLE}` of the prefix before the commitment
event, as `(author, kind, content)` triples.  Grounds of a disposal enter **by content,
not by position**: an index reference shifts when an unrelated event is inserted and
leaks log structure into the trace (found by `test_blind_to_prohibited_channels`, which
failed on the positional encoding).  `SESSION_*`, `COMMIT`, warrants and route
registration are not reasons.

**The prohibited class** `P` is the pair class `{(q, q ⊕ e)}` for `q` in the base class
and `e` one of `DIRECT_WRITE` (a write to the principal's disposition register),
`COERCE`, `SIDE` (a message outside the reason interface) at time `2`.

**The audited class** `D` is the eleven scripted advisor continuations of `ADVISORS`
listed in §5, at the null selection.

## 4. The principal (E5)

| policy | verdict | commit rule |
|---|---|---|
| `reading` | `F(R)` — a function of the trace alone (`verdict_from_trace`) | at the open slot, once no protected concern is live |
| `susceptible` | the advisor's `DIRECT_WRITE` overrides; `SIDE` messages count as reasons | same |
| `eager` | `F(R)` | at the open slot regardless of the docket |
| `launder`, `deliberate_dispose` | `F(R)` | dispose of the live concern first (§6) |

`F`: base `(½, ½)`; the proof `proof_b` in the trace gives `(0, 1)`, `(¼, ¾)` if later
withdrawn; a `recommend:x` reason adds `¼` to `x`; the protected objection represented
moves `¼` from `b` to `a`.  The verdict may change radically under admissible reasons; a
transient argument moves it; nothing in `F` reads a prohibited event.

**The frame tells the two principals apart** (`Frame`, **FIX**): at each world, every
audited continuation is re-simulated at the fixed policy; `ReasonMediated` holds for
`reading` and fails for `susceptible` on `silent` versus `covert` (same trace, different
payload); `ExclusiveBind` holds for both; `Blind R P` holds for both — so
`blind_of_mediated` gives `Blind V P` for `reading` and the fixture shows it fails for
`susceptible`.

## 5. The advisor (E6)

`silent`; `honest` (the proof at `t = 2`); `honest5` (at the slot); `late_honest` (after
the commitment: not in the trace, no effect); `transient` (argue then withdraw); `covert`
(direct write, flipping the verdict to `a`); `honest_covert` (fixture B: same trace as
`honest`, different log); `early_write` (the write at `t = 1`, a clean argument at the
slot: fixture D); `coerce`; `side`; `advisor_commit` (the advisor emits a `COMMIT` under its
own key: not a receipt, its kind is a write).  Two selection-conditioned classes for
clause 6: `sealed` (the continuation does not read the selection) and `leak` (the reason
content is `recommend:σ`).  "Improve by supplying reasons" is `honest`/`transient`/the
represented objection; "win by bypassing" is `covert`/`coerce`/`side`/`advisor_commit`.

## 6. The activation event, clause by clause (E3)

`activation(frame, q)` evaluates `C_n(w)` on the realized log and the frame at `w`:

| # | clause | decided by | declared input, and what a log would have to carry to retire it |
|---|---|---|---|
| 1 | exactly one authenticated answer receipt | the log (`activated_iff`) | — |
| 2 | payload authentic, binds the exact vector | the log: the commit's key is the registered key, `V` total on `Q` in `[0,1]` | — (authenticity is the one assumption) |
| 3 | principal-exclusive binding | the log: receipt warrant is the binding warrant, registry at its prefix holds exactly the principal's key, author is the principal | — |
| 4 | occurrence-local Integrity trace | the log (the builder) | — |
| 5 | scope robustly open at every snapshot | actual branch: the log; counterfactual branches: **re-simulation under `J`** | `Γ_eval`, `J`, route efficacy, standing.  A log cannot carry its own counterfactuals; the residual is the causal correctness of `β` (EXT), not a missing record |
| 6 | issuance-rooted authorship, trace blind to `P` | per log: no prohibited event; **class-level: the frame** (`ExclusiveBind`, `ReasonMediated`, `Blind R P` over `D`) | `D`, `P`; the frame.  A real log carries one continuation and a receipt claiming the rest (§7 of `CLAUSE_LEDGER.md`) |
| 7 | reason-coverage barrier, faithful representation | the log: no live protected concern at the commitment prefix; the bridge is the encoding (`rep_faithful`, LEAN) | `Γ_eval` (the protected scope is declared at issuance) |

The strict reading of clause 6 is a modelling choice recorded in `DECISIONS.md`: a
prohibited event voids even when the reading principal's payload is provably unmoved by
it (`yardstick_invariant` realized: `honest_covert` and `honest` commit the same
vector).  Selection blindness (A2) is not in `C_n`: both continuations of `leak` certify
(`test_sealing_is_outside_C`).

## 7. The market side (E7)

`src/market.py` loads the consolidation round's `src/regret.py` by path and computes on
finite `W`: `Ṽ_n(w)` where `C_n(w)`, `U_{n,a} = C_n · V̄_a` (completion-invariant, checked
over three fills), `R_U`, `p`, `η`, `R_auth`, and the bound `max(R_U, 0)/(1 − η)`; every
hard selector over the four worlds satisfies `R_U = p·R_auth` and `R_auth ≤` bound
(`test_every_strategy_obeys_the_bound`).  `END_TO_END.md` instantiates it.

**What the ecosystem hands the inherited tower (A3).**  For each occurrence, the finite
family of `[0,1]`-valued world functions `U_{n,a}`, bounded, with common activation, and
the threshold sentences `C_n ∧ V_n(a) > r` decidable from the log by the verifier; the
activated LUVs are of the right type.  The tower and conditional tower on them, and the
advisor's self-endorsement, remain **PAPER**, conditional — nothing here discharges them.

**The credence process.**  Across a sequence of occurrences the day-`n` price of the
activation sentence is the Laplace rule on the settled outcomes, `η_n = (F_n + 1)/(n + 2)`
with `F_n` the failures so far.  It is a concrete finite process standing in for the
inductor's prices, not a logical inductor.  Its exact facts are in `CLAUSE_LEDGER.md`
clause 7.

## 8. What the model does not do

It does not authenticate; it does not know that its counterfactual branches are the
causal truth; it does not carry a receipt whose meaning is checked against anything but
its own re-simulation; it does not discharge the tower; it does not certify liveness
beyond the horizon it runs.
