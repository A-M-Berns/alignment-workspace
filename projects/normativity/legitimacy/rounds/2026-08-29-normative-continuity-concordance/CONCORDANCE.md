# Provenance concordance — Normative Continuity against the prior legitimacy work

Verdict: **`CONCORDANT WITH LOCAL REPAIRS`.** No theorem of the synthesis contradicts a
frozen result; every trace the synthesis admits satisfies the frozen Legitimate Evolution
carry law. What the concordance found is undeclared *design reversals* of frozen LE
decisions, inherited through the unfrozen Answerable Process page, and one provenance
misstatement about the no-rewiring rule. The repairs are errata (§5) for the next revision
of the source, and one decision reserved to the author (§6). The checkpoint bytes are not
touched.

Sources. **LE** = `rounds/2026-08-25-legitimate-evolution/` (`02a91fa`, frozen:
`LEGITIMATE-EVOLUTION-FROZEN`); **AP** = the Answerable Process one-pager and its freeze
report (`~/Downloads/answerable_process_onepager.tex`, `answerable_process_freeze_report.md`,
`answerable_process_final_freeze.md`, 2026-08-28 — **not in the repository, not a round,
not frozen by the workspace's convention**); **ACS** =
`rounds/2026-08-28-answerable-challenge-service/`; **SR** =
`rounds/2026-08-28-service-realization/` (`e2f6265`); **LI** =
`rounds/2026-08-27-legitimate-improvement/` (`4745c8d`); **CIS/TC** =
`rounds/2026-08-23-certified-interactive-service/`, `2026-08-23-transition-certificates/`
(`289a07a`). "Synthesis" = `NORMATIVE_CONTINUITY.tex` in this directory. Proof status
column: *paper* = paper proof in the synthesis, checked by the proof pass;
*Lean* = proved in `lean/Workspace/Normativity/Contrib/NormativeContinuity.lean`;
*assumption* = not a theorem anywhere.

## 1. Standing layer (Legitimate Evolution)

| Current item | Status | Exact source | Exact change | Proof status |
|---|---|---|---|---|
| `L_n`, `G = L_0` | rephrased | LE `LEGITIMATE_EVOLUTION.md` §MINIMAL: `L_0 = G`, `L_{t+1} = apply_t(L_t,e_t) if Valid ... L_t otherwise` | rejected-edit branch and `Valid` fold dropped; update written for accepted batches only, `L_{n+1} = (L_n \ L_n^-) ∪ L_n^+` | definition |
| `Auth` | inherited exactly | LE ibid. `Auth : Occ -> Prop`; `replay.py` "a predicate, not half of a partition" | — | definition |
| `Permit_n(c)` at strict pre-state | consolidated, **weakened** | LE §2 `Valid_α(L,e) := grounds ⊆ Auth(L) ∧ (changes → grounds ≠ ∅) ∧ ProvComplete_α(e) ∧ Permit(L,e,ProvView_α(e))`; `ANSWERABILITY.md` A21/A34 | `Permit_n` absorbs `Valid`; the `ProvComplete`/`ProvView` clauses (LE §6: "the largest hole") are gone. S1 applied to every accepted edit in LE; synthesis Req 1 constrains grounds only of edits that change standing (erratum E6) | definition |
| `g ⊆_fin Past_n` | consolidated | LE Cor. 1 (no self-ratification, derived); AP §3 "`g ⊆_fin Ref(H_n)`" | one global strict-prefix typing for all grounds; LE's Corollary 1 becomes typing | definition |
| nonempty standing `Auth` grounds on change (S2) | inherited exactly | LE `S2 apply_t(L_t,e_t) ≠ L_t → grounds(e_t) ≠ {}` with S1 | S1 and S2 fused into one clause conditioned on change | Lean: `StandingTrace.grounds_standing`, `grounds_nonempty` |
| freshness of `L_n^+` | inherited, made explicit | LE "Freshness is definitional — the trace is a list"; THEOREM_MAP #8 (`office.readoption` issues one content twice) | stated as a clause (added by the proof pass) | Lean: `StandingTrace.Fresh`, stated, **not consumed** by `grounded_replay` |
| Grounded Replay | restricted | LE Theorem: tree for every `o ∈ Adm_t`, leaves in `G`, children the grounds, positions strictly descending; `replay.py:282 thm_grounded_replay` | quantified over `λ ∈ L_n` (live) instead of `Adm_t` (admitted); induction on entry position instead of on `t` through `Adm_t` | Lean: `StandingTrace.grounded_replay` (from Req 1 alone) |
| ancestry not permanence | rephrased | LE §3 "`Live_t ⊆ Admitted`; a grounding tree ... cannot certify that it is still in force"; THEOREM_MAP #10–11 | prose only; no named `Admitted`/`Grounded` sets | — |
| standing-change vs resolution grounding asymmetry | consolidated, newly stated | LE S2 (standing edits only); AP report §E "the kernel never reads g (ResolveOK does)" | stated as a principle for the first time. Note LE A21/A22 gate *resolution* by `Permit` at the pre-state; the synthesis gates it by `κ_q` via `Resolve_n` only (erratum E4) | — |
| `λ ▷ (κ,τ,x)`, `κ ⊩_n (τ,x)` | **new** (typed realization) | LE §5 "`PAuth` carries a `SchemaCode` and no domain" (`PRIORITIES.md` 67); AP §9 opaque `Stand_n(κ,·,·) ⇒ κ in force at n with finite ancestry` | replaces AP's opaque `Stand_n` with a derived relation reading `L_n`; `Stand`-soundness becomes trivial; the `▷` feature is the capability field item 67 says RI lacks | Lean: `Licensing.standsFor`, `anchor_grounded` |

## 2. Due / issue materialization

| Current item | Status | Exact source | Exact change | Proof status |
|---|---|---|---|---|
| `Due` as level, `NewDue_n = Due_n \ Due_{n-1}` | rephrased, **timing changed** | LE `ANSWERABILITY.md` DUE ACTIVATION: `ActiveDue_t = Due(represented_{≤t}, L_t)`, `NewDue_t = ActiveDue_t \ ActiveDue_{t-1}` (A28) | LE reads `represented_{≤t}` (current event included); synthesis reads the strict prefix `H_n`, so activation from a record in `e_n` lands in `NewDue_{n+1}` (erratum E3) | definition |
| falling edge resolves nothing | inherited exactly | LE A31 | — | — |
| Req 3 (new demands become issues) | consolidated, **reclassified** | LE `D1 NewDue_t ⊆ NewlyIncurred_t`, A18 "a conformance condition, not a premise", A33 inclusion; AP §2 Materialization | inclusion kept; promoted from realization-boundary conformance to structural requirement, as AP did; not load-bearing for any theorem (synthesis says so) | — |
| phase order (A34) | **changed** | LE A34 "descriptive material from the current event; normative standing from the strict pre-state" | synthesis "Acceptance convention": every judgment at `H_n`. The standing half of A34 is preserved (Req 2); the descriptive half is not | — |
| compatibility of due with standing | generalized | AP §9 constitution example "an admission protocol stands at every n"; AP report §D "H-adm" | stated for every newly-due pair, explicitly not a theorem | assumption |

## 3. Answerable Process continuity

| Current item | Status | Exact source | Exact change | Proof status |
|---|---|---|---|---|
| issue occurrence `π(q) = (τ,x,κ,s⁰)` | inherited exactly | AP §2 | "claim" → "issue" | definition |
| Req 4 `O_{n+1} = (O_n \ Res_n) ∪ Q⁺_n` | inherited from AP; **reverses LE** | AP §4, AP report D4 ("forces every new claim to be outstanding for at least one step"); LE `answer.py step` unions openings before removals, A17 "same-step Due and resolution ... is not a loophole" | synthesis follows AP: a fresh issue cannot resolve in its birth batch (erratum E2) | Lean: `IssueTrace.resolution_continuity` (field) |
| Req 5 `S ⊆ Q⁺_n` (fresh successors) | inherited from AP; **reverses LE** | AP report §E "`S ⊆ N_n` **kept** ... freshness makes acyclicity a theorem"; LE A11 "freshness is not required and successors may be preexisting or shared", A5 withdrew the fresh-successor clause (`office.carry_into_existing_claim` is a *legitimate* LE fixture) | synthesis restricts LE's design space; every synthesis trace satisfies LE's carry law (`S ≠ ∅ → S ⊆ O_{t+1}`), so no LE theorem is contradicted, but a trace LE called legitimate is refused (erratum E1; reserved decision §6) | Lean: `IssueTrace.fresh_successors` (field); acyclicity via `born_lt_of_out` |
| prospective re-anchoring (Lemma 1) | strengthened (condition → lemma) | AP §5 (anchor) + (episode); ACS §C E1; CSP SC7′ | (episode) is derived from `Resolve_n` being defined as `κ_q`'s verdict | paper |
| Req 6 state continuity | abstracted | AP §5 `origin ∈ {transport(f), reset(g₀)}`; AP-final B3 `Par_n` | two-shape disjunction replaced by opaque `Continue_n(P;q',g)`; `Par_n` exact | — (not load-bearing) |
| matters, split/merge, designation | inherited | AP report D2 `μ(q)`, AP-final B1 ("descendants never leave an ancestor's matter ... Merge: a joint successor is in both parents' matters. Split: designate") | `Live_n(m) = {q ∈ O_n : m ⪯ q}` | Lean: `TraceData.Live`, `live_empty_persistent` |
| time-indexed `M_n`, `β(m)` | **new** | none (AP defines matters atemporally) | needed so `o_n(m) = 0` before birth and the NSA case split is well-formed | Lean: `M`, `matters_mono`, `matters_prior` (abstract fields the paper's construction satisfies) |

## 4. Prerequisite / actionability layer

| Current item | Status | Exact source | Exact change | Proof status |
|---|---|---|---|---|
| prerequisite occurrences `δ(d) = (q_d, χ_d, T_d)` | rephrased, **semantics changed** | AP report D1 (records with disjunctive alternatives); AP §6 `Met_n(r) ⇔ r resolved with S=∅` | `Met_n(d)` is a primitive judgment on `χ_d`; there is no clause making a route's terminal resolution satisfy `d`; external `(i,σ)` typing dropped; `d[r:=r']` transfer replaced by `Routes_n(d)` ancestry closure (erratum E7) | definition |
| one-shot occurrences, no re-add | new statement | AP allows withdrawal "with grounds"; nothing on re-adding | withdrawn `d` cannot return as the same occurrence | Lean: `pre_intro`, `add_of_mem_pre` |
| route extinction (Lemma 3) | new; **repaired by proof pass** | — | qualified by `n > intro d` (fixture B) | Lean: `routes_empty_persistent`; falsity of the unqualified form: `fixB_routes` |
| `⇝_n`, `Reach_n(m)` | inherited | AP §7 `Reach_n(X)` closure under `⇒`; BLK Idle/Front | Idle dropped (as AP-final did) | Lean: `waits`, `Reach`, `mem_reach_of_waits` |
| `Work_n(m)` | rename of `Front_n(m)` | AP §7/§8, AP-final "`Front_n = {unblocked} ∪ {on a ⇒-cycle}`" | same object modulo the `Met` change above; the synthesis records the rename | Lean: `Work` |
| `o_n(m)`, `Ω_N(m)` | inherited exactly | AP §8 `o_n(m) = 1[Front_n(m) ≠ ∅]`; AP report: "fractional o_n was dead weight" | — | Lean: `opp`, `Omega` |
| `a_n(m)`, unit budget | **changed grain** | AP §8: budget `Σ_q a_n(q) ≤ 1` on claims, matter credit by max; AP-final E4 relies on that for overlapping matters | budget on matters `Σ_{m∈M_n} a_n(m) ≤ 1`; stricter under nested/joint matters; not used by any theorem (erratum E8) | — |
| Req 11 non-starvation | inherited from AP-final | AP-final §D matter-only; AP report D3 had claim *and* matter grain, superseded the same day | matter grain only | Lean: `NonStarving` (hypothesis) |
| feasibility witness (Lemma 4) | specialized | SR §B/§D: any positive summable schedule, floor `W1`, atomic LRS (SR8) | fixed `w_j = 2^{-j-1}` by birth order, called "only a feasibility witness"; SR's floor and atomic results not restated | paper |
| Req 12 reach gate | **weakening of AP's Discipline, mislabelled new** | AP §6 Discipline: "A dependency record may be created in `e_n` only on a claim in `Front_n`, on a root opened in `e_n`, or on a successor opened in `e_n` of a claim in `Front_n`" against "keeping one requirement always pending"; AP-final C11 "pipelined blockers" | AP gates on `q ∈ Front_n`, which implies Req 12 (`q ∈ Reach_n(m) ∩ Front_n ⊆ Work_n(m)`); Req 12 additionally allows adding to a non-frontier issue when every reaching matter has other work. Synthesis §Scope cites only the "ownership-only gate" (erratum E5) | Lean: `no_rewire` (field); necessity: `fixA_*` |

## 5. Theorem family

| Current item | Status | Nearest prior | Exact change | Proof status |
|---|---|---|---|---|
| Persistent-Wait (Thm 2) | **new**, strengthened conclusion | AP §7 Lemma (one-position sink characterization); AP Theorems "External waiting" ("if `Ω_N(m)` is bounded, the claims ... cite finitely many requirements and one of them is never met"); BLK Actionability Theorem | a *fixed* `d` eventually permanently in `NoRoute_n(m)`, via stabilization; from Req 12 instead of AP's Discipline | **Lean**: `IssueTrace.persistent_wait` |
| wait responsiveness | consolidated | BLK dependency adequacy; AP §9 input coverage; proof pass: `External(d)` carried no logical weight | one liveness assumption over `NoRoute` | assumption (`WaitResponsive`) |
| Persistent Opportunity (Thm 3) | rephrased | AP corollary (coverage ⇒ `Ω_N(m) → ∞`) | contrapositive of Thm 2 | **Lean**: `persistent_opportunity` |
| No Structural Abandonment (Thm 4) | **new form** | AP §F chain; CSP §129; ACS §B "starvation gap" | disjunctive statement is new | **Lean**: `no_structural_abandonment` |
| Lemma 5 (every issue has a matter) | inherited | AP-final B1 | not used by any theorem | not formalized |

## 6. Non-supersession map

| Body of work | Where it sits relative to Normative Continuity | What NC does not do |
|---|---|---|
| **Proper Exercise** (LE `PROPER_EXERCISE.md`: E2 no jurisdictional self-ratification; THEOREM_MAP P5 "no generic no-escalation theorem") | downstream consumer of the standing layer: it asks whether grounded authority is *properly exercised* (`Cap`, `Reach(L)`) | NC has no capability notion; Grounded Replay gives ancestry, not proper exercise; nothing here bears on P5 |
| **Checker / trace-agreement / realization** (LE §4 simulation, THEOREM_MAP 12–14; CIS `ServiceCertificate`/`MayClose`; TC "no self-grounding is a theorem, not an axiom") | the layer that says a concrete run follows the represented semantics | NC is a specification over an already-extracted record; it has no `Check`, no extraction, no certificate; its eight judgments are parameters exactly as LE's `Valid` is |
| **Legitimate Improvement** (LI Theorem C; evidence / uptake-regret / answerability decomposition) | substantive layer above NC's service guarantee | NC ends at "unbounded attention"; the arrow from attention to a useful disposition is LI's, and NC §10 says so |
| **Charge / liability realization** (ACS §I; SR §F "bridge blocked by direction"; `PRIORITIES.md` 33, 69) | a future realization theorem that a concrete bounded reasoner satisfies NC's requirements and adds finite-time guarantees | NC keeps liability out of its definitions (§Scope, consistent with SR §F) |
| **Service realization** (SR: positive floor `W1`, atomic LRS) | supplies non-starvation; strictly more than NC's Lemma 4 | NC's Lemma 4 is the `2^{-j-1}` witness only; SR's floor and atomic results stand unrestated |

## 7. Errata for the next revision of the source (not applied to the checkpoint)

- **E1 (fresh successors).** §Scope should say that Req 5 reverses LE A11/A5 (which withdrew the fresh-successor clause as refusing legitimate consolidation), with AP's reason ("cross-event merge is unnecessary: a dependency edge or a terminal disposition citing the existing claim expresses it explicitly"; acyclicity becomes a theorem). Reserved decision, §8.
- **E2 (same-batch open-and-resolve).** Req 4 reverses LE A17; the reason is AP D4 (`s_n(q)` would be undefined). Declare it.
- **E3 (Due timing).** `Due_n := Due(H_n, L_n)` shifts LE's same-position activation from the current event to `NewDue_{n+1}`; the "Acceptance convention" paragraph should say the descriptive half of LE A34 is replaced by the one-step shift, not preserved.
- **E4 (resolution gating).** LE A21/A22 gate resolution by `Permit`; the synthesis gates it by `κ_q` alone. Say that `Resolve_n` may, but need not, consult `Permit`.
- **E5 (no-rewiring provenance).** §Scope calls the no-rewiring rule "the newer part of the synthesis" and cites only the ownership-only gate. Its ancestor is AP §6 Discipline, which is *stronger*; Req 12 is a deliberate weakening that keeps the Persistent-Wait proof (this round's Lean proof confirms sufficiency). Cite it.
- **E6 (S1 scope).** LE S1 constrains grounds of every accepted edit; Req 1 only of changing edits. Harmless for Grounded Replay (proof pass §2a); declare or restore.
- **E7 (`Met` for internal routes).** AP had `Met_n(r) ⇔ r resolved terminally` for claim alternatives; the synthesis makes `Met` primitive and adds Req 10. Both are departures from the AP page; declare them.
- **E8 (attention grain).** The unit budget moved from claims (max-credited to matters) to matters. Not used by any theorem; declare, and note it is stricter under overlapping matters.
- **E9 (`\Ext` macro).** The `\newcommand{\Ext}` survives in the preamble with no use; remove.

## 8. Reserved to the author

Whether Req 5's successor freshness (`S ⊆ Q⁺_n`) supersedes LE A11 for the continuity line, or LE's "successors may be preexisting or shared" should be recovered by weakening Req 5 to `S ⊆ Q⁺_n ∪ O_{n+1}` with an explicit acyclicity requirement. The Persistent-Wait proof uses freshness at exactly one point — a fresh descendant of a route root or of `m` needs a parent that resolves in the same batch (`exists_parent_of_anc`) — and would need an extra hypothesis under the weaker rule. Recorded in `DECISIONS.md` *Awaiting the author*.
