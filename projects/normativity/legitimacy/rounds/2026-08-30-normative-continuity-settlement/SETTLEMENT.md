# The settlement: what Normative Continuity's mathematics is, exactly

Verdict: **`NORMATIVE-CONTINUITY-MATH-SETTLED`.** Gloss: the structural mathematical
specification, its principal modeling choices, theorem dependencies, satisfiability,
and Lean theorem spine have been settled. This does not assert Coverage, Progress,
substantive normative correctness, Proper Exercise, or realization by a concrete
reasoner, and it does not call the legitimacy project settled.

The settled specification is revision 2 of `NORMATIVE_CONTINUITY.tex` in this directory
(digests in `ORIGIN.md`), descending from the `AGENT-CONSOLIDATED` checkpoint of
`../2026-08-29-normative-continuity-concordance/`, which is unchanged. Every decision
below is recorded in the revision at the requirement it touches; this file is the
argument for each.

Governing question at each point: does the structure preserve exactly the continuity
relation meant, or is it merely convenient for the proof?

## 1. Successor freshness — resolved: **A, fresh successors** (`S ⊆ Q⁺_n`)

**B, existing successors with static ancestry, is incoherent, not merely inconvenient.**
Let `q'` be born at `j`, and let `q` resolve into `q'` at `n > j`. With a static
relation `q → q'`, `m ⪯ q'` holds for every matter `m ⪯ q`, at every prefix. So
`Live_k(m) ∋ q'` for `j < k ≤ n`, before the resolution was written, and `o_k(m)`
(hence `Ω_N(m)`, hence non-starvation's antecedent) at those `k` changes when `e_n`
is appended. Opportunity would not be a function of `H_{k+1}`. An acyclicity premise
addresses graph cycles only and does nothing about this: the defect is retroactivity,
not circularity. Matter inheritance cannot be defined extensionally from static
ancestry without time-indexing the edge. So B fails the governing question outright.

**C, time-stamped edges `q →_n q'`,** is coherent: ancestry `m ⪯_k q'` = a chain whose
stamps are all `< k`; `Live_k(m)` uses `⪯_k`; ancestry is monotone in `k` and
prefix-determined. Acyclicity is automatic (a resolved issue never returns to `O`, and
every edge's source leaves `O` at the next prefix). The Persistent-Wait proof survives
because after the last opportunity no reachable issue resolves, so no new stamped edge
touches the reachable structure. Cost: every ancestry-dependent definition (`Live`,
`Routes`, `Reach`, the matter construction, Lemmas 2 and 3) becomes doubly
time-indexed.

**Expressivity.** The one thing C expresses that A does not is "resolve `q` *into* the
existing `q'`" — consolidation. Under A, the same situation is written as: `q` stays
outstanding with a prerequisite `d` whose route root is `q'`. Then `q' ∈ Reach_n(m)` for
every matter `m` of `q`, so `q'`'s readiness is `m`'s available work and non-starvation
credits `q'`'s service to `m`; when `q'` resolves, `Met(d)` is what the current rules
say about `χ_d`, and `q` can then resolve. Matter identity, attention and reach are all
preserved. What is *not* preserved is `q'` being counted as a live descendant of `m`
(`m ⪯ q'`) — which is exactly the retroactive claim B was wrong to make and C makes
prospectively. No theorem, fixture, or consumer in the workspace needs `q'` to be a
descendant rather than a route.

**Recommendation and reason.** Fresh successors. Succession represents diachronic
continuation of an entitlement into a fresh episode; relation to an existing issue is a
prerequisite/reference edge. This supersedes frozen LE A5/A11, whose objection (the
freshness clause "refuses ordinary consolidation into a claim already outstanding") is
answered: consolidation is expressed, by a route edge, with its accounting intact.
Time-stamped consolidation (C) is deferred until a consumer needs `q'` to *be* a
descendant; the hypothesis in the prompt is vindicated. Recorded at Requirement 5.

## 2. The other departures — resolved

**Same-batch opening and resolution: forbidden, deliberately.** `Res_n ⊆ O_n` and
`Q⁺_n ∩ O_n = ∅` make it impossible. Every judgment about `q` reads a prefix at which
`q` is outstanding, so `s_n(q)`, `Pre_n(q)`, `Ready_n(q)` are defined whenever
`Resolve_n(q;·)` is consulted; permitting a birth-batch resolution would need a
birth-state semantics for all three, and would let Requirement 3 be discharged by an
issue that exists at no prefix (`Q⁺_n` would contain it, `O_k` never would) — a silent
materialization loophole at the structural level. Supersedes LE A17. Recorded at
Requirement 4.

**Due timing: uniformly strict prefix.** A record in `e_n` first affects `Due` at
`n+1`. The only loss is one position; LE A34's asymmetry (an unauthorized act's own
occurrence activates a complaint at its own position) becomes activation at `n+1`, and
the descriptive/normative split disappears from the interface. Recorded at the
acceptance convention.

**Resolution gating: `Resolve` is sufficient alone.** A second `Permit` gate does no
structural work: no theorem reads it (Persistent-Wait reads only `Ready`), and a
constitution that wants permission checked at resolution can have `κ_q`'s acceptance
read `L_n`. Supersedes LE A21. Recorded at the resolution judgment.

**Scope of standing grounds: constrained only for records that change standing.** A
record that adds nothing and removes nothing creates no node of any authorization tree;
constraining its grounds (LE S1 did) has no structural content. Recorded at
Requirement 1.

## 3. Matters — the paper construction realizes the Lean abstraction

`IssueTraceCore.mattersOf Desig` in Lean is the paper's `M_n`: `M_0 = ∅`,
`M_{n+1} = M_n ∪ {q ∈ Q⁺_n : par q = ∅} ∪ Desig_n`. With the paper's side condition
`Desig_n ⊆ O_n ∪ Q⁺_n` (the only hypothesis needed), `mattersOf_mono` and
`mattersOf_prior` are proved, and `IssueTraceCore.toIssueTrace` builds the abstract
`IssueTrace`, so every theorem applies to the paper's matters. `mem_mattersOf_succ`
is prospective matterhood; `mattersOf_not_mem_of_lt` is no retroactive matterhood;
`anc_of_parent` / `mem_live_succ_of_parent` are merge and split; `Live` is the paper's
definition verbatim. **No extra property was needed**: the two abstract fields are
exactly what the construction gives and exactly what the theorems consume. The theorem
stays generic over abstract `M` with the realization lemma, as expected; the paper now
carries the same two facts as Lemma "matter bookkeeping".

## 4. Joint satisfiability

`src/settled_model.py` checks every requirement of revision 2 at once (standing with
fresh occurrences, anchors, Due rising edges with compatibility, issue layer, unit
matter-grain budget with positive shares, reach gate) and runs a witness trace `W`
that exercises: standing gain (`r1`, `r2`) and loss (`g0` repealed at 2) with authorized
grounds; an issue (`a`, anchored to `P`) staying live and later resolving under `P`
after `P` lost standing; `Due` rising twice for the same pair with a fresh issue each
time; a co-opened route root; withdrawal of `d0` and reintroduction of a semantically
identical `d1` as a fresh occurrence; route extinction (`t1` resolves terminally);
reach-gated additions that pass because the reaching matter has work; split and merge
(`v → {v1, v2}`); designation of a descendant as its own matter (`t1`) overlapping
its ancestor's matter (`t`), with the budget respected. No hidden totality assumption
beyond the compatibility condition was needed. In Lean, `Fixtures.fixE_issueTrace`
inhabits the full issue-trace specification and `shareAttention_sum_le_one` /
`shareAttention_nonStarving` are the attention witness for any injective index and any
number of matters over time.

## 5. Dependencies after settlement — unchanged

Persistent-Wait uses Requirements 4, 5, 7, 8, 9, 10, 12 and bookkeeping; Persistent
Opportunity = Persistent-Wait + wait responsiveness (`persistent_opportunity'` from the
primitive form); No Structural Abandonment = Persistent Opportunity + non-starvation;
Grounded Replay from Requirement 1, connected to issues only by Requirement 2. No
settled choice changed a dependency, because none changed a definition a theorem reads.
Fixtures rerun: rotating prerequisite (Lean, both directions), co-opened route root
(Lean), waiting cycle (Lean), split/merge/designation (Python; Lean lemmas), protocol
losing standing while its issue is live (Python witness `W`).

## 6. Wait responsiveness — settled form

Primitive: `∀ d N0, ∃ n ≥ N0, d ∉ NoRoute_n(m)` ("no fixed prerequisite is a permanent
no-route wait"). It is the exact negation of Persistent-Wait's conclusion, so Persistent
Opportunity is literally the contrapositive. The "eventually `Met`" form is equivalent
(`noPermanentWait_of_waitResponsive`, `waitResponsive_of_noPermanentWait`) and names a
mechanism; it is kept as the sufficient-condition reading. What the theorem assumes is
the primitive; Coverage, inquiry and prerequisite hygiene are future sufficient
conditions. No `External(d)` classification.

## 7. Grounded Replay — settled form

Stated over admitted occurrences `Adm_n = G ∪ ⋃_{j<n} L_j^+`, with the live form as
corollary (`grounded_replay_admitted`, `grounded_replay_live`). `Adm` is a derived set;
no complication to the model. This is LE's theorem exactly, and "ancestry, not
permanence" is now the statement rather than a remark.

## 8. Theory membership versus theorem hypotheses

The revision's §Scope carries the table. In brief: normatively continuous evolution is
*defined* by Requirements 1–12 with the compatibility assumption; Requirements 2 (except
as the bridge), 3, 6 and the judgments `Permit`, `Due`, `Continue`, `Designate` are part
of the definition and used by no theorem; wait responsiveness is an assumption outside
the definition.

## 9. Red team against the settled choices

Each attack was tried against revision 2; none produced a violated theorem or an
inconsistent requirement set.

- *Successor sharing / merge / split.* A joint successor is live for both parents'
  matters (`anc_of_parent`); each matter is charged its own share; nothing double-counts
  because `o_n` is an indicator per matter.
- *Designation timing.* Designating `q ∈ O_n` that resolves terminally in `e_n` yields a
  matter born closed; NSA's first disjunct holds vacuously. Designating `q ∈ Q⁺_n`
  gives `β = n+1`, no retroactivity (`mattersOf_not_mem_of_lt`).
- *Standing repeal.* The anchored protocol keeps judging its issue; no theorem reads
  standing after opening. Witness `W` step 8.
- *Due timing.* A pair due, dropped, due again yields two issues; a falling edge closes
  nothing. Witness `W` prefixes 2, 4, 6.
- *Co-batch events.* Standing change and opening in one batch: the opening reads `L_n`,
  so the change cannot license it. Prerequisite withdrawal and resolution in one batch:
  readiness reads `Pre_n`, so the withdrawn prerequisite still counts — consistent.
- *Prerequisite churn on fresh issues.* Unrestricted, but a fresh issue joins a starving
  matter's reach only through a resolution (an opportunity) or as its own matter.
- *Route-root churn.* `T_d` is immutable; a new occurrence is gated.
- *`Met` transitions coinciding with withdrawals.* Both monotone; stabilization argument
  unaffected.
- *Attention across overlapping matters.* Shares sum below one for any finite `M_n`
  regardless of overlap (`shareAttention_sum_le_one`).
- *Empty and degenerate histories.* No issues: theorems vacuous, `M = ∅`. `G = ∅`:
  nothing ever stands, so compatibility forces `Due_0 = ∅` and no issue opens;
  consistent.
- *Requirement conflict search.* Requirements 2 and 3 conflict exactly when
  compatibility fails, which is why compatibility is an explicit assumption and not a
  theorem; Requirement 12 and Requirement 7 cannot conflict because 12 restricts only
  `Pre⁺`, which 7 leaves free; Requirement 5 and Lemma 2 cannot conflict because 5 is
  what makes Lemma 2 true. No pair of requirements constrains the same record
  incompatibly.

## What this settlement does not do

It does not derive wait responsiveness or non-starvation from anything; it does not
realize the eight judgments; it does not touch Coverage, Progress, Proper Exercise, the
checker layer, or charge/liability. The next reason to reopen this layer is a downstream
consumer exposing a concrete missing capability — the one candidate identified here is
time-stamped consolidation (§1, model C), if a consumer ever needs an existing issue to
*be* a descendant rather than a route.
