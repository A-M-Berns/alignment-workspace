# Continuity bridge

Status: exact dependency reconstruction and proposed realization layer; unregistered.

## 1. The existing consumer

The settled Continuity paper has eight prefix-dependent semantic judgments:
`Permit`, `Due`, `Resolve`, `Continue`, `Met`, `AddPre`, `DropPre`, and `Designate`.
All read the strict prefix. The Lean theorem spine erases most of them into trace data.

| component | exact dependencies | conclusion |
| --- | --- | --- |
| Grounded Replay | Requirement 1 only: exact standing update and prior standing `Auth` grounds for a standing change | finite authorization ancestry for every admitted rule |
| Persistent-Wait | Requirements 4, 5, 7, 8, 9, 10, 12; finite births/prerequisites; persistent/prior matter fields | live forever + bounded opportunity implies one fixed eventually permanent `NoRouteWait` |
| Persistent Opportunity | Persistent-Wait + Wait Responsiveness | live forever implies unbounded cumulative opportunity |
| No Structural Abandonment | Persistent Opportunity + non-starvation + matter-continuity lemma | eventual permanent empty `Live`, or unbounded attention |

Requirements 2, 3, 6 and the semantic meanings of `Permit`, `Due`, `Continue`, and
`Designate` are not read by these three issue theorems. `Resolve`, `AddPre`, and
`DropPre` enter only through accepted trace records. `Met` enters as a primitive
monotone oracle. Compatibility of Due with standing is a satisfiability condition, not
a theorem hypothesis.

```text
Permit + standing/Auth grounds ───────────────> Grounded Replay

Due rising edge ─Req 3─> fresh issue q ─root/designate─> matter m
                                │
                                ├─Resolve + fresh successors + Continue─> live lineage
                                └─prerequisites + issue ancestry routes─> Reach/Work/NoRouteWait

Req 4,5,7,8,9,10,12 ─────────────────────────> Persistent-Wait
Persistent-Wait + Wait Responsiveness ───────> Persistent Opportunity
Persistent Opportunity + NonStarvation ─────> No Structural Abandonment
```

### Exact derived objects

- `NewDue_n = Due_n \ Due_{n-1}` (and `Due_0` at zero). A later fall from `Due` does
  not close the issue. Reappearance creates a new rising edge.
- `O_{n+1}=(O_n\ResSet_n)∪Born_n`. Fresh issues cannot resolve in their birth batch.
- A successor is fresh in the parent's resolution batch. `Continue` checks its initial
  state; it is not needed by the theorem spine.
- A matter is a root/designated issue and all fresh successor descendants. Matterhood
  persists. If `Live_n(m)` becomes empty, it stays empty.
- A prerequisite occurrence is fresh and owned by one issue. Its route roots name
  existing or co-opened issues. `Routes_n(d)` consists of outstanding descendants of
  those roots. After introduction, an empty route set stays empty.
- `Reach_n(m)` closes live descendants under unmet-prerequisite issue routes.
- `Work_n(m)` is the ready reachable issues plus reachable waiting-cycle members.
- `NoRouteWait_n(m,d)` means an unmet active `d` on a reachable issue has no live
  procedural route.
- Wait Responsiveness says no fixed `d` remains such a wait forever; equivalently a
  permanent wait eventually becomes `Met`.
- NSA does not imply resolution, successful inquiry, satisfaction, correct attention,
  or eventual representation. Attention may be ineffective forever.

## 2. Handoff from Coverage

At a strict prefix, let

\[
(\texttt{maintainCoverage},\sigma)\in\operatorname{NewDue}_n.
\]

Requirement 3 opens a fresh issue \(q_\sigma\), whose root matter \(m_\sigma\) is the
ongoing entitlement to implementation of \(\sigma\). The contract is immutable data of
the issue anchor. `Due` may cease later without closing it.

The current semantics naturally allow a perpetual maintenance matter. It remains
outstanding until an accepted `Resolve` disposes it; NSA then says that a forever-live
matter receives unbounded attention under Wait Responsiveness and non-starvation. There
is no pathology in perpetual openness, because NSA is explicitly a liveness/service
disjunction rather than an eventual-closure theorem.

A physical sensor or interaction route \(R\) is not a Continuity successor and is not
`Routes_n(d)`. Routine \(R_1\to R_2\) changes an implementation witness only. A
substantive contract change uses `Resolve` and a fresh successor, with `Continue`
certifying state/contract translation. Successor freshness is therefore helpful, not a
problem.

The anchored protocol blocks retrospective scope reset only if \(\Gamma_\sigma\) is
part of its immutable adjudicative data and `Resolve` is semantically refined to reject
silent shrinkage. Structural Continuity alone permits an anchored protocol which accepts
the shrinkage.

## 3. Two route notions

Use these terms without abbreviation collision:

- **procedural issue route**: `Routes_n(d)`, an outstanding issue occurrence descended
  from a prerequisite root;
- **interaction inquiry route**: a certified Coverage witness \(R\) whose patch exposes
  and registers a target.

A procedural inquiry issue may have an active prerequisite \(d_T\) whose condition is
successful receipt/registration. An interaction inquiry route realizes how that
condition can be achieved. Existence of the interaction route does not put an issue in
`Routes_n(d_T)`, exercise it, or make `Met(d_T)` true.

For known inquiry obligations the existing lifecycle is enough:

\[
q\text{ waits on }d_T
\to q_{\rm inquiry}\in\operatorname{Routes}_n(d_T)
\to \text{exercise certified interaction route}
\to \text{receipt/registration}
\to \operatorname{Met}(d_T).
\]

Thus Coverage requires no second inquiry lifecycle system. The missing ingredients are
realization and fairness, not issue identity.

## 4. `Met` and Wait Responsiveness

Coverage can supply sufficient conditions for Wait Responsiveness only when every
persistent no-route wait of the coverage matter is classified. A useful bridge is:

\[
\begin{aligned}
&d\text{ permanently in }NoRouteWait(m_\sigma)\\
&\quad\Longrightarrow
\text{ repair/replace an interaction route, withdraw }d\text{ by authorized obsolescence,}
\text{ or register enough to make }Met(d).
\end{aligned}
\]

Coverage by itself supplies route quality, not this eventuality. It is orthogonal when a
procedural route exists but is never exercised.

The six demanded cases are classified as follows:

| case | correct `Met` reading |
| --- | --- |
| issue routes disappear after successful information | `Met(d)` becomes true before or with their terminal resolution |
| issue routes disappear because physical channels were destroyed | `Met(d)` stays false; this may create `NoRouteWait` after procedural routes also vanish |
| physical route replaced | no `Met` change merely from replacement |
| inquiry genuinely impossible | authorized withdrawal or contract disposition; impossibility alone is not `Met` |
| target ceases to be relevant | anchored applicability/disposition may justify `Met` or withdrawal, as specified by `χ_d` |
| concept deleted | no `Met` change unless the anchored semantic oracle recognizes a real disposition |

`Met` is intentionally coarse and need not be structurally modified. Proper Exercise
defines which events make the oracle true. The Continuity theorem consumes only its
persistence.

## 5. Zero-surgery result

Coverage supplies meanings and conformance conditions for `Due`, `Resolve`, `Continue`,
`Met`, prerequisite records, and route exercise. No new field is required by
`IssueTrace`, and no existing theorem statement needs alteration. What Continuity cannot
supply is resolution soundness, target relevance, interaction-route adequacy, route
exercise, registration, or progress.
