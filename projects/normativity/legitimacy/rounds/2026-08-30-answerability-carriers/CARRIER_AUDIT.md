# Carrier audit

## Structural substrate

Settled Continuity has immutable issue occurrences (q), one birth batch per issue,
outstanding sets (O_n), resolutions (q\overset g\Longrightarrow_n S), and finite fresh
successor sets (S\subseteq Born_n). A fresh child may have several parents, all of which
resolve in its birth batch. The successor relation is acyclic and its reflexive-transitive
closure gives matter ancestry. A matter (m) is a root or designated issue; matterhood
persists. Its structural frontier is

\[
Live_n(m)=\{q\in O_n:m\preceq q\}.
\]

Exact evolution is (O_{n+1}=(O_n\setminus Res_n)\cup Born_n). Freshness and ancestry
make split children live for the parent's matter and a merge child live for every
parent's matter. Once `Live` is empty it stays empty.

`Continue_n(P;q',g)` says current rules accept the fresh child's initial state as a
continuation of all parents' current states. It permits an explicit reset and is not read
by the Lean theorem spine. `Resolve`, `Continue`, and `Met` are semantic oracles;
outstanding evolution, ancestry, `Live`, reach, and matter closure are structural.

## Three carrier candidates

Let semantic content range over a finite join-semilattice
((L,\vee,0,\leq)). Finite sets with union are the executable instance. Overlap is
allowed, while a missing component changes the join.

| candidate | split | merge | laundering test | verdict |
| --- | --- | --- | --- | --- |
| issue load `Load(q)` | needs several children to be assessed jointly; one issue may simultaneously descend from several matters | conflates matter-relative inherited content unless loads are indexed by matter | catches a bogus child only with an external parent-to-child comparison | insufficient alone |
| matter burden `Burden(m)` | states what persists but not which child carries which part | retains identity across merges | a matter can remain live through a successor carrying none of its burden | insufficient alone |
| matter-indexed carrier frontier | evaluates the join of all current carrier loads | the same issue may carry a separate load for each ancestral matter | detects both missing content and bogus live carriers | required |

The selected semantics is therefore two-level:

* the matter indexes anchored diachronic identity;
* a distinguished issue frontier collectively realizes its current unresolved content.

For a load assignment \(\lambda_n(m,q)\in L\), define

\[
C_n(m)=\{q\in Live_n(m):\lambda_n(m,q)\neq0\}.
\tag{CF}
\]

and require

\[
A(m)=Sat_{\le n}(m)\vee Disp_{\le n}(m)
      \vee\bigvee_{q\in C_n(m)}\lambda_n(m,q).
\tag{Realize}
\]

`Live_n(m)` is too coarse. It can contain a procedural shell, an obsolete but
outstanding occurrence, or a branch that carries another component of a merged matter.
`Reach_n(m)` is coarser still because it includes prerequisite helpers. The carrier
frontier is not a second lifecycle: it is derived at each prefix from existing live
issues and the semantic load relation.

## No independent burden graph

The theory needs semantic content but not new burden *occurrences* with their own births,
parents, and closure law. Every finite burden graph used in the hostile examples embeds
as matter-indexed loads on existing issue successors: graph branching is successor-set
branching, graph merging is multiple parenthood, and terminal vertices are satisfaction
or disposition receipts. A separate graph would duplicate precisely the lifecycle that
Continuity already enforces.

The matter's anchored content need not be frozen prose. (A(m)) is a denotation or
equivalence class. Representations, decompositions, and ontologies may evolve under an
authenticated translation preserving that denotation. Newly incurred content is an
explicit anchored increment with its own origin time; it is not smuggled in as a
translation of old content. The conservation theorem may be applied to each anchored
slice. For an inherited slice, the invariant is accounted semantic denotation, not
surface vocabulary or one issue state.

## Countermodel verdicts

Issue-only semantics fails the joint-half split: neither child realizes the whole, yet
the pair does. Matter-only semantics accepts a structurally live successor whose load is
empty. Raw `Live`-frontier semantics treats helpers as carriers. Matter-indexed nonzero
load fixes all three with no new structural occurrence type.
