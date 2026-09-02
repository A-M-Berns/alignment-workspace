# Theorems

Everything here rests on the **Defeat Principle**, which is settled (`DECISIONS.md`,
2026-09-03, maintainer ruling). This round ran under it as a hypothesis and predates
the ruling, so the statements below are no longer conditional on it. Where a statement
is proved in Lean it says so with the declaration name; everything else is
**paper-derived and test-supported**, which per `AGENTS.md` is not citable as proven.

## T1 Conservation

**Carrier layer — proved (prose, on the carriers round's algebra).** In a
defeat-disciplined trace the `disp` receipt is identically bottom and

    A = Sat_[n0,n](m) ∨ Settled_[n0,n](m) ∨ ⋁_{q ∈ C_n(m)} λ_n(m,q).

Proof: the carriers round's induction, with the disposition branch of `(TC)` replaced
by an identity-frame transfer. The join algebra is unchanged; what changes is that the
disposition summand is bottom, so the invariant loses a term rather than gaining one.
Mixed resolutions split componentwise and the identity-frame condition is checked per
component. `LOADS_AND_MASS.md` §1.

**Service layer — stated; checked on finite fixtures.** Open mass at `N` equals
initial minus answered minus settled; disposal contributes zero.
`MassLedger.conserved`, `test_disposal_contributes_zero_to_terminal_fates`,
`test_answer_and_settle_are_the_only_exits`. Exact rationals throughout.

## T2 Liveness — **Lean**

`persistent_wait`, `persistent_opportunity` and `no_structural_abandonment`
**re-elaborate unchanged** on the unified trace. This is verified by construction:
`DefeatTrace extends IssueTrace`, the whole `IssueTrace` layer is byte-identical to
the settled spine, and the module builds with all 976 jobs clean.

**Corollary — `DefeatTrace.live_nonempty_of_dispose_only`.** If the live issues of a
matter resolve only by disposal, `Live (n+1) m` is nonempty. Iterating gives
`Live n m ≠ ∅` for all `n ≥ n₀` on a trace whose resolutions over `m` are disposals
from `n₀` on. A matter cannot be made to disappear by defeating it repeatedly.

Supporting Lean results, all sorry-free and auditing to
`[propext, Classical.choice, Quot.sound]`:

| declaration | content |
| --- | --- |
| `DefeatTrace.fresh` | `StandingTrace.Fresh` is a theorem, not a postulate |
| `DefeatTrace.grounded_replay` | Grounded Replay from `anc`, by strong induction on birth position |
| `DefeatTrace.grounded_replay_live` | the live form |
| `DefeatTrace.anchor_grounded` | Requirement 2, with no cross-layer bridge |
| `DefeatTrace.met_persistent'` | Requirement 9 as a theorem of `met_def` |
| `DefeatTrace.dispose_not_met` | a disposed root meets nothing |
| `DefeatTrace.routes_survive_dispose` | **a prerequisite cannot be disposed away** |
| `DefeatTrace.no_grounding_in_batch` | the successor cannot ground the disposal |
| `DefeatTrace.self_grounding_not_excluded_by_priority` | **the finding**: priority does not refuse self-grounding |
| `DefeatTrace.no_self_grounding` | with the clause, none of the three cases passes |

### The strengthening of `persistent_wait`, stated and proved

> **A prerequisite cannot be disposed away.** If `t ∈ roots d` is disposed at `n`,
> then `Routes (n+1) d` is nonempty.

`Routes n d = (O n).filter (fun r => ∃ t ∈ roots d, anc t r)` is ancestry-closed;
`dispose_successor` supplies `q' ∈ Born n` with `t ∈ par q'`, hence `anc t q'`;
`resolution_continuity` puts `q' ∈ O (n+1)`. **No new axiom.** The dispatch asked
whether this holds or fails; it holds. `DefeatTrace.routes_survive_dispose`.

## T3 Reach

**Proved on the trace; composition gap stated.** For principal `P`, advisor `V`, and
corrective matters `Corr(P)`: if every disposal by `V` over a matter in `Corr(P)` is
separated with `P` among the standing-holders on the successor, then at every `n` each
`m ∈ Corr(P) ∩ M n` has a live issue on which `P` stands. `DEFEAT.md` §6.

**This preserves reach.** It does **not** preserve the ability to open a challenge —
a scorekeeping move, item 58 — nor the service of that issue, which is non-starvation
and a scheduling property. **The composition is not proved and not attempted.**

## T4 Persistence with defeat

**Proved under exogenous contest durations; endogeneity gap stated.** Let `τ(q')` be
the number of dates a disposal's successor stays open, and let contest charge `c` per
open successor per date enter the liability account as a budget drain. Then a norm has
a persistent affordable schedule iff

    liminf_t L_t(1) = 0    and    Σ_disposals τ(q') < ∞.

The first conjunct is the affordability round's criterion, unchanged. The second is
new and is exactly the condition that the total contest drain is finite; if it
diverges, the drain exhausts any lifetime budget however large, and no schedule
survives — which is why the budget does not appear in the criterion, matching the
shape of the fixed-era result.

**Bounded-delay refinement.** Successors inherit deadlines; D4 applies to *terminal*
claims (`μ̃`, the pushforward), not to the originally-owed ones; and uniform bounded
delay requires `τ(q') ≤ H` for every successor — a bound on each contest, not merely
on their sum.

**Stated, not proved:** `τ` is **policy-dependent**. A participant that contests
longer makes the trace less affordable, and the closed-loop version — where the
contest duration responds to the schedule — is **item 75** and is not attempted.
Checked as exogenous sequences only: `test_bounded_contest_is_summable`,
`test_unbounded_contest_diverges`.

## T5 Necessity of separation — finite fixture

**Drop D3 and the following is admitted.** `V` disposes `a` into `a1`, grounding the
disposal in `g_V`, an issue `V` itself opened; only `V` holds standing on `a1`; `V`
then disposes `a1` the same way, indefinitely. Mass is conserved at every step — T1
holds — the chain is contested by nobody and serviced by nobody, and the matter stays
formally live forever while nothing is ever owed to anyone who could act on it.

`test_single_author_walk_is_refused` shows D3 refuses it (`D3-uncontested` /
`D3-self-grounds`); removing the clause admits it.

**Relation to the two-books countermodel.** The affordability round's reasonwise
accounting countermodel has two books with increments `+1` and `-1`: the aggregate
account is identically zero and healthy, while each row is individually unbounded. The
structure here is the same failure at a different level. Conservation is an
**aggregate** law — total mass in equals total mass out — and an aggregate law is
blind to who holds the mass. The self-grounded disposal chain conserves perfectly
while concentrating the entire obligation in one participant's private cycle. In both
cases the repair is the same shape: a **per-row** condition (there, a liability floor
on each row; here, a standing-holder outside the resolver on each successor), and in
both cases the aggregate law alone is exactly what fails to imply it.

## What is not established

- T1 (service layer), T3, T4 and T5 are **paper-derived and test-supported**, not
  Lean. Only T2 and the §5 supporting results are kernel-checked.
- **D3 does not stop coalitions.** The two-participant alternating walk satisfies it
  and launders (`DEFEAT.md` §5). This is a live hole in the separation story, filed
  and not repaired.
- The `Auth` filter and the nonemptiness of grounds **do not** re-derive from
  ancestry and are carried as side conditions (`GROUNDS.md` §3).
- T4's contest charge has **no market realization**. It is a budget drain by
  stipulation; whether the traderized construction produces it is out of scope.
- Nothing here says a defeat-disciplined trace **exists** for any interesting
  practice, nor that any real reasoner produces one.
