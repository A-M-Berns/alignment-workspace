# Traderized realization, and what history alone secures

## 1. The mapping

| schematic object | traderized instance |
|---|---|
| normative control `u_t` | the added projection/authority position entering the aggregate |
| aggregation | sum of trader positions; the market maker prices the aggregate |
| assessment set `Assess(h_N)` | `PC(D_N)`, or `Omega_N^live` in the generalized lift |
| account `Acc(kappa)` | `W(E_{<=N})`, the enforcement position's cumulative value |
| safe class at `B` | uniformly bounded lifetime downside over every live world |
| `SafeCert ==> PreservedUptake` | bounded liability implies no efficiently computable trader exploits the modified market, and each has assessed net worth at most `1 + B` — a statement about the ordinary trader class |
| Uptake | the market maker's cumulative cap: `omega(sum_{i<=n} E_i) <= 1 + B_F` at every live world and date |
| normative defect `d_t` | `dist(P_t, K_t)` |
| assessment misfit `e_t(W)` | `dist(W|_{Phi_t}, K_t)` |
| Actionability margin | the force/friction inequality of §2 |
| joint feasibility `K_t != empty` | covered compatibility; its failure has the unsupported-authority certificate |
| per-reason accounting | the combined cap less the other reasons' floors, `U_j = 1 + B_F + sum_{k != j} B_k` |
| allocated service `a^r_t` | the enforcement multiplier `beta_{t,j}`, equivalently the promised tolerance; predictable, inside a per-date capacity box |
| realized force | `beta_{t,j} g_{t,j}(P_t)`, endogenous at the market maker's fixed point |

The last two rows are the ones worth pausing on, and they are two objects rather
than one. The scheduling variable is the multiplier, which is fixed before the
maker picks a price; what the multiplier buys is conformance precision,
`d_j <= sqrt((eps_t + M_t)/beta_j)`, and the position actually taken is decided at
the fixed point. A scheduler that services a reason weakly is one that promises it
a loose tolerance, not one that takes a small position — the source's adversarial
fixture has the realized position identical across `beta in {10, 100, 1000}`, which
is the same point from the other side.

The parsimony cap `K` of `SERVICE_TRANSFER.md` §4 bounds how much *authority* may
be allocated where nothing is owed. `SERVICE_FORCE_TYPING.md` carries the audit and
`LI_PROGRESS_FROM_SERVICE.md` the theorem the split makes available.

## 2. The score identity and the friction inequality

Let `K` be a closed convex region in the priced coordinates, `p` the displayed
state, `q = proj_K(p)`, `d = |q - p| = dist(p, K)`, and let the enforcement
position be `zeta = lambda (q - p)`. Write `Br_x(v) = sum_i (v_i - x_i)^2`, which
for a Boolean truth vector `x` is the Brier score and in general is the squared
Euclidean distance. Then

    dist(x, K)^2 = min_{v in K} Br_x(v)

**by definition**, not as a theorem: the two sides are the same expression. The
content is in what the position collects.

**The identity.** From `|x - p|^2 - |x - q|^2 = 2 <x - p, q - p> - |q - p|^2`,

    <zeta, x - p>  =  (lambda / 2) ( Br_x(p) - Br_x(q) + d^2 ) .

So the enforcement position's payoff in an assessment world is exactly half the
Brier improvement its own projection induces, plus half the squared normative
defect. The second term is the part the position collects for being *demanding* —
it is paid whether or not the world rewards the move — and the first is the part it
collects for being *right*. Both are exact, and the identity is checked over a
grid of states, worlds and intensities in `tests/test_force.py::ScoreIdentity`.

**The friction inequality.** With `x_K = proj_K(x)` and `e = dist(x, K)`,
`<q - p, x - q> = <q - p, x_K - q> + <q - p, x - x_K> >= -d e`, the first term
being nonnegative by the obtuse-angle property of the projection. Hence

    <zeta, x - p>  >=  lambda ( d^2 - d e ) ,

which is the local force/friction inequality the dispatch names. For a halfspace
region and an assessment world outside it, the inequality is an **equality** —
checked exactly — and the enforcement position's entire downside is `lambda d e`.
Liability is therefore bought by *assessment misfit*, not by defect: enforcing a
norm costs exactly what the live worlds' disagreement with the norm is worth.

Combining the two: `Br_x(p) - Br_x(q) >= d^2 - 2 d e`.

**This does not belong in the abstract definition.** The schematic theory uses
only the pairing `<zeta, v - p>` and never an inner product on the state space.
The Brier form appears exactly when the region is Euclidean-projected, which is a
choice of compiler, and a differently-built force mechanism reading only prices
would have a different identity and the same interface.

## 3. The core minimum as affordability with slack

Settlement-interface `P1` asks not for membership but for depth: the reference `q`
and the certified core minimum `theta` satisfy `q + theta (P - q) subseteq S`,
where `P` is the post-settlement simplex and `S` the endorsed region inside it.

**Consequence.** For every `x in P`, the point `q + theta (x - q)` lies in `S`, so

    dist(x, S)  <=  (1 - theta) |x - q|  <=  (1 - theta) diam(P) .

The misfit is bounded by the *core minimum*, uniformly, with no dependence on how
small `S` is. Precision may become arbitrarily tight without a precision-dependent
liability penalty: what is priced is the depth of the reference, not the tightness
of the region. Checked in `tests/test_force.py::CoreMinimumBoundsMisfit`, including
that a region the homothety misses is reported as such.

Fed into §2, this gives a per-round liability floor `-lambda_t d_t (1 - theta)
diam(P)`, which is the workspace's already-recorded conformance/liability trade

    delta_t >= (eps_t + C_t^vol) D_t / b_t

with `D_t` the live-world deficit supremum and `b_t` the per-date liability
allowance. So the core minimum is the mechanism by which `D_t` stays bounded as
the endorsement sharpens, and that is what "robust affordability with slack"
means here.

## 4. History, revision, and no-reset

Every quantity the affordability definition uses is a function of immutable
history: the claim measures are computed from settled record, the transport plan
is adapted, and the account is a supremum over an assessment set determined by the
settled record. Two consequences follow without any new machinery.

**Prior settlement pins and created exposures cannot be reset.** A settlement
event is never reopened, so the assessment set only shrinks, so a robust bound
established at `h_n` survives every extension (`SAFECERT.md`, T5). A successor
regime inherits the account rather than restarting it, and it does so because the
account is a supremum over a shrinking family — not because a rule forbids
resetting.

**Prior service claims cannot be reset**, for the same reason: `C^r_N` is a sum
over settled dates.

What legitimately changes is the reason's admissible region — the semantics. So
the two things to keep apart are:

- **historical persistence**, which is free, and covers claims, pins, exposures
  and the account; and
- **semantic transport**, which is not free, and covers only what is still owed.

**An exposure already created needs no transport.** Its account is evaluated
against the assessment set the settled record defines, and settlements are never
re-spoken in a new vocabulary — the settlement interface's `J3`. A historically
fixed settlement-contingent contract can simply remain in its original semantics,
and the migration cells that carry translated content live in the answerable
layer, where they are objectionable. Transport is needed for **live claims**: a
reason still owed service, whose defect must be recognizable after the ontology
moves.

## 5. Cross-era Actionability and deferral: one inequality, two provenances

Deferral transports owed service across time within one semantics. Era change
transports a live reason across evaluator succession or ontology revision. The
dispatch asks whether these are one mathematical problem.

**The inequality unifies.** Both need exactly `(T3)`: `d_t <= L d_s + eps`
whenever the plan sends claim mass at `t` to service at `s`, with `(T1)`–`(T2)`
unchanged — service delivered in the successor era is real service and is drawn
from the successor era's capacity, so the feasibility constraint reads across the
boundary without amendment. Theorem T3 applies verbatim to a plan whose support
crosses an era boundary.

**The provenance of the constants does not unify.** In the deferral case `L` and
`eps` are a claim about the *persistence of the defect* over the delay: the same
reason, the same coordinates, and a bound on how much the defect can decay while
the claim waits. In the era case the two defects are defects of different
representations of the reason, so `(T3)` is not even statable without a semantic
bridge fixing which successor coordinate the predecessor defect is compared
against. That bridge is faithfulness of the reason's re-representation, which is a
different obligation with a different respondent.

**Verdict: unify the interface, not the construction.** One transport object with
one stability inequality, and two distinct certificates discharging it. Forcing a
single construction would hide the fact that a scheduler can supply the first and
cannot supply the second.

## 6. What this section does not establish

The identities of §2 are checked on a rational halfspace region; the convex case
is derived by the projection property and is not machine-checked. The mapping
table cites the traderized statements by content; only the ones marked
`lean-proved` in the force-interface note are kernel-checked, and this round adds
no Lean. §4's claim that a settled exposure needs no transport is an argument from
the settlement interface's `J3` and no-claw-back, not a theorem proved here.
