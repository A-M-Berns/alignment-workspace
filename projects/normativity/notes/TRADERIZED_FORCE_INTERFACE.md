# Traderized force interface

Status: **OPEN specification note**, provisional names throughout. The research
round behind it is
`../rounds/2026-08-16-traderized-enforcement/`, and nothing here is a registered
claim. For which of its statements are kernel-checked, read that round's
`PROOF_CLOSURE.md`; for the paper-facing theorem spine and the two remaining
formalization debts, `GENERALIZED_LI_PAPER_HANDOFF.md` beside this file.

This note exists so that a later component can answer *"I have an admissibility
constraint; how do I make it operatively affect a bounded reasoner?"* without
reading that round. It specifies the **force** layer only. It determines nothing
about whether the constraint is correct, legitimate, or semantically meaningful.

## What force consumes

A **price-space region** at date `t`, presented as finitely many rational rows

    K_t = { P ∈ [0,1]^{Φ_t} : ⟪c_j, P⟫ ≥ r_j,  j ∈ J_t } ,

together with six declarations:

| declaration | what it is | who supplies it |
|---|---|---|
| the row system | rational, computable at date `t` | constraint source |
| nonemptiness | `K_t ≠ ∅` inside the cube | feasibility adapter |
| priceability | each row is a functional of priced sentence values | constraint source |
| `ε_t` | the market maker's slack | the market |
| `C_t^{vol}` | a bound on the ordinary aggregate's realised `ℓ¹` position | the market |
| `δ_t` | the promised conformance tolerance | the force mechanism |

A region is **not** a semantics. If the source has a semantic credal constraint,
`K_t` is its projection; if it has only a price demand, force still applies and
the semantics is a separate lift. See
`../rounds/2026-08-16-traderized-enforcement/SEMANTIC_PROJECTION.md`.

## What force emits

**The compiled position.** Violations `g_j(P) = max(0, r_j − ⟪c_j,P⟫)`, intensities
`β_{t,j} = (ε_t + C_t^{vol}) / δ_t²`, and

    E_t(P) = Σ_j β_{t,j} · g_j(P) · c_j ,

an expressible feature and therefore a legal day-`t` trading strategy. It enters
the aggregate the market maker prices against; it does **not** modify the market
maker, which is why the maker's totality and every theorem about it survive.

**The conformance guarantee**, `lean-proved`. At any price meeting the market
maker's contract,

    Σ_j β_{t,j} · g_j(P_t)²  ≤  ε_t + C_t^{vol}      hence   g_j(P_t) ≤ δ_t .

Kernel-checked as `Workspace.Normativity.Contrib.TraderizedEnforcement.weighted_square_le_slack_add_volume`.

**A liability obligation, not a safety certificate.** Force does not certify that
the surrounding criterion survives. It emits a quantity the surrounding layer must
discharge: the enforcement position's cumulative value over the assessment worlds.
Two sufficient routes to bounding it, neither dominating and neither necessary:

    deficit route:  L_t(ω) ≤ Σ_j β_{t,j} g_j(P_t) d_j(ω)          no support hypothesis
    support route:  E_t(ω) ≥ −(1 − θ_t(ω)) · U_t / θ_t(ω)         U_t = the position's cube maximum gain

with `d_j(ω) = max(0, r_j − ⟪c_j,ω⟫)` the exclusion deficit and
`θ_t(ω) = max{ μ(ω) : μ ∈ C_t }` the support capacity of the **semantic** set. The assessment worlds are the generalized process `Ω_t^live`; ordinary deduction specializes them to `PC(D_t)`.

**The preservation theorem the obligation feeds.** If the cumulative liability
over the assessment worlds is bounded by `B`, no efficiently computable trader
exploits the modified market, and every such trader's assessed net worth is at
most `1 + B`.

**The generalized live-world Budgeter/TradingFirm lift it rests on is
`lean-proved`** — `AssessmentFirm.trading_firm_dominance` and
`no_efficient_trader_exploits`, against the pinned dependency's own types, under
hypotheses weaker than (L1)–(L3). What remains conditional is the modified market's
computability, a transcription obligation recorded in the round's `PROOF_CLOSURE.md`
§VII. The force layer supplies the liability bound and nothing else; it does **not**
independently supply a generalized Logical Induction criterion, and a caller reading a
conformance certificate as one has misread this note.

The compiler's legality as a source-side `Strategy n` is `lean-proved` too:
`EnforcementStrategy.enforcementStrategy` is the term, with `coefficientFeature_rank_le`,
`enforcementStrategy_support` and `coefficientFeature_continuous` its legality, and
`marketValueRat_enforcementStrategy` the identity saying the force algebra is about
it.

## What force does not determine

Whether the source is legitimate. Which credal states are semantically
admissible. Which worlds are live. Whether a world may be removed from support.
Settlement reports, timing or persistence. `Due`, `Licensed` or `Loss`. Learning
among licensed responses. Authorization or corrigibility.

A component asserting any of these on the strength of a conformance certificate
has misread this note.

## Boundaries of the guarantee

**Exact enforcement is not part of this API.** The stable guarantee is
conformance to a declared tolerance; the default compiler is the
violation-proportional one. What is known about exactness, at its earned levels:

| statement | evidence |
|---|---|
| exactness at zero slack against the violation-proportional compiler | `lean-proved` |
| interior-anchored exactness against a positive disturbance budget | `test-supported`, one and two dimensions only |
| impossibility for a one-sentence region strictly inside `(0,1)` | `derived` |
| cube-face settlement pinning enforced exactly | `witness`, one and two dimensions |
| `face-solidity` as the general condition | `conjecture` |

A caller wanting exactness is outside this interface and should read
`ENFORCEMENT.md` §5 rather than assume any of the above generalizes.

**A compiler that is both exact and safe is not known.** The interior-anchored
compiler achieves exactness and loses the nonnegativity property; the
violation-proportional compiler keeps it and does not achieve exactness.

**Conformance and liability trade against each other**, and the trade is now an
equation rather than a warning. Against a per-date liability allowance `b_t`,

    δ_t  ≥  (ε_t + C_t^{vol}) · D_t / b_t ,     D_t = sup over live ω of Σ_j d_j(ω).

Force is bought, not promised: the caller does not pick a tolerance and hope, it
learns which tolerances its remaining account affords. There is no intensity-free
ceiling; that claim was made and withdrawn.

**Force consumes a presentation, not just a set.** `(K_t, presentation)` is the
argument. Equivalent descriptions of the same admissible set do **not** in general
receive the same force or cost the same:

| operation | position, liability, charge |
|---|---|
| `k` duplicate rows | `× k` |
| rescaling by `λ` | `× λ²` |
| a redundant non-duplicate row | changes |

Rescaling is the one that is really a reparametrization — declare `λ·η` to ask for
actual conformance `η` and everything agrees — so it needs no normalization.
Duplication and redundancy are billed. A caller wanting cost to depend only on the
admissible set must deduplicate, weight, or minimize over presentations upstream;
this interface does not.

**"Meaningful" tolerance is scale-relative.** `δ ≤ 1` says nothing
presentation-independent. Use `δ_t ≤ α·V_max` with `V_max = r − Σ_i min(c_i, 0)`
the largest violation the row can attain in the cube.

## Verification pointers

- Objects and types: `../rounds/2026-08-16-traderized-enforcement/MODEL.md`
- Theorems and evidence classes: same round's `THEOREM_MAP.md`
- Conformance and exactness: `ENFORCEMENT.md`
- Liability and safety: `FUNDING_AND_SAFETY.md`
- Semantics and projection: `SEMANTIC_PROJECTION.md`
- The core-condition compilation: `CORE_CONDITION.md`
- Lean: `lean/Workspace/Normativity/Contrib/TraderizedEnforcement.lean`

## What a source must do to discharge the obligation

Producing a region is half of it. The source must also bound the cumulative
enforcement liability, or supply the quantities from which the force layer derives
a bound. For the settlement/core statics that motivate this work:

- **settlement and coherence rows are liability-free**, always, because their
  right-hand sides are minima over the assessed worlds;
- **endorsement rows carry `max(0, r − m_c)`** — how far the demand exceeds the
  worst assessed world — **independent of the declared core minimum**;
- settlement monotonicity makes that quantity non-increasing for a fixed
  endorsement under irreversible settlement, which is **helpful and neither
  necessary nor sufficient** — not sufficient because non-increasing is not
  summable, and not necessary because pressure or tolerance can compensate for a
  depth that rises;
- **finite gating is not enough**, and neither are per-endorsement finite caps:
  a source obeying both can drive the aggregate to infinity with fresh
  endorsements, one live at a time;
- what discharges it is a **finite global account** out of which force is
  purchased at `(ε_t + C_t^{vol})·D_t/δ_t` per date, with allocation checked
  at admission so that `Σ_e B_e ≤ B` holds rather than being hoped for.

**What force costs is a product of three factors**, and none of them is
privileged:

    q_t = (ε_t + C_t^{vol})·D_t / δ_t ,     the condition is   Σ_t q_t < ∞ .

Indefinite force stays affordable if the exclusion depth decays, **or** if the
ordinary aggregate pressure decays, **or** if the tolerance loosens. Only when
depth and pressure both stay above positive floors *and* the tolerance stays under
a ceiling does the account necessarily run out, and then after at most `B·δ̄/(cd)`
dates.

`D_t` is the **certified** aggregate `sup_{ω ∈ Ω_t^live} Σ_j d_{t,j}(ω)` — the
sharp supremum of the row sum, not the rowwise sum of per-row worst cases, which
is larger. Supply it as a `LiveDeficitCertificate`; a bound the caller asserts is
carried through marked unverified.

**At exhaustion the endorsement is quarantined and its deadline tolled**, which
is the API's default: force is withheld, nothing is spent, normative standing is
kept, and an answerability deadline does not count a failure the substrate
caused. Tolerance relaxation and refusal stay available on request. Weakening the
declared core minimum is not among them — the worst deficit `max(0, r − m_c)` has
no `θ` in it, so weakening the core buys nothing.

**The account is never replenished**, and is market-owned: one finite allowance
for the whole force channel, out of which `cap` carves per-endorsement budgets.
The bound a caller may quote is the capital the account was opened with. A new
constitutional era opens a new account with its own allocation.

`../rounds/2026-08-16-traderized-enforcement/NORMATIVE_SAFETY.md` carries the
account, the type comparison against `P2`, a safe trajectory whose bound is
constant across horizons, a forever-unvindicated trajectory funded within a
closed-form `17/2`, and a bounded-liability failure whose realized loss at one
followed world diverges.

The missing arrow — from a normative record to a semantic credal constraint or a
price-visible region, **together with its liability certificate** — is
`PRIORITIES.md` item 39 and is deliberately absent here.
