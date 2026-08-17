# Traderized force interface

Status: **OPEN specification note**, provisional names throughout. The research
round behind it is
`../rounds/2026-08-16-traderized-enforcement/`, and nothing here is a registered
claim.

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

**This is conditional on the generalized live-world Budgeter/TradingFirm lift**,
which is `derived` and unformalized. The force layer supplies the liability
bound and nothing else; it does **not** independently supply a generalized
Logical Induction criterion, and a caller reading a conformance certificate as
one has misread this note.

The compiler's legality as a source-side `Strategy n` is likewise `derived` — the
embedding is exhibited in the source's feature grammar, not written as a term.

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

**Conformance and liability trade against each other.** A tighter `δ_t` needs a
larger intensity, which permits a larger position, which raises the liability
ceiling. There is no intensity-free ceiling; that claim was made and withdrawn.

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
- settlement monotonicity makes that quantity non-increasing, which is necessary
  and not sufficient;
- what remains is a **limit on cumulative net outflow** for the compiled
  enforcement position, which is a discipline the corpus already adopted for the
  same failure in another context.

`../rounds/2026-08-16-traderized-enforcement/NORMATIVE_SAFETY.md` carries the type
comparison against `P2`, a safe trajectory whose bound is constant across
horizons, and an unsafe one whose bound grows quadratically.

The missing arrow — from a normative record to a semantic credal constraint or a
price-visible region, **together with its liability certificate** — is
`PRIORITIES.md` item 39 and is deliberately absent here.
