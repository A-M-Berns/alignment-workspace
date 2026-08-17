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

together with five declarations:

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

**The conformance guarantee.** At any price meeting the market maker's contract,

    Σ_j β_{t,j} · g_j(P_t)²  ≤  ε_t + C_t^{vol}      hence   g_j(P_t) ≤ δ_t .

Kernel-checked as `Workspace.Normativity.Contrib.TraderizedEnforcement.weighted_square_le_slack_add_volume`.

**A liability obligation, not a safety certificate.** Force does not certify that
the surrounding criterion survives. It emits a quantity the surrounding layer must
discharge: the enforcement position's cumulative value over the assessment worlds.
Two sufficient routes to bounding it, neither dominating and neither necessary:

    deficit route:  L_t(ω) ≤ Σ_j β_{t,j} g_j(P_t) d_j(ω)          no support hypothesis
    support route:  E_t(ω) ≥ −(1 − θ_t(ω)) · U_t / θ_t(ω)         U_t = the position's cube maximum gain

with `d_j(ω) = max(0, r_j − ⟪c_j,ω⟫)` the exclusion deficit and
`θ_t(ω) = max{ μ(ω) : μ ∈ C_t }` the support capacity of the **semantic** set.

**The preservation theorem the obligation feeds.** If the cumulative liability
over the assessment worlds is bounded by `B`, no efficiently computable trader
exploits the modified market, and every such trader's assessed net worth is at
most `1 + B`. Derived, composing two Logical Induction lemmas taken as
hypotheses; not formalized.

## What force does not determine

Whether the source is legitimate. Which credal states are semantically
admissible. Which worlds are live. Whether a world may be removed from support.
Settlement reports, timing or persistence. `Due`, `Licensed` or `Loss`. Learning
among licensed responses. Authorization or corrigibility.

A component asserting any of these on the strength of a conformance certificate
has misread this note.

## Boundaries of the guarantee

**Exactness is not promised, and is sometimes unavailable.** The conformance
tolerance can be made any positive rational; exact membership is available for
regions with an interior and for regions on a cube face — settlement pinning is
the easy case — and unavailable for a region strictly inside the open cube with
empty interior, which is where a coherence relation lands. The general condition
is conjectural.

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

The missing arrow — from a normative record to a semantic credal constraint or a
price-visible region — is `PRIORITIES.md` item 39 and is deliberately absent here.
