# Loads and mass — two layers, one rule

Two accounting layers already exist and were built for different jobs. The carriers
stack (`2026-08-30-answerability-carriers`) tracks **loads** in a join-semilattice with
satisfaction, disposition and transfer components. The service layer
(`2026-08-31-normative-affordability`, frozen) tracks numeric obligation **mass** with
two fates. The Defeat Principle is one rule that lands consistently on both.

> A `dispose` contributes **zero** to either terminal fate. It moves.

## 1. Carrier layer

`ANSWERABILITY_CONSERVATION.md` states the invariant

    A = Sat_[n0,n](m) ∨ Disp_[n0,n](m) ∨ ⋁_{q ∈ C_n(m)} λ_n(m,q)

with `Disp` the accumulated **disposition** receipts. Under the Defeat Principle the
disposition receipt is not a terminal exit at all, and the restatement is:

**Slice-wise Conservation, defeat-disciplined.** In a defeat-disciplined trace the
`disp` receipt is **identically bottom**, and

    A = Sat_[n0,n](m) ∨ Settled_[n0,n](m) ∨ ⋁_{q ∈ C_n(m)} λ_n(m,q).

A `dispose` sets the disposition component to bottom and **transfers** the disposed
component to the successor under an identity certificate — the identity frame, so the
transfer is exact and the SDT certificate's `L = 1`, `ε = 0`. What was a third terminal
fate becomes a transfer edge, and `Settled` takes the vacated slot: settlement is the
one non-satisfaction exit that genuinely removes content, because it is the one the
world performs rather than a participant.

**Mixed resolutions, componentwise.** A resolution may answer part of a slice and
dispose the rest. The carrier layer already handles this — the join-semilattice
splits — and the identity-frame condition is checked **per component**: the answered
component takes a satisfaction receipt and leaves; the disposed component takes an
identity certificate onto the successor. The failure mode the check catches is a
resolution whose receipts do not partition the load — an answered receipt for a
component that was in fact moved, which would double-count it.

Checked at the mass level by `test_mixed_resolution_components`; the semilattice half
is stated and not re-proved, since the carriers round proves the join algebra and this
round changes only which component is terminal.

## 2. Service layer

**The terminal claim measure.** Define `μ̃^r_N` as the pushforward of `μ^r_N` along
disposal chains: mass owed at a disposed issue is carried to the successor that
inherited it, iterated to the chain's end.

**Disposal is a claim-to-claim transport step with `L = 1`, `ε = 0`.** The successor
inherits the disposed issue's load exactly — that is `D2` — so the transport plan
`T(t,s)` restricted to a disposal edge is the identity on mass. It contributes nothing
to the semantic error, because nothing about the reason changed: the *grounds for
saying it is not owed* changed, which is a different object. Checked:
`test_transport_step_is_lossless`.

**F3 factors through it.** The fixed-era transport plan of F3 composes with the
disposal pushforward, and since the disposal step is `L = 1, ε = 0`, the composite's
constants are F3's own. This is why the frozen affordability files need no change.

**The contest residual.** Define

    κ^r_N  =  (mass in open successors of disposals)  /  C^r_N

and the F3 bound acquires one added term:

    E_{μ̃^r_N}[d]  ≤  (F3's bound)  +  D · κ^r_N

**This is a corollary of F3 plus conservation, and needs nothing more.** The argument:
conservation says the mass in open successors is exactly the mass that left the
disposed issues and has not since been answered or settled; the defect on those issues
is bounded by `D`; so their contribution to the terminal expectation is at most
`D · κ^r_N`, and the rest of the mass is F3's. No new hypothesis, no new transport
constant.

## 3. The rule, stated once

| resolution | carrier layer | service layer | contributes to a terminal fate |
| --- | --- | --- | --- |
| `answer` | satisfaction receipt | mass leaves to `answered` | **yes** |
| `settle s` | settlement receipt | mass leaves to `settled` | **yes** |
| `dispose G` | identity-frame transfer to successor; `disp` receipt bottom | mass moves along the disposal edge, `L=1, ε=0` | **no** |

`MassLedger.conserved()` checks `open == initial − answered − settled` after arbitrary
interleavings, in exact rationals. `MassLedger.dispose` refuses a successor-free
disposal with the same code the structural layer uses (`dispose-successor`), which is
the two layers agreeing on the one requirement the round added.

## 4. What is not touched

The transport constants on **answer** edges are item 76 and are untouched. Nothing in
`2026-08-31-normative-affordability` is edited; the frozen files are consumed as
hypotheses, and `κ^r_N` is defined on top of them rather than inside them.
