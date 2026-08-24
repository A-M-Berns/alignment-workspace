# Right-consumer contract: the frontier compilation `R → O` over the frozen waist

Status: **handoff note; unregistered**. This specifies what the frozen
reason-state interface and the record expose to a future operative compiler.
It does not build the compiler, and it claims nothing about fundability,
settlement safety, or credal geometry — priority item 39 is untouched.

## The central distinction

```text
arbitrary candidate stance B  ≠  record-accounted compiling stance B̂_n
```

Reason queries remain valid for every hypothetical `B` — that totality is
frozen. But the frontier design constraint, stated here and not yet a
theorem, is:

```text
arbitrary stance may be queried; only diary-bound stance may acquire operative force.
```

`B̂_n` is not defined here. Whatever its final definition, it is constrained
to stances whose adoption history is bound into the record — endorsements
entering through certified transitions — so that a compiler never gives
force to a free-floating marking. This is the transition-certificate layer's
purpose seen from the right.

## What the waist and record expose to the compiler

| Needed | Supplied by |
|---|---|
| endorsed content, including quantitative constraint contents | membership in `B̂_n`; payloads live inside `Atom` contents, endorsement stays qualitative (tested) |
| the historical stance/revision events behind an endorsement | record acknowledgment and transition events; certificates by move identity |
| exact cited reason occurrences | certificate `basis` |
| applicability dependencies | derived `ApplicabilityProvenance` — the `App` claims among cited constitutive sources |
| settled receipt dependencies versus revisable claim dependencies | the two-sorted **provenance manifest** below |
| license and authority lineage | certificate `license` plus record genealogy |
| basis-loss status | `TransitionLostBasis` over the frozen citation |
| open review and accountability state | the record's review liabilities and account DAG |

## The provenance manifest

For a cited occurrence set `X`:

```text
Deps(X) = (ReceiptDeps(X), DirectClaimDeps(X))
ReceiptDeps(X)     = ⋃_{e ∈ X} s_L(e)
DirectClaimDeps(X) = ⋃_{e ∈ X} s_V(e)
```

— every settled receipt the cited reasoning rests on, and every revisable
claim it directly depends on. Cited targets are deliberately **not**
subtracted. A cited occurrence targeting `v` exposes support for `v`; it
does not put `v` into any stance, and the ledger has no
support-implies-endorsement closure, so `v` remains a live stance
dependency of every cited occurrence that consumes it. The regression and
circular kill fixtures (`test_handoff.TestRightHandoff`) pin this:
`e₁ : {g} ⇝ v, e₂ : {v} ⇝ q` cited together still report `v` open, and a
citation circle `e₁ : {q} ⇝ p, e₂ : {p} ⇝ q` does not certify itself into
an empty frontier.

The conceptual lesson: **the notebook can expose support for a premise, but
it cannot certify that the premise was actually adopted. Discharging a
stance dependency requires record-side evidence of an accountable
endorsement transition, not merely another reason pointing at that
content.** A closed notion `OpenClaimDeps(X, N, B̂)` — direct dependencies
minus those discharged by certified diary-bound endorsements — is a
frontier-side open problem over the diary, deliberately not implemented in
the ledger.

The quantitative fixture exercises the manifest end to end: a content
`P(rain|front) ≥ 4/5` carried as ordinary `Atom` payload, a reason bearing
on it from a station-log receipt under a frequency-inference schema, a valid
certified belief revision citing it, basis loss detected after the
applicability is withdrawn, and the manifest splitting
`({station-log}, {frontal-pattern, App(frequency-inference, c, 3)})`.

This is the settled-versus-defeasible split the compiler needs the waist to
hand over; what the compiler does with it — dependency discharge against
the diary, joint semantics before projection, nonemptiness, convexity,
funding — remains the open right-side program.

## What stays open on the right

Defining `B̂_n` (which record events bind a stance member); the discharge
notion `OpenClaimDeps(X, N, B̂)` over the diary; the joint semantics of
endorsed quantitative contents; compilation to a nonempty closed convex
credal set with an effective presentation (priority item 39); the
enforcement-liability certificate; and everything the traderized-force
interface already lists as its inputs. None of these requires a new
reason-state primitive; each consumes the exposures above.
