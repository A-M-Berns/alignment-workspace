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
Deps(X) = (ReceiptDeps(X), ClaimDeps(X))
ReceiptDeps(X) = ⋃_{e ∈ X} s_L(e)
ClaimDeps(X)   = ⋃_{e ∈ X} s_V(e)  minus  { t(e) : e ∈ X }
```

— every settled receipt the cited reasoning rests on, and the frontier of
revisable claims it still openly depends on, with internally supplied
targets closed off. Syntactic, computable, and exercised on a quantitative
fixture (`test_handoff.TestRightHandoff`): a content
`P(rain|front) ≥ 4/5` carried as ordinary `Atom` payload, with a reason
bearing on it from a station-log receipt under a frequency-inference schema,
a valid certified belief revision citing it, basis loss detected after the
applicability is withdrawn, and the manifest splitting
`({station-log}, {frontal-pattern, App(frequency-inference, c, 3)})`.

This is exactly the settled-versus-defeasible split the compiler needs the
waist to hand over; what the compiler does with it — joint semantics before
projection, nonemptiness, convexity, funding — remains the open right-side
program.

## What stays open on the right

Defining `B̂_n` (which record events bind a stance member); the joint
semantics of endorsed quantitative contents; compilation to a nonempty
closed convex credal set with an effective presentation (priority item 39);
the enforcement-liability certificate; and everything the traderized-force
interface already lists as its inputs. None of these requires a new
reason-state primitive; each consumes the exposures above.
