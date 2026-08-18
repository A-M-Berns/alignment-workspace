# Naturalized agency

**Verdict: usable existing interface, with a recorded negative that decides the
shape of this round's typing.** No Cartesian-frame formalism is imported; the
finite result stands without this bridge.

## 1. Is there already an object for the H-owned selector?

Yes, and it is `AgentInert` in
`lean/Workspace/Deference/Contrib/CartesianFrameBridge.lean:278` — whether the
outcome varies with the agent coordinate at all. It is a function of `outcome`
rather than a payload no formula reads, and it is invariant under homotopy
equivalence and under biextensional equivalence, so a frame cannot acquire or
lose it by adding behaviourally redundant choices.

That file already carries the delegation/simulation pair this round is about:
`delegated` and `simulated` agree on the nose once the agent coordinate is pinned
to the choice actually taken (`:362`), and are not biextensionally equivalent
(`:376`). It also carries the loss of future corrective agency in two shapes —
restriction and transfer — separated by whether the reachable worlds shrink
(`:552`, `:557`).

## 2. Is generic subagency too weak?

For this question, yes, and the file says why in its own words. `simRead not` — a
process executing the **negation** of the principal's disposition — is homotopy
equivalent to `delegated` (`:506`), so in that register varying with the
principal is not separated from deferring to it. What is separated is a process
supplying a fixed value that happens to coincide.

That is the reason this round does not type mediation as dependence.
`model.responds_to_the_choice` is the dependence predicate and `model.mediated`
is not it: the systematic overrider satisfies the first and fails the second, and
that separation is exhibited in the round's own types. What buys it is naming
**which argument of the quantity** the conduct writes, which the agent coordinate
of a frame does not record.

## 3. Does externalization suggest a sharper factorization?

It suggests the shape and does not supply it. `Commit^B` restricts the agent to a
subset — the foreclosing preparation, whose residual is a singleton.
`External^{/B}` moves a degree of freedom to the environment side while it is
still exercised — `transfer`, which is what a bypassing channel does to the
choice. The correspondence is close enough to be worth stating and is not a map:
the frames there are over a world type with no cell structure, so `A`'s
information at `t(n)` — the thing the whole efficacy quantifier is about — has no
image in them.

## 4. What theorem would discharge the primitive `H owns D`?

The finite model assumes the selector is the principal's. Discharging that would
be a theorem of roughly this shape:

> In the joint frame of advisor and principal over a world type recording the
> executed choice, the principal's choice coordinate is a factor that survives
> every world map distinguishing the executed choice at some environment state,
> and no advisor-side coordinate is such a factor.

The second half is the hard one, and `CartesianFrameBridge.lean`'s own negative
control N1 is why: being separated by a biextensional-equivalence invariant does
**not** certify that a separation is structural. A controller label moved into
the world type passes that test and is destroyed by the map that forgets the
label. The file's reply is robustness under world maps and it says explicitly
that this is a structural argument and not a proof that no label can pass it.

So a discharge needs a criterion that survives an adversary of that kind, and the
repository does not have one.

## 5. Disposition

Usable as an interface for the delegation/simulation separation and for the two
shapes of losing future agency. Not usable as a source of ownership, for the
reason in §2. The finite repair test does not depend on any of it.
