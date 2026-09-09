"""The principal-mediated lift.

`lift(pi, game)` is a policy in the *same* physical game.  It runs `pi` and intercepts
every declared protected effect: where `pi` would execute `('raw', r)`, the lift executes
`('propose', r)` and, on the following step, `('gated', r)` — which fires iff the
principal's latch holds `r`, i.e. iff the principal approved in that step.  The task
component of `pi`'s move is passed through unchanged, so mediation costs the task nothing
unless the exterior is time-sensitive.  A declined effect is not re-proposed: the decline
continuation is `pi` with that effect forbidden.

This is effective repairability by interposition: the transform reads only `pi`'s moves
and the declared effect interface, needs no model of `pi`'s internals, and adds one
principal round-trip per declared effect.  It is exactly the constitutional gate with a
mediation option in place of refusal.

`normalize_provenance(pi, game, subst)` is the truthful-channel substitution: in
addition it replaces every move on a declared prohibited influence channel by the
authorized disclosure move for the same matter (`subst`), so the principal's decision at
the mediation point is a function of the declared reason view only.  It is *not*
reason-preserving: the raw trajectory's declared reason trace did not contain the
disclosure, and the transform assumes an authorized channel carrying the relevant
protected content exists (fixture K is where none does).

`lift_catchup(pi, game, catchup)` runs the catch-up continuation `catchup` after an
approved execution instead of continuing `pi` verbatim: joinability bounds the mediation
discrepancy of *this* lift, not of the verbatim one.
"""


def lift(pi, game, subst=None):
    def lifted(h):
        s = h.state
        task, comm = pi(h)
        if subst is not None:
            comm = subst(comm)
        if s.latch is not None:
            # agent-first ordering: approved last step, execute now
            return (task, ("gated", s.latch))
        if s.pending is not None:
            # our proposal from the previous step is on the table this step
            return (task, ("gated", s.pending))
        if comm is not None and comm[0] == "raw":
            r = comm[1]
            if r in s.refused:
                return (task, None)
            return (task, ("propose", r))
        return (task, comm)
    lifted.__name__ = "lift(%s)" % getattr(pi, "__name__", "pi")
    return lifted


def normalize_provenance(pi, game, subst):
    """`subst` maps each prohibited-channel move onto the authorized disclosure move for
    the same matter, or onto silence where none exists."""
    return lift(pi, game, subst=subst)


def lift_catchup(pi, game, catchup):
    """The mediated lift whose approve branch continues with `catchup(h)` from the step
    after an approved execution.  `catchup` is a history policy; it may read the mediated
    history, including the principal's decision, and not the exterior's future."""
    base = lift(pi, game)

    def lifted(h):
        executed = any(a[1] is not None and a[1][0] == "gated"
                       and (p[0] == "approve" or s.latch == a[1][1])
                       for (_, s, a, p, _) in h.steps)
        if executed:
            return catchup(h)
        return base(h)
    lifted.__name__ = "lift_catchup(%s)" % getattr(pi, "__name__", "pi")
    return lifted


def approve_all(h):
    s = h.state
    return ("approve" if s.pending is not None else None, False)


def decline_all(h):
    s = h.state
    return ("decline" if s.pending is not None else None, False)
