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

`lift_rho(pi, game, prohibited)` is the reason-preserving variant: in addition it
replaces every move on a declared prohibited influence channel by silence, so the
principal's decision at the mediation point is a function of the declared reason view
only.  Trajectory reproduction is *not* its target; reason reproduction is.
"""


def lift(pi, game, subst=None):
    def lifted(h):
        s = h.state
        task, comm = pi(h)
        if subst is not None:
            comm = subst(comm)
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


def lift_rho(pi, game, subst):
    """`subst` maps each prohibited-channel move onto the declared channel for the same
    matter (or onto silence)."""
    return lift(pi, game, subst=subst)


def approve_all(h):
    s = h.state
    return ("approve" if s.pending is not None else None, False)


def decline_all(h):
    s = h.state
    return ("decline" if s.pending is not None else None, False)
