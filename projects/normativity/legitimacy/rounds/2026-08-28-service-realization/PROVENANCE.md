# Provenance

## Frozen inputs

**None imported.** This round does not touch frozen Legitimate Evolution, and a
test asserts by parsing that neither module names `replay`, `answer`, `Duties`
or `A1`. The subject is liveness and arrival; persistence is settled and was not
re-derived.

The three rounds below are cited and not imported.

## No external sources

Nothing fetched. The scheduling construction is elementary and is proved in the
document rather than imported.

## New names introduced

All provisional under `AGENTS.md` §6.

*adjudicative opportunity*, *service*, *service entitlement*, *positive share*,
*summable schedule*, *least-recently-served*, *positive floor* (W1), *service
realization*, *starvation debt*, *latent opportunity*, *represented opportunity*,
*qualitative coverage*, *fractional coverage*, *criticism coverage*, *opportunity
coverage*, *the coverage boundary observation*.

## What was computed rather than asserted

Every number in `SERVICE_REALIZATION.md` is produced by `src/cases.py` and
re-derived by the tests. Three claims most at risk of being asserted are each
checked directly: that the peak total service never exceeds the budget while
every challenge is served positively; that a fixed dovetailer starves a challenge
the adaptive rule does not, on an identical opportunity stream; and that the
starvation debt diverges while the service condition holds.

## A caveat the fixtures cannot remove

The service and coverage conditions are statements about divergence, and every
fixture is finite. The module's checks are therefore **proxies** -- opportunity
mass above a stated threshold with service or representation at or near zero --
and are named as proxies in the code and the document. `SR6` is the case that
makes this matter: a geometrically shrinking entitlement satisfies the finite
proxy for the service condition while destroying the mechanism that would
guarantee it, which is why `W1` is stated as the invariant rather than `S1`
alone.
