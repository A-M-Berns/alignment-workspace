# Conservative underwriting against the signed account

## 0. Three classes, and the inclusions

    conservative certificate      sum_t q_t sqrt(a_t) <= B
    sharp robust certificate      sum_t L_t(a_t) <= B, L_t the exact worst case
    signed-account affordability  V_N(omega) >= -B on the realized trajectory

    conservative  (  sharp robust  (  signed account .

The first inclusion is pointwise — `L_t(a) <= q_t sqrt(a)` at every `a`, since the
conservative charge assumes both the largest violation the modulus permits and the
deepest exclusion — and it is strict by `s_t = 1/t`, `m_t = t^4`, where the
conservative class is empty of persistent schedules and the sharp one contains the
constant allocation (`SHARP_PERSISTENCE.md` §3). The second is because the sharp
charge is the worst case over the market's response and the realized response need
not be worst; it is strict by §2 below, unboundedly.

The first two are **policy guarantees**: they are checkable before the market
responds, and an existence theorem must deliver one of them. The third is a
**realized-path fact** about a trajectory that occurred. The fixed-era construction
consumes only the third — it needs the account to have stayed above the floor — but
a scheduler can only aim at the first two.

## 1. The two guarantee classes

**Conservative affordability** is a property of the friction sequence alone: a
schedule is conservatively affordable when `sum_t q_t sqrt(a_t) <= B`, where the
charge is the worst case over the market's response and over the live worlds.

**Signed-account affordability** is a property of a realized trajectory: the
account `V_N(omega) = sum_t a_t d_t (d_t - s_t(omega))` stays above `-B` at every
horizon and every live world.

The first implies the second and is strictly stronger. The previous pass exhibited
only a two-date gap in the local cap. The separation is unbounded.

## 2. An infinite-horizon separation

**Countermodel S1.** One row, friction floored: `D_t = 3/4` and `m_t = 1` at every
date, so `q_t = 3/4` and `liminf q_t > 0`. By `PERSISTENT_AFFORDABILITY.md` P1 the
reason is **not conservatively affordable**: every conservatively safe schedule has
`sum_t a_t <= (B/q_0)^2 = (4B/3)^2`, bounded at every horizon.

Now let the market comply: the displayed price satisfies the row at every date, so
`d_t = 0`, while a live world continues to violate it with deficit `3/4`. Allocate
`a_t = 1` forever. Then

- the compiled position is `beta g(P_t) c = 0`, since `g = 0`;
- the account increment is `a_t d_t (d_t - s_t) = 0` at every date and every world;
- `V_N(omega) = 0` for all `N` and all `omega`, so SafeCert holds at `B = 0`;
- `A_N = N -> infinity`.

The conservative charge over the same trajectory is `sum_t q_t = 3N/4`, diverging.
`tests/test_persistence.py::SignedAccountBeatsTheConservativeCertificate` pins the
account at exactly zero, the charge at `6, 48, 384` for horizons `8, 64, 512`, and
the authority at `8, 64, 512`.

The mechanism is not subtle. **A satisfied row has a zero position, so it costs
nothing however deep its exclusion of the live worlds.** The conservative
certificate charges for a violation that never occurs, and it must, because it is a
bound over every market response.

So

    conservative affordability  (  signed-account affordability ,

and the containment is proper by an unbounded margin: the first caps lifetime
authority at a constant, the second permits linear growth on the same friction
sequence.

## 3. What the separation does and does not license

The separation is about **realized trajectories**, and that is the whole of its
content. Conservative affordability is a guarantee against every market response;
signed-account affordability on the trajectory that occurred is not a guarantee
about the trajectory that might have.

Three statements, kept apart.

**Robust safety is available in both classes.** Route B of
`CAPACITY_VS_SAFETY.md` — allocate `a_t` so that the date's worst-case charge is at
most the *realized* slack — is safe against every response, because a single date
cannot spend more than the slack it starts with. So a signed-account policy can be
robustly safe without being conservatively affordable.

**Persistence in the signed class is path-dependent.** Under Route B, a date on
which the market violates consumes slack; if the slack is exhausted, the policy
allocates zero thereafter and `A_N` stops. So the signed class buys persistence
*conditional on compliance*, where the conservative class buys it unconditionally.
S1 has one violating date costing `1/8` out of a budget the policy can absorb; a
run of violating dates would stall it.

**The classes answer different questions.** Conservative affordability asks whether
a norm can be enforced persistently no matter how the reasoner behaves.
Signed-account affordability asks whether the enforcement that actually happened
was underwritten. The composition theorem consumes the second; the existence theory
of `PERSISTENT_AFFORDABILITY.md` proves things about the first because it is the
only one a scheduler can guarantee in advance.

## 4. The drift reading

The signed class has a natural cumulative characterization and it is not a new
concept: for every world live at the horizon, the cumulative value stays above the
floor. Written as increments, the requirement is that the sequence

    a_t d_t ( d_t - s_t(omega) )

have partial sums bounded below, uniformly in `omega`. Positive dates are those
where the displayed defect exceeds the world's own misfit, negative dates those
where it falls short. The extremes are both free — `d = 0` and `d = s` are the two
roots — and the cost is maximal at `d = s/2`.

So the account is not a budget being spent; it is a **potential that the
trajectory's own compliance profile moves in both directions**, and the affordable
class is the one whose partial sums never cross the floor. There is no shorter
description of it, and this document deliberately does not name it.

What is missing for a usable existence theory in the signed class is a lower bound
on the drift that a scheduler can guarantee. Nothing here supplies one, and without
it the signed class is a description of outcomes rather than a criterion a policy
can be checked against in advance.

## 5. What this does not establish

That the containment is proper for *robust* persistence — S1's separation uses a
particular realized path, and Route B's persistence is conditional. That the signed
class admits any characterization in terms of the friction sequence alone; §2 shows
it cannot, since the same friction sequence supports both outcomes. That a
scheduler can detect in advance which regime it is in.
