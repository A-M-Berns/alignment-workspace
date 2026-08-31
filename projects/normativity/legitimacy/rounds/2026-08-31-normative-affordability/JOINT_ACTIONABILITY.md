# Joint Actionability

## 0. The question, stated so it can be answered

Single-reason Actionability says the control the reason asks for buys a
recognizable advantage proportional to the recognized defect:

    g^r >= gamma_r d^r ,      g^r = inf_{v in K^r} <zeta^r, v - p> ,

where `p` is the displayed state, `zeta^r` the reason's certified position, and
`K^r` the reason's admissible region. The dispatch asks whether this composes.

It does not compose as stated, and the reason is sharper than "the controls
interfere": **the scoring set is reason-relative.** Once that is fixed the
composition is a two-line argument requiring neither convexity nor separability.

## 1. Countermodel J1 — interference with jointly satisfiable demands

Three response modes `x, y, z`, displayed state `p = (1/2, 1/2, 0)`, margin
`gamma = 1/4`. Reason 1 demands `v_y - v_x >= gamma` and takes the position
`zeta^1 = (-1/2, 1/2, 0)`. Reason 2 demands `v_z - v_y >= gamma` and takes
`zeta^2 = (0, -1/2, 1/2)`. Defect `d^r = 1/2` for both.

Each is individually actionable, `g^1 = 1/8 = gamma d^1` exactly. The regions are
jointly satisfiable — `v = (0, 1/4, 1/2)` lies in both. Yet the aggregated
position `zeta = zeta^1 + zeta^2 = (-1/2, 0, 1/2)`, read against reason 1's *own*
region, has

    inf_{v in K^1} <zeta, v - p>  =  -1/8  <  0  <  gamma d^1 .

Sequential composition gives the same displacement and the same number. Both
values are exact in `tests/test_joint.py::ChainInterference`.

Nothing here is a conflict of demands and nothing is nonlinear. Reason 1's region
constrains the gap `v_y - v_x` and says nothing about `v_z`; the aggregate moves
mass into `z`, and reason 1's own region is free to price `z` at zero. The defect
is in the *evaluation*, not in the control.

## 2. Theorem T4 — composition by common-region superposition

**Theorem T4.** Let reasons `r in R` present positions `zeta^r`, regions `K^r`,
defects `d^r >= 0` and margins `gamma_r > 0` with `g^r >= gamma_r d^r` at the
displayed state `p`. Let `K = intersect_r K^r` be nonempty and let
`zeta = sum_r w^r zeta^r` with `w^r >= 0`. Then

    G := inf_{v in K} <zeta, v - p>  >=  sum_r w^r g^r  >=  sum_r w^r gamma_r d^r .

*Proof.* `inf` is superadditive and positively homogeneous, so
`G >= sum_r w^r inf_{v in K} <zeta^r, v - p>`. Since `K subseteq K^r`, each such
infimum is at least `inf_{v in K^r} <zeta^r, v - p> = g^r`. `square`

The hypotheses actually used are: additivity of the aggregate position in the
individual positions; nonnegative weights; and `K` nonempty. Convexity,
separability, noninterference and superposition-as-an-extra-axiom are **not**
needed — superposition is already the definition of the aggregate, and the only
structural fact is that an infimum over a smaller set is larger. Of the
composition assumptions the dispatch lists, exactly one survives as load-bearing:
**positive homogeneity plus additivity of the aggregation map**, which is what
"the controls add" means.

On the J1 instance, `G = 1/2` against a floor of `1/4`, verified over a grid of
weight pairs.

**Corollary T4.1 (the weights are the service intensities).** The scaling `w^r`
that T4 quantifies over is the same object as the service intensity `w^r_t` in
Service Transfer. A capacity constraint on the aggregate — the control set `U_t`
is bounded, or the state must stay in the simplex — is a constraint on `w`, so
choosing how hard to press each reason *is* scheduling. Joint Actionability and
Service Transfer are two readings of one variable, not two mechanisms.

## 3. Countermodel J2 — the common region must be nonempty

Two reasons demanding `v_A >= 3/4` and `v_A <= 1/4`, at `p_A = 1/2`, with
positions `+1/2 e_A` and `-1/2 e_A`. Each is individually actionable with gain
`1/8 = gamma d`. Their intersection is empty, the aggregate position is exactly
zero, and each reason's gain at the aggregate is `0 < gamma d`. T4's conclusion is
not false here; it is unavailable, and correctly so.

This is the same instance as the covered-compatibility duality's §3 example, with
the demands read as positions rather than as rows. Nonemptiness of `K` is
therefore not a new hypothesis: it is synchronic covered compatibility, and its
failure already has an exact certificate in that document. **Joint Actionability
inherits its feasibility condition from the liability theory rather than adding
one.**

## 4. Countermodel J3 — aggregate Uptake does not give per-reason Progress

T4 delivers a bound on the *aggregate* gain. If Uptake is applied to the
aggregate — `limsup (sum_n G_n) / W_N^total <= 0` — then

    sum_n sum_r w^r_n gamma_r d^r_n  =  o(W_N^total) ,

and since every term is nonnegative, each reason's weighted defect is
`o(W_N^total)`. That is a statement about the *total* service mass, and Service
Transfer needs `o(W_N^r)`.

Take reason 1 served at intensity `1` on every date with zero defect, and reason
2 served at intensity `1/(n+1)` with defect `1` throughout. Reason 2's own service
diverges — it is persistently relevant — yet its contribution to the aggregate
density is `H_N / (N + H_N) -> 0`, while `E_{nu^2_N}[d^2] = 1` at every horizon.
Exact in `tests/test_joint.py::VanishingShare`.

Two repairs, and they are not equivalent:

- **Share persistence.** Assume `liminf W^r_N / W^total_N > 0` for each
  persistent reason. This is a scheduling obligation and it fails as soon as the
  number of live reasons grows without bound.
- **Per-reason Uptake.** Assume Uptake separately for each reason's own position
  against its own service measure. This carries no share obligation.

Per-reason Uptake is the right schematic assumption, and §5 says why it is not an
extra cost in the traderized realization.

## 5. What traderized LI gets for free, and what it does not

**Free: per-reason Uptake.** The Logical Induction criterion quantifies over
every efficiently computable trader individually; a reason's enforcement position
is one such trader, and its value is bounded against the market prices the whole
ensemble produced. No share condition and no aggregate normalization is involved,
so J3 does not arise.

**Free: a common scoring set.** In the traderized reading the quantity scored is
`W(E_{<=N})` for `W` ranging over the live assessment worlds — `PC(D_N)` in the
deductive case — which is the *same* set for every reason. J1's mechanism needs a
reason-relative scoring set, so it cannot be built there. What the reason's own
region `K^r` does in that setting is **select the position** (`zeta^r =
lambda_r (proj_{K^r} P - P)`), not score it.

**Free: additivity.** Positions enter the market as a sum, and the market maker
prices against the aggregate, so T4's one structural hypothesis is the
construction.

**Not free: nonemptiness of the intersection with the assessment set.** With a
common scoring set, T4's `K nonempty` becomes `PC(D_N) ∩ intersect_r K^r ≠ empty`
— and, once the coverage requirement is added, covered compatibility. Its failure
is J2, and it is the one thing that genuinely can go wrong.

**Not free: the reactive step.** The positions are computed at the price the
aggregate produced, which is a fixed point rather than an open-loop schedule.
Open-loop control — positions fixed before the joint state is known — reinstates
J1 even with a common scoring set, because the certified defect `d^r` was measured
at a state the aggregate then left. **Adaptedness is doing two jobs**: it keeps
round-`t` control out of round-`t` settlement, and it keeps Actionability
evaluated where the intervention actually landed.

## 6. Verdict on the proposed type

The dispatch proposes

    J_t(h) subseteq R_+^{R_t} x U_t x Q_t^{R_t} .

Drop the third coordinate. `q^r`, the reason-indexed object Uptake scores, is the
reason's own position `zeta^r`, which is already determined by the reason and the
state; carrying it separately invites the reason-relative scoring that J1
exploits. The minimal type is

    J_t(h) = { (w, u) in R_+^{R_t} x U_t : u = sum_r w^r zeta^r_t(h) } ,

standing beside one datum of the history, `K_t(h) = intersect_r K^r_t(h) ≠ empty`.

This has a payoff for §7 of `EXISTENCE_AND_DUALITY.md`: so defined, `J_t(h)` is
the image of a nonnegative orthant under a linear map, intersected with `U_t`.
If `U_t` is convex then `J_t(h)` is convex, and if `U_t` is a bounded polytope
then `J_t(h)` is one. The convexity the existence theory wants is not an extra
assumption; it is what the minimal type already is.

## 7. What this section does not establish

That `gamma_r` and `d^r` are correctly recognized — Answer-Mode Adequacy is
assumed throughout and nothing here bears on it. That the fixed point in §5
exists in a given engine; in LI it does by construction, and no general statement
is offered. J1 and J2 are two-reason instances and no claim is made that they
exhaust the failure modes at `|R| > 2`.
