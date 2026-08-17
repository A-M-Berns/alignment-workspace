# Traderized enforcement

Whether an admissibility constraint on a bounded reasoner can be given operative
force by a distinguished trader that trades against violations of it, what that
costs, and whether it can take the role a specially constrained market maker was
meant to take.

Verdict: traderization can carry the force layer, the constrained market maker is
retired from it, and the safety boundary is not world-inclusiveness.

**Force-story verdict: yes.** Compiling a row presentation into one trading
strategy gives a validated region operative force, with a certified conformance
tolerance derived from quantities available before the price is set. The
alternative implementation of the same contract — constraining the market maker
itself — is not known to be a total function, and there is a displayed date where
it demonstrably is not. That is a proof-level asymmetry, not a preference.

**Constrained-market-maker verdict: retired for the enforcement column, and
nothing else.** The settlement interface's reports, timing, persistence,
grounding, feasibility, breach stack and answerability are untouched and stay
upstream. What traderization replaces is the *mechanism* that was to make prices
respect a region.

**Safety verdict: bounded cumulative enforcement liability, and
world-inclusiveness is only its `B = 0` case.** The per-date ceiling is
`C_t · max_j d_j(W)` — ordinary volume times how deep the region excludes a live
world — and the intensities cancel out of it. A region excluding a live world at
*every* date can be enforced forever and safely, provided the depth decays
against the growth in volume.

```sh
python3 tests/run.py     # 99 tests, exact rationals
```

| file | what it is |
|---|---|
| `SOURCE_AUDIT.md` | where `D` enters Logical Induction, the market maker's contract, what breaks and where, and why constraining the maker costs its totality |
| `MODEL.md` | the objects, and which assumptions on the region the proofs consume |
| `ENFORCEMENT.md` | Theorems 1–9: the contract resolved, the enforcement inequality, the modulus, and the exactness fork resolved |
| `FORCE_INTERFACE.md` | the mechanism-neutral force contract, the two implementations, and the responsibility table |
| `CORE_CONDITION.md` | `P1`'s depth condition compiled to a trader, worked end to end |
| `FUNDING_AND_SAFETY.md` | the liability identity, the intensity-free ceiling, and the safety condition below world-inclusiveness |
| `DEDUCTION_SPECIAL_CASE.md` | deduction as the calibration case; presentation cost; the four equivalence relations |
| `INTEGRATION_MAP.md` | objects touched and untouched, the four vocabulary collisions, Legitimacy and Deference |
| `THEOREM_MAP.md` | every result with its evidence class, and the named future Lean port target |
| `PROSECUTION.md` | seventeen attacks; the worst of them is the round's own |

## The other verdicts

**Exact enforcement:** resolved into cases. Achievable by an interior-anchored
trader against a positive disturbance budget when the region has an interior;
**impossible for any continuous trader** when it does not — which covers every
settlement equality and every coherence polytope over a fragment with a
propositional relation. In that second case arbitrary finite tolerance is
available and exactness only as a limit.

**And exactness costs the safety property.** The compiler that achieves it does
not vanish on the region, so it holds positions where there is no violation, and
it loses in a plausible world at a price *inside* a world-inclusive region. The
two compilers are not ordered: one is safe and approximate, the other exact and
unsafe. Nothing here produces one that is both.

**Tolerance:** sufficient. The settlement interface's `T1` is built to consume a
declared tolerance schedule, and the round's modulus converts to the incoherence
functional that clause measures — verified against the interface's own displayed
instance, where a coefficient net at denominator three recovers `4/15` exactly
and coarser nets see none of it.

**Constitution boundary:** construction of `K_t`, legitimacy, priceability,
effective presentation, nonemptiness, persistence, and the depth of any exclusion
stay upstream. `FORCE_INTERFACE.md` §3 assigns each one. Bounded liability is the
*source's* obligation, because the mechanism cannot change the ceiling.

**Traderized deduction:** an addition, not a replacement — unchanged from the
first pass, and still false under relations R1 and R4 of `SOURCE_AUDIT.md` §4.

## Provisional names

`enforcement trader`, `enforcement intensity`, `enforcement liability`,
`violation-proportional position`, `interior-anchored position`, `exclusion
depth`, `world-inclusive region`, `support-function presentation`,
`constraint-to-trade compiler`, `market-maker contract`, `enforcement
inequality`, `force contract`, `force declaration`, `priceable endorsement`. None
is identified with an existing workspace term; the four live collisions are listed
in `INTEGRATION_MAP.md` §3.

## Status

`test-supported` for the fixtures; `lean-proved` and **unregistered** for the five
inequalities in `lean/Workspace/Normativity/Contrib/TraderizedEnforcement.lean`;
`derived` for the safety theorem and the exactness impossibility, which compose
source lemmas taken as hypotheses. Nothing is registered in `CLAIMS.md`, and the
round adds no living specification note — `FORCE_INTERFACE.md` is a proposal for
one, not one.
