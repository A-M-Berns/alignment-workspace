# Traderized enforcement

Whether an admissibility constraint on a bounded reasoner can be given operative
force by a distinguished trader that trades against violations of it, what that
costs, and whether it can take the role a specially constrained market maker was
meant to take.

Verdict: the semantic state is a credal set, the price-visible object is its
projection, and that projection loses information. Traderized force acts on the
projection and is installed as a living interface; the semantics is not.

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

**Safety verdict: bounded cumulative enforcement liability, with bound `1 + B`.**
That abstract theorem is the round's most robust result. The *sufficient
conditions* for bounding `B` are weaker than a previous pass claimed: the
per-date bound is `(ε_t + C_t)·‖d_t(W)‖₁/δ_t`, the intensity does **not** cancel,
and conformance and liability are traded against each other. A region excluding a
live world at every date can still be enforced forever and safely.

**Architectural verdict: two objects, not one.** The semantic state is a credal
set `C_t ⊆ Δ(Ω_t)`; the live worlds are read off it by support; the price-visible
object is its projection `K_t = π_t(C_t)`, and that projection **loses
information** — `Δ({00,11})` and its fibre saturation share a projection and have
different live worlds. So semantics and force are two channels for a reason about
information, not about mechanism convenience. Force consumes `K_t`; it does not
determine `C_t`.

**Paper verdict: the core generalized-LI paper is available conditional on one
named theorem** — the live-world TradingFirm lift, which is read off the source
proofs and not formalized. Everything else on the spine is derived, proved,
witnessed, or an explicitly downstream application.

```sh
python3 tests/run.py     # 158 tests, exact rationals
```

Four claims from earlier passes are withdrawn, each with its counterexample kept
as a regression in `tests/test_regressions.py`: an intensity-free liability
ceiling; an exactness impossibility stated for every empty-interior region; the
reading of a live world as one whose own price vector is admissible, with the
laundering conclusion that depended on it; and the reading of semantic
admissibility off a price region by preimage, with the deductive recovery that
depended on *that*.

| file | what it is |
|---|---|
| `SOURCE_AUDIT.md` | where `D` enters Logical Induction, the market maker's contract, what breaks and where, and why constraining the maker costs its totality |
| `MODEL.md` | the objects, and which assumptions on the region the proofs consume |
| `ENFORCEMENT.md` | Theorems 1–9: the contract resolved, the enforcement inequality, the modulus, and the exactness case split |
| `FORCE_INTERFACE.md` | the mechanism-neutral force contract, the two implementations, and the responsibility table |
| `CORE_CONDITION.md` | `P1`'s depth condition compiled to a trader, worked end to end |
| `FUNDING_AND_SAFETY.md` | the liability identity, the withdrawn ceiling and what replaced it, and the safety condition |
| `DEDUCTION_SPECIAL_CASE.md` | deduction as the calibration case; presentation cost; the four equivalence relations |
| `INTEGRATION_MAP.md` | objects touched and untouched, the four vocabulary collisions, Legitimacy and Deference |
| `THEOREM_MAP.md` | every result with its evidence class, and the named future Lean port target |
| `PAPER_RECONCILIATION.md` | credal semantics, support-live worlds, the live-world lift, deductive recovery, and the expectation/worldwise bridge |
| `PROSECUTION.md` | seventeen attacks; the worst of them is the round's own |

## The other verdicts

**Exact enforcement:** case-split by geometry, and the split is *not* interior
versus empty interior. Available for regions with an interior, and also for
regions sitting on a cube face — a settlement pinning a sentence to probability
one is enforced exactly by a constant trader. Unavailable for a region strictly
inside the open cube with empty interior, which is where a coherence relation
lands. The proved theorem is one-dimensional; the general condition
(*face-solidity*: nonempty interior relative to the smallest cube face containing
the region) is a conjecture delimited by witnesses on both sides.

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
stay upstream. `FORCE_INTERFACE.md` §3 assigns each one. Bounded liability is
**shared** — the source sets the exclusion depth, the mechanism sets the promised
tolerance, and the surviving bound carries both. Which worlds the bound is
assessed over is the open question.

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
`derived` for the safety theorem, the liability bound, the live-world lift, the
deductive recovery and the one-dimensional exactness theorem. Nothing is
registered in `CLAIMS.md`, and the round adds no living specification note —
`FORCE_INTERFACE.md` and `PAPER_RECONCILIATION.md` are proposals for one, not
one.
