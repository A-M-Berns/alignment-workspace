# Traderized enforcement

Whether an admissibility constraint on a bounded reasoner can be given operative
force by a distinguished trader that trades against violations of it, and what
that costs.

**Research verdict: the mechanism is real and its safety condition is sharp.**
Compiling a row presentation of an admissible region into one violation-weighted
trading strategy forces the displayed price into the region exactly, under an
exact market-maker contract, at every positive intensity. Under the algorithm's
actual contract it forces the price to within a computable modulus. Whether the
modified market is still inexploitable turns on one thing: whether the region
excludes a world the deductive process has not yet ruled out. If it does not,
enforcement is free and the criterion survives with its original bound. If it
does, an ordinary trader exploits, and the round exhibits it.

**Integration verdict: nothing is promoted, and no living interface is edited.**
The mechanism is orthogonal to `Due/Licensed/Loss`; the map from a normative
record to an admissible region does not exist and is filed as an item.

```sh
python3 tests/run.py     # 50 tests, exact rationals
```

| file | what it is |
|---|---|
| `SOURCE_AUDIT.md` | where `D` enters Logical Induction, what the market maker's contract is, what breaks and where — read against the paper source and the pinned formalization |
| `MODEL.md` | the objects, and which assumptions on the region the proofs consume |
| `ENFORCEMENT.md` | Theorems 1–6: the contract resolved, the enforcement inequality, exact enforcement, the modulus, and the two ways exactness fails |
| `FUNDING_AND_SAFETY.md` | the three funding quantities, the liability identity, the safety theorem, and how much converse survives |
| `DEDUCTION_SPECIAL_CASE.md` | deduction as a constraint source; presentation cost; the four equivalence relations, answered separately |
| `INTEGRATION_MAP.md` | objects touched and untouched, the four vocabulary collisions, and the boundaries with Legitimacy and Deference |
| `THEOREM_MAP.md` | every result with its evidence class, and the named future Lean port target |
| `PROSECUTION.md` | sixteen attacks; four land |

## The five statuses

**Exact enforcement:** proved under an exact contract, kernel-checked
(`le_pair_of_contract_zero`), and **false** under the algorithm's positive slack —
smallest counterexample `P = 1/3` against `K = [1/2, 3/4]` at slack `1/8`.

**Non-exploitation:** proved conditional on bounded enforcement liability, with
bound `1 + B`; unconditional for regions containing every still-plausible world.
The converse is a witness, not a theorem.

**Traderized deduction:** an addition, not a replacement. It supplies a
finite-date coherence guarantee a logical inductor does not have, at zero
plausible cost. It does not remove the deductive process from the criterion or
from the construction, and the equivalence is stated only against relations R2 and
R3 of `SOURCE_AUDIT.md` §4.

**Funding:** not the scarce resource. The framework caps no trader's losses, so
growing external credit is free; what is scarce is showing a loss in a world that
is still plausible. Intensity is a position size and is separated from funding by
a fixture in which the realised position is identical across three intensities
spanning two orders of magnitude.

**Legitimacy:** untouched, and the mechanism sharpens rather than answers it.
Operative force is cheap, whoever writes the rows sets the price, and the only
thing the market checks about a source is that it does not contradict what
deduction has settled.

## Provisional names

`enforcement trader`, `enforcement intensity`, `enforcement liability`,
`violation-proportional position`, `world-inclusive region`, `support-function
presentation`, `constraint-to-trade compiler`, `market-maker contract`,
`enforcement inequality`. None is identified with an existing workspace term; the
four live collisions are listed in `INTEGRATION_MAP.md` §3.

## Status

`test-supported` for the fixtures; `lean-proved` and **unregistered** for the four
inequalities in `lean/Workspace/Normativity/Contrib/TraderizedEnforcement.lean`;
`derived` for the safety theorem, which composes two source lemmas taken as
hypotheses. Nothing is registered in `CLAIMS.md`, and the round adds no living
specification note — the formulation is not stable enough for one.
