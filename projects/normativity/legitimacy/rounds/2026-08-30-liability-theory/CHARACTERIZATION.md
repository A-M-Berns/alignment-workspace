# Characterization and necessity

## 1. Common compatibility is not necessary

Bounded liability can occur without a covered common mixture:

- the authority never trades because displayed prices already follow the schedule;
- total authority inventory is finite or absolutely summable;
- incompatible regions occur only finitely often;
- no opponent ever supplies the flow that realizes the dangerous inventory;
- compatibility exists only on the boundary (`theta=0`) but the realized ledger is
  nevertheless bounded.

These are exact logical counterexamples to necessity. They show that common covered
compatibility is a strong schedule-level certificate, not the definition of
affordability. Conversely, failure of the certificate is a vulnerability, not proof
that a particular run loses without bound.

## 2. A finite ex post algebraic iff—and its limit

There is a clean but deliberately modest characterization. Let `mathcal E` be a
family of payoff vectors on one fixed **finite** profile set and suppose every
`E in mathcal E` satisfies `E_i<=U` for one common finite `U`.

The following are equivalent:

1. `inf_{E in mathcal E,i} E_i> -infinity`;
2. there exists one full-support probability `mu` and finite `S` such that
   `mu dot E>=-S` for every `E in mathcal E`.

The forward direction uses any full-support `mu`: if `E_i>=-B`, then
`mu dot E>=-B`. The reverse takes `theta=min_i mu_i>0` and applies the Underwriting
Lemma. Thus the equivalence is mathematically sound. Full support matters in the
reverse direction, but is freely selectable in the forward direction once bounded
liability is already known.

This is an **ex post algebraic covered-potential characterization**, not a design
theorem. Its forward direction can select `mu` after knowing that liability is
bounded; `mu` need not be compatible with a region, predictable, or produced by an
authority policy. A **certified underwriting potential** is stronger: it is obtained
from public constraint/settlement geometry or by one adapted selector rule before the
payoff increment it underwrites. Only the certified form is an operational safety
certificate. The stronger geometry-derived converse is false in general because of
inactive and finite-exposure schedules.

## 3. Static taxonomy

| regime | certificate | conclusion |
| --- | --- | --- |
| pointwise/world inclusion | every profile in every region | zero liability |
| common covered | one `theta`-covered barycenter in all contributing regions | bounded nonzero liability |
| bounded exposure | finite/summable authority payoff magnitude | bounded by exposure, no compatibility needed |
| bounded switching debt | changing covered potentials with uniformly bounded running `D_n` | bounded by `(BSD)` |
| unsupported | none of the above known | no conclusion; PR50 supplies an unbounded witness |

These routes overlap. They classify available proofs, not moral kinds of authority.

## 4. Static versus diachronic necessity

For a projection authority required to enforce indefinitely against all admissible
opposition, common compatibility may be close to a robust necessity, but the workspace
does not prove such a converse. PR50's flow-quantified one-coordinate converse is
model-supported only. In multiple dimensions an iff would require quantifying over
market response, authority turnover, live-set nesting, and the Budgeter—not just
`K` and the settlement hull.

The theory should therefore state:

- static covered underwriting is sufficient and sharp given its abstract algebraic
  premises;
- the LP dual exactly characterizes failure of that certificate;
- bounded liability itself has additional accidental/exposure-bounded routes;
- general affordable revision remains a controlled-switching problem.
