# Single-run stabilization

Lean: `SeedStatics.lean` §10.  Fixtures: `stabilization_finite`, `stabilization_oscillation`,
`stabilization_summable`, `hysteresis`.

## 1. S1 — finite discovery class: eventually constant

**Theorem (`eventually_const_of_finite`).**  Let `ι` be finite, `R : ℕ → Finset ι`
monotone (the raised subset of the discovery class), `F : ℕ → Finset (Fin d)` monotone
(the settled coordinates), and `g` any function of the pair.  Then `g (R n) (F n)` is
eventually constant.  *Proof* (`eventually_const_of_monotone`): the card sum is a bounded
monotone natural sequence; at its supremum both finsets stop growing.

The forced interval of any `φ` is a function of (which items of `𝒟` have been raised,
which coordinates are settled): raising a warrant adds its rows, raising a defeater
lands on a port, settling pins a coordinate.  With `𝒟` finite, every element eventually
raised (so `R` is monotone and reaches `𝒟`) and settlement monotone, every `I_φ` is
eventually constant.  The fixture: two warrants and one defeater over
`{φ, ψ}`, schedule `w₁, w₂, d₁, settle ψ = 1, nothing`; intervals
`[1/2,1], [1/2,1], [0,1], [3/4,1], [3/4,1]`.

The statement quantifies over the raised *set*, not the order; order-dependence is the
selection problem of §4, which S1 excludes by taking strengths as given.

## 2. The oscillation witness — infinite discovery class

`𝒟 = {w_k, d_k : k ≥ 1}` with `w_k : P(φ) ≥ 1/2` a fresh warrant and `d_k` its undercut.
Schedule: `w_k` at date `2k − 1`, `d_k` at date `2k`.  Every element of `𝒟` is
eventually raised; settlement is empty.  `I_φ` is `[1/2, 1]` at odd dates and `[0, 1]` at
even dates, forever (`stabilization_oscillation`: eight dates, four reopenings of size
`1/2`).  No `I_φ` converges.

## 3. What restores convergence

Call a **reopening** at date `t` the amount by which an endpoint moves outward,
`max(0, lo_t − lo_{t+1})` for the lower endpoint.

**S2 (`tendsto_of_summable_drops`, Lean).**  A real sequence bounded above whose
downward steps are summable converges.  *Proof:* `l_n + D_n` with `D_n` the partial sum
of drops is monotone and bounded, hence convergent; `D_n` converges; subtract.  Applied
to `lo_t` (and to `−hi_t`): **summable reopenings give convergent intervals**.  The
fixture `stabilization_summable`: warrants `P(φ) ≥ 1/2 + 2^{−(k+1)}` raised and undercut
in turn with a floor `P(φ) ≥ 1/2` re-raised; drops `3/4, 1/8, 1/16, 1/32, 1/64, 1/128`,
sum `127/128`, lower endpoint `→ 1/2`.

Summability is sufficient, not necessary: a sequence can converge with non-summable
reopenings if narrowings cancel them (`lo_t = 1/2 ± 1/t`).  The exact condition is that
the endpoint sequences are Cauchy, which is not a condition on `𝒟`.  Of the prompt's
candidates: finitely many reopenings is the finite-`𝒟` case in disguise and gives
eventual monotonicity, hence convergence; bounded reopening *depth* (each warrant undercut
at most `k` times) does not help, since fresh warrants are the witness's mechanism, not
repeated undercuts of one; finite defeat chains do not help for the same reason.  What
the witness needs is an infinite supply of fresh warrants *of the same content* and their
undercuts; a discovery class with **finitely many distinct rows** (however many items)
is finite for the purposes of S1, since the forced bundle sees rows.

**Filed, not proved:** the restored version for a discovery class whose *row set* is
finite but whose item set is infinite (S1 applies once one notices the bundle is a
function of rows and defeated ports; the Lean statement takes `ι` finite and does not
make that reduction).

## 4. Hysteresis through strength selection

Selection rule modelled: an item has candidate strengths, weakest to strongest; on
arrival it adopts the **strongest candidate feasible against the current live bundle**.

`hysteresis`: one coordinate, `ρ` with lower-bound candidates `3/10, 6/10, 9/10`, `σ` with
upper-bound candidates `95/100, 8/10, 5/10`.

| order | `ρ` selects | `σ` selects | forced interval |
|---|---|---|---|
| `ρ` then `σ` | `9/10` | `19/20` | `[9/10, 19/20]` |
| `σ` then `ρ` | `3/10` | `1/2` | `[3/10, 1/2]` |

Same seed, same `W`, different order, disjoint forced regions.  Hysteresis occurs.

**The minimal reopening condition.**  Reopening a selection — re-running it against the
full docket when the docket changes — is *not* enough: both outcomes above are maximal
joint selections (neither component can be strengthened), so a reasoner that reopens and
re-maximises can land on either.  What kills the hysteresis is reopening **under a fixed
canonical rule on joint selections**: every joint candidate combination is re-run against
the whole docket and the choice is by a fixed order (the fixture maximises the interval
width; result `[9/10, 19/20]` regardless of arrival order).  So the condition is
*reopening plus a canonical joint rule*; reopening alone restores nothing.

**Bearing on the 2026-08-08 ruling** (as the prompt states it: mechanically filed
past-self charges burn).  A reopened selection is a charge against the reasoner's own
earlier selection.  If such charges burn when mechanically filed, a reasoner cannot
reopen its own selections from inside, and the hysteresis stands unless an external
challenger files.  The narrow exception the ruling would need: a strength selection is
**recomputed state, not a commitment** — re-selection under the canonical rule is not a
past-self charge and does not burn.  Filed as an outstanding maintainer action
(`REPORT.md`); not amended here.  The ruling itself was not found in `DECISIONS.md` on
`main` (`REPORT.md`, deviations).

The legal fixture reads the same phenomenon in the other direction: *stare decisis* is a
selection that must **not** be reopened (`FIXTURES.md` §4).
