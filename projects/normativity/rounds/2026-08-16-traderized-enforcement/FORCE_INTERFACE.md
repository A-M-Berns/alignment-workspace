# The force interface, and where the other responsibilities go

The replacement question is narrow: can traderization take the role a specially
constrained market maker was meant to take? It is not whether traderization
replaces settlement, feasibility, answerability or legitimacy. Those are upstream
layers, and the point of this note is that they *stay* upstream and that saying
so costs the mechanism nothing.

## 1. What force must achieve, separated from how

Force is one contract, signed at each date, in quantities an outside party can
check.

> **Force contract.** Given a region `K_t` presented by a finite rational row
> system, a declared bound `M_t` on the ordinary aggregate's realised position,
> the market maker's slack `ε_t`, and a declared tolerance `δ_t`, the mechanism
> guarantees `g_j(P_t) ≤ δ_t` for every row `j`.

Five declarations in, one promise out. The declarations are what make the promise
attributable: a price outside tolerance is a failure of the implementation, or of
one of the four named assumptions, and which one is checkable after the fact.

**Which measure.** The row-violation vector is the primitive, because it is what
the compiler consumes and what the theorem bounds. It converts to the two
measures the existing machinery uses:

- **Supremum distance** — exactly `max_j g_j` when each row touches one
  coordinate, which is the shape settled facts produce. No constant.
- **Incoherence**, the functional the settlement interface's tolerance clause
  measures. By duality the incoherence *is* the largest row violation over signed
  weight vectors of total mass at most one, so enforcing a rational net of those
  rows enforces incoherence up to the net's resolution. On the interface's own
  displayed instance a net at denominator three recovers `4/15` exactly, and nets
  at denominators one and two report nothing at all — the resolution is what
  decides how much incoherence a mechanism can see, and it is a presentation
  choice, not a property of the mechanism.

So the contract is compatible with `T1`'s tolerance schedule, and `D3(a)` asks
for exactly a computable schedule with per-date conformance.

## 2. Two implementations, and one of them may not exist

```text
ForceContract
    ├── constrained market maker
    └── traderized compiler
```

**The constrained market maker is not known to be a total function.** Logical
Induction's market maker is: Brouwer supplies a fixed point for whatever
aggregate it is handed, and the search terminates. A market maker additionally
required to display a price inside `K_t` must satisfy two demands at once, and
nothing in the source construction supplies a joint solution.

It can fail. One priced sentence, `K = {P ≤ 1/2}`, an ordinary aggregate buying
one share flat. The contract forces `P = 1`; the region forbids it; every price
in the region leaves the aggregate a gain of at least `1/2`. **No price satisfies
both.** `test_contract.ConstrainedMakerNeedsAnExistenceTheorem` displays it.

The traderized compiler changes only the *input* to a function already proved
total, so it inherits existence, `lem:mm`, `lem:tfdom` and the shape of
`thm:lia`. At the same date it has a solution, and what it then owes is
conformance rather than membership: at intensity `β` against volume `M` the
displayed price sits `M/β` outside the region, which is a declared tolerance.

This is a proof-level asymmetry, not a preference. Whatever else is true, an
implementation that is total dominates one that is not known to be.

## 3. Which responsibilities are not the force mechanism's

| responsibility | source / constitution | feasibility adapter | force mechanism | answerability |
|---|---|---|---|---|
| construct `K_t` | ✓ | | | |
| legitimacy of the source | ✓ | | | |
| priceability — `K_t` stated in traded coordinates | ✓ | ✓ checks | | |
| effective presentation as rational rows | ✓ | ✓ checks | | |
| nonemptiness of `K_t` | | ✓ | | |
| quarantine when `K_t` is empty | | ✓ | | ✓ |
| persistence of a positive coefficient (`D1`) | ✓ | ✓ per date | | |
| exclusion depth `d_t(W)` | ✓ | ✓ measures | | |
| **choice of assessment set** | ✓ | | | **unresolved — see `PAPER_RECONCILIATION.md` §5** |
| exclusion depth in the liability bound | ✓ | | | ✓ charges |
| declared tolerance in the liability bound | | | ✓ | ✓ charges |
| declaring `M_t`, `ε_t`, intensities, `δ_t` | | | ✓ | |
| conformance to `δ_t` | | | ✓ | |
| breach attribution | | | contract output | ✓ |
| settlement reports, timing, persistence | ✓ | | | |
| learning among licensed responses | | | | separate |

Two rows carry the follow-up's correction.

**Nonemptiness is the adapter's, not the mechanism's.** A constrained market
maker cannot display a price in an empty region either, so "traderization does
not detect emptiness" is not a force-level objection — it is a statement about
which layer runs the check. The settlement interface already has that layer:
`NL-SI-A3` decides nonemptiness of the admissible-reference polytope by one
linear program and declares quarantine of operative force when it is empty. That
is exactly the precondition the compiler needs, and it is already built.

**Bounded liability is shared, and the split is not clean.** An earlier draft
put it wholly on the source, on the strength of a ceiling `M_t × d_t(W)` in which
the intensities cancelled. That ceiling is false — the counterexample is in
`FUNDING_AND_SAFETY.md` §4 — and the surviving bound
`(ε_t + M_t)·‖d_t(W)‖₁/δ_t` carries the mechanism's own declared tolerance.

So both layers contribute. The **source** sets the exclusion depth `d_t`; the
**mechanism** sets the tolerance `δ_t`, and a tighter promise raises the ceiling.
The two are traded against each other, and neither can discharge the obligation
alone. That is a worse factorization than the one this section originally
claimed, and it is the true one.

## 4. What this does to the attribution objection

The earlier reading was that `∑_j β_j g_j² ≤ ε_t + M_t` makes ordinary traders
partly responsible for a price sitting outside the region, which would put an
unaccountable third party inside the answerability system and break the
settlement interface's rule that attribution is total and exclusive.

That reading was wrong, and the declaration is why. `M_t` is not a cause the
mechanism suffers; it is an **assumption the mechanism names in advance and
promises conformance relative to**. The trading-firm construction already
computes a bound on its own realised volume from the belief history, so `M_t` is
available before the price is set. Three cases, and each has one respondent:

- realised volume within `M_t` and the price outside `δ_t` — the force
  implementation has failed its own promise;
- realised volume above `M_t` — a declared assumption is false, which is a
  detectable fact about the environment and is the adapter's to report;
- price within `δ_t` and the docket still unable to certify — the tolerance is
  sound and not *working*, which is the interface's existing `T1` distinction and
  is the book's or the source's.

That is the same three-way partition `NL-SI-T4` already runs on a certified
tolerance and a book-declared tighter one, with the force mechanism occupying the
engine's place. Nothing about a bounded disturbance class disturbs it.

## 5. The decomposition

```text
constraint source  →  validated admissible set  →  traderized force  →  ordinary bounded reasoner
```

with five theories, four of which this round does not touch:

**Constitution and legitimacy** — which sources may define admissible sets. The
round contributes only a separation: force is cheap and indifferent to content,
so being operative is no evidence of being legitimate.

**Feasibility** — whether a requested constraint is coherent, nonempty,
priceable, effectively presented, and sustainable. Already partly built
(`NL-SI-A2`, `NL-SI-A3`, `NL-SI-A5`); the round adds priceability as a
requirement it discovered rather than assumed.

**Force** — this round. One contract, one implementation that is total, an
explicit conformance modulus, and a resolved account of when exactness is and is
not available.

**Safety** — when applying force preserves the surrounding non-exploitation
guarantee. Bounded cumulative liability suffices; the surviving bound is
`∑_t (ε_t + M_t)·‖d_t(W)‖₁/δ_t`; and a region containing every live world is the
zero-depth case, not the boundary. **Which worlds the sum ranges over is open**,
and `PAPER_RECONCILIATION.md` §5 shows why it cannot be read off the constraint.

**Learning** — untouched, and in a different space.

**The obstruction, stated.** The decomposition survives the constructions with
one genuine cut across the layers: the safety theory's hypothesis is a property
of the *source's* trajectory, not of the force mechanism, so force cannot be
audited alone. A mechanism that conforms perfectly to a region whose exclusion
depth does not decay will preserve nothing. That is not a defect in the
factorization — it is where the factorization says the obligation sits — but it
does mean "the force layer is correct" is never by itself a safety claim.
