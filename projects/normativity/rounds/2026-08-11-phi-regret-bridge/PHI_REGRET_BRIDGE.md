# Fixed-action Φ-regret bridge

## Verdict

**Repaired for the frozen item-30 environment.** The horizon-growing action
identity and arbitrary-comparator capture defects are removed by a fixed
eight-label alphabet and a finite declarative class of nine programs. This closes
item 29 positively and makes item 30 executable. It does not run an online
learner or establish an empirical regret rate.

The result is conditional on the declared frozen boundary: one occasion per
date; service window four; canonical responses; frozen arrivals and reasons;
guards evaluated on the actual strict prefix and candidate action; no suspension
or solvency coupling; no post-hoc affordability deletion; exact full-information
charge in `[0,2]`; the default policy suite; and the nine audited programs.

## Fixed representation

The theorem-facing action type is

```
Lambda = {
  merits-positive, merits-negative, default,
  decline-0, decline-1, decline-2, decline-3, decline-4
}.
```

These labels contain no date, occasion, case, obligation, ledger, or horizon
identity. For occasion `t`, `d_t : Lambda -> A_t` maps the two merits labels to
the schedule's positive and negative verdicts, maps `default` to scheduled
default, and maps `decline-k` to a decline tolling `k` dates. `d_t` derives the
ledger closure from the occasion: merits closes `d:<occasion>` by discharge,
default closes it procedurally, and decline leaves it open.

In the frozen environment `service_window = 4` and the positive and negative
verdicts are distinct. The eight decoded responses are therefore distinct and
are exactly the declared repository action set `A_t`. `encode_response` is the
inverse of `d_t` on that set. A response with a noncanonical ledger effect is
rejected rather than identified with a label. Thus bookkeeping multiplicity is
not hidden: it is excluded by the environment's canonical-response premise.

Consequently `|Lambda| = 8` at every occasion and horizon. No unavailable-label
padding is needed. A schedule with another service window or coincident merits
directions fails validation instead of acquiring a fake loss.

## The nine lawful programs

Each program is a `LawfulProgram` data record containing an identifier, one of
five rule kinds, an optional parity, and an optional toll amount. It contains no
callable.

| program | fixed mathematical rule | licensing ground |
|---|---|---|
| `identity` | leave every label unchanged | none |
| `repair_declines` | decline to the merits direction selected by a live separating interval | that interval |
| `repair_declines_even` | the preceding rule on even occasion indices | that interval |
| `repair_declines_odd` | the preceding rule on odd occasion indices | that interval |
| `toll_declines_1` | replace a decline by `decline-1` | live impediments |
| `toll_declines_2` | replace a decline by `decline-2` | live impediments |
| `toll_declines_4` | replace a decline by `decline-4` where the recorded allowance reaches four | live impediments |
| `default_declines` | replace an untolled decline by scheduled default | live ripeness |
| `withdraw_merits` | replace either merits direction by `decline-0` | live ripeness |

The certificate remains decisive. For example, `default_declines` is identity on
an already tolled decline because ripeness licenses the basis move but not
removal of the toll coordinate. `toll_declines_4` is identity when magnitude
support is unresolved. Every nonidentity program has an admitted finite witness.

## Factorization and preservation

Let `x_t` be the strict pre-action public context. The interpreter proposes a
target label and grounds from `(program, x_t, lambda)`. The existing certificate
checker then admits the decoded edit or returns the source label. This defines a
total closed map

```
Ftilde_phi^t(x_t) : Lambda -> Lambda.
```

For all nine programs, all eight labels, every occasion, and each declared
horizon `12, 24, 48, 96`, exact tests establish the commuting equation

```
d_t(Ftilde_phi^t(x_t)(lambda))
  = F_phi^t(x_t)(d_t(lambda)).
```

Define `elltilde_t(lambda) = ell_t(d_t(lambda))`. Then pointwise loss is equal by
definition, actual transcript loss is equal after encoding, and transformed loss
is equal by the commuting equation. Summation gives

```
R_T^Lambda(phi) = R_T^repo(phi).
```

The test suite recomputes both sides with exact rationals for every program at
all four horizons and also checks equality for a nondegenerate exact mixed-action
distribution. `PhiRegretBridge.regret_preserved` proves the generic finite-sum
argument in Lean from pointwise loss preservation and commutation.

## Causality and non-capture

Programs receive only `RuleContext`: occasion identifier/index, date, target,
threshold, and reason views containing kind, subject, liveness, interval bounds,
or impediment allowance. They receive no response history, future record,
tariff, charge, account, balance, horizon, saving, or profitability field. The
current action is the explicit source label. Reasons filed after the round are
absent.

The legacy replay adapter creates callbacks only for compatibility. Their sole
nonlocal is the immutable `LawfulProgram` data record. The finite audit checks:

1. exact equality with the declared nine-record tuple;
2. nine distinct identifiers and only the three declared toll magnitudes;
3. no callable stored in a program;
4. adapter closures contain only their program and no environment object;
5. the policy suite is exactly the five default top-level functions;
6. those policy functions have no nonlocal or environment capture; and
7. the rule-context schema contains no prohibited field.

This closes non-capture for the finite class under the ordinary assumption that
audited Python modules are not monkey-patched after audit. It makes no claim
about arbitrary `Comparator` callbacks, which remain capable of closure capture.

## Additive boundary

Repository replay and local counterfactual loss agree under these assumptions:

- arrivals, filings, schedules, reasons, and obligations are frozen;
- the guard uses the actual strict prefix and candidate action;
- responses are canonical and the edit changes only the current response;
- `Accounting.suspends` is false, so current charge cannot change later service;
- the comparator class is not filtered after play by affordability;
- one occasion occurs per date and each response fits the declared work cap; and
- each complete charge vector is available and lies in `[0,2]^8`.

The executable boundary checker rejects suspension, filing sources, multiple
same-date occasions, noncanonical responses, altered service windows, excessive
charge, or a one-response work overrun. The theorem does not cover replay-prefix
guards, endogenous filings, suspension, solvency coupling, or post-hoc deletion.

## Blum--Mansour instantiation

The cited source is Blum and Mansour, “From External to Internal Regret,” JMLR 8
(2007), §7, Theorem 18
([article](https://www.jmlr.org/beta/papers/v8/blum07a.html),
[PDF](https://www.jmlr.org/papers/volume8/blum07a/blum07a.pdf)).

| Theorem 18 hypothesis/object | frozen lawful instance |
|---|---|
| fixed finite actions `{1,...,N}` | `Lambda`, `N=8` |
| finite modification rules `F`, `K` | the nine audited declarative programs, `K=9` |
| finite time selectors `I`, `M` | always-on selector, `M=1` |
| history-indexed rule fixed before play | program fixed; `Ftilde_phi^t` uses predictable `x_t` |
| total action transformation | rejection/no proposal is identity; every map closes on `Lambda` |
| bounded loss vector in `[0,1]^N` | divide the exact `[0,2]^8` charge vector by `ell_max=2` |
| full information | every label's charge is computable from the frozen schedule |
| stationary distribution | computed on the program-mixture `8 x 8` stochastic matrix |
| row-conditioned weights | one weight per source label and program; 72 weights for `M=1` |

The source algorithm uses real-valued weights and a stationary distribution.
Item 30 must either implement those semantics directly or justify an
exact-rational parameter/solver variant; this is implementation debt, not an
action-interface obstruction.

Theorem 18 therefore yields an online learner satisfying, for every audited
program `phi`,

```
L_H,T <= L_H,T,phi + O(ell_max * sqrt(T * 8 * log 9)).
```

Equivalently, expected mixed-action charge regret is
`O(ell_max sqrt(8 T log 9))`, hence `o(T)`. The source states big-O and does not
give this round a sharper constant. The controlled quantity is the loss of the
mixed distribution (and therefore expected sampled charge under ordinary
sampling). No pathwise or high-probability sampled-trajectory bound is claimed.

**Frozen Lawful Φ-Regret Theorem (provisional name).** In the frozen environment
specified above, for every declared horizon `T` and the nine audited fixed causal
programs, there exists a horizon-tuned online learner whose expected cumulative
charge regret against every program is
`O(ell_max sqrt(8 T log 9))`. This is a derived instantiation of Blum--Mansour
Theorem 18 through the proved/tested representation bridge, not a local reproof
of their reduction. The source proof optimizes its parameter `beta`; this round
does not supply an anytime tuning or doubling argument for one infinite run.

## Recurrent-failure consequence

At round `t`, let `q_t` be the learner's mixed-action probability mass on source
labels where a fixed audited program is admitted and saves at least `delta > 0`.
If residual counterfactual distortion is at most a horizon-independent `B`, then

```
R_T(phi) >= delta * sum_t q_t - B.
```

If `sum_t q_t >= rho*T` for all sufficiently large `T`, then

```
R_T(phi) >= rho*delta*T - B.
```

This contradicts `R_T(phi)=o(T)`. The finite inequality and an inhabited witness
are Lean-proved as `recurrentFailure_lowerBound`. Thus any learner with an
anytime `o(T)` guarantee cannot assign positive asymptotic expected mass to a
failure pattern represented by one fixed audited lawful program with uniform
positive saving and bounded distortion. Deterministic play is the special case
`q_t` in `{0,1}`. A claim about the density on one realized sampled path needs
the sampling result that this round does not supply.

The conclusion concerns recurrent correctable failures visible to this
nine-program charge comparator class. It does not establish comparator coverage,
moral truth, a uniquely correct normative state, pathwise convergence, or the
answerability of whatever learner item 30 constructs.

## Evidence status

- `semanticAction_card`, generic regret preservation, and the finite
  recurrent-failure inequality: `lean-proved`, unregistered.
- Python representation, factorization, boundary, and finite non-capture audit:
  `test-supported` over exact exhaustive finite domains, unregistered.
- The online regret guarantee: derived instantiation of the cited source theorem,
  not a local reproof.
- An item-30 learner, measured regret curve, and integration/answerability result:
  open.
- An anytime tuning connecting the horizon-wise source instantiation to one
  infinite sampled run: open.
