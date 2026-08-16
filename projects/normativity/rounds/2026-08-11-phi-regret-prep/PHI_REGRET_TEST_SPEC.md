# The φ-regret test specification

The next round's work order. Everything below is fixed by this round; a round
that changes any of it is doing something else and should say so.

## 1. The finite test environment

| parameter | value | fixed by |
|---|---|---|
| horizon `T` | run at 12, 24, 48, 96 | replication across horizons is how a rate claim is exhibited |
| occasions | one per date, identifier `o:i`, target `q:i` | `src/experiments.py` |
| action set | `merits(uphold)`, `merits(deny)`, `default`, `decline(k)` for `k ∈ 0..4` | `src/model.py` |
| schedule | `τ_def = 1`, `τ_ref = 1/2`, `w = 4`, threshold `1/2` | `src/experiments.py::SCHEDULE` |
| loss range | `[0, 2]`; `ℓ_max = 2` | `PHI_REGRET_OBJECTIVE.md` §2 |
| service work | `per_date = 3`, `merits = 1`, `default = 1/2`, `decline = 0` | `src/experiments.py::COSTS` |
| accounting | **`Accounting({}, suspends=False)`** | `COUNTERFACTUAL_CHARGE_INFLUENCE.md` §C — declared, not assumed away |
| filings | frozen | `REPLAY_SEMANTICS.md` |
| guards | actual prefix | `REPLAY_SEMANTICS.md` |
| policy | `PolicySuite()` defaults | `REASONS_RESPONSIVENESS_INTERFACE.md` |

**The comparator class.** Nine rules, explicit:

1. `identity`.
2. `repair_declines` — decline to merits wherever a live interval separates the
   threshold. The canonical repair.
3. `repair_declines` restricted to even-indexed occasions.
4. `repair_declines` restricted to odd-indexed occasions.
5. `toll_declines(1)`, 6. `toll_declines(2)`, 7. `toll_declines(4)` — the last of
   which is `unresolved` wherever the allowance is under 4 and therefore fires
   only where it is licensed.
8. `default_declines` — decline to the scheduled default wherever a ripeness
   ground licenses the basis move. To be written; it is one call to
   `fixed_edit`.
9. `withdraw_merits` — merits to decline on a ripeness ground. Present so that
   Φ_law is not entirely composed of improvements.

`|Φ_law| = 9`, so `√(log|Φ_law|)` is about 1.48 and the horizons above are enough
for a `√T` bound to be visible against it.

## 2. Baselines

Three, and no prediction about which wins.

**B1 — the transcript learner.** The actual history: declines everywhere the
pattern is recognised. This is the learner that refuses to learn, and it is what
`E4` shows carrying linear regret.

**B2 — a standard online baseline.** Exponential weights over the 9-element Φ_law
via the Blum–Mansour fixed point, learning rate `√(8 log 9 / T)`. Report both the
realised `sup_φ R_T(φ)` and the bound.

**B3 — a lawful-edit-tracking learner.** Maintains, per guard, a count of
occasions at which a certificate was admitted and the charge that firing would
have saved; adopts a rule once its count exceeds a declared threshold. This is
the learner that would make the self-hosting identity of `REMEDIABLE_FAILURES.md`
true, and it is the one whose answerability has to be checked separately (S4).

## 3. What is measured

For each `φ ∈ Φ_law`: `R_T(φ) = L_T(H) − L_T(H^φ)`, the fire count, the rejection
codes and their counts. Then `sup_{φ admissible} R_T(φ)`, normalized by `T`, at
each horizon. `src/regret.py::evaluate_class` already returns all of it.

Report `|Φ_law|` and its contents alongside every regret number. A regret figure
without the class it is against is not a result.

## 4. Success outcomes

- **S0 — semantics.** Every quantity well defined; replay deterministic; identity
  replay reproduces the actual run. **Reached in this round**, for all fifteen
  fixtures.
- **S1 — witness.** A persistent remediable failure produces linear lawful-edit
  regret. **Reached in this round**: `E4`, `2/3` per occasion at three horizons.
- **S2 — algorithmic.** A candidate learner obtains sublinear `sup_φ R_T(φ)` on
  the finite class. **Open. This is the next round's target.**
- **S3 — consequence.** Sublinear φ-regret implies no positive-rate recurrent
  remediable failure under the stated assumptions. Open; the argument is one line
  and its hypotheses are in `REMEDIABLE_FAILURES.md`.
- **S4 — integration.** The successful learner remains answerable,
  reasons-responsive by the declared interface, and inside the declared service
  work. Open, and the most likely place for the round to fail interestingly: B3
  adopts rules, and adopting a rule is itself a normative change that ought to be
  answerable.

S2 alone is a result. S2 without S4 is a result with a named gap.

## 5. Pre-registered negative outcomes

Each of these is a finding, and a round that hits one should report it rather
than adjust the environment until it goes away.

1. **No satisfactory replay semantics under the restrictions.** Would be shown by
   a fixture where identity replay fails to reproduce the actual run for a reason
   that is not a malformed fixture.
2. **Counterfactual influence unbounded even fenced.** *Already found* —
   `E10b`. The next round inherits the finding, not the question.
3. **Φ_law too weak, self-correction vacuous.** Would be shown by a plausible
   recurrent failure with no certifiable repair in the nine rules. Report the
   pattern and what it would take to represent it.
4. **Φ_law too broad, admitting cost-driven rewriting.** Would be shown by a rule
   that passes the interface and that a reader recognises as illegitimate. This
   is the one negative result that would invalidate the interface rather than
   bound it, and it should be escalated rather than filed.
5. **Charge loss does not track the remediable-failure intuition.** Would be shown
   by a pattern that is intuitively a failure and costs nothing, or the reverse.
6. **Standard machinery does not apply.** Would be shown by the Blum–Mansour
   fixed-point step failing to instantiate — most plausibly on the varying
   per-occasion action set. See `ONLINE_LEARNING_MAP.md`.
7. **Low regret compatible with an important recurrent failure.** The coverage
   gap made concrete. Expected, and worth exhibiting rather than assuming.
8. **Resource feasibility destroys the reduction.** Would be shown if the
   affordability constraint makes the affordable subclass of Φ_law depend on the
   learner's own play, since then the comparator class is not fixed. `E13` is the
   simplest case and does not yet exhibit it.

## 6. Order of work

1. Instantiate the Blum–Mansour reduction against this substrate and record
   whether it applies. Nothing else is worth doing first.
2. Write rules 8 and 9, run the class at four horizons, table the results.
3. B2 and B3, same table.
4. S3, which is one line given a bound and the hypotheses already listed.
5. S4, which is where the round should expect to spend its time.

## 7. What the next round must not do

Redesign the ontology. Add a coordinate to the response set. Change the loss.
Lift a v1 exclusion without measuring what lifting it costs, the way `E11`, `E12`
and `E10` measure the three that exist. Define lawfulness by anything that reads
the charge table — the footprint will stop it, and a round that works around the
footprint has removed the reason any of this means anything.
