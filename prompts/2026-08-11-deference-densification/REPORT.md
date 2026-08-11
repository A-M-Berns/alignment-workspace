# Track E — bounded densification study: report

Round: `prompts/2026-08-11-deference-densification`.
Answers `PRIORITIES.md` item 18. Consumed `FINITE_MODEL_SKELETON.md` v1 (§1 carrier
`F`, §8.6 aggregation hole), `CORRIGIBILITY_ROADMAP.md` § V, `CORRIGIBILITY_PAPER_LEDGER.md`.

**Stopping object reached: a sharp lower bound.** Theorem 2 below is an exact
value, not an estimate: the maximum harvest placeable by time `T` under an
exposure cap is attained, and the bound and the construction are the two sides of
one identity. The construction (Theorem 5) is that identity's attainment case, not
a second stopping object. Per the prompt's stopping rule, work stopped here.

---

## 1. Exact result

### Setup (all objects provisional, §8)

`F : ℕ → ℕ` with `F(n) > n` is the settlement delay of `FINITE_MODEL_SKELETON.md`
§1, transported to a single infinite index line. A position opened at `n` occupies
the **settlement window** `I_n = [n, F(n)) ∩ ℤ`. Exposure weights `a_n ∈ ℚ≥0`.
Outstanding exposure and harvest are

```
E(t)  =  Σ { a_n : n ≤ t and F(n) > t }  =  Σ { a_n : t ∈ I_n }
H(T)  =  Σ { a_n · D_n : n ≤ T }
```

`S ⊆ ℕ` is the set of stages carrying defect, `D_n ≥ 0` its magnitude, `M ∈ ℚ>0`
the exposure cap, `Ω` a finite index set. Write

```
ν_F(Ω)  =  max size of a pairwise-disjoint subfamily of { I_n : n ∈ Ω }
ν_F(T)  =  ν_F(S ∩ [0,T])
```

the **window packing number**.

### Lemma 1 (piercing duality for settlement windows)

For finite `Ω ⊆ ℕ`, `ν_F(Ω) = τ_F(Ω)`, where `τ_F(Ω)` is the least size of a set
`P ⊆ ℤ` meeting every `I_n`, `n ∈ Ω`. Greedy attains both.

*Proof.* `ν ≤ τ`: disjoint windows need distinct piercing points. For `τ ≤ ν`, run
greedy: `R_0 = Ω`; at step `k`, pick `m_k ∈ R_{k-1}` minimizing `F(m)` (ties by
least `n`), set `p_k = F(m_k) − 1` and `R_k = { n ∈ R_{k-1} : p_k ∉ I_n }`. Since
`m_k ≤ F(m_k) − 1 < F(m_k)`, we have `p_k ∈ I_{m_k}`, so `m_k ∉ R_k` and the
process terminates after `K = |P|` steps having removed every index; each index was
removed at a step whose point it contains, so `P = {p_1,…,p_K}` pierces `Ω`. The
selected windows are pairwise disjoint: for `j < k`, `m_k ∈ R_{k−1} ⊆ R_j` gives
`p_j ∉ I_{m_k}`, and `m_k ∈ R_{j−1}` with the minimality of `m_j` gives
`F(m_k) ≥ F(m_j) = p_j + 1 > p_j`; so `p_j ∉ I_{m_k}` forces `m_k > p_j`, i.e.
`m_k ≥ F(m_j)`, and `I_{m_k} ∩ I_{m_j} = ∅`. Hence `τ ≤ K ≤ ν ≤ τ`. ∎

### Theorem 2 (exact exposure–harvest bound)

Let `a : Ω → ℚ≥0` satisfy `E(t) ≤ M` for every `t ∈ ℤ`. Then

```
Σ_{n ∈ Ω} a_n  ≤  ν_F(Ω) · M ,
```

and equality holds for `a = M` on a maximum disjoint subfamily and `0` elsewhere.

*Proof.* Take `P` from Lemma 1 with `|P| = ν_F(Ω)`. Every `n ∈ Ω` has some
`p ∈ P ∩ I_n`, and `a ≥ 0`, so
`Σ_{n∈Ω} a_n ≤ Σ_{p∈P} Σ_{n : p ∈ I_n} a_n = Σ_{p∈P} E(p) ≤ |P| · M`.
Attainment: a disjoint family has `E(t) ≤ M` pointwise. ∎

Three consequences are worth stating separately, because each kills a strategy the
task description asks about.

- **Adaptivity buys nothing.** The bound quantifies over all nonnegative offline
  weightings, so no placement rule measurable at decision time can exceed it.
- **Overlapping positions buy nothing.** The optimum is attained by a disjoint
  family; a maximizer never needs two positions outstanding at once.
- **Fractional sizing buys nothing.** The bound is the exact value of the linear
  program `max Σ a` over `{ a ≥ 0 : E(t) ≤ M ∀t }`, and that value is integral in
  units of `M`.

### Corollary 3 (harvest cap)

If `0 ≤ D_n ≤ D̄` then `H(T) ≤ D̄ · M · ν_F(T)`.

### Corollary 4 (orbit formula)

If `F` is nondecreasing and `S = ℕ`, then
`ν_F(T) = #{ k ≥ 0 : F^k(0) ≤ T } = min{ k : F^k(0) > T }`.

*Proof.* On `Ω = [0,T]`, monotone `F` makes `n = min Ω` the `F`-minimizer, so
greedy sets `m_1 = 0`; survivors after step `k` are `{ n ≤ T : n ≥ F(m_k) }`, whose
`F`-minimizer is `F(m_k)`. Hence `m_{k+1} = F(m_k)`, and greedy runs exactly while
`F^k(0) ≤ T`. ∎

### Theorem 5 (the construction: the stated target is achievable in every regime)

For every `F` with `F(n) > n` and every infinite `S`, define `n_1 = min S` and
`n_{k+1} = min { n ∈ S : n ≥ F(n_k) }`. Each `n_{k+1}` exists (`S` is infinite,
`F(n_k)` finite); the windows `I_{n_k}` are pairwise disjoint. Setting `a_n = M` on
`{n_k}` and `0` elsewhere gives `sup_t E(t) = M < ∞`, and under persistent defect
(assumption **(P)**, §5) `H(∞) ≥ M δ · |{n_k}| = ∞`.

`a_n` depends only on `F` and `S ∩ [0,n]`, so placement uses decision-time
information only — the roadmap's *placement precedes settlement* commitment holds.

**So the target as literally posed — bounded outstanding exposure with divergent
harvest — holds for every delay regime, including regimes growing faster than any
computable bound.** It is not the binding question. What the delay costs is *rate*,
and Theorem 2 says the rate exactly.

### Theorem 6 (time-to-force: the sharp lower bound, inverse form)

Take `S = ℕ`, `D_n = δ` exactly, `F` nondecreasing. The least `T` at which harvest
`W` is achievable under exposure cap `M` is

```
T_W  =  F^{m−1}(0)  ,      m = ⌈ W / (M δ) ⌉ .
```

*Proof.* By Corollary 3 and Theorem 2 the achievable harvest by `T` is exactly
`M δ ν_F(T)`; by Corollary 4 that is `≥ W` iff `#{k : F^k(0) ≤ T} ≥ m` iff
`F^{m−1}(0) ≤ T`. ∎

### Corollary 7 (density is forced to zero by unbounded delay)

If `F(n) − n → ∞` then `ν_F(T)/T → 0`.

*Proof.* The greedy orbit satisfies `m_{k+1} − m_k ≥ F(m_k) − m_k → ∞` since
`m_k → ∞`, so `m_k / k → ∞` (Cesàro). With `k = ν_F(T)` we get
`T / ν_F(T) ≥ m_{k−1}/k → ∞`. ∎

Since at most `ν_F(T)/ε` stages in `[0,T]` can carry weight `≥ εM` (Theorem 2), the
same bound governs *how often discretion can be exercised at scale*, not only the
total.

### Regime values (exact integers, computed)

`ν_F(T)`:

| `F` | `T=10` | `10²` | `10³` | `10⁶` | `10¹²` |
|---|---|---|---|---|---|
| `n+1` | 11 | 101 | 1001 | 1000001 | 1000000000001 |
| `n+8` | 2 | 13 | 126 | 125001 | 125000000001 |
| `n+⌊√n⌋+1` | 5 | 19 | 62 | 1999 | 1999999 |
| `2n+1` | 4 | 7 | 10 | 20 | 40 |
| `2ⁿ+1` | 3 | 4 | 4 | 4 | 5 |

Time-to-force `F^{m−1}(0)`:

| `m` | `n+1` | `n+8` | `n+⌊√n⌋+1` | `2n+1` | `2ⁿ+1` |
|---|---|---|---|---|---|
| 4 | 3 | 24 | 5 | 7 | 33 |
| 5 | 4 | 32 | 8 | 15 | 8589934593 |
| 6 | 5 | 40 | 11 | 31 | `2^8589934593 + 1` |

The three growth classes the prompt asked for behave as: **bounded delay** —
positive density `1/ℓ`, densification is free; **polynomial-type**
`F(n) = n + n^β` — density `≍ T^{−β}`, harvest `≍ T^{1−β}`; **exponential-type**
`F(n) = cn` — density `≍ (log T)/T`, harvest logarithmic; **iterated-exponential**
`F(n) = 2ⁿ` — harvest `≍ log* T`, and forcing five units of exposure-weight already
costs `T ≥ 2^{2^{33}}`.

### Collateral accounting

Replacing the indicator of `I_n` by a collateral profile `w_n : ℤ → [0,1]`
supported on `I_n` (constraint `Σ_n a_n w_n(t) ≤ M`) changes nothing structural. If
`w_n ≥ c > 0` on `J_n ⊆ I_n`, the same piercing argument over `{J_n}` gives
`Σ a_n ≤ (1/c) · ν_F({J_n}) · M`. Mark-to-market release, amortization schedules
and haircuts are all absorbed into "what is the effective above-threshold window",
and the geometry is then identical with `I_n` replaced by `J_n`.

---

## 2. Evidence class

Nothing in this round is registered, and `CLAIMS.md` does not exist in the tree.

- Lemma 1, Theorems 2, 5, 6, Corollaries 3, 4, 7: complete elementary proofs,
  written above, **adjudicated by no gate in this repository**. Under the
  `AGENTS.md` classes they are *proposals* until a Lean port; the honest registry
  entry today is `conjectured` for each, with the proof text as documentation.
  They are finite-combinatorial and would port to Lean without new theory.
- The random-instance agreement of greedy, exhaustive search and the exact
  rational LP (`test-supported`, 4000 + 250 instances, seeds fixed in the script).
  This is a cross-check on the proofs, not a substitute for them.
- The regime tables and the netting witness: exact integer/`Fraction` computations,
  reproducible by the script. Witness-shaped, but no house checker was invoked, so
  they are not `witness-checked`.

---

## 3. Files, declarations, checks

Written this round, both inside `prompts/2026-08-11-deference-densification/`:

- `REPORT.md` — this file.
- `exposure_geometry_check.py` — exact-arithmetic checks. `python3
  exposure_geometry_check.py`, ≈17 s, no dependencies outside the standard library,
  no floats. Checks, in order: Lemma 1 on 4000 random families (greedy = exhaustive
  maximum = greedy piercing size); Theorem 2's integrality on 250 random families
  by exact rational vertex enumeration (0 instances where the LP exceeds `ν`);
  Corollary 4 against greedy for all `T < 300` in five regimes plus the two closed
  forms; the two tables of §1; the §6 netting witness.

No Lean declarations. `lake build` was not run, per the dispatch. No file outside
the round directory was touched.

---

## 4. What was not established

- **No Lean, no gate, no registry entry.** Every mathematical statement here is
  unadjudicated.
- **No connection to an actual Logical Induction trader.** `H(T) = Σ a_n D_n` is a
  posited linear harvest model. That a trader's realized value against a persistent
  price defect is proportional to position size times defect magnitude is not
  proved here and not inherited — it sits on the standing gap in
  `CORRIGIBILITY_PAPER_LEDGER.md` ("the criterion forces the tower" is `open`) and
  on `PRIORITIES.md` item 7. Nothing here narrows that gap.
- **Nothing here forces anything.** Theorem 6 says what accumulating `W` costs in
  time. It does not establish that any particular `W` suffices to force a criterion
  violation, nor that a defect is present, nor that the market is well defined.
- **Persistence is assumed, not derived.** Assumption (P) is exactly the antecedent
  the ledger says the corpus does not supply.
- **`F` is treated as exogenous and, for Corollary 4, nondecreasing.** Corollary 4
  and Theorem 6 fail as stated for non-monotone `F`; Lemma 1 and Theorem 2 do not
  need monotonicity, so the exact bound survives and only the orbit *formula* is
  lost. A delay chosen adversarially in response to placement is out of scope.
- **The bounded-loss (budget) variant is not solved.** §9 item 1 and §10.
- **`ν_F(T)` was not computed for any non-elementary `F`.** The claim "even
  Ackermann-type delay leaves harvest divergent" follows from Theorem 5, which is
  regime-independent; no growth-rate claim beyond the tabulated five is made.

---

## 5. Assumptions added

1. **(Aggregation.)** `FINITE_MODEL_SKELETON.md` §8.6 leaves cross-decision
   structure open. This round aggregates over a single infinite index line `ℕ`
   with one position per index, each with one settlement time `F(n)`. Stated as
   required by §8.6; it is an addition, not an inheritance.
2. **(P) Persistent selected defect.** There are `δ ∈ ℚ>0` and an infinite
   `S ⊆ ℕ`, with `n ∈ S` decidable from information available at `n`, such that
   `D_n ≥ δ` for all `n ∈ S`.
3. **(Bounded defect.)** `D_n ≤ D̄ ∈ ℚ>0` — used only in Corollary 3.
4. **(Hold-from-open.)** A position exploiting the defect at `n` is outstanding on
   all of `[n, F(n))`. This is the assumption that carries the entire difficulty;
   see §6.2.
5. **(Gross exposure.)** `a_n ≥ 0` and exposure is the sum, not a signed net. From
   the prompt; §6.1 shows it is load-bearing.
6. **(No reinvestment.)** `M` is a constant, so settled gains do not enlarge the
   exposure budget. Implied by the prompt's `sup_t` form; §6.3.
7. **(Linear harvest.)** Harvest from position `n` is `a_n D_n`, realized at
   `F(n)`. §4.

---

## 6. Counterexamples and necessity witnesses

Each shows one assumption of §5 is load-bearing: drop it and the answer changes
qualitatively, in the direction of making the problem trivial. That is the real
content of the impossibility search — the geometry is rigid, and every apparent
escape is an accounting artifact.

### 6.1 Gross exposure (assumption 5) is necessary

Signed positions under *net* exposure accounting break the bound by an exponential
factor. Witness, exact: `F(n) = 2n+1`, `a_n = 1` for all `n`, signs
`ε_n = (−1)^n`, `D_n = 1` for even `n` and `1/2` for odd `n`, `M = 1`, `D̄ = 1`.
Then the supremum over `t` of the absolute net exposure is `1`, while harvest is
linear in `T`:

| `T` | sup abs net exposure | harvest | gross bound `M·D̄·ν_F(T)` |
|---|---|---|---|
| 10 | 1 | 7/2 | 4 |
| 100 | 1 | 26 | 7 |
| 1000 | 1 | 251 | 10 |
| 10000 | 1 | 2501 | 14 |

The netting is not legitimate. Two positions cancel in exposure only if their
settlement payoffs cancel; here they settle at different times to different values,
and the short leg's risk is real. The general statement: **legitimate netting is
harvest-neutral.** If a pair is removed from the exposure count on the ground that
it bears no residual risk, its combined settlement payoff is identically zero, so
its combined harvest is zero; the remaining book is gross and Theorem 2 applies to
it unchanged. Sign-alternating spread trades reduce the *measured* number without
reducing the risk borne, so net-of-sign exposure is not an exposure functional for
this problem.

### 6.2 Hold-from-open (assumption 4) is necessary, and carries everything

If the position may instead be opened at any `s ∈ [n, F(n))` with undiminished
harvest, the effective windows are `[F(n)−1, F(n))`, so
`ν_F(T) = |{ F(n) : n ∈ S, n ≤ T }|`, which is `|S ∩ [0,T]|` for injective `F` —
full density, in every delay regime, at exposure cap `M`. The entire densification
difficulty is the requirement that exploiting a defect *observed at `n`* means
carrying a position from `n`. Whether that requirement is real is a modelling
question about what the trader is buying and when the price gap exists, and this
round does not answer it.

### 6.3 No-reinvestment (assumption 6) is necessary

Under greedy disjoint rounds with persistent `δ`, settled gains permit
`M_{k+1} = M_k (1+δ)`. Harvest by `T` becomes `M((1+δ)^{ν_F(T)} − 1)` — exponential
in the packing number rather than linear — but `sup_t E(t) = M(1+δ)^{ν_F(T)−1} → ∞`,
so the prompt's constraint is violated exactly by the mechanism that would defeat
it. Bounded outstanding exposure and compounding are incompatible, and this is not
a proof artifact: it is the same trade-off in two notations.

### 6.4 Non-witness: adaptivity

No witness exists, and that is the finding. Theorem 2 bounds all offline
nonnegative weightings, so no adaptive rule — including one that sees `S` in full —
beats the fixed greedy family by any factor.

---

## 7. Deviations

1. **A second file beyond `REPORT.md`** was written in the round directory: the
   check script (`AGENTS.md` standard 3 — a claim without a check is a proposal).
   It is inside the granted write scope. The prompt named only `REPORT.md`.
2. **The prompt's literal target is satisfiable in every delay regime** (Theorem 5,
   two lines of proof), so answering it as posed would have produced a true and
   uninformative "yes". The round instead established the exact rate (Theorem 2)
   and its inverse (Theorem 6), which is the "sharp lower bound" stopping object
   the prompt lists. The re-scoping is declared here rather than absorbed. It stays
   inside the scope boundary: no trader formalization was attempted, and no
   Logical Induction fact was used or re-asserted.
3. **Snapshot discrepancy.** The prompt names parent snapshot `ec7d6cc`; the
   working checkout is `990a822`. The difference is the seven wave-1 `PROMPT.md`
   files plus a version-note edit in `FINITE_MODEL_SKELETON.md` §10; the skeleton's
   carriers are byte-identical, so the consumed input matches what the prompt names.
4. **`lake build` not run**, per the dispatch. No Lean was written, so nothing was
   left unverified by that omission.
5. **The human register was not written as a file.** The executing harness refuses
   report-shaped files from a subagent; the verification register above is complete,
   and the dual-register requirement is listed as an outstanding maintainer action.

---

## 8. Provisional names

All provisional (`AGENTS.md` standard 6); none proposed for permanence.

`settlement window` (`I_n`), `outstanding exposure` (`E`), `harvest` (`H`),
`exposure cap` (`M`), `window packing number` (`ν_F`), `piercing number` (`τ_F`),
`orbit formula`, `time-to-force` (`T_W`), `persistent selected defect` (assumption
(P)), `collateral profile` (`w_n`), `effective window` (`J_n`),
`hold-from-open`, `harvest-neutral netting`.

---

## 9. Maintainer decisions surfaced

1. **Which exposure functional the program means.** This prompt's `sup_t E(t) < ∞`
   is bounded *outstanding gross exposure*. The Logical Induction budget constraint
   is bounded *worst-case cumulative loss*, which is a different functional: it
   permits reinvestment and therefore permits outstanding exposure to grow. §6.3
   shows the answers diverge — linear in `ν_F(T)` under one, exponential in
   `ν_F(T)` under the other. The densification question has no determinate answer
   until this is fixed, and the choice is a modelling commitment, not a lemma.
2. **Whether hold-from-open is the intended geometry** (§6.2). If a defect observed
   at `n` can be traded at any point before `F(n)` at undiminished value,
   densification is free and item 18 dissolves. If it cannot, the reason is a fact
   about the market this repository does not yet model.
3. **Whether signed books are admissible** and, if so, under which functional
   (§6.1). Recording *net-of-sign exposure is not admissible as an exposure
   functional* would close a route that otherwise trivializes the problem for the
   wrong reason.
4. **Whether `F` is exogenous.** Everything here assumes the delay does not respond
   to placement. Under the roadmap's adversarial framing that is a substantive
   restriction.

---

## 10. Next recommended theorem

**The budget-functional analogue of Theorem 2**, stated as the controlling lemma
and offered as `conjectured`:

> Let `b ∈ ℚ>0` bound worst-case cumulative loss, let settled gains be available
> for redeployment, and let (P) hold with parameter `δ`. Then the maximum harvest
> achievable by time `T` is `b · ((1+δ)^{ν_F(T)} − 1)`, with the same packing
> number `ν_F(T)` and the same greedy attainment.

If it holds, the delay's cost is `log` of the harvest rather than the harvest
itself, exponential-type delay stops being a barrier, and item 18's negative half
is an artifact of the gross-exposure functional. If it fails, the failure locates
where reinvestment breaks against delayed settlement — which is the same place
`PRIORITIES.md` item 7 sits. Either outcome is decisive for decision 9.1, and the
statement is finite and elementary enough to attack directly.

Second, and cheaper: **port Lemma 1 and Theorem 2 to Lean.** They are `Finset`
arguments over `ℕ` with no analysis, they need no Logical Induction fact, and the
nonvacuity witness required by the Lean regime is Theorem 5's greedy family —
constructed, not stipulated. That would move the round's core from proposal to
`lean-proved` without any maintainer decision being taken first.

Not recommended: further search inside the gross-exposure model. Theorem 2 is an
exact value; there is nothing left in that model to find.

---

## 11. Attribution

- Prompt-author model: GPT-5.6 Sol (OpenAI), per the round's `PROMPT.md` header.
- Executor model: **Claude Opus 5 (Anthropic)**, model id `claude-opus-5`, run as a
  Claude Code subagent.
- Date: 2026-08-11. Repository `alignment-workspace`, branch
  `round/2026-08-11-deference-corrigibility`, working checkout at commit `990a822`.
- Review status: `ci-only` — no maintainer has read this, and no CI job in this
  repository adjudicates any statement in it.

---

## Outstanding maintainer actions

1. **Decide the exposure functional** (§9.1) — gross outstanding exposure, or the
   Logical Induction bounded-loss budget. Record the choice in `DECISIONS.md`.
   Until it is recorded, item 18 has two different answers and this report supplies
   both.
2. **Decide whether hold-from-open is the intended geometry** (§9.2). If it is not,
   close `PRIORITIES.md` item 18 as dissolved, citing §6.2.
3. **Rule on signed books and net-of-sign exposure** (§9.3), and if net accounting
   is inadmissible, record it in `FINITE_MODEL_SKELETON.md` or its successor so no
   later round re-derives §6.1 as a result.
4. **Write the human register** for this round (`AGENTS.md` dual-register standard),
   or waive it on the ground that no result entered the record; §7.5.
   *(Written by the orchestrator as `FOR_HUMANS.md`, 2026-08-11, and labelled as
   the orchestrator's text rather than the executing agent's.)*
5. **File the Lean-port item** for Lemma 1 and Theorem 2 if the port is wanted:
   deliverable `lean-proved`, acceptance `lean` gate green with the Theorem 5
   greedy family as the inhabitation witness.
6. **File the budget-functional lemma** (§10) as a `PRIORITIES.md` item if decision
   1 goes to the bounded-loss functional; it is the theorem that decides item 18
   under that reading.
7. **Decide whether anything from this round is registered.** `CLAIMS.md` does not
   exist in the tree. If the regime tables and the §6.1 witness are wanted as
   `witness-checked`, a house checker covering "exact packing number of a finite
   window family" is needed; the round did not write one, since
   `checkers/contrib/` entries would cap at `contributor-checked` and the Lean port
   is the better path.
8. **Add a `PROVENANCE.md` entry** for this round directory: generator
   `prompts/2026-08-11-deference-densification` (Claude Opus 5, Anthropic; prompt
   GPT-5.6 Sol, OpenAI), review status `ci-only`, date 2026-08-11.
