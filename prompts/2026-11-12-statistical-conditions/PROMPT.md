# Statistical conditions on logical inductors — an exploratory proof round

A new round on `A-M-Berns/alignment-workspace`. It builds on pull request #146
(`round/2026-11-10-exact-conditions-capital`, open and unmerged at the time of
dispatch). Work in a fresh git worktree on one branch,
`round/2026-11-12-statistical-conditions`, branched from
`origin/round/2026-11-10-exact-conditions-capital` — or from `origin/main` if #146 has
merged by the time you start. Open a pull request; if #146 is still unmerged, set its
branch as the base and say in the description that this one is stacked on it.
**Do not merge anything and do not enable auto-merge.**

Commit this prompt verbatim as `prompts/2026-11-12-statistical-conditions/PROMPT.md` in
the first commit. Prompt author: Claude Fable 5.2 (Anthropic), on the maintainer's
instruction in conversation on 2026-11-12. Identify the executing model accurately.

**This round is exploratory and its deliverable is a judgment with proofs behind it:**
what is the right theorem for *statistical* conditions on a logical inductor, what is
its right hypothesis, and how much of it can be proved now. A route that fails is a
result; say what killed it, with the evidence. Depth over coverage. Do not weaken a
statement silently; declare each change. Nothing below is kernel-checked unless it
cites a declaration.

## Where this sits

PR #146 gives the interface `DualCertifiedMarket` (a price history meeting a condition
exactly, with multipliers and a per-day inequality), its account, preservation
(`no_efficient_trader_exploits`: account bounded below implies no e.c. trader exploits),
the prefix reserve bound (`reserve_bound`), the seller obstruction (`seller_exploits`),
the conditional bridge (`Bridge.bridge`, `accountBounded_of_frequency`) and a market for
one floor per day (`FloorSchedule.market`). Read
`projects/normativity/rounds/2026-11-10-exact-conditions-capital/THEOREM.md` and the
three `ExactConditions*.lean` files first, then `WarrantSolvency.lean`
(`Schema.bounded_iff_frequency`, the unit-stake form) and the pinned dependency's
pseudorandomness results (`DivergentWeighting`, `PGenerableWeighting`,
`lic_learning_pseudorandom_frequency_above` and neighbours; see
`lean/.lake/packages/agentFoundations/APITests/LogicalInduction.lean`).

Why it matters to the program. A defeasible reason applied repeatedly is, on prices, a
stream of conditional bets at a fixed strength `c < 1` whose instances settle. One open
instance is a hedged bet and the reserve bound covers it. Across instances the reserve
shrinks at each lost bet, so what keeps the reason affordable is its track record. That
is the case the program's warrants and its epistemic deference actually live in, and it
is proved only in two partial forms: with unit stakes (`bounded_iff_frequency`), and
with market-set stakes under a hypothesis (`Bridge.Frequency`) that is inhabited only
where every instance is true. ATTENTION items 138 and 139 on the #146 branch state the
gap.

The running setting unless a matter says otherwise: one fresh sentence `phi_n` per day,
the floor `c <= price(phi_n)` with fixed `0 < c < 1`, settlement the next day, realized
truth values `x_n`, multipliers `mu_n` (in the floor market: the firm's net short
position on the floored sentence), account `Q_N = sum mu_n (x_n - c)` plus open
exposure, ceiling `U`.

## Matters, in priority order

### 1. The cost of finitely many failures (prove)

From the prefix reserve bound, or directly: if at most `R` instances are lost (applied
and false) through day `N`, the account in every world live at `N` is at least
`-U ((1 - c)^-(R+1) - 1)` or the correct expression of that shape — find the exact
constant, including the open instance. Then tightness for the class of all nonnegative
multiplier sequences under the ceilings: a compounding staker that loses nothing and
stakes its whole headroom on each instance that will fail attains it. State both in
Lean. Corollaries to state plainly: a schema with finitely many lost instances is
affordable with an explicit bound; called-off instances (premise false, or withdrawn
before settlement) cost nothing; the bound grows geometrically in the number of losses,
which is why the reserve alone cannot carry a schema that loses infinitely often.

### 2. Unit stakes and market stakes (identify, prove)

Relate `WarrantSolvency.Schema` to the floor market's account precisely: which of its
conclusions survive when the stake is `mu_n` rather than one, and which do not. Exhibit
exactly (in exact rationals, Lean or Python) a truth sequence and a nonnegative stake
sequence under the ceilings for which the unit-stake account is bounded and the staked
account is not, and the reverse. Say what property of the stake sequence the
equivalence needs.

### 3. Random outcomes: a capital bound with a probability (prove abstractly)

Abstract statement, no market needed: a filtration, outcomes `x_n` in `[0,1]` with
`E[x_n | past] >= c`, predictable stakes `mu_n >= 0`, the per-day ceiling
`Q_{n-1} + mu_n (1 - c) <= U` (so `U - Q_n` is a nonnegative supermartingale started at
`U`). Conclude `P(inf_n Q_n <= -K) <= U / (U + K)` for every `K > 0` (Ville / Doob's
maximal inequality), and almost-sure boundedness below. Mathlib has the maximal
inequality for submartingales; use it. Then state exactly what additional structure an
assessment process driven by random observations would need for this to give
`AccountBounded` path by path — in particular that the comparison must be with the
*settled* account, and that an unsettled-true instance left open indefinitely breaks
it. Do not build that structure; state it and file it if it is well-posed. No margin
`gamma` should be needed here; if one is, say why.

### 4. The deterministic case: what hypothesis makes the bridge fire (the core)

The question is ATTENTION item 138. Work it in this order and stop where it honestly
stops.

(a) **One trader.** Fix one e.c. trader in the firm. Is its own headroom-normalized
floor-selling a `PGenerableWeighting` in the dependency's sense, or dominated by one?
If so, prove: under frequency at least `c + gamma` along every P-generable divergent
weighting, that trader's cumulative gain from selling at the floor is bounded. If the
normalized weighting is not expressible, say which operation breaks expressibility
(division by headroom, dependence on settled outcomes, discontinuity) and whether a
smoothed or dominated variant repairs it.

(b) **The mixture.** The account's multiplier is the firm's aggregate net short, a
weighted sum over infinitely many budgeted traders. Individual bounds do not sum
without uniform control: a claim on record, unverified, is that under some computable
enumeration of traders, traders that hard-code finite tables of failing instances and
reinvest can make the firm's cumulative gain at the floor unbounded although no single
trader's is. Decide this. Either construct it (a truth sequence that is pseudorandom
above `c + gamma` in the dependency's sense, an enumeration, and an unbounded account),
or prove a uniform bound under a stated assumption on the enumeration (for example
index at least exponential in description length), or show which assumption on the
*sequence* suffices (a uniform version of pseudorandomness: one bound on the weighted
shortfall across all weightings, discounted by their firm weight). Say whether the
answer depends on the enumeration; if it does, that is a finding about what the
theorem's hypothesis must mention.

(c) **Account unbounded is not exploitation.** Preservation is one-way. If (b) yields
an unbounded account, determine whether the floor market is nevertheless unexploited by
every e.c. trader on that sequence — a direct argument not passing through the account,
for instance from the dependency's theorem that a logical inductor's prices on such a
sequence are eventually at least `c + gamma` minus any margin, so the floor is
eventually slack. Be careful about circularity: that theorem assumes the market is a
logical inductor. If a non-circular version exists (the floor market's prices dominate
the unconstrained market's in a usable sense; or the substitution
`lo + (1 - lo) * price` transports the unconstrained market's guarantee), find it.
A market that is a logical inductor with an unbounded account would show the account is
the wrong sufficient condition for statistical floors and should be recorded as such.

(d) **Item 139.** With (a)–(c) in hand, restate the extraction problem in the sharpest
form you believe, or mark it as dissolved by (c).

### 5. Look before proving (a toy, exact)

A small exact model to see the phenomena before or alongside matter 4: a finite firm of
explicit traders (a constant seller, a seller on a fixed residue class, a table trader
with reinvestment, a buyer), a floor, truth sequences of several kinds (all true;
periodic with frequency above `c`; a sequence the listed traders cannot predict; one a
listed trader can), and the per-day inequality solved exactly in `fractions.Fraction`.
Record the account, the multipliers and the normalized weighting. This is exploration:
mark it as such, and let no theorem depend on it. Its purpose is to tell you which of
4(a)–(c) is true before you spend the round proving the wrong one.

### 6. What it means for a warrant (short, last)

In at most a page in the round's `THEOREM.md`, with no new mathematics: translate the
results into the three-form warrant of `SeedStatics.Form` (premise, applicability,
strength), saying which settlement outcomes (`kept`, `vacuous`, `rebutted`, `retired`,
and undercut by the docket) are charged and which are free under the account, and what
the affordable strengths of a schema are in terms of its lost-instance record.

## Standards particular to this round

- **Judgment first.** The report opens with the answer to: what is the statistical
  theorem, what is its hypothesis, what is proved, what is refuted, what is open.
- **Second opinion.** Once, on the round's strongest claimed result and its strongest
  claimed refutation, obtain an adversarial review from GPT-6 Astra through the `codex`
  CLI (`codex exec --skip-git-repo-check --sandbox read-only --cd <dir> "<prompt>"`,
  with the statement and proof in a file it can read). Commit the review verbatim under
  the round's `prompts/` directory and say in the report what you did with each
  finding. If `codex` is unavailable, say so and continue.
- **Lean discipline** as in `AGENTS.md`. New modules under
  `lean/Workspace/Normativity/Contrib/`. Every registered theorem has an inhabited
  hypothesis package; for matter 4 a witness whose truth values are not all one is the
  point.
- **Registry.** Register what closes in `projects/normativity/CLAIMS.md` against items
  138 and 139 where they answer or narrow them, updating those items in place. File at
  most three new items. Item numbers: pull requests #145 and #146 both file items
  numbered 136–138 on their own branches; number new items above every number used on
  either branch and on `main`, and say in the report that the collision exists.
- **Round records** as usual: `state/rounds.json` with `depends_on` naming the
  exact-conditions round, the round directory
  `projects/normativity/rounds/2026-11-12-statistical-conditions/` with `THEOREM.md`,
  provenance rows, `prompts/2026-11-12-statistical-conditions/REPORT.md`.
- **Do not edit anything under `checkers/`, `tests/`, `.github/` or `graph/policy.yaml`.**
  If a gate fails for a reason only such an edit would fix, stop, leave the gate red,
  and report it.
- **Citations.** Cite nothing you cannot verify; state mathematical content directly.
- **No wiki edits** beyond a count binding a checker requires.

## Operating constraints on this machine

- Never call `lake` directly: `~/.claude/scripts/safe-lake.sh build <target>` from
  `lean/`. Run `~/.claude/scripts/resource-guard.sh check` before any long job and
  `... wait` if it reports loaded. Other sessions are running.
- `tests/audit_axioms.py` (about 16 minutes) and `tests/run.py` (about 11 minutes)
  exceed the foreground limit: run each in the background with a long timeout and wait
  for it before proceeding. Do not end your run while a background job is going.
- Commits signed off (DCO) with `Model:` and `Prompt-author-model:` trailers; the pull
  request body carries the Model attribution section and the template's fields. No
  co-author lines.
- Do not touch other worktrees under `.claude/worktrees/`.
- Before you exit, whatever state the round is in, push the branch and write
  `/tmp/astra-consult/round2/FINAL.md`: the pull request URL (or the branch and why
  there is none), the judgment in five sentences, each matter's outcome with
  declaration names, every statement that changed and how, what the second opinion
  found, what is unverified, and the gates' last results.
