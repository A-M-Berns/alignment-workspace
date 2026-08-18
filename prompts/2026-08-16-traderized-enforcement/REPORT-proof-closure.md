# Report — proof-closing pass

Starting head `5fc434dc0440c757616cb68b98e9fdb51bbaaa53`. Branch
`traderized-enforcement`; no new pull request; `main` not merged. Seven commits:

    26e4392  the live-world Budgeter/TradingFirm lift against the source types
    d8189e5  the enforcement Strategy term, the composition, traderized deduction
    6dde749  the two nesting notions separated; two property families generalized
    4655c66  the coherence modulus; the C_t notation collision; five regressions
    3bbbcc9  the exact dual-distance presentation, eliminating the mesh term
    0590360  the theorem ledger, the closure document, the prompt and this report
    (this commit)  the commit list and the ending head

The ending head is this commit; `gh pr view 38` reports it as the branch head.

## What the pass closed

**The live-world lift is a theorem.** `Assessment` — a family of world sets over the
fixed Logical Induction world space, carrying a finite sound-and-complete enumeration
of the payout tables its worlds realise on any finite sentence support, plus
support-local temporal nesting — substitutes for `DeductiveProcess` inside the pinned
dependency's own `Budgeter` and `TradingFirm`. `lem:budgeter` parts 1–3 and `lem:tfdom`
go through against the dependency's real `Strategy n`, `Trader`, `EF`, `PCWorld`,
`MarketMaker` and `EfficientlyComputable`, and `MarketMaker(TF^L)` satisfies `LIC_L`.
This is outcome A/B of the dispatch's §4a, not a structurally similar finite model.

**The enforcement trader is a legal strategy, and the algebra is about it.**
`enforcementStrategy` is a `Strategy n`, and `marketValueRat_enforcementStrategy` proves
its exact rational value is the quantity `TraderizedEnforcement`'s inequalities bound.

**Enforcement preservation and traderized deduction are composed theorems.** The latter
runs against the source's own `TradingFirm` and `trading_firm_dominance`, so its
conclusion is the original `def:lic` over `D`, assembled as the dependency's own
`IsLogicalInductor`.

**The coherence bridge is closed with no error term.** The exact dual-distance
presentation of a rational polytope is a finite rational row family, independent of the
price, whose largest violation *is* the sup-norm distance.

## Corrections to the round

1. **`PAPER_RECONCILIATION.md` §2's hypothesis table is wrong about part 1.** It gives
   `lem:budgeter`.1 "(L2) only" and attributes nesting to `.2`. Nesting is consumed by
   part 1 as well: the available capital in each world's loss cap must be positive, and
   that is where a world live at `n` has to have been live at `n-1`.
2. **(L3) nonemptiness is not a hypothesis of the lift.** The source's own
   `EF.listMin [] = EF.const 1`, so the scaling infimum over no plausible world is one.
   The model refused that case; `src/budgeter.py` and `src/assessment.py` now return
   one, and `test_budgeter.Preconditions` records the behaviour instead of the refusal.
   Where (L3) does appear is in the source's §4 properties, as
   `∀ n, ∃ v, v.ConsistentWith (DP.D n)`.
3. **(L1) global nesting is not a hypothesis either.** Only its support-local shadow is
   used, and `lateAllTrueLive` satisfies the whole interface with `Live 1 ⊄ Live 0`. The
   two coincide exactly for families determined by their finite restrictions.
4. **`β_j ≥ (ε+M)/δ²` does not give `g_j ≤ δ`.** At `ε+M = 0` the condition is met by
   `β_j = 0` and nothing is constrained. The Lean statement carries `0 < ε+M`, which the
   source market supplies.
5. **Row conformance is not a distance bound.** Two near-parallel rows cutting the same
   region give ratio `1/e`. The round's result 26 was `test-supported` at "the net's
   resolution"; the exact statement is now three separate results, one of them a
   refutation of the naive reading.
6. **`C_t` was doing three jobs.** The ordinary aggregate's volume bound is `M_t`
   throughout the theorem-facing prose and docstrings; the paper's own `C_n` survives
   only where the source is cited; the coefficient family in `MODEL.md` is `N`.

## Deviations from the dispatch

- **§7, computability.** Not closed. The dispatch allowed "close it or find the
  obstruction"; the obstruction is named and is a transcription, not a mathematical gap.
  Three of the four pieces a compiler needs are present and proved; the absent one is
  the first-order erasure that `Construction/LIACompiler.lean` performs for the
  dependency's own aggregate in 7300 lines. `PROOF_CLOSURE.md` §VII.
- **§2's single table** is delivered as `THEOREM_MAP.md` sorted into settled /
  conditional / open / refuted, plus the arrow-by-arrow status in `PROOF_CLOSURE.md`,
  rather than as one table. The dispatch's §17 asks for exactly that sorting, and one
  table carrying both would repeat itself.
- **§5's classification** is by hypothesis shape for all but two families, which are
  transcribed and kernel-checked. The universal-semimeasure family was **not audited**.
- **§16's twenty-four tests** are not twenty-four new tests. Eighteen were already
  present and are cited in `THEOREM_MAP.md`; six were added, for the items the earlier
  passes had no executable trace of: resurrection breaking the floor, empty assessment
  sets, support-local against global nesting, presentation-relative conformance, the
  per-row tolerance hypothesis, and intensity information time. Item 2 (incompatible
  finite restrictions) is covered by the pre-existing
  `test_assessment.TheFailureCaseIsRejected` and `restriction_consistent`.
- **Addendum §A** is proved on paper, not in Lean. The separation step needs a
  sup-norm/`ℓ¹` duality over `Fin d → ℝ` that Mathlib does not carry conveniently.
- **Addendum §C's exactness** is `derived` plus `exhaustive-finite`, not `lean-proved`,
  for the same reason. `DistanceComplete` names it at the type the force theorem
  consumes, and `gap_le_of_distanceComplete` proves the interface cannot be met
  vacuously.
- **Addendum §B's regression against `δ+2η`** is recorded as a sharpness witness rather
  than a regression against shipped code: the round never shipped `δ+2η`. The Lean
  modulus has always carried the constant `1`, and `TheLipschitzConstantIsOne` shows it
  is attained.
- One rename was made and reverted: `README.md`'s "Force consumes `K_t`; it does not
  determine `C_t`" is the *credal* set and was briefly changed to `M_t`.

## Structural defects found

- **`AGENTS.md` requires a per-commit `Model:` trailer and nothing checks it.** The
  branch's earlier commits carry `Signed-off-by` only. This pass's commits carry both,
  which makes the history non-uniform either way. Queued in `DECISIONS.md`.
- **The local Lean build needed manual wiring.** The pinned dependency and its
  transitive packages were made available by symlinking another checkout's
  `.lake/packages` after confirming that every pinned revision in
  `lean/lake-manifest.json` matches, and by checking the dependency out at
  `1fffea44eece253cda1722568a3adfe34e822f03`. Nothing in the repository changed; the
  note is here because a reader reproducing the build will hit the same wall.

## What this does not establish

- The modified market is a computable belief sequence. `blocked`.
- `DistanceComplete` is not kernel-checked.
- Necessity of the safety condition. Open, and `PROOF_CLOSURE.md` §VI states where the
  one-way proof loses information rather than gesturing at it.
- The property-family classification is a reading of hypothesis shapes for all but two
  families; one family was not read at all.
- No tight size bound for the exact dual-distance family; only the crude one.
- The `Python` results are `test-supported` or `exhaustive-finite` over stated finite
  rational domains, never proofs of general statements.
- Nothing is registered in any `CLAIMS.md`, and no claim class was changed.

## Counts

- Lean: nine files under `lean/Workspace/Normativity/Contrib/`, eight of them new. 438
  results across the library audit to `[propext, Classical.choice, Quot.sound]`.
  Sorry-free. Nothing registered.
- Python: 365 tests in the round, up from 320; exact rationals throughout.
- Repository: `python3 tests/run.py` green over twelve projects;
  `python3 -m checkers.run` green.

## Outstanding maintainer actions

1. **Decide whether to file the two `blocked` obligations as `PRIORITIES.md` items** —
   the erasure of `MarketMaker(TF^L + E)`, and the kernel proof of `DistanceComplete`.
   Queued in `DECISIONS.md`. Nothing was filed: filing is the maintainer's, and this
   pass's dispatch did not name these items.
2. **Rule on the provisional names** listed in `DECISIONS.md`, in particular
   `Assessment`, `FiniteDetermined`, `DistanceComplete`, and the phrase *exact
   dual-distance presentation*.
3. **Decide the per-commit `Model:` trailer question**, in `DECISIONS.md`.
4. **Nothing to register.** No `CLAIMS.md` entry was added or changed, and no epistemic
   class was upgraded.

## Model attribution

- **Prompt-author-model:** unrecorded — the dispatch and its addendum were written
  outside this session.
- **Model:** Claude Opus 5 (Anthropic) — the executor.
- **Dates:** 2026-08-18.
