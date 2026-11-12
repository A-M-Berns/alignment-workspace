GPT-6 Astra (OpenAI) through `codex exec --skip-git-repo-check --sandbox read-only` (codex-cli 0.153.4), 2026-11-12, on `REVIEW-astra-request.md` with `StatisticalConditions.lean` at commit `743c5a8b`, `ExactConditions.lean`, `ExactConditionsReserve.lean` and `floor_toy.py` beside it. The reply's final message, verbatim:

The core inequalities and dichotomy are sound. The main overclaims concern what the frequency hypothesis establishes, whether the buyer is efficient, and whether the sequence-level mixture represents the fixed trading firm. I read the cited declarations and `DualCertifiedMarket`; `floor_toy.py --check` passed. I did not build Lean.

- **R1 — CORRECT.** `DualCertifiedMarket.P_range` permits substituting `P n` into `day_le`. Every trade then has zero value, giving `mu_n(p_n-c) ≤ eps_n`. This uses the actual cube-valued certificate, not merely the account ceiling.

- **R2 — CORRECT.** Nonnegativity gives each account contribution the lower bound `-c mu_n`. On days with clearance at least `delta`, R1 bounds the multiplier by `eps_n/delta`. Summing proves the stated estimate. Eventual clearance leaves only finitely many exceptional multipliers. The lower bound is **minus** the displayed positive constant.

- **R3 — CORRECT under the stated settlement and live-world assumptions.** The settled surplus grows at least as `(gamma-delta) ΣW`, and the open position loses at most one. The finite initial segment supplies a uniform lower bound; nonempty live sets supply witnesses for unboundedness above.

  Expressibility and rank control do **not** establish efficient computability of the trader. In particular, `φ : ℕ → Sentence` is unrestricted in the declaration. Producing `φ n` efficiently is a separate issue.

- **R — CORRECT, including the explicitly conditional corollary.** Summability gives `W_n → 0`, hence eventual clearance by `delta/2`; nonsummability invokes R3. `accountBounded_iff_unexploited` explicitly assumes `heff`. Neither declaration proves that frequency alone bounds the account, nor that the market is computable.

- **g1 — CORRECT with the corollary’s `heff` hypothesis retained.** Under threshold frequency, failure of every uniform account lower bound forces this buyer to exploit. Calling it an *efficiently computable* exploiter requires `heff`; the dichotomy itself supplies only a `Trader`.

- **g2 — CORRECT within that same scope.** A logical inductor cannot be exploited by the efficient threshold buyer, so its account must be bounded under the other hypotheses.

  “Exactly the right criterion” means the displayed conditional equivalence. It does not establish a statistical condition sufficient to construct a logical inductor. Moreover, `DualCertifiedMarket` includes rational quotes but no `ComputableMarket` field; the latter is separately required by `isLogicalInductor`.

- **g3 — WRONG.** The parenthetical claim that the normalized-multiplier frequency hypothesis is uninhabited except on all-true sequences is false. In `ExactConditionsReserve.lean`, `Bridge.Frequency` is an implication whose antecedent is nonsummability. Summable normalized stakes satisfy it automatically.

  A concrete sequence-level counterexample is
  `c=1/2`, `U=1`, `x_0=0`, `x_n=1` thereafter, `mu_0=1`, and `mu_n=0` thereafter. The ceiling holds, and the normalized stakes have finite support. Thus `Bridge.Frequency` holds for every positive `gamma`, despite the false first instance.

  Even the supplied one-loss market undermines the parenthetical: its ceiling bounds the sum of subsequent multipliers because every subsequent realized account increment is `(1-c)mu_n`. Consequently its multipliers, and hence its normalized multipliers, are summable.

  The eventual-slackness equivalence is defensible **under threshold frequency and `heff`**:
  ```
  summable W ⇒ eventual clearance ⇒ bounded account
             ⇒ no efficient exploitation ⇒ buyer does not exploit
             ⇒ summable W.
  ```
  It is not an unconditional equivalence between eventual clearance and summability of the threshold weights.

- **g4 — CORRECT as a statement of what remains unresolved by these results.** The dichotomy allows its exploitation alternative; frequency alone does not eliminate it. The toy does not establish that alternative for the pinned firm.

  “Near the floor infinitely often” is weaker than nonsummability. For example, prices approaching `c+delta` from below can produce positive but geometrically summable threshold weights.

- **X1 — OVERSTATED.** The boundedness conclusion is correct, but the proposed bound using `N0` covers only the **nonsummable** branch. `gain_bddAbove` explicitly splits into two cases:
  - Summable weights: use `c Σ'w`.
  - Nonsummable weights: use `c Σ_{i<N0}w_i`.

  For example, take `c=1/2`, `gamma=0`, `x_n=0`, and `w_n=2^{-n}`. `Along` holds vacuously, but there is no eventual frequency cutoff `N0`. No finite-prefix bound `c Σ_{i<N0}w_i` bounds all later gains. The theorem is sound; the gloss omits its summable case.

- **X2 — CORRECT at sequence level.** The formula matches `table_prior`, and each table has at most `R` nonzero entries. Its finite support makes any divergence-conditioned frequency requirement vacuous, after normalization if weights must lie in `[0,1]`.

  The declaration is a `noncomputable def` using `x n`. For each fixed `R`, its finitely many selected dates can be hard-coded into a program. That does **not** supply a uniformly computable family indexed by `R`, an effective enumeration at prescribed indices, or membership in the pinned firm at the desired weights.

- **X3 — CORRECT at sequence level.** The geometric-series identity, ceiling, and settled-account formula match the declarations. With `0<c<1` and infinitely many false instances, the account diverges downward when `theta≥1-c` and is uniformly bounded below when `theta<1-c`.

  This proves that summable mixture weights need not make the weighted component gain bounds summable. It does not identify the resulting stakes with market certificate multipliers.

- **h1 — OVERSTATED.** X correctly refutes the inference
  ```
  each component has a finite gain bound
  ⇒ their weighted mixture has a finite gain bound.
  ```
  It also shows that frequency restrictions on divergent weightings do not directly constrain finite tables.

  The extension to the fixed trading firm is unsupported. The selected tables and their assigned weights depend on the realized sequence; an effective firm enumeration need not realize that assignment. Nor has the aggregate multiplier been shown to be an admissible efficiently generated weighting.

  “A theorem must mention the weights or go through prices” is also too strong. Other structural assumptions could control the aggregate without displaying weights explicitly. The example defeats the proposed summation argument, not every possible account-bound theorem.

- **h2 — OVERSTATED, although its disclaimer about counterexample markets is correct.** The actual toy supports less than the subsequent description:
  - **E3:** there are 10 floor-binding days, of which 6 are false. Thus E3 does not demonstrate that floor prices identify precisely the false days. A finite wealth increase also does not establish exploitation.
  - **E5:** all 32 simulated prices equal the floor, and the buyer finishes with wealth about `13.47`. This establishes neither perpetual floor binding nor an account unbounded below.
  - **Pseudorandomness:** `scrambled(n)` is an explicit efficiently computable hash. The weighting that selects exactly its false outputs is efficiently computable and has zero selected truth frequency. Constant prices therefore do not make this sequence pseudorandom against all efficient weightings.

  If perpetual floor binding and the required limiting frequency were independently established, the threshold buyer’s exploitation would follow from R3. The finite simulation does not establish those premises.

- **h3 — OVERSTATED.** The algebra conditional on `j_R≈aR` is correct:
  `2^{-j_R}(1-c)^{-R}` has geometric factor approximately `1/(2^a(1-c))`. At equality, individual contributions need not grow, but their sum can still diverge.

  The enumeration premise is the problem. Program length, enumeration index, and the description length of the first `R` false dates are different quantities. No specified encoding justifies the claimed index estimate.

  In particular, an effective enumeration cannot generally place the exact tables of an incompressible sequence at indices `O(R)`: knowing `R` and such an index would let one recover the first `R` false dates by running the table, giving a short description of those dates. An arbitrary sequence-dependent rearrangement may achieve the desired placement while losing effective enumerability. The calculation establishes sensitivity of an abstract mixture, not enumeration dependence of the pinned market’s account.

**The most damaging objection to presenting R as “the statistical theorem”:** its frequency assumption is endogenous to the prices, and the conclusion deliberately retains exploitation as an alternative. Ordinary high truth frequency does not imply `Along` for the threshold weights. For example, a sequence with truth frequency `3/4` can have prices at the floor on false days and at `1` on true days; when `c+delta<1`, the threshold weighting selects only false days. R supplies a valid conditional converse to preservation, but no deduction of account boundedness from ordinary truth frequency. The one-loss witness establishes inhabitation, not the intended case with infinitely many losses. “No witness with infinitely many false instances exists” should mean *none is supplied*, not a proved impossibility.

**The most damaging objection to presenting X as “a refutation”:** its stakes satisfy a necessary scalar ceiling but are not shown to satisfy `DualCertifiedMarket.day_le` for the fixed universal firm. That missing connection is precisely where the firm’s buyers, effective enumeration, and price-dependent selection matter. X refutes an unrestricted summation argument. It does not exhibit a market satisfying the target statistical hypotheses with an unbounded account.
