Reviewed head `d3d3542e` against `73edb7de`. No Lean build or test suite was run; the worktree is unchanged.

1. **Score-side test: outcome (b) is not established as stated.**

   In [WarrantInductorScoreSide.lean:150](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-07-score-side-binding/lean/Workspace/Normativity/Contrib/WarrantInductorScoreSide.lean:150), market equality is definitional:

   ```lean
   theorem market_unchanged (σ : Sentence) (ϖ : ℝ) :
       (scoreSide σ ϖ).schedule.market DP = WB.market DP := rfl
   ```

   `scoreSide` explicitly stores `WB` (line 141). This proves that an added scoring function reads the same market, not that independently constructed markets coincide.

   The bundle claim is proved, but narrowly:

   ```lean
   theorem no_conduct_row (σ : Sentence) (ϖ : ℝ) (n : ℕ) :
       ∀ c ∈ (scoreSide σ ϖ).schedule.bundle n, c.row ≠ conductRow
   ```

   Lines 166–204 check that no existing row has constant `1/3`. Thus the selected row is absent; there is no semantic predicate classifying *all* conduct rows. The unchanged bundle was chosen by construction.

   **Strength necessity is only prose.** The proof of `before` uses the strength and applicability rows, but no theorem deletes the strength row, constructs the resulting market, or supplies the advertised counterexample. Proof dependence establishes sufficiency, not necessity. The reduced-region counterexample is plausible; it still needs a checked witness and careful distinction between losing a guarantee and changing the realized decision.

   The assessment connection is also missing. At lines 71–82:

   ```lean
   structure RefrainWhileLive where
     shortfall : Sentence

   def ShortfallAt (_n : ℕ) : Prop :=
     OccurrenceIntegrity.Fate.live ∈
       (state₀.account 0 (by simp [state₀, Initial.state, start])).fates

   theorem shortfall_assessed (n : ℕ) : ShortfallAt n := account_live 0 _
   ```

   The date is ignored, the account never changes, and this proposition never enters the scoring proofs. Nothing relates arbitrary `σ` to `ShortfallAt`, even as an explicit interpretation hypothesis. This is stronger than merely lacking generability or accurate pricing: the priced sentence has no formal assessment meaning.

   The charge is free, with explicit restrictions:

   ```lean
   theorem before (σ : Sentence) (ϖ : ℝ) (_hϖ : 0 ≤ ϖ)
       (hsmall : ϖ * shortfallPrice (scoreSide σ ϖ) 4 ≤ 19/240) :
       (24/25 : ℝ) ≤ scoreGate (scoreSide σ ϖ) 4 0
   ```

   `same_question_two_realizations` repeats that bound; `after` requires nonnegative charge. The detailed report states this correctly, but its categorical verdict and wiki exposition omit the qualification. Its suggested “vacuity” scenario is impossible: prices lie in `[0,1]`, so every `0 < ϖ ≤ 19/240` satisfies the bound.

   The other registered result is genuinely proved, for the **chosen** compilation:

   ```lean
   theorem conduct_on_prices_conflicts :
       ¬ ∃ x, ((NB 4).bundle ++
         [(⟨Cite.str 99, conductRow⟩ : CitedRow (Cite 5) 5)]).Region x
   ```

   This does not establish that every price-side representation of the obligation conflicts.

2. **Solvency: an honest algebraic instantiation, without an enforcer instantiation.**

   [WarrantSolvency.lean:71](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-07-score-side-binding/lean/Workspace/Normativity/Contrib/WarrantSolvency.lean:71) defines:

   ```lean
   def UnitPosition (v : ℕ → ℝ) : Prop :=
     ∀ t, v t = S.realized t - S.held t
   ```

   The registered statement, lines 110–114, does **not** assume `UnitPosition`:

   ```lean
   theorem bounded_iff_frequency (B : ℝ) :
       (∀ n, -B ≤ liability S.realized S.held n) ↔
         ∀ n, S.c * S.undefeatedCount n - S.trueCount n ≤ B
   ```

   The separate `solvent_iff` transfers this identity to arbitrary `v` under `UnitPosition`. `Schema` contains a rational and two Boolean sequences; no settlement process, settlement deadline, or calibrated trader appears.

   `UnitPosition` is not generally plausible for the actual enforcer. Its positions are intensity times violation times row coefficients; they vanish when the row is satisfied ([EnforcementStrategy.lean:143](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-07-score-side-binding/lean/Workspace/Normativity/Contrib/EnforcementStrategy.lean:143)). A unit position bought at strength generally has nonzero settled gain even then. The report acknowledges the missing connection, but “timeliness is the shape of the data” supplies no timing guarantee.

3. **Conflict audit: the mathematical generality matches the certificate type.**

   [WarrantSolvency.lean:204](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-07-score-side-binding/lean/Workspace/Normativity/Contrib/WarrantSolvency.lean:204):

   ```lean
   theorem suspect_in_bundle {Q : Type*} (B : Bundle Q d) (c : FarkasCert d m)
       (hv : ∀ i, B.Allowed (c.row i)) (x : Fin d → ℚ) (hx : InCube x) :
       ∃ i, 0 < c.mult i ∧ (∃ cr ∈ B, cr.row = c.row i) ∧ ¬ (c.row i).Sat x
   ```

   This is **every point has some violated supported row**, not one identified row violated everywhere. The underlying result covers arbitrary rational vectors; the cube assumption excludes cube constraints as the culprit. Calling the culprit a “mis-admission” additionally requires an admission standard demanding validity at the chosen point; bundle membership alone does not supply that interpretation.

4. **Eight-world fixture: arithmetic correct; defeat integration incomplete.**

   [RobustWarrant.lean:154](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-07-score-side-binding/lean/Workspace/Normativity/Contrib/RobustWarrant.lean:154) proves:

   ```lean
   theorem posterior_signal : post μ Aev Yev = 3/4
   theorem posterior_contrary : post μ (Aev ∩ Cev) Yev = 3/5
   ```

   The masses are `3/8 ÷ 1/2 = 3/4`, and `1/8 ÷ 5/24 = 3/5`; the concurring case is `6/7`. Lines 314–358 establish:

   ```lean
   theorem robustStrength_all :
       robustStrength μ Aev Yev Uall Uall_nonempty = 3/5

   theorem robustStrength_defeated :
       robustStrength μ Aev Yev Udef Udef_nonempty = 3/4

   theorem robust_meet (y : ℚ) :
       (3/5 ≤ y ∧ 2/5 ≤ 1 - y) ↔ y = 3/5
   ```

   These are minima over explicitly selected families. Declaring the challenge a defeater means deleting `Cev` from `Uall`; no repository defeat mechanism performs that deletion.

   Actual repository rules are used at lines 208–216:

   ```lean
   theorem kept_under_challenge :
       settleOutcome Fch occ.form = .kept ∧
       settleForm Fch occ = some [specialize Fch occ.form.row]

   theorem not_undercut : ¬ undercut DocketState.quiet occ
   ```

   However, there is no theorem applying `Grounds.survivors` to this fixture. With `occ.cites = .none`, completing that proof should be straightforward, but it is absent. Also, `valid_at_signal` actually states `RowValid ... univ`, and `invalid_at_contrary` uses `Cev`; the separate posterior theorems supply the signal-conditioned numbers.

   `Robust` is the right finite-family conditional bound **given an externally specified undefeated family**. Its soundness lemma is exactly the promised algebraic restatement:

   ```lean
   theorem robust_sound
       (h : Robust μ A Y c U) (hE : E ∈ U)
       (hpos : 0 < mass μ E) (hA : 0 < mass μ (A ∩ E)) :
       RowValid μ A Y c E
   ```

   It divides the defining inequality by positive `mass μ E`; it establishes no independent admission or defeat soundness.

5. **Standing: positive admission is arranged; rejection has real content.**

   [AdmissionByStanding.lean:85](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-07-score-side-binding/lean/Workspace/Normativity/Contrib/AdmissionByStanding.lean:85) chooses each holder to equal its issuer. Consequently:

   ```lean
   theorem admitted_by_allocation (h : List ℕ) (e : Fin 2) :
       protocolS.Admitted h e () := rfl
   ```

   That fixture admits everything by construction. Nevertheless, the predicate is not universally vacuous: changing the holder proves non-admission. The registered statement is:

   ```lean
   theorem reallocated_entitles_nothing (O : ObligationState protocolS₁ wAnchor)
       (Expresses : Unit → SeedStatics.Form 5 → Prop)
       (E : Entitlement O grounds Expresses)
       (o : WarrantEntitlement.Occurrence 5) (ho : o ∈ grounds) :
       E.origin o ≠ 0
   ```

   This excludes **origin 0**, not entitlement of the same grounds through another origin. `Expresses := True` permits that alternative. No concrete `O` and `E` under `protocolS₁` are supplied; `entitlementS` inhabits the different protocol under `J₀`.

6. **Registry and exposition.**

   All six registered declarations are actual propositions proved as theorems; none is a definition or `True` placeholder. Their witness and item coverage differ:

   | Claim | Witness coverage | Attention coverage |
   |---|---|---|
   | `scoreside.same-question-two-realizations` | Zero-charge recipe in prose; no explicit complete hypothesis-package witness | Conditional contribution to 35; necessity unproved |
   | `scoreside.conduct-on-prices-conflicts` | Closed statement; concrete `conductCert` | Selected compilation at item 35 |
   | `solvency.bounded-iff-frequency` | Concrete schemas and bounded/unbounded witnesses | Touches 61; its summability requirement remains |
   | `solvency.conflict-names-suspects` | Certificate, allowed-row proof and cube witness exist separately | Supports 133; does not answer its requested rule |
   | `robust.eight-world-strengths` | Closed fixture, including `Uall_nonempty` | Supports 133; rule and compilation remain open |
   | `standing.reallocated-entitles-nothing` | Missing witness under `J₁` | Only admission part of 128(a) |

   The standing registration fails the explicit full-hypothesis witness requirement in [AGENTS.md:568](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-07-score-side-binding/AGENTS.md:568). The report’s “inhabited … vacuously” is not such a witness.

   Item 128(a) explicitly requires both `Admitted` **and** `Expresses` to carry content, so “clause (a) landed” is too strong ([item-128.md:37](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-07-score-side-binding/graph/nodes/item-128.md:37)). Its `closed` status predates this PR, but the edited node leaves that inconsistency unreported.

   The wiki distinguishes registered results from auxiliary `LEAN` declarations, but **the prose exceeds them**. Most seriously, [Normativity.md:225](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-07-score-side-binding/wiki/Normativity.md:225) says “a conflict among solvent rows cannot occur.” False: two contradictory rows enforced on only one instance each have bounded cumulative liability. Simultaneous validity at one point—not solvency—is what excludes a Farkas certificate.

   The robust graph bridge also attributes both strengths to a statement of record proving only `3/5`; `3/4` is a separate theorem ([bridge:12](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-07-score-side-binding/graph/nodes/robust.eight-world-strengths.bridge.md:12)). Register the conjunction or narrow the bridge.

   The report’s limitations omit the missing assessment interpretation, strength-necessity witness, grounded-survivor theorem, and `J₁` witness.

7. **Standards.**

   - The undeclared substantive shortfall is claiming the dispatch’s outcome discrimination without the necessity test. Using a new `softGate` construction instead of the requested decision-component functions is also not declared as a deviation.
   - New conceptual names are marked provisional in the report and PR body.
   - [REPORT.md:16](/Users/anson/hub/repos/alignment-workspace/.claude/worktrees/round-2026-11-07-score-side-binding/projects/normativity/rounds/2026-11-07-score-side-binding/REPORT.md:16) “corrects” a dispatch reference to `PRIORITIES.md` that the committed dispatch does not contain.
   - The exposition inventory and concluding merge recommendation repeat earlier material; the latter repeats the unsupported outcome-(b) claim.
   - The [PR body](https://github.com/A-M-Berns/alignment-workspace/pull/140) and all six `Model:` trailers agree on Claude Fable 5.1. All commits omit the separately required `Prompt-author-model:` trailer; this is missing attribution, not a conflicting executor identity.

Ranked defects:

1. **Blocking:** Outcome (b) is promoted without a strength-necessity witness, and the “assessed shortfall” sentence is formally disconnected from assessment.
2. **Blocking:** The wiki’s “solvent rows cannot conflict” claim is false.
3. **Blocking:** The registered standing theorem lacks its required hypothesis-package witness.
4. **Should-fix:** Complete the grounded-survivor fixture; narrow item 128 completion and the robust registry bridge; propagate the charge qualification.
5. **Note:** Correct the impossible charge-vacuity scenario, false dispatch correction, missing prompt-author trailers, and repetitive report prose.

The report’s largest oversell is that the score-side test **discriminates the three outcomes and establishes (b)**. It proves a conditional charged-gate result on a reused market, without proving either the claimed necessity or the assessment interpretation.

**fix-then-merge**

The registered mathematics can support narrower claims, but the current report and wiki promote conclusions beyond those statements. Add the missing witnesses and semantic connection, or explicitly narrow the claims and leave those obligations open.