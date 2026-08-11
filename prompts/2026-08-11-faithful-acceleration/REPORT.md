# Report — Track A, faithful acceleration / FAF integration

Round: `prompts/2026-08-11-faithful-acceleration/`, answering `PRIORITIES.md` item 14.
Repository at `990a822`, branch `round/2026-08-11-deference-corrigibility`.

## 1. Exact result

Three things, in decreasing order of strength.

**(a) A compiling partial port with an exact dependency map.** Six of the ledger's
Movement-I statements now re-elaborate inside this repository against the pinned toolchain
(`leanprover/lean4:v4.31.0`) and the pinned FAF commit
`1fffea44eece253cda1722568a3adfe34e822f03`, in
`lean/Workspace/Deference/Contrib/InheritedAlgebra.lean` and
`lean/Workspace/Deference/Contrib/FaithfulAcceleration.lean`. Nothing is strengthened; each
transcribed statement names the inherited declaration it restates. The ledger's evidence
caveat — "attested by the inherited audit, not rebuilt here" — is now discharged for those
six and remains for the rest (§4).

**(b) The strongest inherited Movement-I theorem, stated exactly.** It is
`FaithfulAccel.soft_total_trust_doublysoft`
(`projects/deference/note-dump-2026-06-27/lean/FaithfulAcceleration.lean:203`):

```
theorem soft_total_trust_doublysoft (v p a : ℕ → ℝ) (t ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (hbias : Tendsto
      (fun n => (∑ i ∈ Finset.range n, dsWeight t ε δ (a i) (p i) * (v i - a i))
              / (∑ i ∈ Finset.range n, dsWeight t ε δ (a i) (p i))) atTop (𝓝 0))
    (hbdd : ∃ M, ∀ n, (∑ i ∈ Finset.range n, dsWeight t ε δ (a i) (p i) * (v i - p i)) ≤ M) :
    ¬ Tendsto (fun n => ∑ i ∈ Finset.range n, dsWeight t ε δ (a i) (p i)) atTop atTop
```

Its hypotheses classify as: `hε`, `hδ` — parameters; the support conditions `hone`/`hmis`
— **(a) derived**, discharged from `dsWeight`; `hbias` — **(b) LI citation**, A's
calibration; `hbdd` — **(c) modelling substitution**, the no-Dutch-book criterion applied to
an unmodelled trader. That last classification is the inherited audit's §3.1 and it is
correct.

**(c) A new theorem replacing `hbdd` by the pinned dependency's criterion.**
`Workspace.Deference.Contrib.FaithfulAcceleration.weight_not_divergent` builds the
doubly-soft gate as a `LogicalInduction.EF` of rank `n`, builds the round-trip trader as a
`LogicalInduction.Trader`, proves the exact accounting identity, and derives the
bounded-value conclusion from `IsLogicalInductor` instead of assuming it. `hbdd` is gone.
What replaces it is `EfficientlyComputable (accelTrader …)`, which is **not discharged** —
that is the exact residual market/trader gap (§4).

Doing the port produced four corrections to the inherited record. They are the substantive
findings of this round and are stated in §6 and §4.

## 2. Evidence class

`lean-proved` for every declaration listed in §3, in the sense of `AGENTS.md`'s classes:
kernel-adjudicated, free of `sorry`, `#print axioms` within `[propext, Classical.choice,
Quot.sound]`.

**No entry is proposed for `CLAIMS.md`.** `weight_not_divergent` has no term inhabiting its
full hypothesis package, so by the Lean regime it is `unverified-nonvacuous` and sits in a
contribution namespace rather than the record. The ported statements are re-verifications of
inherited results, not new claims, and registering them would need a maintainer decision
about what a "port of an inherited statement" is a claim *of*.

## 3. Files, declarations, checks

**Files written** (the only files this track touched):

- `lean/Workspace/Deference/Contrib/InheritedAlgebra.lean`
- `lean/Workspace/Deference/Contrib/FaithfulAcceleration.lean`
- `lean/Workspace/Deference/Contrib/PROVENANCE.md`
- `prompts/2026-08-11-faithful-acceleration/REPORT.md`, `FOR_HUMANS.md`

**Checks run**, all green:

```
cd lean && lake build                                          # 1716 jobs, unchanged
cd lean && lake build Workspace.Deference.Contrib.FaithfulAcceleration \
                      Workspace.Deference.Contrib.InheritedAlgebra   # 1834 jobs
python3 tests/audit_axioms.py        # 38 results across 5 files, all within the allowance
python3 tests/audit_axioms.py --self-test
```

`lake build` on the default target reports the same job count as before the round: the new
modules are not reachable from `lean/Workspace.lean`, which is a specification-layer file
this track may not edit. See **Outstanding maintainer actions 1**.

**Declarations — ported (Layer 1).** Each restates the named inherited declaration.

| here | inherited source |
|---|---|
| `InheritedAlgebra.decomposition` | `Deference.decomposition` |
| `InheritedAlgebra.witness_identity` | `DeferenceConverse.witness_identity` |
| `InheritedAlgebra.value_iff_totalTrust` | `DeferenceConverse.value_iff_totalTrust` |
| `InheritedAlgebra.AntiExpert.{stationary, TT_negative, value_fails}` | `DeferenceConverse.AntiExpert.*` |
| `InheritedAlgebra.value_iff_totalTrust_asymptotic` | `DeferenceConverseAsymp.value_iff_totalTrust_asymptotic` |
| `InheritedAlgebra.value_asymptotic` | `DeferenceAsymp.value_asymptotic` |
| `FaithfulAcceleration.roundProfit_ge` | `FaithfulAccel.round_profit_ge` |
| `FaithfulAcceleration.profitPartialSum_ge` | `FaithfulAccel.profit_partial_sum_ge` |
| `FaithfulAcceleration.profitDiverges` | `FaithfulAccel.profit_diverges` |
| `FaithfulAcceleration.violationNotPersistent` | `FaithfulAccel.violation_not_persistent` |
| `FaithfulAcceleration.profitDiverges_nonvacuous` | `FaithfulAccel.profit_diverges_nonvacuous` |
| `FaithfulAcceleration.{softInd, dsWeight, dsWeight_pos_imp_fst, dsWeight_pos_imp_snd}` | `FaithfulAccel.{softInd, dsWeight, …}` |

**Declarations — new (Layer 2).** `gateA`, `gateH`, `weightEF`, `weightEF_rank`,
`weightEF_denote`, `holdEF`, `tradeEF`, `tradeEF_rank`, `accelTrader`, `position_sum_eq`,
`banked`, `bias`, `weight`, `accelTrader_netWorth_eq`, `netWorth_sub_banked_abs_le`,
`accel_partial_sum_ge`, `exists_lower_bound_of_tendsto_atTop`, `weight_not_divergent`,
`dsWeight_pos_witness`, `netWorth_ne_banked_witness`.

**Dependency map — which FAF declarations the port stands on.** Every name below was
confirmed to exist in `lean/.lake/packages/agentFoundations` at the pinned commit.

| FAF declaration | file | used for |
|---|---|---|
| `EF`, `EF.rank`, `EF.denote`, `EF.rank_*`, `EF.denote_*` | `Framework/Criterion.lean` | the weight as a legal feature |
| `clip01`, `clip01_denote`, `clip01_rank`, `efMin` | `Properties/Hysteresis.lean` | the clipped ramp |
| `clipVal_nonneg`, `clipVal_le_one`, `clipVal_pos_imp` | `Properties/Hysteresis.lean` | `softInd` facts, reused not re-proved |
| `Strategy`, `Strategy.value`, `Trader`, `Trader.netWorth` | `Framework/Criterion.lean` | the trader |
| `Trader.plausibleAssessments`, `Trader.Exploits` | `Framework/Criterion.lean` | `def:exploitation` |
| `IsLogicalInductor`, `.noExploit`, `.price_mem_Icc` | `Framework/Criterion.lean` | the criterion, applied |
| `EfficientlyComputable` | `Framework/Criterion.lean` | the named residual |
| `PCWorld`, `PCWorld.payout`, `PCWorld.Holds`, `DeductiveProcess` | `Framework/Criterion.lean` | worlds and stages |
| `AsympEq` (`≈ₙ`), `AsympLE` (`≲ₙ`), `AsympEq.{refl,symm,trans,asympLE,finsetSum}`, `AsympLE.{trans,trans_asympEq}`, `ConvergesTo` | `Framework/Asymptotics.lean` | the entire inherited limit calculus |

**Consulted and cited but not used**, because they are the general-lookahead and efficiency
machinery the port stopped short of: `AffineCombination.roundTrip`, `roundTrip_netWorth`
(`Framework/Affine.lean`); `hystTrader`, `hystTrader_netWorth`, `hystTrader_ecTok`,
`oscillation_exploitable_hyst`, `buyIndEF_tokenStream_comp` (`Properties/Hysteresis.lean`);
`ecTok_of_segStream` (`Framework/Computable.lean`); `EfficientlyComputable.ofTokenEmitter`,
`IsLogicalInductor.noExploitTok` (`Framework/RpnEmission.lean`);
`AffineCombination.lic_wub` (`thm:wub`), `lic_wubaff`, `DeferralFunction`,
`WeightingSupportedOnDeferralImage`, `TheoryTruth` (`Properties/Pseudorandomness.lean`,
`Properties/SelfTrust.lean`); `recurringunbiasedness_of_historicalVerifiers`,
`weightedBias`, `HasLimitPoint` (`Properties/Calibration.lean`);
`exists_logical_inductor`, `LIA_is_logical_inductor` (`Construction/LIACompiler.lean`).

## 4. What was not established

**The residual market/trader gap, exactly.** `weight_not_divergent` assumes
`EfficientlyComputable (accelTrader φ t ε δ a)`. That is the whole remaining distance between
"the criterion applies to this trader" and "the criterion is assumed to have applied". It is
not bookkeeping trivia: FAF's `dd:fuel` efficiency model is a disclosed type-`(c)`
substitution in its own right, and discharging it for this trader additionally requires
emitting the exogenous rational sequence `a` (A's quotes) under the same polynomial clock.
The route exists — `hystTrader_ecTok` is the worked pattern and `buyIndEF_tokenStream_comp`
handles rung-varying rational constants — and was not attempted this round.

**`hbias` has no FAF endpoint, for a precise reason.** FAF's closest endpoint is
`AffineCombination.lic_wub` (`thm:wub`), whose conclusion shape is right — full convergence,
`weightedBias … ≈ₙ 0`, not merely a limit point as in the recurring-unbiasedness variants.
But it requires `TheoryTruth φ DP truth`: the feedback target must be the completed-theory
truth stream, a world-settled `{0,1}` value. The faithful-acceleration target is
`E^H_{f(n)}(X)`, H's future *credence* — continuous, and on the relevant sentences never
settling. There is no FAF theorem about calibration to a non-settling target, and the
inherited notes' own `faithful-acceleration-scope.md` argues informally that on the
quote-referencing family such calibration is *unsatisfiable*. The formal interface confirms
the informal finding: this is not a missing lemma, it is a missing kind of theorem.

**FAF's market model is single-market.** `EF.price` reads the one history the trader trades
against. There is no vocabulary in the pin for "A's price of a sentence about H's price", so
the cross-process content of Movement I cannot be stated in FAF's types at all. The port
substitutes an exogenous computable rational sequence for A's quotes (§5, assumption A3).

**Ledger rows re-elaborated vs. inspected.** Confirmed by re-elaboration: `decomposition`,
`value_iff_totalTrust` (finite-exact, with its anti-expert witness),
`value_iff_totalTrust_asymptotic`, `value_asymptotic` (tower ⟹ Value, asymptotic), and the
`soft_total_trust_doublysoft` chain's arithmetic core. Confirmed by source inspection only,
not re-elaborated: `softmax_lower_bound` (50 lines of `exp` analysis;
`DeferenceExtra.softmax_lower_bound`), `value_of_CM` (tower ⟹ Value, finite-exact),
`CM_implies_immodest`, the `DeferenceArgmax` family, and everything in
`TowerAndAcceleration.lean` including `two_faces_distinct`. I read each of these in full and
found no discrepancy with the ledger, but reading is not the kernel.

**One precision the ledger does not record.** `softmax_lower_bound` proves the crude
`(card J)·δ` bound, not the paper's tight `δ·log(card J)`. The inherited docstring discloses
this; the ledger row ("proved outright; was a hypothesis, became a theorem") does not. The
row is not wrong — the `δ → 0` argument needs only the crude bound — but a reader taking the
row as "the paper's softmax bound is proved" would be over-reading.

**A shape precision on `value_iff_totalTrust`.** The finite-exact biconditional is the
universal closure of a *pointwise* algebraic equivalence (`value_witness_iff_totalTrust_mass`
holds for each `(X, s)` separately). It is genuinely proved and genuinely non-vacuous, but it
is not a derivation relating two independently characterised global properties. The
asymptotic version has the same shape: both arrows are one `linarith` after unfolding `≲ₙ`,
over a hypothesis (`hLoe`) that identifies the followed-strategy price with the linear
combination. The ledger's "algebra alone" is accurate; "the direct LI counterpart of DDB's
Theorem 2.2" in the inherited docstring is the phrase that invites over-reading.

**Not attempted.** Movements II–VII; any strengthening of the inherited theorem; a general
lookahead `f` (§6, finding F2); an inhabitation witness for `IsLogicalInductor` (available as
`exists_logical_inductor`, but `Construction/` was not built this round and it would not
complete the package anyway).

## 5. Assumptions added

Every assumption the new theorem carries beyond the inherited one, with its class.

- **A1 (a).** `hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)` — each deductive stage
  admits a consistent world. FAF's `DeductiveProcess` does not carry this as a field; FAF's
  own `oscillation_exploitable_hyst` and `lic_wub` state it identically. Needed only for the
  unbounded-above half: without it the plausible-assessment set can be empty.
- **A2 (c), undischarged.** `hEC : EfficientlyComputable (accelTrader φ t ε δ a)`.
- **A3 (c), disclosed.** A's forecasts enter as a rational sequence `a : ℕ → ℚ` hard-coded by
  the trader, not as prices in a second market. This is the single-market restriction of
  `EF` (§4), and it is what makes A2 depend on `a` being polynomial-time computable.
- **A4, deliberate restriction.** The lookahead is one day: `v n = P (n+1) φ`. The inherited
  statement carries a general `f`. See F2.
- **A5.** Prices in `[0,1]`, obtained from `IsLogicalInductor.price_mem_Icc` — derived, not
  assumed.

## 6. Corrections, counterexamples and necessity witnesses

**F1 — the inherited audit's finding 7 is dischargeable, and is discharged here.** That
finding reads: "'continuous ⇒ legal `𝒞_H`-expressible-feature trader' remains a modeling
step", severity Medium. Against the pin it is not a modelling step: the doubly-soft gate is
literally an element of FAF's `EF` grammar (`weightEF`), and `weightEF_rank` proves it has
rank exactly `n`, so it is legal on its own day. `weightEF_denote` proves it denotes the
inherited `dsWeight`. **Recommend downgrading finding 7 to closed for this weight.** It
remains open for any weight not expressible in `EF`.

**F2 — `hbdd` is not what the criterion delivers, and the gap is the lookahead.** The
criterion bounds a trader's *net worth*, not the banked partial sum. `accelTrader_netWorth_eq`
gives the exact relation:

```
netWorth P v n = dsWeight … (a n) (P n φ) * (v.payout φ − P n φ) + banked P φ t ε δ a n
```

The correction term is the still-open position. For a one-day lookahead it is bounded by `1`
(`netWorth_sub_banked_abs_le`), so `hbdd` is recoverable up to an additive constant and the
inherited argument survives. For a general lookahead `f` the correction is the value of all
simultaneously open round trips, bounded by `sup_n #{i ≤ n : f i > n}` — unbounded when the
lookahead grows. So the inherited `hbdd`, *read as what the criterion supplies*, is sound
only when concurrently open positions are bounded. This is not a hypothetical worry: FAF's
own feedback theorem `lic_wub` carries exactly the device that rules it out,
`WeightingSupportedOnDeferralImage W P f` together with `StrictlyIncreasingDeferral f` — the
weighting is supported on the image of the deferral function, so at most one round trip is
ever open. The inherited statement has no counterpart of that condition.

*Necessity witness:* `netWorth_ne_banked_witness` exhibits a market, a world and a day where
net worth and banked value differ, so the correction term is not removable.

**F3 — `hbdd` assumes the criterion's conclusion while skipping its precondition.**
`Trader.Exploits = BddBelow (plausibleAssessments) ∧ ¬ BddAbove (plausibleAssessments)`, so
`IsLogicalInductor` yields `BddAbove` only *given* `BddBelow`. The inherited `hbdd` asserts
the bounded-above half outright and never states, let alone discharges, the bounded-downside
obligation. In the port that obligation is a real proof step: `BddBelow` is derived from the
per-day bound plus calibration, via `eventually_half_weight_le` and
`exists_lower_bound_of_tendsto_atTop`. A trader whose downside is unbounded is simply outside
the criterion's reach, and no amount of banked upside would matter.

**F4 — the inherited limit calculus is redundant against the pin.** The inherited modules'
`Approx` and `AsympLE` are *definitionally* FAF's `AsympEq` (`≈ₙ`) and `AsympLE` (`≲ₙ`);
`approx_sum` is `AsympEq.finsetSum`; `AsympLE.trans_approx` is `AsympLE.trans_asympEq`. The
port re-proves none of it, and `InheritedAlgebra.lean` compiles with FAF's vocabulary
substituted verbatim. Any future port should not carry the inherited calculus across.

**Non-vacuity, as far as it goes.** `dsWeight_pos_witness` shows the gate is not identically
zero, guarding against the degenerate reading in which the conclusion holds because the
constructed trader never trades. `profitDiverges_nonvacuous` (ported) is a non-constant
witness for the divergence hypotheses. Neither is an inhabitation witness for
`weight_not_divergent`, and none is available while A2 stands.

**A near-duplicate, disclosed.** FAF has `prefixSum_mul_eq_abel`
(`Properties/Calibration.lean`) — Abel summation in the inclusive-prefix arrangement.
`position_sum_eq` is the position-chain arrangement `∑ (h(i+1) − h i)(y − p i)`, which is not
that statement, though the two are inter-derivable. Flagged rather than left for a reader to
discover.

## 7. Deviations

1. **The prompt's parent snapshot is stated as `ec7d6cc`.** The working tree is at `990a822`
   (`ec7d6cc` is its parent). No content this track read differs between them; recorded
   because the prompt is kept verbatim.
2. **Two Lean files instead of one.** The prompt permits `lean/Workspace/Deference/Contrib/`
   without prescribing a file count. Splitting the inherited-algebra transcription from the
   new market bridge keeps "what was already established" separable from "what this round
   added"; a reviewer will want to weigh them differently.
3. **`FOR_HUMANS.md` added.** Not requested by the prompt; required by `AGENTS.md`'s
   dual-register rule, which binds every round.
4. **`PROVENANCE.md` added under `lean/Workspace/Deference/Contrib/`.** Same reason —
   `AGENTS.md` provenance mechanics ask for one per results directory, and none existed.
5. **The inherited tree was read, never edited**, as instructed. It was also not built: it
   pins `leanprover/lean4:v4.27.0` and its own Mathlib, and building it would have meant a
   second full Mathlib build on a machine where the prompt forbids concurrent ones. The port
   is the substitute, and it re-elaborates statements rather than the inherited files.

## 8. Provisional names

All new names are provisional and marked as such in both files' headers. New: `gateA`,
`gateH`, `weightEF`, `holdEF`, `tradeEF`, `accelTrader`, `position_sum_eq`, `banked`,
`bias`, `weight`, `accelTrader_netWorth_eq`, `netWorth_sub_banked_abs_le`,
`accel_partial_sum_ge`, `exists_lower_bound_of_tendsto_atTop`, `weight_not_divergent`,
`dsWeight_pos_witness`, `netWorth_ne_banked_witness`, and the namespaces
`Workspace.Deference.Contrib.FaithfulAcceleration` and
`Workspace.Deference.Contrib.InheritedAlgebra`.

Renamed in transcription (inherited name → name here, so that a reader cannot mistake the
transcription for the inherited declaration itself): `round_profit_ge` → `roundProfit_ge`,
`profit_partial_sum_ge` → `profitPartialSum_ge`, `profit_diverges` → `profitDiverges`,
`violation_not_persistent` → `violationNotPersistent`, `profit_diverges_nonvacuous` →
`profitDiverges_nonvacuous`. Ledger-row names (`decomposition`, `witness_identity`,
`value_iff_totalTrust`, `value_iff_totalTrust_asymptotic`, `value_asymptotic`) are kept
identical so the ledger's rows point at something.

`banked` / `bias` / `weight` are the inherited note's `P` / `C` / `W`. Those single letters
collide with `P : History` in the market layer, which is why they were spelled out.

## 9. Maintainer decisions surfaced

1. **Whether a re-elaborated inherited statement is registrable, and as what.** The ported
   declarations are `lean-proved` in this repository, but they are not new results, and
   demand-gating says nothing enters the registry except in answer to a filed item. Item 14
   asked for the port; it did not say the port becomes a claim.
2. **Whether `weight_not_divergent` should be pursued to a full inhabitation witness.** That
   means discharging `EfficientlyComputable` for `accelTrader`, a scoped but real
   emission-calculus project (§10). Until then it cannot leave `unverified-nonvacuous`.
3. **Whether the ledger's Movement-I rows should be re-marked.** Six rows now have a stronger
   basis than "the inherited audit attests it"; the rest do not. The ledger has no vocabulary
   for that distinction, and inventing one is a specification-layer act.
4. **Whether the inherited audit's finding 7 is closed** (F1). This is a judgement about the
   inherited audit's severity table, which lives in a consolidated tree.
5. **The lookahead question raised by F2** sits upstream of the settlement decision the
   roadmap already reserves: a lookahead that grows is what makes "H's future credence" a
   forecastable target at all, and it is exactly what breaks the bounded-open-position
   accounting.

## 10. Next recommended theorem or experiment

In value order.

1. **Discharge `EfficientlyComputable (accelTrader φ t ε δ a)`** for a polynomial-time
   computable `a : ℕ → ℚ`. Scoped, and the pattern is fully worked in FAF:
   `hystTrader_ecTok` for the shape, `buyIndEF_tokenStream_comp` for the rung-varying
   rational constants, `ecTok_of_segStream` for the capstone, then
   `EfficientlyComputable.ofTokenEmitter`. This is the single step that turns
   `weight_not_divergent` from `unverified-nonvacuous` into a candidate for the record, and
   it needs no new mathematics — it needs emission bookkeeping.
2. **Generalise the port to a strictly increasing deferral `f` with supported weighting**,
   reusing `AffineCombination.roundTrip` / `roundTrip_netWorth` and FAF's
   `WeightingSupportedOnDeferralImage`. This is what makes the lookahead real rather than one
   day, and F2 says it cannot be done without that support condition.
3. **State the cross-process object.** The genuine blocker is that FAF has no two-market
   vocabulary. The smallest useful step is a definition of "market `A` forecasts a
   `[0,1]`-valued feature of market `H`" plus the statement of what calibration to a
   non-settling target would have to say — not a proof, a *statement*, so that the missing
   theorem in §4 becomes something one could look for. Discharging `hbias` from any LI
   theorem is the standing open problem; the scope note's gate argument suggests it is false
   in general and true only off the quote-referencing family, which is a theorem shape nobody
   has written down.

## 11. Executor-model attribution

- **Prompt-author model:** GPT-5.6 Sol (OpenAI), per the round's `PROMPT.md`.
- **Executor model:** Claude Opus 5 (Anthropic), model id `claude-opus-5`. Self-identified.
- **Orchestrator model:** Claude Opus 5 (Anthropic), per the round's `PROMPT.md`.
- **Dates:** dispatched and executed 2026-08-11.
- **Review status:** `ci-only`. No maintainer has read any of it.

---

## Outstanding maintainer actions

1. **Add the two modules to the library root**, or decide they should stay out of the default
   build. `lean/Workspace.lean` is a specification-layer file this track may not edit, so the
   new modules build only when named explicitly and are invisible to `lake build`. The exact
   change:

   ```
   # in lean/Workspace.lean, after the existing imports
   import Workspace.Deference.Contrib.InheritedAlgebra
   import Workspace.Deference.Contrib.FaithfulAcceleration
   ```

   Then re-run `cd lean && lake build` and `python3 tests/audit_axioms.py`. Both pass today
   with the modules named explicitly; the axiom audit already covers them, because it globs
   `lean/Workspace/**/*.lean` rather than following imports.

2. **Decide item 1 of §9** — whether any ported declaration is registered in `CLAIMS.md`, and
   under which `PRIORITIES.md` item. No registry edit was made.

3. **Decide whether to re-mark the six confirmed Movement-I rows** in
   `projects/deference/notes/CORRIGIBILITY_PAPER_LEDGER.md`, whose evidence caveat currently
   applies uniformly to all of them. `notes/` is specification space; this track made no edit.

4. **Decide whether the inherited audit's finding 7 is closed** (F1), and whether that
   warrants an edit to the consolidated tree's `AUDIT.md` §5 severity table or only a
   `DECISIONS.md` entry. Editing a consolidated tree is a maintainer act with a stated reason.

5. **File a follow-up item for §10.1** (discharging `EfficientlyComputable` for
   `accelTrader`) if the port is to be finished. Nothing in `PRIORITIES.md` currently covers
   it: item 7 is the general market/trader modelling gap, which the pinned dependency already
   closes; what is left is this specific emission certificate.
