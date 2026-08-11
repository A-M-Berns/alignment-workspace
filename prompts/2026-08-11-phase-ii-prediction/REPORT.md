# Report — Phase II Track H: signed versus magnitude prediction of the principal

Round directory: `prompts/2026-08-11-phase-ii-prediction/`
Authorizing item: `PRIORITIES.md` 21
Checkout: `alignment-workspace`, branch `round/2026-08-11-deference-corrigibility`, `beae92f`

**The pre-registered prediction is confirmed, and sharpened.** Ordinary market structure
forces signed calibration and not magnitude. The reason is not that the criterion is weak:
a trader's payoff is affine in the settlement vector, magnitude error is not, and the exact
gap between them is the market's own indecision — a quantity the market computes from its
own prices and no trader can reach.

## 1. Exact result

**S1 — ordinary LIC gives signed calibration only.** Three statements, all `lean-proved` in
`Workspace/Deference/Contrib/MagnitudePrediction.lean`.

*The signed functional is a trader payoff, exactly.* `unitTrader φ` buys one share of each
day's grade contract and holds it to settlement; its `def:exploitation` net worth on day `n`
**is** the signed error partial sum, with no remainder term (`unitTrader_netWorth_eq`). So
the criterion has an instrument for (S), and `signed_bddAbove_of_bddBelow` applies it: under
`IsLogicalInductor`, with the emission certificate, the signed sum cannot be bounded below
and unbounded above.

*The magnitude functional is not a trader payoff, and cannot be made one.* Let `P` be any
market that is the mean of a finite mixture of p.c. worlds — `CoherentMixture P`, meaning
`P n φ = ∑ⱼ wⱼ · (worldⱼ).payout φ` at every day and every sentence. Then for **every**
`Trader` and every day, the mixture-average of its net worth is exactly `0`
(`CoherentMixture.netWorth_eq_zero`). No hypothesis on the trader, on efficiency, on rank,
on what it reads. Consequently no trader's net worth dominates a magnitude sum that grows at
a positive rate in every world of the mixture (`magnitude_not_traderPayoff`).

The mechanism is one line of the pinned definition: `Strategy.value` is
`∑ᵢ eᵢ(𝓥) · (w φᵢ − 𝓥ₙ(φᵢ))`, and the coefficients `eᵢ` are functions of the price history
alone. Net worth is therefore affine in the payout vector `w`, whatever the coefficients
read and however long positions are carried. `|·|` is not affine. That is the whole
obstruction, and it is intrinsic to cash settlement, not an artefact of the feature grammar.

**The quantitative form.** For binary settlement the squared error splits exactly:

    (Y − p)²  =  (1 − 2p)(Y − p)  +  p(1 − p)

(`sq_error_split`; `sq_error_le_of_mem_Icc` gives `≤` for any settlement in `[0,1]`, the
direction that survives the LUV substitution). Summing, with `sharpTrader φ` = the day-`n`
grade contract held with coefficient `1 − 2p`:

    ∑_{i≤n} (Yᵢ − pᵢ)²  =  sharpTrader.netWorth P v n  +  ∑_{i≤n} pᵢ(1 − pᵢ)

exactly, in every world, on every day (`sharpTrader_netWorth_eq`). The first summand is a
trader payoff; the second is a function of `A`'s own prices. **The criterion drives the
first and has no instrument for the second**, and the second is what stands between signed
and magnitude control.

**S2 — the weakest additional tradeable instrument.** Two answers, and the first is the one
that matters.

*(a) No tradeable instrument gives magnitude control.* Adding contracts cannot help, because
whatever is added, net worth remains affine in the enlarged settlement vector and
`CoherentMixture.netWorth_eq_zero` still applies. The specific candidate that looks like it
should work — a self-referential contract settling at `|Y − p| ≥ q`, so that magnitude
becomes a payout rather than a functional of one — does work *as an instrument*, and what
the criterion then forces is that **its price** is calibrated. That is a calibrated
self-estimate of the magnitude error. It is measurement, not control. This is the sharpest
finding of the round and it is the one that should change the downstream design: the
certificate engine cannot be given (M); it can be given a calibrated estimate of (M) and
told to gate on it.

*(b) The cheapest instrument that upgrades signed to magnitude, conditionally, is already in
the grammar.* It is the coefficient `1 − 2p` on the existing grade contract —
`sharpEF φ n = add (const 1) (mul (const (−2)) (price φ n))`, rank `n` (`sharpEF_rank`),
reading only the day-`n` price of the contract it is applied to. No new contract family, no
new settlement assumption, no new emission obligation beyond the one every trader carries.
What it buys is `squaredError_bdd_of_sharpness_bdd`: under the criterion, if the market's
own indecision `∑ p(1−p)` stays bounded then the squared grade error is bounded on every
plausible world, hence the magnitude average vanishes. The side condition is about `A`'s
prices only, is evaluable at `t(n)`, and is **not** implied by the criterion —
`coin_sharpness` shows it failing at rate `1/4` per decision in the separating instance.

*One requirement the instrument does impose.* The identity needs `Y² = Y`. For the
skeleton's rational-valued `v⁺_n : Ω × Π_n → ℚ` it does not hold, so the grade contract must
be threshold-decomposed into indicator contracts before the instrument exists. The prompt
listed "a threshold decomposition of magnitude error" as a candidate; it is needed, but for
a different reason than expected — not to make `|·|` tradeable (nothing does) but to make
the *square* tradeable. Given the decomposition, `|Y − ŷ| ≤ ∑_q Δq · |1{Y≥q} − p_q|` with
`ŷ = ∑_q Δq · p_q` recovers the grade-level magnitude bound from the per-threshold ones.
That last chain is arithmetic and is **not** formalized here (§4).

## 2. Evidence class

`lean-proved` for every declaration listed in §3: 21 declarations, `lake build` green,
`#print axioms` on all of them, all reporting subsets of
`[propext, Classical.choice, Quot.sound]`. No `sorry`.

`squaredError_bdd_of_sharpness_bdd` is `lean-proved` **and** `unverified-nonvacuous` in the
sense of `AGENTS.md`'s Lean regime: it carries `EfficientlyComputable (sharpTrader φ)` and
ships no term inhabiting its full hypothesis package, exactly as
`FaithfulAcceleration.weight_not_divergent` does. It is not promotable to `CLAIMS.md`. Every
other theorem in the file is hypothesis-complete, and the ones with non-trivial hypotheses
ship witnesses (§6).

Nothing here is registered. No `CLAIMS.md` entry is proposed; that is a maintainer act under
demand-gating.

## 3. Files, declarations, checks

One new file: `lean/Workspace/Deference/Contrib/MagnitudePrediction.lean` (499 lines).
`lean/Workspace/Deference/Contrib/PROVENANCE.md` gains one row.

| declaration | what it says |
|---|---|
| `CoherentMixture` | finite mixture of p.c. worlds whose sentence-wise mean is the price, every day |
| `CoherentMixture.exists_weight_pos` | some world carries mass |
| `CoherentMixture.mixture_trades_eq_zero` | one strategy's trade list averages to zero |
| `CoherentMixture.netWorth_eq_zero` | **every trader's mixture-averaged net worth is exactly 0** |
| `CoherentMixture.exists_netWorth_nonpos` | no trader profits in every world of the support |
| `signedSum`, `magnitudeSum`, `squaredSum`, `sharpnessDeficit` | the four partial sums |
| `magnitude_not_traderPayoff` | **no trader's net worth dominates a positive-rate magnitude sum** |
| `unitTrader`, `unitTrader_netWorth_eq` | **the signed sum is literally a net worth** |
| `signed_bddAbove_of_bddBelow` | the criterion applied to the unit trader |
| `sharpEF`, `sharpEF_rank`, `sharpEF_denote` | `1 − 2p` as a rank-`n` element of the pinned grammar |
| `sharpTrader` | the grade contract held at coefficient `1 − 2p` |
| `payout_mul_self` | a `{0,1}` payout is its own square |
| `sq_error_split` | the pointwise residual identity |
| `sq_error_le_of_mem_Icc` | its one-sided form for `[0,1]` settlements |
| `sharpTrader_netWorth_eq` | **squared error = net worth + market indecision, exactly** |
| `squaredError_bdd_of_sharpness_bdd` | what the instrument buys, under the criterion |
| `magnitude_ge_of_price_limit` | **(M) forced to fail where the principal is unpredictable** |
| `coinWorld`, `coinPrices`, `coinMixture` | the two-point separating instance |
| `coin_magnitudeSum` | magnitude error `= 1/2` per decision, in both worlds |
| `coin_separates` | the separating witness, against the whole trader class |
| `coin_sharpness` | indecision `= 1/4` per decision — the necessity witness |
| `sharpnessDeficit_zero_witness` | the sharpness hypothesis is satisfiable |
| `signed_ne_magnitude` | the two functionals differ at one decision |

**Checks run.** `lake build Workspace.Deference.Contrib.MagnitudePrediction` — green,
1725 jobs, no errors, no warnings from this file. `lake env lean` re-elaboration of the file
— 21 `#print axioms` lines, two distinct axiom sets, both allowed. The repo-level
`tests/audit_axioms.py` was **not** run: it re-elaborates every file under `Workspace/`, and
this checkout has three other tracks working in it concurrently (four foreign `.lean` files
appeared in `Contrib/` during this round), so a repo-wide re-elaboration would report other
tracks' in-flight state rather than mine. Per-file re-elaboration is the same check
restricted to what this round wrote.

**Names confirmed against the installed source, not memory.** `EF` and its constructors,
`EF.rank`, `EF.denote_*`, `Strategy`, `Strategy.value`, `Trader`, `Trader.netWorth`,
`Trader.plausibleAssessments`, `Trader.Exploits`, `PCWorld`, `PCWorld.payout`,
`PCWorld.ConsistentWith`, `DeductiveProcess`, `EfficientlyComputable`,
`IsLogicalInductor.noExploit`, `History`, `Sentence`, `AsympEq` / `≈ₙ`,
`asympEq_iff_eventuallyWithin` — all read in
`.lake/packages/agentFoundations/LogicalInduction/Framework/{Criterion,Foundations,Asymptotics}.lean`.
Cited but not imported, with file and line: `lic_limitCoherence`
(`Properties/LimitCoherence.lean:777`),
`lic_learning_pseudorandom_frequency_of_historicalVerifiers`
(`Properties/Pseudorandomness.lean:3013`), `lic_wub` (`Properties/Pseudorandomness.lean:1901`),
`TheoryTruth` and `TheoryTruth.isBoolean` (`Properties/Calibration.lean:3435`, `:3439`).
Each statement was read in full before citation.

## 4. What was not established

1. **The separating market is not shown to be a logical inductor.** `coinMixture` prices
   every atom at `1/2` and is mixture-coherent by construction; nothing here shows it
   satisfies `IsLogicalInductor` for any deductive process. The negative answer does not
   rest on it: `CoherentMixture.netWorth_eq_zero` quantifies over all traders at any
   mixture-coherent market, and `magnitude_ge_of_price_limit` handles an actual inductor.
   But the cleanest possible witness — "here is a logical inductor at which (M) fails" — is
   not delivered, and I do not claim it.
2. **Layer 3's hypothesis package is not discharged.** `magnitude_ge_of_price_limit` takes
   `hconv` — price converging to a frequency `p` — as a hypothesis. It is verbatim the
   conclusion of `lic_learning_pseudorandom_frequency_of_historicalVerifiers`, and `hbin` is
   verbatim `TheoryTruth.isBoolean`'s, so the composition is a two-line `exact`. I did not
   perform it: that import chain (`Properties/Calibration`, `Properties/SelfTrust`,
   `Properties/Pseudorandomness`, ~10k lines) is not built in this checkout and building it
   is precisely the broad rebuild the dispatch forbids while another track builds. The
   satisfiability of `PseudorandomFrequency` and of
   `PseudorandomFrequencyInfrastructureWithHistoricalVerifiers` is in any case **not**
   established anywhere — by me or by the dependency — so even composed, Layer 3 would be a
   conditional.
3. **The Cesàro form of (S) is not proved here.** `signed_bddAbove_of_bddBelow` is the
   Dutch-book form, strictly weaker than `(1/N)∑(Y−p) → 0`. The Cesàro statement is
   `lic_wub` in the pinned dependency, and it carries real hypotheses — `RpnSentenceCodes`,
   `FeedbackTraderEmissionSigns`, `FeedbackTruthSequence`, `hworld`. So "(S) is forced" is
   accurate **modulo the dependency's representation hypotheses**, not unconditionally. What
   this round adds on the signed side is the structural fact that the signed functional is a
   net worth on the nose.
4. **The threshold-decomposition chain is not formalized.** `|Y − ŷ| ≤ ∑_q Δq·|1{Y≥q} − p_q|`
   and the reduction of the menu maximum to a sum over `|Πₙ|` are stated in §1 as arithmetic
   and proved nowhere. Both are routine; neither is checked.
5. **`squaredError_bdd_of_sharpness_bdd` ships no inhabitation witness** for its full
   package. `hsharp` alone is witnessed (`sharpnessDeficit_zero_witness`);
   `IsLogicalInductor` and `EfficientlyComputable` are not.
6. **(M) restricted to the menu maximum was analysed per-contract only.** Every theorem here
   is about one contract sequence `φ : ℕ → Sentence`. The `max_{π∈Πₙ}` of the dispatch's (M)
   is handled by the union bound in §1, which is not formalized, and which degrades with
   unbounded menus.

## 5. Assumptions added

`CoherentMixture` is a new definition, not a substitution: it is a specialization of the
conclusion of `lic_limitCoherence` to finite support, and it is inhabited (`coinMixture`).

Two hypotheses are named and undischarged, both of a class already standing in this
repository: `EfficientlyComputable` (type `(c)`, the `dd:fuel` model of the pinned
dependency) and `IsLogicalInductor` (type `(b)`, a citation).

No modelling substitution is introduced. The propositional substrate — grade contracts as
`{0,1}` sentences rather than rational-valued objects — is the pinned dependency's standing
substitution, and this round makes its cost *explicit* rather than absorbing it:
`sq_error_split` needs binarity, `sq_error_le_of_mem_Icc` is what remains without it, and
§1's threshold decomposition is the price of the rational-valued grade the skeleton actually
carries.

## 6. Counterexamples and necessity witnesses

All exact rationals; no floats anywhere in the file.

**6.1 The separating instance.** Two p.c. worlds — one making every atom true, one making
every atom false — with weights `1/2, 1/2`, and the market that prices every sentence at
their mean. On atoms the price is exactly `1/2` (`coinPrices_atom`). Then:

* every trader's mixture-averaged net worth is `0`, on every day
  (`CoherentMixture.netWorth_eq_zero` at `coinMixture`) — (S) holds *exactly*, not in the
  limit;
* the magnitude error is exactly `1/2` per decision **in both worlds** (`coin_magnitudeSum`)
  — so it is not an artefact of averaging over worlds;
* no trader's net worth dominates it up to a constant (`coin_separates`).

This is the trader-class-respecting instance `PRIORITIES.md` 21 names as the acceptable
negative deliverable, in Lean rather than as checker data.

**6.2 Necessity of the sharpness hypothesis.** At the same instance the indecision grows at
`1/4` per decision (`coin_sharpness`), so `hsharp` of `squaredError_bdd_of_sharpness_bdd`
fails there. The hypothesis cannot be dropped, and the theorem is not vacuous in the
direction that would make it useless.

**6.3 Satisfiability of the sharpness hypothesis.** A market pricing every contract at `0`
has zero deficit (`sharpnessDeficit_zero_witness`). Degenerate, and labelled as such — it
witnesses satisfiability, nothing more.

**6.4 The two functionals differ at a single decision.** `signed_ne_magnitude`: `−1/2`
against `1/2`. The smallest form of §6.1, and a guard against a reader concluding that (S)
and (M) coincide because both partial sums are `0` at the mixture average.

**6.5 Relation to the wave-1 instance.** `prompts/2026-08-11-deference-certificates/REPORT.md`
§6.4 exhibits per-intervention signed error exactly zero with override mass `1/2`. That
instance shows (S) does not imply (M) *pointwise*. §6.1 here shows the criterion does not
close the gap either — the same separation, promoted from an arithmetic fact about one model
to a statement about every trader in the pinned class.

## 7. Deviations

1. **Snapshot.** The dispatch names `23fc1aa`; the checkout's `HEAD` on the branch is
   `beae92f`, two commits later, and the orchestrator's dispatch message names `beae92f`. I
   worked against `HEAD`. `beae92f` is "Phase II: dispatch H, I, K, M against the repaired
   build" and `23fc1aa` is the build-coverage fix; neither touches the binding inputs
   (`FINITE_MODEL_SKELETON.md`, `FaithfulAcceleration.lean`, the pinned dependency).
2. **The prompt's (S) is written `v̂⁺ − v⁺` and (M) as `|v̂⁺ − v⁺|`.** In the market model the
   natural orientation is settlement minus price, `Y − p`. I use that throughout; the sign
   is immaterial to both statements and to every theorem here, but the report and the file
   are consistent in the market orientation and differ from the dispatch's.
3. **`lic_learning_pseudorandom_frequency_of_historicalVerifiers` is cited, not imported.**
   Reason in §4.2: importing it is a ~10k-line rebuild of `Properties/Calibration`,
   `Properties/SelfTrust` and `Properties/Pseudorandomness`, which the dispatch's build
   constraint forbids while track M may be building. The exact composition is stated in the
   file's Layer-3 docstring so a later round can perform it in one step.
4. **`tests/audit_axioms.py` was not run repo-wide.** Reason in §3. Per-file re-elaboration
   was run instead and is reported in full.
5. **The round produced Lean, which the dispatch permits conditionally ("only if you produce
   compiling Lean").** It compiles; `lean/Workspace/Deference/Contrib/` is therefore in
   scope, and `PROVENANCE.md` in that directory is updated as `AGENTS.md`'s provenance
   mechanics require. That file is shared with other tracks; if another track edits it in
   the same wave the rows merge cleanly but the maintainer should check.
6. **`REPORT.md` and `FOR_HUMANS.md` could not be written by the executor.** Its harness
   blocks report-shaped files from a subagent. Both were returned to the orchestrator as
   text, as the dispatch's fallback instructs, and written by the orchestrator.

## 8. Provisional names

All new; none proposed for permanence.

`CoherentMixture` · `signedSum` · `magnitudeSum` · `squaredSum` · `sharpnessDeficit` ·
`unitTrader` · `sharpEF` · `sharpTrader` · `coinWorld` · `coinPrices` · `coinMixture` · and
the theorem names listed in §3.

Two are worth the maintainer's attention specifically. **`sharpnessDeficit`** names the
quantity `∑ p(1−p)`; the forecasting literature calls the same object *sharpness* (or its
complement, *resolution*), and if the programme is going to talk about it repeatedly the
name should be chosen deliberately rather than inherited from this round.
**`CoherentMixture`** is close enough to the dependency's `LimitCoherence` vocabulary to be
confusing; it is a finite-support, every-day condition, which limit coherence is not.

## 9. Maintainer decisions surfaced

**9.1 (M) is not available, and the certificate engine's design has to absorb that.** This
is a value decision, not a gap. The options the mathematics leaves are: gate on `A`'s own
sharpness `∑ p(1−p)` (checkable at `t(n)`, forced by nothing); or add a self-referential
magnitude contract and gate on its calibrated price (measurement, still not control); or
weaken the downstream theorem to carry a predictability hypothesis on the principal as a
named assumption. There is no fourth option that the criterion supplies.

**9.2 Which of those three the deference line takes**, and whether a predictability
hypothesis on the principal is acceptable at all. `FINITE_MODEL_SKELETON.md` §3 says
explicitly that a `t(n)`-measurable `v⁺_n` — a perfectly predictable principal — is
permitted and must not be ruled out. It says nothing about assuming *approximate*
predictability, which is what magnitude control needs. That is the decision.

**9.3 The obstruction relocates the open question to the settlement slot.** Magnitude
control is not a property of the trader class; it is a property of how much of the
principal's grade is knowable at `t(n)`. `FINITE_MODEL_SKELETON.md` §5 is where that lives.
Whether the deference line wants to open the settlement slot is a maintainer call.

**9.4 Decision 9.4 of the certificates round is now answered.** That round asked "which
trust relation will WP-D actually deliver, `L¹` or signed?" The answer is signed, and `L¹`
is not obtainable from the criterion at any tolerance. The certificate's (TR-ε) hypothesis
therefore has no antecedent in a Dutch-book argument, and its status changes from "to be
derived" to "to be assumed or gated".

**9.5 Whether to register anything.** Nothing here is registered; demand-gating makes that a
maintainer act. The natural candidate is `magnitude_not_traderPayoff` together with
`coin_separates` as the `PRIORITIES.md` 21 negative deliverable.

## 10. Next recommended theorem

**Compose Layer 3.** One `exact`, once `Properties/Pseudorandomness` is built:
`magnitude_ge_of_price_limit` applied to
`lic_learning_pseudorandom_frequency_of_historicalVerifiers`'s conclusion with
`TheoryTruth.isBoolean` supplying `hbin`. It turns "the criterion does not force (M)" into
"the criterion forces ¬(M), at rate `min p (1−p)`, wherever the principal is unpredictable
at frequency `p`" — a strictly stronger negative, at near-zero proof cost, in an isolated
round whose only expense is the build.

**Then, and only if 9.1 goes the sharpness way:** state the certificate's grade clause with
`sharpnessDeficit` as an explicit gate, and prove the Cesàro corollary
`squaredError_bdd_of_sharpness_bdd → (1/N)∑|Y − p| → 0` (Cauchy–Schwarz; routine). That is
the smallest change that gives the certificate engine something the criterion actually
delivers.

**Not recommended:** proving that `coinMixture` is a logical inductor. It is a research
question — it asks whether a maximally-undecided market with an empty deductive process
resists every efficiently computable trader — and the negative answer does not need it.

## 11. Executor-model attribution

Executed by **Claude Opus 5 (Anthropic)**, exact model id `claude-opus-5`, as a dispatched
subagent of the Phase II wave.
Prompt author: **GPT-5.6 Sol (OpenAI)**.
Orchestrator: **Claude Opus 5 (Anthropic)**.
Date: 2026-08-11. Review status: `ci-only` — no maintainer has read it.

---

## Outstanding maintainer actions

1. **Decide 9.1** — which of the three options the certificate engine takes, given that (M)
   is unavailable. Everything downstream of `prompts/2026-08-11-deference-certificates/`
   (TR-ε, L2, the certificate's grade clause) is blocked on this.
2. **Decide 9.2** — whether a predictability hypothesis on the principal may be assumed, and
   if so, record it in `DECISIONS.md` as a modelling commitment before any track uses it.
3. **Decide §8's two names** — `sharpnessDeficit` and `CoherentMixture` — or accept them as
   provisional for one more round. Command: edit the declarations in
   `lean/Workspace/Deference/Contrib/MagnitudePrediction.lean` and the rows in §3 of this
   report.
4. **Decide 9.5** — whether to file a `CLAIMS.md` entry for
   `Workspace.Deference.Contrib.MagnitudePrediction.magnitude_not_traderPayoff` and
   `…coin_separates`, class `lean-proved`, against `PRIORITIES.md` 21. Contributors may not
   register.
5. **Run the repo-wide gates once the wave's tracks are merged**:
   `python3 tests/audit_axioms.py` and `python3 tests/run.py`. This round ran only the
   per-file re-elaboration (§3, §7.4), because four tracks share the checkout.
6. **Check `lean/Workspace/Deference/Contrib/PROVENANCE.md` for merge damage** — this round
   appended a row to a file other tracks in the same wave may also have appended to.
7. **Close `PRIORITIES.md` 21** with the negative answer, or say what would reopen it. The
   item's stated acceptance is met in the stronger of the two forms it allows: a
   trader-class-respecting instance is delivered `lean-proved` rather than `witness-checked`.
