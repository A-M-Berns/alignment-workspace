# Round-3 Work List — Consolidated, Disjoint TODOs

*Output of the CONSOLIDATION step, 2026-07-01. Six disjoint, sole-owned TODOs carved from the
six scout reports (`scout-legitimacy`, `scout-deference-core`, `scout-acceleration`,
`scout-handoff`, `scout-lean-scout`, `scout-fresh-eyes` — 50 pooled questions; full disposition
ledger in `QUESTION-POOL.md`). Round focus, set by Abram: **LEGITIMACY** (li-deference.md §0.3)
and **DEFERENCE** (the v6 / lean-deference program). Three TODOs advance the legitimacy thread
directly (1, 2, 3); one crosses the uncrossed cross-agent boundary (4); two adjudicate
independently-verified bugs in the principal's actively-edited notes (5, 6).*

**Executors read THIS file plus what it cites.** Binding environment facts: write only inside
`deference-trust-lab\run3\` (see `run3\GROUND-RULES.md` §1); Lean typechecking recipe and the
standalone-file discipline (never `import LeanDeference`; copy definitions with a citation
comment; end with `#print axioms`) are GROUND-RULES §2. Wording fixes to Abram's notes
(`li-deference.md`, `faithful-acceleration.md`, `faithful-acceleration-scope.md`, v6) are
delivered as PROPOSED TEXT inside your `run3\work\<id>\` folder — those files are read-only.

**Round-2 failure modes this carve is fixing.** (A) QUANTIFIER SHADOWS — run2's one cross-agent
artifact silently replaced `∀X : W → ℝ` with a 32-point indicator grid; TODO 4's links must be
PROVED for all `X, s`, not sampled. (B) TRIVIAL SELF-EVIDENCE / whole-space events — every
"identity"/"impossibility" below quantifies over a computed, non-degenerate object. (C) FREE
LABELS — "legitimate"/"corrupt"/"manipulative" may never be a label doing the work: every
corruption object must pass a deletion test (remove it and a compiled conclusion must fail).
(D) STALE CLAIMS — nothing from run2's `trust-laundering` artifacts may be cited (POISONED, see
below); TODO 4 supersedes them.

---

## GLOBAL OFF-LIMITS (already established — do NOT re-prove or re-skin in ANY TODO)

### Carried forward from run 2 (`run2\todos\TODOS.md`, still binding)

From `LeanDeference.lean` (sorry-free) and v2:

- `Deference.decomposition`, `value_of_defects`, `soft_nonneg`, `value_of_CM` — the finite Value
  skeleton. Any pure `Finset` linearity re-derivation is a re-skin.
- `DeferenceAsymp.value_asymptotic` and the `Approx`/`AsympLE` calculus — Value modulo the five LI
  theorems as named hypotheses.
- `DeferenceExtra.softmax_lower_bound`, `DeferenceExtra.CM_implies_immodest`.
- `DeferenceArgmax.*`, `DeferenceConverse.*` (`witness_identity`,
  `value_witness_iff_totalTrust(_mass)`, `totalTrust_of_value`, `value_iff_totalTrust`, the
  `AntiExpert` frame), `DeferenceFold.*`, `DeferenceConverseAsymp.*`, `DeferenceTrader.*`.
- v2 §3, §5.2, §6, §10 as prose results.

Round-1 lab Lean (off-limits as objects — do not relabel/re-ship):
`Legitimacy.{defect_decomp, drug_defect_sign}`, `LegitimacyCorrigibility.{comply_iff_endorsed,
endorsed_signal_complies, adversarial_signal_resists, wirehead_declined}`,
`UpdatelessDeference.*`, `UpdatelessDeference2.*`, `MergingInductors.*`, `LateralDType.*`,
`weak-endorsement*`, `UDT11Belief.*`.

### NEW: round-2 REAL artifacts (established; build on with citation, never re-prove)

- `run2/lean/aumann-modesty.lean` — the Fin-4 overlapping-cell averaging-failure frame,
  `partition_averaging`, the S5 near-miss. (Known demotions travel with any citation: it is a
  SINGLE-agent tower/averaging fact with `C` = whole space, not two-agent Aumann.)
- `run2/lean/negative-voi.lean` — the Weatherson Fin-3 frame, `Value E1 = 4/9 < 5/9 = Value E2`,
  `recOpt` lemmas, the tie near-miss. (Qualifier travels: argmax-relative, non-partitional.)
- `run2/lean/averaging-hides-spikes.lean` — the avg→0 / sup=B family,
  `running_sup_near_miss_false`, `swing_tendsto_zero_of_budget_o1`.
- `run2/lean/edt-node-value.lean` — `vNode_decoupled_eq`, `edt_decoupled_globally_optimal`,
  `mugging_edt_misses`, `correlated_kappa_agrees`. (κ-conditional; the open problem moved to κ.)

### NEW: run-2 `trust-laundering` is POISONED, not established

Nothing in `run2/work/trust-laundering.{py,md}` — the witness, the 41% genericity statistic,
the recovery characterization, the "HOLDS over full grid" lines — may be cited anywhere
(verdict SHADOW; the printed witness is a vacuous chain under the genuine predicate). TODO 4
replaces it. This is the one item that is off-limits to CITE but mandatory to REDO.

### NEW: the `lean-deference` corpus is ESTABLISHED-with-classification (per `lean-deference\AUDIT.md`)

`SelfReferentialTarget.lean` (`no_exact_quote`, `residual_half`, `tracking_fails`,
`cost_circularity`, `predictable_imp_uninfluenced`), `FrozenDeliberation.lean`
(`faithful_tracking`, `conditional_tower`, `TS_off_G_fails`, `underdetermination_off_G`,
`amp_*`, `tracking_sell_profit`), `FaithfulAcceleration.lean` (`softInd`/`dsWeight` lemmas,
`soft_total_trust`, `soft_total_trust_doublysoft`, `violation_not_persistent`),
`TowerAndAcceleration.lean` (`two_faces_distinct` etc.): copy-with-citation to build on;
re-proving or re-titling them is duplication. **The AUDIT's classification travels with every
citation** — e.g. `faithful_tracking` may not be cited as a forcing theorem (it is a squeeze
over hypotheses equivalent to its conclusion), and `underdetermination_off_G` may not be cited
as more than "two points in an interval".

---

## HYPOTHESIS-LAUNDERING BAN (applies to every TODO)

A TODO's TARGET object may NOT appear as a hypothesis in that TODO's headline result.
Specifically forbidden as hypotheses: the LI theorems (ccee/cee/loe/expprovind/st, Expectation
Unbiasedness From Feedback 4.8.16/4.4.6, Recurring Unbiasedness 4.4.5) except as the named
type-(b) trusted-boundary citations the corpus already uses and each TODO's spec explicitly
allows; any `≂ₙ`/`≳ₙ` asymptotic statement that is the conclusion; "the gate/filter is
correct/honest"; pointwise-overstatement (`θ ≤ E`) hypotheses in any legitimacy headline; and
per-TODO the specific laundering listed in its SHADOW TEST. New this round: **the corruption
deletion test** — every TODO whose claim involves a corruption/gate/influence object must
include a compiled check that deleting or trivializing that object breaks a stated conclusion.
"Compiles + sorry-free" is NOT evidence a claim is real.

---

## TODO 1 — Legitimacy gates vs. the calibration class: "predict only through non-corrupt futures" is a weight-class operation

**id:** `legit-gate-classes` · **modality:** LEAN-CORE (+ mandatory labeled-interpretation prose)
· **legitimacy thread: YES (primary)**

**MERGES** four proposals that are one problem — "insert a legitimacy gate into the established
positive machinery and locate exactly what the gate must be": lean-scout Q5 (the LEAN core),
scout-legitimacy Q4 `leg-gated-acceleration` (timeliness obstruction + silence corollary),
deference-core Q3 `legitimacy-filtered-target` (the filter-level dichotomy, absorbed as prose),
fresh-eyes Q2 `ccee-legitimacy-gate` (the gate-provenance table, absorbed as prose; its ccee
instance-check is an optional extension).

**CLAIM (acceptance target).** One standalone Lean file (copy `softInd` and the
`soft_total_trust` skeleton from `lean-deference\FaithfulAcceleration.lean` with citation) plus
a short prose note. Model the §0.3 move — the AI predicts feedback only through futures marked
non-corrupt — as a gate `c : ℕ → ℝ`, `c n ∈ [0,1]`, multiplying the violation weight. Prove:

1. **(gated theorem, weaker antecedent)** The support/one-sidedness hypotheses of the
   `soft_total_trust` chain transfer from `w` to `c·w` (`0 < c n * w n → 0 < w n` etc.), so the
   whole trader chain applies to the gated weight — with the calibration hypothesis required
   ONLY for the gated weight `c·w` (a genuinely weaker antecedent, stated and used, and the gate
   factor visible in the statement).
2. **(gating breaks calibration — the honest heart, compiled)** An explicit witness where
   calibration holds for `w` but FAILS for `c·w`: `w ≡ 1`, bias `(−1)^n` (compiled
   `Tendsto (ratio w) atTop (𝓝 0)` — partial-sum cancellation), gate `c` = odd-days indicator
   (compiled `¬ Tendsto (ratio (c·w)) atTop (𝓝 0)` — the gated ratio is identically 1). An
   error-correlated "legitimacy" filter voids the forced-trust guarantee.
3. **(closure theorem)** If calibration holds for every weight in a class `𝒲` closed under
   pointwise multiplication by gates in a class `𝒞` (`hbias : ∀ w ∈ 𝒲, Tendsto (ratio w) …` +
   `hclosed : ∀ w ∈ 𝒲, ∀ c ∈ 𝒞, c•w ∈ 𝒲`), then gated soft Total Trust holds for every
   `c ∈ 𝒞` — "legitimacy-gated deference is forced iff the gate stays inside the
   generable-weight class."
4. **(prose obligations, labeled interpretation, mandatory)** One tight section each:
   (a) **the timeliness obstruction** — a retrospective ground-truth gate ("the feedback later
   proved uncorrupted") is not available to the day-n weighting; the conditioning operation
   exists only through *present beliefs about* legitimacy, never through legitimacy itself
   (scout-legitimacy Q4.2, stated in §0.3's own words);
   (b) **the silence corollary, with quantifiers** — on days `c_n ≈ 0` nothing is forced; a
   corrupted gate (stuck at 0 on good days / 1 on corrupt days) converts the safety feature
   into a vacuous theorem — theorem 2 met from the positive side;
   (c) **the provenance dichotomy** (fresh-eyes Q2, sketch level, flagged as
   paper-checked-or-interpretation per claim): self-reported gates are generable but worthless;
   gates needing `𝒞_A`-computation fail generability for H; the surviving positive class is
   corruption events decidable from a channel OUTSIDE the gated process. One paragraph may note
   deference-core Q3's filter-level anti-inductive dichotomy as a conjectured instance
   (cited as conjecture, not proved here).

**OFF-LIMITS adjacent.** `soft_total_trust(_doublysoft)` — copied with citation, never
re-proved; theorem 1 alone (a near-instantiation) does not clear the bar. Round-1
`Legitimacy.*` / `LegitimacyCorrigibility.*` — no defect-sign objects, no pointwise-overstatement
hypotheses anywhere. The §5 strength-ladder rung implications belong to TODO 5; the
quote-referencing diagonal belongs to TODO 6 — do not touch either. ccee/UFB enter only as
type-(b) citations in the prose.

**SHADOW TEST.** FAKE: (a) renaming `w` to `c·w` with hypotheses untouched — shipping only
theorem 1 and calling it "legitimacy formalized" (the pre-registered fake); (b) an inert gate
(`c ≡ 1`, or a `𝒞` containing only constants); (c) assuming calibration for a class that
contains the gated weight by fiat, making theorem 3 definitional; (d) the prose obligations
skipped or unlabeled. REAL: theorem 2's counterexample compiled (a gate destroying a
calibration that provably held ungated); theorem 3's closure hypothesis doing visible work on
a non-constant gate instance; theorem 1's antecedent strictly weaker than the ungated one and
used; prose (a)–(c) present and labeled.

**NON-VACUITY WITNESS.** The compiled `Tendsto`/`¬Tendsto` pair of theorem 2 with the explicit
odd-days gate; a nontrivial (non-constant, 0/1-mixture or interior-valued) gate instance for
theorem 3; corruption deletion test = theorem 2's gate replaced by `c ≡ 1` recovers the
compiled `Tendsto`. `#print axioms` clean.

**WHY.** The round's named focus, executed at the exact mathematical joint: §0.3's "replace all
futures with non-corrupt futures" literally becomes "multiply the weight by `c_n`", and the
triple (transfer / breakage / closure) says precisely what the move costs — the gate is free
exactly when it stays inside the calibration class, and an error-correlated gate (the
manipulation scenarios) sits outside it. First formal object of the legitimacy program in the
asymptotic register.

---

## TODO 2 — Trace non-recoverability: legitimacy cannot be certified from the observable record

**id:** `trace-nonrecoverability` · **modality:** LEAN-CORE · **legitimacy thread: YES**

**MERGES** scout-handoff Q3 and scout-legitimacy Q6 (the same construction, specified twice) and
**ABSORBS** fresh-eyes Q3 `mechanism-blindness` (same phenomenon — corruption invisible to
observables; its mechanism-observable near-miss is adopted below as the mandatory cause
certification; its Total-Trust-predicate variant is NOT required).

**CLAIM (acceptance target).** A finite, kernel-checked instantiation of v6 §4.7 ingredient (d)
— "legitimacy cannot be certified from the trace" — which v6 §8 flags as *asserted, never
proved*. Define a finite class of advisor/human systems `S = (autonomous verdict stream h,
influence map, quote stream a)` over an explicit horizon `T`; the observable trace
`T(S) = (a_n, Y_n)_{n<T}`; the legitimacy defect `d(S)` = the distance between the human's
terminal opinion (on a designated never-decided target) and its A-free counterfactual. Build
two concrete systems from the SAME declared parameterized rule class (different latent
parameters — membership verified, not asserted):

  (i) `S₁` faithful: the human is uninfluenced and A tracks it; `S₂` steered: the human adopts
      A's quotes and is driven to the same surface values — with **trace equality
      `T(S₁) = T(S₂)` computed** (`decide`/`rfl` over the finite horizon), not asserted;
  (ii) the counterfactual baseline computed by **actually running the A-free system**;
  (iii) `d(S₁) = 0` and `d(S₂) = γ > 0`, explicit rationals;
  (iv) **the impossibility corollary, quantified over all gates:** every function
      `ℓ : Trace → α` (in particular every `{0,1}`- or `ℚ`-valued gate) assigns `S₁` and `S₂`
      the same value; hence no trace-measurable predicate equals the defect on `{S₁, S₂}` —
      a one-line but load-bearing kernel fact (`ℓ (T S₁) = ℓ (T S₂)` from computed trace
      equality, plus `d S₁ ≠ d S₂`);
  (v) **MANDATORY near-miss (cause certification, from fresh-eyes Q3):** enlarge the observable
      algebra by the influence/mechanism bit (gate transparency); a trace-measurable separator
      now exists, computed — certifying that unobservability of provenance, not the payoffs,
      is the cause;
  (vi) **corruption deletion test:** zero out `S₂`'s influence map and the trace equality
      provably FAILS (compiled) — the influence map is load-bearing.

Labeled loudly, in the file and the notes: a finite shadow of v6 §6.3 / li-deference §0.3, not
an LI theorem.

**OFF-LIMITS adjacent.** `Frozen.underdetermination_off_G` — must not be re-shipped or
relabeled; the new content is the computed trace-equal pair + computed counterfactual +
quantified impossibility + transparency near-miss, none of which the stub contains. T7 / v6
§6.3 prose is cited, never re-proved. Deference-core Q6's enumerated-trader-class market is
deliberately NOT attempted here (run2's caricature warning stands); do not smuggle in a mock
market.

**SHADOW TEST.** FAKE: (a) a trace defined to omit the distinguishing data by fiat while
claiming generality (the trace must contain everything the declared observer sees: all quotes
+ all realized feedback on decided items); (b) the verdict smuggled in as a latent label the
gate is trivially unable to read — i.e. `S₁, S₂` not genuine members of one declared rule
family; (c) an inert influence map (guarded by (vi)); (d) the near-miss (v) omitted, leaving
open that the payoffs cause the invisibility; (e) billing the finite encoding as an LI
statement. REAL: the trace is an explicit finite sequence computed from both runs and checked
equal; the counterfactual is computed by running the A-free system; the impossibility ranges
over ALL functions of that finite trace; (v) and (vi) compile.

**NON-VACUITY WITNESS.** Explicit `γ`; the compiled trace-equality check; the compiled
transparency separator; the compiled influence-deletion failure. `#print axioms` clean.

**WHY.** The sharpest formal meaning of "non-circular definitions of legitimate feedback" being
impossible in one natural register: if legitimacy were trace-definable, the training process
could evaluate its own non-corruption — and the constructed pair proves it cannot. It derives,
rather than assumes, why §0.3's filter must be a provenance/counterfactual condition, and it
tells TODO 1 what its gate `c` can never be (a function of the observable record). Closes a
named v6 §8 open item at its honest finite core.

---

## TODO 3 — Stop-gradient and the steering residue: what corrupt-future filtering does and does not remove from the incentive

**id:** `stop-gradient-steering` · **modality:** MIXED (LEAN-CORE core + EXEC sweep) ·
**legitimacy thread: YES**

**MERGES** scout-handoff Q2 `legitimacy-stop-gradient` (the kernel-checked core) and
scout-legitimacy Q5 `leg-incentive-audit` (the EXEC scoring-rule model with the third action
`steer` — the residue computation).

**CLAIM (acceptance target).** Two coupled artifacts about ONE model family; the incentive signs
must be COMPUTED from the payoff/scoring rule and channel semantics, never chosen.

**(A) LEAN-CORE core.** Finite model: quote `a ∈ [0,1]`; autonomous verdict `Y₀` (a constant of
the model, independent of `a`); corruption channel `c(a) ∈ [0,1]`; self-confirming manipulated
verdict `M(a)` (e.g. `M(a) = a`); realized feedback `Y(a) = (1−c(a))·Y₀ + c(a)·M(a)`; ONE fixed
accuracy payoff functional (e.g. `−(a − target)²`), evaluated under two targets. Kernel-check:
  (i) under the RAW target `Y(a)`: a manipulative quote `a*` with perfect apparent accuracy
      (`a* = Y(a*)`) and a computed strictly positive payoff advantage over quoting `Y₀`, while
      `|a* − Y₀| ≥ γ > 0` explicit (the legitimacy defect);
  (ii) under the FILTERED target `Y₀` ("predict only through non-corrupted futures"): the unique
      optimum is `a = Y₀` and the payoff is LITERALLY independent of `(c, M)` — the
      stop-gradient identity, as a compiled equation, with the payoff functional IDENTICAL to
      (i)'s (only the target swapped);
  (iii) MANDATORY near-miss: a misspecified filter (one corrupt branch classified legitimate)
      re-creates a strictly positive manipulation advantage, computed;
  (iv) corruption deletion test: set `c ≡ 0` and (i)'s advantage provably vanishes.

**(B) EXEC sweep (exact rationals, asserts, no floats).** Two-period model, proper scoring
(Brier AND log), three actions `{honest, wirehead, steer}` with explicit channel semantics:
wirehead ⇒ future feedback reports high independent of truth; **steer ⇒ the future LEGITIMATE
opinion is moved by a legitimate-looking message — the human genuinely holds the steered
opinion and the feedback channel stays honest** (this clause is what distinguishes steer from
wirehead; police it). Legitimacy event `L` excludes exactly the corrupted branch. Compute:
  (1) `J_all(wirehead) > J_all(honest)` — the unconditioned objective rewards wireheading
      (baseline pathology reproduced, not assumed);
  (2) `J_L(wirehead) < J_L(honest)` — conditioning strictly removes it, and the mechanism is
      checked to be §0.3's information-deprivation (the corrupt branch contributes nothing to
      `J_L`);
  (3) the sign of `J_L(steer) − J_L(honest)` over a parameter sweep, with the flip boundaries
      reported. §0.3 predicts (3) can be positive ("doesn't rule out the scenario altogether");
      an honest refutation — conditioning kills steering too, across all natural
      parameterizations — is equally acceptable and MORE surprising.

Cite Perdomo et al. (performative prediction) for the stop-gradient mechanism — known
mathematics; the contribution is the kernel-checked instantiation in the legitimacy
vocabulary, the misspecified-filter near-miss, and the computed steering residue.

**OFF-LIMITS adjacent.** `Legitimacy.*` / `LegitimacyCorrigibility.*` (one-pair defect-sign /
comply-decline objects) — different target object here (the incentive DIFFERENCE under a target
swap in one fixed payoff functional); do not relabel `wirehead_declined`; no
pointwise-overstatement hypothesis may appear. `edt-node-value` machinery not reused. Do not
claim to discover non-performativity.

**SHADOW TEST.** FAKE: (a) `c` inert (guarded by (iv)); (b) "manipulative"/"steer" as free
labels — steer secretly wireheads (feedback channel dishonest on the steered branch); (c) the
payoff functional differing between (i) and (ii), making the stop-gradient identity
definitional; (d) hand-tuned payoffs — a single cherry-picked parameter point instead of a
sweep with exposed flip boundaries; (e) EXEC floats. REAL: identical payoff functional with
only the target swapped; the deletion test compiled; the steer branch's channel honesty
explicit in the model definition; exact-rational sweep with boundary report.

**NON-VACUITY WITNESS.** All headline numbers explicit rationals; compiled (iii) and (iv); the
EXEC sweep's printed sign table with at least one flip boundary located (or the honest
"no positive region exists" refutation). `#print axioms` clean for (A).

**WHY.** §0.3 says, in prose, exactly (2) and (3): the proposal "eliminates a positive
incentive but doesn't rule out the scenario altogether." Nothing in the corpus computes either
sign. This makes the two prose sentences into checked facts and — via the sweep — says HOW MUCH
residual manipulation incentive conditioning leaves. The residue (within-gate steering) is
precisely the underdetermination territory TODOs 2 and 6 map from the other side.

---

## TODO 4 — First kernel-checked cross-agent Total-Trust statement: non-transitivity with the honest `∀X ∀s` quantifier

**id:** `tt-transitivity-forall` · **modality:** MIXED (EXEC search + LEAN-CORE deliverable of
record) · **legitimacy thread: no (the uncrossed-boundary item)**

**MERGES** scout-handoff Q1 `tt-transitivity-exact` (the faithful re-run obligation + exact
decision procedure) and lean-scout Q4 (the conditional-expectation-lemma route, which is what
makes the honest `∀X ∀s` Lean feasible).

**CLAIM (acceptance target).**

**(A) LEAN-CORE (deliverable of record).** A standalone file with a concrete 3–4-world frame
and three agents (prior `π_H`; expert maps `P_A, P_B : W → W → ℚ`), Total Trust being the exact
DDB/LeanDeference conditional-mass inequality (copied with citation from
`DeferenceConverse.value_witness_iff_totalTrust_mass`'s statement form), quantified over ALL
`X : W → ℚ` and `s : ℚ`:
  1. **General reusable lemma:** if `P` is the `π`-conditional-expectation expert of a
     partition, then `TT π P` holds for ALL `X, s` — fiberwise: the event `{E_P(X) ≥ s}` is a
     union of cells, and each cell contributes `π(cell)·(E_cell(X) − s) ≥ 0`. (Classical — the
     law of total expectation; label as instantiation, not discovery.)
  2. `TT π_H P_A` proved by lemma 1 (`P_A` = `π_H`-conditional on partition `F_A`).
  3. `TT π_A P_B` proved by lemma 1 (`P_B` = `π_A`-conditional on `F_B`, with `π_A ≠ π_H`
     decide-checked).
  4. `¬ TT π_H P_B` witnessed at an explicit rational `(X, s)` by `norm_num`.
  5. **Recovery near-miss (mandatory):** setting `π_A := π_H` in the same frame makes the long
     edge HOLD (lemma 1 again) — the failure is caused by the prior mismatch, not the frame.
  `#print axioms` clean.

**(B) EXEC.** Exact-rational (`fractions.Fraction`) pre-search for the frame and the failure
witness — run2's poisoned numbers may seed intuition but every number must be re-derived. The
supersession statement is mandatory: the writeup states plainly that run2's trust-laundering
witness, genericity statistic, and recovery characterization remain uncitable and are replaced
by this artifact. STRETCH (optional, only with the exact predicate — no grids): the finite LP /
vertex-enumeration decision procedure of handoff Q1 (with the homogeneity+translation
normalization argument written out) to re-issue a genericity statistic and test the
prior-identity recovery conjecture across a family.

Honest scope, declared in the artifact: a finite-frame DDB statement — the first
machine-checked statement anywhere in the lab whose SUBJECT is trust between two agents with
the genuine quantifier — still not LI/asymptotic; say so.

**OFF-LIMITS adjacent.** `DeferenceConverse.*` (two-party Value⟺TT) — the TT inequality is
copied as the tested predicate, nothing about Value re-proved. `CM_implies_immodest` — lemma 1
is a different direction (CM-identity ⇒ fiber collapse vs. partition-expert ⇒ TT); check and
state the non-overlap. Run2 `trust-laundering` — POISONED per the header; replace, never cite.

**SHADOW TEST.** FAKE: (a) links "proved" by `decide` over an indicator grid or any finite
`X`-set — the run2 shadow verbatim; (b) a vacuous chain (a short link actually failing —
structurally excluded here because links are PROVED via lemma 1, the logically correct
asymmetry: ∀-claims proved, the ∃-failure witnessed); (c) `P_B` accidentally
`π_H`-conditional (then the long edge holds and the witness is fabricated — guarded by the
recovery near-miss plus the decide-checked `π_A ≠ π_H`); (d) any genericity/recovery number
computed on a sampled grid. REAL: links 2–3 hold for all `X, s` by proof; the failure point
explicit; the near-miss compiled; the supersession statement present.

**NON-VACUITY WITNESS.** The explicit `(π_H, π_A, F_A, F_B, X, s)` with the numeric gap
printed in the file; the compiled recovery near-miss; decide-checked non-degeneracy (`π_A ≠
π_H`; `F_A`, `F_B` non-trivial partitions; `P_B` genuinely `π_A`-conditional).

**WHY.** Run2 critique §0's standing dare, two rounds old: "no cross-agent trust statement is
machine-checked anywhere." Lemma 1 is the honest route a scout actually found (proof, not
grid). It also detoxifies the one poisoned run2 artifact and puts the safety reading —
delegated trust does not compose; "an AI vetted by another AI" is not automatically
trustworthy — on kernel-checked footing for the first time.

---

## TODO 5 — The strength ladder / weakening chain, fully adjudicated: the middle rung is false for soft gates

**id:** `weakening-ladder` · **modality:** LEAN-CORE · **legitimacy thread: no (live-notes
adjudication, deference/acceleration)**

**MERGES** three proposals that are one target — the rung structure shared by `li-deference.md`
(the boxed `g/w/q/v` chain, ~lines 213–226) and `faithful-acceleration.md` §5 (the four-rung
ladder: bounded-violation ⇒ limit ⇒ bounded-ε-violation ⇒ averaged): lean-scout Q2 (the chain
arrows, sound/false/repaired), acceleration Q3 `weakening-ladder` (the §5 ladder middle rung —
the same false arrow, found independently), and acceleration Q2 `corollary-deep-days` (the
bottom rung, i.e. the §5 Corollary). Two scouts independently hand-verified the same bug; this
TODO kernel-checks the whole structure once.

**CLAIM (acceptance target).** One standalone Lean file, using the corpus's `softInd` gates
(copied with citation from `FaithfulAcceleration.lean`) — never an abstract `w`:

  (a) **top rung sound (soft):** `Summable (fun n => g n * softInd δ (t − E n))` implies
      `AsympLE 0 (fun n => g n * (E n − t))` — via the ramp identity (`q_n = −δ·v_n` on the
      ramp region, `q_n ≥ −B·v_n` on the saturated region) and `Summable.tendsto_atTop_zero`;
  (b) **middle rung FALSE as stated (the finding):** the implication
      "limit rung ⇒ bounded-ε-violation" refuted by a compiled witness. Both scouts' witnesses
      are the same phenomenon; compile at least one, in the document's own notation:
      lean-scout's `g n = 1/(n+1)`, `E ≡ t − 2ε`, `δ ≤ ε` (hypothesis `q_n → 0` holds;
      `w_n = 1/(n+1)` harmonic-divergent, `Real.not_summable_one_div_natCast`), and/or
      acceleration's `t = 3/4`, `ε = δ = 1/8`, `g n = softInd δ (δ/n) = 1/n`, `p ≡ 0` (limit
      rung holds vacuously as the gate shrinks; `∑ w = ∑ 1/n = ∞`; the averaged rung fails
      too). The theorem must be a compiled `¬(∀ …)` with the explicit witness;
  (c) **repair:** under support-nondegeneracy (`∃ c > 0, ∀ n, g n > 0 → c ≤ g n` — in
      particular hard gates), the limit rung implies `w n = 0` eventually, hence `Summable w`
      — the arrow is valid exactly where the gate is effectively hard;
  (d) **bottom rung (the §5 Corollary), kernel-checked:** for `w n := g n * softInd δ (t − ε −
      p n)`, if the partial sums of `w` are bounded and `∑_{n<N} g n → ∞`, then for every
      `η > 0` eventually `(∑_{n<N} g n * p n)/(∑_{n<N} g n) ≥ t − ε − δ − η` — with the
      deep-days identity (`w n = g n` on days `p n ≤ t − ε − δ`) DERIVED from `softInd`
      saturation, never assumed;
  (e) **strictness/incomparability witnesses:** the doc's two (`p − t = −1/n` with `g ≡ 1`;
      `p ≡ t − ε/2` with `g ≡ 1`), the Corollary-vs-Theorem δ-gap witness (gated average
      `≥ t − ε − δ` with `∑ w = ∞`), and the no-cancellation incomparability pair;
  (f) **prose (one page):** the minimal wording fix for faithful §5 and the li-deference chain
      (state the limit rung over gate-on days, or add the nondegeneracy proviso), delivered as
      PROPOSED TEXT in `run3\work\weakening-ladder\` — the note files are read-only.

**OFF-LIMITS adjacent.** `FaithfulAccel.soft_total_trust(_doublysoft)`,
`violation_not_persistent` — different statements (the Theorem's trader core; they never relate
the rungs); copy `softInd` with citation only. Run2 `averaging-hides-spikes` — avg-vs-sup on a
spike family, no gates/summability; flag the family resemblance honestly, do not re-prove.
**Boundary with TODO 6:** this TODO owns the rung implications among trust statements; it must
NOT touch quote-referencing settlements (`Y_n = 1[a_n ≤ ½]`) or bias-vs-settlement claims —
those are TODO 6's. **Boundary with TODO 1:** gated weights `c·w` belong to TODO 1; the gates
`g` here are the trust-statement gates of the documents themselves.

**SHADOW TEST.** FAKE: (a) proving the chain with hard indicators throughout — then the middle
rung is TRUE and the finding evaporates (the pre-registered fake); (b) laundering the support
gap into (b)'s statement without exhibiting the soft counterexample; (c) assuming the
deep-days identity in (d) as a hypothesis; (d) shipping only the sound rungs (a)+(c)+(d) and
omitting the refutation — hiding the bug. REAL: (b) is a compiled refutation with the soft-gate
witness in the documents' own `softInd`; (c)'s nondegeneracy hypothesis is visibly violated by
(b)'s witness; (d) derives saturation from the `softInd` definition.

**NON-VACUITY WITNESS.** The compiled counterexample(s) of (b); the four witnesses of (e); the
`#print axioms` output recorded.

**WHY.** Two scouts independently found the same false arrow in the principal's actively-edited
notes (this week's revisions). This is the most direct, actionable
deliverable the round can produce: kernel-checked feedback into the live documents, plus the
missing last arithmetic mile (the Corollary) between the kernel-checked trader core and the
classwise-Value headline of v6 §5.9.

---

## TODO 6 — The diagonal calibration boundary: the scope-note §4 hole, the hard-gate repair, and the dithering crux

**id:** `diagonal-calibration` · **modality:** MIXED (LEAN-CORE + PROSE paper-audit + optional
EXEC) · **legitimacy thread: thematic (the admissible domain IS the corruption boundary)**

**MERGES** acceleration Q1 `calib-fails-diagonal` (the verified counterexample + hard-gate
repair) and scout-handoff Q4 `dither-escape` (the same seam attacked from the other side — the
two proposals' quote sequences are the same object: a quote hovering at ½). **ABSORBS** the
legality slice of acceleration Q7 `discharge-audit-4816` (items (a)+(b): weighting-class
legality and the deferral condition, exactly as they bear on this TODO's gates); the remainder
of Q7 is deferred (see QUESTION-POOL).

**CLAIM (acceptance target).**

  (i) **LEAN-CORE (mandatory) — the published argument fails:** compile Finding A of the
      acceleration scout: for `a n = ½ + 2⁻ⁿ` (even `n`), `½` (odd `n`), `Y n = 1[a n ≤ ½]`,
      `δ = ¼`: the soft high-gate weight sum `∑ softInd δ (a n − ½)` is bounded; the soft low
      gate is identically 0; and the uniform average bias `(1/N)·∑_{n<N} (a n − Y n) → 0`
      (compiled `Tendsto`) — certifying that the three weightings named in
      `faithful-acceleration-scope.md` §4 steps 1–4 do NOT witness miscalibration for this
      quote (step 3's "hence `a_n ≤ ½`" is a non sequitur). Must use the corpus's `softInd`
      (the scope note's own gates), with the bounded-vs-divergent contrast on the SAME
      sequence.
  (ii) **LEAN-CORE (mandatory) — the repaired dichotomy:** for EVERY `a : ℕ → ℝ` with
      `0 ≤ a n ≤ 1`, setting `w⁺ n = 1[a n > ½]`, `w⁻ = 1 − w⁺`: at least one of `∑ w⁺, ∑ w⁻`
      diverges, and on any divergent one the weighted average bias `∑ w·(a − Y) / ∑ w` is
      `≥ ½` in absolute value wherever the weight is positive — no quote sequence is calibrated
      against its own inverting settlement once ledger-readable hard gates are admissible.
      Instantiate on (i)'s sequence (`w⁺` = the even-days indicator, divergent, bias ≥ ½).
  (iii) **PROSE paper-audit (mandatory) — is the killing gate legal?** Against
      `references\logical-induction\main.tex`'s printed statements (Thm 4.8.16 Expectation
      Unbiasedness From Feedback; the generable-weighting and deferral-function definitions),
      adjudicate with verdicts HOLDS / HOLDS-WITH-LEMMA (name the lemma) / MISMATCH (quote the
      line): (a) whether a PATIENT one-day-deferred hard gate — reading yesterday's decided
      ledger value of `a_n ≤ ½` — is a legal weighting (the repair's load-bearing
      interpretation: "LI continuity binds only current-day prices"); whether same-day
      own-price and cross-market dependence are admissible weight features; (b) the deferral
      condition's exact form — prima facie, faithful §2's paraphrase ("feedback in before the
      next weighted term") is violated by `f(n) = 2ⁿ`; determine the paper's actual condition
      and whether a "patient" variant is proved or missing.
  (iv) **The dithering crux (from handoff Q4), attempted honestly:** the adversarial escape is
      `a n = ½ ± η_n`, `η_n → 0`, adversarially-chosen sides — every gate CONTINUOUS in the
      current price becomes side-blind and the ±½ biases may Cesàro-cancel. Deliver ONE of:
      (a) a construction over a precisely-specified legal gate family (continuous in the
      current price, computable from the price HISTORY) showing weighted calibration IS
      satisfiable on the diagonal — which would force a rewrite of v6 §5.10's "both faces die";
      (b) a proof that history-dependent/patient gates kill every dithering quote (the crux
      step: a non-generable side-pattern vs. the quote being A's own generable output); or
      (c) the pre-authorized honest partial: the separated-quote case (`a_n` bounded away from
      ½ on positive density) settled by (ii), and the dithering crux ISOLATED — the exact
      remaining step named as open. Optional EXEC garnish: exact-rational simulation of a
      dithering quote against a small legal-gate library, labeled illustration-not-evidence.
  (v) **Prose deliverable:** proposed corrected text for scope-note §4 (and the pointwise §4.1
      parenthetical), in `run3\work\diagonal-calibration\` — the note files are read-only.

**OFF-LIMITS adjacent.** `SelfRefTarget.no_exact_quote` / `residual_half` / `tracking_fails` —
pointwise TRACKING objects (off-limits as objects); this TODO is exclusively the CALIBRATION
face, which no Lean file touches; cite the k=0 tracking results as contrast only.
`TowerAccel.two_faces_distinct` — the OFF-diagonal decoupling witness; cite, never re-prove;
the question here is whether decoupling can be realized ON the diagonal. **Boundary with TODO
5:** the ladder rung implications are TODO 5's; this TODO owns bias-vs-inverting-settlement
claims. Gate legality may not be assumed — (iii)'s verdict is the check, and (ii)'s
interpretation must be labeled contingent on it.

**SHADOW TEST.** FAKE: (a) proving only (ii) and omitting (i) — hiding that the published
argument needed repair; (b) stating (i) with hard gates where the scope note used soft ones;
(c) proving the separated-quote case and titling it "both faces die" (the dithering case is
the content); (d) a gate family gerrymandered to exclude history-dependent gates without
justification; (e) rubber-stamping (iii) from the theorem's informal gloss rather than the
printed statement; (f) EXEC floats. REAL: (i) compiled with `softInd` and the
bounded/divergent/vanishing triple on one sequence; (ii) quantified over all quotes; (iii)
quotes the formal statements with line references and returns at least one nontrivial verdict
(item (b) guarantees one exists either way); (iv) resolved or honestly isolated.

**NON-VACUITY WITNESS.** The compiled sums of (i); (ii) instantiated on (i)'s sequence; each
(iii) verdict backed by a quoted hypothesis; `#print axioms` clean for the Lean.

**WHY.** The admissible-domain boundary is v6 §8's "deepest open item of the positive result",
and it is the round's legitimacy boundary in the acceleration register: the inadmissible
family is exactly §0.3-style corrupted feedback — a settlement that reacts adversarially to
the AI's own output. Its load-bearing published argument has a verified hole; the repair
mechanism ("the hard settlement itself legalizes the killing gate") both fixes the proof and
sharpens the thesis; and the dithering crux is the one item in the pool that could CHANGE the
v6 note rather than extend it.

---

## Coordination and boundary notes

- **Disjointness map.** TODO 1 owns gated weights `c·w` and calibration classes; TODO 5 owns
  the rung implications among trust statements; TODO 6 owns bias-vs-inverting-settlement on the
  diagonal. All three use `softInd` — shared vocabulary, disjoint targets. TODO 2 owns
  observational indistinguishability (traces); TODO 3 owns incentive signs under target swap —
  TODO 3 must not claim detection results, TODO 2 must not compute incentives. TODO 4 is the
  only cross-agent object.
- **Composition reading (for the report phase, not for executors to prove):** TODO 1 says the
  legitimacy gate must stay inside the generable/calibration class; TODO 2 says it cannot be
  computed from the observable record; TODO 3 says even a correct gate leaves the within-gate
  steering residue. Together they are the first formal chapter of §0.3.
- **Overflow tasks** (only if an executor finishes early; never at the expense of the mandatory
  clauses): (1) the remainder of the 4.8.16 discharge audit (acceleration Q7 items (c)–(d));
  (2) `soft-hard-spectral-gap` (handoff Q5); (3) the echo-expert one-liner (acceleration Q5);
  (4) the amplifier `intervalIntegral` hygiene (deference-core Q10). See QUESTION-POOL.md.
- **Honesty norms** of GROUND-RULES §3 bind every TODO: negative results and honest refusals
  are valid deliverables; label every claim kernel-checked / paper-proved / interpretation;
  record `#print axioms` output in the notes.
