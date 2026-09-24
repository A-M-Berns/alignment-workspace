# Transparency as faithful implementation of a declared influence channel

Dispatch: `prompts/2026-09-24-transparent-channel/PROMPT.md`.  Lean:
`lean/Workspace/Deference/Contrib/TransparentChannel.lean` (28 audited declarations,
axioms `propext`, `Classical.choice`, `Quot.sound` only).  Fixtures: `src/transparency.py`,
`tests/` (27 tests; the foreign fixtures run in their own rounds' interpreters).

Labels as in `FINAL_THEOREM.md` of the non-capture round: **LEAN**, **FIX**, **EXT**,
**OPEN**.

## 1. Verdict

**Transparency is the upstream half of authorship, and it is the same primitive.**  Reason
mediation says the payload factors through the reason trace; transparency says the reason
trace (or the activation event, or the specification) factors through its declared inputs.
Both are fiber invariance over the audited class at a fixed exterior, and both come in a
class-relative form (`ReasonMediated`) and a reference-relative form (the factor map
declared: `eval π_P` for the payload, a public `κ` for the channel).  The repository already
used the reference-relative form three times without naming it — the committed principal
program (`reasonMediated_of_reexecution`), representation as the registrar's move (`routed`),
and counterfactual branches as declared log transforms (`silentOf`, `jamOf`).  What the
name buys is that item 87 clause 6, item 89, the clause-2 receipts residual, Priority 68,
inquiry causal faithfulness, trigger integrity and secret evaluator change become one
hypothesis shape, *the channel realizes its declared reference*, discharged by one
realization pattern, *commit the reference as a program and re-execute it, or give the
channel to a party the advisor cannot write*.

It is not a new mathematical layer.  Every theorem below is one to four lines of
factorization algebra on objects that exist; the only new object is the reference `κ`.  The
substance it does *not* supply, and which stays external in the same places: whether the
declared-input view `x` is the right one (representation adequacy, the over-rich end
`realizes_of_injOn`), whether the reference is well designed (exposure, exploration, a
selection-blind `x`, a legitimate amendment rule), whether the ecosystem realizes it (engine
ownership, isolation, commitment), and whether coercive content carried transparently is
legitimate.  The last is why authorized environmental action stays a separate interface.

| problem | status after this round |
|---|---|
| item 87 clause 6 (selection sealing) | reduced: `Blind R P_sel` = selection-blind `x` + realized reference (`selectionBlind_of_realizes`, LEAN); the view-leak fixture is a failure of the first, not of the second |
| item 89 (activation independence) | reduced: `M ≡ 0` from a transparent activation channel on shared inputs (`mismatch_zero_of_realizes`, LEAN); approximate `D·E[M] ≤ D·(τ_raw + τ_corr)` (`security_bypass_le_defects`, LEAN); the pathwise form is necessary |
| Priority 68 (provenance adequacy) | answered in the second branch of its deliverable: the condition is transparency over the frame's re-simulated variation class; no record-internal condition works, the unlinked `C25` arm is the witness; the three acceptance fixtures behave as required (FIX) |
| Priority 72 (CM2, CM5) | clarified: both fixtures are *public* amendments of a declared input, so reference design and trigger design, not anti-manipulation; the secret variants are transparency failures, closed by a committed re-executed evaluator |
| provenance normalization | given a home: the reason-side corrigibilization, a substitution on the move alphabet; criterion, existence (truthful completeness of the authorized alphabet) and cost separated; `ShopK` is the existence failure; cannot repair selection failures |
| inquiry causal faithfulness | split: the reference `K_E` becomes an object, realization `A = K_E` a transparency hypothesis of the same kind as the others, adequacy of `K_E` as a model of the experiment stays EXT |
| free amendment / trigger integrity | reduced to transparency of the specification and activation channels above a fixed floor (`tower_factor`, LEAN); the floor and the legitimacy of the amendment rule stay EXT |
| independent inquiry / supplier | rewritten as realization lemmas for a reference; the soundness and coverage of the reference are reference design, not transparency |
| service / discovery residuals | unchanged; `α`, `β` are properties of the reference, and the transparency defect is a third link of the same chain |
| representation adequacy | independent, untouched |

## 2. The primitive

Frame `β : Q → Z → Ω` as in `ReasonMediatedAuthorship.lean`: `q` the advisor's whole
continuation from issuance, `z` the exterior — the principal's response policy *and* nature's
coordinate — and `β q z` the outcome world.  Readings of the world: the declared-input view
`x : Ω → X`, a channel `f : Ω → Y`, the reason trace `R`, the payload `V`.  A **reference**
is `κ : X → Z → Y`.

```
Realizes β x f κ D    :=  ∀ q ∈ D, ∀ z,  f (β q z) = κ (x (β q z)) z          reference-relative
Transparent β x f D   :=  ∀ z,  ReasonMediated β x f D z                       class-relative
```

**T0** (`transparent_iff_realizes`, LEAN).  `Transparent β x f D ↔ ∃ κ, Realizes β x f κ D`.
Class-relative transparency is the existence of *some* reference the whole class realizes;
reference-relative transparency is that reference declared.  `ReasonMediated β R V D z` is
the class-relative form for the payload channel with `x := R`; `reasonMediated_of_reexecution`
is its reference-relative form with `κ := eval π_P`.

**Why this and not the four alternatives.**

| candidate | relation to `Realizes` | verdict |
|---|---|---|
| posterior transparency `ν(·∣Y=y) = ν(·∣ref y)` for one prior | implied (`posterior_weight_eq`); prior-dependent; not compositional | corollary, not primitive |
| likelihood proportionality for all priors | equivalent to posterior transparency for all priors; the *marginal* shadow of `Realizes` after integrating `z` | the right statement of the motivating `P(·∣AI says X) = P(·∣X)`, which is `Realizes` with the content-uniform reference `κ(y∣ω) = c(y)·[ω ∈ y]` |
| channel equality `A_q(·∣x) = K(·∣x)` | the pushforward of `Realizes` under a credence on `z`; loses the coupling across `q` | enough for marginal expectations (clause 6's payload bound), not for joint events |
| SCM factorization `Y = κ(X, U)` | **is** `Realizes` with `U := z`; the frame is already a structural model with the exterior as exogenous noise | the same thing in the repo's own frame |
| fiber invariance à la `ReasonMediated` | **is** `Transparent`; `Realizes` adds the declared factor map | the primitive |

The frame is deterministic in `(q, z)` and probabilistic only through a credence on `z`
(`ActivatedValue.expect`, `LICorrigibility.expectR`), so every landed statement is already
pathwise in `z`.  Marginal channel equality is strictly weaker: `LICorrigibility.Witness.marginal_refuted`
has `E[c_raw] = E[c_corr]` with joint mismatch `1/2`, and the round's `PathwiseVersusMarginal`
tests show that *no* common reference has defects summing below the mismatch mass on that
fixture.  So the causal (pathwise) formulation is necessary exactly for item 89 and is free,
because the frame already has it.

**Approximate.**  With a finite credence `μ` on `Z`, the **defect** of `q` is the pathwise
disagreement with the reference, `τ_q(z) := [f(β q z) ≠ κ(x(β q z)) z]`, and `E_μ[τ_q]` its
mass.  It is not total variation: `abs_expect_event_sub_le` shows TV is a lower bound on the
disagreement mass, and `ValueBounds.test_tv_below_disagreement` shows the inequality is
strict when the realization couples badly (`1/4 < 3/4`).  The advisor chooses the coupling,
so the disagreement mass is the honest quantity and TV is what it becomes when the
realization couples optimally, which is a property of the realization and not of the
marginals.

**Over-rich and under-rich ends.**  An injective `x` makes every channel transparent
(`realizes_of_injOn`), the twin of `reasonMediated_of_injOn`: a declared-input view that
contains the advisor's whole continuation certifies nothing.  A constant `x` says the channel
does not depend on the advisor at all.  The declaration of `x` carries the normative content,
as `R`'s does for authorship, and it is EXT in the same way.

## 3. Theorem spine

All LEAN unless marked.  `D` the audited class, `z` fixed, `hP : ∀ p ∈ P, p.1 ∈ D ∧ p.2 ∈ D`.

**T1 (oracle replacement; `oracle_replacement`, `payload_factor`).**  `Realizes β x R κ D` and
`ReasonMediated β R V D z` give `ReasonMediated β x V D z`, hence `V (β q z) = G (x (β q z))`
on `D` with `G := F ∘ κ(·, z)`.  Hidden advisor variation moves the committed judgment only
through the declared inputs.  Proof: fiber invariance composes.

**T2 (no hidden steering; `blind_of_realizes`, `blind_payload_of_realizes`).**  If the
prohibited pair class leaves `x` unchanged and the trace realizes a reference, the trace is
blind to `P`; with mediation so is the payload.  `blind_of_mediated` twice.

**T3 (selection sealing, item 87 clause 6; `selectionBlind_of_realizes`).**  Hypotheses: the
selection is not a declared input, `∀ σ σ', x (β (qpol σ) z) = x (β (qpol σ') z)`; the trace
realizes `κ`; mediation.  Conclusion: `SelectionBlind β V qpol z`.  The proof produces the
`hnoPreview` hypothesis of the landed `selectionBlind_of_noPreview`, so clause 6 is that
theorem's hypothesis derived from two others.  **Approximate** (`expect_disagree_le`,
`abs_expect_sub_le_width`): with `E[τ_σ] ≤ τ` for every selection, `E[R_σ ≠ R_σ'] ≤ 2τ` and,
for `V = F ∘ R` of width `D`, `|E V_σ − E V_σ'| ≤ 2Dτ`.  Here marginal TV would also do,
since the conclusion is about marginal expectations.

**T4 (activation independence, item 89; `activation_eq_of_realizes`, `mismatch_zero_of_realizes`).**
An activation channel `c` realizing `κ_c` on declared inputs shared by the two candidates,
`x (β q_raw z) = x (β q_corr z)`, gives `c (β q_raw z) = c (β q_corr z)` pathwise and
`c_raw ∧ ¬c_corr ≡ 0`, the zero case of `mismatch_bound`.  The hypothesis is exactly "candidate
identity is not an allowed input of the answering process, and the process realizes its
declared kernel"; sequenced settlement makes `x` candidate-blind by timing, evaluator
factorization by isolation.  **Approximate** (`expect_mismatch_le_defects`,
`security_bypass_le_defects`):
```
E[U_raw] − E[U_corr]  ≤  L·E[both·δ] + E[both·ρ] + D·( E[τ_raw] + E[τ_corr] )
```
the landed `security_bypass_le_mismatch` with `D·E[M]` charged to the two activation defects.

**T5 (posterior corollary; `likelihood_iff`, `posterior_weight_eq`).**  Under `Realizes`, for
every prior on `D × Z` and every output `y`, the unnormalized posterior weights computed with
the actual likelihood `[f(β q z) = y]` and with the reference likelihood `[κ(x(β q z)) z = y]`
coincide pointwise; hence every posterior and every conditional expectation coincide.  The
motivating equality is the instance where `Y` is content and `κ` is content-uniform.  FIX:
`PosteriorCorollary.test_every_prior` on three priors, and its failure without `Realizes`.

**T6 (data processing in the pathwise norm; `abs_expect_sub_le_width`, `abs_expect_event_sub_le`).**
For `V : Y → ℝ` of width `D` and `μ ≥ 0`, `|E V(f) − E V(g)| ≤ D·E[f ≠ g]`; for an event,
`|μ(f ∈ A) − μ(g ∈ A)| ≤ E[f ≠ g]`.  For content-valued traces the width is replaced by the
sensitivity mass of the symmetric difference (`ReasonSupply.sensitive_symmDiff`, pointwise),
which is the form the landed inequality already charges.

**T7 (the amendment tower; `tower_factor`).**  With a fixed floor `spec 0 = c₀` on `D` and
`spec (t+1) = Amend (spec t) (g t) (e t)` — declared grounds, an authorized event — two
continuations agreeing on `(g s, e s)` for all `s < t` have the same `spec t`.  Free amendment
is the failure of this factorization: a write to the specification not carried by `(g, e)`.
Trigger integrity is T4 for the activation channel.  The floor is EXT.

**T8 (composition with service and discovery; algebra on `li_noncapture`, not mechanized
here).**  See §7.

**T9 (normalization is the reason-side `corr`; FIX, `Normalization`, `ProvenanceNormalization`).**
See §5 of the impact table and §6.

## 4. Repo mapping

| theorem | reuses | file | new definitions | generalization needed |
|---|---|---|---|---|
| T0 | `ReasonMediated`, `reasonMediated_iff_factor` | `ReasonMediatedAuthorship.lean` | `Realizes`, `Transparent` | none |
| T1, T2 | `blind_of_mediated`, `reasonMediated_iff_factor` | same | none | none |
| T3 | `selectionBlind_of_noPreview`, `SelectionBlind`, `selPairs` | same | none | none; the ecosystem's `x` must be exposed as a reading of the log (the non-advisor pre-commitment events) |
| T4 | `mismatch_common`, `mismatch_bound`, `security_bypass_le_mismatch`, `indR`, `expectR` | `LICorrigibility.lean` | `disagree`, `defect` | `ValidAt.M_val` can be supplied by `expect_mismatch_le_defects` as the `G_M` bound in `li_noncapture`'s `hsealed` slot, replacing the Boolean sealing hypothesis by a rate |
| T5 | none | — | none | the `EvaluationEcosystem` frame `β : Q → Z → Log` is a `Realizes` instance with `κ := builder ∘ (declared events)`; nothing to generalize |
| T6 | `Finset.abs_sum_le_sum_abs` | Mathlib | none | for content, compose with `ReasonSupply.sensitive_symmDiff` |
| T7 | none | — | none | the ecosystem's `ISSUE` event carrying `π_P` is `spec 0`; an amendment event kind would be `e t` |
| T8 | `li_noncapture`, `asympLE_add`, `li_noncapture_chain` | `ReasonSupply.lean`, `ReasonDiscovery.lean` | a third `MediatedPair` (actual supplier, reference supplier) | the chain theorem admits any number of links with shared middles; no change of shape |
| T9 | `MediatedRepairDominance.corr`, `corr_idem`, `corr_fix_iff` | `MediatedRepairDominance.lean` | a `Move` alphabet with prohibited kinds and a `subst` | the reason-side analogue is a rewrite on `Move E`; `corr_fix_iff`'s twin is "no prohibited move" |

Exact mismatches found: (i) the ecosystem's `Frame` exposes `R` and `V` but not `x`; the
round reads `x` off the log as the non-advisor pre-commitment events, which is what the
`SelectionSealing` fixture uses; (ii) `LICorrigibility.ValidAt` takes sealing as
`hsealed : φs → φn` in `li_noncapture`; the approximate T4 needs the `G_M` family bounded by a
rate `a/b` instead, which `li_gated_le` already supports (the mismatch branch of
`li_noncapture`'s proof is the `0/1` case of it); (iii) `ReasonDiscovery.Model` has a
deterministic `truth` and an `Indist` relation; under a stochastic `K_E` the cell is
"same kernel", which the model expresses only once `Ω` includes nature's coordinate.

## 5. Open-item impact

| item / boundary | classification | what changes | what remains |
|---|---|---|---|
| **68** provenance adequacy | answered, negative-plus-construction | the non-circular condition is `Transparent` over the frame's variation class `D`; acceptance fixtures pass and fail as required (§6) | the class `D` must include world counterfactuals (excision, re-simulation); a log carries one member of `D`, so no record-internal condition exists — the clause-2 receipts residual, already recorded |
| **72** CM2, CM5 | clarified, still open at its own layer | both fixtures declare their change (`licensed`, `evaluator` are surface inputs): reference design and trigger design; secret variants are transparency failures closed by re-execution | the exposure-adequacy clause on the reference and the amendment-trigger clause are design decisions (Coverage of the evaluation opportunity, Integrity's episode pinning) |
| **87 clause 6** sealing | reduced to a realization theorem | `selectionBlind_of_realizes`: a selection-blind `x` plus a realized `κ` | that the ecosystem's `x` is selection-blind is a *design* fact about what the market publishes (the view-leak fixture is exactly a non-blind `x`); that the advisor's channel realizes `κ` is EXT for a real advisor, as before |
| **87 clause 7** availability | independent | — | — |
| **89** activation independence | reduced to a realization theorem | `mismatch_zero_of_realizes`; approximate charge `D·(τ_raw + τ_corr)` | that the answering process realizes a candidate-blind kernel: sequenced settlement (timing) or factorization (isolation) are the two realizations, unchanged |
| **92** service residual | independent | `α` is a property of the reference supplier; the actual supplier's departure from it is `τ` | unchanged |
| **93** discovery residual | independent | `β` is a property of the reference repertoire | unchanged |
| provenance normalization | given a home, not closed | `Norm_σ := subst on the move alphabet`; idempotent, fixed on prohibited-free continuations; exists iff every prohibited move `q` uses has an authorized substitute; `ShopK` is the negative | the substitution's *matter* map is a declaration; cost is the advisor's lost gain plus the principal's lost legitimate content (silence); selection failures are not repairable by any substitution and belong to supply |
| inquiry causal faithfulness | split | `K_E` is an object; `A = K_E` is a transparency hypothesis | adequacy of `K_E` as a model of the physical experiment |
| free amendment | reduced | `tower_factor` | the fixed floor; legitimacy of `Amend` (episode pinning is one clause of it) |
| trigger integrity | reduced | T4 on the activation channel | as 89 |
| representation adequacy | independent | the over-rich end `realizes_of_injOn` is its formal shadow | untouched |
| independent inquiry / supplier | rewritten | engine-owned selection, stopping, candidate generation, advisor-proof capacity = the engine realizes `κ`; exogenous costs = costs are in `x` not in `q` | evidence soundness and coverage are reference design; the theorem interface reads `Realizes` for the channel and the supply/discovery theorems for the reference |
| clause-2 receipts residual | named | class-level transparency is not log-certifiable; reference-relative transparency by re-execution is | unchanged, now the same residual for every channel |

## 6. Countermodels

The condition run against the exact fixtures (`tests/test_fixtures.py`; each in its own
round's interpreter) and the dispatch's list (`tests/test_algebra.py`, Lean `Witness`).

| attack | fixture | `x` | `f` | transparent? | classification |
|---|---|---|---|---|---|
| hidden read in the semantics | `office.hidden_reading_pair` | trace | `replay` | **no** | transparency |
| hidden read in the effect | `cases.partial_effect_pair` | `declared_data` | trace | **no** (`extraction_agrees` = "effect differs on equal declarations") | transparency |
| honest hidden state | `office.hidden_pair` | trace | `replay` | yes | — |
| permitted persuasion | `office.persuasion` (+ a hidden-state variant) | trace | `replay` | yes; the argument is a declared finding | passes |
| licensed persuasion | `licensed_persuasion` (silent, reasoned, loud) | `ltrace` | `Z_FIVE` | yes; reasoned ≠ silent moves the machinery, loud = reasoned | passes |
| pressure with the trace fixed | `residual_placebo` | `ltrace` | `Z_FIVE` | **no** | transparency |
| unlinked split campaign | `C25_split_episode(linked=False)` | settlements of `ancestry(E2)` | licence status | **no**: `x` equal across excising `E1`, verdict `Licensed → Unresolved` | transparency, *visible only under the excision counterfactual*; the criterion says `Licensed` |
| linked split campaign | `C25_split_episode(linked=True)` | same | same | vacuous (`x` changes) | the criterion defeats the citation |
| selection read off an undeclared source | ecosystem `leak`, quiet world | non-advisor pre-commitment events | `R` | **no** (`x` blind, `R` not) | transparency |
| selection read off a declared publication | ecosystem `view_prog`, market world | same | `R` | yes, and `x` is not selection-blind | reference design (what the market publishes) |
| sealed advisor | ecosystem `sealed` | same | `R` | yes, `R` blind even when `x` is not | — |
| truthful cherry-picking | non-capture fixture 2 | the world's true reasons | canonical content | realizes `κ_first`, not `κ_full`; every audit clause holds | selection failure: the *supplier* reference is not realized; charged as content `d = 2`, adverse mass `1/4` |
| searching many candidates for the outlier | Lean `Witness.picker` | fact set | trace | not transparent as a two-element class; realizes the reference that declares its selection rule | reference design decides which selection rules are legitimate; transparency then enforces the declared one |
| outright false reporting | non-capture fixtures 12, 12b | — | — | voids under authentication; a certified false reason is authentication soundness | authentication (a transparency failure of the settlement channel) |
| hidden psychological targeting | `ReasonMediatedAuthorship.Witness.covert` | argument made | payload | `R` transparent, `V` not mediated | authorship |
| secret evaluator change | `CommittedEvaluator` | (occasion, declared evaluator) | score | **no** | transparency; impossible under re-execution |
| public evaluator amendment | `cm5_evaluator_shedding` (`e0 → e1` at 60, declared) | same | score | yes | integrity/amendment (trigger design: no challenge opens) |
| preemptive retirement | `cm2_preemptive_delicensing` (`licensed` false from 4) | licence schedule | exposure | yes | reference design (exposure adequacy); openness of the evaluation opportunity |
| candidate-dependent activation | `LICorrigibility.Witness.marginal_refuted` | — | activation | marginal equal, joint mismatch `1/2` | transparency of the activation channel (pathwise) |
| no authorized truthful channel | `ShopK` | — | — | authorship voids (`η = 1`); only silence normalizes; distortion `1` | authority/effect completeness of the *reason* alphabet: the substitution has no codomain |
| authorized substitute exists | `ShopD` | — | — | `lie ↦ report` normalizes; `W_act = 1/2`, void `0` | normalization exists; cost `1/2` to the advisor |
| omitted reason type | non-capture fixture 7, discovery rows 18–19 | — | — | vacuous | representation |
| bounded inquiry honestly fails | discovery rows 2, 14, 17 | — | — | transparent | discovery (`β`) |
| transparent threat | `ReasonMediatedAuthorship` fixture C | argument + threat | payload | `R` may be transparent, `V` not blind | authorship for the effect on `V`; the threat's *execution* is the effect interface |
| protocol self-amendment | `Tower.test_tower_factor` | `(g, e)` | `spec` | the authorized tower factors; an undeclared write does not | integrity/amendment (with a fixed floor) |

The classification is modular in the intended sense: every attack lands in exactly one of
representation, reference design, transparency, authorship, openness, discovery, service,
effect/alphabet completeness, integrity/amendment, and the two ambiguous fixtures of the
improvement round (CM2, CM5) split cleanly once "is the change declared?" is asked.

## 7. The quantitative theorem

The landed chain is `U_T → U_disc → U_full` with `li_noncapture` on each link and the
discovered comparator as shared middle.  The transparency defect enters as a third link in
front: `U_T → U_disc^A → U_disc^K → U_full`, where `U_disc^A` is the actual supplier's docket
trace and `U_disc^K` the reference supplier's on the same `z`.  Each link is a `MediatedPair`
with the same `L`; `li_noncapture_chain`'s proof is `asympLE_add` on two `li_noncapture`s and
admits a third verbatim.  The resulting statement, with every term that cannot honestly be
dropped:

```
E_n(U_T) − E_n(U_full)  ≲_n  L·( τ_n + α_n + β_n )  +  E_n[both·κ_n]  +  D·E_n(M_n)
```

- `τ_n` — the **transparency defect in content units**: the certified bound on the adverse
  sensitivity mass of `disc^A Δ disc^K` on the common-audit branch (T6 with
  `sensitive_symmDiff` in place of the width); zero under an independent supplier, which is
  what "independent" now means.
- `α_n` — the service residual, a property of the reference supplier (suffix-cut excess).
- `β_n` — the discovery residual, a property of the reference repertoire (cell gap).
- `κ_n` — the form residual, zero for an extensional program.
- `M_n` — the audit mismatch, `≤ τ^c_T + τ^c_disc` by `expect_mismatch_le_defects`, zero under
  a content-monotone audit.

The norm is the pathwise one throughout: disagreement mass for Boolean and width-bounded
payloads, expected sensitivity mass of the symmetric difference for content.  Total variation
appears nowhere, because the payoff algebra is pointwise in `z` and TV is only a lower bound
on what it charges.  The composition is compatible with `li_noncapture`, `li_noncapture_chain`,
`TraceSteering.steering_bound` (which already has `D·M` in this position) and `ReasonSupply`'s
gated families; it is not mechanized here because the third pair needs the supply modules
built, which this round did not import.

## 8. Lean

Built and audited: `TransparentChannel.lean`, importing `ReasonMediatedAuthorship` and
`LICorrigibility`.  Easy algebra, done: T0–T7 and the witnesses (`picker`, `hidden_read`,
`leak_kinds`, `defect_attained`, `tower_inhabited`).  Easy algebra, not done: the third chain
link (T8; `li_noncapture` thrice) and the content form of T6 (`sensitive_symmDiff` composed
pointwise).  Genuinely new semantics, not Lean: which `x` the ecosystem declares (a reading
of the log the round proposes as "the non-advisor pre-commitment events"); the reference
`κ` for each channel (supplier, repertoire, registrar, answering process); the substitution
alphabet of normalization; the stochastic inquiry model.  Nothing is registered; the round
files no claim.

## 9. Architecture

```
                 declared inputs x                    reason trace R                payload V
 (ω, q, H) ───────────────────────────► x(ω) ─── κ ───► R ─── F = eval π_P ───► V
            transparency of the           (reference-relative:      authorship (landed)
            reason channel                 Realizes β x R κ D)
            [T1: V = G ∘ x on D]

 same shape, three more channels:
   activation  c = κ_c(x, z)      candidate ∉ x        ⇒  M ≡ 0            (item 89)
   inquiry     y = K_E(ω, z)      declared kernel      ⇒  posterior = ref  (causal faithfulness)
   spec        C_{t+1} = Amend(C_t, g_t, e_t), C_0 fixed                    (free amendment)

 what each landed contract contributes:
   Integrity        the log every x, R, c, C is read off is append-only and authenticated
   Robust Openness  the reference keeps routes open under the declared interventions (K-design)
   effect completeness   every environmental influence is a declared release (the other interface)
   settlement       the reference's truth inputs are exogenous to the disposer
   authorship       V = F(R) on the audited class (the downstream half)
   transparency     R = κ(x, z) on the audited class (the upstream half)
```

**Legitimate influence = Legitimate Evolution + Transparent Mediation**, with Transparent
Mediation = transparency of the reason channel + reason-mediated authorship, is mathematically
natural in one exact sense: both halves are fiber invariance of a reading over the audited
class, and their composite is T1.  It is not a conjunct of legitimacy and should not be
written as one; it is a third contract next to Non-Capture and authorship, consumed by
deference.  The global statement — every path from advisor-private state to the principal's
normative trajectory factors through the authenticated reason interface or the authorized
effect interface — is the conjunction of `Realizes` for the reason, activation and
specification channels with effect completeness for the world channel.  It does not make
coercion or manufactured incentives legitimate: a transparent threat is a transparent reason
with an effect behind it, and the effect interface, not this one, governs it.

## What this does not establish

That any `x` is adequate; that any reference is well designed; that any real advisor or
engine realizes its reference (EXT for the same reasons the receipts residual is EXT: a log
carries one member of the audited class); that the amendment tower has a floor; that the
third chain link is mechanized; that transparency by itself removes the service or discovery
residuals, which are properties of the reference it is measured against.  The Carroll
finding depends on `enrichment.excise` being the world counterfactual it names.  Names are
provisional (`AGENTS.md` standard 6): `Realizes`, `Transparent`, `defect`, `disagree`,
`tower_factor`, "transparency defect", "reference-relative / class-relative".

## Deviations from the prompt

- The prompt's phrase "declared inquiry outcomes and log transforms are the evidential and
  counterfactual processes they name" is a paraphrase; the repository's text is the
  causal-contract row of `FINAL_THEOREM.md` §8 and the §9 wall of `wiki/Corrigibility.md`.
- `ShopK` is a fixture of the mediated-repair-dominance round, not of `PRIORITIES.md`; the
  prompt's "`ShopK`-style obstruction" is read as that fixture.
- Items 94–100 do not exist; the next free number is 94, which this round files.
- The TV formulation the prompt proposed is replaced by the pathwise disagreement mass; the
  prompt asked for exactly that if TV was wrong.

## Outstanding maintainer actions

1. Rule on the `Awaiting the author` entry this round adds: whether *transparent mediation*
   enters the wiki as a named layer beside Non-Capture and authorship, and under which name.
2. Decide whether item 94 (filed here) is dispatched before or after item 89's architecture
   question, since T4 makes them one construction.
