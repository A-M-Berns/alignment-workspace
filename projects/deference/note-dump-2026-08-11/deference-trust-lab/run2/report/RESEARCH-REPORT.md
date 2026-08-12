# Deference & Trust Lab — Round 2 Research Report

*Honest synthesis. Defers throughout to `run2/report/CRITIQUE.md`. Every claim is tagged
PROVED (kernel-checked) / SKETCHED / CONJECTURE / INTERPRETATION. Where validation is finite-core-only
or assumes the LI layer, it says so inline.*

---

## 0. The one sentence the principal must read first

> Round 2 kernel-checked **four finite single-frame facts** — a single-agent averaging/tower failure, a
> single-decider negative-value-of-information menu example, a real-analysis average-vs-sup separation, and
> a single-agent EDT/UDT κ-collapse — and ran **one** cross-agent EXEC search **whose submitted artifact is
> a shadow**. **No cross-agent or asymptotic trust statement is machine-checked anywhere; the four PROVED
> results bear on human↔AI trust by INTERPRETATION, not by derivation.** The genuine new content is:
> `edt-node-value`'s κ-collapse lemma (the one substantive new theorem), `negative-voi`'s faithful build of
> v2 §1.1's previously *unbuilt* Weatherson example, and `aumann-modesty`'s instantiated averaging-failure +
> partitional near-miss. `trust-laundering`'s underlying claim is *plausibly true but its artifact
> establishes none of its reported numbers* and needs a real-grid re-run before anything is cited.

This is the same boundary round-1's critique flagged (no LI/asymptotic/cross-agent statement is
machine-checked). Round 2 did not cross it — by design (OFF-LIMITS + PROOF-ONLY routing) — and must not be
read as having crossed it.

---

## 1. One-screen ledger

| TODO | Claim (what it tries to show) | Modality | Verdict | Honest one-liner: established vs open |
|---|---|---|---|---|
| `aumann-modesty` | Aumann's load-bearing **averaging/tower step** fails for a modest (S4, non-partitional) single agent; partitionality restores it | LEAN-CORE | **REAL** (over-titled) | PROVED: on a Fin-4 frame two overlapping cells covering a common-knowledge event carry distinct posteriors 2/3≠1/3, overall 1/2 matches neither, so no averaging value exists; `hdisj` load-bearing. OPEN: it is a **one-agent** tower fact (not two-agent agreement), and `C`=whole space makes the self-evidence checks true-but-trivial. |
| `negative-voi` | A *less*-refined non-partitional expert yields **strictly higher** Value (negative value of information); partitional anchor removes the gap | LEAN-CORE | **REAL** (best, on-spec) | PROVED: Fin-3 Weatherson frame, `Value E1 = 4/9 < 5/9 = Value E2`, recOpt = genuine data-driven argmax-of-own-posterior, near-miss `Value Q ≤ Value E1` (a **tie**, 4/9=4/9) with strictness carried by `Value Q < Value E2`. OPEN: finite static single-decider only; "negative VoI" is **non-partitional-argmax-relative**, not "more info is bad for a Bayesian." |
| `averaging-hides-spikes` | Average→0 gives **no** single-round bound (sup↛0); forbidding per-round concentration is the exact cure | LEAN-CORE | **REAL** (≈1.5 of 2 pieces) | PROVED (i): explicit family, avg `B/T → 0` (genuine `Tendsto`) while running sup `= B ↛ 0`. The mandatory near-miss (ii) **as specified is FALSE** and was proved false; the shipped substitute binds only the *per-round* swing, not the running-sup spike. So "the cause is single-round concentration" holds for **recurring** spikes only. |
| `edt-node-value` | Replace round-1's free `node_value` by a genuine EDT conditional `U∘κ`; decoupled ⇒ EDT-argmax = global UDT optimum; coupled ⇒ strict divergence | LEAN-CORE | **REAL** (most substantive new Lean) | PROVED: new κ-collapse lemma `vNode_decoupled_eq`; decoupled coincidence; coupled mugging near-miss on a **proven-non-separable** U where the EDT-argmax misses the unrestricted optimum, gap = acausal payoff *net of own-cost* (9900 = 10000−100). OPEN: everything is **conditional on the free modeling input κ**; the open problem moved from `node_value` to κ, it was not closed. |
| `trust-laundering` | DDB/Lean **Total Trust is not transitive** (EXEC over the real conditional-mass inequality); recovery characterization | EXEC | **SHADOW** | The underlying claim is **plausibly true** (gate located 6 faithful witnesses, fine-grid-verified one), but the executor's **search, headline witness, 41% genericity stat, and recovery characterization are all computed on a 32-point {0,1}-indicator shadow of the ∀X:W→ℝ quantifier** the property actually uses; under genuine Total Trust BOTH "short links" of the printed witness fail → vacuous chain. None of the reported numbers transfers. Re-run required. |

**Consolidation note (INTERPRETATION):** `aumann-modesty` and `negative-voi` are **two faces of one
structural fact** — drop the Euclidean/partition property and a partitional guarantee fails (averaging in
one, VoI≥0 in the other). They are disjoint as the CONSOLIDATION step intended, so this is *not* round-1
duplication, but they should not be sold as two independent phenomena. None of the four REALs is a re-skin of
v2/LeanDeference (verified against the OFF-LIMITS list; the critique §6 confirms).

---

## 2. The results that are REAL and new

### 2.1 `edt-node-value` — the one substantive new theorem (PROVED, finite, κ-conditional)
**Artifact:** `run2/lean/edt-node-value.lean` (exit 0, no `sorryAx`, 19 theorems, axioms ⊆
`[propext, Classical.choice, Quot.sound]`). **Adversarial witnesses:** `run2/verify/edt-node-value-attack.lean`,
verdict `run2/verify/edt-node-value-verdict.md`. **EXEC cross-check:** `run2/work/edt-node-value-sanity.py`.

Round 1 defined updateless deference through a **free** per-node valuation `node_value : S → A → ℝ`,
untied to the utility — a hand-fed discriminator that "could not tell a caver from a non-caver" (round-1
CRITIQUE §3, BLOCKER). This file **removes the free input**: the node value is *derived* as a genuine EDT
conditional of the *same* utility, routed through an explicit self-prediction/reachability kernel:
`vNode U κ s a := U (κ s a)`. Using the **coupled** utility type `U : (S → A) → ℝ` (not round-1's
separable `U : S → A → ℝ`) is what gives κ work to do.

- **New lemma `vNode_decoupled_eq` (the κ-collapse):** under separability + decoupling,
  `vNode U κ s a = p s · u s a + ∑_{t≠s} p t · u t (base s t)` — the a-dependence is carried exactly by the
  local term and the off-s mass is κ's prediction. This is *not* a relabel of the off-limits
  `split_eq_global`: there the per-node optimality was *assumed*; here it is *derived from the EDT argmax
  through κ*. The critique (§4) confirms this is "the only file that checks a non-trivial NEW lemma."
- **Decoupled coincidence `edt_decoupled_globally_optimal`:** the EDT-argmax policy attains the global UDT
  optimum.
- **Mandatory coupled near-miss `mugging_edt_misses` (0 < 9900):** on a **proven-non-separable** U
  (`not_separable`: separability would force 9900 = −100), with `globalOpt = (pay,pay)` the *unrestricted*
  maximizer (`global_opt_dominates_all`), the severing κ drives the EDT-argmax to refuse at **both** nodes
  (computed, no diagonal-by-fiat), strictly missing the optimum. `correlated_kappa_agrees` shows a
  correlated κ restores agreement → **κ's severing structure is load-bearing, not inert** (the settling
  attack `A1_hDec_load_bearing` confirms: a separable U with a deceiving non-decoupled κ satisfies every
  other hypothesis yet breaks the conclusion).

**Precise scope (defer to critique §4):** the result is **entirely conditional on κ, a free modeling
input.** `mugging_edt_misses` is *not* "EDT agents fail to defer"; it is "**given a severing κ**, the
EDT-argmax misses the UDT optimum." The locus of the open problem moved from `node_value` to κ — a real
advance (the discriminator is now explicit and inspectable) but **not a closure**. The gap statistic is the
acausal payoff **net of the own-cost the optimum also pays** (9900 = 10000 − 100), both numbers exposed in
`gap_is_acausal_payoff`. An earlier draft's separable-U-with-diagonal-by-fiat shadow was self-caught and
genuinely removed.

### 2.2 `negative-voi` — faithful build of v2 §1.1's unbuilt Weatherson example (PROVED, the cleanest deliverable)
**Artifact:** `run2/lean/negative-voi.lean` (exit 0, no `sorryAx`, axioms clean). **Attack:**
`run2/verify/negative-voi-attack.lean`; **verdict:** `run2/verify/negative-voi-verdict.md`. **EXEC:**
`run2/work/negative-voi.py` (exhaustive 3-world S4 search + >1.1M-case argmax sweep in the gate, **zero**
Geanakoplos violations).

v2 §1.1 (line 244) *cites* a 3-world tightness example in prose with no frame. This builds it: `W = Fin 3`,
uniform π, menu `O⁰=(0,2/3,1/3)`, `O¹=(2/3,0,0)`; experts `E1` (cells `{0},{1},{0,2}`) refining the
**non-partitional** `E2` (cells `{0},{1},{0,1,2}`). `recOpt` is the **identical** genuine argmax-of-own-
posterior rule for every expert (`recOpt_eq_posterior_argmax` ties numerator-argmax to the normalized
posterior; strict at world 2 so the tie-break is never exercised). Result: **`Value E1 = 4/9 < 5/9 =
Value E2`** — the more-refined expert is strictly worse. The settling attack
`A4_partitional_destroys_gap : ¬(Value E1 < Value Q)` compiles, proving the negative sign is caused by E2's
non-partitionality, **not** the payoffs; the adversarial-menu test flips `recOpt` to all-1/all-0, defeating
the "hand-tuned constant" shadow.

**Two qualifiers (defer to critique §2):** (a) the mandatory near-miss `near_miss_partitional` is an
**EQUALITY** `4/9 = 4/9` — replacing E2 by the partitional anchor Q makes the negative gap **vanish**, it
does *not* flip the refined expert to a strict win; the strict separation is carried by the *separate*
`partitional_anchor_strictly_dominated : Value Q < Value E2`. The refined expert "stops losing value," it
does not gain it. (b) "Negative value of information" is **decision-rule-relative**: it is negative *for a
non-partitionally-informed argmax decider*, not "more information is bad for an optimal Bayesian" (which is
impossible). The qualifier must travel with the slogan, or a reader over-generalizes to "deferring to a more
capable system is worse" without the load-bearing non-partitionality clause.

### 2.3 `aumann-modesty` — instantiated averaging-failure + partitional near-miss (PROVED, but over-titled)
**Artifact:** `run2/lean/aumann-modesty.lean` (exit 0, no `sorryAx`, axioms clean). **Attacks:**
`run2/verify/aumann-modesty-attack.lean` (deletes `hdisj` → fails at both sum-splits, confirming load-bearing),
`run2/verify/aumann-modesty-attack2.lean`; **verdict:** `run2/verify/aumann-modesty-verdict.md`. **EXEC:**
`run2/work/aumann-modesty-sanity.py` (reproduces every number; exhaustive 355-frame boundary — disjoint covers
NEVER break averaging, overlap breaks it 16×).

On a Fin-4 common-prior frame, an S4-but-non-Euclidean correspondence has two genuinely-overlapping
non-nested cells `E0={0,1,2}`, `E3={1,2,3}` covering a common-knowledge event `C`, with kernel-checked
distinct posteriors `post(E0)=2/3 ≠ post(E3)=1/3` and `post(C)=1/2` matching neither — so the averaging
identity has no value `q` to land on. The general lemma `partition_averaging` (disjoint cells sharing `q` ⇒
`post C = q`) instantiated on an S5 correspondence on the same prior restores `post(C)=1/2`. Disjointness is
decisively load-bearing (the attack's `hdisj` deletion fails at the numerator AND denominator splits). This
is the D9 "Aumann-fails-under-modesty" example CRITIQUE flagged as skipped low-hanging fruit.

**Two demotions the report enforces (defer to critique §1):** (a) **The title is wrong.** This is a
**single-agent** object (one correspondence `E`), not Aumann's two-agent agreement theorem. What is shown is
the **tower/averaging *step*** failing on a non-partition — the load-bearing ingredient *inside* Aumann,
exhibited in isolation. Do **not** let a reader hear "two rational agents fail to agree." (b) **`C` is the
whole space** (`fun _ => true`), so `C_self_evident`, `C_is_knowledge_fixed_point`, `C_is_union_of_cells` are
true but **trivial in any S4 frame**; the cover "`E0 ∪ E3 = C`" is just "`E0 ∪ E3 = everything`." The overlap,
distinct posteriors, and averaging failure are all genuine, but the "non-trivial self-evident sub-event" is
**not** exhibited. The modesty≡non-partition tie is INTERPRETATION; the phenomenon is classical (Geanakoplos),
cited not discovered — the novel content is precisely the kernel-checked instance + near-miss + 355-frame
boundary.

---

## 3. Honest negatives & impossibilities (valuable!)

1. **`averaging-hides-spikes` — the natural near-miss is FALSE, and proved false (PROVED negative).**
   `run2/lean/averaging-hides-spikes.lean`, `running_sup_near_miss_false`. The intuitive cure "o(1) per-round
   budget ⇒ running sup → 0" is **false**: a single early fixed spike pins the running sup at `B` forever.
   The executor did not fake it — shipped a false-witness theorem and a *true* substitute about the **per-round
   swing** (`swing_tendsto_zero_of_budget_o1`). The gate's probe `existence_family_SATISFIES_nearmiss` compiles:
   the vulnerable family itself satisfies the substitute's hypotheses **and** conclusion. So the substitute
   does **not** isolate the cause of the existence direction; "the vulnerability is exactly single-round
   concentration" is established for **recurring** spikes only, **not** for the one catastrophic round. The
   report must **not** write "(ii) certifies the cause of (i)." This is a textbook honest negative and the
   reason the file is "≈1.5 of 2 pieces," not 2.

2. **`negative-voi` near-miss is a tie, not a flip (PROVED, disclosed).** See §2.2(a). Worth restating as a
   negative: refining a non-partitional expert to a partition does **not** make the refined expert *win* on
   this menu — it merely *stops it from losing*. The "monotonicity restored" reading is the weaker `≥` form.

3. **`trust-laundering`'s pre-registered recovery conjecture is REFUTED (an EXEC negative — but see §4).**
   The executor's search killed the conjecture that transitivity recovers when `B` is `H`-observable/nested,
   replacing it with "recovers under shared prior `π_H = π_A`." **However, the recovery analysis is computed
   with the same shadow predicate**, so neither the refutation nor the replacement is validated as reported
   (the gate confirms the qualitative content is *plausible*, not established). An honest negative computed on
   a shadow grid does **not** transfer.

4. **The whole run produced zero cross-agent kernel-checked trust facts (structural negative).** Exactly one
   TODO was even a two-party object (`trust-laundering`) and it is the SHADOW. This is not a failure of effort
   — it is the OFF-LIMITS/PROOF-ONLY boundary working as designed — but it is the honest ceiling of round 2.

---

## 4. The SHADOW: `trust-laundering` (the principal must not bank this as a win)

**Verdict: SHADOW (gate), concurred by critique §5 [BLOCKER as stated].** Artifacts:
`run2/work/trust-laundering.py`, `run2/work/trust-laundering.md`, verdict `run2/verify/trust-laundering-verdict.md`.

The per-(X,s) inequality the script computes **is** the faithful DDB/Lean conditional-mass form (not "equal
means") — so the laundering is **not** in the inequality. It is in the **quantifier**: `link_holds`
iterates `X` over `{0,1}^W` (a 32-point indicator grid for |W|=3) and `s` over `{1/3,1/2,2/3,1}`, whereas the
genuine property (`DeferenceConverse.value_iff_totalTrust`, v2 §0.2) quantifies over **all real-valued
`X : W → ℝ`**. Re-running the headline `WITNESS` against a rich rational grid, **both** "short links" FAIL
(L1 at `X=(0,7/8,5/8), s=2/3`; L2 at `X=(3/4,0,1/4), s=1/3`) — so the printed "non-vacuity witness with both
links holding over all 32 (X,s)" is a **vacuous chain** (pre-registered shadow case (c)). **Every** downstream
number — the explicit witness, the 41% genericity stat, the `NESTED_WITNESS` refutation, the 343/0 recovery
sweep — is computed with this shadow predicate and **does not transfer** to genuine Total Trust.

Two things to preserve exactly:
- **The claim is TRUE** (the gate located 6 honest faithful witnesses among the coarse-accepted chains and
  fine-grid-verified one: `π_H=(1/4,1/2,1/4)`, `π_A=(1/4,1/4,1/2)`, with the long edge failing 213× and both
  short links genuinely clean). So this is **SHADOW, not BROKEN** — the safety reading "alignment is not
  closed under delegation" survives *morally*. But **"the claim is true" ≠ "the work established it."**
- **The work writeup `run2/work/trust-laundering.md` is STALE/WRONG as written** — lines 47/118 still assert
  "L1: HOLDS over full grid. L2: HOLDS over full grid" for the printed WITNESS, which is false under genuine
  Total Trust. The report flags this so the writeup is not read as a finding.

**Status of the TODO:** non-transitivity of genuine DDB Total Trust is **plausibly true** (gate-located,
not original-author-validated), but the executor's search, headline witness, genericity statistic, and
recovery characterization are **all on a 32-point indicator shadow and none is validated**. A real-grid
re-run is required before any number — including the recovery condition — is cited.

---

## 5. What remains PROOF-ONLY (and why) — no fake Lean was produced for these

These are honestly *not* Lean-tractable yet; an honest "no Lean here" is the correct outcome.

- **The LI cross-agent / D3 recovery characterization** (the `LUV-Total-Trust(H→B)` martingale, the
  conditions under which delegated trust composes for *logical inductors*). PROOF-ONLY because it needs the
  LI machinery and the `≂ₙ` asymptotic layer; explicitly out of scope of `trust-laundering` and untouched.
- **Geanakoplos VoI≥0 in general** and **Aumann's two-agent agreement theorem proper.** The lab built
  *finite single-frame instances/illustrations*; the general theorems are established prose, deliberately not
  re-derived (OFF-LIMITS) and not honestly finitely formalizable as stated.
- **Which κ is "correct"** in `edt-node-value`. κ is a modeling input; selecting it (deciding when an agent's
  self-model *should* sever an acausal coupling) is a normative/decision-theoretic question, not a finite
  algebra fact. The dropped Christiano reflective-probability and dependent-typed candidates (TODOS §DROPPED)
  correctly self-identify as infinitary/truth-definability obstructions — deferred, not faked.
- **The mapping from any of these finite facts to the actual LI trader/market.** Every "trader budget,"
  "endorsement," "future self" gloss is INTERPRETATION; the kernel checked the arithmetic/structure, never the
  LI realization.

---

## 6. Concrete next steps

1. **`trust-laundering` re-run (highest value, unblocks a citable cross-agent result).** Replace `link_holds`'s
   `{0,1}^W` grid with the genuine `∀X:W→ℝ` test — for the conditional-mass inequality on a fixed finite frame
   this is a **finite LP / vertex check** (the inequality is linear in `X`, so checking the extreme rays of the
   conditioning cone is exact, not a sampled grid). Reissue *all* numbers (witness, genericity %, recovery
   characterization) under the faithful predicate. Until then cite **none** of them.
2. **`aumann-modesty` proper self-evident sub-event.** Re-build with `C` a *proper* S4-self-evident subset
   (not the whole space) so `C_is_knowledge_fixed_point` is a non-trivial fixed point and the cover
   "two overlapping cells tile a proper common-knowledge event" is genuinely surprising. Also kernel-confirm
   attack2 (its conclusions follow from source but did not reach a kernel exit in the gate).
3. **`negative-voi` strict near-miss.** If a menu exists where the partitional anchor makes the refined
   expert *strictly* win (not tie), build it — it would upgrade "stops losing value" to "gains value" and make
   the Blackwell-monotonicity restoration sharp.
4. **`averaging-hides-spikes` true cause-isolation.** Find a near-miss hypothesis that *does* exclude the
   single catastrophic round (e.g. bound the **running sup** directly, or a per-round budget that is summable),
   closing the "1.5 of 2" gap so the cause of the existence direction is fully isolated.
5. **Bridge `edt-node-value` toward κ-selection.** State (PROOF-ONLY first) the condition on κ under which the
   EDT/UDT divergence vanishes for an *inductor's* self-model — the genuine deference question the finite file
   relocated but did not answer.

---

### Faithfulness gate × critique reconciliation (for the record)

The gate returned 4 REAL + 1 SHADOW; the critique upholds every verdict but trims research over-claims. This
report adopts the critique's trims verbatim: `aumann-modesty` is a single-agent tower step (not agreement),
`negative-voi`'s near-miss is a tie, `averaging-hides-spikes` is ≈1.5/2 pieces, `edt-node-value` is
κ-conditional with a net-of-own-cost gap, and `trust-laundering` is a shadow whose true claim awaits a
real-grid re-run. No verdict is overturned; nothing labelled "salvageable"; no shadow called a result.
