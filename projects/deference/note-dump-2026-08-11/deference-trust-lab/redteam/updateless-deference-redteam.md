# Red-team: Updateless Deference Model

**Target:** `models/updateless-deference-model.md` (+ `models/updateless_deference_check.py`,
`lean/updateless-deference.lean`).
**Verdict: SALVAGEABLE** — the Lean lemma is correct and will check, but the *central claim* as
written is **over-stated in two ways** (a triviality dressed as a reduction-to-endorsement, and a
"discrimination" that is supplied by hand rather than derived). Both are fixable by honest
re-labeling + one extra hypothesis. The core relation is not false; it is *under-determined* and the
prose claims more than the math delivers.

Each item flagged PROVED / SKETCHED / CONJECTURE / INTERPRETATION as in the v2 discipline. All
probes below were **executed** (`/tmp/redteam_probe.py`, `/tmp/redteam_probe2.py`); outputs quoted.

---

## A. Is the central claim actually TRUE? — partly; the discrimination is an artifact of a free input

**The relation, made fully explicit (PROVED by reading the definition + code).**
`A updatelessly-defers to u  :⇔  U(π_u) = maxₚ U(π)`, where `π_u(s) = argmaxₐ node_value[s][a]`.
So **`defers` depends on `node_value` ONLY through its per-node argmax `π_u`**, and the predicate is
*purely extensional*: "the policy `π_u` happens to globally maximize `U`." Nothing about
calibration, anticipation, van-Fraassen endorsement, or the *epistemics* of the update survives —
only "did your final policy hit my optimum."

**Probe 1 (PROVED — the decisive one). The mugging classification is not a property of the
world/`U`; it is a property of the hand-chosen `node_value`.** Hold the mugging utility `U₁` fixed
and vary only the free input `node_value`:

```
node_value = decoupled (model)     : π_u={heads:refuse}  defers=False
node_value = keeps-acausal-term    : π_u={heads:pay}     defers=True
node_value = arbitrary pay>refuse  : π_u={heads:pay}     defers=True
```

The model gets "mugging ⇒ NOT defer" **only because `node_value1` was hand-set to
`{pay:-100, refuse:0}`** (the decoupled valuation). The doc's §5.1 admits this ("the single most
important caveat"), but the §6 CENTRAL CLAIM and the task-summary still assert the relation **"fails
for the counterfactual-mugging caver"** as if the relation does the discriminating. It does not: the
modeler does, by choosing `node_value`. There is **no link in the formalism between `node_value` and
`U`** — `node_value` is an independent dict. So the "PROVED by finite witness" for clauses (ii)/(iii)
proves only "*if* you feed in a decoupling valuation, *then* `π_u` loses" — which is true but is an
input assumption, not a discriminating theorem. **The relation as defined cannot tell a caver from a
non-caver; the human modeler tells it.**

**Probe 3 (PROVED). `defers` accepts garbage/adversarial updates that "luck into" the optimum.**
A `node_value = {blue:-1000, red:-999}` (epistemically nonsense, but ranks `red>blue`) yields
`defers=True` on the "genuine improvement" example. The relation cannot distinguish a calibrated
improver from a broken-but-lucky or adversarial one. So "(UD) holds for genuine improvements UDT
accepts" is really "(UD) holds whenever `π_u` = an optimum, for *any* reason." This undercuts the
INTERPRETATION that (UD) is an *endorsement-like* or *legitimacy* test (§5.5): it is agreement-with-
optimum, blind to process. (The wireheading discussion in §5.5 silently relies on `node_value`
tracking a corrupted `U`, again a hand-supplied input.)

**Probe 4 (PROVED). Ill-defined under `node_value` ties.** With an indifferent informed self
(`node_value` ties), the verdict flips with action-list ordering (`[x,y]`→defers, `[y,x]`→not),
because `max(..., key=...)` breaks ties by position. The doc's §5.4 mentions tie non-uniqueness but
calls Thm R "robust"; the *relation itself* is **not** well-defined when the update is indifferent.

**Net (INTERPRETATION).** The central claim is true *as a classification of three hand-built
instances*, but the headline "the relation classifies the canonical examples correctly" is
misleading: the classification is carried by the externally-supplied `node_value`, which the
formalism never ties to `U`. The relation is a thin wrapper around "is `π_u` a global argmax."

---

## B. Does a hypothesis smuggle in the conclusion? — Theorem R is a true tautology about argmax,
mis-glossed as "reduction to ordinary endorsement"

**Theorem R / `defers_of_local_argmax` (PROVED, but the gloss is inflated).** On a **separable**
`U`, the hypothesis `hLoc : ∀ s a, U s a ≤ U s (nodeChoice s)` says *exactly* `nodeChoice s =
argmaxₐ U s a`. The conclusion is then term-by-term immediate (`p ≥ 0`). This is correct and
non-vacuous **as the fact "per-node argmax of a separable utility is globally optimal."** But:

1. **`u` has disappeared.** `hLoc` ties `nodeChoice` to `U`'s own node-argmax. There is no longer any
   independent "update" or "second agent" in the statement — `nodeChoice` *is* `U`'s argmax. So the
   theorem is not "`A` defers to `u`"; it is "argmax is optimal when separable." Calling this
   "reduces to ordinary (van-Fraassen) endorsement" (doc §2, Lean header) reads a rich concept into
   a tautology. **Endorsement is a relation between two belief states; here there is only one object.**

2. **It is only one direction; "reduces to endorsement" claims a biconditional that is FALSE.**
   Probe 6 (PROVED): a `node_value` whose argmax matches the global optimum but whose *numbers* do
   **not** equal `U`'s node-utilities still yields `defers=True`. So in the separable case
   (UD) ⇔ "`node_value`'s argmax = `U`'s argmax at each node", which is **strictly weaker** than
   "`A` would adopt `u`'s local verdicts" (endorsement-of-the-credence). Probe 5 (PROVED): a
   calibrated `node_value` and a numerically insane one with the same argmax are **indistinguishable**
   to (UD). Hence (UD) is *not* equivalent to endorsement even in the regime where the doc claims the
   cleanest equivalence; only the trivial `argmax⇒optimal` direction holds. **"Reduction to ordinary
   endorsement" overstates a one-directional argmax fact.**

This is the smuggling: the word "endorsement" imports content (a two-place
believes-what-the-other-believes relation) that the math (`argmax of separable U is optimal`) does
not contain.

---

## C. Lean file — predicted to TYPE-CHECK; faithful to *its own narrow* claim, NOT to the prose
"reduction to endorsement"

By careful reading (not compiled):

**Will it type-check? — YES, high confidence.**
- `policyValue p U π = ∑ s, p s * U s (π s)`; `defersTo := ∀ π, policyValue π ≤ policyValue nodeChoice`.
- Proof: `intro π; unfold policyValue; apply Finset.sum_le_sum; intro s _;
  exact mul_le_mul_of_nonneg_left (hLoc s (π s)) (hp s)`.
- `Finset.sum_le_sum : (∀ i ∈ s, f i ≤ g i) → ∑ i∈s, f i ≤ ∑ i∈s, g i` — confirmed present
  (`Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:117`, `to_additive` of `prod_le_prod'`,
  built `.olean` present). The confirmed `LeanDeference.lean:230` uses the identical idiom.
- `mul_le_mul_of_nonneg_left (hbc : b ≤ c) (ha : 0 ≤ a) : a*b ≤ a*c` — confirmed present
  (`Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean:224`); `LeanDeference.lean:222` uses it.
- Goal after `unfold` is over `Finset.univ` (`[Fintype S]`); `apply Finset.sum_le_sum` unifies,
  `intro s _` discharges `s ∈ univ`. `ℝ` supplies the ordered-monoid + `PosMulMono` instances.
- `#print axioms` will print **`[propext, Classical.choice, Quot.sound]`** (no `sorry`, no choice
  beyond Mathlib's). No `sorryAx`.

**Residual risk for the Lean-verify agent (LOW):** the two stated imports
(`Algebra.BigOperators.Group.Finset.Basic`, `Algebra.Order.BigOperators.Group.Finset`) must
transitively expose `mul_le_mul_of_nonneg_left` and the `PosMulMono ℝ` instance. They almost
certainly do (ordered-algebra is upstream of ordered-BigOperators, and `ℝ`'s instances are
foundational), and the confirmed file pulls both lemmas from a similar import set. **If it errors on
`mul_le_mul_of_nonneg_left`, add `import Mathlib.Algebra.Order.Ring.Lemmas` or
`import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs`.** No `sup'` is used, so the
proof-irrelevance defeq spot the sibling `UpdatelessDeference.lean` flagged is avoided.

**Does it mean what the prose says? — it faithfully captures the NARROW lemma, NOT the headline.**
- FAITHFUL: "for separable `U`, `p ≥ 0`, and a per-node argmax `nodeChoice`, the diagonal policy
  dominates every policy." Hypotheses are honest (decoupled type `S → A → ℝ` makes separability
  structural; `nodeChoice` arbitrary-then-constrained, so global optimality is concluded not
  assumed). **Non-vacuous** (fails for coupled `U`).
- **NOT faithful to "the deference relation reduces to ordinary endorsement"**: per §B above, the
  Lean has no second agent and proves only `argmax ⇒ optimal` (one direction). The theorem name
  `endorsement_reduction` and the header's "coincides with ordinary (van-Fraassen) endorsement"
  **claim more than the term proves.** Verify agent: the theorem is real; the *informal label*
  "endorsement" is not earned by the statement — it would kernel-check while the prose gloss remains
  an INTERPRETATION, not a proved equivalence. Flag the name as aspirational.

---

## D. Secondary finding — verification-count inflation

The model summary and §3 table claim **"6/6 cases pass"** and that clauses (ii)/(iii) including the
**"red over blue" genuine-improvement** row and **both Twin-PD** rows are "PROVED by finite witness."
The executed `updateless_deference_check.py` contains **exactly 3 cases** (mugging, Newcomb, benign
empirical). The three rows that actually demonstrate *non-triviality* (improvement ≠ default; the
reveal-vs-decouple Twin-PD pair that "isolates the mechanism") are **worked in prose only, not in the
executed checker.** "6/6 pass" is not supported by the artifact. (Re-running the .py: 3 cases, all
labeled OK.) — PROVED (by inspection/execution).

---

## E. Smallest changes that make the claims honest/substantive

1. **Tie `node_value` to `U` (the real fix for §A).** Define the update's local valuation as the
   *genuine EDT-conditional of `U`* at each node — `vₛ(a) := E_p[ U(π) | reach s, π(s)=a ]` under a
   specified self-prediction — so `node_value` is **derived**, not free. Then "mugging caver ⇒ not
   defer" becomes a theorem about *the EDT update of this `U`*, not an input. Without this, drop the
   words "the relation fails for the caver" and say "**for the EDT-decoupling update**, (UD) fails"
   — which is what is actually shown. (CONJECTURE that the EDT-derived version still classifies all
   three; needs its own check.)
2. **Downgrade "reduction to ordinary endorsement" → "in the separable case (UD) ⇔ node-argmax
   agrees with `U`-argmax."** State it as the one-directional argmax fact it is; rename
   `endorsement_reduction` to e.g. `separable_argmax_global`. Recover a genuine biconditional-with-
   endorsement only after fix (1) supplies a second belief object.
3. **Well-define ties:** specify a fixed tie-break (or quantify "defers for *some* argmax" vs "*every*
   argmax") so Probe 4's order-dependence is resolved.
4. **Either add the 3 missing cases to the .py or change "6/6 PROVED" to "3 executed + 3 by-hand."**

---

## Single most valuable next step

**Make `node_value` a derived quantity, not a free input: define `vₛ` as the explicit
EDT-conditional of the *same* `U`, and re-run all six examples.** That is the one change that turns
the model from "a relation whose verdict the modeler hand-supplies" into "a relation that *derives*
the mugging/Newcomb non-deference from `U` itself" — the actual content the thread is after, and the
prerequisite for any honest Total-Trust⇔Value (UD ⇔ endorsement) biconditional.
