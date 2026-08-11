# aumann-modesty — Aumann's averaging step fails under modesty (overlapping-cell witness + partitional near-miss)

- **id:** `aumann-modesty`
- **modality:** LEAN-CORE
- **status:** PROVED (kernel-checked, sorry-free, axioms clean) — see axiom audit below.
- **artifact (the deliverable):** `run2/lean/aumann-modesty.lean`
- **supplementary EXEC cross-check:** `run2/work/aumann-modesty-sanity.py` (exact-rational
  recomputation + exhaustive search; not the deliverable, a faithfulness witness).

---

## What the result says (informal)

Aumann's agreement machinery has a load-bearing **averaging step**: if an event `C` is
common knowledge (self-evident) and is *tiled by the cells of a partition*, and the posterior
of a random variable `X` is common knowledge and equal to some value `q` on those cells, then
the overall posterior `E_π(X | C)` equals `q`. That is the law of total probability over a
partition, and it is what forces rational agents with a common prior to agree.

**This step is exactly the Euclidean (S5 / partitional) ingredient of v2 §1.1.** Drop the
Euclidean property — i.e. let the agent be **modest** (an S4, non-partitional information
correspondence, the v2 §5.2 regime) — and the cells that *cover* a self-evident event can
**overlap** instead of partitioning it. Then the per-cell posteriors can differ, the overall
posterior matches neither, and there is no common-knowledge value `q` for the averaging
identity to deliver: **Aumann's averaging step fails.** Restoring partitionality restores it.

The lab-specific reading (INTERPRETATION, per the TODO): v2 §5.2's modesty/immodesty
dichotomy **is** the non-partition/partition dichotomy, here *instantiated* rather than argued
by analogy. The safety gloss: persistent disagreement between a principal and a trusted modest
AI is not by itself evidence of irrationality — it is the structural signature of dropped
negative-introspection. The negative phenomenon itself is classical (Geanakoplos's
game-theory-without-partitions); **we cite it, we do not claim to discover it.** The
contribution is the explicit, kernel-checked lab instance and its partitional near-miss.

---

## The concrete frame (all finite, decidable; NO LI machinery, NO asymptotics)

Worlds `Fin 4`, uniform common prior `π ≡ 1/4`, random variable `X = (1, 0, 1, 0)`
(equivalently the indicator of the event `{0,2}`).

- **Information correspondence** `E : Fin 4 → Fin 4 → Bool`:
  `E 0 = {0,1,2}`, `E 1 = {1,2}`, `E 2 = {1,2}`, `E 3 = {1,2,3}`.
  - `E_reflexive`, `E_transitive` — `decide`-checked (so it is an S4 / positive-introspective
    correspondence).
  - `E_not_euclidean` — axiom 5 fails (`decide`).
  - `cells_overlap_not_nested` — cells `E 0` and `E 3` **genuinely overlap** (share `{1,2}`)
    and are **non-nested** (`0 ∈ E 0 \ E 3`, `3 ∈ E 3 \ E 0`). `decide`-checked. A partition
    would force cells equal-or-disjoint; these are neither ⇒ genuinely non-partitional.

- **Self-evident event** `C = {0,1,2,3}`. Defined via the *real* knowledge-operator fixed
  point, NOT a free Boolean label:
  - `knows S w := decide (E w ⊆ S)` (the agent knows `S` at `w` iff its info set lies in `S`).
  - `C_self_evident` : `C ⊆ knows C` (closed under `E`).
  - `C_is_knowledge_fixed_point` : `C = knows C` (genuine common knowledge throughout).
  - `C_is_union_of_cells` : `w ∈ C ↔ ∃ w' ∈ C, w ∈ E w'` (a real meet/cell-union event).
  - `C_nonempty`. All `decide`-checked.
  - `cells_cover_C` : `E 0 ⊆ C`, `E 3 ⊆ C`, and `E 0 ∪ E 3 = C` (the two overlapping cells
    cover `C`). `decide`-checked.

- **Posteriors** `post S := (∑_{v∈S} π v · X v) / (∑_{v∈S} π v)`. These are the **CONCLUSION**,
  computed from `π` and `E` (not hypotheses):
  - `post_E0 = 2/3`, `post_E3 = 1/3`, `post_C = 1/2` (`norm_num` over `Fin.sum_univ_four`).

## The failure (headline)

- `covering_cells_disagree` : `post (E 0) ≠ post (E 3)` — the two covering cells of the
  self-evident `C` carry **strictly different** posteriors (`2/3 ≠ 1/3`).
- `no_common_knowledge_value` : `¬ ∃ q, post (E 0) = q ∧ post (E 3) = q` — **no single
  common-knowledge value exists** for the averaging identity to use.
- `averaging_target_unattainable` : `post C ≠ post (E 0) ∧ post C ≠ post (E 3)` — even the
  overall posterior `1/2` matches **neither** cell, so Aumann's conclusion `post C = q` is
  unattainable for any cell-consistent `q`.
- `nonvacuity_witness` : a single bundled theorem asserting, all at once and all checked:
  `∑π = 1`, `π > 0`, `E` reflexive+transitive, cells overlap & non-nested, `C` self-evident &
  nonempty & covered, and `post_E0 = 2/3`, `post_E3 = 1/3`, `post_C = 1/2`. This is the
  **required non-vacuity witness**: a concrete `π, E, X, C` with everything decide/norm_num-
  checked and the two distinct covering posteriors as the conclusion.

## The mandatory near-miss (partitional ⇒ averaging holds ⇒ forced agreement)

- `partition_averaging` (GENERAL lemma, fully proved, no `decide` on the frame): for **disjoint**
  cells `S₁, S₂` with `S₁ ∪ S₂ = C`, positive masses, and a **common** posterior `q`, the
  overall posterior `post C = q`. This is finite-Aumann-proper: the averaging step the
  overlapping cover destroyed. The hypothesis the overlapping witness lacks is `hdisj`
  (disjointness).
- `Ehat` : a concrete **partitional / Euclidean (S5)** correspondence on the **same** `π`:
  `Ehat 0 = Ehat 1 = {0,1}`, `Ehat 2 = Ehat 3 = {2,3}`. `Ehat_reflexive`,
  `Ehat_transitive`, `Ehat_euclidean` all `decide`-checked (an equivalence relation = genuine
  partition). `Ehat_partition_of_C` : its cells `{0,1}`, `{2,3}` are disjoint and cover `C`.
- `post_Ehat0 = post_Ehat2 = 1/2` — both partition cells **share** the posterior `1/2`
  (a genuine common-knowledge value, so the lemma genuinely bites).
- `aumann_holds_under_partition` : `post C = 1/2`, derived by **applying `partition_averaging`**
  to `Ehat`. The averaging step that FAILED on the overlapping cover now HOLDS, and agreement
  is **forced** by partitionality. (This is the compiled near-miss.)

## "Weaker hypothesis ⇒ FALSE"

- `disjointness_essential` : taking the **same** averaging template but on the original
  **overlapping** cover `E 0, E 3` (i.e. dropping disjointness) makes the conclusion false —
  the cells disagree, the target matches neither, yet they DO cover `C` and DO overlap. So the
  single failed hypothesis is disjointness; **overlap is exactly what breaks Aumann.**

---

## Supplementary EXEC faithfulness witness (`aumann-modesty-sanity.py`)

Independent exact-rational recomputation of the same frame confirms every posterior the Lean
asserts (`post_E0=2/3`, `post_E3=1/3`, `post_C=1/2`, `post_Ehat*=1/2`, forced `post_C=1/2`),
**and** runs an exhaustive search over all reflexive+transitive correspondences on `Fin 4`
with this prior (355 frames, 349 shared-value 2-cell covers of a self-evident `C`):

```
averaging BROKE with DISJOINT cells:     0   (expected 0)
averaging BROKE with OVERLAPPING cells: 16   (>0: overlap is what breaks it)
RESULT: PASS — disjoint covers NEVER break averaging; only overlap can.
```

This is the structural converse to the Lean near-miss: across the whole frame space, the
averaging identity is broken **only** by overlap, never by a disjoint (partitional) cover —
exactly the modesty/partition dividing line.

---

## What I did NOT establish / honesty boundary

- **No LI / asymptotic / cross-agent content.** This is a pure finite-probability fact about a
  single agent's information correspondence. It does **not** prove anything about logical
  inductors, the `≂ₙ` layer, or two communicating inductors. The connection to v2 §5.2
  ("modest = non-partitional") is an **INTERPRETATION**, stated as such; the Lean checks the
  finite-frame fact, not the LI realization.
- **Not a re-skin of OFF-LIMITS results.** `CM_implies_immodest` (CM-identity ⇒ immodest fiber
  collapse) is a *different* statement (it derives immodesty from a martingale identity at one
  world); nothing here re-derives it. The `AntiExpert` Fin-2 novice/expert Value frame is a
  *different object* and is not reused — this is a genuinely new 4-world frame about
  posteriors/averaging, not Value/Total-Trust. v2 §1.1's S4/S5 exposition is used as
  background, not re-proved.
- **The negative result is classical** (Geanakoplos). The novelty is the *instantiated lab
  witness + partitional near-miss + the kernel-checked exhaustive boundary*, not the discovery
  that non-partitional information defeats Aumann.
- **No shadow.** The differing posteriors and "no common `q`" are CONCLUSIONS computed from
  `π, E`; `C` is a decide-checked knowledge-operator fixed point (not a label); the cells
  genuinely overlap (decide-checked non-nestedness). None of the failure is assumed.

## Axiom audit

`bash deference-trust-lab/lean/check.sh <abs path>` → **exit 0, no errors, sorry-free.**
Every theorem depends only on the standard Mathlib axioms `[propext, Classical.choice,
Quot.sound]` (or a subset); **no `sorryAx`** anywhere:

```
'AumannModesty.E_reflexive'                 depends on axioms: [propext]
'AumannModesty.E_transitive'                depends on axioms: [propext]
'AumannModesty.E_not_euclidean'             depends on axioms: [propext, Quot.sound]
'AumannModesty.cells_overlap_not_nested'    depends on axioms: [propext, Quot.sound]
'AumannModesty.C_self_evident'              depends on axioms: [propext]
'AumannModesty.C_is_knowledge_fixed_point'  depends on axioms: [propext]
'AumannModesty.C_is_union_of_cells'         depends on axioms: [propext, Quot.sound]
'AumannModesty.cells_cover_C'               depends on axioms: [propext]
'AumannModesty.post_E0'                     depends on axioms: [propext, Classical.choice, Quot.sound]
'AumannModesty.post_E3'                     depends on axioms: [propext, Classical.choice, Quot.sound]
'AumannModesty.post_C'                      depends on axioms: [propext, Classical.choice, Quot.sound]
'AumannModesty.covering_cells_disagree'     depends on axioms: [propext, Classical.choice, Quot.sound]
'AumannModesty.no_common_knowledge_value'   depends on axioms: [propext, Classical.choice, Quot.sound]
'AumannModesty.averaging_target_unattainable' depends on axioms: [propext, Classical.choice, Quot.sound]
'AumannModesty.nonvacuity_witness'          depends on axioms: [propext, Classical.choice, Quot.sound]
'AumannModesty.partition_averaging'         depends on axioms: [propext, Classical.choice, Quot.sound]
'AumannModesty.Ehat_euclidean'              depends on axioms: [propext]
'AumannModesty.aumann_holds_under_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
'AumannModesty.disjointness_essential'      depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both the headline failure (`nonvacuity_witness`, `covering_cells_disagree`,
`no_common_knowledge_value`, `averaging_target_unattainable`) and the mandatory near-miss
(`partition_averaging`, `aumann_holds_under_partition`, `Ehat_euclidean`,
`disjointness_essential`) compile clean.
