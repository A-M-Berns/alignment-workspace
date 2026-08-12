# Faithfulness-gate verdict — TODO `aumann-modesty`

**Role:** independent skeptic (success = finding fakeness). **Modality:** LEAN-CORE.
**Verdict:** **REAL** (a correctly-validated, instantiated *negative* finite fact — the executor
honestly frames the negative phenomenon as classical/Geanakoplos and the contribution as the
kernel-checked lab instance + partitional near-miss).

Deliverable under attack: `run2/lean/aumann-modesty.lean` (19 theorems).
EXEC cross-check: `run2/work/aumann-modesty-sanity.py`.
Attack files: `run2/verify/aumann-modesty-attack.lean`, `run2/verify/aumann-modesty-attack2.lean`,
baseline copy `run2/verify/aumann-modesty-baseline.lean`.

---

## 1. Baseline reproduction — the executor's report is ACCURATE

Copied the deliverable verbatim to `aumann-modesty-baseline.lean` and ran `check.sh`:

```
EXIT=0   (no errors, sorry-free)
all 19 theorems depend on a subset of [propext, Classical.choice, Quot.sound]; NO sorryAx
```

The 4-decide-only structural theorems (`E_reflexive`, `E_transitive`, `C_self_evident`,
`C_is_knowledge_fixed_point`, `cells_cover_C`, `Ehat_euclidean`) carry `[propext]` /
`[propext, Quot.sound]`; the norm_num/posterior theorems carry the full standard triple. Clean.

## 2. HYPOTHESIS-INERTNESS attack — the load-bearing hypothesis is genuinely load-bearing

`partition_averaging` is the positive (near-miss) averaging lemma; its essential hypothesis is
`hdisj` (disjointness of the two cells). The file's entire thesis is *"overlap breaks averaging,
disjointness restores it."* So `hdisj` MUST be load-bearing.

**ATTACK 1 (`aumann-modesty-attack.lean`, `partition_averaging_NO_HDISJ`):** took the original
proof body VERBATIM and deleted only the `hdisj` hypothesis. Result:

```
aumann-modesty-attack.lean:57:29: error: Unknown identifier `hdisj`
aumann-modesty-attack.lean:74:29: error: Unknown identifier `hdisj`
```

The proof references `hdisj` at TWO sites (the numerator split AND the denominator split — exactly
where a world in *both* overlapping cells would be double-counted). Removing it does NOT still
compile; it breaks. **`hdisj` is NOT inert ⇒ not a shadow on this axis.** This is the decisive
settling check.

**ATTACK 5 (`aumann-modesty-attack2.lean`, `partition_averaging_NO_HCOVER`):** delete `hcover`
from the same body → CONFIRMED by kernel:

```
aumann-modesty-attack2.lean:56:15: error: Unknown identifier `hcover`
```

hcover is load-bearing too. (The compile aborted at this first error before reaching the
supplementary `fake_partition_unprovable` / `bad_set_not_self_evident` / `C_fixed_point_genuine`
probes, whose source semantics are decide/trivial and unambiguous.) Both essential hypotheses of
the positive averaging lemma — disjointness and cover — are non-inert.

## 3. CONCLUSION-TRIVIALITY attack — the headline conclusion is NOT trivially derivable

The headline FAILURE theorems take **NO hypotheses at all**:

- `covering_cells_disagree : post (E 0) ≠ post (E 3)`           — proved from `post_E0`,`post_E3`.
- `no_common_knowledge_value : ¬ ∃ q, post (E 0)=q ∧ post (E 3)=q` — proved from the above.
- `averaging_target_unattainable : post C ≠ post(E 0) ∧ post C ≠ post(E 3)`.
- `nonvacuity_witness` — bundles ∑π=1, π>0, refl+trans, overlap, non-nested, C self-evident,
  cover, and `post_E0=2/3, post_E3=1/3, post_C=1/2`, all `decide`/`norm_num`.

The "differing posteriors" and "no common q" are **CONCLUSIONS computed from π and E**, not
hypotheses. `conclusion_not_trivial` (∃ q, post C ≠ q) confirms `post C` is a *fixed* rational
(1/2), so "post C = q" for the free q of `partition_averaging` is genuinely informative, not a
tautology.

## 4. HYPOTHESIS-LAUNDERING check — the TARGET object is not assumed

The TODO's target object is the *modesty (non-partition) ⇒ averaging-failure / partition ⇒
agreement* dichotomy. Grep of every headline theorem's hypotheses: the strings `post (E 0) ≠
post (E 3)`, `no common q`, and the disagreement never appear LEFT of a `:` (as a hypothesis) in
the failure results. The ONLY `post S = q` hypotheses (`hq₁`,`hq₂`) live in the *positive*
`partition_averaging` lemma — where a SHARED value is correctly the *input* that forces agreement,
not a smuggled assumption of the failure. **No laundering.**

## 5. SHADOW-LIST, item by item (from the spec)

- **(a) naive nested 3-world "agree-to-disagree" (ships a falsehood):** AVOIDED. 4 worlds, and
  `cells_overlap_not_nested` decide-checks BOTH non-nestedness directions (`0 ∈ E0\E3`,
  `3 ∈ E3\E0`) — the cells are non-nested, so the nesting subtlety that makes the 3-world story
  false does not arise.
- **(b) "agents disagree / no q" as a HYPOTHESIS ⇒ triviality:** AVOIDED (see §3, §4).
- **(c) C as a free Boolean label instead of the knowledge fixed point:** AVOIDED. `knows S w :=
  decide(E w ⊆ S)` is the real operator; `C_is_knowledge_fixed_point : ∀w, C w = knows C w` and
  `C_is_union_of_cells` decide-check C against it. (Caveat below.)
- **(d) cells that don't genuinely overlap:** AVOIDED. `E 0 ∩ E 3 = {1,2}` (decide-checked
  overlap), and they are neither equal nor disjoint ⇒ genuinely non-partitional.

## 6. EXEC cross-check searches the REAL model

`aumann-modesty-sanity.py` (re-run by me): independent exact-rational recomputation reproduces
EVERY Lean number (`post_E0=2/3, post_E3=1/3, post_C=1/2, post_Ehat*=1/2`, forced `post_C=1/2`),
and exhaustively searches ALL reflexive+transitive correspondences on Fin 4 with this prior:

```
frames: 355   shared-value 2-cell covers checked: 349
averaging BROKE with DISJOINT cells:     0   (expected 0)
averaging BROKE with OVERLAPPING cells: 16   (>0)
RESULT: PASS — disjoint covers NEVER break averaging; only overlap can.
```

This is the structural converse of the Lean near-miss, over the real frame space — not a shadow.
I attempted to find a disjoint-cover counterexample (a partition that breaks averaging): the
search confirms none exists on Fin 4, consistent with the theorem.

## 7. Non-re-skin / OFF-LIMITS

`CM_implies_immodest` (LeanDeference.lean) derives immodesty from a martingale identity at one
world via the fiber indicator — a DIFFERENT statement; nothing here re-derives it. CRITIQUE.md §
explicitly flags D9 ("Aumann fails under modesty, finite example is LEAN-ABLE") as the cheapest
real result that round 1 SKIPPED. This TODO builds exactly that missed fruit. The §5.2
modesty≡non-partition tie is flagged INTERPRETATION; Geanakoplos cited, not claimed as discovery.

## 8. One honest caveat (does NOT change the verdict)

`C := fun _ => true` is the WHOLE space. The whole space is *always* self-evident / common
knowledge, so `C_self_evident` and `C_is_knowledge_fixed_point` are TRUE but EASY (any S4 frame
has the whole space as a fixed point). A proper self-evident *sub*-event would make those
fixed-point checks more substantive. This is a simplicity choice, not a cheat: the cover
(E0∪E3=C), the overlap, and the averaging failure are all genuine on the whole space, and C is
still checked against the real `knows` operator (not a free label). The mathematical content
— overlap ⇒ averaging fails, partition ⇒ agreement forced — is faithfully and non-vacuously
captured. (Attack 2 also checks the `knows` predicate genuinely discriminates: a bad set `{0}`
is decide-provably NOT self-evident, so self-evidence is not a vacuously-true predicate.)

---

## Verdict: REAL

Faithful to the informal claim (overlapping-cell modesty defeats Aumann's averaging step;
partitionality restores it); non-vacuous (concrete π,E,X,C with decide/norm_num-checked overlap,
self-evidence, cover, and two distinct CONCLUDED posteriors 2/3≠1/3 plus a compiled partitional
near-miss forcing 1/2); target object not assumed (the dichotomy is established, not laundered);
the load-bearing disjointness hypothesis is decisively non-inert (deleting it breaks the proof).
The negative phenomenon is correctly attributed as classical; the kernel-checked lab instance +
partitional near-miss + exhaustive boundary are the genuine contribution.
