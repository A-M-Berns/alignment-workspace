Use this as the closeout prompt:

---

# Prompt: close out PR #47 and merge

Work in the live `A-M-Berns/alignment-workspace` repository on **PR #47, “Legitimacy: consolidate afoundational normative record and inquiry.”**

This is a **closeout pass, not another research round**. The conceptual consolidation is good and should land. Make only the repairs needed to leave the PR technically accurate, epistemically calibrated, and merge-ready. Then **merge PR #47 into `main`**.

Start by fetching the current PR head and reviewing the live diff. Do not rely solely on this prompt if the branch has moved.

## 1. Fix the authority-genealogy DAG bug

In the current finite witness, `authority_roots` appears to use one global `seen` set and treats revisiting any previously traversed node as an authorization cycle.

That is incorrect for a DAG with convergent ancestry.

For example, a valid structure like

```text
        act
       /   \
      a     b
       \   /
        seed
```

must not be rejected merely because `seed` is reached along two different parent paths.

Repair the traversal so that:

* genuine cycles are rejected if cycles are possible at this abstraction;
* ordinary DAG convergence is accepted;
* repeated ancestry does not duplicate root identities;
* strict pre-state/index ordering remains the primary reason cycles should be impossible in accepted records.

Add adversarial tests for at least:

1. two license parents sharing the same seed;
2. a deeper diamond-shaped DAG;
3. whatever malformed cyclic/non-pre-state object is appropriate to ensure the checker still fails closed.

If strict decreasing indices make a genuine accepted cycle impossible, make the implementation reflect that cleanly rather than maintaining a misleading cycle test.

## 2. Strengthen or recalibrate the scheduler-bridge executable tests

The prose derivations for the restricted Set Cover with Delay and MLSC/submodular-ranking bridges are useful.

However, the current executable checks are too close to tautological if:

```python
scd_objective(...)
```

simply delegates to

```python
inquiry_delay_objective(...)
```

and

```python
mlsc_unit_metric_objective(...)
```

simply delegates to

```python
fixed_docket_latency(...)
```

Do one of the following, preferring the stronger option if it remains small:

### Preferred

Implement the two sides of each tested translation independently enough that equality is a meaningful executable witness.

For SCD, independently compute:

* inquiry-side action/service/delay objective;
* translated SCD purchase/request objective.

For the unit-metric MLSC/submodular-ranking bridge, independently compute:

* inquiry-side sum of liability cover times;
* translated ranking/MLSC objective.

Then test equality on multiple nontrivial finite examples.

### Acceptable fallback

If independent implementations would add disproportionate machinery, explicitly weaken the documentation from language suggesting the code “verifies the exact reduction” to language such as:

> the paper derivation establishes the objective-preserving translation; the executable example is a finite sanity check of the identified objective.

The theorem map, memo, PR description, and tests should all use the same calibration.

Do **not** weaken the actual paper derivation merely because the old test was tautological.

## 3. Recalibrate the narrow-waist conclusion

The round correctly found that the naive three-constructor proposal

```text
Root / Undertake / Account
```

does not by itself expose all the historical information needed by the current implementation.

But do not overstate this as a proof that `Accrue`, `BasisLost`, etc. are irreducible primitive constructors.

Distinguish:

> the three-constructor proposal as currently typed is insufficient

from the stronger, currently unresolved claim:

> no semantics-preserving representation of accrual/review can be compiled into a smaller event calculus.

The latter is exactly a future **narrow-waist representation question** and should remain open.

Likewise, due tokens are currently usefully modeled as distinct from docketed commitments, but the round has not proved an impossibility theorem against every alternate representation.

Adjust `MEMO.md`, `THEOREM_MAP.md`, wiki prose, and PR description where necessary so that the verdict is:

* **partial unification under the tested representation**;
* operational distinctions identified;
* true representation-theoretic minimality remains open.

Do not undo the useful positive result that docketed inquiry tasks reuse the answerability liability/account kernel.

## 4. Preserve the seed question as an explicit open problem

The wiki's treatment of the afoundational seed is good, but the round does **not** explain where the initial normative induction comes from.

Make sure the final state clearly distinguishes:

[
S_0=\text{current positive-model initialization interface}
]

from a future theory of

[
I_0\xrightarrow{\mathrm{Uptake}}R_0
]

where an induction history might be mostly empirical/social/practical and the irreducible primitive normative expenditure could be thinner than an arbitrary bundle of substantive norms.

Do not build that theory in this closeout pass.

Just ensure that the current documentation does not sound as though “assume (S_0)” settles normative bootstrapping.

A good explicit next question is approximately:

> Can the seed be factored into an ordinary induction history plus a minimal primitive uptake/participation license, and what normative structure must that uptake operation contain?

Also preserve the excellent checker-boundary observation:

> any substantive normative permission hardcoded into the fixed checker is itself another primitive normative expenditure.

## 5. Do not broaden scope

Do **not**:

* start a new research round;
* attempt the `R -> O` compiler;
* attempt the bootstrapping theory;
* attempt a representation theorem for the narrow waist;
* change counterfactual-legitimacy theory;
* promote any unregistered result;
* add Lean merely for the sake of formalization;
* rewrite unrelated wiki or repo material.

This pass is for correctness and merge readiness.

## 6. Final verification

After repairs:

* run the new afoundational-inquiry test suite;
* run all relevant legitimacy tests;
* run `python3 tests/run.py`;
* run structured-state checks;
* run wiki link/binding checks;
* ensure no registered claim changed;
* inspect the full diff;
* ensure terminology/status labels agree among:

  * `MEMO.md`
  * `THEOREM_MAP.md`
  * round `README.md`
  * `wiki/Normative-Record-and-Inquiry.md`
  * PR description.

Update the PR description if needed to accurately report the repaired state.

The final status should remain approximately:

```text
research round: unregistered
conceptual consolidation: adopt
finite witnesses: repaired and green
general mathematical claims: paper derivations / interfaces unless otherwise marked
narrow-waist minimality: open
normative bootstrapping beneath S₀: open
R -> O: open
```

## 7. Merge

If all tests/checks are green and the final diff is internally consistent:

1. ensure PR #47 is mergeable and current with the intended base;
2. merge it into `main` using the repository's normal merge method;
3. do not leave it as a draft or merely report that it is ready;
4. report the resulting merge commit SHA and a concise summary of the closeout repairs.

If an actual merge blocker appears, fix it if it is local to this PR. Only stop without merging if resolving it would require a substantive new research decision or unrelated repository change.

The closeout standard is:

> **Land the consolidation, fix the finite-witness bug, make the executable bridge evidence honest, keep representation minimality and normative bootstrapping visibly open, and merge.**
