# Counterfactual legitimacy: a trust-facing interface

**Verdict: `interface-closed-by-role / trust-premise-integrity /
target-bridge-open`.**

Internally accountable trajectory plus counterfactual non-capture is a viable
architecture for legitimate deference. It is four clauses, not one, its protected
object is defined by role rather than enumerated, and what it buys on the
deference side is the integrity of a hypothesis rather than a new theorem.

**The interface.** Answerability, coverage, access, non-capture. The two
counterfactual clauses compare advisor policies; coverage compares a run to what
was due, and is the only clause a single realized run determines. A class every
member of which withholds the same due reason satisfies access and fails
coverage, which is why they are separate.

**The protected object.** The normative response function — what the process
answers to *what arises*, *what settles*, *what may merge*, *what bears* — taken
along the run. A field is protected exactly when changing it changes an answer,
so a writable field answering nothing is outside, merge policy is inside without
being named, renaming is equivariant, and an advisor that captures the process
and hands it back before the horizon is caught. The five coordinates of the first
pass are a sound but incomplete presentation of it.

**The deference side.** `GradeTrust` in
`lean/Workspace/Deference/Contrib/DelegationBridge.lean` is the workspace's
operative trust predicate, and its own docstring records that it is imported and
not derived. It can be made true from either side: `A`'s model tracking a fixed
grade, which is competence, or the grade moving onto a fixed model, which is
capture. `manufactured_trust` exhibits the second — every record-internal
condition holding, grade trust bought at zero, and delegation then selecting what
the environment convicts. Legitimacy is what closes that route, given that the
grade factors through the protected object; `grade_reads_outside` witnesses that
the factorization is a real premise and not free.

**What blocks a deference theorem.** Not legitimacy. The finite skeleton declares
"the relation between `v⁺` and `X` — none" (`FINITE_MODEL_SKELETON.md` §8.5), so
whether the principal's grade tracks the quantity that matters is open upstream
of anything here.

- `LEGITIMACY_INTERFACE.md` — the four clauses, the protected object, what `Due`
  and `Licensed` must export, and how each clause could be assured.
- `LEGITIMACY_TO_TRUST_INTERFACE.md` — the deference statements by exact path,
  the three-column table, the candidate theorem, and the bearing on a live
  ledger decision about endpoint-preservation.
- `COUNTERFACTUAL_INTERFACE.md` — the clauses, quantifiers and coupling.
- `MODEL.md` — the paired-run model and what is provisional.
- `PROSECUTION.md` — the attack and control matrix.
- `THEOREM_MAP.md` — every statement, classified.
- `BOUNDARY.md` — what this establishes, and who could check it.
- `src/`, `tests/`.

```sh
python3 tests/run.py
```

The procedural-legitimacy round's `src/` is a declared dependency: its
`Trajectory`, its four conditions and its target `L*` are the objects prosecuted
here rather than re-implementations of them.

Nothing here is registered in `CLAIMS.md` and nothing is in Lean.
