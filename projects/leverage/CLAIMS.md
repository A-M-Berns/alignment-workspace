# Claims registry — leverage

**Specification layer.** Every entry's *statement of record* is a checker
invocation or a fully-qualified Lean declaration, never prose. The class is part
of the claim; a class change is a diff to this file and therefore a maintainer
act. See `AGENTS.md`.

Schema: `### <id>` followed by one fenced `json` block with `class`,
`statement_of_record`, `answers_item`, `provenance`, and `docs`.

## The frozen consolidation is not migrated into this registry

`frozen/consolidation_aug9/` carries **180 claims** with their own statuses. They
are **deliberately not re-registered here**, and the reason is not laziness.

Their statements of record are theory-part prose plus a verifier **inside the
frozen tree** — code that predates this regime and that a contributor did not
write, but that is also not the house checker harness. Re-registering them would
mean either relabelling 180 claims under a class vocabulary they were not stated
in, or asserting that the house checkers adjudicate them, and neither is true.
The frozen tree is immutable, so its own labels cannot be changed even if that
were desirable.

What holds instead: the tree is a **foundation**, verified continuously by CI's
`foundations-verification` gate, which re-runs its own verifier on every push and
confirms 180 claims with statuses agreeing between its theory parts and its
ledger. Cite its claims by identifier against the frozen path, carrying the
status the tree itself gives them.

Migrating selected claims — most naturally as Lean ports — is filed as an open
problem rather than done by relabelling.

---

## Registered claims

### smoke.faf-asymp-refl

```json
{
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Smoke.faf_asympEq_refl"
  },
  "answers_item": "13",
  "provenance": {
    "generator": "maintainer's round 2026-08-10-repo-scaffolding",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "SETUP_REPORT.md",
    "human": "README.md"
  },
  "note": "Reaches a real declaration in the pinned dependency. Certifies the chain, not mathematics."
}
```

### smoke.chain-compiles

```json
{
  "class": "lean-proved",
  "statement_of_record": {
    "kind": "lean",
    "declaration": "Workspace.Smoke.chain_compiles"
  },
  "answers_item": "13",
  "provenance": {
    "generator": "maintainer's round 2026-08-10-repo-scaffolding",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "SETUP_REPORT.md",
    "human": "README.md"
  },
  "note": "States a Mathlib limit in the dependency's own vocabulary, so it typechecks only if both halves of the chain agree."
}
```

### simplex.rational-points-sum-to-one

```json
{
  "class": "enumeration-verified",
  "statement_of_record": {
    "kind": "checker",
    "checker": "enumeration",
    "parameters": {
      "domain": "rational-simplex",
      "dimension": 3,
      "denominator": 6,
      "property": "satisfies-linear-constraints",
      "constraints": [
        {"coefficients": [1, 1, 1], "rhs": 1, "equality": true}
      ]
    }
  },
  "answers_item": "13",
  "provenance": {
    "generator": "maintainer's round 2026-08-10-contribution-architecture",
    "review_status": "ci-only"
  },
  "docs": {
    "verification": "GOVERNANCE_REPORT.md",
    "human": "GOVERNANCE_REPORT.md"
  },
  "note": "A worked example of the schema, not a research result: the house enumeration checker generates the 28 rational simplex points at denominator six and confirms each sums to one. It exists so the registry, the checker and the CI job are exercised by something real before any research claim depends on them."
}
```
