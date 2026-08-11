# Governance report — contribution architecture

2026-08-11. What was installed so that an untrusted contributor's pull request is
either verifiably correct or automatically rejected.

## Awaiting the author

1. **Auto-merge for green proof-layer pull requests.** Installed as
   **maintainer-merge required**, per the dispatch. Auto-merge is a supported
   future flip: the gates already decide correctness, so the flip is a policy
   change and not an engineering one.
2. **Approval of the initial checker set and each checker's meaning statement.**
   Three checkers, meanings quoted below. These are the judge; they deserve a
   read.
3. **Initial resource budgets.** Proposed below, flagged provisional.
4. **The specification-path enumeration.** Proposed below; it lives in
   `tests/path_gate.py`.
5. **Whether contribution namespaces are per-contributor, per-problem, or
   pooled.** Installed as **pooled** — `Workspace.<Line>.Contrib` and
   `projects/<line>/contrib/` — because it is the option that is cheapest to
   change later. Per-problem namespaces need a naming scheme, and naming is
   reserved.
6. **License and third-party redistribution**, carried over from the setup round
   and now more urgent: see the note at the end.

## What was installed

**Two layers, path-gated.** Every file belongs to exactly one. `tests/path_gate.py`
fails any non-maintainer pull request touching a specification path, and prints
the classification locally so a contributor can see where a file lands before
submitting. There is no intermediate trust tier.

**The trust chain, enumerated** in `AGENTS.md`: the pinned toolchain and kernel;
the pinned dependency commits; the axiom allowance; the CI workflow definitions;
the checker harness and its interpreter; the resource budgets. That list is the
definition of the security-critical core, and auditing this repository means
auditing that list.

**The house checker harness**, `checkers/` — stdlib only, exact rationals, short
enough to read, each with a meaning docstring:

| checker | what a passing verdict means |
|---|---|
| `witness` | the supplied instance parsed as exact rationals and the named property evaluated true on it, every step exact. **Not** that the property is the right one, nor that anything follows. |
| `enumeration` | the checker **generated the domain itself** from the parameters and the property held at every point, with the count reported. **Nothing** about any point outside it. |
| `registry` | every entry parses, identifiers are unique, classes are legal, every statement of record resolves, every entry answers a filed item. **Nothing about whether any claim is true** — it audits bookkeeping, not mathematics. |

The harness has a self-test with six cases, including that a float is **rejected**
rather than rounded and that an empty domain is **refused** rather than passing
vacuously.

**The claims registry**, `projects/leverage/CLAIMS.md`. A statement of record is a
checker invocation or a fully-qualified Lean declaration — never prose. Three
entries, and the demand rule proved itself immediately: the registry checker
**rejected all three** until the item they answer was filed.

**Demand-gating.** `PRIORITIES.md` reformatted to the item schema — precise
statement, deliverable shape, acceptance check stated as something CI runs,
context pointer, difficulty. Thirteen items.

**Three new CI jobs** — `path-gate`, `checkers`, `conservativity` — beside the
four that existed. **Seven gates, all green.** The workflow now declares
`permissions: contents: read` repository-wide: zero secrets, permanently.

**Conservativity**, `tests/conservativity.py`: no `axiom` declaration anywhere; a
recorded instance-and-notation shape per specification file, compared on every
run; `#print axioms` present in every file. `tests/spec_shape.json` is itself
specification layer, so updating it is a maintainer act.

## The specification-path enumeration — proposed

```
AGENTS.md  CONTRIBUTING.md  DECISIONS.md  PRIORITIES.md  README.md
PROVENANCE.md  SETUP_REPORT.md  GOVERNANCE_REPORT.md  LICENSE  LICENSE.*
.github/**  .gitattributes  .gitignore
checkers/**  tests/**  frozen/**  prompts/**
lean/lakefile.toml  lean/lean-toolchain  lean/lake-manifest.json
lean/Workspace.lean  lean/Workspace/Smoke.lean
lean/Workspace/*/Basic.lean  lean/Workspace/*/Spec/**
projects/*/CLAIMS.md  projects/*/MODEL.md  projects/*/README.md
projects/*/THEOREMS.md
```

Proof layer: `lean/Workspace/*/Contrib/**`, `projects/*/contrib/**`,
`projects/*/rounds/**`.

**The default is deliberate.** A path matching neither list is *not* specification
— so a genuinely new kind of file is contributable rather than blocked. The
alternative default, deny-by-default, would have meant every new file kind
needing a maintainer decision before anyone could work. Worth confirming, since
it is the one place the enumeration can be wrong in the permissive direction.

## Resource budgets — proposed, provisional

| budget | value | reasoning |
|---|---|---|
| enumeration points per claim | **200,000** | large enough for a three-coordinate rational simplex at a fine denominator; small enough that a runaway fails in seconds rather than hanging a runner |
| Lean build wall time per pull request | **25 minutes** | the cold build measured 5m19s and the warm 1m50s, so this is roughly four times the cold figure — enough headroom for a dependency bump, tight enough to catch a proof that loops |
| enumeration wall time | **not separately capped** | the point cap bounds it in practice; a separate wall-clock cap is worth adding if a property function ever becomes expensive per point |

All three are specification-layer values. A pull request that needs more is a
conversation, not an override — including `maxHeartbeats`-style option changes in
Lean files, which count as budget changes.

## Epistemic-class judgment calls

**One, and it is significant: the frozen consolidation's 180 claims were not
migrated into the registry.**

Their statements of record are theory-part prose plus a verifier *inside the
frozen tree* — code that predates this regime, that no contributor wrote, but
that is also not the house harness. Migrating them would mean either relabelling
180 claims under a class vocabulary they were not stated in, or asserting that
the house checkers adjudicate them. Neither is true, and the tree is immutable so
its own labels cannot change.

What holds instead: the tree is a **foundation**, re-verified by the
`foundations-verification` gate on every push — 180 claims with statuses agreeing
between its theory parts and its own ledger, and 26 of its internal digests.
Claims are cited by identifier against the frozen path, carrying the status the
tree gives them. Selective migration, most naturally as Lean ports, is filed
rather than done by relabelling.

The three registered entries were classed as follows: the two Lean smoke results
are `lean-proved`, which is unambiguous; the simplex example is
`enumeration-verified`, and its registry note says plainly that it is a worked
example of the schema rather than a research result. It exists so that the
registry, the checker and the CI job are exercised by something real before any
research claim depends on them.

## Deviations

1. **The three initial checkers are generic in a specific way**: the property
   *forms* live in `checkers/witness.py` and contributors select among them by
   name with parameters. A contributor needing a new property form needs a
   maintainer, which is the intended shape — but it does mean the harness's
   expressiveness, not just its correctness, is now a maintainer bottleneck. That
   is a real cost and it is the right one to pay first.
2. **Nonvacuity witnesses are specified but not yet mechanically registered.**
   `AGENTS.md` states the rule and the registry schema has room; no theorem of
   record currently needs one, since the only Lean entries are smoke results with
   no hypothesis package. The CI check that a witness term exists and typechecks
   should be built with the first real theorem, not before it, when its shape is
   known.
3. **Conservativity's clause (d)** — no change to the elaboration of existing
   files — is approximated, as the dispatch anticipated, by the build staying
   green plus unchanged axiom output. A contributor could in principle change
   elaboration in a way both miss. Tightening this needs per-declaration
   fingerprinting, which is worth doing when there are declarations worth
   protecting.
4. **The dual-register presence check is still not in CI**, filed as item 11. It
   needs a definition of "results directory" that the repository will not have
   until it has results.
5. **`GOVERNANCE_REPORT.md` and this round's other output are `llm-unreviewed`**,
   recorded in `PROVENANCE.md`. That includes the checker harness — the judge
   itself is, at this moment, unreviewed code that a model wrote. CI shows it
   runs; nobody has yet read it asking whether the rule it implements is the rule
   intended. **Of everything in this repository, that is the thing most worth the
   author's eye**, because the architecture's whole premise is that the judge is
   trustworthy and the contributions are not.

## What this does not establish

The gates run, and they are **not yet required**: branch protection remains
unavailable on a private repository on this plan, so a direct push to `main`
still bypasses everything. Until that is fixed the architecture is a convention
enforced by habit, not a mechanism. The updated payload with all seven check
names is committed at `.github/branch-protection.json`.

No claim is made that the checker harness is correct — only that it is small,
stdlib-only, exact, self-tested and readable, which is what makes reviewing it
feasible rather than what makes it right.
