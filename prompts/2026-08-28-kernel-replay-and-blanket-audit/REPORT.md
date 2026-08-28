# Report — kernel replay and a blanket axiom audit

**Prompt author:** unrecorded — authored outside this repository. **Executor:**
Claude Opus 5 (Anthropic). **Dispatched and executed:** 2026-08-28. An
infrastructure round, run across two repositories: this one and
`A-M-Berns/Formalized-Agent-Foundations`.

`tests/audit_axioms.py` is **unmodified**. So are `AxiomAudit.lean` and
`SurfaceProbe.lean` in the sibling repository, the allowlist, and required-check
membership. The two gates are added beside the existing machinery, not in place
of it.

---

## The finding that reshaped the round

**`leanprover/lean4checker` is deprecated.** From Lean v4.28.0 the toolchain
ships `leanchecker` itself; both repositories pin v4.31.0. The dispatch asked for
the standalone repository pinned to the tag matching `lean-toolchain`, "failing
loudly on any version mismatch". That instruction was not followed, and the
reason is that following it would have made the situation worse rather than
better.

A pinned external checker is a second version that must be kept in step with the
first. The failure it invites — a checker one release behind the library, reading
an olean format it half-understands — is the failure the pin exists to prevent.
The bundled binary cannot be out of step because there is only one version, and
`AGENTS.md`'s trust chain gains no entry for it: it is already covered by entry
1, the toolchain pin. The deviation is recorded as a dated `DECISIONS.md` entry
rather than as a silent substitution.

`assert_toolchain` in `tests/replay.py` still checks that the pin and the binary
`elan` resolves agree, because "cannot drift" is a claim about the present
arrangement and that function is where the claim would stop being true. F3 below
is its transcript.

---

## What is installed — this repository (WP-A)

Two steps inside the existing `lean` job, and two gate scripts.

**`tests/replay.py`** runs `lake env leanchecker -v Workspace` from `lean/`. The
`Workspace` prefix is what leaves Mathlib, Foundation and
Formalized-Agent-Foundations to their own repositories; `--fresh` is deliberately
not passed, since it re-replays every imported constant into an empty environment
and that is a Mathlib-sized job for a workspace-sized library.

**`tests/blanket_axioms.py`** clones `leanprover-community/axiom-audit` at
`v0.1.2`, **verifies the commit** `46024e005996495c65ef609368e11ab39c4222e3`
after the clone, builds it under this repository's `lean-toolchain`, and runs it
with `--root Workspace --modules-from Workspace --json`. Tags are mutable, so the
tag is for readability and the commit is the pin — the same discipline
`leanprover/lean-action` applies to the same dependency.

Both are wired into `tests/lean_scope.py`, so a change to either re-runs the gate
it defines. That matters most for the pin: bumping it changes the Lean verdict
with no Lean file touched.

### A3 — the protection payload is untouched

Both steps live inside the existing `lean` job. Its `name:` — the required-check
context string, matched exactly by `.github/branch-protection.json` — is
**unchanged**, so no open pull request waits on a context that will not arrive
and the payload needed no edit. The name now understates what the job does;
`ci.yml` carries a comment saying that the steps are the authority on what the
job does and the string is an identifier.

### A2 — the audit's scope, and why it is not the tool's default

The lakefile globs `Workspace.+`. That glob builds the submodules and **not** the
root module: `lean/Workspace.lean` has no olean, which is a fact worth knowing
independently of this round. So `axiom-audit`'s default — import the root module,
audit its import closure — would have failed to find an olean at all. And even
with the root built, its closure reaches `Smoke.lean` and the two `Basic.lean`
namespace roots, neither of which imports a single `Contrib/` module: the default
would have audited three files out of fifty-two while reporting success.

The module list is therefore given explicitly, from the source tree, with
`--modules-from`. The consequence, stated because it is the price: this gate's
coverage is defined by what is on disk under `lean/Workspace/`, not by what any
module happens to import.

**Nothing was excluded.** Every committed module under `lean/Workspace/` is
audited. There is no scratch tree in this repository's Lean library to classify.

---

## What is installed — Formalized-Agent-Foundations (WP-B)

`scripts/lean_gates.py`, with three modes (`--self-test`, `--replay`, `--audit`),
and three steps in `ci.yml`. The self-test runs on pull requests too — it needs
neither toolchain nor network, and its scope assertion is what stops a new
`lean_lib` from arriving unclassified, which is a thing a pull request does and a
nightly run would only notice afterwards. Replay and the audit run on push to a
listed branch, on a nightly cron (`17 6 * * *`) and on manual dispatch, never on
a pull request.

### B1 — the library map, and the scope decision

Every `lean_lib` in `lakefile.lean` is classified **by name**, and one that is
neither audited nor excluded fails the self-test — the same fail-closed
discipline `scripts/check_paper_wiring.py` applies to the paper registry.

| library | in scope | why |
|---|---|---|
| `LogicalInduction` | audited | paper library |
| `ModalAgents` | audited | paper library |
| `CartesianFrames` | audited | paper library |
| `FiniteFactoredSets` | audited | paper library |
| `FactoredSpaces` | audited | paper library |
| `Condensation` | audited | paper library, in-progress; its `sorry` ledger stays `check_sorry_ledger.py`'s job, and that ledger's pending block is currently empty |
| `ShannonInformation` | audited | shared paper-neutral infrastructure |
| `PFR` | audited | vendored `teorth/pfr` slice — dependency code, audited anyway: it is compiled into this environment and the Shannon layer rests on it, and auditing it costs one more prefix |
| `ProvabilityLogic` | audited, **built closure only** | vendored `FormalizedFormalLogic/ProvabilityLogic` subset. Not a `@[default_target]`, so `lake build` compiles only the modules `ModalAgents` imports; the coverage is those, not all 34 source modules |
| `APITests` | audited | declarations in this environment like any other |
| `AxiomAudit` | audited | the inventory target itself |
| `MachineExec` | **excluded** | not a separate module tree — its `roots` is `LogicalInduction.Construction.Machine`, so its modules carry the `LogicalInduction` prefix and are already covered. A second root would double the work and audit nothing new |
| `Scratchpad` | **excluded** | not a `@[default_target]`; `lake build` never compiles it, so there are no oleans to check. A statement about what was built, not a judgement about the code |

The dispatch anticipated that `Scratchpad` or the vendored `PFR` slice might be
excluded. `PFR` is **not** excluded — the round could see no reason to trust
vendored code more than its own. `ProvabilityLogic` is the one genuinely partial
entry, and its partiality is recorded in the script rather than glossed: saying
"we replayed ProvabilityLogic" would read as a claim about all 34 of its modules
when it is a claim about the ones `ModalAgents` needs.

The scope checks are two-directional and each has a self-test case: an
unclassified library fails, a classification naming no library fails, an audited
library that stops being a default target fails unless it is recorded as
partially covered, and `Scratchpad` becoming a default target fails.

### B2 — the division of labour with the registered snapshots

Stated in a comment in `ci.yml`, so a future reader finds it where the gates are
rather than in a report:

> Palomar runs Comparator + NanoDa — an independent Rust type checker — over
> *registration commits*: the deep verification of a frozen snapshot. These gates
> are the everyday coverage of `main` **between** those freezes. Neither replaces
> the other. Palomar answers "is this snapshot sound, by an independent
> implementation"; these answer "did anything land on main today that the kernel
> would not accept, or that carries an axiom nobody declared".

---

## Both gates refuse a run that verified nothing

This is the design point, not a detail. A replay that checked nothing exits zero
and prints nothing, which is indistinguishable from a clean run.

**Replay** is run with `-v`, which prints one `replaying <Module>` line per
module. Those lines are parsed, printed in the CI log, and compared against the
modules the committed sources say must exist. A missing one fails. The comparison
is one-directional — replaying *more* than the sources name is fine, since a warm
`.lake` cache can hold an olean for a module the change deleted.

**The audit** is run with `--json` and its report is checked: a zero `audited`
count fails, a `root` other than the one asked for fails, an `allowed` list wider
than the three fails, an unparseable report fails, and a non-zero exit with no
violation fails. `axiom-audit` refuses an empty audit itself; this checks it
rather than trusting it.

Every one of those refusals is a self-test case, so removing a guard fails the
gate that guards it.

---

## Fixtures

The demonstration is the deliverable. Each gate was shown red on a poison branch
the other gates pass; no poison branch was merged, and each was deleted after its
transcript was captured.

### The separation, in one run

A three-module probe package, built locally under `leanprover/lean4:v4.31.0`:
`Probe.Good` (clean), `Probe.Unreached` (a `native_decide` proof named by no
`#print axioms` line), `Probe.Poison` (a theorem of `False` pushed in with
`doCheck := false`).

```
--- lake build
info: Probe/Unreached.lean:3:0: 'Probe.Unreached.also_ok' does not depend on any axioms
info: Probe/Good.lean:3:0: 'Probe.Good.trivial_ok' does not depend on any axioms
info: Probe/Poison.lean:14:0: 'Probe.Poison.falseThm' does not depend on any axioms
Build completed successfully (5 jobs).

--- blanket axiom audit
axiom-audit: 2 declaration(s) under 'Probe' use disallowed axioms:
  Probe.Unreached.native_poison._native.native_decide.ax_1_1 → [Probe.Unreached.native_poison._native.native_decide.ax_1_1]
  Probe.Unreached.native_poison → [Probe.Unreached.native_poison._native.native_decide.ax_1_1]
allowed: [propext, Classical.choice, Quot.sound]
rc=1

--- kernel replay
leanchecker found a problem in Probe.Poison
replaying Probe.Unreached
replaying Probe.Good
replaying Probe.Poison
uncaught exception: while replaying declaration 'Probe.Poison.falseThm':
(kernel) declaration type mismatch, 'Probe.Poison.falseThm' has type
  Prop
but it is expected to have type
  False
rc=1
```

Read the three blocks together. The build is green. Every `#print axioms` line
reports **no axioms at all**, including the one on the theorem of `False` — which
is what `tests/audit_axioms.py` reads, so it is green on both poisons. The audit
catches the `native_decide` and not the unchecked declaration; replay catches the
unchecked declaration and not the `native_decide`. Neither gate subsumes the
other, and neither subsumes the one that was already there.

