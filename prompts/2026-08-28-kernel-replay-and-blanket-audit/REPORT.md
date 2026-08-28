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

### F1 — the blanket audit catches what the enumerated audit cannot

Branch `poison/ws-native-decide`, pull request 65, never merged. One declaration
appended to `lean/Workspace/Deference/Contrib/StaticViewFactorization.lean`:

```lean
theorem poison_native_decide : (List.range 64).length = 64 := by native_decide
```

No `#print axioms` line names it. It is not a proof placeholder, so the textual
scan in `tests/run.py` does not see it; it is not an `axiom` declaration, so
`tests/conservativity.py` does not see it; and its axiom —
`…poison_native_decide._native.native_decide.ax_1_1` — is minted by the compiler
and written in no source file, so nothing reading the source could see it at all.

All five gates on that one commit, from the `lean` job's log:

```
AXIOM AUDIT: 755 results across 48 files, all within ['Classical.choice', 'Quot.sound', 'propext']

BLANKET AXIOM AUDIT FAILED:
  - Workspace.Deference.Contrib.StaticViewFactorization.poison_native_decide
      depends on ['….poison_native_decide._native.native_decide.ax_1_1']
      outside ['propext', 'Classical.choice', 'Quot.sound']
BLANKET AXIOM AUDIT: 3116 declaration(s) under 'Workspace', axioms used:
  ['propext', 'Classical.choice', 'Quot.sound',
   '….poison_native_decide._native.native_decide.ax_1_1']

REPLAY: the live fixture was rejected — leanchecker still refuses
  Fixture.Unchecked.falseThm, a theorem of `False` the elaborator accepted.
REPLAY: 50 module(s) replayed, covering all 48 committed source module(s);
  the kernel accepted every declaration.
```

Build green, `conservativity` green, `tests/audit_axioms.py` green, replay green,
**blanket audit red**. Note the axiom name: it exists only in the compiled
environment, which is why the gate that reads the environment is the one that
finds it.

The same fixture in the sibling repository, on `poison/faf-native-decide`, one
`native_decide` theorem appended to `APITests/CartesianFrames.lean`:

```
condensation sorry ledger: OK — 0 sorry-dependent declarations, all ledgered
BLANKET AXIOM AUDIT FAILED:
  - APITests: poison_native_decide depends on
      ['poison_native_decide._native.native_decide.ax_1_1'] outside […]
KERNEL REPLAY: the kernel accepted every declaration in all 273 replayed module(s).
```

The build, all seven node checkers, `AxiomAudit.lean`'s enumerated inventory and
`check_sorry_ledger.py` are green on that commit. This is the pair the dispatch
asked for: the existing audit green and the new blanket gate red, on the same
commit.

A note on the fixture's own history, because it is the better half of the story.
The first revision of it explained in prose that the declaration "is not a
`sorry`" — and the textual scan caught the *comment*. A true positive about the
scan, and evidence for nothing about the poison. The fixture was reworded to
avoid the token, which is what made the demonstration honest.

### F2 — replay catches what neither axiom gate can

Branch `poison/ws-unchecked-declaration`, pull request 66, never merged.
`lean4checker`'s own `AddFalse` fixture, adapted: a `.thmDecl` whose type is
`False`, pushed into the environment with `doCheck := false`.

All three gates on that one commit, from the `lean` job's log:

```
AXIOM AUDIT: 756 results across 48 files, all within ['Classical.choice', 'Quot.sound', 'propext']

BLANKET AXIOM AUDIT: 3115 declaration(s) audited across the whole library,
  all within ['propext', 'Classical.choice', 'Quot.sound']
  — axiom-audit v0.1.2 (46024e005996495c65ef609368e11ab39c4222e3)

REPLAY FAILED:
  - leanchecker exited 1
  - 8 committed module(s) were not replayed: [… the eight the run never reached]
    replaying Workspace.Deference.Contrib.StaticViewFactorization
    leanchecker found a problem in Workspace.Deference.Contrib.StaticViewFactorization
    uncaught exception: while replaying declaration
      'Workspace.Deference.Contrib.StaticViewFactorization.poison_false':
    (kernel) declaration type mismatch, '…poison_false' has type
      Prop
    but it is expected to have type
      False
```

Build green, both axiom gates green, **replay red** — and note the second
finding, which is the module-count assertion doing its own job: the checker died
part-way, so eight committed modules were never replayed, and that is reported as
a failure in its own right rather than left implicit in the exit code.

The elaborator emitted `'…poison_false' does not depend on any axioms` during the
build, which is what the axiom audit reads. A theorem of `False` in the
environment, and the axiom gates report it clean, because that is a true answer to
the question they ask.

**A permanent in-CI fixture was achievable, and was added.** The dispatch asked
for one only if it could be had cleanly. `tests/replay_fixture/` is a
dependency-free Lake package holding the same declaration; `tests/replay.py`
builds and replays it on every run and **fails if that replay succeeds**. Three
seconds, no dependencies, reached by no glob of `lean/lakefile.toml`, audited by
neither axiom gate.

It earns its three seconds by pinning what the self-test cannot. Every null-input
case in `tests/replay.py` would pass unchanged if `leanchecker`, after some future
toolchain bump, quietly stopped rejecting anything under this repository's
invocation of it. The fixture is the case that would then fail. Its cost is
recorded rather than hidden: it reaches into `Lean.Environment`, which carries no
stability promise, so a toolchain bump can break its elaboration — and the gate
distinguishes "the fixture no longer compiles" from "the fixture was accepted",
because reporting the first as the second would be a different claim.

The equivalent for the blanket audit was **not** added, and the reason is that it
would be ceremony. The audit already refuses a report with zero declarations, a
wrong root, or a widened allowlist, and those refusals are self-tested. A live
poison would additionally require carrying a `native_decide` proof in a package
that is built on every run, which buys a case the tool's own exit code already
covers.

### F3 — a mismatched checker fails loudly, and cannot pass vacuously

There is no version to mismatch by construction: `lake env leanchecker` resolves
through `elan` to the toolchain `lean-toolchain` names. The transcript below
forces the mismatch anyway, by moving the pin under an already-built tree.

```
### 0. baseline: pin and checker agree
leanprover/lean4:v4.31.0
/Users/…/.elan/toolchains/leanprover--lean4---v4.31.0/bin/leanchecker
replaying Probe.Unreached
replaying Probe.Good
rc=0

### 1. the pin is moved forward to v4.33.1; the oleans are still v4.31.0
leanprover/lean4:v4.33.1
/Users/…/.elan/toolchains/leanprover--lean4---v4.33.1/bin/leanchecker
leanchecker found a problem in Probe.Unreached
replaying Probe.Unreached
uncaught exception: failed to read file '…/Probe/Unreached.olean', incompatible header
rc=1

### 2. the pin is moved back to v4.27.0, which predates the bundled checker
leanprover/lean4:v4.27.0
error: not a file: '/Users/…/leanprover--lean4---v4.27.0/bin/leanchecker'
elan-which-rc=1
```

Three independent things catch each case, which is the answer to "fails loudly
rather than passing vacuously":

1. `assert_toolchain` compares the pin against the path `elan which leanchecker`
   resolves, and turns case 2's exit into a message naming v4.28.0 as the release
   the bundled checker arrived in.
2. The exit code. Case 1 is `rc=1` with an explicit `incompatible header`.
3. The module-count assertion. Case 1 died after enumerating one of two modules,
   so even had it exited zero the missing module would have failed the gate. This
   is the guard that matters, because it is the only one that survives a checker
   that fails *silently*.

---

## A4 — runtimes, measured

Warm runs, `ubuntu-latest`, `.lake` restored from cache. Per-step wall times read
from the Actions API.

**alignment-workspace**, pull request 64, the `lean` job:

| step | warm | note |
|---|---|---|
| Cache `.lake` (restore) | 48 s | pre-existing |
| Mathlib oleans (`lake exe cache get`) | 31 s | pre-existing |
| Build | 2 s | fully cached |
| Axiom audit (`tests/audit_axioms.py`) | 217 s | pre-existing; re-elaborates all 48 files |
| **Blanket axiom audit** | **10 s** | includes cloning and building `axiom-audit`; 3114 declarations |
| **Kernel replay** | **57 s** | 50 modules; plus ~3 s for the live fixture |
| job total | ~6 min | was ~5 min |

**Formalized-Agent-Foundations**, branch `demo/faf-gates-run`, the `build` job:

| step | warm | note |
|---|---|---|
| Free runner disk space | 61 s | pre-existing |
| Build (`lean-action`, all default targets) | 131 s | warm GitHub cache |
| Condensation sorry ledger | 8 s | pre-existing |
| **Blanket axiom audit** | **33 s** | 28 627 declarations across 11 roots |
| **Kernel replay** | **305 s** | 273 modules |

**Verdict against the ~10 minute budget: both stay in the pull-request path in
the workspace.** Replay adds 57 seconds warm, an order of magnitude under budget,
and the blanket audit adds 10. Together they lengthen a warm `lean` job by about
one minute, against an axiom audit that already costs three and a half. Nothing
is moved to push-and-nightly here.

The number worth watching is not the one that changed. `tests/audit_axioms.py` at
217 s is 60% of this job, because it re-elaborates every file with `lake env
lean`. The blanket audit reaches every declaration in 10 s by reading the compiled
environment once. That is not a reason to replace the per-file audit — it answers
a different question and this round does not touch it — but if the `lean` job's
wall time ever becomes the constraint, that is where the time is.

In Formalized-Agent-Foundations replay costs 305 s over 273 modules — five
minutes, still inside the dispatch's budget, and the schedule there is
push-and-nightly anyway because the dispatch asked for the lighter schedule and
because that repository's pull-request path already carries a build measured in
minutes when the cache misses. Its protection on a pull request is the build,
seven node checkers, the enumerated inventory and the sorry ledger. The blanket
audit at 33 s would have been affordable per-pull-request; it is scheduled with
replay so that the two verdicts always come from the same commit.

---

## What the new gates found in existing code

### alignment-workspace — nothing, and one surprise about the enumeration

The blanket audit's first run: **3114 declarations under `Workspace`, all within
`[propext, Classical.choice, Quot.sound]`.** No violation, no debt to classify,
nothing excluded.

The number is the finding. `tests/audit_axioms.py` reports **756 results across
48 files** on the same tree. So the enumerated trust surface covers roughly a
quarter of what is built, and the other three quarters had never been asked. They
turn out to be clean, which is the outcome to want and not the outcome to assume:
the gap between 756 and 3114 was invisible before this round and is now
checked on every run.

The replay's first run turned up a second thing, and it is the reason the
module comparison is one-directional. It replayed **50 modules against 48
committed sources** — the surplus being `Workspace` and `Workspace.Leverage.Basic`,
oleans restored from an older `.lake` cache by the workflow's `restore-keys`
prefix, for modules this tree no longer has. A strict equality check would have
failed the first real run for a reason that is not a fault. Replaying *more* than
the sources name is therefore allowed and replaying *fewer* is not, which is the
direction that corresponds to something being unverified.

### Formalized-Agent-Foundations — three committed modules that nothing compiles

The blanket audit found **no axiom violation** in any audited root — **28 627
declarations across 11 roots**, all within the three:

| root | declarations | modules |
|---|---|---|
| `LogicalInduction` | 19 746 | 126 |
| `ProvabilityLogic` | 3 948 | 34 (built closure) |
| `FiniteFactoredSets` | 1 179 | 18 |
| `FactoredSpaces` | 954 | 18 |
| `Condensation` | 907 | 11 |
| `PFR` | 798 | 25 |
| `CartesianFrames` | 405 | 10 |
| `ModalAgents` | 351 | 9 |
| `APITests` | 190 | 12 |
| `ShannonInformation` | 142 | 9 |
| `AxiomAudit` | 7 | 1 |

The vendored slices are clean, which is worth having checked rather than
assumed: `PFR` and `ProvabilityLogic` together are 4 746 declarations that no
gate in that repository had ever asked about, and the `ModalAgents` cooperation
results rest on the second of them.

Kernel replay: **273 modules, kernel accepted every declaration.**

The replay found something else, and it is the round's most substantive finding
about existing code: **three committed `LogicalInduction` modules are compiled by
nothing.** They are reachable from no library root and imported by no module, so
`lake build` never touches them, `AxiomAudit.lean` never sees them, the sorry
ledger never sees them, and no node checker reads their declarations.

Classified, per the dispatch's instruction to report rather than exclude:

| module | classification |
|---|---|
| `LogicalInduction/Construction/Machine/TimedRespectsProbe.lean` | **scratch.** Its own header: "This file is a spike, not part of the formalization. It is not imported by `LogicalInduction.lean`, contributes to no endpoint, and carries no paper node." |
| `LogicalInduction/Framework/FirstOrderSubstrateProbe.lean` | **scratch.** Its own header: "Not part of the build … imported by nothing, claims no paper node, and is excluded from `AxiomAudit`." |
| `LogicalInduction/Framework/Machine/SentenceCodes.lean` | **debt.** It says no such thing. It presents itself as content — `RpnSentenceCodes.toMachine`, the machine reading of the efficient sentence-sequence class — and `Framework/RpnEmission.lean` cites it by path in prose. Nothing imports it, so nothing compiles it. |

The third is the one worth a decision. It is not scratch that says it is scratch;
it is a module written as part of the machine-reading line, pointed at from a
built module's documentation, and never compiled. Whether to wire it into the
build or retire it is a question for that line and not for a CI gate, so this
round did neither. What it did do is make the situation impossible to keep
missing: `UNBUILT` in `scripts/lean_gates.py` names all three with reasons, the
replay prints them on every run, and the list fails in both directions — a module
that is neither built nor listed fails, and a listed module that turns out to be
built fails too, so no entry can outlive the situation it describes.

A second, smaller finding from the same run: `ShannonInformation.lean` is not
compiled either, but for a structural reason rather than an oversight — the
library is globbed `.submodules`, which builds the submodules and not the root
module. `source_modules` now reads the lakefile's globs, so the three forms
(`.submodules`, `.andSubmodules`, no globs) are distinguished, with a self-test
case each. The same is true of `lean/Workspace.lean` in this repository, whose
library is globbed `Workspace.+`.

---

## What these gates do not establish

Worth stating plainly, because two new green checks invite more confidence than
they earn.

**Replay trusts the `.olean` files are structurally well-formed.** The Lean
reference manual is explicit: it "is prone to an attacker crafting invalid
`.olean` files". It is a defence against bugs in Lean's handling of declarations
and against tactics that bypass the checked environment — not against a forged
build artifact.

**The blanket audit revalidates no proofs.** It loads the environment at
`trustLevel := 1024`, taking imported constants as type-correct. It answers *which
axioms*, and its answer is only as good as the build it reads — which is exactly
why replay is its sibling and not its replacement.

**Neither says the statements mean anything.** A theorem can be kernel-checked,
axiom-clean, and vacuous, or true and about the wrong object. That is the
nonvacuity witness's job and the human read-through's job, and nothing here
touches either.

**Coverage is defined by what is on disk and what was built.** In this repository
the audit's module list comes from the source tree, so a module deleted from disk
stops being audited silently — which is correct, but is a fact about the gate
rather than about the library. In Formalized-Agent-Foundations coverage is what
`lake build` compiled, which is why the three unbuilt modules above are a finding
and not an omission.

---

## Verification

Both repositories, on the round branches:

- Full local suite green: `python3 tests/run.py` (28 project runners, every
  gate's self-test, gate coverage), `python3 -m checkers.run`,
  `python3 -m checkers.workspace_state --check`, `python3 tests/workflow_scope.py`,
  `python3 tests/dead_pointers.py`, `python3 tests/name_lint.py`.
- `python3 scripts/lean_gates.py --self-test` in the sibling repository: 42 cases.
- Every required check green on pull request 64, including the two new steps
  inside the `lean` job.
- Pull request 7 in the sibling repository green, with the two gates correctly
  **skipped** on the pull-request path and the self-test running.
- `demo/faf-gates-run`, which is that pull request plus one line adding itself to
  `ci.yml`'s push-branch list: **green**, with the blanket audit over 28 627
  declarations and the replay over 273 modules both reported in the log.

New self-test cases: 16 in `tests/replay.py`, 16 in `tests/blanket_axioms.py`,
5 added to `tests/lean_scope.py`, 42 in `scripts/lean_gates.py`. Every guard that
makes a gate fail closed has one, so removing the guard fails the self-test that
pins it.

## Housekeeping

Four branches exist only for the transcripts above and are **never merged**:
`poison/ws-native-decide` and `poison/ws-unchecked-declaration` here, and
`demo/faf-gates-run` and `poison/faf-native-decide` in the sibling repository.
The `demo/` branch exists because the push-only gates cannot run on a pull
request by design and `workflow_dispatch` is not available until the workflow
declaring it is on the default branch; it adds itself to `ci.yml`'s push-branch
list and differs from the round branch in nothing else. All four are deleted once
this report is filed.
