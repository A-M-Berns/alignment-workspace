# Kernel-replay and blanket-axiom-audit round — CI hardening, two repos

*Filed verbatim as dispatched, including anything it got wrong. Where the round's
findings contradicted the dispatch, the deviation is recorded in `REPORT.md`
rather than corrected here.*

---

KERNEL-REPLAY AND BLANKET-AXIOM-AUDIT ROUND — CI hardening, two repos

Context: Neither alignment-workspace nor Formalized-Agent-Foundations runs
external kernel replay in CI; both trust the elaborator (oleans from `lake
build` are believed, then audited for axioms inside that same environment).
This round adds two independent gates to each repo: (1) lean4checker replay,
which catches declarations that entered the environment without kernel
checking; (2) the community blanket axiom-allowlist audit, which checks every
declaration in the library — not just the trust-surface closure — against
{propext, Quot.sound, Classical.choice}. The existing AxiomAudit machinery is
NOT modified, replaced, or slimmed this round; it keeps the trust-surface
inventory role. The two additions are second opinions with different failure
coverage.

Read first:
  1. https://lean-lang.org/doc/reference/latest/ValidatingProofs/
     (what replay does and does not establish; the lean-action integration)
  2. https://github.com/leanprover/lean4checker (invocation modes, toolchain
     matching, its own test fixtures for environment hacks)
  3. https://github.com/leanprover-community/axiom-audit (setup, scope
     semantics — it audits the lakefile's lean_lib; note trustLevel := 1024,
     i.e. it classifies axioms, it does not re-validate proofs — that is
     exactly why replay is the sibling gate)
  4. Both repos' existing ci.yml, and in the workspace: tests/lean_scope.py
     (the lean gate is work-conditional), the protection-payload discipline
     (a required-check change must update the payload in the same change or
     PRs block forever), and the round-record/PROVENANCE delta gate.

Binding house rules for this round: every new gate ships with a demonstrated
failure (see Fixtures below) — a gate that has never gone red proves nothing;
gates fail closed on uncertainty; all new git dependencies pinned to full
40-char SHAs; Model trailers per commit; this prompt filed in prompts/;
round record + PROVENANCE row in the same change. Workspace demand-gating:
open the round by filing its priority item as the first commit.

WP-A — alignment-workspace:
  A1. Add a lean4checker step INSIDE the existing lean job (so it inherits
      lean_scope.py's work-conditionality and only runs when the Lean gate
      is reached). Prefer lean-action's `lean4checker: true` if it composes
      with the existing elan/cache steps; otherwise invoke lean4checker
      directly, pinned to the tag matching lean-toolchain, failing loudly on
      any version mismatch. Scope: replay the Workspace library's own
      modules, trusting Mathlib/FAF dependencies (no --fresh). The CI log
      must enumerate the modules checked and assert a nonzero count — a
      replay that silently checked nothing is the failure mode we are
      guarding against, not an acceptable pass.
  A2. Add the blanket axiom-audit as a step in the same job, dependency
      pinned by SHA, default allowlist unchanged. Decide and document scope
      (which lean_libs are audited); any violation it finds in existing code
      is REPORTED and classified (real debt vs. out-of-scope scratch), never
      silently excluded.
  A3. Required-check handling: land both steps inside the existing required
      `lean` job rather than as new job names, so the protection payload is
      untouched. If that proves impossible, the payload update ships in the
      same change, per house precedent.
  A4. Measure and report warm runtimes for both steps. If replay adds more
      than ~10 minutes to a warm PR run, do not eat the latency silently:
      keep it in the PR path only if under budget, else move replay to
      push-to-main + nightly and say so in the report.

WP-B — Formalized-Agent-Foundations:
  B1. Same two gates, lighter schedule: replay + blanket audit on
      push-to-main and a nightly cron, not per-PR. Same toolchain-pinning,
      module-enumeration, and scope-documentation requirements. Map FAF's
      lean_libs first (paper libraries, shared infrastructure, APITests,
      Scratchpad) and decide audit scope explicitly — if Scratchpad or the
      vendored PFR slice is excluded, the exclusion and its reason are
      documented in the workflow file, and anything excluded is named in
      the report.
  B2. Registered-snapshot note for the report: Palomar runs Comparator +
      NanoDa on registration commits, so this CI coverage is for everyday
      main between freezes — state that division of labor in a comment in
      ci.yml so future readers know why both layers exist.

Fixtures — the demonstration is the deliverable:
  F1. Axiom-audit poison: a temporary branch (never merged) adding a sorry
      or custom axiom to a module chosen OUTSIDE the existing AxiomAudit
      trust-surface closure. The transcript must show the existing audit
      GREEN and the new blanket gate RED on the same commit — that pair is
      the proof of non-redundancy.
  F2. Replay poison: adapt one of lean4checker's own test fixtures (an
      environment-manipulation example) to demonstrate the replay step
      going red, on a branch or locally with a full transcript. If a
      permanent in-CI self-test fixture for replay is achievable cleanly,
      add it; if not, file that as a friction item honestly rather than
      shipping a fake one — do not manufacture ceremony to satisfy the
      letter of the null-input rule.
  F3. Toolchain-mismatch check: demonstrate (transcript) that a wrong
      lean4checker version fails loudly rather than passing vacuously.

Deliverables: the two branches (workspace round branch per round machinery;
FAF as an ordinary PR), poison-branch transcripts F1–F3, runtime table, the
scope decisions with reasons, and a report section listing anything the
blanket audit found in existing code. Out of scope, explicitly: modifying
AxiomAudit.lean or SurfaceProbe.lean in any way, changing the allowlist,
touching required-check membership beyond A3, and any Palomar work.

Reservation-bar note: gate placement, scope choices, and PR-vs-main
scheduling are agent-decided and reversible per house rules. Reserve to the
maintainer only if the blanket audit finds a real violation in existing code
whose classification (debt vs. exclusion) is genuinely unclear.
