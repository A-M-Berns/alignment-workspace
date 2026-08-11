# BRANCH-PROTECTION ROUND — payload audit + flip runbook

*Dispatched 2026-08-11. Verbatim as sent, per `prompts/README.md`.*

*Prompt author: Claude Fable 5 (Anthropic), 2026-08-11, in a maintainer-directed
session. Dispatched by the maintainer.*

---

Extends the governance architecture; AGENTS.md rules apply. This round prepares
and (where possible) applies branch protection. The visibility flip itself remains
reserved to the maintainer — never change visibility.

## A. Audit the committed payload against the decided semantics

Verify, and correct where wrong (each correction is a normal commit with reasons):

1. **Required approvals = 0.** This is deliberate and load-bearing: GitHub forbids
   self-approval, so "require 1 approval" would mechanically reinstate a two-human
   gate on every maintainer PR — the exact thing the constitution decided against
   (DECISIONS, 2026-08-11). Enforcement lives in required checks, not required
   reviews. If the payload says 1 (or more), set it to 0 and note why in the
   commit.
2. **Required status checks: exactly the eight gate names**, matching the CI job
   names string-for-string (path-gate, checkers, conservativity, python,
   frozen-integrity, foundations-verification, lean, dco — use the true job-name
   strings from ci.yml, not this prose).
3. **Force-pushes blocked and branch deletion blocked** on main — this is what
   makes git history immutable in fact rather than by convention, and the frozen
   discipline presumes it.
4. **Enforce for administrators: ON.** Recorded understanding (put it in the
   DECISIONS entry): the repo owner can always disable protection in settings, so
   this is a latch, not a lock — it does not stop deliberate bypass; it converts
   accidental or lazy bypass into a visible, deliberate settings change. That is
   the intended amount of self-binding.
5. **PRs required** for all changes to main (no direct pushes).

## B. Check names become spec

Add to AGENTS.md (spec layer): CI job names are spec-layer values. Required
status checks match job names by exact string, so renaming a CI job silently
breaks enforcement in one of two directions (blocks everything, or stops
requiring the real gate). Any job rename must update the protection payload in
the same PR, and the payload file is the source of truth for the required-check
list.

## C. Apply now if the plan allows; otherwise stage

Attempt to apply the audited payload to main via the API while the repo is
private. If GitHub rejects it (branch protection on private repos requires a
paid plan), do not treat this as failure: commit the audited payload plus a
one-command application script (gh api, no third-party dependencies), and write
FLIP_RUNBOOK.md at repo root containing the flip-minute procedure below. If it
applies while private, the runbook shrinks accordingly (protection is already
live; the flip is just the flip) — write it anyway.

## D. FLIP_RUNBOOK.md — the flip minute, exactly

For the maintainer to execute, in order, at a moment they are at the keyboard:

1. Flip visibility to public (Settings → General → Danger Zone, or gh api).
2. Immediately run the application script; confirm via API that main reports:
   required checks = the eight names, approvals 0, force-push and deletion
   blocked, admins included.
3. Only then link, announce, or reference the repo anywhere. Exposure begins at
   attention, not at the visibility bit; the unprotected-public window binds only
   accounts with write access (the two maintainers), so executed in one sitting
   its risk is a maintainer's accidental direct push during that minute and
   nothing else.
4. DECISIONS.md entry: went public, protection applied, date.

Note in the runbook what the flip does NOT discharge, so it can't be executed by
momentum: the maintainer's read-through sign-off of the note-dump conversations
must already be in DECISIONS.md before step 1 (release gate), and the checker
harness remains llm-unreviewed until the maintainer's pass — public flip does not
change its provenance class.

## Report

ROUND_REPORT.md per convention: payload deltas found in the audit (list each,
before/after), whether protection applied while private or was staged, the exact
eight check-name strings as committed, and confirmation that the runbook's
preconditions section names the release gate.
