# Round report — branch-protection audit and flip runbook

**Attribution.** Prompt author: Claude Fable 5 (Anthropic), 2026-08-11, in a
maintainer-directed session. Executor: Claude Opus 5 (Anthropic), 2026-08-11.

## Audit deltas

Four corrections. Three were the brief's; one was not, and it defeats the same
decision by a different route.

| field | before | after | why |
|---|---|---|---|
| `required_approving_review_count` | `1` | **`0`** | GitHub forbids self-approval, so requiring one approval mechanically reinstates a two-human gate on every maintainer pull request — the thing decided against on 2026-08-11. Enforcement lives in the required checks. |
| `require_code_owner_reviews` | `true` | **`false`** | **Not in the brief.** With both maintainers listed as code owners, a code-owner requirement reinstates exactly the same two-human gate. Setting approvals to zero while leaving this true would have looked correct and behaved wrongly. |
| `dismiss_stale_reviews` | `true` | **`false`** | Dead configuration at zero approvals. Removed so the file states only what it means; dead config in a spec-layer file invites misreading. |
| `enforce_admins` | `false` | **`true`** | The latch, per below. |

**Already correct, unchanged:** `allow_force_pushes: false`,
`allow_deletions: false`, `strict: true`, `restrictions: null`, and pull requests
required for all changes to `main`.

**Required status checks: verified by string comparison**, not by eye. A script
parsed the `name:` values out of `ci.yml`, sorted both lists, and compared:
8 job names, 8 contexts, **exact match including the em-dashes**.

```
checkers — house harness self-test and the claims registries
conservativity — no new axioms, specification shape unchanged
dco — every commit carries a sign-off
foundations-verification — the frozen consolidation re-proves itself
frozen-integrity — digests and the manifest rule
lean — build, sorry-free, axiom audit
path-gate — proof-layer PRs may not touch the specification layer
python — project test runners
```

## Applied, or staged?

**Staged.** Application was attempted against the live repository and refused:

```
HTTP 403 — Upgrade to GitHub Pro or make this repository public
           to enable this feature.
```

Per the brief this is not a failure. Committed instead:
`.github/apply-branch-protection.sh` — one command, `gh` only, no third-party
dependencies — which applies the payload, **reads back what GitHub actually
stored**, verifies six properties, and exits non-zero unless all hold. Verifying
by read-back rather than by trusting the write is the point: a payload that was
accepted is not the same as a protection that is correct.

## Check names are now spec

Added to the trust chain in `AGENTS.md` as item 6: required checks match job names
by exact string, so a rename breaks enforcement silently **in one of two
directions** — the branch demands a check that no longer reports and blocks
everything, or it stops requiring a gate that still runs and nothing announces it.
The second is the dangerous one, because everything looks green. Any job rename
updates the payload in the same pull request, and the payload file is the source
of truth for the list.

## The runbook

`FLIP_RUNBOOK.md` at repository root. Its preconditions section comes **first**,
before step 1, and **names the release gate**: the maintainer's read-through
sign-off of the note-dump conversations must already be recorded in
`DECISIONS.md`, and only the maintainer can discharge it. Two further
preconditions are named — the checker harness remains `llm-unreviewed` and a
public flip does not change that, and the one unverified citation.

The flip minute is four steps: flip, apply-and-verify, *then* announce, then
record. Step 3 carries the reasoning rather than just the instruction — exposure
begins at attention, not at the visibility bit, and the unprotected-public window
can only be written to by accounts with push access, which is the two
maintainers. So its real risk is a maintainer's own accidental direct push during
that minute. In one sitting that is close to nil; left open overnight it is a
habit forming.

## What this round does not establish

Protection is **not live**. Nothing about `main` changed: direct pushes still
work, and all eight gates remain advisory until the payload is applied after the
flip. This round moved the work from "unavailable" to "one command, verified on
application" — it did not enforce anything.

And the honest limit of what will be enforced, recorded in the ledger rather than
implied away: `enforce_admins` is a **latch, not a lock**. The owner can disable
protection in settings at any time. It does not stop deliberate bypass; it
converts accidental or lazy bypass into a visible, deliberate act. Against someone
holding admin rights that is the most a self-binding rule can honestly claim.
