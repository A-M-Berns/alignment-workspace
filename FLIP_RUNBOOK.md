# Flip runbook

The procedure for making this repository public, to be executed **in one sitting,
at the keyboard**. It exists because the flip and the protection cannot be
simultaneous: GitHub will not apply branch protection to a private repository on
this plan, so protection can only be applied *after* the repository is public.

## Before you start — preconditions this runbook does not discharge

**Do not execute step 1 until these are true.** They are listed first so the
procedure cannot be run by momentum.

1. **The note-dump read-through sign-off is recorded in `DECISIONS.md`.** The
   frozen bundles contain research conversations that have never been scrubbed or
   read for release. `AGENTS.md` requires the maintainer's explicit read-through
   sign-off before a dump reaches a public repository. **Only the maintainer can
   discharge this, and nothing else in this runbook substitutes for it.** If that
   entry is not in the ledger, stop.
2. **You accept that the checker harness is still `llm-unreviewed`.** Going public
   does not change an artifact's provenance class. The harness is the judge in an
   architecture whose premise is that the judge is trustworthy and contributions
   are not; a public flip makes it load-bearing for strangers while leaving it
   unread. Either review it first or flip knowing this.
3. **The one unverified citation** in `frozen/references-citations-2026-08-11/` is
   either verified or you are content to publish it flagged as unverified.

## The flip minute

**1. Flip visibility to public.**

Settings → General → Danger Zone → Change visibility → Public. Or:

```sh
gh api -X PATCH /repos/A-M-Berns/alignment-workstudio -f visibility=public
```

**2. Immediately apply and verify protection.**

```sh
bash .github/apply-branch-protection.sh
```

The script applies the committed payload, reads back what GitHub actually stored,
and prints a verification block. **It exits non-zero unless all of the following
hold**, so you do not have to eyeball it:

- required checks = the **eight** gate names
- required approvals = **0**
- code-owner reviews = **off**
- enforce for administrators = **on**
- force pushes = **blocked**, branch deletion = **blocked**

If it reports `CHECK THE LINES MARKED WRONG`, fix before step 3.

**3. Only then link, announce, or reference the repository anywhere.**

Exposure begins at attention, not at the visibility bit. Between steps 1 and 2 the
repository is public and unprotected — but writing to it requires push access,
which only the two maintainers have. So the real risk of that window is *a
maintainer's own accidental direct push during that minute*, and nothing else.
Executed in one sitting it is close to nil; left open overnight it is a habit
waiting to form.

**4. Record it.** A dated `DECISIONS.md` entry: went public, protection applied,
date, and the verification output.

## If protection becomes available while still private

If the plan changes, run step 2 on its own. The repository then arrives at the
flip already protected, and the flip is just the flip — steps 1, 3, 4.

## What protection is worth

A latch, not a lock. The owner can disable it in settings at any time, so it does
not stop deliberate bypass. It converts accidental or lazy bypass into a visible,
deliberate act. Against someone holding admin rights that is the most any
self-binding rule can honestly claim, and the ledger says so rather than implying
more.
