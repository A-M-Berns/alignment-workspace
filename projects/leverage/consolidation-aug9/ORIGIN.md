# Origin — the leverage consolidation

**Status: `agent-consolidated`.** Ordinary content — editable and
reviewable, not machine-protected. The norm is that it is not tweaked. Edit it
when there is a reason, state the reason in the commit, and record substantive
edits in `DECISIONS.md`. Rewriting it to fit new work is not a reason.

## What it is

The consolidation of the leverage line: six theory parts numbered 7–12, a ledger
of 180 claims with hypotheses, statuses, sharpness and dependencies, and a trust
audit separating machine-checked from hand-derived from transcribed from
reading-audit from assumed. It **vendors the August 8 consolidation internally**
at `vendor/consolidation_aug8.zip`, together with the settlement-interface
documents and the source tree's own theory documents, each pinned by digest
inside it. It verifies standalone:

```sh
cd projects/leverage/consolidation-aug9 && python3 tests/run.py
```

## As received

| | |
|---|---|
| received | 2026-08-09, corrections folded in 2026-08-10 |
| archive sha256 | `5f3bf1bee88fdb8808b3d976358e32f2e21e93f4cb2041d79cc3e0c90f0ba0cc` |
| tree sha256 at intake | `a2ca95ad9d6cafcaecb77b7b4d7a0d75f9a33738e3ecb65437b50a56eb7a164a` |
| files at intake | 59 |

The archive itself is not kept: this material is here to be read and cited, and a
zip is neither.

## What cites it

`projects/leverage/README.md`, which names it the authoritative record for the
line; `PRIORITIES.md` items 1–6; `projects/leverage/forward/CONSOLIDATION_REF.md`;
and CI's consolidation-verification job, which runs the verifier above from a
copy on every push. Cite results **by claim identifier** — `NL-SI-A3`, `CD-L1` —
never by copying statements into new work.

It also carries its own internal digest manifest over its vendored inputs, which
its own runner checks, so the CI job exercises a second independent layer of
digests inside this one.

## Checking this receipt

The tree hash is over relative paths and file digests in sorted order, excluding
bytecode artifacts and `.DS_Store` — and **excluding this file**, which did not
exist at intake. Recompute it that way and you learn whether the tree has moved
since it arrived. Nothing enforces that it has not: this is a receipt, not a
gate. The protection that remains is that these paths are specification layer in
`tests/path_gate.py`, so a contributor cannot touch them and a maintainer's edit
is a reviewed diff in git history.
