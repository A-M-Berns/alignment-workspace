"""Gate 8: the Developer Certificate of Origin.

Every commit in a pull request carries a `Signed-off-by:` line — `git commit -s`.
The sign-off is the contributor's assertion of rights under the DCO in the `DCO`
file at the repository root.

**Pseudonymous sign-offs are accepted.** The maintainers acknowledge that this is
a thinner assertion from a pseudonym than from a known person, and accept it
deliberately: Apache-2.0 §5 is the primary rights mechanism, and the DCO is the
recorded assertion on top of it. Identity is not a factor in a proof-layer
verdict, and this gate does not make it one — it checks that an assertion was
made, not who made it.

Merge commits are excluded: on a pull request GitHub checks out a synthetic merge
of the branch into its base, and that commit has no author who could sign it.

No third-party app: this is a script, so the gate has no dependency the
repository does not control.
"""
from __future__ import annotations

import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SIGNOFF = re.compile(r"^Signed-off-by: .+ <[^>]+>\s*$", re.M)


def commits() -> list[str]:
    base = os.environ.get("GITHUB_BASE_REF")
    if not base:
        return []
    subprocess.run(["git", "fetch", "--depth=50", "origin", base],
                   cwd=ROOT, capture_output=True)
    # --no-merges is load-bearing, not tidiness. On a pull request GitHub checks
    # out a synthetic merge of the branch into the base; that commit has no
    # author to sign it and structurally cannot carry a sign-off. Counting it
    # would fail every pull request the repository ever receives.
    out = subprocess.run(["git", "rev-list", "--no-merges", f"origin/{base}..HEAD"],
                         cwd=ROOT, capture_output=True, text=True)
    return [c for c in out.stdout.split() if c]


def main() -> int:
    shas = commits()
    if not shas:
        print("DCO: no pull-request context; nothing to check")
        return 0
    missing = []
    for sha in shas:
        message = subprocess.run(["git", "log", "-1", "--format=%B", sha],
                                 cwd=ROOT, capture_output=True, text=True).stdout
        if not SIGNOFF.search(message):
            subject = message.strip().splitlines()[0] if message.strip() else "(empty)"
            missing.append(f"{sha[:9]}  {subject[:70]}")
    if missing:
        print("DCO FAILED: these commits carry no `Signed-off-by:` line:",
              file=sys.stderr)
        for m in missing:
            print(f"  - {m}", file=sys.stderr)
        print("\n  Sign off with `git commit -s` (or amend with "
              "`git commit --amend -s`). The sign-off asserts the Developer "
              "Certificate of Origin in `DCO`. Pseudonymous sign-offs are "
              "accepted.", file=sys.stderr)
        return 1
    print(f"DCO: all {len(shas)} commit(s) signed off")
    return 0


if __name__ == "__main__":
    sys.exit(main())
