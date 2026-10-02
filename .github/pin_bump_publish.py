#!/usr/bin/env python3
"""The write-scoped half of `.github/workflows/pin-bump.yml`, over files as data.

Runs in `pin-bump-publish` after `pin-trial`, whether the trial passed or failed.
It installs no toolchain and executes nothing from `lean/` or from a dependency:
every input is a text file read from the run's artifacts, from this checkout of
`main`, or from the GitHub API, and every output is a branch push or an issue.

Trial green: the three bumped files are verified before anything is pushed —

  * `lean/lakefile.toml` differs from `main`'s copy in exactly one line, the
    `rev = "…"` line, and the new rev is the head of FAF `main` *as this job
    resolves it* (a head that moved between the two jobs fails here);
  * `lean/lean-toolchain` equals FAF's `lean-toolchain` at that rev;
  * every dependency entry in `lean/lake-manifest.json` other than
    `agentFoundations` itself names the same url and rev as FAF's own manifest at
    that rev, and FAF's manifest names nothing this one lacks.

Then one signed-off commit is force-pushed to `bot/pin-bump` and the issue
"pin bump ready" is opened or updated. The maintainer opens the pull request;
this script never does, and it never touches `main`.

Trial red, or verification fails: nothing is pushed; "pin bump blocked" is
opened or updated, naming the failing step and linking the run.
"""
from __future__ import annotations

import argparse
import base64
import json
import os
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
FAF = os.environ.get("FAF", "A-M-Berns/Formalized-Agent-Foundations")
MAINTAINER = "A-M-Berns"
BRANCH = "bot/pin-bump"
TITLE_READY = "pin bump ready"
TITLE_BLOCKED = "pin bump blocked"
PIN_FILES = ("lean/lakefile.toml", "lean/lake-manifest.json", "lean/lean-toolchain")
REV_LINE = re.compile(r'^rev = "([0-9a-f]{40})"$')
BOT_NAME = "github-actions[bot]"
BOT_EMAIL = "41898282+github-actions[bot]@users.noreply.github.com"


def sh(*args: str, check: bool = True, cwd: pathlib.Path | None = None) -> subprocess.CompletedProcess:
    proc = subprocess.run(args, capture_output=True, text=True, cwd=cwd or ROOT)
    if check and proc.returncode != 0:
        raise RuntimeError(f"{' '.join(args)} failed ({proc.returncode}):\n{proc.stderr.strip()}")
    return proc


def api(path: str, jq: str | None = None) -> str:
    args = ["gh", "api", path] + (["--jq", jq] if jq else [])
    return sh(*args).stdout.strip()


def faf_file(path: str, ref: str) -> str:
    content = api(f"repos/{FAF}/contents/{path}?ref={ref}", ".content")
    return base64.b64decode(content).decode("utf-8")


def run_url() -> str:
    return (f"{os.environ['GITHUB_SERVER_URL']}/{os.environ['GITHUB_REPOSITORY']}"
            f"/actions/runs/{os.environ['GITHUB_RUN_ID']}")


def repo() -> str:
    return os.environ["GITHUB_REPOSITORY"]


def read_trial(trial: pathlib.Path, name: str) -> str | None:
    path = trial / name
    return path.read_text().strip() if path.exists() else None


def failed_steps() -> list[str]:
    """`pin-trial`'s failed step names, from this run's job list."""
    data = json.loads(api(f"repos/{repo()}/actions/runs/{os.environ['GITHUB_RUN_ID']}/jobs?per_page=100"))
    for job in data.get("jobs", []):
        if job.get("name") != "pin-trial":
            continue
        return [s["name"] for s in job.get("steps", [])
                if s.get("conclusion") in ("failure", "timed_out", "cancelled")]
    return []


# ----------------------------------------------------------------------- verification

def manifest_packages(text: str) -> dict[str, dict]:
    return {p["name"]: p for p in json.loads(text).get("packages", [])}


def verify(files: pathlib.Path, head: str) -> list[str]:
    """Every way the artifact can fail to be the bump it claims to be."""
    findings: list[str] = []
    for name in PIN_FILES:
        if not (files / name).exists():
            findings.append(f"artifact is missing `{name}`")
    if findings:
        return findings

    # lakefile.toml: one line differs, it is the rev line, and the rev is FAF main.
    before = sh("git", "show", f"HEAD:lean/lakefile.toml").stdout.splitlines()
    after = (files / "lean/lakefile.toml").read_text().splitlines()
    if len(before) != len(after):
        findings.append("`lean/lakefile.toml` changed its line count; only the rev line may change")
    else:
        diffs = [(a, b) for a, b in zip(before, after) if a != b]
        if len(diffs) != 1:
            findings.append(f"`lean/lakefile.toml` differs from `main` in {len(diffs)} line(s); exactly one is allowed")
        else:
            old_m, new_m = REV_LINE.match(diffs[0][0]), REV_LINE.match(diffs[0][1])
            if not (old_m and new_m):
                findings.append(f"the changed line of `lean/lakefile.toml` is not the rev line: {diffs[0][1]!r}")
            elif new_m.group(1) != head:
                findings.append(f"`lean/lakefile.toml` pins `{new_m.group(1)[:10]}` but FAF `main` is "
                                f"`{head[:10]}` as this job resolves it")

    # lean-toolchain equals FAF's at the rev.
    want = faf_file("lean-toolchain", head).strip()
    got = (files / "lean/lean-toolchain").read_text().strip()
    if want != got:
        findings.append(f"`lean/lean-toolchain` is `{got}`; FAF's at `{head[:10]}` is `{want}`")

    # Manifest: every dependency entry matches FAF's manifest at the rev.
    try:
        ours = manifest_packages((files / "lean/lake-manifest.json").read_text())
        theirs = manifest_packages(faf_file("lake-manifest.json", head))
    except (json.JSONDecodeError, KeyError) as exc:
        return findings + [f"a manifest did not parse: {exc}"]
    faf_entry = ours.pop("agentFoundations", None)
    if faf_entry is None:
        findings.append("`lean/lake-manifest.json` has no `agentFoundations` entry")
    elif faf_entry.get("rev") != head:
        findings.append(f"`lean/lake-manifest.json` records agentFoundations at "
                        f"`{str(faf_entry.get('rev'))[:10]}`, not `{head[:10]}`")
    for name, entry in sorted(ours.items()):
        ref = theirs.get(name)
        if ref is None:
            findings.append(f"manifest entry `{name}` has no counterpart in FAF's manifest at `{head[:10]}`")
            continue
        for field in ("url", "rev"):
            if entry.get(field) != ref.get(field):
                findings.append(f"manifest entry `{name}`.{field} is `{entry.get(field)}`; FAF's is `{ref.get(field)}`")
    for name in sorted(set(theirs) - set(ours)):
        findings.append(f"FAF's manifest names `{name}`, which `lean/lake-manifest.json` lacks")
    return findings


# ------------------------------------------------------------------------------ issues

def mention() -> str:
    return f"@{MAINTAINER}"


def open_or_update_issue(title: str, body: str) -> str:
    listing = sh("gh", "issue", "list", "-R", repo(), "--state", "open", "--search",
                 f'in:title "{title}"', "--json", "number,title,url", "--limit", "20").stdout
    exact = [i for i in json.loads(listing or "[]") if i["title"] == title]
    if exact:
        issue = sorted(exact, key=lambda i: i["number"])[-1]
        sh("gh", "issue", "comment", str(issue["number"]), "-R", repo(), "--body", body)
        sh("gh", "issue", "edit", str(issue["number"]), "-R", repo(), "--add-assignee", MAINTAINER, check=False)
        print("commented on", issue["url"])
        return issue["url"]
    proc = sh("gh", "issue", "create", "-R", repo(), "--title", title, "--body", body,
              "--assignee", MAINTAINER)
    print("opened", proc.stdout.strip())
    return proc.stdout.strip()


def blocked(step: str, detail: str, old: str | None, head: str | None) -> int:
    revs = (f"`{old[:10]}` → `{head[:10]}`" if old and head else "(not resolved)")
    body = "\n".join([
        f"{mention()} — the FAF pin bump is **blocked**.",
        "",
        f"**Failing step:** {step}",
        "",
        detail,
        "",
        f"**Revision attempted:** {revs}",
        f"**Run:** {run_url()}",
        "",
        "Nothing was pushed. This workflow does not fix breakage; it reports it.",
    ])
    open_or_update_issue(TITLE_BLOCKED, body)
    return 0


# ----------------------------------------------------------------------------- publish

def publish(files: pathlib.Path, trial: pathlib.Path, old: str, head: str) -> int:
    toolchain = (files / "lean/lean-toolchain").read_text().strip()
    build_seconds = read_trial(trial, "build_seconds")
    build_time = f"{int(build_seconds) // 60} min {int(build_seconds) % 60} s" if build_seconds else "not recorded"
    commits = api(f"repos/{FAF}/compare/{old}...{head}", ".total_commits") or "?"

    sh("git", "config", "user.name", BOT_NAME)
    sh("git", "config", "user.email", BOT_EMAIL)
    sh("git", "checkout", "-B", BRANCH)
    for name in PIN_FILES:
        (ROOT / name).write_text((files / name).read_text())
    sh("git", "add", *PIN_FILES)
    message = "\n".join([
        f"Bump the Formalized-Agent-Foundations pin to {head[:10]}",
        "",
        f"agentFoundations {old} -> {head} ({commits} upstream commits);",
        f"lean-toolchain {toolchain}, copied from FAF at that rev; lake-manifest.json",
        f"from `lake update agentFoundations`. Built and audited by {run_url()}.",
        "The three files were verified as data against FAF's own files at the rev",
        "before this commit was made.",
        "",
        f"Signed-off-by: {BOT_NAME} <{BOT_EMAIL}>",
    ])
    sh("git", "commit", "-q", "-m", message)
    sh("git", "push", "--force", "origin", f"HEAD:refs/heads/{BRANCH}")
    server, r = os.environ["GITHUB_SERVER_URL"], repo()
    compare = f"{server}/{r}/compare/main...{BRANCH.replace('/', '%2F')}?expand=1"
    print("pushed", f"{server}/{r}/tree/{BRANCH}")

    body = "\n".join([
        f"{mention()} — a pin bump to FAF `main` built and audited green and is ready to open as a pull request.",
        "",
        f"**Compare / open the pull request:** {compare}",
        "",
        "| | old | new |",
        "| --- | --- | --- |",
        f"| agentFoundations | `{old[:10]}` | `{head[:10]}` |",
        f"| lean-toolchain | `{sh('git', 'show', 'HEAD~1:lean/lean-toolchain').stdout.strip()}` | `{toolchain}` |",
        "",
        f"**Upstream commits:** {commits}  ",
        f"**Trial build wall time:** {build_time}  ",
        f"**Run:** {run_url()}",
        "",
        f"The branch `{BRANCH}` holds one signed-off commit touching only `lean/lakefile.toml`, "
        "`lean/lake-manifest.json` and `lean/lean-toolchain`, force-pushed by the workflow; `.lake` for "
        "these files is saved under the key the `lean` job will compute. The workflow does not open the "
        "pull request and does not touch `main`: opening it is the maintainer's review that means reading.",
    ])
    open_or_update_issue(TITLE_READY, body)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--trial-result", required=True, help="needs.pin-trial.result")
    parser.add_argument("--trial-dir", default="trial")
    parser.add_argument("--files-dir", default="files")
    args = parser.parse_args()
    trial = ROOT / args.trial_dir
    files = ROOT / args.files_dir

    status = read_trial(trial, "status")
    old, head = read_trial(trial, "old"), read_trial(trial, "head")
    if status == "unchanged":
        print(f"lean/lakefile.toml already pins FAF main ({head}); nothing to publish")
        return 0
    if args.trial_result != "success" or status != "bump":
        steps = failed_steps()
        step = ", ".join(f"`{s}`" for s in steps) if steps else f"pin-trial ({args.trial_result})"
        return blocked(f"pin-trial — {step}", "The trial did not complete green; see the run log.", old, head)

    resolved = api(f"repos/{FAF}/commits/main", ".sha")
    findings = verify(files, resolved)
    if findings:
        detail = "The trial was green but the artifact did not verify as data:\n\n" + \
                 "\n".join(f"- {f}" for f in findings)
        return blocked("pin-bump-publish — verification", detail, old, resolved)
    return publish(files, trial, old or "", resolved)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except RuntimeError as exc:
        print("pin_bump_publish:", exc, file=sys.stderr)
        sys.exit(2)
