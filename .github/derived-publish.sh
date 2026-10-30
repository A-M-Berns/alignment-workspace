#!/usr/bin/env bash
# Publish the plain derivation of main — graph/derived.json and graph/index.json,
# the two generated files that are not committed (ruling F3, 2026-10-23) — to the
# orphan branch `derived`, then prove the publish landed exactly.
#
# The branch is a mirror of one derivation: a single commit, force-pushed on
# every push to main, whose message carries the main commit it derives from.
# Whatever the branch held before is replaced, by design. The verification step
# is not decoration: a push that half-lands leaves a site reading a derivation
# no checker run produced, and nothing else would notice.
#
#   GITHUB_TOKEN=<ephemeral> FILES=<dir holding derived.json and index.json> \
#     bash .github/derived-publish.sh
#
# On a token refusal this stops and reports. It does not fall back to another
# credential: CI holds zero permanent secrets, and minting one to get past this
# is the thing the rule exists to prevent. This script runs no checker and
# imports nothing: the files are data it was handed (AGENTS.md, Security,
# condition 5).
set -euo pipefail

REPO="${GITHUB_REPOSITORY:-A-M-Berns/alignment-workspace}"
SOURCE_SHA="${GITHUB_SHA:?the source commit on main}"
FILES="${FILES:?the directory holding derived.json and index.json}"
BRANCH="${DERIVED_BRANCH:-derived}"
WORK="${RUNNER_TEMP:-/tmp}/derived-publish"
# `DERIVED_REMOTE` exists so this can be rehearsed against a local bare
# repository. The workflow never sets it, and a run that does not set it needs
# the token.
REMOTE="${DERIVED_REMOTE:-https://x-access-token:${GITHUB_TOKEN:?the ephemeral workflow token}@github.com/${REPO}.git}"

for f in derived.json index.json; do
  if [ ! -s "$FILES/$f" ]; then
    echo "DERIVED PUBLISH STOPPED: $FILES/$f is missing or empty; the build job did not hand over the derivation." >&2
    exit 1
  fi
done

rm -rf "$WORK"
mkdir -p "$WORK/src/graph"
cp "$FILES/derived.json" "$FILES/index.json" "$WORK/src/graph/"
cat > "$WORK/src/README.md" <<EOF
# derived — the plain derivation of main

The two generated files of the argument map that are not committed to the
source tree (ruling F3, 2026-10-23): \`graph/derived.json\`, the full derivation
(every level, status, probability, value and ranked unit), and
\`graph/index.json\`, the structure-only index a site renders from. Both are
written by \`python3 -m checkers.graph --root .\` on the plain run and carry a
\`generated_hash\` over their own content; \`graph/versions.json\` on main
records each file's derivation hash, so a derivation can be checked against the
commit it came from.

This branch is replaced on every push to main by the workflow \`derived\`. Do not
commit to it: the next push discards whatever is here.

Derived from main at ${SOURCE_SHA}.
EOF

digest() {
  (cd "$1" && find . -type f -not -path './.git/*' -print0 | LC_ALL=C sort -z | xargs -0 sha256sum | sha256sum | cut -d' ' -f1)
}
SOURCE_DIGEST="$(digest "$WORK/src")"
echo "derivation of ${SOURCE_SHA} -> ${SOURCE_DIGEST}"

git -C "$WORK/src" init --quiet --initial-branch "$BRANCH"
git -C "$WORK/src" config user.name "github-actions[bot]"
git -C "$WORK/src" config user.email "41898282+github-actions[bot]@users.noreply.github.com"
git -C "$WORK/src" add -A
git -C "$WORK/src" commit --quiet -m "derived: the plain derivation of main at ${SOURCE_SHA}" -m "graph/derived.json and graph/index.json as the plain checker run wrote them on ${REPO}@${SOURCE_SHA}. One commit, force-pushed on every push to main; the source tree does not commit these files (ruling F3, 2026-10-23)."

echo "Force-pushing to ${BRANCH} ..."
if ! git -C "$WORK/src" push --force --quiet "$REMOTE" "HEAD:refs/heads/${BRANCH}" 2> "$WORK/push.err"; then
  echo "DERIVED PUBLISH STOPPED: the workflow token was refused push access to ${REPO}." >&2
  echo "  git said:" >&2
  sed 's/^/    /' "$WORK/push.err" >&2
  echo "  This is a stop-and-report. Do not mint a personal access token to get" >&2
  echo "  past it — CI holds zero permanent secrets, and which fallback to take" >&2
  echo "  is a maintainer decision recorded in DECISIONS.md." >&2
  exit 1
fi

# Verify against what the remote now serves, from a clone that shares nothing
# with the tree just pushed.
echo "Verifying ..."
git clone --quiet --depth 1 --branch "$BRANCH" "$REMOTE" "$WORK/verify"
PUBLISHED_DIGEST="$(digest "$WORK/verify")"
echo "branch ${BRANCH} -> ${PUBLISHED_DIGEST}"
if [ "$SOURCE_DIGEST" != "$PUBLISHED_DIGEST" ]; then
  echo "DERIVED PUBLISH FAILED: the branch ${BRANCH} does not match the derivation after the push." >&2
  echo "  derivation  ${SOURCE_DIGEST}" >&2
  echo "  branch      ${PUBLISHED_DIGEST}" >&2
  exit 1
fi
echo "DERIVED PUBLISH: branch ${BRANCH} carries the derivation of ${SOURCE_SHA} — ${SOURCE_DIGEST}"
