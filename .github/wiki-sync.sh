#!/usr/bin/env bash
# Publish wiki/ to the hosted wiki, then prove the publish landed exactly.
#
# The repository is the source of truth and the hosted wiki is a mirror, so the
# push is a force-push over a single commit: whatever the wiki's web editor has
# accumulated is replaced, by design. The verification step is not optional
# decoration — a push that half-lands leaves the register saying something no
# reviewed diff ever said, and nothing else in the system would notice.
#
#   GITHUB_TOKEN=<ephemeral> bash .github/wiki-sync.sh
#
# On a token refusal this stops and reports. It does not fall back to another
# credential: CI holds zero permanent secrets, and minting one to get past this
# is the thing the rule exists to prevent.
set -euo pipefail

REPO="${GITHUB_REPOSITORY:-A-M-Berns/alignment-workspace}"
SOURCE_SHA="${GITHUB_SHA:?the source commit on main}"
WORK="${RUNNER_TEMP:-/tmp}/wiki-sync"
# `WIKI_REMOTE` exists so this can be rehearsed against a local bare repository.
# The workflow never sets it, and a run that does not set it needs the token.
REMOTE="${WIKI_REMOTE:-https://x-access-token:${GITHUB_TOKEN:?the ephemeral workflow token}@github.com/${REPO}.wiki.git}"

# What the hosted wiki should contain: wiki/ minus the files that are not
# pages. The list comes from the checker that also decides what a wiki link may
# resolve to, so the two cannot disagree — a file that is a page to the checker
# and absent from the wiki is a link that passes CI and 404s for a reader.
EXCLUDE="$(python3 -c 'from checkers import wiki_links
print(" ".join(wiki_links.REPO_ONLY_FILES))')"

rm -rf "$WORK"
mkdir -p "$WORK"
cp -R wiki "$WORK/src"
for name in $EXCLUDE; do rm -f "$WORK/src/$name"; done
SOURCE_DIGEST="$(python3 .github/wiki_tree_digest.py "$WORK/src")"
echo "wiki/ (excluding: ${EXCLUDE}) -> ${SOURCE_DIGEST}"

echo "Cloning the wiki remote ..."
if ! git clone --quiet "$REMOTE" "$WORK/dst" 2> "$WORK/clone.err"; then
  echo "WIKI SYNC STOPPED: the workflow token could not read the wiki remote." >&2
  echo "  git said:" >&2
  sed 's/^/    /' "$WORK/clone.err" >&2
  echo "  This is a stop-and-report. Do not add a personal access token: the" >&2
  echo "  fallback is a maintainer decision, not this job's to take." >&2
  exit 1
fi
BRANCH="$(git -C "$WORK/dst" symbolic-ref --short HEAD)"

find "$WORK/dst" -mindepth 1 -maxdepth 1 -not -name .git -exec rm -rf {} +
cp -R "$WORK/src/." "$WORK/dst/"

git -C "$WORK/dst" config user.name "github-actions[bot]"
git -C "$WORK/dst" config user.email "41898282+github-actions[bot]@users.noreply.github.com"
git -C "$WORK/dst" add -A
if git -C "$WORK/dst" diff --cached --quiet; then
  echo "The wiki already matches wiki/; nothing to push."
else
  git -C "$WORK/dst" commit --quiet -m "Sync from ${REPO}@${SOURCE_SHA}

The source of truth is wiki/ in the repository. This wiki is a mirror,
force-pushed on merge; edits made here are overwritten."
  echo "Force-pushing to ${BRANCH} ..."
  if ! git -C "$WORK/dst" push --force --quiet origin "HEAD:${BRANCH}" 2> "$WORK/push.err"; then
    echo "WIKI SYNC STOPPED: the workflow token was refused push access to the wiki remote." >&2
    echo "  git said:" >&2
    sed 's/^/    /' "$WORK/push.err" >&2
    echo "  This is a stop-and-report. Do not mint a personal access token to get" >&2
    echo "  past it — CI holds zero permanent secrets, and which fallback to take" >&2
    echo "  is a maintainer decision recorded in DECISIONS.md." >&2
    exit 1
  fi
fi

# Verify against what the remote now serves, from a clone that shares nothing
# with the one just pushed. Reading back the directory this job wrote would
# confirm only that the job can copy files.
echo "Verifying ..."
git clone --quiet "$REMOTE" "$WORK/verify"
PUBLISHED_DIGEST="$(python3 .github/wiki_tree_digest.py "$WORK/verify")"
echo "hosted wiki -> ${PUBLISHED_DIGEST}"

if [ "$SOURCE_DIGEST" != "$PUBLISHED_DIGEST" ]; then
  echo "WIKI SYNC FAILED: the hosted wiki does not match wiki/ after the push." >&2
  echo "  wiki/       ${SOURCE_DIGEST}" >&2
  echo "  hosted      ${PUBLISHED_DIGEST}" >&2
  diff -r "$WORK/src" "$WORK/verify" -x .git >&2 || true
  exit 1
fi

echo "WIKI SYNC: hosted wiki matches wiki/ at ${SOURCE_SHA} — ${SOURCE_DIGEST}"
