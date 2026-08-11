#!/usr/bin/env bash
# Apply branch protection to main from the committed payload, then read it back
# and verify. Also enables GitHub-native auto-merge, so a pull request whose
# required checks all pass merges without a maintainer click. One command, no
# third-party dependencies beyond `gh`.
#
#   bash .github/apply-branch-protection.sh
#
# The payload is the source of truth for the required-check list, including how
# many there are: the read-back counts what the payload declares rather than a
# literal, which is what let a stale `8` survive the retirement of a gate and
# report correct protection as wrong.
set -euo pipefail

REPO="${REPO:-A-M-Berns/alignment-workspace}"
PAYLOAD="$(dirname "$0")/branch-protection.json"

echo "Applying branch protection to ${REPO}:main ..."
# The API rejects unknown keys, so strip the documentation comment.
python3 -c "
import json,sys
d=json.load(open('${PAYLOAD}'))
d.pop('_comment',None)
json.dump(d,sys.stdout)
" | gh api -X PUT "/repos/${REPO}/branches/main/protection" \
      -H "Accept: application/vnd.github+json" --input - > /dev/null

echo
echo "Enabling auto-merge on the repository ..."
gh api -X PATCH "/repos/${REPO}" -H "Accept: application/vnd.github+json" \
   -F allow_auto_merge=true > /dev/null

echo
echo "Reading back what GitHub actually stored:"
EXPECTED_CHECKS="$(python3 -c "
import json
print(len(json.load(open('${PAYLOAD}'))['required_status_checks']['contexts']))
")"
AUTO_MERGE="$(gh api "/repos/${REPO}" --jq .allow_auto_merge)"

gh api "/repos/${REPO}/branches/main/protection" | EXPECTED_CHECKS="${EXPECTED_CHECKS}" AUTO_MERGE="${AUTO_MERGE}" python3 -c "
import json,os,sys
p=json.load(sys.stdin)
expected=int(os.environ['EXPECTED_CHECKS'])
checks=p.get('required_status_checks',{}).get('contexts') or \
       p.get('required_status_checks',{}).get('checks')
names=[c if isinstance(c,str) else c.get('context') for c in (checks or [])]
rev=p.get('required_pull_request_reviews') or {}
ok=True
def line(label,got,want):
    global ok
    good = got==want
    ok = ok and good
    print(f\"  {'ok  ' if good else 'WRONG'} {label}: {got!r}\" + ('' if good else f' (expected {want!r})'))
print('Verification:')
print(f'  required checks ({len(names)}):')
for n in sorted(names): print(f'      {n}')
line('required approvals', rev.get('required_approving_review_count'), 0)
line('code-owner reviews', rev.get('require_code_owner_reviews'), False)
line('enforce for admins', p.get('enforce_admins',{}).get('enabled'), True)
line('force pushes blocked', not p.get('allow_force_pushes',{}).get('enabled',True), True)
line('deletions blocked', not p.get('allow_deletions',{}).get('enabled',True), True)
line('auto-merge enabled', os.environ['AUTO_MERGE']=='true', True)
line('check count matches payload', len(names), expected)
print()
print('PROTECTION LIVE AND CORRECT' if ok else 'CHECK THE LINES MARKED WRONG')
sys.exit(0 if ok else 1)
"
