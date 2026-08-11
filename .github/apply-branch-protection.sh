#!/usr/bin/env bash
# Apply branch protection to main from the committed payload, then read it back
# and verify. One command, no third-party dependencies beyond `gh`.
#
#   bash .github/apply-branch-protection.sh
#
# The payload is the source of truth for the required-check list.
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
      -H "Accept: application/vnd.github+json" --input -

echo
echo "Reading back what GitHub actually stored:"
gh api "/repos/${REPO}/branches/main/protection" | python3 -c "
import json,sys
p=json.load(sys.stdin)
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
print()
print('PROTECTION LIVE AND CORRECT' if ok and len(names)==8 else 'CHECK THE LINES MARKED WRONG')
sys.exit(0 if ok and len(names)==8 else 1)
"
