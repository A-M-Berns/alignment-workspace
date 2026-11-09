# Report — sign in with GitHub; the receipt opens its own pull request

Identity on the site is the reader's GitHub account, matched to a handle through
`graph/policy.yaml`'s mapping, which the build ships as `/assets/account.json` with the
repository slug and the relay URL. Sign-in (`site/assets/account.js`, the chip in every
header) is GitHub's device flow — the reader enters a code at github.com, and the token
lands only in their own browser's storage — or a pasted fine-grained token where the
relay is not deployed. The two device-flow endpoints on github.com send no CORS headers,
so a static page cannot call them; `infra/github-login-relay/` is a worker that forwards
exactly those two endpoints, pins the public client id, and holds **no secret**, because
device flow has none. Everything after sign-in runs in the browser against
api.github.com, which allows CORS.

Signed in as a mapped handle, a score's receipt gains *Open the pull request*: the
browser forks the repository under the reader's account where no fork exists, syncs it,
appends the event line to the reader's own ledger on a fresh branch, and opens the pull
request — the site still accepts no write, and the checker adjudicates the event like
any other. A GitHub account no handle maps to can sign in and prepare events but not
submit; the receipt's issue link remains the way to propose a handle. The copy flow is
unchanged and remains the fallback the submit button names on any failure.

The type sampler's leftover loader in `site/assets/app.js` (a stylesheet link into the
removed candidates directory, applied from a stale localStorage key) left with this
change.

Agent-decided, reversible: device flow over the OAuth web flow — web flow requires a
client secret at token exchange, so a worker would hold a credential; device flow's
relay holds none, at the cost of one code-entry step at sign-in. And the `public_repo`
scope over finer grants — the classic-app device flow offers no per-repository scope,
and the token stays in the reader's own browser.

Not shown: the device flow end-to-end is untested until the OAuth app exists and the
relay is deployed (the queue entry below); the submit path is exercised against
api.github.com's documented shapes, not a live run — the first real submission is the
test, and the copy flow backstops it. A token in localStorage is readable by any script
on the origin; the site ships no third-party script, and the scope is public-repository
write on the reader's own account. Nothing here authenticates the *site* to anyone: the
pull request's authorship is GitHub's assertion, as it always was.

The maintainer created the OAuth app and authorized the deploy on 2026-11-09; the relay
runs at `login.alignmentworkspace.com`, `state/site_auth.json` carries it, and the
device-code endpoint round-trips against GitHub. The queue entry is retired. The first
real submission remains the end-to-end test of the fork-and-pull-request path.

## Outstanding maintainer actions

None.

## The follow-up of 2026-11-09 (`PROMPT-followup.md`)

The sign-in dialog is the device flow alone — the pasted-token path leaves — and the
device code renders large, bold and monospaced, selectable in one tap. A human handle is
now the GitHub login: `@anson` and `@abram` become `@A-M-Berns` and `@abramdemski`
across `graph/policy.yaml`, the frame owners, 59 node files' authors and owners, the
protocol's and `AGENTS.md`'s examples, and the ledger `graph/events/A-M-Berns.jsonl`
(its two events' `by` and ids included) — the ledger rename rewrites the maintainer's
own two events at the maintainer's direction, and the checker adjudicates the renamed
tree green. `graph/DESIGN-LOG.md` and completed round records keep the old spelling as
history. New contributors need no minted name: their handle is `@<login>`, and
admission to `policy.yaml` stays the maintainer's act.

## Attribution

Prompt-author: the maintainer, in conversation, kept verbatim (`PROMPT.md`). Executor:
Claude Fable 5 (Anthropic). 2026-11-09.
