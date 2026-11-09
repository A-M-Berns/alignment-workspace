# The GitHub sign-in relay

The site signs readers in with GitHub's device flow. Those two login endpoints send no
CORS headers, so the browser cannot call them from a static page; this worker forwards
exactly `/device/code` and `/oauth/access_token` to github.com and nothing else. It
holds **no secret** — device flow has none, the client id is public and pinned by a
plain variable — and tokens pass through to the reader's own browser without being
stored. Everything after sign-in (reading the account, forking, writing the ledger line,
opening the pull request) runs in the browser against api.github.com, which allows CORS.

Deploy (maintainer, once):

1. Create a GitHub OAuth App (Settings → Developer settings → OAuth Apps): any homepage
   and callback URL (device flow uses neither), and **enable Device Flow**. Copy the
   client id.
2.     cd infra/github-login-relay
       wrangler deploy --var CLIENT_ID:<client id>
3. Put the relay URL in `state/site_auth.json` (`"relay": "https://login.alignmentworkspace.com"`)
   and commit; the build embeds it and the sign-in button appears. With the field empty
   the dialog says sign-in is unconfigured.
