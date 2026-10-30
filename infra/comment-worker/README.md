# The comment intake worker

The site's comment form POSTs here; the worker files the comment as a GitHub issue titled
`[comment] <concept id>` — the on-site act and the issue are one step. It holds one
credential, a fine-grained GitHub token with issues:write on this repository alone, as a
Cloudflare Worker secret: never in the repository, never in its CI. Reviewed comments
reach the site when a maintainer round moves them into `state/comments.json`.

Deploy (maintainer, once):

    cd infra/comment-worker
    wrangler deploy            # a Cloudflare token with Workers edit scope
    wrangler secret put GITHUB_TOKEN

The custom domain `comments.alignmentworkspace.com` is created by the deploy.
