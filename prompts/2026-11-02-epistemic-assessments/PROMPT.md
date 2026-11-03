# Dispatch of 2026-11-02 — collaborative epistemic status, first increment

Maintainer directives, in conversation on the site's design, verbatim:

> let's talk more about the epistemic status/builder-breaker stuff. I agree that the site
> should be a render rather than a source, but i also want the ability for a human to
> read content on the site and then be able to like change the epistemic status from the
> site itself, which then goes back into the repo. and then we should perhaps carefully
> refine the repo's own claim/status system to best fit with this along with the
> builder-breaker idea

> get a second opinion from astra on the very best way to set up this collaborative
> epistemic status/builder breaker system

> Ok right so at this point I'm thinking probably that straight up comments should
> probably not be part of this. There should just be this builder-breaker system, plus a
> tool in the chatbot that files an issue / contacts us

> Ok so let's start work on the new epistemic status stuff

The design adopted (this conversation, after a GPT-6 Astra consult of 2026-11-02): one
event graph, three derived views — mechanical verification class (registry, untouchable
from any UI), contest state (derived from case/response/resolution artifacts; a response
never resolves a case by existing; resolutions carry a basis and an actor), and human
assessment (stance + aspect + required rationale, revision-bound, in the contributor's
own ledger, superseding only that contributor's own earlier event; human disagreement is
displayed, never resolved by timestamp or vote). Builder-breaker organises work through
derived queues. No reputation scores; self-attacks allowed but labelled; attack artifacts
register their own claims when they assert something checkable.

Scope of this round, the first increment: the `assessment` event kind — protocol text,
checker validation with null-input self-tests, and the derived view the site will read.
Site rendering and the record-my-assessment flow follow in the same round once the open
site pull request (#136) has merged, so the branches do not stack. Write scope granted;
the round lands as its own pull request.
