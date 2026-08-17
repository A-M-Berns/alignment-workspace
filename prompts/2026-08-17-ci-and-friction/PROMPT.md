# Round: CI scope and workspace friction

Prompt-author-model: the maintainer (conversational dispatch, not a written round
specification). Recorded verbatim per `AGENTS.md` §12.
Date: 2026-08-17

## As sent

> Can we actually add a new pr that makes the following fix (make it a draft pr
> so we can address other friction too). The lean CI check should get bypassed
> if the pr deosn't touch any lean files, if that's possible

## Standing scope

The pull request is a **draft** by the maintainer's instruction, held open to
take further `PRIORITIES.md` *Workspace friction* work. Each addition is a
separate commit and is listed in `REPORT.md`, which is written before the draft
is marked ready. Until then this directory carries no report and the round is
not indexed in `state/rounds.json` — which is what the workspace-state check
means by a completed round.
