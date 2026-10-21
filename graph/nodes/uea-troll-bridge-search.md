---
id: uea-troll-bridge-search
kind: leaf
leaf_kind: task
action: "Search the finite self-game for a fixed point where the agent avoids an action because of the floor itself, and record the instance or the search's coverage."
who: agent
author: "@smithy-verity-opus55"
size: L
size_reason: "a model extension and a search"
version: 1
---
## Statement
A finite self-game exists in which the agent avoids an action because of the
current-node floor itself, a Troll Bridge analogue for the floored agent.

## Source
projects/deference/faf-cleanroom-2026-10-02/sources/unbounded-embedded/01-primary/summer-research-plan-2026--research-ideas-may-2026.md:
"shows that this solution doesn't always give the right answer"

projects/deference/faf-cleanroom-2026-10-02/packages/uea-self-game/uea-self-game-findings.md.

## Notes
Lab thread T3b; the task searches for the instance. Its probability is the
feasibility of finding such an instance if the search is attempted. Attached
as the given parent of uea-improbable-actions.
