---
id: item-f9
kind: leaf
leaf_kind: task
action: "Extend checkers/wiki_links.py to resolve each commit-pinned repository link against the local git objects (commit exists, path exists in its tree), with a null-input case for a pin naming a commit or path git does not have."
who: agent
item: "F9"
title: "wiki_links accepts a commit pin that does not resolve"
section: "Workspace friction"
maintainer_order: 142
project: none
dispatchable: true
item_status: open
deliverable: "the extended house checker and its --self-test case; every existing wiki pin still passing."
acceptance: "checkers/wiki_links.py --self-test fails a fabricated pin and passes the live wiki; the checkers job stays green."
context: ["checkers/wiki_links.py", "wiki/Theorem-Spine.md"]
author: "@claude-fable-5"
size: S
size_reason: "one check inside one gate, plus its null case"
version: 1
---
## Statement
Item F9, wiki_links accepts a commit pin that does not resolve, is answered as its entry specifies.

## Source
ATTENTION.md, item F9 (wiki_links accepts a commit pin that does not resolve).

## Notes
Filed by the site-priorities round (prompts/2026-11-05-site-priorities), which hit the defect; the entry's text is the Item section below, rendered into ATTENTION.md by checkers/attention_render.py.

## Item
`checkers/wiki_links.py` reports a commit-pinned repository link clean without checking
that the named commit exists or that the path exists in that commit's tree. The
site-priorities round pinned `wiki/Theorem-Spine.md`'s ledger link to a fabricated
40-character hash sharing only its 8-character prefix with the real commit, and the gate
passed it; the defect surfaced only because the site build printed the true hash moments
later. A pin the gate cannot resolve is exactly the unverified identifier the citation
rule exists to refuse, and a fabricated-but-well-formed pin is the shape an agent error
takes. The fix is contained: resolve each pin against local git objects
(`git cat-file`-grade checks, no network), and ship the null case — a well-formed pin
naming a commit or path git does not have must fail.
