---
id: shortfall.security-generable.record
kind: leaf
leaf_kind: record
statement_of_record: Workspace.Deference.Contrib.ShortfallSecurity.shortLUV_codes
hypotheses: unread
size: S
size_reason: "one declaration against the registry"
version: 1
author: "@smithy-verity"
registry_id: shortfall.security-generable
---
## Statement
The declaration Workspace.Deference.Contrib.ShortfallSecurity.shortLUV_codes is accepted by the Lean kernel in the repository's Lean library.

## Source
projects/deference/CLAIMS.md, entry `shortfall.security-generable` (class lean-proved, status superseded, origin round 2026-10-01-thin-legitimacy-and-effective-authority; answers item 107).
Documentation: verification: projects/deference/rounds/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md; context: prompts/2026-10-01-thin-legitimacy-and-effective-authority/REPORT.md.
The signature of `Workspace.Deference.Contrib.ShortfallSecurity.shortLUV_codes` (theorem) in lean/Workspace/Deference/Contrib/ShortfallSecurity.lean, verbatim, binders included (ruling F1, 2026-10-23: the hypotheses are unread, and this text is what a reader files them from):

    (cm : ControlModel 4) :
        LUV.RpnThresholdCodeSeq (fun z => indicator (shortSentence cm z))
