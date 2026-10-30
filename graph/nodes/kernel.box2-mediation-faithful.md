---
id: kernel.box2-mediation-faithful
kind: and
children: [kernel.box2-mediation-faithful.record, kernel.box2-mediation-faithful.bridge, kernel.box2-mediation-faithful.complete]
size: M
size_reason: "one registry entry, its Lean declaration and its bridge"
version: 1
work: [{kind: round, ref: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2}, {kind: decision, ref: 2026-09-27--corrigible-names-property-preferences-only-mediation}, {kind: priorities, ref: 104}]
author: "@smithy-verity"
---
## Statement
Formerly `kernel.box2-mediation`, statement of record `box2_mediation_corrigible` (the landed policy notion `Corrigibilization.Corrigible`); renamed by the second follow-up (2026-09-27) because "corrigible" names a property of preferences (`Headline.Corrigible`) and the landed policy notion is faithfulness's pre-emption clause (`landed_corrigible_iff_no_preemption`). `Headline.FaithfulPolicy`: no declared violation — bypass, pre-emption, foreclosure, unlicensed reallocation, missed report, exploitation — on any exterior path; `faithfulPolicy_landed_corrigible`.

## Source
projects/deference/CLAIMS.md, entry `kernel.box2-mediation-faithful` (class lean-proved, status active, origin round 2026-09-27-corrigibility-kernel-phase2; answers item 104).
Documentation: verification: projects/deference/rounds/2026-09-27-corrigibility-kernel-phase2/SPEC.md; context: prompts/2026-09-27-corrigibility-kernel-phase2/REPORT.md.
The signature of `Workspace.Deference.Headline.box2_mediation_faithful` in lean/Workspace/Deference/Spec/Headline.lean.

## Notes
Filed by the map-as-canonical round (prompts/2026-10-22-map-as-canonical) from the registry entry and the declaration's signature; its hypotheses are unread (ruling F1, 2026-10-23): the record's Source carries the signature verbatim, and a reader files the hypothesis leaves. Registry note: Formerly `kernel.box2-mediation`, statement of record `box2_mediation_corrigible` (the landed policy notion `Corrigibilization.Corrigible`); renamed by the second follow-up (2026-09-27) because "corrigible" names a property of preferences (`Headline.Corrigible`) and the landed policy notion is faithfulness's pre-emption clause (`landed_corrigible_iff_no_preemption`). `Headline.FaithfulPolicy`: no declared violation — bypass, pre-emption, foreclosure, unlicensed reallocation, missed report, exploitation — on any exterior path; `faithfulPolicy_landed_corrigible`. The six clauses for `𝔱` are the landed `authPolicy_no_bypass`, `authPolicy_no_missed_report`, `authPolicy_no_exploit`, `authPolicy_no_realloc` and `corrigible_authPolicyJ`, with no foreclosure a stated hypothesis (the reach cone is EXT). With `box2_mediation_approve_branch`: on approval `𝔱π` releases the latch with `π`'s task component up to the required report. Inhabited by `ProtectedAuthorityTheorem.Witness.corrigible_instance` on the two-state physics; the obstruction without delegation safety is `box2_delegated_cut`, which no reach relation repairs. The registry's `answers_item` is the `priorities` pointer to item 104 (ruling F2).
