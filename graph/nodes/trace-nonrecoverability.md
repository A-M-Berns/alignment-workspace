---
id: trace-nonrecoverability
kind: and
children: [trace-nonrecoverability.record, trace-nonrecoverability.bridge, trace-finite-report-layer, trace-nonrecoverability.complete]
author: "@smithy-verity"
size: M
size_reason: "one note section and one finite package"
version: 1
---
## Statement
No function of the observable trace is a legitimacy predicate: two valid finite
systems share a trace and have influence defects 0 and one half, and the
defects consistent with a trace form exactly the interval from 0 to the trace's
maximal defect.

## Source
projects/deference/note-dump-2026-08-11/notes/legitimacy-theory-v1.md, section
2.3 ("Why legitimacy cannot be a trace condition"), whose provenance principle
says every safety-relevant boundary is a fact about "where a value came from";
projects/deference/faf-cleanroom-2026-10-02/packages/legit-finite-defect/legit-finite-defect-report.md,
the declarations no_recovery and IdentifiedSet.defect_consistent_iff (the exact
identified set).

## Notes
A formal result in the landed shape, finite version. The LI-register version is
the question trace-nonrecoverability-li. Its validity as an implication is
evidence for the picture of the local-rules crux under which no sound local
rule set exists (records cannot certify provenance).
