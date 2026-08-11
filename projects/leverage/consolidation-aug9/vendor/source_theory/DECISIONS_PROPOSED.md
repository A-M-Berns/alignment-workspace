# Proposed decisions

Items the decisions block left unmarked, or that this phase's work raised.

## P-1. `REPORT.md` name collision

The deliverables list requires a downstream `REPORT.md`, but decision D1 cites
"per REPORT.md" meaning the *upstream* `consolidation_aug8/REPORT.md`. Both now
exist under one name at different roots. **Proposed:** rename the downstream file
`ROUND_REPORT.md`, or cite the upstream one as `upstream/REPORT.md` throughout.
Not acted on: renaming would break this phase's own deliverable list.

## P-2. Scope of the D4 flip against frozen files

D4 says no text may use "liveness" in the old sense after this phase. Two frozen
pinned files contain 10 such occurrences. **Proposed:** restate D4 as applying to
unfrozen documents only, with a mapping note in the rename manifest recording
that the frozen files retain the pre-flip term as fossils — the same treatment
the ST-* claim IDs already receive.

## P-3. Downstream rename manifest

WP-C5 requires extending a manifest that is read-only upstream. **Proposed:** a
downstream `rename_manifest_downstream.json` with its own roundtrip check, wired
into `tests/run.py` beside the existing upstream gate.

## P-4. Where WP-C1 lands

The jump-recursion tightening cannot edit `src/joint.py`. **Proposed:**
`src/joint_tightening.py` importing the frozen module, with `NL-J2'` as a new
claim row citing the original, rather than a superseding edit.

## P-5. Legacy family reconstruction

`GRAMMAR.md` §3 declares a four-family legacy assignment because upstream has no
machine-readable catalog. **Proposed:** either accept the declared reconstruction
as authoritative going forward, or derive the families from `THEORY_5`'s claim
table and accept that it is a claim-family table, not an objection catalog.
